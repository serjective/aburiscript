#include "mangle.h"

#include "../ast/ast_context.h"

#include <algorithm>
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

namespace {
std::string pointer_identity_string(const void* ptr) {
    return std::to_string(reinterpret_cast<uintptr_t>(ptr));
}

const TemplateDecl* canonical_template_decl_identity(const TemplateDecl* decl) {
    return decl ? get_template_decl_canonical_decl(decl) : nullptr;
}

bool is_single_void_parameter(const FunctionType& fn) {
    return fn.parameters.size() == 1 && fn.parameters[0] && fn.parameters[0]->isVoid();
}

QualType decay_parameter_type_for_mangling(const QualType& qt) {
    if (!qt) {
        return qt;
    }
    if (qt->kind == TypeKind::Array) {
        auto arr = qt.as_shared<ArrayType>();
        if (!arr) {
            return qt;
        }
        QualType elem = arr->element_type;
        elem = QualType(elem.get_shared(), elem.get_qualifiers() | qt.get_qualifiers());
        return QualType(std::make_shared<PointerType>(elem));
    }
    if (qt->kind == TypeKind::Function) {
        return QualType(std::make_shared<PointerType>(qt));
    }
    return qt;
}

void append_source_name(std::string& out, const std::string& name) {
    out += std::to_string(name.size());
    out += name;
}

void append_source_name(std::string& out, std::string_view name) {
    out += std::to_string(name.size());
    out.append(name.data(), name.size());
}

const AttributeList& empty_attribute_list_for_mangling() {
    static const AttributeList empty;
    return empty;
}

const AttributeList& attrs_for_decl_node(uint32_t node_id) {
    if (auto* ast_ctx = get_active_side_table_ast_context()) {
        return ast_ctx->get_attrs(node_id);
    }
    return empty_attribute_list_for_mangling();
}

void collect_abi_tags_from_attribute_list(const AttributeList& attrs,
                                          std::vector<std::string>& out) {
    for (const auto& attr : attrs.attrs) {
        if (attr.resolved_kind != AttributeKind::ABI_TAG) {
            continue;
        }
        for (const auto& arg : attr.args) {
            switch (arg.kind) {
                case AttributeArg::Kind::STRING:
                case AttributeArg::Kind::IDENTIFIER:
                    if (!arg.str_value.empty()) {
                        out.push_back(arg.str_value);
                    }
                    break;
                default:
                    break;
            }
        }
    }
}

void normalize_abi_tags(std::vector<std::string>& abi_tags) {
    abi_tags.erase(
        std::remove_if(
            abi_tags.begin(),
            abi_tags.end(),
            [](const std::string& tag) { return tag.empty(); }),
        abi_tags.end());
    std::sort(abi_tags.begin(), abi_tags.end());
    abi_tags.erase(
        std::unique(abi_tags.begin(), abi_tags.end()),
        abi_tags.end());
}

std::vector<std::string> merge_abi_tags(const AttributeList* first,
                                        const AttributeList* second = nullptr) {
    std::vector<std::string> abi_tags;
    if (first) {
        collect_abi_tags_from_attribute_list(*first, abi_tags);
    }
    if (second) {
        collect_abi_tags_from_attribute_list(*second, abi_tags);
    }
    normalize_abi_tags(abi_tags);
    return abi_tags;
}

std::vector<std::string> abi_tags_for_decl(const Decl& decl) {
    return merge_abi_tags(&attrs_for_decl_node(decl.node_id));
}

std::vector<std::string> abi_tags_for_function_decl(const FuncDecl& decl) {
    return abi_tags_for_decl(decl);
}

std::vector<std::string> abi_tags_for_variable_decl(const VariableDecl& decl) {
    const AttributeList* decl_attrs = &attrs_for_decl_node(decl.node_id);
    const AttributeList* symbol_attrs =
        decl.sym ? &decl.sym->sym_attrs : nullptr;
    return merge_abi_tags(decl_attrs, symbol_attrs);
}

std::vector<std::string> abi_tags_for_symbol(const Symbol& sym) {
    return merge_abi_tags(&sym.sym_attrs);
}

std::vector<std::string> abi_tags_for_class_template_primary(
    const Decl* primary_template) {
    auto* class_template =
        dyn_cast<ClassTemplateDecl>(const_cast<Decl*>(primary_template));
    if (!class_template) {
        return {};
    }
    auto* record = class_template->record_decl();
    if (!record) {
        return {};
    }
    return abi_tags_for_decl(*record);
}

void append_itanium_abi_tags(std::string& out,
                             const std::vector<std::string>& abi_tags) {
    for (const auto& tag : abi_tags) {
        out += 'B';
        append_source_name(out, tag);
    }
}

std::vector<std::string_view> split_cxx_qualifier_prefix(std::string_view prefix) {
    std::vector<std::string_view> components;
    size_t cursor = 0;
    while (cursor < prefix.size()) {
        while (cursor + 1 < prefix.size() &&
               prefix[cursor] == ':' &&
               prefix[cursor + 1] == ':') {
            cursor += 2;
        }
        if (cursor >= prefix.size()) {
            break;
        }
        size_t next = prefix.find("::", cursor);
        if (next == std::string_view::npos) {
            components.push_back(prefix.substr(cursor));
            break;
        }
        components.push_back(prefix.substr(cursor, next - cursor));
        cursor = next + 2;
    }
    return components;
}

size_t implicit_object_parameter_count(const FunctionType& fn,
                                       std::string_view qualifier_prefix,
                                       QualType owner_type);
void append_qualifiers(std::string& out, const QualType& qt);

std::optional<std::string_view> itanium_operator_name_encoding(
    std::string_view name) {
    constexpr std::string_view kOperatorPrefix = "operator";
    if (!name.starts_with(kOperatorPrefix)) {
        return std::nullopt;
    }
    std::string_view suffix = name.substr(kOperatorPrefix.size());
    struct OperatorEncodingEntry {
        std::string_view suffix;
        std::string_view code;
    };
    static constexpr OperatorEncodingEntry kOperatorEncodings[] = {
        {"new", "nw"},
        {"new[]", "na"},
        {"delete", "dl"},
        {"delete[]", "da"},
        {"+", "pl"},
        {"-", "mi"},
        {"*", "ml"},
        {"/", "dv"},
        {"%", "rm"},
        {"&", "an"},
        {"|", "or"},
        {"^", "eo"},
        {"=", "aS"},
        {"+=", "pL"},
        {"-=", "mI"},
        {"*=", "mL"},
        {"/=", "dV"},
        {"%=", "rM"},
        {"&=", "aN"},
        {"|=", "oR"},
        {"^=", "eO"},
        {"<<", "ls"},
        {">>", "rs"},
        {"<<=", "lS"},
        {">>=", "rS"},
        {"==", "eq"},
        {"!=", "ne"},
        {"<", "lt"},
        {">", "gt"},
        {"<=", "le"},
        {">=", "ge"},
        {"<=>", "ss"},
        {"!", "nt"},
        {"~", "co"},
        {"++", "pp"},
        {"--", "mm"},
        {",", "cm"},
        {"&&", "aa"},
        {"||", "oo"},
        {"->", "pt"},
        {"->*", "pm"},
        {"()", "cl"},
        {"[]", "ix"},
        {"?", "qu"},
    };
    for (const auto& entry : kOperatorEncodings) {
        if (entry.suffix == suffix) {
            return entry.code;
        }
    }
    return std::nullopt;
}

struct ItaniumMangleContext;
void append_object_name_encoding(std::string& out,
                                 const ObjectType& object,
                                 ItaniumMangleContext& ctx);

void append_itanium_unqualified_name(std::string& out, std::string_view name) {
    if (auto op_encoding = itanium_operator_name_encoding(name)) {
        out.append(op_encoding->data(), op_encoding->size());
        return;
    }
    if (name.empty()) {
        out += '0';
        return;
    }
    append_source_name(out, name);
}

void append_itanium_unqualified_function_name(
    std::string& out,
    std::string_view name,
    const FunctionTemplateSpecializationInfo* specialization,
    const std::vector<std::string>& abi_tags,
    ItaniumMangleContext& ctx);

void append_itanium_unqualified_variable_name(
    std::string& out,
    std::string_view name,
    const VariableTemplateSpecializationInfo* specialization,
    const std::vector<std::string>& abi_tags,
    ItaniumMangleContext& ctx);

std::shared_ptr<ObjectType> owner_object_type_for_naming(QualType owner_type) {
    return desugar_type(owner_type).as_shared<ObjectType>();
}

std::optional<std::string> owner_record_name_for_spelling(QualType owner_type) {
    auto owner_object = owner_object_type_for_naming(owner_type);
    if (!owner_object) {
        return std::nullopt;
    }
    if (owner_object->is_class_template_specialization()) {
        if (auto* primary = owner_object->get_primary_class_template()) {
            if (auto* record = primary->record_decl()) {
                return record->name;
            }
        }
    }
    if (const auto* decl = dyn_cast<ObjectDecl>(owner_object->get_decl());
        decl && !decl->get_tag_name().empty()) {
        return decl->get_tag_name();
    }
    return std::nullopt;
}

std::vector<std::string_view> normalized_member_qualifier_components(
    std::string_view qualifier_prefix,
    QualType owner_type);

void append_itanium_function_name(std::string& out,
                                  std::string_view name,
                                  const FunctionType& fn,
                                  std::string_view qualifier_prefix,
                                  QualType owner_type,
                                  const FunctionTemplateSpecializationInfo* specialization,
                                  const std::vector<std::string>& abi_tags,
                                  ItaniumMangleContext& ctx) {
    auto owner_object = owner_object_type_for_naming(owner_type);
    if (qualifier_prefix.empty() && !owner_object) {
        append_itanium_unqualified_function_name(
            out, name, specialization, abi_tags, ctx);
        return;
    }
    auto components =
        normalized_member_qualifier_components(qualifier_prefix, owner_type);
    if (components.empty() && !owner_object) {
        append_itanium_unqualified_function_name(
            out, name, specialization, abi_tags, ctx);
        return;
    }
    size_t implicit_object_params =
        implicit_object_parameter_count(fn, qualifier_prefix, owner_type);
    out += 'N';
    if (implicit_object_params > 0 && !fn.parameters.empty()) {
        if (auto this_param =
                desugar_type(fn.parameters.front()).as_shared<PointerType>()) {
            append_qualifiers(out, this_param->pointed_type);
        }
        switch (fn.member_ref_qualifier) {
            case FunctionRefQualifierKind::LValue:
                out += 'R';
                break;
            case FunctionRefQualifierKind::RValue:
                out += 'O';
                break;
            case FunctionRefQualifierKind::None:
                break;
        }
    }
    for (auto component : components) {
        append_source_name(out, component);
    }
    if (owner_object) {
        append_object_name_encoding(out, *owner_object, ctx);
    }
    append_itanium_unqualified_function_name(
        out, name, specialization, abi_tags, ctx);
    out += 'E';
}

void append_itanium_unqualified_or_nested_name(std::string& out,
                                               const std::string& name,
                                               std::string_view qualifier_prefix) {
    if (qualifier_prefix.empty()) {
        append_itanium_unqualified_name(out, name);
        return;
    }
    auto components = split_cxx_qualifier_prefix(qualifier_prefix);
    if (components.empty()) {
        append_itanium_unqualified_name(out, name);
        return;
    }
    out += 'N';
    for (auto component : components) {
        append_source_name(out, component);
    }
    append_itanium_unqualified_name(out, name);
    out += 'E';
}

void append_vendor_extended_type(std::string& out, const std::string& name) {
    out += 'u';
    append_source_name(out, name.empty() ? "unknown" : name);
}

void append_qualifiers(std::string& out, const QualType& qt) {
    if (qt.is_const()) {
        out += 'K';
    }
    if (qt.is_volatile()) {
        out += 'V';
    }
    if (qt.is_restrict()) {
        out += 'r';
    }
}

void append_substitution_reference(std::string& out, size_t index) {
    out += 'S';
    if (index == 0) {
        out += '_';
        return;
    }

    static constexpr char kDigits[] = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";
    size_t value = index - 1;
    std::string encoded;
    do {
        encoded.push_back(kDigits[value % 36]);
        value /= 36;
    } while (value != 0);
    std::reverse(encoded.begin(), encoded.end());
    out += encoded;
    out += '_';
}

void append_const_value_fragment(std::string& out, const ConstValue& value) {
    switch (value.kind) {
        case ConstValueKind::Invalid:
            out += '0';
            return;
        case ConstValueKind::Integer:
            if (!value.int_value.is_unsigned &&
                value.int_value.to_signed_i64() < 0) {
                out += 'n';
                out += std::to_string(-value.int_value.to_signed_i64());
            } else if (value.int_value.is_unsigned) {
                out += std::to_string(value.int_value.to_unsigned_u64());
            } else {
                out += std::to_string(value.int_value.to_signed_i64());
            }
            return;
        case ConstValueKind::Boolean:
            out += value.bool_value ? '1' : '0';
            return;
        case ConstValueKind::Floating:
            out += 'f';
            out += std::to_string(static_cast<double>(value.float_value.value));
            return;
        case ConstValueKind::NullPointer:
            out += "null";
            return;
        case ConstValueKind::Address:
            out += "ad";
            if (value.address_value.symbol &&
                !value.address_value.symbol->name.empty()) {
                append_source_name(out, value.address_value.symbol->name);
            } else {
                out += pointer_identity_string(value.address_value.symbol.get());
            }
            out += '_';
            out += std::to_string(value.address_value.byte_offset);
            return;
        case ConstValueKind::MemberPointer:
            out += value.member_pointer_value.is_function_member ? "mf" : "md";
            if (value.member_pointer_value.method_symbol &&
                !value.member_pointer_value.method_symbol->name.empty()) {
                append_source_name(out, value.member_pointer_value.method_symbol->name);
            } else {
                out += pointer_identity_string(
                    value.member_pointer_value.method_symbol.get());
            }
            out += '_';
            out += std::to_string(value.member_pointer_value.byte_offset);
            out += '_';
            out += std::to_string(value.member_pointer_value.virtual_slot_index);
            if (value.member_pointer_value.member_name) {
                out += '_';
                append_source_name(out, *value.member_pointer_value.member_name);
            }
            return;
        case ConstValueKind::Object:
            out += value.object_value &&
                    value.object_value->kind == ConstObjectValueKind::Record
                ? "ob"
                : "ar";
            if (!value.object_value) {
                out += '0';
                return;
            }
            out += std::to_string(value.object_value->elements.size());
            out += '_';
            for (const auto& element : value.object_value->elements) {
                append_const_value_fragment(out, element);
                out += '_';
            }
            return;
    }
}

struct ItaniumMangleContext {
    // The current MVP only needs the Itanium substitution subset that keeps
    // repeated user/compound types and repeated template prefixes ABI-stable.
    std::unordered_map<std::string, size_t> substitution_lookup;
    std::vector<std::string> substitutions;

    bool try_emit_substitution(std::string& out, const std::string& key) const {
        auto it = substitution_lookup.find(key);
        if (it == substitution_lookup.end()) {
            return false;
        }
        append_substitution_reference(out, it->second);
        return true;
    }

    void remember_substitution(std::string key) {
        if (key.empty() || substitution_lookup.contains(key)) {
            return;
        }
        size_t index = substitutions.size();
        substitutions.push_back(key);
        substitution_lookup.emplace(std::move(key), index);
    }
};

std::string template_specialization_key(const Decl* primary_template,
                                        std::string_view template_name,
                                        const std::vector<TemplateArgument>& arguments);

void append_template_argument_encoding(std::string& out,
                                       const TemplateArgument& argument,
                                       ItaniumMangleContext& ctx);

std::string function_template_prefix_substitution_key(
    const FunctionTemplateSpecializationInfo* specialization,
    std::string_view name) {
    std::string key = "function-template-prefix:";
    if (specialization && specialization->primary_template) {
        key += pointer_identity_string(specialization->primary_template);
    } else {
        key.append(name.data(), name.size());
    }
    return key;
}

std::string variable_template_prefix_substitution_key(
    const VariableTemplateSpecializationInfo* specialization,
    std::string_view name) {
    std::string key = "variable-template-prefix:";
    if (specialization && specialization->primary_template) {
        key += pointer_identity_string(specialization->primary_template);
    } else {
        key.append(name.data(), name.size());
    }
    return key;
}

void append_itanium_unqualified_function_name(
    std::string& out,
    std::string_view name,
    const FunctionTemplateSpecializationInfo* specialization,
    const std::vector<std::string>& abi_tags,
    ItaniumMangleContext& ctx) {
    append_itanium_unqualified_name(out, name);
    append_itanium_abi_tags(out, abi_tags);
    if (!specialization || !specialization->primary_template) {
        return;
    }
    ctx.remember_substitution(
        function_template_prefix_substitution_key(specialization, name));
    out += 'I';
    for (const auto& argument : specialization->arguments) {
        append_template_argument_encoding(out, argument, ctx);
    }
    out += 'E';
}

void append_itanium_unqualified_variable_name(
    std::string& out,
    std::string_view name,
    const VariableTemplateSpecializationInfo* specialization,
    const std::vector<std::string>& abi_tags,
    ItaniumMangleContext& ctx) {
    append_itanium_unqualified_name(out, name);
    append_itanium_abi_tags(out, abi_tags);
    if (!specialization || !specialization->primary_template) {
        return;
    }
    ctx.remember_substitution(
        variable_template_prefix_substitution_key(specialization, name));
    out += 'I';
    for (const auto& argument : specialization->arguments) {
        append_template_argument_encoding(out, argument, ctx);
    }
    out += 'E';
}

void append_type_substitution_key(std::string& out, QualType qt);

std::string type_substitution_key(QualType qt) {
    auto canonical = desugar_typedefs(qt);
    if (!canonical) {
        return {};
    }

    switch (canonical->kind) {
        case TypeKind::Builtin:
        case TypeKind::Placeholder:
        case TypeKind::Other:
        case TypeKind::Auto:
        case TypeKind::TypeofExpr:
        case TypeKind::DecltypeExpr:
            return {};
        default:
            break;
    }

    std::string out;
    append_type_substitution_key(out, canonical);
    return out;
}

void append_template_argument_substitution_key(std::string& out,
                                               const TemplateArgument& argument) {
    out += "arg:";
    switch (argument.kind) {
        case TemplateArgumentKind::Type:
            append_type_substitution_key(out, argument.type);
            return;
        case TemplateArgumentKind::Value:
            append_type_substitution_key(out, argument.value_type);
            out += ":";
            if (argument.is_dependent) {
                if (argument.referenced_parameter) {
                    out += "dep:";
                    out += std::to_string(
                        reinterpret_cast<uintptr_t>(argument.referenced_parameter));
                } else if (!argument.value_spelling.empty()) {
                    out += "sp:";
                    out += argument.value_spelling;
                } else {
                    out += "dep";
                }
                return;
            }
            switch (argument.value.kind) {
                case ConstValueKind::Invalid:
                    out += "invalid";
                    return;
                case ConstValueKind::Integer:
                    out += argument.value.int_value.is_unsigned ? "u:" : "s:";
                    out += argument.value.int_value.is_unsigned
                        ? std::to_string(argument.value.int_value.to_unsigned_u64())
                        : std::to_string(argument.value.int_value.to_signed_i64());
                    return;
                case ConstValueKind::Boolean:
                    out += argument.value.bool_value ? "true" : "false";
                    return;
                case ConstValueKind::Floating:
                    out += "f:";
                    out += std::to_string(
                        static_cast<double>(argument.value.float_value.value));
                    return;
                case ConstValueKind::NullPointer:
                    out += "null";
                    return;
                case ConstValueKind::Address:
                    out += "addr:";
                    out += std::to_string(
                        reinterpret_cast<uintptr_t>(
                            argument.value.address_value.symbol.get()));
                    out += ":";
                    out += std::to_string(argument.value.address_value.byte_offset);
                    return;
                case ConstValueKind::MemberPointer:
                    out += argument.value.member_pointer_value.is_function_member
                        ? "mfn:"
                        : "mdata:";
                    out += std::to_string(
                        reinterpret_cast<uintptr_t>(
                            argument.value.member_pointer_value.method_symbol.get()));
                    out += ":";
                    out += std::to_string(
                        argument.value.member_pointer_value.byte_offset);
                    return;
                case ConstValueKind::Object:
                    out += "obj:";
                    append_const_value_fragment(out, argument.value);
                    return;
            }
        case TemplateArgumentKind::Template:
            if (argument.is_dependent) {
                if (argument.referenced_parameter) {
                    out += "templ-dep:";
                    out += std::to_string(
                        reinterpret_cast<uintptr_t>(argument.referenced_parameter));
                } else if (!argument.template_name.empty()) {
                    out += "templ-name:";
                    out += argument.template_name;
                } else {
                    out += "templ-dep";
                }
                return;
            }
            if (const auto* canonical =
                    canonical_template_decl_identity(argument.template_decl)) {
                out += "templ:";
                out += pointer_identity_string(canonical);
                return;
            }
            out += "templ-invalid";
            return;
    }
}

std::string template_specialization_key(const Decl* primary_template,
                                        std::string_view template_name,
                                        const std::vector<TemplateArgument>& arguments) {
    std::string key = "class-template-specialization:";
    if (primary_template) {
        key += pointer_identity_string(primary_template);
    } else {
        key.append(template_name.data(), template_name.size());
    }
    key += "<";
    for (size_t idx = 0; idx < arguments.size(); ++idx) {
        if (idx > 0) {
            key += ",";
        }
        append_template_argument_substitution_key(key, arguments[idx]);
    }
    key += ">";
    return key;
}

void append_type_substitution_key(std::string& out, QualType qt) {
    auto canonical = desugar_typedefs(qt);
    if (!canonical) {
        out += "null";
        return;
    }

    out += "q";
    out += std::to_string(canonical.get_qualifiers());
    out += ":";

    auto raw = canonical.get_shared();
    switch (raw->kind) {
        case TypeKind::Builtin: {
            auto builtin = static_cast<BuiltinType*>(raw.get());
            out += "builtin:";
            out += std::to_string(static_cast<int>(builtin->builtin_kind));
            return;
        }
        case TypeKind::Pointer: {
            auto ptr = static_cast<PointerType*>(raw.get());
            out += "ptr(";
            append_type_substitution_key(out, ptr->pointed_type);
            out += ")";
            return;
        }
        case TypeKind::Reference: {
            auto ref = static_cast<ReferenceType*>(raw.get());
            out += ref->reference_kind == ReferenceKind::RValue ? "rref(" : "lref(";
            append_type_substitution_key(out, ref->referred_type);
            out += ")";
            return;
        }
        case TypeKind::MemberPointer: {
            auto mem_ptr = static_cast<MemberPointerType*>(raw.get());
            out += "mp(";
            append_type_substitution_key(out, mem_ptr->class_type);
            out += ")(";
            append_type_substitution_key(out, mem_ptr->member_type);
            out += ")";
            return;
        }
        case TypeKind::BlockPointer: {
            auto blk = static_cast<BlockPointerType*>(raw.get());
            out += "block(";
            append_type_substitution_key(out, blk->pointed_type);
            out += ")";
            return;
        }
        case TypeKind::Function: {
            auto fn = static_cast<FunctionType*>(raw.get());
            out += "fn(";
            append_type_substitution_key(out, fn->ret_type);
            out += ")(";
            for (size_t idx = 0; idx < fn->parameters.size(); ++idx) {
                if (idx > 0) {
                    out += ",";
                }
                append_type_substitution_key(out, fn->parameters[idx]);
            }
            out += ")";
            out += fn->is_variadic ? "var" : "fixed";
            out += fn->has_prototype ? ":proto" : ":noprototype";
            return;
        }
        case TypeKind::Array: {
            auto arr = static_cast<ArrayType*>(raw.get());
            out += "array(";
            append_type_substitution_key(out, arr->element_type);
            out += ")[";
            out += std::to_string(static_cast<int>(arr->size_kind));
            out += ":";
            if (arr->size.has_value()) {
                out += std::to_string(*arr->size);
            } else {
                out += "?";
            }
            out += "]";
            return;
        }
        case TypeKind::Object: {
            auto object = static_cast<ObjectType*>(raw.get());
            auto* decl = dyn_cast<ObjectDecl>(object->get_decl());
            if (object->is_class_template_specialization()) {
                out += template_specialization_key(
                    object->get_primary_class_template(),
                    decl ? decl->get_tag_name() : std::string_view("record"),
                    object->get_template_specialization_arguments());
                return;
            }
            out += "object:";
            const void* object_identity =
                object->get_decl()
                    ? static_cast<const void*>(object->get_decl())
                    : static_cast<const void*>(object);
            out += pointer_identity_string(object_identity);
            return;
        }
        case TypeKind::Enum: {
            auto enum_type = static_cast<EnumType*>(raw.get());
            out += "enum:";
            const void* enum_identity =
                enum_type->get_decl()
                    ? static_cast<const void*>(enum_type->get_decl())
                    : static_cast<const void*>(enum_type);
            out += pointer_identity_string(enum_identity);
            return;
        }
        case TypeKind::CppTypeInfo: {
            auto type_info = static_cast<CppTypeInfoType*>(raw.get());
            out += "cpp-type-info:";
            out += std::to_string(type_info->descriptor_width_bits);
            return;
        }
        case TypeKind::Vector: {
            auto vec = static_cast<VectorType*>(raw.get());
            out += "vector(";
            append_type_substitution_key(out, vec->element_type);
            out += "):";
            out += std::to_string(vec->total_bytes);
            return;
        }
        case TypeKind::Complex: {
            auto complex = static_cast<ComplexType*>(raw.get());
            out += "complex:";
            out += std::to_string(static_cast<int>(complex->element_type->builtin_kind));
            return;
        }
        case TypeKind::TemplateTypeParm: {
            auto parm = static_cast<TemplateTypeParmType*>(raw.get());
            out += "template-parm:";
            if (parm->parameter_decl) {
                out += pointer_identity_string(parm->parameter_decl);
            } else {
                out += std::to_string(parm->depth);
                out += ":";
                out += std::to_string(parm->index);
            }
            return;
        }
        case TypeKind::TemplateSpecialization: {
            auto specialization = static_cast<TemplateSpecializationType*>(raw.get());
            out += template_specialization_key(
                specialization->primary_template,
                specialization->template_name,
                specialization->arguments);
            return;
        }
        case TypeKind::DependentName: {
            auto dependent_name = static_cast<DependentNameType*>(raw.get());
            if (auto resolved_type = lookup_dependent_name_resolved_type(
                    dependent_name,
                    nullptr)) {
                append_type_substitution_key(
                    out,
                    resolved_type.with_qualifiers(canonical.get_qualifiers()));
                return;
            }
            out += "dependent-name:";
            out += dependent_name->to_string();
            return;
        }
        case TypeKind::Typedef: {
            auto typedef_type = static_cast<TypedefType*>(raw.get());
            append_type_substitution_key(out, typedef_type->underlying_type);
            return;
        }
        case TypeKind::BuiltinTypeTransform: {
            auto transform =
                static_cast<BuiltinTypeTransformType*>(raw.get());
            auto resolved = apply_builtin_type_transform(
                transform->transform_kind,
                transform->operand_type);
            if (resolved) {
                append_type_substitution_key(
                    out,
                    QualType(
                        resolved.get_shared(),
                        static_cast<uint8_t>(
                            canonical.get_qualifiers() |
                            resolved.get_qualifiers())));
                return;
            }
            out += "builtin-type-transform:";
            out += std::to_string(static_cast<int>(transform->transform_kind));
            out += "(";
            append_type_substitution_key(out, transform->operand_type);
            out += ")";
            return;
        }
        case TypeKind::BuiltinTypePackElement: {
            auto pack_element =
                static_cast<BuiltinTypePackElementType*>(raw.get());
            auto resolved =
                apply_builtin_type_pack_element(pack_element->arguments);
            if (resolved) {
                append_type_substitution_key(
                    out,
                    QualType(
                        resolved.get_shared(),
                        static_cast<uint8_t>(
                            canonical.get_qualifiers() |
                            resolved.get_qualifiers())));
                return;
            }
            out += "builtin-type-pack-element:<";
            for (size_t idx = 0; idx < pack_element->arguments.size(); ++idx) {
                if (idx > 0) {
                    out += ",";
                }
                append_template_argument_substitution_key(
                    out,
                    pack_element->arguments[idx]);
            }
            out += ">";
            return;
        }
        case TypeKind::Placeholder:
        case TypeKind::Other:
        case TypeKind::Auto:
        case TypeKind::TypeofExpr:
        case TypeKind::DecltypeExpr:
            break;
    }

    out += "kind:";
    out += to_string_type_kind(raw->kind);
}

std::string template_prefix_substitution_key(std::string_view template_name,
                                             const Decl* primary_template) {
    std::string key = "template-prefix:";
    if (primary_template) {
        key += pointer_identity_string(primary_template);
    } else {
        key.append(template_name.data(), template_name.size());
    }
    return key;
}

std::string_view class_template_name(const Decl* primary_template,
                                     std::string_view fallback_name) {
    if (auto* class_template = dyn_cast<ClassTemplateDecl>(primary_template)) {
        if (auto* record = class_template->record_decl()) {
            return record->name;
        }
    }
    return fallback_name;
}

void append_template_specialization_name(std::string& out,
                                         std::string_view template_name,
                                         const Decl* primary_template,
                                         const std::vector<TemplateArgument>& arguments,
                                         const std::vector<std::string>& abi_tags,
                                         ItaniumMangleContext& ctx) {
    std::string prefix_key =
        template_prefix_substitution_key(template_name, primary_template);
    if (!ctx.try_emit_substitution(out, prefix_key)) {
        append_source_name(out, template_name);
        append_itanium_abi_tags(out, abi_tags);
        ctx.remember_substitution(std::move(prefix_key));
    }
    out += 'I';
    for (const auto& argument : arguments) {
        append_template_argument_encoding(out, argument, ctx);
    }
    out += 'E';
}

void append_object_name_encoding(std::string& out,
                                 const ObjectType& object,
                                 ItaniumMangleContext& ctx) {
    auto* decl = dyn_cast<ObjectDecl>(object.get_decl());
    if (object.is_class_template_specialization()) {
        auto abi_tags =
            abi_tags_for_class_template_primary(object.get_primary_class_template());
        append_template_specialization_name(
            out,
            class_template_name(
                object.get_primary_class_template(),
                decl ? decl->get_tag_name() : std::string_view("record")),
            object.get_primary_class_template(),
            object.get_template_specialization_arguments(),
            abi_tags,
            ctx);
        return;
    }
    if (!decl) {
        append_vendor_extended_type(out, "record");
        return;
    }
    if (!decl->get_tag_name().empty()) {
        append_source_name(out, decl->get_tag_name());
        append_itanium_abi_tags(out, abi_tags_for_decl(*decl));
        return;
    }
    append_vendor_extended_type(out, "record");
}

void append_type_encoding(std::string& out, const QualType& qt, ItaniumMangleContext& ctx);

void append_template_argument_encoding(std::string& out,
                                       const TemplateArgument& argument,
                                       ItaniumMangleContext& ctx) {
    switch (argument.kind) {
        case TemplateArgumentKind::Type:
            append_type_encoding(out, argument.type, ctx);
            return;
        case TemplateArgumentKind::Value:
            out += 'L';
            append_type_encoding(out, argument.value_type, ctx);
            append_const_value_fragment(out, argument.value);
            out += 'E';
            return;
        case TemplateArgumentKind::Template:
            // For now, we only need deterministic handling for the generalized
            // template-argument model. Full template-template argument ABI
            // parity is deferred to broader specialization work.
            if (argument.is_dependent || !argument.template_decl) {
                append_vendor_extended_type(out, "ttarg");
                return;
            }
            if (auto* alias_template =
                    dyn_cast<AliasTemplateDecl>(
                        const_cast<TemplateDecl*>(argument.template_decl))) {
                append_source_name(out, alias_template->alias_decl()->name);
                return;
            }
            if (auto* class_template =
                    dyn_cast<ClassTemplateDecl>(
                        const_cast<TemplateDecl*>(argument.template_decl))) {
                append_source_name(out, class_template->record_decl()->name);
                return;
            }
            if (auto* function_template =
                    dyn_cast<FunctionTemplateDecl>(
                        const_cast<TemplateDecl*>(argument.template_decl))) {
                append_itanium_unqualified_name(
                    out,
                    function_template->function_decl()->name);
                return;
            }
            append_vendor_extended_type(out, "ttarg");
            return;
    }
}

void append_function_type_encoding(std::string& out,
                                   const FunctionType& fn,
                                   ItaniumMangleContext& ctx) {
    out += 'F';
    append_type_encoding(out, fn.ret_type, ctx);
    if (fn.parameters.empty() || is_single_void_parameter(fn)) {
        out += 'v';
    } else {
        for (const auto& param : fn.parameters) {
            append_type_encoding(out, decay_parameter_type_for_mangling(param), ctx);
        }
    }
    if (fn.is_variadic) {
        out += 'z';
    }
    out += 'E';
}

void append_builtin_type_encoding(std::string& out, BuiltinTypes kind) {
    switch (kind) {
        case BuiltinTypes::Void: out += 'v'; return;
        case BuiltinTypes::NullPtr: out += "Dn"; return;
        case BuiltinTypes::Bool: out += 'b'; return;
        case BuiltinTypes::Char: out += 'c'; return;
        case BuiltinTypes::SChar: out += 'a'; return;
        case BuiltinTypes::UChar: out += 'h'; return;
        case BuiltinTypes::WChar: out += 'w'; return;
        case BuiltinTypes::Char16: out += "Ds"; return;
        case BuiltinTypes::Char32: out += "Di"; return;
        case BuiltinTypes::Short: out += 's'; return;
        case BuiltinTypes::UShort: out += 't'; return;
        case BuiltinTypes::Int: out += 'i'; return;
        case BuiltinTypes::UInt: out += 'j'; return;
        case BuiltinTypes::Long: out += 'l'; return;
        case BuiltinTypes::ULong: out += 'm'; return;
        case BuiltinTypes::LongLong: out += 'x'; return;
        case BuiltinTypes::ULongLong: out += 'y'; return;
        case BuiltinTypes::Int128: out += 'n'; return;
        case BuiltinTypes::UInt128: out += 'o'; return;
        case BuiltinTypes::Float16:
            append_vendor_extended_type(out, "Float16");
            return;
        case BuiltinTypes::Float: out += 'f'; return;
        case BuiltinTypes::Double: out += 'd'; return;
        case BuiltinTypes::LongDouble: out += 'e'; return;
    }
    append_vendor_extended_type(out, "builtin");
}

void append_type_encoding(std::string& out, const QualType& qt, ItaniumMangleContext& ctx) {
    if (!qt) {
        append_vendor_extended_type(out, "null");
        return;
    }

    auto canonical = desugar_typedefs(qt);
    if (!canonical) {
        append_vendor_extended_type(out, "null");
        return;
    }
    if (canonical.get_shared() != qt.get_shared() ||
        canonical.get_qualifiers() != qt.get_qualifiers()) {
        append_type_encoding(out, canonical, ctx);
        return;
    }

    std::string substitution_key = type_substitution_key(canonical);
    if (!substitution_key.empty() && ctx.try_emit_substitution(out, substitution_key)) {
        return;
    }

    append_qualifiers(out, canonical);
    switch (canonical->kind) {
        case TypeKind::Reference: {
            auto ref = canonical.as_shared<ReferenceType>();
            out += (ref && ref->reference_kind == ReferenceKind::RValue) ? 'O' : 'R';
            append_type_encoding(out, ref ? ref->referred_type : QualType(nullptr), ctx);
            break;
        }
        case TypeKind::Builtin: {
            auto builtin = canonical.as_shared<BuiltinType>();
            if (!builtin) {
                append_vendor_extended_type(out, "builtin");
                return;
            }
            append_builtin_type_encoding(out, builtin->builtin_kind);
            return;
        }
        case TypeKind::Pointer: {
            auto ptr = canonical.as_shared<PointerType>();
            out += 'P';
            append_type_encoding(out, ptr ? ptr->pointed_type : QualType(nullptr), ctx);
            break;
        }
        case TypeKind::Function: {
            auto fn = canonical.as_shared<FunctionType>();
            if (!fn) {
                append_vendor_extended_type(out, "func");
                return;
            }
            append_function_type_encoding(out, *fn, ctx);
            break;
        }
        case TypeKind::Array: {
            auto arr = canonical.as_shared<ArrayType>();
            out += 'A';
            if (arr && arr->size_kind == ArraySizeKind::Constant && arr->size.has_value()) {
                out += std::to_string(arr->size.value());
            }
            out += '_';
            append_type_encoding(out, arr ? arr->element_type : QualType(nullptr), ctx);
            break;
        }
        case TypeKind::Object: {
            auto obj = canonical.as_shared<ObjectType>();
            if (!obj) {
                append_vendor_extended_type(out, "record");
                return;
            }
            append_object_name_encoding(out, *obj, ctx);
            break;
        }
        case TypeKind::Enum: {
            auto en = canonical.as_shared<EnumType>();
            const TagDecl* decl = en ? en->get_decl() : nullptr;
            if (decl && !decl->get_tag_name().empty()) {
                append_source_name(out, decl->get_tag_name());
            } else {
                append_vendor_extended_type(out, "enum");
            }
            break;
        }
        case TypeKind::TemplateSpecialization: {
            auto specialization = canonical.as_shared<TemplateSpecializationType>();
            if (!specialization) {
                append_vendor_extended_type(out, "template-specialization");
                return;
            }
            append_template_specialization_name(
                out,
                class_template_name(
                    specialization->primary_template,
                    specialization->template_name),
                specialization->primary_template,
                specialization->arguments,
                abi_tags_for_class_template_primary(specialization->primary_template),
                ctx);
            break;
        }
        case TypeKind::TemplateTypeParm: {
            auto parm = canonical.as_shared<TemplateTypeParmType>();
            out += 'T';
            if (!parm || parm->index == 0) {
                out += '_';
            } else {
                out += std::to_string(parm->index - 1);
                out += '_';
            }
            break;
        }
        case TypeKind::DependentName: {
            auto dependent_name = canonical.as_shared<DependentNameType>();
            if (auto resolved_type = dependent_name
                    ? lookup_dependent_name_resolved_type(
                          dependent_name.get(),
                          nullptr)
                    : nullptr) {
                append_type_encoding(
                    out,
                    resolved_type,
                    ctx);
                break;
            }
            append_vendor_extended_type(out, "dependent-name");
            return;
        }
        default:
            append_vendor_extended_type(out, to_string_type_kind(canonical->kind));
            return;
    }

    if (!substitution_key.empty()) {
        ctx.remember_substitution(std::move(substitution_key));
    }
}

void append_bare_function_type(std::string& out,
                               const FunctionType& fn,
                               ItaniumMangleContext& ctx) {
    if (!fn.has_prototype || fn.parameters.empty() || is_single_void_parameter(fn)) {
        out += 'v';
    } else {
        for (const auto& param : fn.parameters) {
            append_type_encoding(out, decay_parameter_type_for_mangling(param), ctx);
        }
    }
    if (fn.is_variadic) {
        out += 'z';
    }
}

void append_bare_function_type(std::string& out,
                               const FunctionType& fn,
                               size_t parameter_start_index,
                               ItaniumMangleContext& ctx) {
    if (!fn.has_prototype || parameter_start_index >= fn.parameters.size()) {
        out += 'v';
        if (fn.is_variadic) {
            out += 'z';
        }
        return;
    }
    bool emitted_parameter = false;
    for (size_t idx = parameter_start_index; idx < fn.parameters.size(); ++idx) {
        const auto& param = fn.parameters[idx];
        if (!param) {
            continue;
        }
        // `void` in a singleton position denotes an empty parameter list.
        if (param->isVoid() && idx == parameter_start_index &&
            fn.parameters.size() == parameter_start_index + 1) {
            continue;
        }
        append_type_encoding(out, decay_parameter_type_for_mangling(param), ctx);
        emitted_parameter = true;
    }
    if (!emitted_parameter) {
        out += 'v';
    }
    if (fn.is_variadic) {
        out += 'z';
    }
}

void append_bare_function_type_with_return(std::string& out,
                                           const FunctionType& fn,
                                           ItaniumMangleContext& ctx) {
    append_type_encoding(out, fn.ret_type, ctx);
    append_bare_function_type(out, fn, ctx);
}

void append_bare_function_type_with_return(std::string& out,
                                           const FunctionType& fn,
                                           size_t parameter_start_index,
                                           ItaniumMangleContext& ctx) {
    append_type_encoding(out, fn.ret_type, ctx);
    append_bare_function_type(out, fn, parameter_start_index, ctx);
}

std::optional<std::string_view> last_qualifier_component(std::string_view qualifier_prefix) {
    if (qualifier_prefix.empty()) {
        return std::nullopt;
    }
    auto components = split_cxx_qualifier_prefix(qualifier_prefix);
    if (components.empty()) {
        return std::nullopt;
    }
    return components.back();
}

std::vector<std::string_view> normalized_member_qualifier_components(
    std::string_view qualifier_prefix,
    QualType owner_type) {
    auto components = split_cxx_qualifier_prefix(qualifier_prefix);
    auto owner_name = owner_record_name_for_spelling(owner_type);
    if (!owner_name.has_value() || components.empty()) {
        return components;
    }
    if (components.back() == *owner_name) {
        components.pop_back();
    }
    return components;
}

size_t implicit_object_parameter_count(const FunctionType& fn,
                                      std::string_view qualifier_prefix,
                                      QualType owner_type) {
    if (fn.parameters.empty()) {
        return 0;
    }
    auto first_param = desugar_type(fn.parameters.front()).as_shared<PointerType>();
    if (!first_param || !first_param->pointed_type) {
        return 0;
    }
    auto pointee_record = desugar_type(first_param->pointed_type).as_shared<ObjectType>();
    if (!pointee_record) {
        return 0;
    }
    auto owner_object = owner_object_type_for_naming(owner_type);
    if (owner_object) {
        if (owner_object.get() == pointee_record.get()) {
            return 1;
        }
        if (owner_object->get_decl() && pointee_record->get_decl() &&
            owner_object->get_decl() == pointee_record->get_decl()) {
            return 1;
        }
    }
    if (auto class_component = last_qualifier_component(qualifier_prefix);
        class_component.has_value()) {
        const TagDecl* record_decl = pointee_record->get_decl();
        if (!record_decl) {
            return 0;
        }
        if (record_decl->get_tag_name() == std::string(*class_component)) {
            return 1;
        }
    }
    return 0;
}

void append_itanium_constructor_name(std::string& out,
                                     std::string_view qualifier_prefix,
                                     QualType owner_type,
                                     const std::vector<std::string>& abi_tags,
                                     ItaniumMangleContext& ctx) {
    auto components =
        normalized_member_qualifier_components(qualifier_prefix, owner_type);
    auto owner_object = owner_object_type_for_naming(owner_type);
    if (components.empty() && !owner_object) {
        // Fallback to complete-object constructor code without a nested prefix.
        out += "C1";
        append_itanium_abi_tags(out, abi_tags);
        return;
    }
    out += 'N';
    for (auto component : components) {
        append_source_name(out, component);
    }
    if (owner_object) {
        append_object_name_encoding(out, *owner_object, ctx);
    }
    // Itanium ctor-name: use complete-object constructor form.
    out += "C1";
    append_itanium_abi_tags(out, abi_tags);
    out += 'E';
}

void append_itanium_destructor_name(std::string& out,
                                    std::string_view qualifier_prefix,
                                    QualType owner_type,
                                    const std::vector<std::string>& abi_tags,
                                    ItaniumMangleContext& ctx) {
    auto components =
        normalized_member_qualifier_components(qualifier_prefix, owner_type);
    auto owner_object = owner_object_type_for_naming(owner_type);
    if (components.empty() && !owner_object) {
        // Fallback to complete-object destructor code without a nested prefix.
        out += "D1";
        append_itanium_abi_tags(out, abi_tags);
        return;
    }
    out += 'N';
    for (auto component : components) {
        append_source_name(out, component);
    }
    if (owner_object) {
        append_object_name_encoding(out, *owner_object, ctx);
    }
    // Itanium dtor-name: use complete-object destructor form.
    out += "D1";
    append_itanium_abi_tags(out, abi_tags);
    out += 'E';
}

enum class CxxSpecialMemberKind {
    None,
    Constructor,
    Destructor
};

std::string mangle_function_entity_itanium(const std::string& name,
                                           const FunctionType& fn,
                                           std::string_view qualifier_prefix,
                                           QualType owner_type,
                                           CxxSpecialMemberKind special_kind,
                                           const FunctionTemplateSpecializationInfo* specialization,
                                           const std::vector<std::string>& abi_tags,
                                           const FunctionType* specialization_pattern_type) {
    std::string out = "_Z";
    ItaniumMangleContext ctx;
    if (special_kind == CxxSpecialMemberKind::Constructor) {
        append_itanium_constructor_name(
            out, qualifier_prefix, owner_type, abi_tags, ctx);
        size_t param_start =
            implicit_object_parameter_count(fn, qualifier_prefix, owner_type);
        append_bare_function_type(out, fn, param_start, ctx);
        return out;
    }
    if (special_kind == CxxSpecialMemberKind::Destructor) {
        append_itanium_destructor_name(
            out, qualifier_prefix, owner_type, abi_tags, ctx);
        size_t param_start =
            implicit_object_parameter_count(fn, qualifier_prefix, owner_type);
        append_bare_function_type(out, fn, param_start, ctx);
        return out;
    }
    size_t param_start =
        implicit_object_parameter_count(fn, qualifier_prefix, owner_type);
    append_itanium_function_name(
        out,
        name,
        fn,
        qualifier_prefix,
        owner_type,
        specialization,
        abi_tags,
        ctx);
    if (specialization && specialization_pattern_type) {
        append_bare_function_type_with_return(
            out,
            *specialization_pattern_type,
            param_start,
            ctx);
    } else {
        append_bare_function_type(out, fn, param_start, ctx);
    }
    return out;
}

std::string mangle_variable_entity_itanium(
    const std::string& name,
    std::string_view qualifier_prefix,
    QualType owner_type,
    const VariableTemplateSpecializationInfo* specialization,
    const std::vector<std::string>& abi_tags) {
    std::string out = "_Z";
    ItaniumMangleContext ctx;
    auto owner_object = owner_object_type_for_naming(owner_type);
    if (qualifier_prefix.empty() && !owner_object) {
        append_itanium_unqualified_variable_name(
            out, name, specialization, abi_tags, ctx);
        return out;
    }

    auto components =
        normalized_member_qualifier_components(qualifier_prefix, owner_type);
    if (components.empty() && !owner_object) {
        append_itanium_unqualified_variable_name(
            out, name, specialization, abi_tags, ctx);
        return out;
    }

    out += 'N';
    for (auto component : components) {
        append_source_name(out, component);
    }
    if (owner_object) {
        append_object_name_encoding(out, *owner_object, ctx);
    }
    append_itanium_unqualified_variable_name(
        out, name, specialization, abi_tags, ctx);
    out += 'E';
    return out;
}

bool symbol_looks_like_constructor(const Symbol& sym, std::string_view spelling) {
    if (sym.function_definition && isa<CppConstructorDecl>(sym.function_definition)) {
        return true;
    }
    if (auto owner_name = owner_record_name_for_spelling(get_symbol_owner_record_type(&sym));
        owner_name.has_value()) {
        return spelling == *owner_name;
    }
    auto* qualifier_prefix = get_symbol_cxx_qualifier_prefix(&sym);
    if (!qualifier_prefix || qualifier_prefix->empty()) {
        return false;
    }
    auto class_component = last_qualifier_component(*qualifier_prefix);
    if (!class_component.has_value()) {
        return false;
    }
    return spelling == *class_component;
}

bool symbol_looks_like_destructor(const Symbol& sym, std::string_view spelling) {
    if (sym.function_definition && isa<CppDestructorDecl>(sym.function_definition)) {
        return true;
    }
    if (auto owner_name = owner_record_name_for_spelling(get_symbol_owner_record_type(&sym));
        owner_name.has_value()) {
        std::string expected = "~";
        expected += *owner_name;
        return spelling == expected;
    }
    auto* qualifier_prefix = get_symbol_cxx_qualifier_prefix(&sym);
    if (!qualifier_prefix || qualifier_prefix->empty()) {
        return false;
    }
    auto class_component = last_qualifier_component(*qualifier_prefix);
    if (!class_component.has_value()) {
        return false;
    }
    std::string expected = "~";
    expected += std::string(*class_component);
    return spelling == expected;
}

bool decl_is_constructor(const FuncDecl& decl) {
    return isa<CppConstructorDecl>(&decl);
}

bool decl_is_destructor(const FuncDecl& decl) {
    return isa<CppDestructorDecl>(&decl);
}

const FunctionType* specialization_pattern_function_type(
    const FunctionTemplateSpecializationInfo* specialization) {
    if (!specialization || !specialization->primary_template) {
        return nullptr;
    }
    const auto* pattern = specialization->primary_template->function_decl();
    if (!pattern) {
        return nullptr;
    }
    return QualType(pattern->type).as<FunctionType>();
}

LanguageLinkage effective_language_linkage_for_naming(LanguageLinkage linkage,
                                                      const AbiPolicy& policy) {
    if (linkage != LanguageLinkage::None) {
        return linkage;
    }
    return policy.mangling == ManglingKind::C
        ? LanguageLinkage::C
        : LanguageLinkage::CXX;
}
} // namespace

std::string mangle_function_name_itanium(const std::string& name,
                                         const QualType& function_type,
                                         const AbiPolicy& policy) {
    (void)policy;
    auto fn = function_type.as_shared<FunctionType>();
    if (!fn) {
        std::string out = "_Z";
        append_itanium_unqualified_or_nested_name(out, name, "");
        out += 'v';
        return out;
    }
    return mangle_function_entity_itanium(
        name,
        *fn,
        "",
        QualType(),
        CxxSpecialMemberKind::None,
        nullptr,
        {},
        nullptr);
}

std::string mangle_function_name_itanium(const FuncDecl& decl, const AbiPolicy& policy) {
    (void)policy;
    auto fn = QualType(decl.type).as_shared<FunctionType>();
    if (!fn) {
        std::string out = "_Z";
        append_itanium_unqualified_or_nested_name(
            out,
            decl.name,
            get_func_decl_cxx_qualifier_prefix(&decl)
                ? std::string_view(*get_func_decl_cxx_qualifier_prefix(&decl))
                : std::string_view{});
        out += 'v';
        return out;
    }
    std::string_view qualifier_prefix =
        get_func_decl_cxx_qualifier_prefix(&decl)
            ? std::string_view(*get_func_decl_cxx_qualifier_prefix(&decl))
            : std::string_view{};
    QualType owner_type = get_func_decl_owner_record_type(&decl);
    CxxSpecialMemberKind special_kind = CxxSpecialMemberKind::None;
    if (decl_is_constructor(decl)) {
        special_kind = CxxSpecialMemberKind::Constructor;
    } else if (decl_is_destructor(decl)) {
        special_kind = CxxSpecialMemberKind::Destructor;
    }
    const auto* specialization =
        get_func_decl_function_template_specialization(&decl);
    auto abi_tags = abi_tags_for_function_decl(decl);
    return mangle_function_entity_itanium(
        decl.name,
        *fn,
        qualifier_prefix,
        owner_type,
        special_kind,
        specialization,
        abi_tags,
        specialization_pattern_function_type(specialization));
}

std::string mangle_type_name_itanium(const QualType& type) {
    std::string out;
    ItaniumMangleContext ctx;
    append_type_encoding(out, type, ctx);
    return out;
}

std::string mangle_function_name_for_policy(const std::string& name,
                                            const QualType& function_type,
                                            const AbiPolicy& policy) {
    switch (policy.mangling) {
        case ManglingKind::Itanium:
            return mangle_function_name_itanium(name, function_type, policy);
        case ManglingKind::Msvc:
        case ManglingKind::C:
        default:
            return name;
    }
}

std::string mangle_function_name_for_policy(const FuncDecl& decl, const AbiPolicy& policy) {
    switch (policy.mangling) {
        case ManglingKind::Itanium:
            return mangle_function_name_itanium(decl, policy);
        case ManglingKind::Msvc:
        case ManglingKind::C:
        default:
            return decl.name;
    }
}

std::string mangle_function_symbol_name_for_policy(const Symbol& sym,
                                                   std::string_view fallback_spelling,
                                                   const AbiPolicy& policy) {
    std::string spelling = sym.name;
    if (spelling.empty()) {
        spelling = std::string(fallback_spelling);
    }
    switch (policy.mangling) {
        case ManglingKind::Itanium: {
            auto fn = sym.type.as_shared<FunctionType>();
            if (!fn) {
                std::string out = "_Z";
                append_itanium_unqualified_or_nested_name(
                    out,
                    spelling,
                    get_symbol_cxx_qualifier_prefix(&sym)
                        ? std::string_view(*get_symbol_cxx_qualifier_prefix(&sym))
                        : std::string_view{});
                out += 'v';
                return out;
            }
            std::string_view qualifier_prefix =
                get_symbol_cxx_qualifier_prefix(&sym)
                    ? std::string_view(*get_symbol_cxx_qualifier_prefix(&sym))
                    : std::string_view{};
            CxxSpecialMemberKind special_kind = CxxSpecialMemberKind::None;
            if (symbol_looks_like_constructor(sym, spelling)) {
                special_kind = CxxSpecialMemberKind::Constructor;
            } else if (symbol_looks_like_destructor(sym, spelling)) {
                special_kind = CxxSpecialMemberKind::Destructor;
            }
            const auto* specialization =
                get_symbol_function_template_specialization(&sym);
            return mangle_function_entity_itanium(
                spelling,
                *fn,
                qualifier_prefix,
                get_symbol_owner_record_type(&sym),
                special_kind,
                specialization,
                abi_tags_for_symbol(sym),
                specialization_pattern_function_type(specialization));
        }
        case ManglingKind::Msvc:
        case ManglingKind::C:
        default:
            return spelling;
    }
}

std::string mangle_variable_decl_name_for_policy(const VariableDecl& decl,
                                                 const AbiPolicy& policy) {
    std::string spelling = decl.name;
    if (spelling.empty() && decl.sym) {
        spelling = decl.sym->name;
    }
    switch (policy.mangling) {
        case ManglingKind::Itanium: {
            std::string_view qualifier_prefix{};
            QualType owner_type;
            if (decl.sym) {
                if (auto* prefix = get_symbol_cxx_qualifier_prefix(decl.sym.get())) {
                    qualifier_prefix = *prefix;
                }
                owner_type = get_symbol_owner_record_type(decl.sym.get());
            }
            const auto* specialization =
                get_variable_decl_variable_template_specialization(&decl);
            return mangle_variable_entity_itanium(
                spelling,
                qualifier_prefix,
                owner_type,
                specialization,
                abi_tags_for_variable_decl(decl));
        }
        case ManglingKind::Msvc:
        case ManglingKind::C:
        default:
            return spelling;
    }
}

std::string mangle_variable_symbol_name_for_policy(const Symbol& sym,
                                                   std::string_view fallback_spelling,
                                                   const AbiPolicy& policy) {
    std::string spelling = sym.name;
    if (spelling.empty()) {
        spelling = std::string(fallback_spelling);
    }
    switch (policy.mangling) {
        case ManglingKind::Itanium:
            {
            const auto* specialization =
                get_symbol_variable_template_specialization(&sym);
            return mangle_variable_entity_itanium(
                spelling,
                get_symbol_cxx_qualifier_prefix(&sym)
                    ? std::string_view(*get_symbol_cxx_qualifier_prefix(&sym))
                    : std::string_view{},
                get_symbol_owner_record_type(&sym),
                specialization,
                abi_tags_for_symbol(sym));
            }
        case ManglingKind::Msvc:
        case ManglingKind::C:
        default:
            return spelling;
    }
}

ResolvedFunctionName resolve_function_linkage_name(
    const std::string& name,
    const QualType& function_type,
    LanguageLinkage language_linkage,
    const AbiPolicy& policy,
    const std::string* asm_label) {
    if (asm_label) {
        return ResolvedFunctionName{*asm_label, true};
    }

    if (name == "main") {
        return ResolvedFunctionName{"main", false};
    }

    LanguageLinkage effective = effective_language_linkage_for_naming(
        language_linkage, policy);
    if (effective == LanguageLinkage::C) {
        return ResolvedFunctionName{name, false};
    }

    return ResolvedFunctionName{
        mangle_function_name_for_policy(name, function_type, policy),
        false
    };
}

ResolvedFunctionName resolve_function_linkage_name(const FuncDecl& decl,
                                                   const AbiPolicy& policy) {
    if (decl.asm_label) {
        return ResolvedFunctionName{*decl.asm_label, true};
    }
    if (decl.name == "main") {
        return ResolvedFunctionName{"main", false};
    }
    LanguageLinkage effective = effective_language_linkage_for_naming(
        decl.get_language_linkage(), policy);
    if (effective == LanguageLinkage::C) {
        return ResolvedFunctionName{decl.name, false};
    }
    return ResolvedFunctionName{
        mangle_function_name_for_policy(decl, policy),
        false
    };
}

ResolvedFunctionName resolve_function_linkage_name(const Symbol& sym,
                                                   const AbiPolicy& policy,
                                                   std::string_view fallback_spelling) {
    const std::string* asm_label = sym.asm_label.has_value()
        ? &sym.asm_label.value()
        : nullptr;
    std::string spelling = sym.name;
    if (spelling.empty()) {
        spelling = std::string(fallback_spelling);
    }
    if (asm_label) {
        return ResolvedFunctionName{*asm_label, true};
    }
    if (spelling == "main") {
        return ResolvedFunctionName{"main", false};
    }
    LanguageLinkage effective = effective_language_linkage_for_naming(
        sym.get_language_linkage(), policy);
    if (effective == LanguageLinkage::C) {
        return ResolvedFunctionName{spelling, false};
    }
    return ResolvedFunctionName{
        mangle_function_symbol_name_for_policy(sym, spelling, policy),
        false
    };
}

ResolvedVariableName resolve_variable_linkage_name(const VariableDecl& decl,
                                                   const AbiPolicy& policy) {
    std::string spelling = decl.name;
    if (spelling.empty() && decl.sym) {
        spelling = decl.sym->name;
    }
    if (decl.asm_label) {
        return ResolvedVariableName{*decl.asm_label, true};
    }

    LanguageLinkage language_linkage = decl.get_language_linkage();
    if (language_linkage == LanguageLinkage::None && decl.sym) {
        language_linkage = decl.sym->get_language_linkage();
    }
    LanguageLinkage effective =
        effective_language_linkage_for_naming(language_linkage, policy);
    if (effective == LanguageLinkage::C) {
        return ResolvedVariableName{spelling, false};
    }

    return ResolvedVariableName{
        mangle_variable_decl_name_for_policy(decl, policy),
        false};
}

ResolvedVariableName resolve_variable_linkage_name(
    const Symbol& sym,
    const AbiPolicy& policy,
    std::string_view fallback_spelling) {
    const std::string* asm_label =
        sym.asm_label.has_value() ? &sym.asm_label.value() : nullptr;
    std::string spelling = sym.name;
    if (spelling.empty()) {
        spelling = std::string(fallback_spelling);
    }
    if (asm_label) {
        return ResolvedVariableName{*asm_label, true};
    }
    LanguageLinkage effective = effective_language_linkage_for_naming(
        sym.get_language_linkage(), policy);
    if (effective == LanguageLinkage::C) {
        return ResolvedVariableName{spelling, false};
    }
    return ResolvedVariableName{
        mangle_variable_symbol_name_for_policy(sym, spelling, policy),
        false};
}
