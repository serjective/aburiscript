#include "mangle_cir.h"

#include "../numeric/floating_point.h"

#include <algorithm>
#include <cstdint>
#include <string>
#include <variant>
#include <vector>

namespace aburi::abi {

namespace {

constexpr std::string_view anonymous_namespace_source_name = "(anonymous namespace)";

const char* itanium_operator_code(std::string_view spelling, bool unary) {
    if (spelling == "new") return "nw";
    if (spelling == "new[]") return "na";
    if (spelling == "delete") return "dl";
    if (spelling == "delete[]") return "da";
    if (spelling == "co_await") return "aw";
    if (spelling == "+") return unary ? "ps" : "pl";
    if (spelling == "-") return unary ? "ng" : "mi";
    if (spelling == "*") return unary ? "de" : "ml";
    if (spelling == "/") return "dv";
    if (spelling == "%") return "rm";
    if (spelling == "^") return "eo";
    if (spelling == "&") return unary ? "ad" : "an";
    if (spelling == "|") return "or";
    if (spelling == "~") return "co";
    if (spelling == "!") return "nt";
    if (spelling == "=") return "aS";
    if (spelling == "<") return "lt";
    if (spelling == ">") return "gt";
    if (spelling == "+=") return "pL";
    if (spelling == "-=") return "mI";
    if (spelling == "*=") return "mL";
    if (spelling == "/=") return "dV";
    if (spelling == "%=") return "rM";
    if (spelling == "^=") return "eO";
    if (spelling == "&=") return "aN";
    if (spelling == "|=") return "oR";
    if (spelling == "<<") return "ls";
    if (spelling == ">>") return "rs";
    if (spelling == "<<=") return "lS";
    if (spelling == ">>=") return "rS";
    if (spelling == "==") return "eq";
    if (spelling == "!=") return "ne";
    if (spelling == "<=") return "le";
    if (spelling == ">=") return "ge";
    if (spelling == "<=>") return "ss";
    if (spelling == "&&") return "aa";
    if (spelling == "||") return "oo";
    if (spelling == "++") return "pp";
    if (spelling == "--") return "mm";
    if (spelling == ",") return "cm";
    if (spelling == "->*") return "pm";
    if (spelling == "->") return "pt";
    if (spelling == "()") return "cl";
    if (spelling == "[]") return "ix";
    return nullptr;
}

const char* itanium_operator_code(cir::OperatorFunctionSpelling spelling,
                                  bool unary) {
    return itanium_operator_code(
        cir::operator_function_spelling_text(spelling), unary);
}

std::string integer_template_argument_spelling(
    const cir::TemplateArgument& argument) {
    std::string value = argument.integer_value.decimal();
    if (!value.empty() && value.front() == '-') {
        value.front() = 'n';
    }
    return value;
}

class ItaniumMangler {
public:
    explicit ItaniumMangler(const cir::File& file) : file_(file) {}

    std::string conversion_operator_terminal(cir::TypeId function_type) {
        cir::TypeId resolved = file_.resolved_type(function_type);
        const auto* payload = file_.valid(resolved)
            ? std::get_if<cir::FunctionTypePayload>(
                  &file_.type_payload(resolved))
            : nullptr;
        if (!payload || !payload->return_type.type.valid()) {
            return {};
        }
        ItaniumMangler nested(file_);
        nested.out_ = "cv";
        nested.encode_type(payload->return_type);
        return nested.out_;
    }

    std::string conversion_operator_terminal(cir::EntityId entity_id) {
        if (!entity_id.valid() || !file_.valid(entity_id)) {
            return {};
        }
        cir::TypeRef return_type{};
        if (const cir::RecordMethodFact* fact = file_.method_fact(entity_id)) {
            cir::TypeId declared = file_.resolved_type(fact->type.type);
            if (file_.valid(declared) &&
                file_.type(declared).kind == cir::TypeKind::Function) {
                if (const auto* payload =
                        std::get_if<cir::FunctionTypePayload>(
                            &file_.type_payload(declared))) {
                    return_type = payload->return_type;
                }
            }
        }
        if (!return_type.type.valid()) {
            cir::TypeId entity_type =
                file_.resolved_type(file_.entity(entity_id).type);
            if (file_.valid(entity_type) &&
                file_.type(entity_type).kind == cir::TypeKind::Function) {
                if (const auto* payload =
                        std::get_if<cir::FunctionTypePayload>(
                            &file_.type_payload(entity_type))) {
                    return_type = payload->return_type;
                }
            }
        }
        if (!return_type.type.valid()) {
            return {};
        }
        ItaniumMangler nested(file_);
        nested.out_ = "cv";
        nested.encode_type(return_type);
        return nested.out_;
    }

    std::string mangle(cir::EntityId entity_id) {
        const cir::Entity& entity = file_.entity(entity_id);
        if (entity.object_origin ==
            cir::EntityObjectOrigin::TemplateParameterObject) {
            if (entity.kind != cir::EntityKind::Variable ||
                !entity.has_constant_value) {
                return {};
            }
            cir::TemplateArgument argument;
            argument.kind = cir::TemplateArgumentKind::Value;
            argument.value_type = file_.type_ref(entity.type);
            argument.value_kind = entity.constant_value_kind;
            argument.null_kind = entity.constant_null_kind;
            argument.integer_value = entity.constant_integer_value;
            argument.value_entity = entity.constant_entity;
            argument.closure_identity = entity.constant_closure_identity;
            argument.value_byte_offset = entity.constant_byte_offset;
            argument.value_elements = entity.constant_value_elements;

            out_ = "_ZTA";
            encode_template_value_argument(argument);
            return out_;
        }
        if (entity.object_origin ==
            cir::EntityObjectOrigin::StructuredBindingBacking) {
            return structured_binding_name(entity_id);
        }
        if (std::string local_member = local_record_member_name(entity_id);
            !local_member.empty()) {
            return local_member;
        }
        if (entity.local_source_name.valid() &&
            entity.local_enclosing_function.valid()) {
            return local_entity_name(entity);
        }
        std::vector<cir::EntityId> namespaces;
        if (!namespace_chain(entity_id, namespaces)) {
            return {};
        }
        std::string source_name =
            entity.name.valid() ? std::string(file_.name(entity.name)) : std::string();
        if (source_name.empty()) {
            return {};
        }

        const char* operator_code = nullptr;
        std::string operator_terminal_storage;
        const cir::OperatorFunctionIdentity& operator_identity =
            entity.operator_function;
        if (operator_identity.kind == cir::OperatorFunctionKind::Literal &&
            operator_identity.literal_suffix.valid()) {
            std::string_view suffix =
                file_.name(operator_identity.literal_suffix);
            operator_terminal_storage =
                "li" + std::to_string(suffix.size()) + std::string(suffix);
            operator_code = operator_terminal_storage.c_str();
        } else if (operator_identity.valid() &&
                   operator_identity.kind !=
                       cir::OperatorFunctionKind::Conversion) {
            operator_code = itanium_operator_code(
                operator_identity.spelling,
                operator_is_unary(entity_id, {}));
        } else if (source_name.rfind("operator", 0) == 0 &&
                   source_name.size() > 8) {
            operator_code = itanium_operator_code(
                std::string_view(source_name).substr(8),
                operator_is_unary(entity_id, {}));
        }
        std::string conversion_operator_terminal_storage;

        switch (entity.kind) {
            case cir::EntityKind::Function: {
                if (namespaces.empty() && source_name == "main") {
                    return {};
                }

                const cir::TemplateSpecializationFact* spec =
                    file_.template_specialization(entity_id);
                if (spec && spec->pattern_type.valid()) {
                    out_ = "_Z";
                    std::string specialized_operator =
                        specialization_operator_terminal(*spec);
                    encode_specialized_name(
                        namespaces,
                        *spec,
                        false,
                        false,
                        cir::FunctionRefQualifierKind::None,
                        specialized_operator.empty()
                            ? nullptr
                            : specialized_operator.c_str());
                    encode_template_function_type(spec->pattern_type);
                    return out_;
                }
                out_ = "_Z";
                terminal_module_entity_ = entity_id;
                encode_entity_name(namespaces, source_name, operator_code);
                encode_bare_function_type(entity.type, /*skip_first=*/false);
                return out_;
            }
            case cir::EntityKind::Method:
            case cir::EntityKind::Constructor:
            case cir::EntityKind::Destructor: {
                const cir::RecordMethodFact* fact = file_.method_fact(entity_id);
                bool is_static = fact && fact->is_static;
                const char* special_terminal = operator_code;
                bool is_conversion = fact && fact->is_conversion_function;
                if (!special_terminal && is_conversion) {
                    conversion_operator_terminal_storage =
                        conversion_operator_terminal(entity_id);
                    if (!conversion_operator_terminal_storage.empty()) {
                        special_terminal =
                            conversion_operator_terminal_storage.c_str();
                    }
                }
                if (entity.kind == cir::EntityKind::Constructor) {

                    special_terminal = structor_variant_ ? structor_variant_ : "C1";
                } else if (entity.kind == cir::EntityKind::Destructor) {
                    special_terminal = structor_variant_ ? structor_variant_ : "D1";
                }
                cir::EntityId inherited_origin_record =
                    inherited_origin_record_.valid()
                    ? inherited_origin_record_
                    : fact && fact->inherited_constructor
                    ? fact->inherited_constructor->origin_record
                    : cir::EntityId{};
                bool const_member = false;
                bool volatile_member = false;
                cir::FunctionRefQualifierKind ref_qualifier =
                    cir::FunctionRefQualifierKind::None;
                if (const auto* method_payload =
                        std::get_if<cir::FunctionTypePayload>(
                            &file_.type_payload(
                                file_.resolved_type(entity.type)))) {
                    const_member = method_payload->member_is_const;
                    volatile_member = method_payload->member_is_volatile;
                    ref_qualifier = method_payload->member_ref_qualifier;
                }
                if (const cir::TemplateSpecializationFact* spec =
                        file_.template_specialization(entity_id);
                    spec && spec->pattern_type.valid()) {
                    if (is_conversion) {
                        conversion_operator_terminal_storage =
                            conversion_operator_terminal(spec->pattern_type);
                        special_terminal =
                            conversion_operator_terminal_storage.c_str();
                    } else if (!special_terminal) {
                        operator_terminal_storage =
                            specialization_operator_terminal(*spec);
                        special_terminal = operator_terminal_storage.empty()
                            ? nullptr
                            : operator_terminal_storage.c_str();
                    }
                    out_ = "_Z";
                    encode_specialized_name(namespaces, *spec, const_member,
                                            volatile_member, ref_qualifier,
                                            special_terminal,
                                            inherited_origin_record);
                    encode_template_function_type(spec->pattern_type,
                                                  is_conversion ||
                                                      entity.kind ==
                                                          cir::EntityKind::Constructor ||
                                                      entity.kind ==
                                                          cir::EntityKind::Destructor);
                    return out_;
                }
                out_ = "_Z";
                encode_entity_name(namespaces, source_name, special_terminal,
                                   const_member, volatile_member,
                                   ref_qualifier,
                                   inherited_origin_record);
                bool skip_trailing_flag = false;
                if (entity.kind == cir::EntityKind::Constructor ||
                    entity.kind == cir::EntityKind::Destructor) {

                    const cir::RecordFacts* record =
                        file_.record_facts(entity.parent);
                    skip_trailing_flag = skip_trailing_param_ ||
                        (record && !record->virtual_bases.empty());
                }
                encode_bare_function_type(entity.type, /*skip_first=*/!is_static,
                                          skip_trailing_flag ? 2 : 0);
                return out_;
            }
            case cir::EntityKind::Variable: {
                if (const cir::TemplateSpecializationFact* spec =
                        file_.template_specialization(entity_id)) {
                    out_ = "_Z";
                    encode_specialized_name(namespaces, *spec);
                    return out_;
                }

                bool module_attached_name =
                    !module_components(entity_id).empty();
                if (namespaces.empty() && !module_attached_name) {
                    return {};
                }
                out_ = "_Z";
                terminal_module_entity_ = entity_id;
                encode_entity_name(namespaces, source_name);
                return out_;
            }
            default:
                return {};
        }
    }

public:
    void set_structor_variant(const char* variant) { structor_variant_ = variant; }
    void set_inherited_constructor_origin(cir::EntityId origin) {
        inherited_origin_record_ = origin;
    }
    void set_skip_trailing_param(bool skip) { skip_trailing_param_ = skip; }

    std::string record_data_symbol(cir::EntityId record_entity,
                                   const char* prefix) {
        if (!record_entity.valid() || !file_.valid(record_entity)) {
            return {};
        }
        const cir::Entity& record = file_.entity(record_entity);
        if (!record.name.valid()) {
            return {};
        }
        out_ = prefix;
        encode_tag_name(record_entity, record.name);
        return out_;
    }

    std::string type_data_symbol(const cir::TypeRef& type, const char* prefix) {
        out_ = prefix;
        encode_type(type);
        return out_;
    }
    std::string construction_vtable_symbol(cir::EntityId derived_entity,
                                           cir::EntityId base_entity,
                                           size_t offset) {
        if (!derived_entity.valid() || !file_.valid(derived_entity) ||
            !base_entity.valid() || !file_.valid(base_entity)) {
            return {};
        }
        const cir::Entity& derived = file_.entity(derived_entity);
        const cir::Entity& base = file_.entity(base_entity);
        if (!derived.name.valid() || !base.name.valid()) {
            return {};
        }
        out_ = "_ZTC";
        encode_tag_name(derived_entity, derived.name);
        out_ += std::to_string(offset);
        out_ += '_';
        encode_tag_name(base_entity, base.name);
        return out_;
    }

private:
    const cir::File& file_;
    std::string out_;
    const char* structor_variant_ = nullptr;
    cir::EntityId inherited_origin_record_{};
    cir::EntityId terminal_module_entity_{};
    bool skip_trailing_param_ = false;
    const std::string empty_key_;
    std::vector<std::vector<std::string>> substitutions_;

    std::string structured_binding_name(cir::EntityId entity_id) {
        const cir::Entity& entity = file_.entity(entity_id);
        const cir::StructuredBindingFact* fact =
            file_.structured_binding_fact(entity_id);
        if (!fact || fact->source_names.empty()) {
            return {};
        }
        std::string terminal = "DC";
        for (cir::NameId name : fact->source_names) {
            if (!name.valid()) {
                return {};
            }
            append_source_name(terminal, file_.name(name));
        }
        terminal += 'E';

        if (entity.owning_function.valid()) {
            std::string function_encoding =
                enclosing_function_encoding(entity.owning_function);
            if (function_encoding.empty()) {
                return {};
            }
            std::string result = "_ZZ" + function_encoding + "E" + terminal;
            if (entity.local_name_ordinal != 0) {
                uint32_t discriminator = entity.local_name_ordinal - 1;
                result += discriminator < 10
                    ? "_" + std::to_string(discriminator)
                    : "__" + std::to_string(discriminator) + "_";
            }
            return result;
        }

        std::vector<cir::EntityId> namespaces;
        if (!namespace_chain(entity_id, namespaces)) {
            return {};
        }
        out_ = "_Z";
        encode_entity_name(namespaces, {}, terminal.c_str());
        return out_;
    }

    bool operator_is_unary(cir::EntityId entity_id,
                           cir::TypeId pattern_type) const {
        if (!entity_id.valid() || !file_.valid(entity_id)) {
            return false;
        }
        const cir::Entity& entity = file_.entity(entity_id);
        cir::TypeId function_type = pattern_type;
        if (!function_type.valid() &&
            entity.kind == cir::EntityKind::Method) {
            if (const cir::RecordMethodFact* method =
                    file_.method_fact(entity_id)) {
                function_type = method->type.type;
            }
        }
        if (!function_type.valid()) {
            function_type = entity.type;
        }
        function_type = file_.resolved_type(function_type);
        if (!file_.valid(function_type)) {
            return false;
        }
        const auto* payload = std::get_if<cir::FunctionTypePayload>(
            &file_.type_payload(function_type));
        if (!payload) {
            return false;
        }
        return entity.kind == cir::EntityKind::Method
            ? payload->parameters.empty()
            : payload->parameters.size() == 1;
    }

    std::string specialization_operator_terminal(
        const cir::TemplateSpecializationFact& spec) const {
        if (!spec.template_entity.valid() ||
            !file_.valid(spec.template_entity)) {
            return {};
        }
        const cir::Entity& primary = file_.entity(spec.template_entity);
        if (primary.operator_function.kind ==
                cir::OperatorFunctionKind::Literal &&
            primary.operator_function.literal_suffix.valid()) {
            std::string_view suffix =
                file_.name(primary.operator_function.literal_suffix);
            return "li" + std::to_string(suffix.size()) +
                std::string(suffix);
        }
        if (primary.operator_function.valid() &&
            primary.operator_function.kind !=
                cir::OperatorFunctionKind::Conversion &&
            primary.operator_function.kind !=
                cir::OperatorFunctionKind::Literal) {
            const char* code = itanium_operator_code(
                primary.operator_function.spelling,
                operator_is_unary(spec.template_entity, spec.pattern_type));
            return code ? std::string(code) : std::string{};
        }
        if (!primary.name.valid()) {
            return {};
        }
        std::string_view name = file_.name(primary.name);
        if (name.rfind("operator", 0) != 0 || name.size() <= 8) {
            return {};
        }
        const char* code = itanium_operator_code(
            name.substr(8),
            operator_is_unary(spec.template_entity, spec.pattern_type));
        return code ? std::string(code) : std::string{};
    }

    bool namespace_chain(cir::EntityId entity_id,
                         std::vector<cir::EntityId>& namespaces) const {
        if (!entity_id.valid() || !file_.valid(entity_id)) {
            return false;
        }
        const cir::Entity& entity = file_.entity(entity_id);
        cir::DeclContextId context = entity.semantic_context;
        if (!context.valid()) {
            context = entity.lexical_context;
        }

        if (context.valid() &&
            (entity.kind == cir::EntityKind::Record ||
             entity.kind == cir::EntityKind::Enum ||
             entity.kind == cir::EntityKind::Namespace) &&
            file_.decl_context(context).owner.valid() &&
            file_.decl_context(context).owner == entity_id) {
            context = file_.decl_context(context).parent;
        }
        while (context.valid()) {
            const cir::DeclContext& record = file_.decl_context(context);
            if (record.kind == cir::DeclContextKind::TranslationUnit) {
                break;
            }

            if (record.kind == cir::DeclContextKind::TemplateParameter) {
                context = record.parent;
                continue;
            }
            bool is_name_component =
                (record.kind == cir::DeclContextKind::Namespace ||
                 record.kind == cir::DeclContextKind::Record) &&
                record.owner.valid();
            if (!is_name_component) {
                return false;
            }
            namespaces.insert(namespaces.begin(), record.owner);
            context = record.parent;
        }
        return true;
    }

    static void append_source_name(std::string& out, std::string_view name) {
        if (name == anonymous_namespace_source_name) {
            out += "12_GLOBAL__N_1";
            return;
        }
        out += std::to_string(name.size());
        out += name;
    }

    static std::string seq_id(size_t index) {

        if (index == 0) {
            return "S_";
        }
        size_t value = index - 1;
        std::string digits;
        do {
            size_t digit = value % 36;
            digits.insert(digits.begin(),
                          static_cast<char>(digit < 10 ? '0' + digit
                                                       : 'A' + (digit - 10)));
            value /= 36;
        } while (value != 0);
        return "S" + digits + "_";
    }

    std::string local_entity_name(const cir::Entity& entity) const {
        if (!entity.local_source_name.valid() ||
            !entity.local_enclosing_function.valid() ||
            !file_.valid(entity.local_enclosing_function)) {
            return {};
        }
        const cir::Entity& function =
            file_.entity(entity.local_enclosing_function);
        std::string function_encoding;
        if (function.name.valid() && file_.name(function.name) == "main") {
            append_source_name(function_encoding, "main");
        } else {
            ItaniumMangler nested(file_);
            std::string mangled =
                nested.mangle(entity.local_enclosing_function);
            if (mangled.rfind("_Z", 0) != 0) {
                return {};
            }
            function_encoding = mangled.substr(2);
        }

        std::string result = "_ZZ" + function_encoding + "E";
        append_source_name(result, file_.name(entity.local_source_name));
        if (entity.local_name_ordinal == 0) {
            return result;
        }
        uint32_t discriminator = entity.local_name_ordinal - 1;
        if (discriminator < 10) {
            result += "_" + std::to_string(discriminator);
        } else {
            result += "__" + std::to_string(discriminator) + "_";
        }
        return result;
    }

    cir::EntityId local_record_owner(cir::EntityId entity_id) const {
        if (!entity_id.valid() || !file_.valid(entity_id)) {
            return {};
        }
        const cir::Entity& entity = file_.entity(entity_id);
        cir::EntityId owner = entity.declaring_record.valid()
            ? entity.declaring_record
            : entity.parent;
        if (!owner.valid() || !file_.valid(owner) ||
            file_.entity(owner).kind != cir::EntityKind::Record ||
            !file_.entity(owner).local_enclosing_function.valid()) {
            return {};
        }
        return owner;
    }

    std::string enclosing_function_encoding(cir::EntityId function_id) const {
        if (!function_id.valid() || !file_.valid(function_id)) {
            return {};
        }
        const cir::Entity& function = file_.entity(function_id);
        if (function.name.valid() && file_.name(function.name) == "main") {
            std::string result;
            append_source_name(result, "main");
            return result;
        }
        ItaniumMangler nested(file_);
        std::string mangled = nested.mangle(function_id);
        return mangled.rfind("_Z", 0) == 0 ? mangled.substr(2)
                                            : std::string{};
    }

    void encode_local_record_component(cir::EntityId record_id) {
        const cir::Entity& record = file_.entity(record_id);
        const cir::RecordFacts* facts = file_.record_facts(record_id);
        bool is_lambda =
            record.local_name_kind == cir::LocalNameComponentKind::Lambda ||
            (facts && file_.valid(facts->closure_identity));
        if (!is_lambda) {
            if (record.local_name_kind ==
                cir::LocalNameComponentKind::Anonymous) {
                append_source_name(
                    out_, "$_" +
                              std::to_string(record.local_component_ordinal));
                return;
            }
            append_source_name(
                out_, record.local_source_name.valid()
                          ? file_.name(record.local_source_name)
                          : file_.name(record.name));
            if (record.local_name_ordinal != 0) {
                uint32_t discriminator = record.local_name_ordinal - 1;
                out_ += discriminator < 10
                    ? "_" + std::to_string(discriminator)
                    : "__" + std::to_string(discriminator) + "_";
            }
            return;
        }

        const cir::ClosureIdentityFact* identity =
            facts && file_.valid(facts->closure_identity)
                ? &file_.closure_identity(facts->closure_identity)
                : nullptr;
        if (identity &&
            identity->abi_context ==
                cir::ClosureAbiContextKind::VariableInitializer &&
            identity->abi_context_name.valid()) {
            append_source_name(out_,
                               file_.name(identity->abi_context_name));
            out_ += 'M';
        }

        auto signature_encoding = [&](cir::EntityId candidate_id) {
            std::string result;
            const cir::RecordFacts* candidate_facts =
                file_.record_facts(candidate_id);
            const cir::FunctionTypePayload* candidate_signature = nullptr;
            if (candidate_facts) {
                for (const cir::RecordMethodFact& method :
                     candidate_facts->methods) {
                    if (!method.name.valid() ||
                        file_.name(method.name) != "operator()") {
                        continue;
                    }
                    cir::TypeId type = file_.resolved_type(method.type.type);
                    candidate_signature =
                        std::get_if<cir::FunctionTypePayload>(
                            &file_.type_payload(type));
                    if (candidate_signature) {
                        break;
                    }
                }
            }
            ItaniumMangler nested(file_);
            if (!candidate_signature ||
                candidate_signature->parameters.empty()) {
                return std::string("v");
            }
            for (cir::TypeRef parameter :
                 candidate_signature->parameters) {
                parameter.qualifiers = cir::QualNone;
                nested.encode_type(parameter);
            }
            return nested.out_;
        };

        // Itanium <closure-type-name>: Ul <lambda-sig> E [number] _. The
        // ordinal is local to one ABI context and signature, ordered by the
        // lambda key token, never by global parser encounter order.
        out_ += "Ul";
        const cir::FunctionTypePayload* signature = nullptr;
        if (facts) {
            for (const cir::RecordMethodFact& method : facts->methods) {
                if (method.name.valid() &&
                    file_.name(method.name) == "operator()") {
                    cir::TypeId type = file_.resolved_type(method.type.type);
                    signature = std::get_if<cir::FunctionTypePayload>(
                        &file_.type_payload(type));
                    if (signature) {
                        break;
                    }
                }
            }
        }
        if (!signature || signature->parameters.empty()) {
            out_ += 'v';
        } else {
            for (cir::TypeRef parameter : signature->parameters) {
                parameter.qualifiers = cir::QualNone;
                encode_type(parameter);
            }
        }
        out_ += 'E';
        uint32_t preceding = 0;
        std::string signature_key = signature_encoding(record_id);
        for (cir::EntityId candidate_id : file_.entity_ids()) {
            if (candidate_id == record_id || !file_.valid(candidate_id)) {
                continue;
            }
            const cir::Entity& candidate = file_.entity(candidate_id);
            const cir::RecordFacts* candidate_facts =
                candidate.kind == cir::EntityKind::Record
                    ? file_.record_facts(candidate_id)
                    : nullptr;
            if (!candidate_facts || !candidate_facts->is_lambda_closure ||
                signature_encoding(candidate_id) != signature_key) {
                continue;
            }
            const cir::ClosureIdentityFact* candidate_identity =
                file_.valid(candidate_facts->closure_identity)
                    ? &file_.closure_identity(
                          candidate_facts->closure_identity)
                    : nullptr;
            bool same_context = identity && candidate_identity
                ? identity->abi_context == candidate_identity->abi_context &&
                      identity->lexical_owner ==
                          candidate_identity->lexical_owner &&
                      identity->abi_context_name ==
                          candidate_identity->abi_context_name &&
                      identity->abi_context_decl ==
                          candidate_identity->abi_context_decl
                : candidate.local_enclosing_function ==
                      record.local_enclosing_function;
            if (!same_context) {
                continue;
            }
            SrcLoc candidate_key = candidate_identity
                ? candidate_identity->key_loc
                : candidate.loc;
            SrcLoc record_key = identity ? identity->key_loc : record.loc;
            if (candidate_key.offset < record_key.offset ||
                (candidate_key.offset == record_key.offset &&
                 candidate_id.index < record_id.index)) {
                ++preceding;
            }
        }
        if (preceding != 0) {
            out_ += std::to_string(preceding - 1);
        }
        out_ += '_';
    }

    std::string local_record_member_name(cir::EntityId entity_id) {
        cir::EntityId record_id = local_record_owner(entity_id);
        if (!record_id.valid()) {
            return {};
        }
        const cir::Entity& entity = file_.entity(entity_id);
        const cir::Entity& record = file_.entity(record_id);
        std::string function_encoding =
            enclosing_function_encoding(record.local_enclosing_function);
        if (function_encoding.empty()) {
            return {};
        }
        const cir::RecordMethodFact* fact = file_.method_fact(entity_id);
        bool is_static = fact && fact->is_static;
        std::string source_name = fact && fact->name.valid()
            ? std::string(file_.name(fact->name))
            : (entity.name.valid() ? std::string(file_.name(entity.name))
                                   : std::string{});
        if (source_name.empty()) {
            return {};
        }

        bool const_member = false;
        bool volatile_member = false;
        cir::FunctionRefQualifierKind ref_qualifier =
            cir::FunctionRefQualifierKind::None;
        if (const auto* payload = std::get_if<cir::FunctionTypePayload>(
                &file_.type_payload(file_.resolved_type(entity.type)))) {
            const_member = payload->member_is_const;
            volatile_member = payload->member_is_volatile;
            ref_qualifier = payload->member_ref_qualifier;
        }

        const char* special_terminal = nullptr;
        std::string conversion_terminal;
        std::string operator_terminal;
        if (entity.operator_function.kind ==
                cir::OperatorFunctionKind::Literal &&
            entity.operator_function.literal_suffix.valid()) {
            std::string_view suffix =
                file_.name(entity.operator_function.literal_suffix);
            operator_terminal =
                "li" + std::to_string(suffix.size()) + std::string(suffix);
            special_terminal = operator_terminal.c_str();
        } else if (entity.operator_function.valid() &&
                   entity.operator_function.kind !=
                       cir::OperatorFunctionKind::Conversion) {
            special_terminal = itanium_operator_code(
                entity.operator_function.spelling,
                operator_is_unary(entity_id, {}));
        } else if (source_name.rfind("operator", 0) == 0 &&
                   source_name.size() > 8) {
            special_terminal = itanium_operator_code(
                std::string_view(source_name).substr(8),
                operator_is_unary(entity_id, {}));
        }
        if (!special_terminal &&
            (entity.operator_function.kind ==
                 cir::OperatorFunctionKind::Conversion ||
             source_name.rfind("operator ", 0) == 0)) {
            conversion_terminal = conversion_operator_terminal(entity_id);
            if (!conversion_terminal.empty()) {
                special_terminal = conversion_terminal.c_str();
            }
        }
        if (entity.kind == cir::EntityKind::Constructor) {
            special_terminal = structor_variant_ ? structor_variant_ : "C1";
        } else if (entity.kind == cir::EntityKind::Destructor) {
            special_terminal = structor_variant_ ? structor_variant_ : "D1";
        }

        out_ = "_ZZ" + function_encoding + "EN";
        if (const_member) out_ += 'K';
        if (volatile_member) out_ += 'V';
        if (ref_qualifier == cir::FunctionRefQualifierKind::LValue) {
            out_ += 'R';
        } else if (ref_qualifier == cir::FunctionRefQualifierKind::RValue) {
            out_ += 'O';
        }
        encode_local_record_component(record_id);
        if (special_terminal) {
            out_ += special_terminal;
        } else {
            append_source_name(out_, source_name);
        }
        out_ += 'E';
        add_substitution(type_key(
            file_.type_ref(file_.entity(record_id).type)));

        bool skip_trailing_flag = false;
        if (entity.kind == cir::EntityKind::Constructor ||
            entity.kind == cir::EntityKind::Destructor) {
            const cir::RecordFacts* record_facts =
                file_.record_facts(record_id);
            skip_trailing_flag = skip_trailing_param_ ||
                (record_facts && !record_facts->virtual_bases.empty());
        }
        encode_bare_function_type(entity.type, /*skip_first=*/!is_static,
                                  skip_trailing_flag ? 2 : 0);
        return out_;
    }

    // C++20 module mangling (Itanium <module-name>): a namespace-scope
    // entity attached to a named module carries W-prefixed module-name
    // components before its unqualified name — both exported (strong
    // ownership) and module-linkage names, matching clang. Partition names
    // never appear in entity manglings (only per-unit initializers name
    // them). The module name and each dotted prefix are substitution
    // candidates.
    bool at_namespace_scope(cir::EntityId entity_id) const {
        const cir::Entity& entity = file_.entity(entity_id);
        cir::DeclContextId context = entity.semantic_context;
        if (context.valid() && file_.valid(context) &&
            file_.decl_context(context).owner == entity_id) {
            context = file_.decl_context(context).parent;
        }
        while (context.valid() && file_.valid(context)) {
            cir::DeclContextKind kind = file_.decl_context(context).kind;
            if (kind == cir::DeclContextKind::TemplateParameter) {
                context = file_.decl_context(context).parent;
                continue;
            }
            return kind == cir::DeclContextKind::Namespace ||
                   kind == cir::DeclContextKind::TranslationUnit;
        }
        return false;
    }

    std::vector<std::string> module_components(cir::EntityId entity_id) const {
        if (!entity_id.valid() || !file_.valid(entity_id) ||
            !at_namespace_scope(entity_id)) {
            return {};
        }
        const cir::Entity& entity = file_.entity(entity_id);
        cir::ModuleAttachmentId attachment =
            file_.effective_module_attachment(entity);
        if (!attachment.valid() || !file_.valid(attachment)) {
            return {};
        }
        const cir::ModuleUnitFact& unit = file_.module_unit(attachment);
        if (!unit.module_name.valid()) {
            return {};
        }
        std::vector<std::string> parts;
        std::string_view name = file_.name(unit.module_name);
        size_t start = 0;
        while (start <= name.size()) {
            size_t dot = name.find('.', start);
            std::string_view part = dot == std::string_view::npos
                ? name.substr(start)
                : name.substr(start, dot - start);
            if (!part.empty()) {
                parts.emplace_back(part);
            }
            if (dot == std::string_view::npos) {
                break;
            }
            start = dot + 1;
        }
        return parts;
    }

    std::string module_component_key_text(cir::EntityId entity_id) const {
        std::string encoded;
        for (const std::string& part : module_components(entity_id)) {
            encoded += 'W';
            append_source_name(encoded, part);
        }
        return encoded;
    }

    void emit_module_name_prefix(cir::EntityId entity_id) {
        std::vector<std::string> parts = module_components(entity_id);
        if (parts.empty()) {
            return;
        }
        std::vector<std::string> keys;
        std::string key = "#module";
        for (const std::string& part : parts) {
            key += '.';
            key += part;
            keys.push_back(key);
        }
        size_t longest = keys.size();
        while (longest > 0 && !has_substitution(keys[longest - 1])) {
            --longest;
        }
        if (longest > 0) {
            emit_substitution(keys[longest - 1]);
        }
        for (size_t i = longest; i < parts.size(); ++i) {
            out_ += 'W';
            append_source_name(out_, parts[i]);
            add_substitution(keys[i]);
        }
    }

    bool emit_substitution(const std::string& key) {
        for (size_t i = 0; i < substitutions_.size(); ++i) {
            for (const std::string& alias : substitutions_[i]) {
                if (alias == key) {
                    out_ += seq_id(i);
                    return true;
                }
            }
        }
        return false;
    }

    void add_substitution(std::string key) {
        substitutions_.push_back({std::move(key)});
    }

    void add_substitution_aliases(std::vector<std::string> keys) {
        substitutions_.push_back(std::move(keys));
    }

    void encode_entity_name(const std::vector<cir::EntityId>& namespaces,
                            std::string_view terminal,
                            const char* special_terminal = nullptr,
                            bool const_member = false,
                            bool volatile_member = false,
                            cir::FunctionRefQualifierKind ref_qualifier =
                                cir::FunctionRefQualifierKind::None,
                            cir::EntityId inherited_origin_record = {}) {

        cir::EntityId terminal_module_entity = terminal_module_entity_;
        terminal_module_entity_ = {};
        if (namespaces.empty()) {
            emit_module_name_prefix(terminal_module_entity);
            if (inherited_origin_record.valid() &&
                file_.valid(inherited_origin_record)) {
                out_ += "CI";
                out_ += special_terminal && special_terminal[0] == 'C'
                    ? special_terminal + 1
                    : "1";
                encode_type(file_.type_ref(
                    file_.entity(inherited_origin_record).type));
            } else if (special_terminal) {
                out_ += special_terminal;
            } else {
                append_source_name(out_, terminal);
            }
            return;
        }
        if (namespaces.size() == 1) {
            const cir::Entity& only_namespace =
                file_.entity(namespaces.front());
            if (only_namespace.kind == cir::EntityKind::Namespace &&
                only_namespace.name.valid() &&
                file_.name(only_namespace.name) == "std") {
                out_ += "St";
                if (special_terminal) {
                    out_ += special_terminal;
                } else {
                    append_source_name(out_, terminal);
                }
                return;
            }
        }
        out_ += 'N';
        if (const_member) {
            out_ += 'K';
        }
        if (volatile_member) {
            out_ += 'V';
        }
        if (ref_qualifier == cir::FunctionRefQualifierKind::LValue) {
            out_ += 'R';
        } else if (ref_qualifier == cir::FunctionRefQualifierKind::RValue) {
            out_ += 'O';
        }
        encode_prefix(namespaces);
        emit_module_name_prefix(terminal_module_entity);
        if (inherited_origin_record.valid() &&
            file_.valid(inherited_origin_record)) {
            out_ += "CI";
            out_ += special_terminal && special_terminal[0] == 'C'
                ? special_terminal + 1
                : "1";
            encode_type(file_.type_ref(
                file_.entity(inherited_origin_record).type));
        } else if (special_terminal) {
            out_ += special_terminal;
        } else {
            append_source_name(out_, terminal);
        }
        out_ += 'E';
    }

    void encode_referenced_entity_name(cir::EntityId entity_id) {
        if (!entity_id.valid() || !file_.valid(entity_id)) {
            out_ += "0";
            return;
        }
        const cir::Entity& entity = file_.entity(entity_id);
        if (!entity.name.valid()) {
            out_ += "0";
            return;
        }
        if (entity.local_source_name.valid() &&
            entity.local_enclosing_function.valid()) {
            std::string local_name = local_entity_name(entity);
            out_ += local_name.empty() ? "0" : local_name;
            return;
        }
        std::vector<cir::EntityId> namespaces;
        if (!namespace_chain(entity_id, namespaces)) {
            append_source_name(out_, file_.name(entity.name));
            return;
        }
        out_ += "_Z";
        if (entity.linkage != cir::LinkageKind::Internal) {
            terminal_module_entity_ = entity_id;
            encode_entity_name(namespaces, file_.name(entity.name));
            return;
        }
        if (namespaces.empty()) {
            out_ += 'L';
            append_source_name(out_, file_.name(entity.name));
            return;
        }
        out_ += 'N';
        encode_prefix(namespaces);
        out_ += 'L';
        append_source_name(out_, file_.name(entity.name));
        out_ += 'E';
    }

    cir::NameId linkage_source_name(const cir::Entity& entity) const {
        return entity.unnamed_type_linkage_name.valid()
            ? entity.unnamed_type_linkage_name
            : entity.name;
    }

    bool has_record_scope_unnamed_name(const cir::Entity& entity) const {
        return entity.kind == cir::EntityKind::Record &&
            entity.unnamed_type_ordinal !=
                cir::Entity::NoUnnamedTypeOrdinal &&
            !entity.unnamed_type_linkage_name.valid();
    }

    std::string record_scope_unnamed_component(
        const cir::Entity& entity) const {
        std::string component = "Ut";
        if (entity.unnamed_type_ordinal > 0) {
            component +=
                std::to_string(entity.unnamed_type_ordinal - 1);
        }
        component += '_';
        return component;
    }

    std::string component_key(cir::EntityId entity_id) const {
        if (file_.template_specialization(entity_id)) {
            return "#spec" + std::to_string(entity_id.index);
        }
        const cir::Entity& entity = file_.entity(entity_id);
        const cir::RecordFacts* facts =
            entity.kind == cir::EntityKind::Record
                ? file_.record_facts(entity_id)
                : nullptr;
        if (facts && file_.valid(facts->closure_identity)) {
            ItaniumMangler nested(file_);
            nested.encode_local_record_component(entity_id);
            return nested.out_;
        }
        if (has_record_scope_unnamed_name(entity)) {
            return record_scope_unnamed_component(entity);
        }
        cir::NameId abi_name = linkage_source_name(entity);
        std::string component = abi_name.valid()
            ? std::string(file_.name(abi_name))
            : std::string("(anonymous namespace)");

        std::string encoded = module_component_key_text(entity_id);
        append_source_name(encoded, component);
        return encoded;
    }
    std::string encode_prefix(const std::vector<cir::EntityId>& namespaces) {

        std::string key;
        size_t emitted_from = 0;
        std::vector<std::string> keys;
        keys.reserve(namespaces.size());
        for (cir::EntityId namespace_entity : namespaces) {
            key += component_key(namespace_entity);
            keys.push_back(key);
        }
        size_t longest = keys.size();
        while (longest > 0 && !has_substitution(keys[longest - 1])) {
            --longest;
        }
        if (longest > 0) {
            emit_substitution(keys[longest - 1]);
            emitted_from = longest;
        } else if (!namespaces.empty()) {
            const cir::Entity& first = file_.entity(namespaces.front());
            if (first.kind == cir::EntityKind::Namespace &&
                first.name.valid() && file_.name(first.name) == "std") {

                out_ += "St";
                emitted_from = 1;
            }
        }
        for (size_t i = emitted_from; i < keys.size(); ++i) {
            const cir::Entity& record = file_.entity(namespaces[i]);
            const std::string& previous = i > 0 ? keys[i - 1] : empty_key_;
            if (const cir::TemplateSpecializationFact* spec =
                    file_.template_specialization(namespaces[i])) {
                emit_template_id(previous, *spec);
            } else if (const cir::RecordFacts* facts =
                           file_.record_facts(namespaces[i]);
                       facts && file_.valid(facts->closure_identity)) {
                encode_local_record_component(namespaces[i]);
            } else if (has_record_scope_unnamed_name(record)) {
                out_ += record_scope_unnamed_component(record);
            } else {
                emit_module_name_prefix(namespaces[i]);
                cir::NameId abi_name = linkage_source_name(record);
                std::string component = abi_name.valid()
                    ? std::string(file_.name(abi_name))
                    : std::string("(anonymous namespace)");
                append_source_name(out_, component);
            }

            std::vector<std::string> aliases{keys[i]};
            if (record.kind == cir::EntityKind::Record && record.type.valid()) {
                cir::TypeRef canonical{file_.resolved_type(record.type),
                                       cir::QualNone,
                                       cir::MemorySpace::Default};
                aliases.push_back(type_key(canonical));
            }
            add_substitution_aliases(std::move(aliases));
        }
        return key;
    }
    void encode_specialized_name(const std::vector<cir::EntityId>& namespaces,
                                 const cir::TemplateSpecializationFact& spec,
                                 bool const_member = false,
                                 bool volatile_member = false,
                                 cir::FunctionRefQualifierKind ref_qualifier =
                                     cir::FunctionRefQualifierKind::None,
                                 const char* special_terminal = nullptr,
                                 cir::EntityId inherited_origin_record = {}) {
        if (namespaces.empty()) {
            emit_template_id(empty_key_, spec, special_terminal,
                             inherited_origin_record);
            return;
        }
        if (namespaces.size() == 1) {
            const cir::Entity& only_namespace =
                file_.entity(namespaces.front());
            if (only_namespace.kind == cir::EntityKind::Namespace &&
                only_namespace.name.valid() &&
                file_.name(only_namespace.name) == "std") {
                out_ += "St";
                emit_template_id(component_key(namespaces.front()),
                                 spec,
                                 special_terminal,
                                 inherited_origin_record);
                return;
            }
        }
        out_ += 'N';
        if (const_member) {
            out_ += 'K';
        }
        if (volatile_member) {
            out_ += 'V';
        }
        if (ref_qualifier == cir::FunctionRefQualifierKind::LValue) {
            out_ += 'R';
        } else if (ref_qualifier == cir::FunctionRefQualifierKind::RValue) {
            out_ += 'O';
        }
        std::string prefix_key = encode_prefix(namespaces);
        emit_template_id(prefix_key, spec, special_terminal,
                         inherited_origin_record);
        out_ += 'E';
    }

    void encode_template_function_type(cir::TypeId pattern_type,
                                       bool omit_return_type = false) {
        cir::TypeId resolved = file_.resolved_type(pattern_type);
        const auto* payload =
            std::get_if<cir::FunctionTypePayload>(&file_.type_payload(resolved));
        if (!payload) {
            out_ += 'v';
            return;
        }
        if (!omit_return_type) {
            encode_type(payload->return_type);
        }
        if (payload->parameters.empty()) {
            out_ += 'v';
        } else {
            for (const cir::TypeRef& parameter : payload->parameters) {
                cir::TypeRef adjusted = parameter;
                adjusted.qualifiers = cir::QualNone;
                encode_type(adjusted);
            }
        }
        if (payload->is_variadic) {
            out_ += 'z';
        }
    }
    void emit_template_id(const std::string& prefix_key,
                          const cir::TemplateSpecializationFact& spec,
                          const char* special_terminal = nullptr,
                          cir::EntityId inherited_origin_record = {}) {
        std::string template_name = "<template>";
        if (spec.template_entity.valid() && file_.valid(spec.template_entity)) {
            const cir::Entity& tmpl = file_.entity(spec.template_entity);
            if (tmpl.name.valid()) {
                template_name = file_.name(tmpl.name);
            }
        }
        std::string template_key = prefix_key;
        if (inherited_origin_record.valid() &&
            file_.valid(inherited_origin_record)) {
            out_ += "CI";
            out_ += special_terminal && special_terminal[0] == 'C'
                ? special_terminal + 1
                : "1";
            encode_type(file_.type_ref(
                file_.entity(inherited_origin_record).type));
        } else if (special_terminal) {
            template_key += special_terminal;
        } else {
            append_source_name(template_key, template_name);
        }
        if (!inherited_origin_record.valid() &&
            !emit_substitution(template_key)) {
            if (special_terminal) {
                out_ += special_terminal;
            } else {
                append_source_name(out_, template_name);
            }
            add_substitution(std::move(template_key));
        }
        out_ += 'I';
        if (spec.argument_bindings.empty()) {
            for (const cir::TemplateArgument& argument :
                 spec.dependent_arguments) {
                encode_template_argument(argument);
            }
        } else {
            for (const cir::TemplateArgumentBinding& binding :
                 spec.argument_bindings) {
                if (binding.is_pack()) {
                    out_ += 'J';
                }
                for (const cir::TemplateArgument& argument :
                     binding.arguments) {
                    encode_template_argument(argument);
                }
                if (binding.is_pack()) {
                    out_ += 'E';
                }
            }
        }
        out_ += 'E';
    }

    void encode_template_argument(const cir::TemplateArgument& argument) {
        if (argument.expands_parameter_pack ||
            argument.expands_pack_pattern) {

            out_ += "Dp";
        }
        switch (argument.kind) {
            case cir::TemplateArgumentKind::Type:
                encode_type(argument.type);
                break;
            case cir::TemplateArgumentKind::Value:
                encode_template_value_argument(argument);
                break;
            case cir::TemplateArgumentKind::Template:
                if (argument.template_entity.valid() &&
                    file_.valid(argument.template_entity)) {
                    append_source_name(
                        out_,
                        file_.name(file_.entity(argument.template_entity).name));
                } else if (argument.template_name.valid()) {
                    append_source_name(out_,
                                       file_.name(argument.template_name));
                } else {
                    append_source_name(out_, "<template>");
                }
                break;
        }
    }

    std::string reflected_entity_mangle_key(
        const cir::TemplateArgument& argument) const {
        std::string semantic =
            std::to_string(static_cast<unsigned>(argument.meta_kind));
        std::vector<cir::EntityId> chain;
        cir::EntityId current = argument.value_entity;
        while (current.valid() && file_.valid(current)) {
            chain.push_back(current);
            current = file_.entity(current).parent;
        }
        std::reverse(chain.begin(), chain.end());
        for (cir::EntityId entity_id : chain) {
            const cir::Entity& entity = file_.entity(entity_id);
            if (!entity.name.valid()) {
                continue;
            }
            std::string_view name = file_.name(entity.name);
            semantic += ':' + std::to_string(name.size()) + ':' +
                std::string(name);
        }
        if (argument.value_entity.valid() &&
            file_.valid(argument.value_entity)) {
            const cir::Entity& entity = file_.entity(argument.value_entity);
            if (entity.type.valid()) {
                semantic += ':' + file_.format_type(entity.type);
            }
        }

        static constexpr char hex[] = "0123456789abcdef";
        std::string key = "aburi_meta_";
        key.reserve(key.size() + semantic.size() * 2);
        for (unsigned char byte : semantic) {
            key.push_back(hex[byte >> 4]);
            key.push_back(hex[byte & 0x0f]);
        }
        return key;
    }

    void encode_template_value_argument(const cir::TemplateArgument& argument) {
        if (argument.value_kind == cir::TemplateValueKind::MetaInfo) {

            out_ += 'L';
            append_source_name(out_, reflected_entity_mangle_key(argument));
            out_ += "0E";
            return;
        }
        if (argument.dependent_value_expr.valid()) {
            // A dependent non-type argument is a general <expression>, not an
            // integer literal. Itanium wraps those in X...E; every signature,
            // specialization key, and call site must encode the same retained
            // semantic tree ([temp.over.link]).
            out_ += 'X';
            encode_dependent_value_expression(argument.dependent_value_expr,
                                              argument.dependent_value_expr.root,
                                              argument.value_type);
            out_ += 'E';
            return;
        }
        if (argument.value_kind == cir::TemplateValueKind::Closure ||
            argument.value_kind ==
                cir::TemplateValueKind::StructuralObject) {
            out_ += 'X';
            encode_structural_object_expression(argument);
            out_ += 'E';
            return;
        }
        if (argument.value_kind == cir::TemplateValueKind::Address ||
            (argument.value_kind == cir::TemplateValueKind::MemberPointer &&
             argument.value_entity.valid() &&
             file_.valid(argument.value_entity))) {
            out_ += 'X';
            encode_template_value_expression(argument);
            out_ += 'E';
            return;
        }
        encode_template_value_expression(argument);
    }

    void encode_dependent_value_expression(
        const cir::TemplateValueExpression& expression,
        uint32_t index,
        cir::TypeRef value_type) {
        if (index == cir::TemplateValueExprNoNode ||
            index >= expression.nodes.size()) {
            out_ += "L_i0E";
            return;
        }
        const cir::TemplateValueExprNode& node = expression.nodes[index];
        switch (node.kind) {
            case cir::TemplateValueExprKind::Integer:
                out_ += 'L';
                if (node.result_type.type.valid()) {
                    encode_type(node.result_type);
                } else if (value_type.type.valid()) {
                    encode_type(value_type);
                } else {
                    out_ += 'i';
                }
                if (node.integer_value.is_negative()) {
                    out_ += 'n';
                    out_ += node.integer_value.decimal().substr(1);
                } else {
                    out_ += node.integer_value.decimal();
                }
                out_ += 'E';
                return;
            case cir::TemplateValueExprKind::Parameter:
                if (node.parameter_index == 0) {
                    out_ += "T_";
                } else {
                    out_ += 'T';
                    out_ += std::to_string(node.parameter_index - 1);
                    out_ += '_';
                }
                return;
            case cir::TemplateValueExprKind::PackSize:
                out_ += "sZ";
                if (node.parameter_index == 0) {
                    out_ += "T_";
                } else {
                    out_ += 'T';
                    out_ += std::to_string(node.parameter_index - 1);
                    out_ += '_';
                }
                return;
            case cir::TemplateValueExprKind::PackIndex:

                out_ += "sy";
                if (node.semantic_key == "function-parameter-pack") {
                    out_ += "fp";
                    if (node.value != 0) {
                        out_ += std::to_string(node.value - 1);
                    }
                    out_ += '_';
                } else if (node.parameter_index == 0) {
                    out_ += "T_";
                } else {
                    out_ += 'T';
                    out_ += std::to_string(node.parameter_index - 1);
                    out_ += '_';
                }
                encode_dependent_value_expression(
                    expression,
                    node.lhs,
                    {});
                return;
            case cir::TemplateValueExprKind::Entity:
                if (node.entity.valid() && file_.valid(node.entity)) {
                    out_ += 'L';
                    encode_referenced_entity_name(node.entity);
                    out_ += 'E';
                } else if (node.name.valid()) {
                    append_source_name(out_, file_.name(node.name));
                } else {
                    out_ += "L_i0E";
                }
                return;
            case cir::TemplateValueExprKind::Unary:
                switch (node.op) {
                    case cir::TemplateValueExprOp::UnaryPlus: out_ += "ps"; break;
                    case cir::TemplateValueExprOp::UnaryMinus: out_ += "ng"; break;
                    case cir::TemplateValueExprOp::LogicalNot: out_ += "nt"; break;
                    case cir::TemplateValueExprOp::BitwiseNot: out_ += "co"; break;
                    case cir::TemplateValueExprOp::Dereference: out_ += "de"; break;
                    case cir::TemplateValueExprOp::AddressOf: out_ += "ad"; break;
                    case cir::TemplateValueExprOp::Delete: out_ += "dl"; break;
                    case cir::TemplateValueExprOp::DeleteArray: out_ += "da"; break;
                    default: out_ += "ps"; break;
                }
                encode_dependent_value_expression(expression,
                                                  node.lhs,
                                                  node.result_type.type.valid()
                                                      ? node.result_type
                                                      : value_type);
                return;
            case cir::TemplateValueExprKind::Binary: {
                switch (node.op) {
                    case cir::TemplateValueExprOp::Add: out_ += "pl"; break;
                    case cir::TemplateValueExprOp::Sub: out_ += "mi"; break;
                    case cir::TemplateValueExprOp::Mul: out_ += "ml"; break;
                    case cir::TemplateValueExprOp::Div: out_ += "dv"; break;
                    case cir::TemplateValueExprOp::Mod: out_ += "rm"; break;
                    case cir::TemplateValueExprOp::Shl: out_ += "ls"; break;
                    case cir::TemplateValueExprOp::Shr: out_ += "rs"; break;
                    case cir::TemplateValueExprOp::BitAnd: out_ += "an"; break;
                    case cir::TemplateValueExprOp::BitOr: out_ += "or"; break;
                    case cir::TemplateValueExprOp::BitXor: out_ += "eo"; break;
                    case cir::TemplateValueExprOp::Less: out_ += "lt"; break;
                    case cir::TemplateValueExprOp::LessEqual: out_ += "le"; break;
                    case cir::TemplateValueExprOp::Greater: out_ += "gt"; break;
                    case cir::TemplateValueExprOp::GreaterEqual: out_ += "ge"; break;
                    case cir::TemplateValueExprOp::Equal: out_ += "eq"; break;
                    case cir::TemplateValueExprOp::NotEqual: out_ += "ne"; break;
                    case cir::TemplateValueExprOp::ThreeWay: out_ += "ss"; break;
                    case cir::TemplateValueExprOp::LogicalAnd: out_ += "aa"; break;
                    case cir::TemplateValueExprOp::LogicalOr: out_ += "oo"; break;
                    case cir::TemplateValueExprOp::Comma: out_ += "cm"; break;
                    case cir::TemplateValueExprOp::MemberPointerDot:
                        out_ += "ds";
                        break;
                    case cir::TemplateValueExprOp::MemberPointerArrow:
                        out_ += "pm";
                        break;
                    case cir::TemplateValueExprOp::UnaryPlus:
                    case cir::TemplateValueExprOp::UnaryMinus:
                    case cir::TemplateValueExprOp::LogicalNot:
                    case cir::TemplateValueExprOp::BitwiseNot:
                    case cir::TemplateValueExprOp::Dereference:
                    case cir::TemplateValueExprOp::Delete:
                    case cir::TemplateValueExprOp::DeleteArray:
                    case cir::TemplateValueExprOp::AddressOf:
                    case cir::TemplateValueExprOp::None: out_ += "cm"; break;
                }
                encode_dependent_value_expression(expression,
                                                  node.lhs,
                                                  value_type);
                encode_dependent_value_expression(expression,
                                                  node.rhs,
                                                  value_type);
                return;
            }
            case cir::TemplateValueExprKind::Conditional:
                out_ += "qu";
                encode_dependent_value_expression(expression, node.lhs,
                                                  value_type);
                encode_dependent_value_expression(expression, node.rhs,
                                                  value_type);
                encode_dependent_value_expression(expression, node.third,
                                                  value_type);
                return;
            case cir::TemplateValueExprKind::Cast:
                out_ += "cv";
                encode_type(node.result_type.type.valid()
                                ? node.result_type
                                : file_.type_ref(node.type));
                encode_dependent_value_expression(expression, node.lhs,
                                                  value_type);
                return;
            case cir::TemplateValueExprKind::SizeofType:
                out_ += "st";
                encode_type(file_.type_ref(node.type));
                return;
            case cir::TemplateValueExprKind::AlignofType:
                out_ += "at";
                encode_type(file_.type_ref(node.type));
                return;
            case cir::TemplateValueExprKind::TypeTrait: {

                out_ += 'u';
                append_source_name(out_, node.semantic_key.empty()
                    ? std::string_view("__type_trait")
                    : std::string_view(node.semantic_key));
                out_ += 'I';
                for (uint32_t operand : node.operands) {
                    if (operand < expression.nodes.size()) {
                        const cir::TemplateValueExprNode& type_operand =
                            expression.nodes[operand];
                        encode_type(type_operand.result_type.type.valid()
                            ? type_operand.result_type
                            : file_.type_ref(type_operand.type));
                    } else {
                        out_ += 'v';
                    }
                }
                out_ += 'E';
                return;
            }
            case cir::TemplateValueExprKind::TypeOperand:
                if (node.lhs != cir::TemplateValueExprNoNode) {
                    encode_dependent_value_expression(expression,
                                                      node.lhs,
                                                      node.result_type);
                } else {

                    if (node.result_type.type.valid() || node.type.valid()) {
                        out_ += "st";
                        encode_type(node.result_type.type.valid()
                                        ? node.result_type
                                        : file_.type_ref(node.type));
                    } else {
                        append_source_name(
                            out_, node.semantic_key.empty()
                                ? std::string_view("<typed-operand>")
                                : std::string_view(node.semantic_key));
                    }
                }
                return;
            case cir::TemplateValueExprKind::Callee: {
                if (node.lhs != cir::TemplateValueExprNoNode) {
                    encode_dependent_value_expression(expression,
                                                      node.lhs,
                                                      node.result_type);
                    return;
                }
                if (node.rhs != cir::TemplateValueExprNoNode) {
                    bool arrow =
                        (static_cast<uint64_t>(node.value) &
                         static_cast<uint32_t>(
                             cir::TemplateCalleeFlag::MemberArrow)) != 0;
                    out_ += arrow ? "pt" : "dt";
                    encode_dependent_value_expression(expression,
                                                      node.rhs,
                                                      {});
                }
                if (node.entity.valid() && file_.valid(node.entity)) {
                    out_ += 'L';
                    encode_referenced_entity_name(node.entity);
                    out_ += 'E';
                } else if (node.name.valid()) {
                    append_source_name(out_, file_.name(node.name));
                } else {
                    append_source_name(
                        out_, node.semantic_key.empty()
                            ? std::string_view("<dependent-callee>")
                            : std::string_view(node.semantic_key));
                }
                return;
            }
            case cir::TemplateValueExprKind::Call: {
                out_ += "cl";
                encode_dependent_value_expression(expression,
                                                  node.third,
                                                  {});
                uint32_t argument = node.lhs;
                while (argument != cir::TemplateValueExprNoNode &&
                       argument < expression.nodes.size()) {
                    const cir::TemplateValueExprNode& descriptor =
                        expression.nodes[argument];
                    encode_dependent_value_expression(
                        expression, argument, descriptor.result_type);
                    argument = descriptor.rhs;
                }
                out_ += 'E';
                return;
            }
            case cir::TemplateValueExprKind::Noexcept:
                out_ += "nx";
                encode_dependent_value_expression(expression,
                                                  node.lhs,
                                                  value_type);
                return;
            case cir::TemplateValueExprKind::ConceptId:
                out_ += 'u';
                append_source_name(out_, "__aburi_concept_id");
                if (node.entity.valid() && file_.valid(node.entity)) {
                    out_ += 'L';
                    encode_referenced_entity_name(node.entity);
                    out_ += 'E';
                } else if (node.name.valid()) {
                    append_source_name(out_, file_.name(node.name));
                } else {
                    append_source_name(out_, "<dependent-concept>");
                }
                out_ += 'I';
                for (const cir::TemplateArgument& argument :
                     node.template_arguments.values()) {
                    encode_template_argument(argument);
                }
                out_ += 'E';
                return;
            case cir::TemplateValueExprKind::Fold: {

                out_ += 'u';
                const char* form = "fold";
                switch (node.fold_kind) {
                    case cir::TemplateValueFoldKind::UnaryLeft:
                        form = "ul";
                        break;
                    case cir::TemplateValueFoldKind::UnaryRight:
                        form = "ur";
                        break;
                    case cir::TemplateValueFoldKind::BinaryLeft:
                        form = "bl";
                        break;
                    case cir::TemplateValueFoldKind::BinaryRight:
                        form = "br";
                        break;
                    case cir::TemplateValueFoldKind::None:
                        break;
                }
                const char* operator_name = "invalid";
                switch (node.op) {
                    case cir::TemplateValueExprOp::Add:
                        operator_name = "add";
                        break;
                    case cir::TemplateValueExprOp::Sub:
                        operator_name = "sub";
                        break;
                    case cir::TemplateValueExprOp::Mul:
                        operator_name = "mul";
                        break;
                    case cir::TemplateValueExprOp::Div:
                        operator_name = "div";
                        break;
                    case cir::TemplateValueExprOp::Mod:
                        operator_name = "mod";
                        break;
                    case cir::TemplateValueExprOp::Shl:
                        operator_name = "shl";
                        break;
                    case cir::TemplateValueExprOp::Shr:
                        operator_name = "shr";
                        break;
                    case cir::TemplateValueExprOp::BitAnd:
                        operator_name = "band";
                        break;
                    case cir::TemplateValueExprOp::BitOr:
                        operator_name = "bor";
                        break;
                    case cir::TemplateValueExprOp::BitXor:
                        operator_name = "bxor";
                        break;
                    case cir::TemplateValueExprOp::Less:
                        operator_name = "lt";
                        break;
                    case cir::TemplateValueExprOp::LessEqual:
                        operator_name = "le";
                        break;
                    case cir::TemplateValueExprOp::Greater:
                        operator_name = "gt";
                        break;
                    case cir::TemplateValueExprOp::GreaterEqual:
                        operator_name = "ge";
                        break;
                    case cir::TemplateValueExprOp::Equal:
                        operator_name = "eq";
                        break;
                    case cir::TemplateValueExprOp::NotEqual:
                        operator_name = "ne";
                        break;
                    case cir::TemplateValueExprOp::ThreeWay:
                        operator_name = "cmp3";
                        break;
                    case cir::TemplateValueExprOp::LogicalAnd:
                        operator_name = "land";
                        break;
                    case cir::TemplateValueExprOp::LogicalOr:
                        operator_name = "lor";
                        break;
                    case cir::TemplateValueExprOp::Comma:
                        operator_name = "comma";
                        break;
                    case cir::TemplateValueExprOp::MemberPointerDot:
                        operator_name = "dotstar";
                        break;
                    case cir::TemplateValueExprOp::MemberPointerArrow:
                        operator_name = "arrowstar";
                        break;
                    case cir::TemplateValueExprOp::UnaryPlus:
                    case cir::TemplateValueExprOp::UnaryMinus:
                    case cir::TemplateValueExprOp::LogicalNot:
                    case cir::TemplateValueExprOp::BitwiseNot:
                    case cir::TemplateValueExprOp::Dereference:
                    case cir::TemplateValueExprOp::Delete:
                    case cir::TemplateValueExprOp::DeleteArray:
                    case cir::TemplateValueExprOp::AddressOf:
                    case cir::TemplateValueExprOp::None:
                        break;
                }
                std::string name = "__aburi_fold_";
                name += form;
                name += '_';
                name += operator_name;
                for (const cir::TemplateValuePackReference& reference :
                     node.pack_references) {
                    name += "_p";
                    name += std::to_string(
                        static_cast<unsigned>(reference.kind));
                    name += 'd';
                    name += std::to_string(reference.depth);
                    name += 'i';
                    name += std::to_string(reference.index);
                }
                append_source_name(out_, name);
                encode_dependent_value_expression(expression,
                                                  node.lhs,
                                                  value_type);
                if (node.rhs != cir::TemplateValueExprNoNode) {
                    encode_dependent_value_expression(expression,
                                                      node.rhs,
                                                      value_type);
                }
                return;
            }
            case cir::TemplateValueExprKind::None:
                out_ += "L_i0E";
                return;
        }
    }

    void encode_structural_object_expression(
        const cir::TemplateArgument& argument) {
        out_ += "tl";
        cir::TypeRef value_type = argument.value_type;
        if (value_type.type.valid()) {
            encode_type(value_type);
        } else {
            out_ += 'i';
        }
        cir::TypeId resolved = value_type.type.valid()
            ? file_.resolved_type(value_type.type)
            : cir::TypeId{};
        const cir::RecordFacts* facts = resolved.valid()
            ? file_.record_facts_for_type(resolved)
            : nullptr;
        // A union mangles as `tl <type> di <member> <value> E`.  Its
        // `value_elements` holds a single entry -- the active member's value --
        // so the value is at index 0 regardless of where the member sits in
        // the union.  Indexing by field position instead silently dropped the
        // value for any member after the first, mangling `Choice{.second = 5}`
        // as `tl6Choicedi6secondE`.
        if (facts && facts->kind == cir::RecordKind::Union &&
            argument.value_entity.valid()) {
            for (const cir::RecordFieldFact& field : facts->fields) {
                if (field.is_virtual_base_storage ||
                    field.is_flexible_array_member) {
                    continue;
                }
                if (field.entity == argument.value_entity) {
                    out_ += "di";
                    append_source_name(out_, file_.name(field.name));
                    if (!argument.value_elements.empty()) {
                        encode_template_value_expression(
                            argument.value_elements.front());
                    }
                    out_ += 'E';
                    return;
                }
            }
        }
        for (const cir::TemplateArgument& element : argument.value_elements) {
            encode_template_value_expression(element);
        }
        out_ += 'E';
    }

    void encode_template_value_expression(
        const cir::TemplateArgument& argument) {
        if (argument.value_kind == cir::TemplateValueKind::Closure ||
            argument.value_kind ==
                cir::TemplateValueKind::StructuralObject) {
            encode_structural_object_expression(argument);
            return;
        }
        if (argument.value_kind == cir::TemplateValueKind::Address) {
            out_ += "adL";
            if (argument.value_entity.valid() &&
                file_.valid(argument.value_entity)) {
                encode_referenced_entity_name(argument.value_entity);
            } else {
                out_ += '0';
            }
            if (argument.value_byte_offset != 0) {
                out_ += "pl";
                out_ += std::to_string(argument.value_byte_offset);
            }
            out_ += 'E';
            return;
        }
        if (argument.value_kind == cir::TemplateValueKind::MemberPointer &&
            argument.value_entity.valid() &&
            file_.valid(argument.value_entity)) {
            out_ += "adL";
            encode_referenced_entity_name(argument.value_entity);
            out_ += 'E';
            return;
        }

        out_ += 'L';
        cir::TypeRef value_type = argument.value_type;
        if (value_type.type.valid()) {
            encode_type(value_type);
        } else {
            out_ += 'i';
        }
        if (argument.value_kind == cir::TemplateValueKind::Floating) {
            out_ += floating::bit_pattern_hex(argument.floating_value);
        } else {
            out_ += integer_template_argument_spelling(argument);
        }
        out_ += 'E';
    }

    bool has_substitution(const std::string& key) const {
        for (const std::vector<std::string>& aliases : substitutions_) {
            for (const std::string& existing : aliases) {
                if (existing == key) {
                    return true;
                }
            }
        }
        return false;
    }

    void encode_bare_function_type(cir::TypeId function_type, bool skip_first,
                                   size_t skip_trailing = 0) {
        cir::TypeId resolved = file_.resolved_type(function_type);
        const auto* payload =
            std::get_if<cir::FunctionTypePayload>(&file_.type_payload(resolved));
        if (!payload) {
            out_ += 'v';
            return;
        }
        size_t first = skip_first && !payload->parameters.empty() ? 1 : 0;
        size_t last = payload->parameters.size();
        while (skip_trailing > 0 && last > first) {
            --last;
            --skip_trailing;
        }
        if (last <= first) {

            out_ += 'v';
        } else {
            for (size_t i = first; i < last; ++i) {

                cir::TypeRef adjusted = payload->parameters[i];
                adjusted.qualifiers = cir::QualNone;
                encode_type(adjusted);
            }
        }
        if (payload->is_variadic) {
            out_ += 'z';
        }
    }

    std::string type_key(const cir::TypeRef& ref) {
        return std::to_string(ref.type.index) + "/" +
               std::to_string(static_cast<unsigned>(ref.qualifiers));
    }

    void encode_type(const cir::TypeRef& ref) {
        cir::TypeId resolved = file_.resolved_type(ref.type);
        if (!file_.valid(resolved)) {
            out_ += "u7unknown";
            return;
        }
        const cir::Type& type = file_.type(resolved);
        bool is_builtin = type.kind == cir::TypeKind::Builtin;

        cir::TypeRef canonical{resolved, ref.qualifiers, ref.memory_space};
        std::string qualified_key = type_key(canonical);
        if (!is_builtin || ref.qualifiers != cir::QualNone) {
            if (emit_substitution(qualified_key)) {
                return;
            }
        }

        if (ref.qualifiers != cir::QualNone) {
            if (ref.qualifiers & cir::QualRestrict) {
                out_ += 'r';
            }
            if (ref.qualifiers & cir::QualVolatile) {
                out_ += 'V';
            }
            if (ref.qualifiers & cir::QualConst) {
                out_ += 'K';
            }
            cir::TypeRef unqualified{resolved, cir::QualNone, ref.memory_space};
            encode_type(unqualified);
            add_substitution(qualified_key);
            return;
        }

        const cir::TypePayload& payload = file_.type_payload(resolved);
        switch (type.kind) {
            case cir::TypeKind::Builtin:
                encode_builtin(std::get<cir::BuiltinTypePayload>(payload).kind);
                return;
            case cir::TypeKind::Pointer: {
                out_ += 'P';
                encode_type(std::get<cir::PointerTypePayload>(payload).pointee);
                add_substitution(qualified_key);
                return;
            }
            case cir::TypeKind::LValueReference: {
                out_ += 'R';
                encode_type(std::get<cir::ReferenceTypePayload>(payload).referred_type);
                add_substitution(qualified_key);
                return;
            }
            case cir::TypeKind::RValueReference: {
                out_ += 'O';
                encode_type(std::get<cir::ReferenceTypePayload>(payload).referred_type);
                add_substitution(qualified_key);
                return;
            }
            case cir::TypeKind::TypeParam: {

                const auto& param = std::get<cir::TypeParamTypePayload>(payload);
                if (param.index == 0) {
                    out_ += "T_";
                } else {
                    out_ += "T" + std::to_string(param.index - 1) + "_";
                }
                add_substitution(qualified_key);
                return;
            }
            case cir::TypeKind::PackIndex:

                {
                    const auto& pack_index =
                        std::get<cir::PackIndexTypePayload>(payload);
                    out_ += "Dy";
                    encode_type(pack_index.pack_type);
                    encode_dependent_value_expression(
                        pack_index.index_expression,
                        pack_index.index_expression.root,
                        {});
                }
                return;
            case cir::TypeKind::BuiltinPackElement: {

                const auto& pack_element =
                    std::get<cir::BuiltinPackElementTypePayload>(payload);
                append_source_name(out_, "__type_pack_element");
                out_ += 'I';
                if (!pack_element.arguments.empty()) {
                    encode_template_argument(
                        pack_element.arguments.front());
                }
                out_ += 'J';
                for (size_t i = 1;
                     i < pack_element.arguments.size();
                     ++i) {
                    encode_template_argument(
                        pack_element.arguments[i]);
                }
                out_ += "EE";
                add_substitution(qualified_key);
                return;
            }
            case cir::TypeKind::DependentName: {
                const auto& dependent =
                    std::get<cir::DependentNameTypePayload>(payload);

                out_ += 'N';
                encode_type(dependent.qualifier_type);
                append_source_name(out_, file_.name(dependent.member_name));
                if (!dependent.template_arguments.empty()) {
                    out_ += 'I';
                    for (const cir::TemplateArgument& argument :
                         dependent.template_arguments) {
                        encode_template_argument(argument);
                    }
                    out_ += 'E';
                }
                out_ += 'E';
                add_substitution(qualified_key);
                return;
            }
            case cir::TypeKind::TemplateSpecialization: {

                out_ += "u21aburi_splice_template";
                add_substitution(qualified_key);
                return;
            }
            case cir::TypeKind::Record: {
                const auto& record = std::get<cir::RecordTypePayload>(payload);
                encode_tag_name(record.entity, record.name);
                add_substitution(qualified_key);
                return;
            }
            case cir::TypeKind::Enum: {
                const auto& enumeration = std::get<cir::EnumTypePayload>(payload);
                encode_tag_name(enumeration.entity, enumeration.name);
                add_substitution(qualified_key);
                return;
            }
            case cir::TypeKind::Function: {
                const auto& function = std::get<cir::FunctionTypePayload>(payload);
                if (function.exception_spec.kind ==
                    cir::FunctionExceptionSpecKind::NonThrowing) {

                    out_ += "Do";
                }
                out_ += 'F';
                encode_type(function.return_type);
                if (function.parameters.empty()) {
                    out_ += 'v';
                } else {
                    for (const cir::TypeRef& parameter : function.parameters) {
                        cir::TypeRef adjusted = parameter;
                        adjusted.qualifiers = cir::QualNone;
                        encode_type(adjusted);
                    }
                }
                if (function.is_variadic) {
                    out_ += 'z';
                }
                out_ += 'E';
                add_substitution(qualified_key);
                return;
            }
            case cir::TypeKind::Array: {
                const auto& array = std::get<cir::ArrayTypePayload>(payload);
                out_ += 'A';
                if (array.dependent_size_expr.valid()) {
                    encode_dependent_value_expression(
                        array.dependent_size_expr,
                        array.dependent_size_expr.root,
                        {});
                } else if (array.extent_param !=
                    cir::ArrayTypePayload::no_extent_param) {

                    if (array.extent_param == 0) {
                        out_ += "T_";
                    } else {
                        out_ += "T" + std::to_string(array.extent_param - 1) +
                                "_";
                    }
                } else if (array.size.has_value()) {
                    out_ += std::to_string(*array.size);
                }
                out_ += '_';
                encode_type(array.element_type);
                add_substitution(qualified_key);
                return;
            }
            case cir::TypeKind::Complex: {
                out_ += 'C';
                encode_type(std::get<cir::ComplexTypePayload>(payload).element_type);
                add_substitution(qualified_key);
                return;
            }
            case cir::TypeKind::Vector: {
                const auto& vector = std::get<cir::VectorTypePayload>(payload);
                out_ += "Dv" + std::to_string(vector.element_count) + "_";
                encode_type(vector.element_type);
                add_substitution(qualified_key);
                return;
            }
            case cir::TypeKind::BitInt: {
                const auto& bit_int = std::get<cir::BitIntTypePayload>(payload);
                out_ += bit_int.is_unsigned ? "DU" : "DB";
                out_ += std::to_string(bit_int.bits);
                out_ += '_';
                add_substitution(qualified_key);
                return;
            }
            case cir::TypeKind::MemberPointer: {
                const auto& member = std::get<cir::MemberPointerTypePayload>(payload);
                out_ += 'M';
                encode_type(member.class_type);
                encode_type(member.member_type);
                add_substitution(qualified_key);
                return;
            }
            case cir::TypeKind::BlockPointer: {

                out_ += "U13block_pointer";
                encode_type(std::get<cir::BlockPointerTypePayload>(payload).pointee);
                add_substitution(qualified_key);
                return;
            }
            default: {
                std::string formatted = file_.format_type(resolved);
                out_ += 'u';
                append_source_name(out_, formatted);
                return;
            }
        }
    }

    void encode_tag_name(cir::EntityId entity_id, cir::NameId fallback_name) {
        std::vector<cir::EntityId> namespaces;
        std::string source_name;
        const cir::TemplateSpecializationFact* spec = nullptr;
        if (entity_id.valid()) {
            const cir::Entity& entity = file_.entity(entity_id);
            const cir::RecordFacts* facts =
                entity.kind == cir::EntityKind::Record
                    ? file_.record_facts(entity_id)
                    : nullptr;
            bool local_record =
                entity.local_enclosing_function.valid() &&
                entity.local_name_kind !=
                    cir::LocalNameComponentKind::None;
            if (local_record) {
                std::string function_encoding =
                    enclosing_function_encoding(
                        entity.local_enclosing_function);
                if (!function_encoding.empty()) {
                    out_ += 'Z';
                    out_ += function_encoding;
                    out_ += 'E';
                    encode_local_record_component(entity_id);
                    return;
                }
            }
            // Closure naming applies wherever the closure lives — a
            // namespace-scope variable-initializer lambda has no enclosing
            // function yet still names as 14var MUlvE_ in type position.
            if (facts && file_.valid(facts->closure_identity)) {
                const cir::ClosureIdentityFact& identity =
                    file_.closure_identity(facts->closure_identity);
                if (identity.abi_context ==
                        cir::ClosureAbiContextKind::VariableInitializer &&
                    identity.abi_context_decl.valid()) {
                    std::vector<cir::EntityId> context_prefix;
                    cir::DeclContextId context = identity.abi_context_decl;
                    while (context.valid() && file_.valid(context)) {
                        const cir::DeclContext& declaration =
                            file_.decl_context(context);
                        if (declaration.kind ==
                            cir::DeclContextKind::TranslationUnit) {
                            break;
                        }
                        if (declaration.kind ==
                            cir::DeclContextKind::TemplateParameter) {
                            context = declaration.parent;
                            continue;
                        }
                        if ((declaration.kind !=
                                 cir::DeclContextKind::Namespace &&
                             declaration.kind !=
                                 cir::DeclContextKind::Record) ||
                            !declaration.owner.valid()) {
                            context_prefix.clear();
                            break;
                        }
                        context_prefix.insert(context_prefix.begin(),
                                              declaration.owner);
                        context = declaration.parent;
                    }
                    if (!context_prefix.empty()) {
                        out_ += 'N';
                        encode_prefix(context_prefix);
                        encode_local_record_component(entity_id);
                        out_ += 'E';
                        return;
                    }
                }
                encode_local_record_component(entity_id);
                return;
            }
            if (local_record) {
                encode_local_record_component(entity_id);
                return;
            }
            cir::NameId abi_name = linkage_source_name(entity);
            if (abi_name.valid()) {
                source_name = file_.name(abi_name);
            }
            spec = file_.template_specialization(entity_id);

            cir::EntityId scope_owner = entity_id;
            if (spec && spec->template_entity.valid() &&
                file_.valid(spec->template_entity)) {
                scope_owner = spec->template_entity;
            }
            if (!namespace_chain(scope_owner, namespaces)) {
                namespaces.clear();
            }
            if (has_record_scope_unnamed_name(entity)) {
                if (!namespaces.empty()) {
                    out_ += 'N';
                    encode_prefix(namespaces);
                }
                out_ += record_scope_unnamed_component(entity);
                if (!namespaces.empty()) {
                    out_ += 'E';
                }
                return;
            }
        }
        if (spec) {
            encode_specialized_name(namespaces, *spec);
            return;
        }
        if (source_name.empty() && fallback_name.valid()) {
            source_name = file_.name(fallback_name);
        }
        if (source_name.empty()) {
            source_name = "<anonymous>";
        }
        terminal_module_entity_ = entity_id;
        encode_entity_name(namespaces, source_name);
    }

    void encode_builtin(cir::BuiltinTypeKind kind) {
        switch (kind) {
            case cir::BuiltinTypeKind::Void: out_ += 'v'; return;
            case cir::BuiltinTypeKind::Bool: out_ += 'b'; return;
            case cir::BuiltinTypeKind::Char: out_ += 'c'; return;
            case cir::BuiltinTypeKind::SChar: out_ += 'a'; return;
            case cir::BuiltinTypeKind::UChar: out_ += 'h'; return;
            case cir::BuiltinTypeKind::Short: out_ += 's'; return;
            case cir::BuiltinTypeKind::UShort: out_ += 't'; return;
            case cir::BuiltinTypeKind::Int: out_ += 'i'; return;
            case cir::BuiltinTypeKind::UInt: out_ += 'j'; return;
            case cir::BuiltinTypeKind::Long: out_ += 'l'; return;
            case cir::BuiltinTypeKind::ULong: out_ += 'm'; return;
            case cir::BuiltinTypeKind::LongLong: out_ += 'x'; return;
            case cir::BuiltinTypeKind::ULongLong: out_ += 'y'; return;
            case cir::BuiltinTypeKind::Int128: out_ += 'n'; return;
            case cir::BuiltinTypeKind::UInt128: out_ += 'o'; return;

            case cir::BuiltinTypeKind::USize: out_ += 'm'; return;
            case cir::BuiltinTypeKind::WChar: out_ += 'w'; return;
            case cir::BuiltinTypeKind::Char8: out_ += "Du"; return;
            case cir::BuiltinTypeKind::Char16: out_ += "Ds"; return;
            case cir::BuiltinTypeKind::Char32: out_ += "Di"; return;
            case cir::BuiltinTypeKind::Float16: out_ += "DF16_"; return;
            case cir::BuiltinTypeKind::Float: out_ += 'f'; return;
            case cir::BuiltinTypeKind::Double: out_ += 'd'; return;
            case cir::BuiltinTypeKind::LongDouble: out_ += 'e'; return;
            case cir::BuiltinTypeKind::NullPtr: out_ += "Dn"; return;
            default: out_ += "u5other"; return;
        }
    }
};

} // namespace

std::string itanium_linkage_name(const cir::File& file, cir::EntityId entity) {
    if (!file.valid(entity)) {
        return {};
    }
    ItaniumMangler mangler(file);
    return mangler.mangle(entity);
}

std::string itanium_structor_variant_name(const cir::File& file,
                                          cir::EntityId entity,
                                          const char* variant,
                                          bool skip_trailing_param,
                                          cir::EntityId
                                              inherited_origin_record) {
    if (!file.valid(entity)) {
        return {};
    }
    ItaniumMangler mangler(file);
    mangler.set_structor_variant(variant);
    mangler.set_skip_trailing_param(skip_trailing_param);
    mangler.set_inherited_constructor_origin(inherited_origin_record);
    return mangler.mangle(entity);
}

std::string itanium_record_data_symbol(const cir::File& file,
                                       cir::EntityId record_entity,
                                       const char* prefix) {
    ItaniumMangler mangler(file);
    return mangler.record_data_symbol(record_entity, prefix);
}

std::string itanium_type_data_symbol(const cir::File& file,
                                     cir::TypeRef type,
                                     const char* prefix) {
    ItaniumMangler mangler(file);
    return mangler.type_data_symbol(type, prefix);
}

std::string itanium_construction_vtable_symbol(const cir::File& file,
                                               cir::EntityId derived_entity,
                                               cir::EntityId base_entity,
                                               size_t offset) {
    ItaniumMangler mangler(file);
    return mangler.construction_vtable_symbol(derived_entity, base_entity,
                                              offset);
}

std::string itanium_virtual_thunk_symbol(
    const cir::File& file,
    cir::EntityId target,
    const cir::VirtualAdjustmentFact& this_adjustment,
    const cir::VirtualAdjustmentFact& result_adjustment) {
    std::string target_name = file.entity(target).is_extern_c
        ? std::string(file.name(file.entity(target).name))
        : itanium_linkage_name(file, target);
    if (target_name.size() < 3 || target_name.rfind("_Z", 0) != 0) {
        return {};
    }
    auto signed_offset = [](int64_t offset) {
        if (offset < 0) {
            uint64_t magnitude =
                static_cast<uint64_t>(-(offset + 1)) + uint64_t{1};
            return std::string("n") + std::to_string(magnitude);
        }
        return std::to_string(static_cast<uint64_t>(offset));
    };
    auto call_offset = [&](const cir::VirtualAdjustmentFact& adjustment) {
        if (adjustment.kind == cir::VirtualAdjustmentKind::Virtual) {
            return std::string("v") +
                signed_offset(adjustment.static_offset_bytes) + "_" +
                signed_offset(adjustment.vtable_offset_bytes) + "_";
        }
        return std::string("h") +
            signed_offset(adjustment.kind ==
                                  cir::VirtualAdjustmentKind::None
                              ? 0
                              : adjustment.static_offset_bytes) +
            "_";
    };
    std::string suffix = target_name.substr(2);
    if (result_adjustment.required()) {
        return "_ZTc" + call_offset(this_adjustment) +
            call_offset(result_adjustment) + suffix;
    }
    if (this_adjustment.kind == cir::VirtualAdjustmentKind::Virtual) {
        return "_ZTv" + signed_offset(this_adjustment.static_offset_bytes) +
            "_" + signed_offset(this_adjustment.vtable_offset_bytes) + "_" +
            suffix;
    }
    return "_ZTh" + signed_offset(this_adjustment.static_offset_bytes) +
        "_" + suffix;
}

} // namespace aburi::abi
