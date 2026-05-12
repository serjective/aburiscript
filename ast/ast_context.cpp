#include "ast_context.h"
#include "ast.h"
#include "semantic_store.h"
#include "abi/target_info.h"

#include <limits>
#include <sstream>

// Static empty list returned by get_attrs when no attributes exist for a node
static const AttributeList empty_attr_list{};

namespace {
// Threading: g_active_side_table_ast_context is thread_local, so it is safe
// for per-thread use.  However, the registration map and ID counter below
// are plain globals with NO synchronization.  They are safe only under the
// current single-threaded compilation model.  If parallel compilation is
// introduced, protect with a mutex or move into a session-owned context.
thread_local ASTContext* g_active_side_table_ast_context = nullptr;
std::unordered_map<uint32_t, ASTContext*> g_registered_ast_contexts;
uint32_t g_next_ast_context_registry_id = 1;

std::string pointer_identity_string(const void* ptr) {
    return std::to_string(reinterpret_cast<uintptr_t>(ptr));
}

const TemplateDecl* canonical_template_decl_identity(const TemplateDecl* decl) {
    return decl ? get_template_decl_canonical_decl(decl) : nullptr;
}

const TemplateDecl* template_decl_from_decl(const Decl* decl) {
    if (const auto* alias_template =
            dyn_cast<AliasTemplateDecl>(const_cast<Decl*>(decl))) {
        return alias_template;
    }
    if (const auto* function_template =
            dyn_cast<FunctionTemplateDecl>(const_cast<Decl*>(decl))) {
        return function_template;
    }
    if (const auto* class_template =
            dyn_cast<ClassTemplateDecl>(const_cast<Decl*>(decl))) {
        return class_template;
    }
    if (const auto* concept_decl =
            dyn_cast<ConceptDecl>(const_cast<Decl*>(decl))) {
        return concept_decl;
    }
    if (const auto* partial_specialization =
            dyn_cast<ClassTemplatePartialSpecializationDecl>(
                const_cast<Decl*>(decl))) {
        return partial_specialization;
    }
    return nullptr;
}

void append_type_semantic_fingerprint(std::string& out, QualType type);
void append_template_argument_semantic_fingerprint(
    std::string& out,
    const TemplateArgument& argument);

void append_template_decl_semantic_identity(std::string& out,
                                            const TemplateDecl* decl) {
    if (const auto* canonical = canonical_template_decl_identity(decl)) {
        out += pointer_identity_string(canonical);
        return;
    }
    out += "invalid-template";
}

void append_template_parameter_semantic_fingerprint(
    std::string& out,
    const TemplateParameterDecl* parameter) {
    if (!parameter) {
        out += "null";
        return;
    }

    out += "P";
    out += std::to_string(static_cast<int>(parameter->get_kind()));
    out += ":";
    out += std::to_string(parameter->depth);
    out += ":";
    out += std::to_string(parameter->index);
    out += parameter->is_parameter_pack ? ":pack" : ":single";
    if (!parameter->get_name().empty()) {
        out += ":";
        out += parameter->get_name();
    }

    if (const auto* non_type_parameter =
            dyn_cast<TemplateNonTypeParmDecl>(
                const_cast<TemplateParameterDecl*>(parameter))) {
        out += ":type(";
        append_type_semantic_fingerprint(out, non_type_parameter->type);
        out += ")";
        return;
    }

    if (const auto* template_template_parameter =
            dyn_cast<TemplateTemplateParmDecl>(
                const_cast<TemplateParameterDecl*>(parameter))) {
        out += template_template_parameter->uses_typename_keyword
            ? ":typename("
            : ":class(";
        for (size_t idx = 0;
             idx < template_template_parameter->parameters.size();
             ++idx) {
            if (idx > 0) {
                out += ",";
            }
            append_template_parameter_semantic_fingerprint(
                out,
                template_template_parameter->parameters[idx].get());
        }
        out += ")";
    }
}

void append_symbol_semantic_fingerprint(std::string& out, const Symbol* sym) {
    if (!sym) {
        out += "null";
        return;
    }

    out += "S";
    out += std::to_string(static_cast<int>(sym->kind));
    out += ":";
    out += sym->name;
    out += ":T(";
    append_type_semantic_fingerprint(out, sym->type);
    out += ")";
    out += ":SC";
    out += std::to_string(static_cast<int>(sym->storage_class));
    out += ":L";
    out += std::to_string(static_cast<int>(sym->linkage));
    out += ":Lang";
    out += std::to_string(static_cast<int>(sym->get_language_linkage()));

    if (const auto* qualifier_prefix = get_symbol_cxx_qualifier_prefix(sym);
        qualifier_prefix && !qualifier_prefix->empty()) {
        out += ":Q";
        out += *qualifier_prefix;
    }

    if (QualType owner_type = get_symbol_owner_record_type(sym)) {
        out += ":Owner(";
        append_type_semantic_fingerprint(out, owner_type);
        out += ")";
    }

    if (const auto* specialization_info =
            get_symbol_function_template_specialization(sym);
        specialization_info && specialization_info->primary_template) {
        out += ":FT(";
        append_template_decl_semantic_identity(
            out,
            specialization_info->primary_template);
        out += ")<";
        for (size_t idx = 0; idx < specialization_info->arguments.size(); ++idx) {
            if (idx > 0) {
                out += ",";
            }
            append_template_argument_semantic_fingerprint(
                out,
                specialization_info->arguments[idx]);
        }
        out += ">";
    }

    if (sym->asm_label.has_value()) {
        out += ":Asm";
        out += *sym->asm_label;
    }
}

void append_const_value_semantic_fingerprint(std::string& out,
                                             const ConstValue& value) {
    switch (value.kind) {
        case ConstValueKind::Invalid:
            out += "invalid";
            return;
        case ConstValueKind::Integer:
            out += value.int_value.is_unsigned ? "u:" : "s:";
            out += value.int_value.is_unsigned
                ? std::to_string(value.int_value.to_unsigned_u64())
                : std::to_string(
                      static_cast<uint64_t>(value.int_value.to_signed_i64()));
            out += ":w";
            out += std::to_string(value.int_value.bit_width);
            return;
        case ConstValueKind::Boolean:
            out += value.bool_value ? "true" : "false";
            return;
        case ConstValueKind::Floating: {
            std::ostringstream stream;
            stream.precision(std::numeric_limits<long double>::max_digits10);
            stream << value.float_value.value;
            out += "f:";
            out += stream.str();
            out += ":w";
            out += std::to_string(value.float_value.bit_width);
            return;
        }
        case ConstValueKind::NullPointer:
            out += "null";
            return;
        case ConstValueKind::Address:
            out += "addr:";
            append_symbol_semantic_fingerprint(out, value.address_value.symbol.get());
            out += ":off";
            out += std::to_string(value.address_value.byte_offset);
            return;
        case ConstValueKind::MemberPointer:
            out += value.member_pointer_value.is_function_member
                ? "mfn:"
                : "mdata:";
            append_symbol_semantic_fingerprint(
                out,
                value.member_pointer_value.method_symbol.get());
            out += ":off";
            out += std::to_string(value.member_pointer_value.byte_offset);
            out += ":slot";
            out += std::to_string(value.member_pointer_value.virtual_slot_index);
            if (value.member_pointer_value.member_name) {
                out += ":name:";
                out += *value.member_pointer_value.member_name;
            }
            return;
        case ConstValueKind::Object:
            out += value.object_value &&
                    value.object_value->kind == ConstObjectValueKind::Record
                ? "obj:{"
                : "arr:[";
            if (value.object_value) {
                for (size_t idx = 0; idx < value.object_value->elements.size(); ++idx) {
                    if (idx > 0) {
                        out += ",";
                    }
                    append_const_value_semantic_fingerprint(
                        out,
                        value.object_value->elements[idx]);
                }
            }
            out += value.object_value &&
                    value.object_value->kind == ConstObjectValueKind::Record
                ? "}"
                : "]";
            return;
    }
}

void append_template_argument_semantic_fingerprint(
    std::string& out,
    const TemplateArgument& argument) {
    out += "A";
    if (argument.expands_parameter_pack) {
        out += "PX[";
        if (argument.pack_expansion_parameters.empty()) {
            out += "implicit";
        } else {
            for (size_t idx = 0; idx < argument.pack_expansion_parameters.size();
                 ++idx) {
                if (idx > 0) {
                    out += ",";
                }
                append_template_parameter_semantic_fingerprint(
                    out,
                    argument.pack_expansion_parameters[idx]);
            }
        }
        out += "]";
    }

    switch (argument.kind) {
        case TemplateArgumentKind::Type:
            out += "T(";
            append_type_semantic_fingerprint(out, argument.type);
            out += ")";
            return;
        case TemplateArgumentKind::Value:
            out += "V(";
            append_type_semantic_fingerprint(out, argument.value_type);
            out += "):";
            if (argument.is_dependent) {
                if (argument.referenced_parameter) {
                    out += "dep:";
                    append_template_parameter_semantic_fingerprint(
                        out,
                        argument.referenced_parameter);
                } else if (!argument.value_spelling.empty()) {
                    out += "sp:";
                    out += argument.value_spelling;
                } else {
                    out += "dep";
                }
                return;
            }
            append_const_value_semantic_fingerprint(out, argument.value);
            return;
        case TemplateArgumentKind::Template:
            out += "TT:";
            if (argument.is_dependent) {
                if (argument.referenced_parameter) {
                    out += "dep:";
                    append_template_parameter_semantic_fingerprint(
                        out,
                        argument.referenced_parameter);
                } else if (!argument.template_name.empty()) {
                    out += "sp:";
                    out += argument.template_name;
                } else {
                    out += "dep";
                }
                return;
            }
            if (argument.template_decl) {
                append_template_decl_semantic_identity(out, argument.template_decl);
                return;
            }
            if (!argument.template_name.empty()) {
                out += "name:";
                out += argument.template_name;
                return;
            }
            out += "invalid";
            return;
    }
}

void append_type_semantic_fingerprint(std::string& out, QualType type) {
    auto canonical = desugar_type(type);
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
            auto builtin = static_cast<const BuiltinType*>(raw.get());
            out += "b";
            out += std::to_string(static_cast<int>(builtin->builtin_kind));
            return;
        }
        case TypeKind::Pointer: {
            auto ptr = static_cast<const PointerType*>(raw.get());
            out += "P(";
            append_type_semantic_fingerprint(out, ptr->pointed_type);
            out += ")";
            return;
        }
        case TypeKind::Reference: {
            auto ref = static_cast<const ReferenceType*>(raw.get());
            out += ref->isLValueReference() ? "L(" : "R(";
            append_type_semantic_fingerprint(out, ref->referred_type);
            out += ")";
            return;
        }
        case TypeKind::MemberPointer: {
            auto mem_ptr = static_cast<const MemberPointerType*>(raw.get());
            out += "M(";
            append_type_semantic_fingerprint(out, mem_ptr->class_type);
            out += ")(";
            append_type_semantic_fingerprint(out, mem_ptr->member_type);
            out += ")";
            return;
        }
        case TypeKind::BlockPointer: {
            auto blk = static_cast<const BlockPointerType*>(raw.get());
            out += "B(";
            append_type_semantic_fingerprint(out, blk->pointed_type);
            out += ")";
            return;
        }
        case TypeKind::Array: {
            auto arr = static_cast<const ArrayType*>(raw.get());
            out += "Arr(";
            append_type_semantic_fingerprint(out, arr->element_type);
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
        case TypeKind::Function: {
            auto func = static_cast<const FunctionType*>(raw.get());
            out += "F(";
            append_type_semantic_fingerprint(out, func->ret_type);
            out += ")(";
            for (size_t idx = 0; idx < func->parameters.size(); ++idx) {
                if (idx > 0) {
                    out += ",";
                }
                append_type_semantic_fingerprint(out, func->parameters[idx]);
            }
            out += ")";
            out += func->is_variadic ? "V" : "N";
            out += func->has_prototype ? "P" : "K";
            out += ":RQ";
            out += std::to_string(static_cast<int>(func->member_ref_qualifier));
            out += ":ES";
            out += std::to_string(static_cast<int>(func->exception_spec));
            out += func->has_explicit_exception_spec ? ":X" : ":I";
            if (func->exception_spec_expr) {
                out += ":EXPR";
                out += pointer_identity_string(func->exception_spec_expr.get());
            }
            return;
        }
        case TypeKind::Object: {
            auto object = static_cast<const ObjectType*>(raw.get());
            out += "O";
            if (object->get_decl()) {
                out += pointer_identity_string(object->get_decl());
                return;
            }
            out += "anon:";
            out += object->to_string();
            return;
        }
        case TypeKind::Enum: {
            auto enum_type = static_cast<const EnumType*>(raw.get());
            out += "E";
            if (enum_type->get_decl()) {
                out += pointer_identity_string(enum_type->get_decl());
                return;
            }
            out += "anon:";
            out += enum_type->to_string();
            return;
        }
        case TypeKind::CppTypeInfo: {
            auto type_info = static_cast<const CppTypeInfoType*>(raw.get());
            out += "TI";
            out += std::to_string(type_info->descriptor_width_bits);
            return;
        }
        case TypeKind::Vector: {
            auto vec = static_cast<const VectorType*>(raw.get());
            out += "V(";
            append_type_semantic_fingerprint(out, vec->element_type);
            out += "):";
            out += std::to_string(vec->total_bytes);
            return;
        }
        case TypeKind::Complex: {
            auto complex = static_cast<const ComplexType*>(raw.get());
            out += "C";
            out += std::to_string(
                static_cast<int>(complex->element_type->builtin_kind));
            return;
        }
        case TypeKind::TemplateTypeParm: {
            auto parm = static_cast<const TemplateTypeParmType*>(raw.get());
            out += "TP";
            out += parm->is_parameter_pack ? "P" : "S";
            if (parm->parameter_decl) {
                append_template_parameter_semantic_fingerprint(
                    out,
                    parm->parameter_decl);
                return;
            }
            out += std::to_string(parm->depth);
            out += ":";
            out += std::to_string(parm->index);
            out += ":";
            out += parm->name;
            return;
        }
        case TypeKind::TemplateSpecialization: {
            auto specialization =
                static_cast<const TemplateSpecializationType*>(raw.get());
            out += "TS";
            if (const auto* template_decl =
                    template_decl_from_decl(specialization->primary_template)) {
                append_template_decl_semantic_identity(out, template_decl);
            } else if (specialization->primary_template) {
                out += "decl:";
                out += pointer_identity_string(specialization->primary_template);
            } else {
                out += specialization->template_name;
            }
            out += "<";
            for (size_t idx = 0; idx < specialization->arguments.size(); ++idx) {
                if (idx > 0) {
                    out += ",";
                }
                append_template_argument_semantic_fingerprint(
                    out,
                    specialization->arguments[idx]);
            }
            out += ">";
            if (specialization->is_dependent) {
                out += "#dep";
            }
            return;
        }
        case TypeKind::DependentName: {
            auto dependent_name = static_cast<const DependentNameType*>(raw.get());
            out += "DN(";
            append_type_semantic_fingerprint(out, dependent_name->qualifier_type);
            out += ")::";
            out += dependent_name->member_name;
            if (!dependent_name->template_arguments.empty()) {
                out += "<";
                for (size_t idx = 0;
                     idx < dependent_name->template_arguments.size();
                     ++idx) {
                    if (idx > 0) {
                        out += ",";
                    }
                    append_template_argument_semantic_fingerprint(
                        out,
                        dependent_name->template_arguments[idx]);
                }
                out += ">";
            }
            if (dependent_name->is_current_instantiation) {
                out += "#CI";
            }
            if (dependent_name->requires_typename_keyword) {
                out += "#TY";
            }
            if (dependent_name->requires_template_keyword) {
                out += "#TM";
            }
            return;
        }
        case TypeKind::Auto: {
            auto auto_type = static_cast<const AutoType*>(raw.get());
            out += "Auto";
            out += std::to_string(static_cast<int>(auto_type->flavor));
            return;
        }
        case TypeKind::TypeofExpr:
            out += "TypeofExpr";
            return;
        case TypeKind::DecltypeExpr: {
            auto decltype_type = static_cast<const DecltypeExprType*>(raw.get());
            out += "DecltypeExpr";
            if (decltype_type->use_declared_type_rule) {
                out += "#decl";
            }
            return;
        }
        case TypeKind::BuiltinTypeTransform: {
            auto transform =
                static_cast<const BuiltinTypeTransformType*>(raw.get());
            out += "BTT";
            out += std::to_string(static_cast<int>(transform->transform_kind));
            out += "(";
            append_type_semantic_fingerprint(out, transform->operand_type);
            out += ")";
            return;
        }
        case TypeKind::BuiltinTypePackElement: {
            auto pack_element =
                static_cast<const BuiltinTypePackElementType*>(raw.get());
            out += "BTPE<";
            for (size_t idx = 0; idx < pack_element->arguments.size(); ++idx) {
                if (idx > 0) {
                    out += ",";
                }
                append_template_argument_semantic_fingerprint(
                    out,
                    pack_element->arguments[idx]);
            }
            out += ">";
            return;
        }
        case TypeKind::Typedef:
            out += "Typedef(";
            append_type_semantic_fingerprint(
                out,
                static_cast<const TypedefType*>(raw.get())->underlying_type);
            out += ")";
            return;
        case TypeKind::Other:
        case TypeKind::Placeholder:
            break;
    }

    out += "K";
    out += std::to_string(static_cast<int>(raw->kind));
}

std::string make_template_specialization_semantic_fingerprint(
    const TemplateDecl* primary_template,
    const std::vector<TemplateArgument>& arguments) {
    std::string fingerprint = "template-specialization:";
    append_template_decl_semantic_identity(fingerprint, primary_template);
    fingerprint += "<";
    for (size_t idx = 0; idx < arguments.size(); ++idx) {
        if (idx > 0) {
            fingerprint += ",";
        }
        append_template_argument_semantic_fingerprint(fingerprint, arguments[idx]);
    }
    fingerprint += ">";
    return fingerprint;
}

TemplateSpecializationSemanticKey make_template_specialization_semantic_key(
    const TemplateDecl* primary_template,
    const std::vector<TemplateArgument>& arguments) {
    TemplateSpecializationSemanticKey key;
    key.primary_template = canonical_template_decl_identity(primary_template);
    key.arguments = arguments;
    return key;
}

FunctionTemplateSpecializationInfo canonicalize_function_template_specialization_info(
    FunctionTemplateSpecializationInfo info) {
    info.primary_template = dyn_cast<FunctionTemplateDecl>(
        const_cast<TemplateDecl*>(
            canonical_template_decl_identity(info.primary_template)));
    return info;
}

VariableTemplateSpecializationInfo canonicalize_variable_template_specialization_info(
    VariableTemplateSpecializationInfo info) {
    info.primary_template = dyn_cast<VariableTemplateDecl>(
        const_cast<TemplateDecl*>(
            canonical_template_decl_identity(info.primary_template)));
    return info;
}
} // namespace

bool TemplateSpecializationSemanticKey::operator==(
    const TemplateSpecializationSemanticKey& other) const {
    return make_template_specialization_semantic_fingerprint(
               primary_template,
               arguments) ==
           make_template_specialization_semantic_fingerprint(
               other.primary_template,
               other.arguments);
}

size_t TemplateSpecializationSemanticKeyHash::operator()(
    const TemplateSpecializationSemanticKey& key) const {
    return std::hash<std::string>{}(
        make_template_specialization_semantic_fingerprint(
            key.primary_template,
            key.arguments));
}

ASTContext* get_active_side_table_ast_context() {
    return g_active_side_table_ast_context;
}

ASTContext* get_side_table_ast_context_for(const FuncDecl* decl) {
    if (!decl) {
        return nullptr;
    }
    if (auto* store =
            lookup_registered_collect_semantic_store(
                decl->external_semantic_owner_id)) {
        return store->ast_context();
    }
    return nullptr;
}

ASTContext* get_side_table_ast_context_for(const VariableDecl* decl) {
    if (!decl) {
        return nullptr;
    }
    if (auto* store =
            lookup_registered_collect_semantic_store(
                decl->external_semantic_owner_id)) {
        return store->ast_context();
    }
    return nullptr;
}

ASTContext* get_side_table_ast_context_for(const TemplateDecl* decl) {
    if (!decl) {
        return nullptr;
    }
    if (auto* store =
            lookup_registered_collect_semantic_store(
                decl->external_semantic_owner_id)) {
        return store->ast_context();
    }
    return nullptr;
}

ASTContext* get_side_table_ast_context_for(const TemplateParameterDecl* decl) {
    if (!decl) {
        return nullptr;
    }
    if (auto* store =
            lookup_registered_collect_semantic_store(
                decl->external_semantic_owner_id)) {
        return store->ast_context();
    }
    return nullptr;
}

ASTContext* get_side_table_ast_context_for(const ParamDecl* decl) {
    if (!decl) {
        return nullptr;
    }
    if (auto* store =
            lookup_registered_collect_semantic_store(
                decl->external_semantic_owner_id)) {
        return store->ast_context();
    }
    return nullptr;
}

ASTContext* get_side_table_ast_context_for(const ObjectDecl* decl) {
    if (!decl) {
        return nullptr;
    }
    if (auto* store =
            lookup_registered_collect_semantic_store(
                decl->external_semantic_owner_id)) {
        return store->ast_context();
    }
    return nullptr;
}

ASTContext* get_side_table_ast_context_for(const EnumDecl* decl) {
    if (!decl) {
        return nullptr;
    }
    if (auto* store =
            lookup_registered_collect_semantic_store(
                decl->external_semantic_owner_id)) {
        return store->ast_context();
    }
    return nullptr;
}

ASTContext* get_side_table_ast_context_for(const Symbol* sym) {
    if (!sym) {
        return nullptr;
    }
    if (auto* store =
            lookup_registered_collect_semantic_store(
                sym->external_semantic_owner_id)) {
        return store->ast_context();
    }
    return nullptr;
}

ASTContextSideTableScope::ASTContextSideTableScope(ASTContext* context)
    : previous_context_(g_active_side_table_ast_context),
      previous_semantic_store_(get_active_collect_semantic_store()) {
    g_active_side_table_ast_context = context;
    set_active_collect_semantic_store(
        context ? &context->semantic_store() : nullptr);
}

ASTContextSideTableScope::~ASTContextSideTableScope() {
    g_active_side_table_ast_context = previous_context_;
    set_active_collect_semantic_store(previous_semantic_store_);
}

ASTContext::ASTContext()
    : type_ctx(std::make_shared<TypeContext>()),
      global_tracker(std::make_shared<GlobalIdentTracker>()),
      abi_policy(std::make_shared<AbiPolicy>()) {
    registry_id_ = g_next_ast_context_registry_id++;
    g_registered_ast_contexts[registry_id_] = this;
    semantic_store_ = std::make_unique<CollectSemanticStore>(this);
    if (type_ctx && type_ctx->target) {
        *abi_policy = abi_policy_for_target(*type_ctx->target);
    }
}

ASTContext::ASTContext(std::shared_ptr<TargetInfo> ti)
    : type_ctx(std::make_shared<TypeContext>(std::move(ti))),
      global_tracker(std::make_shared<GlobalIdentTracker>()),
      abi_policy(std::make_shared<AbiPolicy>()) {
    registry_id_ = g_next_ast_context_registry_id++;
    g_registered_ast_contexts[registry_id_] = this;
    semantic_store_ = std::make_unique<CollectSemanticStore>(this);
    if (type_ctx && type_ctx->target) {
        *abi_policy = abi_policy_for_target(*type_ctx->target);
    }
}

ASTContext::~ASTContext() {
    if (g_active_side_table_ast_context == this) {
        g_active_side_table_ast_context = nullptr;
    }
    if (get_active_collect_semantic_store() == semantic_store_.get()) {
        set_active_collect_semantic_store(nullptr);
    }
    if (registry_id_ != 0) {
        auto it = g_registered_ast_contexts.find(registry_id_);
        if (it != g_registered_ast_contexts.end() && it->second == this) {
            g_registered_ast_contexts.erase(it);
        }
    }
}

CollectSemanticStore& ASTContext::semantic_store() {
    return *semantic_store_;
}

const CollectSemanticStore& ASTContext::semantic_store() const {
    return *semantic_store_;
}

const std::string* ASTContext::intern_identifier(std::string_view spelling) {
    auto [it, inserted] = identifier_pool_.emplace(spelling);
    if (inserted) {
        identifier_pool_string_storage_bytes_ += it->capacity() + 1;
    }
    return &(*it);
}

size_t ASTContext::identifier_pool_memory_usage_bytes() const {
    return sizeof(identifier_pool_) +
           identifier_pool_.bucket_count() * sizeof(void*) +
           identifier_pool_.size() * sizeof(std::string) +
           identifier_pool_string_storage_bytes_;
}

void ASTContext::set_func_decl_cxx_qualifier_prefix(
    const FuncDecl* decl,
    std::optional<std::string> prefix) {
    semantic_store_->set_func_decl_cxx_qualifier_prefix(decl, std::move(prefix));
}

const std::string* ASTContext::get_func_decl_cxx_qualifier_prefix(
    const FuncDecl* decl) const {
    return semantic_store_->get_func_decl_cxx_qualifier_prefix(decl);
}

void ASTContext::clear_func_decl_cxx_qualifier_prefixes() {
    semantic_store_->clear_func_decl_cxx_qualifier_prefixes();
}

void ASTContext::set_func_decl_owner_record_type(const FuncDecl* decl,
                                                 QualType owner_type) {
    semantic_store_->set_func_decl_owner_record_type(decl, owner_type);
}

QualType ASTContext::get_func_decl_owner_record_type(const FuncDecl* decl) const {
    return semantic_store_->get_func_decl_owner_record_type(decl);
}

void ASTContext::clear_func_decl_owner_record_types() {
    semantic_store_->clear_func_decl_owner_record_types();
}

void ASTContext::set_func_decl_function_template_specialization(
    const FuncDecl* decl,
    FunctionTemplateSpecializationInfo info) {
    semantic_store_->set_func_decl_function_template_specialization(
        decl,
        std::move(info));
}

const FunctionTemplateSpecializationInfo*
ASTContext::get_func_decl_function_template_specialization(
    const FuncDecl* decl) const {
    return semantic_store_->get_func_decl_function_template_specialization(decl);
}

void ASTContext::clear_func_decl_function_template_specializations() {
    semantic_store_->clear_func_decl_function_template_specializations();
}

void ASTContext::set_variable_decl_variable_template_specialization(
    const VariableDecl* decl,
    VariableTemplateSpecializationInfo info) {
    semantic_store_->set_variable_decl_variable_template_specialization(
        decl,
        std::move(info));
}

const VariableTemplateSpecializationInfo*
ASTContext::get_variable_decl_variable_template_specialization(
    const VariableDecl* decl) const {
    return semantic_store_->get_variable_decl_variable_template_specialization(
        decl);
}

void ASTContext::clear_variable_decl_variable_template_specializations() {
    semantic_store_->clear_variable_decl_variable_template_specializations();
}

void ASTContext::set_template_decl_canonical_decl(
    const TemplateDecl* decl,
    const TemplateDecl* canonical_decl) {
    semantic_store_->set_template_decl_canonical_decl(decl, canonical_decl);
}

const TemplateDecl* ASTContext::get_template_decl_canonical_decl(
    const TemplateDecl* decl) const {
    return semantic_store_->get_template_decl_canonical_decl(decl);
}

void ASTContext::clear_template_decl_canonical_decls() {
    semantic_store_->clear_template_decl_canonical_decls();
}

void ASTContext::set_template_parameter_default_argument(
    const TemplateParameterDecl* decl,
    std::optional<TemplateArgument> argument) {
    semantic_store_->set_template_parameter_default_argument(
        decl,
        std::move(argument));
}

const TemplateArgument* ASTContext::get_template_parameter_default_argument(
    const TemplateParameterDecl* decl) const {
    return semantic_store_->get_template_parameter_default_argument(decl);
}

void ASTContext::clear_template_parameter_default_arguments() {
    semantic_store_->clear_template_parameter_default_arguments();
}

bool ASTContext::merge_template_decl_default_arguments(
    const TemplateDecl* decl,
    size_t* conflict_param_index) {
    return semantic_store_->merge_template_decl_default_arguments(
        decl,
        conflict_param_index);
}

const std::vector<std::optional<TemplateArgument>>*
ASTContext::get_template_decl_default_arguments(const TemplateDecl* decl) const {
    return semantic_store_->get_template_decl_default_arguments(decl);
}

void ASTContext::clear_template_decl_default_arguments() {
    semantic_store_->clear_template_decl_default_arguments();
}

void ASTContext::set_param_decl_default_argument(const ParamDecl* decl,
                                                 std::unique_ptr<Expr> expr) {
    semantic_store_->set_param_decl_default_argument(decl, std::move(expr));
}

const Expr* ASTContext::get_param_decl_default_argument(
    const ParamDecl* decl) const {
    return semantic_store_->get_param_decl_default_argument(decl);
}

void ASTContext::clear_param_decl_default_arguments() {
    semantic_store_->clear_param_decl_default_arguments();
}

void ASTContext::set_symbol_cxx_qualifier_prefix(
    const Symbol* sym,
    std::optional<std::string> prefix) {
    semantic_store_->set_symbol_cxx_qualifier_prefix(sym, std::move(prefix));
}

const std::string* ASTContext::get_symbol_cxx_qualifier_prefix(
    const Symbol* sym) const {
    return semantic_store_->get_symbol_cxx_qualifier_prefix(sym);
}

void ASTContext::clear_symbol_cxx_qualifier_prefixes() {
    semantic_store_->clear_symbol_cxx_qualifier_prefixes();
}

void ASTContext::set_symbol_owner_record_type(const Symbol* sym,
                                              QualType owner_type) {
    semantic_store_->set_symbol_owner_record_type(sym, owner_type);
}

QualType ASTContext::get_symbol_owner_record_type(const Symbol* sym) const {
    return semantic_store_->get_symbol_owner_record_type(sym);
}

void ASTContext::clear_symbol_owner_record_types() {
    semantic_store_->clear_symbol_owner_record_types();
}

void ASTContext::set_symbol_function_template_specialization(
    const Symbol* sym,
    FunctionTemplateSpecializationInfo info) {
    semantic_store_->set_symbol_function_template_specialization(
        sym,
        std::move(info));
}

const FunctionTemplateSpecializationInfo*
ASTContext::get_symbol_function_template_specialization(const Symbol* sym) const {
    return semantic_store_->get_symbol_function_template_specialization(sym);
}

void ASTContext::clear_symbol_function_template_specializations() {
    semantic_store_->clear_symbol_function_template_specializations();
}

void ASTContext::set_symbol_variable_template_specialization(
    const Symbol* sym,
    VariableTemplateSpecializationInfo info) {
    semantic_store_->set_symbol_variable_template_specialization(
        sym,
        std::move(info));
}

const VariableTemplateSpecializationInfo*
ASTContext::get_symbol_variable_template_specialization(const Symbol* sym) const {
    return semantic_store_->get_symbol_variable_template_specialization(sym);
}

void ASTContext::clear_symbol_variable_template_specializations() {
    semantic_store_->clear_symbol_variable_template_specializations();
}

bool ASTContext::merge_symbol_cpp_default_arguments(
    const Symbol* sym,
    const std::vector<const Expr*>& defaults,
    size_t* conflict_param_index) {
    return semantic_store_->merge_symbol_cpp_default_arguments(
        sym,
        defaults,
        conflict_param_index);
}

const std::vector<const Expr*>* ASTContext::get_symbol_cpp_default_arguments(
    const Symbol* sym) const {
    return semantic_store_->get_symbol_cpp_default_arguments(sym);
}

void ASTContext::clear_symbol_cpp_default_arguments() {
    semantic_store_->clear_symbol_cpp_default_arguments();
}

void ASTContext::set_template_specialization_resolved_type(QualType type,
                                                           QualType resolved_type) {
    semantic_store_->set_template_specialization_resolved_type(
        std::move(type),
        std::move(resolved_type));
}

QualType ASTContext::get_template_specialization_resolved_type(
    const TemplateSpecializationType* type) const {
    return semantic_store_->get_template_specialization_resolved_type(type);
}

void ASTContext::clear_template_specialization_resolved_types() {
    semantic_store_->clear_template_specialization_resolved_types();
}

void ASTContext::set_dependent_name_resolved_type(QualType type,
                                                  QualType resolved_type) {
    semantic_store_->set_dependent_name_resolved_type(
        std::move(type),
        std::move(resolved_type));
}

QualType ASTContext::get_dependent_name_resolved_type(
    const DependentNameType* type) const {
    return semantic_store_->get_dependent_name_resolved_type(type);
}

void ASTContext::clear_dependent_name_resolved_types() {
    semantic_store_->clear_dependent_name_resolved_types();
}

void ASTContext::clear_record_semantics_cache() {
    semantic_store_->clear_record_semantics_cache();
}

void ASTContext::set_record_semantics(const ObjectDecl* record_decl,
                                      RecordSemanticState state) {
    semantic_store_->set_record_semantics(record_decl, std::move(state));
}

void ASTContext::erase_record_semantics(const ObjectDecl* record_decl) {
    semantic_store_->erase_record_semantics(record_decl);
}

const RecordSemanticState* ASTContext::lookup_record_semantics(
    const ObjectDecl* record_decl) const {
    return semantic_store_->lookup_record_semantics(record_decl);
}

uint64_t ASTContext::record_semantics_cache_epoch() const {
    return semantic_store_->record_semantics_cache_epoch();
}

void ASTContext::clear_enum_semantics_cache() {
    semantic_store_->clear_enum_semantics_cache();
}

void ASTContext::set_enum_semantics(const EnumDecl* enum_decl,
                                    EnumSemanticState state) {
    semantic_store_->set_enum_semantics(
        enum_decl,
        std::move(state));
}

void ASTContext::erase_enum_semantics(const EnumDecl* enum_decl) {
    semantic_store_->erase_enum_semantics(enum_decl);
}

bool ASTContext::lookup_enum_semantics(
    const EnumDecl* enum_decl,
    EnumSemanticState& state_out) const {
    return semantic_store_->lookup_enum_semantics(
        enum_decl,
        state_out);
}

ClassTemplateSpecializationEntry* ASTContext::lookup_class_template_specialization(
    const ClassTemplateDecl* primary_template,
    const std::vector<TemplateArgument>& arguments) {
    return semantic_store_->lookup_class_template_specialization(
        primary_template,
        arguments);
}

const ClassTemplateSpecializationEntry*
ASTContext::lookup_class_template_specialization(
    const ClassTemplateDecl* primary_template,
    const std::vector<TemplateArgument>& arguments) const {
    return semantic_store_->lookup_class_template_specialization(
        primary_template,
        arguments);
}

ClassTemplateSpecializationEntry&
ASTContext::get_or_create_class_template_specialization(
    const ClassTemplateDecl* primary_template,
    std::vector<TemplateArgument> arguments,
    std::shared_ptr<ObjectType> specialization_type,
    std::unique_ptr<ObjectDecl> specialization_decl) {
    return semantic_store_->get_or_create_class_template_specialization(
        primary_template,
        std::move(arguments),
        std::move(specialization_type),
        std::move(specialization_decl));
}

const std::vector<std::unique_ptr<ClassTemplateSpecializationEntry>>&
ASTContext::class_template_specializations() const {
    return semantic_store_->class_template_specializations();
}

FunctionTemplateSpecializationEntry*
ASTContext::lookup_function_template_specialization(
    const FunctionTemplateDecl* primary_template,
    const std::vector<TemplateArgument>& arguments) {
    return semantic_store_->lookup_function_template_specialization(
        primary_template,
        arguments);
}

const FunctionTemplateSpecializationEntry*
ASTContext::lookup_function_template_specialization(
    const FunctionTemplateDecl* primary_template,
    const std::vector<TemplateArgument>& arguments) const {
    return semantic_store_->lookup_function_template_specialization(
        primary_template,
        arguments);
}

FunctionTemplateSpecializationEntry&
ASTContext::get_or_create_function_template_specialization(
    const FunctionTemplateDecl* primary_template,
    std::vector<TemplateArgument> arguments,
    std::unique_ptr<FuncDecl> specialization_decl,
    std::shared_ptr<Symbol> specialization_symbol) {
    return semantic_store_->get_or_create_function_template_specialization(
        primary_template,
        std::move(arguments),
        std::move(specialization_decl),
        std::move(specialization_symbol));
}

const std::vector<std::unique_ptr<FunctionTemplateSpecializationEntry>>&
ASTContext::function_template_specializations() const {
    return semantic_store_->function_template_specializations();
}

VariableTemplateSpecializationEntry*
ASTContext::lookup_variable_template_specialization(
    const VariableTemplateDecl* primary_template,
    const std::vector<TemplateArgument>& arguments) {
    return semantic_store_->lookup_variable_template_specialization(
        primary_template,
        arguments);
}

const VariableTemplateSpecializationEntry*
ASTContext::lookup_variable_template_specialization(
    const VariableTemplateDecl* primary_template,
    const std::vector<TemplateArgument>& arguments) const {
    return semantic_store_->lookup_variable_template_specialization(
        primary_template,
        arguments);
}

VariableTemplateSpecializationEntry&
ASTContext::get_or_create_variable_template_specialization(
    const VariableTemplateDecl* primary_template,
    std::vector<TemplateArgument> arguments,
    std::unique_ptr<VariableDecl> specialization_decl,
    std::shared_ptr<Symbol> specialization_symbol) {
    return semantic_store_->get_or_create_variable_template_specialization(
        primary_template,
        std::move(arguments),
        std::move(specialization_decl),
        std::move(specialization_symbol));
}

const std::vector<std::unique_ptr<VariableTemplateSpecializationEntry>>&
ASTContext::variable_template_specializations() const {
    return semantic_store_->variable_template_specializations();
}

ConceptSpecializationEntry* ASTContext::lookup_concept_specialization(
    const ConceptDecl* primary_template,
    const std::vector<TemplateArgument>& arguments) {
    return semantic_store_->lookup_concept_specialization(
        primary_template,
        arguments);
}

const ConceptSpecializationEntry* ASTContext::lookup_concept_specialization(
    const ConceptDecl* primary_template,
    const std::vector<TemplateArgument>& arguments) const {
    return semantic_store_->lookup_concept_specialization(
        primary_template,
        arguments);
}

ConceptSpecializationEntry& ASTContext::get_or_create_concept_specialization(
    const ConceptDecl* primary_template,
    std::vector<TemplateArgument> arguments) {
    return semantic_store_->get_or_create_concept_specialization(
        primary_template,
        std::move(arguments));
}

const std::vector<std::unique_ptr<ConceptSpecializationEntry>>&
ASTContext::concept_specializations() const {
    return semantic_store_->concept_specializations();
}

bool ASTContext::push_template_instantiation_frame(size_t max_depth) {
    return semantic_store_->push_template_instantiation_frame(max_depth);
}

void ASTContext::pop_template_instantiation_frame() {
    semantic_store_->pop_template_instantiation_frame();
}

size_t ASTContext::template_instantiation_depth() const {
    return semantic_store_->template_instantiation_depth();
}

void ASTContext::clear_external_semantic_side_tables() {
    semantic_store_->clear_translation_unit_semantic_state();
}

void ASTContext::clear_all_semantic_state() {
    semantic_store_->clear_all_semantic_state();
}

void ASTContext::retain_external_decl(std::unique_ptr<Decl> decl) {
    semantic_store_->retain_external_decl(std::move(decl));
}

const std::vector<std::unique_ptr<Decl>>& ASTContext::retained_external_decls()
    const {
    return semantic_store_->retained_external_decls();
}

// --- Attribute side table ---

void ASTContext::set_attrs(uint32_t id, AttributeList attrs) {
    attr_table_[id] = std::move(attrs);
}

void ASTContext::append_attrs(uint32_t id, std::vector<ParsedAttribute>&& attrs) {
    if (attrs.empty()) return;
    attr_table_[id].append(std::move(attrs));
}

const AttributeList& ASTContext::get_attrs(uint32_t id) const {
    auto* found = attr_table_.find(id);
    if (found) return *found;
    return empty_attr_list;
}

AttributeList& ASTContext::get_attrs_mut(uint32_t id) {
    return attr_table_[id];
}

bool ASTContext::has_attrs(uint32_t id) const {
    return attr_table_.contains(id);
}

// --- Bitfield side table ---

void ASTContext::set_bitfield_info(uint32_t id, BitfieldInfo info) {
    bitfield_table_[id] = info;
}

BitfieldInfo* ASTContext::get_bitfield_info(uint32_t id) {
    return bitfield_table_.find(id);
}

const BitfieldInfo* ASTContext::get_bitfield_info(uint32_t id) const {
    return bitfield_table_.find(id);
}

// --- C++ member-declaration side table ---

void ASTContext::set_cpp_member_decl_info(uint32_t id, CppMemberDeclInfo info) {
    cpp_member_decl_info_table_[id] = info;
}

CppMemberDeclInfo* ASTContext::get_cpp_member_decl_info(uint32_t id) {
    return cpp_member_decl_info_table_.find(id);
}

const CppMemberDeclInfo* ASTContext::get_cpp_member_decl_info(uint32_t id) const {
    return cpp_member_decl_info_table_.find(id);
}

bool ASTContext::has_cpp_member_decl_info(uint32_t id) const {
    return cpp_member_decl_info_table_.contains(id);
}

// --- C++ variable-destructor side table ---

void ASTContext::set_cpp_variable_destructor_symbol(uint32_t id,
                                                    std::shared_ptr<Symbol> sym) {
    if (!sym) {
        cpp_variable_destructor_table_.erase(id);
        return;
    }
    cpp_variable_destructor_table_[id] = std::move(sym);
}

std::shared_ptr<Symbol>* ASTContext::get_cpp_variable_destructor_symbol(uint32_t id) {
    return cpp_variable_destructor_table_.find(id);
}

const std::shared_ptr<Symbol>* ASTContext::get_cpp_variable_destructor_symbol(
    uint32_t id) const {
    return cpp_variable_destructor_table_.find(id);
}

bool ASTContext::has_cpp_variable_destructor_symbol(uint32_t id) const {
    return cpp_variable_destructor_table_.contains(id);
}

// --- C++ virtual-call side table ---

void ASTContext::set_cpp_virtual_call_info(uint32_t id, CppVirtualCallInfo info) {
    cpp_virtual_call_info_table_[id] = std::move(info);
}

CppVirtualCallInfo* ASTContext::get_cpp_virtual_call_info(uint32_t id) {
    return cpp_virtual_call_info_table_.find(id);
}

const CppVirtualCallInfo* ASTContext::get_cpp_virtual_call_info(uint32_t id) const {
    return cpp_virtual_call_info_table_.find(id);
}

bool ASTContext::has_cpp_virtual_call_info(uint32_t id) const {
    return cpp_virtual_call_info_table_.contains(id);
}

void ASTContext::set_cpp_lambda_closure_decl_info(uint32_t id,
                                                  CppLambdaClosureDeclInfo info) {
    cpp_lambda_closure_decl_info_table_[id] = std::move(info);
}

CppLambdaClosureDeclInfo* ASTContext::get_cpp_lambda_closure_decl_info(uint32_t id) {
    return cpp_lambda_closure_decl_info_table_.find(id);
}

const CppLambdaClosureDeclInfo* ASTContext::get_cpp_lambda_closure_decl_info(
    uint32_t id) const {
    return cpp_lambda_closure_decl_info_table_.find(id);
}

bool ASTContext::has_cpp_lambda_closure_decl_info(uint32_t id) const {
    return cpp_lambda_closure_decl_info_table_.contains(id);
}

void ASTContext::set_cpp_lambda_invoker_info(uint32_t id,
                                             CppLambdaInvokerInfo info) {
    cpp_lambda_invoker_info_table_[id] = std::move(info);
}

CppLambdaInvokerInfo* ASTContext::get_cpp_lambda_invoker_info(uint32_t id) {
    return cpp_lambda_invoker_info_table_.find(id);
}

const CppLambdaInvokerInfo* ASTContext::get_cpp_lambda_invoker_info(
    uint32_t id) const {
    return cpp_lambda_invoker_info_table_.find(id);
}

bool ASTContext::has_cpp_lambda_invoker_info(uint32_t id) const {
    return cpp_lambda_invoker_info_table_.contains(id);
}
