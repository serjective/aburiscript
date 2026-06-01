#include "semantic_store.h"
#include "ast.h"

#include <limits>
#include <sstream>

namespace {
thread_local CollectSemanticStore* g_active_collect_semantic_store = nullptr;
std::unordered_map<uint32_t, CollectSemanticStore*> g_registered_semantic_stores;
uint32_t g_next_collect_semantic_store_registry_id = 1;

template<typename Map, typename Key>
typename Map::mapped_type* find_external_semantic_info(Map& map, const Key* key) {
    if (!key) {
        return nullptr;
    }
    if (key->external_semantic_owner_id == 0) {
        return nullptr;
    }
    auto it = map.find(key);
    if (it == map.end()) {
        return nullptr;
    }
    return &it->second;
}

template<typename Map, typename Key>
const typename Map::mapped_type* find_external_semantic_info(const Map& map,
                                                             const Key* key) {
    if (!key) {
        return nullptr;
    }
    if (key->external_semantic_owner_id == 0) {
        return nullptr;
    }
    auto it = map.find(key);
    if (it == map.end()) {
        return nullptr;
    }
    return &it->second;
}

template<typename Map, typename Key>
void erase_external_semantic_info_if_empty(Map& map, const Key* key) {
    if (!key) {
        return;
    }
    auto it = map.find(key);
    if (it != map.end() && it->second.empty()) {
        map.erase(it);
    }
}

void erase_func_decl_owner_if_unused(const CollectSemanticStore* store,
                                     const FuncDecl* decl) {
    if (!store || !decl) {
        return;
    }
    if (store->get_func_decl_cxx_qualifier_prefix(decl) != nullptr) {
        return;
    }
    if (store->get_func_decl_owner_record_type(decl)) {
        return;
    }
    if (store->get_func_decl_function_template_specialization(decl) != nullptr) {
        return;
    }
    if (decl->external_semantic_owner_id == store->registry_id()) {
        decl->external_semantic_owner_id = 0;
    }
}

void erase_variable_decl_owner_if_unused(const CollectSemanticStore* store,
                                         const VariableDecl* decl) {
    if (!store || !decl) {
        return;
    }
    if (store->get_variable_decl_variable_template_specialization(decl) != nullptr) {
        return;
    }
    if (decl->external_semantic_owner_id == store->registry_id()) {
        decl->external_semantic_owner_id = 0;
    }
}

void erase_symbol_owner_if_unused(const CollectSemanticStore* store,
                                  const Symbol* sym) {
    if (!store || !sym) {
        return;
    }
    if (store->get_symbol_cxx_qualifier_prefix(sym) != nullptr) {
        return;
    }
    if (store->get_symbol_owner_record_type(sym)) {
        return;
    }
    if (store->get_symbol_function_template_specialization(sym) != nullptr) {
        return;
    }
    if (store->get_symbol_variable_template_specialization(sym) != nullptr) {
        return;
    }
    if (store->get_symbol_cpp_default_arguments(sym) != nullptr) {
        return;
    }
    if (sym->external_semantic_owner_id == store->registry_id()) {
        sym->external_semantic_owner_id = 0;
    }
}

void erase_template_decl_owner_if_unused(const CollectSemanticStore* store,
                                         const TemplateDecl* decl) {
    if (!store || !decl) {
        return;
    }
    if (store->get_template_decl_cxx_qualifier_prefix(decl) != nullptr) {
        return;
    }
    if (store->get_template_decl_owner_record_type(decl)) {
        return;
    }
    if (!decl->merged_default_arguments.empty()) {
        return;
    }
    const TemplateDecl* canonical = store->get_template_decl_canonical_decl(decl);
    if (canonical && canonical != decl) {
        return;
    }
    if (decl->definition_decl) {
        return;
    }
    if (decl->external_semantic_owner_id == store->registry_id()) {
        decl->external_semantic_owner_id = 0;
    }
}

void erase_object_decl_owner_if_unused(const CollectSemanticStore* store,
                                       const ObjectDecl* decl) {
    if (!store || !decl) {
        return;
    }
    if (store->get_object_decl_cxx_qualifier_prefix(decl) != nullptr) {
        return;
    }
    if (store->get_object_decl_owner_record_type(decl)) {
        return;
    }
    if (store->lookup_record_semantics(decl) != nullptr) {
        return;
    }
    if (decl->external_semantic_owner_id == store->registry_id()) {
        decl->external_semantic_owner_id = 0;
    }
}

void erase_template_parameter_decl_owner_if_unused(
    const CollectSemanticStore* store,
    const TemplateParameterDecl* decl) {
    if (!store || !decl) {
        return;
    }
    if (decl->default_argument.has_value()) {
        return;
    }
    if (decl->external_semantic_owner_id == store->registry_id()) {
        decl->external_semantic_owner_id = 0;
    }
}

void erase_param_decl_owner_if_unused(const CollectSemanticStore* store,
                                      const ParamDecl* decl) {
    if (!store || !decl) {
        return;
    }
    if (store->get_param_decl_default_argument(decl) != nullptr) {
        return;
    }
    if (decl->external_semantic_owner_id == store->registry_id()) {
        decl->external_semantic_owner_id = 0;
    }
}

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

    if (const auto* specialization_info =
            get_symbol_variable_template_specialization(sym);
        specialization_info && specialization_info->primary_template) {
        out += ":VT(";
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

void append_qualified_expr_info_semantic_fingerprint(
    std::string& out,
    const CppQualifiedExprInfo* info) {
    if (!info || !info->has_qualifier()) {
        out += "Q:none";
        return;
    }
    out += "Q:";
    out += info->has_global_qualifier ? "global:" : "relative:";
    out += info->is_type_qualified ? "type:" : "namespace:";
    out += info->is_current_instantiation ? "current:" : "ordinary:";
    append_type_semantic_fingerprint(out, info->qualifier_type);
    out += ":";
    for (size_t idx = 0; idx < info->qualifiers.size(); ++idx) {
        if (idx > 0) {
            out += "::";
        }
        out += info->qualifiers[idx];
    }
}

void append_dependent_lookup_qualifier_semantic_fingerprint(
    std::string& out,
    const DependentLookupQualifier& qualifier) {
    out += "DLQ:";
    out += qualifier.has_global_qualifier ? "global:" : "relative:";
    out += qualifier.is_type_qualified ? "type:" : "namespace:";
    out += qualifier.is_current_instantiation ? "current:" : "ordinary:";
    append_type_semantic_fingerprint(out, qualifier.qualifier_type);
    out += ":";
    for (size_t idx = 0; idx < qualifier.qualifiers.size(); ++idx) {
        if (idx > 0) {
            out += "::";
        }
        out += qualifier.qualifiers[idx];
    }
}

void append_expr_semantic_fingerprint(std::string& out, const Expr* expr) {
    if (!expr) {
        out += "E:null";
        return;
    }
    out += "E";
    out += std::to_string(static_cast<int>(expr->get_kind()));
    out += "(";
    append_type_semantic_fingerprint(
        out,
        const_cast<Expr*>(expr)->get_type());
    out += "):";

    switch (expr->get_kind()) {
        case StmtKind::IntegerLiteral: {
            const auto* literal = static_cast<const IntegerLiteral*>(expr);
            out += "int:";
            out += literal->get_value();
            return;
        }
        case StmtKind::VarRef:
        case StmtKind::QualifiedVarRef: {
            const auto* var_ref = static_cast<const VarRef*>(expr);
            out += "var:";
            out += var_ref->get_name();
            out += ":sym:";
            append_symbol_semantic_fingerprint(out, var_ref->symref.get());
            out += ":";
            append_qualified_expr_info_semantic_fingerprint(
                out,
                var_ref->get_cpp_qualified_info());
            return;
        }
        case StmtKind::UnresolvedLookupExpr: {
            const auto* lookup =
                static_cast<const UnresolvedLookupExpr*>(expr);
            out += "lookup:";
            out += lookup->name;
            out += ":";
            append_dependent_lookup_qualifier_semantic_fingerprint(
                out,
                lookup->qualifier);
            out += ":template:";
            out += lookup->requires_template_keyword ? "yes:" : "no:";
            out += lookup->is_dependent ? "dep:" : "nondep:";
            if (lookup->explicit_template_arguments.has_value()) {
                out += "<";
                for (size_t idx = 0;
                     idx < lookup->explicit_template_arguments->size();
                     ++idx) {
                    if (idx > 0) {
                        out += ",";
                    }
                    append_template_argument_semantic_fingerprint(
                        out,
                        (*lookup->explicit_template_arguments)[idx]);
                }
                out += ">";
            }
            return;
        }
        case StmtKind::DependentUnaryExpr: {
            const auto* unary =
                static_cast<const DependentUnaryExpr*>(expr);
            out += "du:";
            out += std::to_string(static_cast<int>(unary->uop));
            out += ":";
            append_expr_semantic_fingerprint(out, unary->operand.get());
            return;
        }
        case StmtKind::UnaryOperation: {
            const auto* unary = static_cast<const UnaryOperation*>(expr);
            out += "u:";
            out += std::to_string(static_cast<int>(unary->uop));
            out += ":";
            append_expr_semantic_fingerprint(out, unary->exp.get());
            return;
        }
        case StmtKind::ParenExpr: {
            const auto* paren = static_cast<const ParenExpr*>(expr);
            out += "p:";
            append_expr_semantic_fingerprint(out, paren->subexpr.get());
            return;
        }
        case StmtKind::DependentBinaryExpr: {
            const auto* binary =
                static_cast<const DependentBinaryExpr*>(expr);
            out += "db:";
            out += std::to_string(static_cast<int>(binary->bop));
            out += ":";
            append_expr_semantic_fingerprint(out, binary->left.get());
            out += ":";
            append_expr_semantic_fingerprint(out, binary->right.get());
            return;
        }
        case StmtKind::BinaryOperation: {
            const auto* binary = static_cast<const BinaryOperation*>(expr);
            out += "b:";
            out += std::to_string(static_cast<int>(binary->bop));
            out += ":";
            append_expr_semantic_fingerprint(out, binary->left.get());
            out += ":";
            append_expr_semantic_fingerprint(out, binary->right.get());
            return;
        }
        case StmtKind::ExplicitCast: {
            const auto* cast = static_cast<const ExplicitCast*>(expr);
            out += "ecast:";
            out += std::to_string(static_cast<int>(cast->cast_kind));
            out += ":";
            append_type_semantic_fingerprint(out, cast->ctype);
            out += ":";
            append_expr_semantic_fingerprint(out, cast->expr.get());
            return;
        }
        case StmtKind::ImplicitCast: {
            const auto* cast = static_cast<const ImplicitCast*>(expr);
            out += "icast:";
            out += std::to_string(static_cast<int>(cast->kind));
            out += ":";
            append_type_semantic_fingerprint(out, cast->ctype);
            out += ":";
            append_expr_semantic_fingerprint(out, cast->expr.get());
            return;
        }
        default:
            out += "kind-only";
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
                } else if (argument.value_expr) {
                    out += "expr:";
                    append_expr_semantic_fingerprint(
                        out,
                        argument.value_expr.get());
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
                out += func->parameter_is_pack(idx) ? "P:" : "S:";
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
            if (func->exception_spec == FunctionExceptionSpecKind::Dependent &&
                func->exception_spec_expr) {
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
    // Specialization lookup keys canonicalize the template identity separately.
    // The side-table info must retain the selected redeclaration so deferred
    // materialization can instantiate from the definition-bearing pattern.
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

CollectSemanticStore::CollectSemanticStore(ASTContext* owner_ast_ctx)
    : owner_ast_ctx_(owner_ast_ctx) {
    registry_id_ = g_next_collect_semantic_store_registry_id++;
    g_registered_semantic_stores[registry_id_] = this;
}

CollectSemanticStore::~CollectSemanticStore() {
    if (g_active_collect_semantic_store == this) {
        g_active_collect_semantic_store = nullptr;
    }
    if (registry_id_ != 0) {
        auto it = g_registered_semantic_stores.find(registry_id_);
        if (it != g_registered_semantic_stores.end() && it->second == this) {
            g_registered_semantic_stores.erase(it);
        }
    }
}

CollectSemanticStore* get_active_collect_semantic_store() {
    return g_active_collect_semantic_store;
}

void set_active_collect_semantic_store(CollectSemanticStore* store) {
    g_active_collect_semantic_store = store;
}

CollectSemanticStore* lookup_registered_collect_semantic_store(
    uint32_t registry_id) {
    if (registry_id == 0) {
        return nullptr;
    }
    auto it = g_registered_semantic_stores.find(registry_id);
    if (it == g_registered_semantic_stores.end()) {
        return nullptr;
    }
    return it->second;
}

const CollectSemanticStore* lookup_registered_collect_semantic_store_const(
    uint32_t registry_id) {
    return lookup_registered_collect_semantic_store(registry_id);
}

void CollectSemanticStore::set_func_decl_cxx_qualifier_prefix(
    const FuncDecl* decl,
    std::optional<std::string> prefix) {
    if (!decl) {
        return;
    }
    auto& info = func_decl_semantic_info_map_[decl];
    if (!prefix.has_value() || prefix->empty()) {
        info.cxx_qualifier_prefix = nullptr;
        erase_external_semantic_info_if_empty(func_decl_semantic_info_map_, decl);
        erase_func_decl_owner_if_unused(this, decl);
        return;
    }
    auto [it, _] = external_qualifier_pool_.emplace(std::move(*prefix));
    info.cxx_qualifier_prefix = &(*it);
    decl->external_semantic_owner_id = registry_id_;
}

const std::string* CollectSemanticStore::get_func_decl_cxx_qualifier_prefix(
    const FuncDecl* decl) const {
    const auto* info = find_external_semantic_info(func_decl_semantic_info_map_, decl);
    if (!info) {
        return nullptr;
    }
    return info->cxx_qualifier_prefix;
}

void CollectSemanticStore::clear_func_decl_cxx_qualifier_prefixes() {
    std::vector<const FuncDecl*> decls;
    decls.reserve(func_decl_semantic_info_map_.size());
    for (const auto& [decl, info] : func_decl_semantic_info_map_) {
        if (info.cxx_qualifier_prefix != nullptr) {
            decls.push_back(decl);
        }
    }
    for (const FuncDecl* decl : decls) {
        auto* info = find_external_semantic_info(func_decl_semantic_info_map_, decl);
        if (info) {
            info->cxx_qualifier_prefix = nullptr;
        }
        erase_external_semantic_info_if_empty(func_decl_semantic_info_map_, decl);
        erase_func_decl_owner_if_unused(this, decl);
    }
}

void CollectSemanticStore::set_func_decl_owner_record_type(const FuncDecl* decl,
                                                           QualType owner_type) {
    if (!decl) {
        return;
    }
    auto& info = func_decl_semantic_info_map_[decl];
    if (!owner_type) {
        info.owner_record_type = QualType();
        erase_external_semantic_info_if_empty(func_decl_semantic_info_map_, decl);
        erase_func_decl_owner_if_unused(this, decl);
        return;
    }
    info.owner_record_type = owner_type;
    decl->external_semantic_owner_id = registry_id_;
}

QualType CollectSemanticStore::get_func_decl_owner_record_type(
    const FuncDecl* decl) const {
    const auto* info = find_external_semantic_info(func_decl_semantic_info_map_, decl);
    if (!info) {
        return QualType();
    }
    return info->owner_record_type;
}

void CollectSemanticStore::clear_func_decl_owner_record_types() {
    std::vector<const FuncDecl*> decls;
    decls.reserve(func_decl_semantic_info_map_.size());
    for (const auto& [decl, info] : func_decl_semantic_info_map_) {
        if (info.owner_record_type) {
            decls.push_back(decl);
        }
    }
    for (const FuncDecl* decl : decls) {
        auto* info = find_external_semantic_info(func_decl_semantic_info_map_, decl);
        if (info) {
            info->owner_record_type = QualType();
        }
        erase_external_semantic_info_if_empty(func_decl_semantic_info_map_, decl);
        erase_func_decl_owner_if_unused(this, decl);
    }
}

void CollectSemanticStore::set_func_decl_function_template_specialization(
    const FuncDecl* decl,
    FunctionTemplateSpecializationInfo info) {
    if (!decl) {
        return;
    }
    ASTContextSideTableScope side_table_scope(owner_ast_ctx_);
    auto& decl_info = func_decl_semantic_info_map_[decl];
    if (!info.primary_template) {
        decl_info.function_template_specialization.reset();
        erase_external_semantic_info_if_empty(func_decl_semantic_info_map_, decl);
        erase_func_decl_owner_if_unused(this, decl);
        return;
    }
    decl_info.function_template_specialization =
        canonicalize_function_template_specialization_info(std::move(info));
    decl->external_semantic_owner_id = registry_id_;
}

const FunctionTemplateSpecializationInfo*
CollectSemanticStore::get_func_decl_function_template_specialization(
    const FuncDecl* decl) const {
    const auto* info = find_external_semantic_info(func_decl_semantic_info_map_, decl);
    if (!info || !info->function_template_specialization.has_value()) {
        return nullptr;
    }
    return &(*info->function_template_specialization);
}

void CollectSemanticStore::clear_func_decl_function_template_specializations() {
    std::vector<const FuncDecl*> decls;
    decls.reserve(func_decl_semantic_info_map_.size());
    for (const auto& [decl, info] : func_decl_semantic_info_map_) {
        if (info.function_template_specialization.has_value()) {
            decls.push_back(decl);
        }
    }
    for (const FuncDecl* decl : decls) {
        auto* info = find_external_semantic_info(func_decl_semantic_info_map_, decl);
        if (info) {
            info->function_template_specialization.reset();
        }
        erase_external_semantic_info_if_empty(func_decl_semantic_info_map_, decl);
        erase_func_decl_owner_if_unused(this, decl);
    }
}

void CollectSemanticStore::set_variable_decl_variable_template_specialization(
    const VariableDecl* decl,
    VariableTemplateSpecializationInfo info) {
    if (!decl) {
        return;
    }
    ASTContextSideTableScope side_table_scope(owner_ast_ctx_);
    auto& decl_info = variable_decl_semantic_info_map_[decl];
    if (!info.primary_template) {
        decl_info.variable_template_specialization.reset();
        erase_external_semantic_info_if_empty(
            variable_decl_semantic_info_map_,
            decl);
        erase_variable_decl_owner_if_unused(this, decl);
        return;
    }
    decl_info.variable_template_specialization =
        canonicalize_variable_template_specialization_info(std::move(info));
    decl->external_semantic_owner_id = registry_id_;
}

const VariableTemplateSpecializationInfo*
CollectSemanticStore::get_variable_decl_variable_template_specialization(
    const VariableDecl* decl) const {
    const auto* info =
        find_external_semantic_info(variable_decl_semantic_info_map_, decl);
    if (!info || !info->variable_template_specialization.has_value()) {
        return nullptr;
    }
    return &(*info->variable_template_specialization);
}

void CollectSemanticStore::clear_variable_decl_variable_template_specializations() {
    std::vector<const VariableDecl*> decls;
    decls.reserve(variable_decl_semantic_info_map_.size());
    for (const auto& [decl, info] : variable_decl_semantic_info_map_) {
        if (info.variable_template_specialization.has_value()) {
            decls.push_back(decl);
        }
    }
    for (const VariableDecl* decl : decls) {
        auto* info =
            find_external_semantic_info(variable_decl_semantic_info_map_, decl);
        if (info) {
            info->variable_template_specialization.reset();
        }
        erase_external_semantic_info_if_empty(
            variable_decl_semantic_info_map_,
            decl);
        erase_variable_decl_owner_if_unused(this, decl);
    }
}

void CollectSemanticStore::set_template_decl_canonical_decl(
    const TemplateDecl* decl,
    const TemplateDecl* canonical_decl) {
    if (!decl) {
        return;
    }
    tracked_template_decls_.insert(decl);
    if (canonical_decl) {
        tracked_template_decls_.insert(canonical_decl);
    }
    if (!canonical_decl) {
        decl->canonical_decl = nullptr;
        erase_template_decl_owner_if_unused(this, decl);
        return;
    }
    decl->canonical_decl = canonical_decl;
    decl->external_semantic_owner_id = registry_id_;
    canonical_decl->external_semantic_owner_id = registry_id_;
}

const TemplateDecl* CollectSemanticStore::get_template_decl_canonical_decl(
    const TemplateDecl* decl) const {
    if (!decl) {
        return nullptr;
    }
    const TemplateDecl* current = decl;
    for (size_t depth = 0; depth < 64; ++depth) {
        const TemplateDecl* next = current->canonical_decl;
        if (!next) {
            return current;
        }
        if (next == current) {
            return current;
        }
        current = next;
    }
    return current;
}

void CollectSemanticStore::set_template_decl_definition_decl(
    const TemplateDecl* decl,
    const TemplateDecl* definition_decl) {
    if (!decl) {
        return;
    }
    tracked_template_decls_.insert(decl);
    if (definition_decl) {
        tracked_template_decls_.insert(definition_decl);
    }
    if (!definition_decl) {
        decl->definition_decl = nullptr;
        erase_template_decl_owner_if_unused(this, decl);
        return;
    }
    decl->definition_decl = definition_decl;
    decl->external_semantic_owner_id = registry_id_;
    definition_decl->external_semantic_owner_id = registry_id_;
}

const TemplateDecl* CollectSemanticStore::get_template_decl_definition_decl(
    const TemplateDecl* decl) const {
    if (!decl) {
        return nullptr;
    }
    if (decl->definition_decl) {
        return decl->definition_decl;
    }
    const TemplateDecl* canonical = get_template_decl_canonical_decl(decl);
    if (canonical && canonical->definition_decl) {
        return canonical->definition_decl;
    }
    return nullptr;
}

void CollectSemanticStore::clear_template_decl_canonical_decls() {
    std::vector<const TemplateDecl*> decls(
        tracked_template_decls_.begin(),
        tracked_template_decls_.end());
    for (const TemplateDecl* decl : decls) {
        if (decl) {
            decl->canonical_decl = nullptr;
            decl->definition_decl = nullptr;
        }
    }
    for (const TemplateDecl* decl : decls) {
        erase_template_decl_owner_if_unused(this, decl);
    }
}

void CollectSemanticStore::set_template_decl_cxx_qualifier_prefix(
    const TemplateDecl* decl,
    std::optional<std::string> prefix) {
    if (!decl) {
        return;
    }
    auto& info = template_decl_semantic_info_map_[decl];
    if (!prefix.has_value() || prefix->empty()) {
        info.cxx_qualifier_prefix = nullptr;
        erase_external_semantic_info_if_empty(template_decl_semantic_info_map_, decl);
        erase_template_decl_owner_if_unused(this, decl);
        return;
    }
    auto [it, _] = external_qualifier_pool_.emplace(std::move(*prefix));
    info.cxx_qualifier_prefix = &(*it);
    decl->external_semantic_owner_id = registry_id_;
}

const std::string* CollectSemanticStore::get_template_decl_cxx_qualifier_prefix(
    const TemplateDecl* decl) const {
    const auto* info =
        find_external_semantic_info(template_decl_semantic_info_map_, decl);
    if (!info) {
        return nullptr;
    }
    return info->cxx_qualifier_prefix;
}

void CollectSemanticStore::clear_template_decl_cxx_qualifier_prefixes() {
    std::vector<const TemplateDecl*> decls;
    decls.reserve(template_decl_semantic_info_map_.size());
    for (const auto& [decl, info] : template_decl_semantic_info_map_) {
        if (info.cxx_qualifier_prefix != nullptr) {
            decls.push_back(decl);
        }
    }
    for (const TemplateDecl* decl : decls) {
        auto* info =
            find_external_semantic_info(template_decl_semantic_info_map_, decl);
        if (info) {
            info->cxx_qualifier_prefix = nullptr;
        }
        erase_external_semantic_info_if_empty(template_decl_semantic_info_map_, decl);
        erase_template_decl_owner_if_unused(this, decl);
    }
}

void CollectSemanticStore::set_template_decl_owner_record_type(
    const TemplateDecl* decl,
    QualType owner_type) {
    if (!decl) {
        return;
    }
    auto& info = template_decl_semantic_info_map_[decl];
    if (!owner_type) {
        info.owner_record_type = QualType();
        erase_external_semantic_info_if_empty(template_decl_semantic_info_map_, decl);
        erase_template_decl_owner_if_unused(this, decl);
        return;
    }
    info.owner_record_type = owner_type;
    decl->external_semantic_owner_id = registry_id_;
}

QualType CollectSemanticStore::get_template_decl_owner_record_type(
    const TemplateDecl* decl) const {
    const auto* info =
        find_external_semantic_info(template_decl_semantic_info_map_, decl);
    if (!info) {
        return QualType();
    }
    return info->owner_record_type;
}

void CollectSemanticStore::clear_template_decl_owner_record_types() {
    std::vector<const TemplateDecl*> decls;
    decls.reserve(template_decl_semantic_info_map_.size());
    for (const auto& [decl, info] : template_decl_semantic_info_map_) {
        if (info.owner_record_type) {
            decls.push_back(decl);
        }
    }
    for (const TemplateDecl* decl : decls) {
        auto* info =
            find_external_semantic_info(template_decl_semantic_info_map_, decl);
        if (info) {
            info->owner_record_type = QualType();
        }
        erase_external_semantic_info_if_empty(template_decl_semantic_info_map_, decl);
        erase_template_decl_owner_if_unused(this, decl);
    }
}

void CollectSemanticStore::set_template_parameter_default_argument(
    const TemplateParameterDecl* decl,
    std::optional<TemplateArgument> argument) {
    if (!decl) {
        return;
    }
    tracked_template_parameter_decls_.insert(decl);
    if (!argument.has_value()) {
        decl->default_argument.reset();
        erase_template_parameter_decl_owner_if_unused(this, decl);
        return;
    }
    decl->default_argument = std::move(*argument);
    decl->external_semantic_owner_id = registry_id_;
}

const TemplateArgument*
CollectSemanticStore::get_template_parameter_default_argument(
    const TemplateParameterDecl* decl) const {
    if (!decl) {
        return nullptr;
    }
    if (!decl->default_argument.has_value()) {
        return nullptr;
    }
    return &(*decl->default_argument);
}

void CollectSemanticStore::clear_template_parameter_default_arguments() {
    std::vector<const TemplateParameterDecl*> decls(
        tracked_template_parameter_decls_.begin(),
        tracked_template_parameter_decls_.end());
    for (const TemplateParameterDecl* decl : decls) {
        if (decl) {
            decl->default_argument.reset();
        }
    }
    for (const TemplateParameterDecl* decl : decls) {
        erase_template_parameter_decl_owner_if_unused(this, decl);
    }
}

bool CollectSemanticStore::merge_template_decl_default_arguments(
    const TemplateDecl* decl,
    size_t* conflict_param_index) {
    if (!decl) {
        return true;
    }

    const TemplateDecl* canonical = get_template_decl_canonical_decl(decl);
    if (!canonical) {
        canonical = decl;
    }

    tracked_template_decls_.insert(canonical);
    canonical->external_semantic_owner_id = registry_id_;
    auto& merged_defaults = canonical->merged_default_arguments;
    if (merged_defaults.size() < decl->parameters.size()) {
        merged_defaults.resize(decl->parameters.size());
    }

    for (size_t index = 0; index < decl->parameters.size(); ++index) {
        const auto* parameter = decl->parameters[index].get();
        const TemplateArgument* incoming_default =
            parameter ? get_template_parameter_default_argument(parameter) : nullptr;
        if (!incoming_default) {
            continue;
        }
        if (merged_defaults[index].has_value()) {
            if (conflict_param_index) {
                *conflict_param_index = index;
            }
            return false;
        }
        merged_defaults[index] = *incoming_default;
    }
    return true;
}

const std::vector<std::optional<TemplateArgument>>*
CollectSemanticStore::get_template_decl_default_arguments(
    const TemplateDecl* decl) const {
    if (!decl) {
        return nullptr;
    }
    const TemplateDecl* canonical = get_template_decl_canonical_decl(decl);
    const TemplateDecl* owner = canonical ? canonical : decl;
    if (!owner || owner->merged_default_arguments.empty()) {
        return nullptr;
    }
    return &owner->merged_default_arguments;
}

void CollectSemanticStore::clear_template_decl_default_arguments() {
    for (const TemplateDecl* decl : tracked_template_decls_) {
        if (decl) {
            decl->merged_default_arguments.clear();
        }
    }
    for (const TemplateDecl* decl : tracked_template_decls_) {
        erase_template_decl_owner_if_unused(this, decl);
    }
}

void CollectSemanticStore::set_param_decl_default_argument(const ParamDecl* decl,
                                                           std::unique_ptr<Expr> expr) {
    if (!decl) {
        return;
    }
    auto& info = param_decl_semantic_info_map_[decl];
    if (!expr) {
        info.default_argument.reset();
        erase_external_semantic_info_if_empty(param_decl_semantic_info_map_, decl);
        erase_param_decl_owner_if_unused(this, decl);
        return;
    }
    info.default_argument = std::move(expr);
    decl->external_semantic_owner_id = registry_id_;
}

const Expr* CollectSemanticStore::get_param_decl_default_argument(
    const ParamDecl* decl) const {
    const auto* info = find_external_semantic_info(param_decl_semantic_info_map_, decl);
    if (!info || !info->default_argument) {
        return nullptr;
    }
    return info->default_argument.get();
}

void CollectSemanticStore::clear_param_decl_default_arguments() {
    std::vector<const ParamDecl*> decls;
    decls.reserve(param_decl_semantic_info_map_.size());
    for (const auto& [decl, info] : param_decl_semantic_info_map_) {
        if (info.default_argument) {
            decls.push_back(decl);
        }
    }
    for (const ParamDecl* decl : decls) {
        auto* info = find_external_semantic_info(param_decl_semantic_info_map_, decl);
        if (info) {
            info->default_argument.reset();
        }
        erase_external_semantic_info_if_empty(param_decl_semantic_info_map_, decl);
        erase_param_decl_owner_if_unused(this, decl);
    }
}

void CollectSemanticStore::set_symbol_cxx_qualifier_prefix(
    const Symbol* sym,
    std::optional<std::string> prefix) {
    if (!sym) {
        return;
    }
    auto& info = symbol_semantic_info_map_[sym];
    if (!prefix.has_value() || prefix->empty()) {
        info.cxx_qualifier_prefix = nullptr;
        erase_external_semantic_info_if_empty(symbol_semantic_info_map_, sym);
        erase_symbol_owner_if_unused(this, sym);
        return;
    }
    auto [it, _] = external_qualifier_pool_.emplace(std::move(*prefix));
    info.cxx_qualifier_prefix = &(*it);
    sym->external_semantic_owner_id = registry_id_;
}

const std::string* CollectSemanticStore::get_symbol_cxx_qualifier_prefix(
    const Symbol* sym) const {
    const auto* info = find_external_semantic_info(symbol_semantic_info_map_, sym);
    if (!info) {
        return nullptr;
    }
    return info->cxx_qualifier_prefix;
}

void CollectSemanticStore::clear_symbol_cxx_qualifier_prefixes() {
    std::vector<const Symbol*> symbols;
    symbols.reserve(symbol_semantic_info_map_.size());
    for (const auto& [sym, info] : symbol_semantic_info_map_) {
        if (info.cxx_qualifier_prefix != nullptr) {
            symbols.push_back(sym);
        }
    }
    for (const Symbol* sym : symbols) {
        auto* info = find_external_semantic_info(symbol_semantic_info_map_, sym);
        if (info) {
            info->cxx_qualifier_prefix = nullptr;
        }
        erase_external_semantic_info_if_empty(symbol_semantic_info_map_, sym);
        erase_symbol_owner_if_unused(this, sym);
    }
}

void CollectSemanticStore::set_symbol_owner_record_type(const Symbol* sym,
                                                        QualType owner_type) {
    if (!sym) {
        return;
    }
    auto& info = symbol_semantic_info_map_[sym];
    if (!owner_type) {
        info.owner_record_type = QualType();
        erase_external_semantic_info_if_empty(symbol_semantic_info_map_, sym);
        erase_symbol_owner_if_unused(this, sym);
        return;
    }
    info.owner_record_type = owner_type;
    sym->external_semantic_owner_id = registry_id_;
}

QualType CollectSemanticStore::get_symbol_owner_record_type(
    const Symbol* sym) const {
    const auto* info = find_external_semantic_info(symbol_semantic_info_map_, sym);
    if (!info) {
        return QualType();
    }
    return info->owner_record_type;
}

void CollectSemanticStore::clear_symbol_owner_record_types() {
    std::vector<const Symbol*> symbols;
    symbols.reserve(symbol_semantic_info_map_.size());
    for (const auto& [sym, info] : symbol_semantic_info_map_) {
        if (info.owner_record_type) {
            symbols.push_back(sym);
        }
    }
    for (const Symbol* sym : symbols) {
        auto* info = find_external_semantic_info(symbol_semantic_info_map_, sym);
        if (info) {
            info->owner_record_type = QualType();
        }
        erase_external_semantic_info_if_empty(symbol_semantic_info_map_, sym);
        erase_symbol_owner_if_unused(this, sym);
    }
}

void CollectSemanticStore::set_object_decl_cxx_qualifier_prefix(
    const ObjectDecl* decl,
    std::optional<std::string> prefix) {
    if (!decl) {
        return;
    }
    auto& info = object_decl_semantic_info_map_[decl];
    if (!prefix.has_value() || prefix->empty()) {
        info.cxx_qualifier_prefix = nullptr;
        erase_external_semantic_info_if_empty(object_decl_semantic_info_map_, decl);
        erase_object_decl_owner_if_unused(this, decl);
        return;
    }
    auto [it, _] = external_qualifier_pool_.emplace(std::move(*prefix));
    info.cxx_qualifier_prefix = &(*it);
    decl->external_semantic_owner_id = registry_id_;
}

const std::string* CollectSemanticStore::get_object_decl_cxx_qualifier_prefix(
    const ObjectDecl* decl) const {
    const auto* info =
        find_external_semantic_info(object_decl_semantic_info_map_, decl);
    if (!info) {
        return nullptr;
    }
    return info->cxx_qualifier_prefix;
}

void CollectSemanticStore::clear_object_decl_cxx_qualifier_prefixes() {
    std::vector<const ObjectDecl*> decls;
    decls.reserve(object_decl_semantic_info_map_.size());
    for (const auto& [decl, info] : object_decl_semantic_info_map_) {
        if (info.cxx_qualifier_prefix != nullptr) {
            decls.push_back(decl);
        }
    }
    for (const ObjectDecl* decl : decls) {
        auto* info =
            find_external_semantic_info(object_decl_semantic_info_map_, decl);
        if (info) {
            info->cxx_qualifier_prefix = nullptr;
        }
        erase_external_semantic_info_if_empty(object_decl_semantic_info_map_, decl);
        erase_object_decl_owner_if_unused(this, decl);
    }
}

void CollectSemanticStore::set_object_decl_owner_record_type(
    const ObjectDecl* decl,
    QualType owner_type) {
    if (!decl) {
        return;
    }
    auto& info = object_decl_semantic_info_map_[decl];
    if (!owner_type) {
        info.owner_record_type = QualType();
        erase_external_semantic_info_if_empty(object_decl_semantic_info_map_, decl);
        erase_object_decl_owner_if_unused(this, decl);
        return;
    }
    info.owner_record_type = owner_type;
    decl->external_semantic_owner_id = registry_id_;
}

QualType CollectSemanticStore::get_object_decl_owner_record_type(
    const ObjectDecl* decl) const {
    const auto* info =
        find_external_semantic_info(object_decl_semantic_info_map_, decl);
    if (!info) {
        return QualType();
    }
    return info->owner_record_type;
}

void CollectSemanticStore::clear_object_decl_owner_record_types() {
    std::vector<const ObjectDecl*> decls;
    decls.reserve(object_decl_semantic_info_map_.size());
    for (const auto& [decl, info] : object_decl_semantic_info_map_) {
        if (info.owner_record_type) {
            decls.push_back(decl);
        }
    }
    for (const ObjectDecl* decl : decls) {
        auto* info =
            find_external_semantic_info(object_decl_semantic_info_map_, decl);
        if (info) {
            info->owner_record_type = QualType();
        }
        erase_external_semantic_info_if_empty(object_decl_semantic_info_map_, decl);
        erase_object_decl_owner_if_unused(this, decl);
    }
}

void CollectSemanticStore::set_symbol_function_template_specialization(
    const Symbol* sym,
    FunctionTemplateSpecializationInfo info) {
    if (!sym) {
        return;
    }
    ASTContextSideTableScope side_table_scope(owner_ast_ctx_);
    auto& sym_info = symbol_semantic_info_map_[sym];
    if (!info.primary_template) {
        sym_info.function_template_specialization.reset();
        erase_external_semantic_info_if_empty(symbol_semantic_info_map_, sym);
        erase_symbol_owner_if_unused(this, sym);
        return;
    }
    sym_info.function_template_specialization =
        canonicalize_function_template_specialization_info(std::move(info));
    sym->external_semantic_owner_id = registry_id_;
}

const FunctionTemplateSpecializationInfo*
CollectSemanticStore::get_symbol_function_template_specialization(
    const Symbol* sym) const {
    const auto* info = find_external_semantic_info(symbol_semantic_info_map_, sym);
    if (!info || !info->function_template_specialization.has_value()) {
        return nullptr;
    }
    return &(*info->function_template_specialization);
}

void CollectSemanticStore::clear_symbol_function_template_specializations() {
    std::vector<const Symbol*> symbols;
    symbols.reserve(symbol_semantic_info_map_.size());
    for (const auto& [sym, info] : symbol_semantic_info_map_) {
        if (info.function_template_specialization.has_value()) {
            symbols.push_back(sym);
        }
    }
    for (const Symbol* sym : symbols) {
        auto* info = find_external_semantic_info(symbol_semantic_info_map_, sym);
        if (info) {
            info->function_template_specialization.reset();
        }
        erase_external_semantic_info_if_empty(symbol_semantic_info_map_, sym);
        erase_symbol_owner_if_unused(this, sym);
    }
}

void CollectSemanticStore::set_symbol_variable_template_specialization(
    const Symbol* sym,
    VariableTemplateSpecializationInfo info) {
    if (!sym) {
        return;
    }
    ASTContextSideTableScope side_table_scope(owner_ast_ctx_);
    auto& symbol_info = symbol_semantic_info_map_[sym];
    if (!info.primary_template) {
        symbol_info.variable_template_specialization.reset();
        erase_external_semantic_info_if_empty(symbol_semantic_info_map_, sym);
        erase_symbol_owner_if_unused(this, sym);
        return;
    }
    symbol_info.variable_template_specialization =
        canonicalize_variable_template_specialization_info(std::move(info));
    sym->external_semantic_owner_id = registry_id_;
}

const VariableTemplateSpecializationInfo*
CollectSemanticStore::get_symbol_variable_template_specialization(
    const Symbol* sym) const {
    const auto* info = find_external_semantic_info(symbol_semantic_info_map_, sym);
    if (!info || !info->variable_template_specialization.has_value()) {
        return nullptr;
    }
    return &(*info->variable_template_specialization);
}

void CollectSemanticStore::clear_symbol_variable_template_specializations() {
    std::vector<const Symbol*> symbols;
    symbols.reserve(symbol_semantic_info_map_.size());
    for (const auto& [sym, info] : symbol_semantic_info_map_) {
        if (info.variable_template_specialization.has_value()) {
            symbols.push_back(sym);
        }
    }
    for (const Symbol* sym : symbols) {
        auto* info = find_external_semantic_info(symbol_semantic_info_map_, sym);
        if (info) {
            info->variable_template_specialization.reset();
        }
        erase_external_semantic_info_if_empty(symbol_semantic_info_map_, sym);
        erase_symbol_owner_if_unused(this, sym);
    }
}

bool CollectSemanticStore::merge_symbol_cpp_default_arguments(
    const Symbol* sym,
    const std::vector<const Expr*>& defaults,
    size_t* conflict_param_index) {
    if (!sym) {
        return true;
    }

    auto [it, inserted] = symbol_semantic_info_map_.try_emplace(sym);
    sym->external_semantic_owner_id = registry_id_;
    auto& merged_defaults = it->second.cpp_default_arguments;
    if (inserted) {
        merged_defaults.assign(defaults.begin(), defaults.end());
        return true;
    }

    if (merged_defaults.size() < defaults.size()) {
        merged_defaults.resize(defaults.size(), nullptr);
    }

    for (size_t index = 0; index < defaults.size(); ++index) {
        const Expr* incoming_default = defaults[index];
        if (!incoming_default) {
            continue;
        }
        if (merged_defaults[index]) {
            if (conflict_param_index) {
                *conflict_param_index = index;
            }
            return false;
        }
        merged_defaults[index] = incoming_default;
    }

    return true;
}

const std::vector<const Expr*>* CollectSemanticStore::get_symbol_cpp_default_arguments(
    const Symbol* sym) const {
    const auto* info = find_external_semantic_info(symbol_semantic_info_map_, sym);
    if (!info || info->cpp_default_arguments.empty()) {
        return nullptr;
    }
    return &info->cpp_default_arguments;
}

void CollectSemanticStore::clear_symbol_cpp_default_arguments() {
    std::vector<const Symbol*> symbols;
    symbols.reserve(symbol_semantic_info_map_.size());
    for (const auto& [sym, info] : symbol_semantic_info_map_) {
        if (!info.cpp_default_arguments.empty()) {
            symbols.push_back(sym);
        }
    }
    for (const Symbol* sym : symbols) {
        auto* info = find_external_semantic_info(symbol_semantic_info_map_, sym);
        if (info) {
            info->cpp_default_arguments.clear();
        }
        erase_external_semantic_info_if_empty(symbol_semantic_info_map_, sym);
        erase_symbol_owner_if_unused(this, sym);
    }
}

void CollectSemanticStore::set_template_specialization_resolved_type(
    QualType key_type,
    QualType resolved_type) {
    auto* type = key_type.as<TemplateSpecializationType>();
    if (!type) {
        return;
    }
    if (!resolved_type) {
        template_specialization_resolved_type_map_.erase(type);
        if (type->external_semantic_owner_id == registry_id_) {
            type->external_semantic_owner_id = 0;
        }
        return;
    }
    type->external_semantic_owner_id = registry_id_;
    template_specialization_resolved_type_map_[type] =
        ResolvedTypeCacheEntry{std::move(key_type), std::move(resolved_type)};
}

QualType CollectSemanticStore::get_template_specialization_resolved_type(
    const TemplateSpecializationType* type) const {
    if (!type) {
        return QualType();
    }
    if (type->external_semantic_owner_id != registry_id_) {
        return QualType();
    }
    auto it = template_specialization_resolved_type_map_.find(type);
    if (it == template_specialization_resolved_type_map_.end()) {
        return QualType();
    }
    return it->second.resolved_type;
}

void CollectSemanticStore::clear_template_specialization_resolved_types() {
    for (const auto& entry : template_specialization_resolved_type_map_) {
        if (entry.first &&
            entry.first->external_semantic_owner_id == registry_id_) {
            entry.first->external_semantic_owner_id = 0;
        }
    }
    template_specialization_resolved_type_map_.clear();
}

void CollectSemanticStore::set_dependent_name_resolved_type(
    QualType key_type,
    QualType resolved_type) {
    auto* type = key_type.as<DependentNameType>();
    if (!type) {
        return;
    }
    if (!resolved_type) {
        dependent_name_resolved_type_map_.erase(type);
        if (type->external_semantic_owner_id == registry_id_) {
            type->external_semantic_owner_id = 0;
        }
        return;
    }
    type->external_semantic_owner_id = registry_id_;
    dependent_name_resolved_type_map_[type] =
        ResolvedTypeCacheEntry{std::move(key_type), std::move(resolved_type)};
}

QualType CollectSemanticStore::get_dependent_name_resolved_type(
    const DependentNameType* type) const {
    if (!type) {
        return QualType();
    }
    if (type->external_semantic_owner_id != registry_id_) {
        return QualType();
    }
    auto it = dependent_name_resolved_type_map_.find(type);
    if (it == dependent_name_resolved_type_map_.end()) {
        return QualType();
    }
    return it->second.resolved_type;
}

void CollectSemanticStore::clear_dependent_name_resolved_types() {
    for (const auto& entry : dependent_name_resolved_type_map_) {
        if (entry.first &&
            entry.first->external_semantic_owner_id == registry_id_) {
            entry.first->external_semantic_owner_id = 0;
        }
    }
    dependent_name_resolved_type_map_.clear();
}

void CollectSemanticStore::clear_record_semantics_cache() {
    std::vector<const ObjectDecl*> decls;
    decls.reserve(record_semantics_cache_.size());
    for (const auto& [decl, state] : record_semantics_cache_) {
        (void)state;
        if (decl) {
            decls.push_back(decl);
        }
    }
    record_semantics_cache_.clear();
    ++record_semantics_cache_epoch_;
    if (record_semantics_cache_epoch_ == 0) {
        record_semantics_cache_epoch_ = 1;
    }
    for (const ObjectDecl* decl : decls) {
        if (decl->external_semantic_owner_id == registry_id_) {
            decl->external_semantic_owner_id = 0;
        }
    }
}

void CollectSemanticStore::set_record_semantics(const ObjectDecl* record_decl,
                                                RecordSemanticState state) {
    if (!record_decl) {
        return;
    }
    record_semantics_cache_[record_decl] = std::move(state);
    record_decl->external_semantic_owner_id = registry_id_;
    ++record_semantics_cache_epoch_;
    if (record_semantics_cache_epoch_ == 0) {
        record_semantics_cache_epoch_ = 1;
    }
}

void CollectSemanticStore::erase_record_semantics(const ObjectDecl* record_decl) {
    if (!record_decl) {
        return;
    }
    if (record_semantics_cache_.erase(record_decl) > 0) {
        if (record_decl->external_semantic_owner_id == registry_id_) {
            record_decl->external_semantic_owner_id = 0;
        }
        ++record_semantics_cache_epoch_;
        if (record_semantics_cache_epoch_ == 0) {
            record_semantics_cache_epoch_ = 1;
        }
    }
}

const RecordSemanticState* CollectSemanticStore::lookup_record_semantics(
    const ObjectDecl* record_decl) const {
    if (!record_decl) {
        return nullptr;
    }
    auto it = record_semantics_cache_.find(record_decl);
    if (it == record_semantics_cache_.end()) {
        return nullptr;
    }
    return &it->second;
}

void CollectSemanticStore::clear_enum_semantics_cache() {
    std::vector<const EnumDecl*> decls;
    decls.reserve(enum_semantics_cache_.size());
    for (const auto& [decl, state] : enum_semantics_cache_) {
        (void)state;
        if (decl) {
            decls.push_back(decl);
        }
    }
    enum_semantics_cache_.clear();
    for (const EnumDecl* decl : decls) {
        if (decl->external_semantic_owner_id == registry_id_) {
            decl->external_semantic_owner_id = 0;
        }
    }
}

void CollectSemanticStore::set_enum_semantics(const EnumDecl* enum_decl,
                                              EnumSemanticState state) {
    if (!enum_decl) {
        return;
    }
    auto& entry = enum_semantics_cache_[enum_decl];
    entry = std::move(state);
    enum_decl->external_semantic_owner_id = registry_id_;
}

void CollectSemanticStore::erase_enum_semantics(const EnumDecl* enum_decl) {
    if (!enum_decl) {
        return;
    }
    if (enum_semantics_cache_.erase(enum_decl) > 0 &&
        enum_decl->external_semantic_owner_id == registry_id_) {
        enum_decl->external_semantic_owner_id = 0;
    }
}

bool CollectSemanticStore::lookup_enum_semantics(
    const EnumDecl* enum_decl,
    EnumSemanticState& state_out) const {
    if (!enum_decl) {
        return false;
    }
    auto it = enum_semantics_cache_.find(enum_decl);
    if (it == enum_semantics_cache_.end()) {
        return false;
    }
    state_out = it->second;
    return true;
}

ClassTemplateSpecializationEntry*
CollectSemanticStore::lookup_class_template_specialization(
    const ClassTemplateDecl* primary_template,
    const std::vector<TemplateArgument>& arguments) {
    ASTContextSideTableScope side_table_scope(owner_ast_ctx_);
    auto key = make_template_specialization_semantic_key(primary_template, arguments);
    auto it = class_template_specialization_lookup_.find(key);
    if (it == class_template_specialization_lookup_.end()) {
        return nullptr;
    }
    if (it->second >= class_template_specializations_.size()) {
        return nullptr;
    }
    return class_template_specializations_[it->second].get();
}

const ClassTemplateSpecializationEntry*
CollectSemanticStore::lookup_class_template_specialization(
    const ClassTemplateDecl* primary_template,
    const std::vector<TemplateArgument>& arguments) const {
    ASTContextSideTableScope side_table_scope(owner_ast_ctx_);
    auto key = make_template_specialization_semantic_key(primary_template, arguments);
    auto it = class_template_specialization_lookup_.find(key);
    if (it == class_template_specialization_lookup_.end()) {
        return nullptr;
    }
    if (it->second >= class_template_specializations_.size()) {
        return nullptr;
    }
    return class_template_specializations_[it->second].get();
}

ClassTemplateSpecializationEntry&
CollectSemanticStore::get_or_create_class_template_specialization(
    const ClassTemplateDecl* primary_template,
    std::vector<TemplateArgument> arguments,
    std::shared_ptr<ObjectType> specialization_type,
    std::unique_ptr<ObjectDecl> specialization_decl) {
    ASTContextSideTableScope side_table_scope(owner_ast_ctx_);
    auto semantic_key =
        make_template_specialization_semantic_key(primary_template, arguments);
    auto existing_it = class_template_specialization_lookup_.find(semantic_key);
    if (existing_it != class_template_specialization_lookup_.end() &&
        existing_it->second < class_template_specializations_.size()) {
        return *class_template_specializations_[existing_it->second];
    }

    auto entry = std::make_unique<ClassTemplateSpecializationEntry>();
    entry->primary_template = dyn_cast<ClassTemplateDecl>(
        const_cast<TemplateDecl*>(semantic_key.primary_template));
    entry->semantic_key = std::move(semantic_key);
    entry->arguments = entry->semantic_key.arguments;
    entry->specialization_type = std::move(specialization_type);
    entry->specialization_decl = std::move(specialization_decl);

    size_t index = class_template_specializations_.size();
    class_template_specialization_lookup_.emplace(entry->semantic_key, index);
    class_template_specializations_.push_back(std::move(entry));
    return *class_template_specializations_.back();
}

FunctionTemplateSpecializationEntry*
CollectSemanticStore::lookup_function_template_specialization(
    const FunctionTemplateDecl* primary_template,
    const std::vector<TemplateArgument>& arguments) {
    ASTContextSideTableScope side_table_scope(owner_ast_ctx_);
    auto key = make_template_specialization_semantic_key(primary_template, arguments);
    auto it = function_template_specialization_lookup_.find(key);
    if (it == function_template_specialization_lookup_.end()) {
        return nullptr;
    }
    if (it->second >= function_template_specializations_.size()) {
        return nullptr;
    }
    return function_template_specializations_[it->second].get();
}

const FunctionTemplateSpecializationEntry*
CollectSemanticStore::lookup_function_template_specialization(
    const FunctionTemplateDecl* primary_template,
    const std::vector<TemplateArgument>& arguments) const {
    ASTContextSideTableScope side_table_scope(owner_ast_ctx_);
    auto key = make_template_specialization_semantic_key(primary_template, arguments);
    auto it = function_template_specialization_lookup_.find(key);
    if (it == function_template_specialization_lookup_.end()) {
        return nullptr;
    }
    if (it->second >= function_template_specializations_.size()) {
        return nullptr;
    }
    return function_template_specializations_[it->second].get();
}

FunctionTemplateSpecializationEntry&
CollectSemanticStore::get_or_create_function_template_specialization(
    const FunctionTemplateDecl* primary_template,
    std::vector<TemplateArgument> arguments,
    std::unique_ptr<FuncDecl> specialization_decl,
    std::shared_ptr<Symbol> specialization_symbol) {
    ASTContextSideTableScope side_table_scope(owner_ast_ctx_);
    auto semantic_key =
        make_template_specialization_semantic_key(primary_template, arguments);
    auto existing_it = function_template_specialization_lookup_.find(semantic_key);
    if (existing_it != function_template_specialization_lookup_.end() &&
        existing_it->second < function_template_specializations_.size()) {
        return *function_template_specializations_[existing_it->second];
    }

    auto entry = std::make_unique<FunctionTemplateSpecializationEntry>();
    entry->primary_template = dyn_cast<FunctionTemplateDecl>(
        const_cast<TemplateDecl*>(semantic_key.primary_template));
    entry->semantic_key = std::move(semantic_key);
    entry->arguments = entry->semantic_key.arguments;
    entry->specialization_decl = std::move(specialization_decl);
    entry->specialization_symbol = std::move(specialization_symbol);

    size_t index = function_template_specializations_.size();
    function_template_specialization_lookup_.emplace(entry->semantic_key, index);
    function_template_specializations_.push_back(std::move(entry));
    return *function_template_specializations_.back();
}

VariableTemplateSpecializationEntry*
CollectSemanticStore::lookup_variable_template_specialization(
    const VariableTemplateDecl* primary_template,
    const std::vector<TemplateArgument>& arguments) {
    ASTContextSideTableScope side_table_scope(owner_ast_ctx_);
    auto key = make_template_specialization_semantic_key(primary_template, arguments);
    auto it = variable_template_specialization_lookup_.find(key);
    if (it == variable_template_specialization_lookup_.end()) {
        return nullptr;
    }
    if (it->second >= variable_template_specializations_.size()) {
        return nullptr;
    }
    return variable_template_specializations_[it->second].get();
}

const VariableTemplateSpecializationEntry*
CollectSemanticStore::lookup_variable_template_specialization(
    const VariableTemplateDecl* primary_template,
    const std::vector<TemplateArgument>& arguments) const {
    ASTContextSideTableScope side_table_scope(owner_ast_ctx_);
    auto key = make_template_specialization_semantic_key(primary_template, arguments);
    auto it = variable_template_specialization_lookup_.find(key);
    if (it == variable_template_specialization_lookup_.end()) {
        return nullptr;
    }
    if (it->second >= variable_template_specializations_.size()) {
        return nullptr;
    }
    return variable_template_specializations_[it->second].get();
}

VariableTemplateSpecializationEntry&
CollectSemanticStore::get_or_create_variable_template_specialization(
    const VariableTemplateDecl* primary_template,
    std::vector<TemplateArgument> arguments,
    std::unique_ptr<VariableDecl> specialization_decl,
    std::shared_ptr<Symbol> specialization_symbol) {
    ASTContextSideTableScope side_table_scope(owner_ast_ctx_);
    auto semantic_key =
        make_template_specialization_semantic_key(primary_template, arguments);
    auto existing_it = variable_template_specialization_lookup_.find(semantic_key);
    if (existing_it != variable_template_specialization_lookup_.end() &&
        existing_it->second < variable_template_specializations_.size()) {
        return *variable_template_specializations_[existing_it->second];
    }

    auto entry = std::make_unique<VariableTemplateSpecializationEntry>();
    entry->primary_template = dyn_cast<VariableTemplateDecl>(
        const_cast<TemplateDecl*>(semantic_key.primary_template));
    entry->semantic_key = std::move(semantic_key);
    entry->arguments = entry->semantic_key.arguments;
    entry->specialization_decl = std::move(specialization_decl);
    entry->specialization_symbol = std::move(specialization_symbol);

    size_t index = variable_template_specializations_.size();
    variable_template_specialization_lookup_.emplace(entry->semantic_key, index);
    variable_template_specializations_.push_back(std::move(entry));
    return *variable_template_specializations_.back();
}

ConceptSpecializationEntry*
CollectSemanticStore::lookup_concept_specialization(
    const ConceptDecl* primary_template,
    const std::vector<TemplateArgument>& arguments) {
    ASTContextSideTableScope side_table_scope(owner_ast_ctx_);
    auto key =
        make_template_specialization_semantic_key(primary_template, arguments);
    auto it = concept_specialization_lookup_.find(key);
    if (it == concept_specialization_lookup_.end()) {
        return nullptr;
    }
    if (it->second >= concept_specializations_.size()) {
        return nullptr;
    }
    return concept_specializations_[it->second].get();
}

const ConceptSpecializationEntry*
CollectSemanticStore::lookup_concept_specialization(
    const ConceptDecl* primary_template,
    const std::vector<TemplateArgument>& arguments) const {
    ASTContextSideTableScope side_table_scope(owner_ast_ctx_);
    auto key =
        make_template_specialization_semantic_key(primary_template, arguments);
    auto it = concept_specialization_lookup_.find(key);
    if (it == concept_specialization_lookup_.end()) {
        return nullptr;
    }
    if (it->second >= concept_specializations_.size()) {
        return nullptr;
    }
    return concept_specializations_[it->second].get();
}

ConceptSpecializationEntry&
CollectSemanticStore::get_or_create_concept_specialization(
    const ConceptDecl* primary_template,
    std::vector<TemplateArgument> arguments) {
    ASTContextSideTableScope side_table_scope(owner_ast_ctx_);
    auto semantic_key =
        make_template_specialization_semantic_key(primary_template, arguments);
    auto existing_it = concept_specialization_lookup_.find(semantic_key);
    if (existing_it != concept_specialization_lookup_.end() &&
        existing_it->second < concept_specializations_.size()) {
        return *concept_specializations_[existing_it->second];
    }

    auto entry = std::make_unique<ConceptSpecializationEntry>();
    entry->primary_template = dyn_cast<ConceptDecl>(
        const_cast<TemplateDecl*>(semantic_key.primary_template));
    entry->semantic_key = std::move(semantic_key);
    entry->arguments = entry->semantic_key.arguments;

    size_t index = concept_specializations_.size();
    concept_specialization_lookup_.emplace(entry->semantic_key, index);
    concept_specializations_.push_back(std::move(entry));
    return *concept_specializations_.back();
}

bool CollectSemanticStore::push_template_instantiation_frame(size_t max_depth) {
    if (template_instantiation_depth_ >= max_depth) {
        return false;
    }
    ++template_instantiation_depth_;
    return true;
}

void CollectSemanticStore::pop_template_instantiation_frame() {
    if (template_instantiation_depth_ > 0) {
        --template_instantiation_depth_;
    }
}

void CollectSemanticStore::clear_translation_unit_semantic_state() {
    clear_func_decl_cxx_qualifier_prefixes();
    clear_func_decl_owner_record_types();
    clear_func_decl_function_template_specializations();
    clear_variable_decl_variable_template_specializations();
    clear_template_decl_canonical_decls();
    clear_template_decl_cxx_qualifier_prefixes();
    clear_template_decl_owner_record_types();
    clear_template_parameter_default_arguments();
    clear_template_decl_default_arguments();
    clear_symbol_cxx_qualifier_prefixes();
    clear_symbol_owner_record_types();
    clear_object_decl_cxx_qualifier_prefixes();
    clear_object_decl_owner_record_types();
    clear_symbol_function_template_specializations();
    clear_symbol_variable_template_specializations();
    clear_param_decl_default_arguments();
    clear_symbol_cpp_default_arguments();
    clear_template_specialization_resolved_types();
    clear_dependent_name_resolved_types();
    clear_record_semantics_cache();
    clear_enum_semantics_cache();
    external_qualifier_pool_.clear();
}

void CollectSemanticStore::clear_all_semantic_state() {
    clear_translation_unit_semantic_state();
    class_template_specialization_lookup_.clear();
    class_template_specializations_.clear();
    function_template_specialization_lookup_.clear();
    function_template_specializations_.clear();
    variable_template_specialization_lookup_.clear();
    variable_template_specializations_.clear();
    retained_external_decls_.clear();
    template_instantiation_depth_ = 0;
}

void CollectSemanticStore::retain_external_decl(std::unique_ptr<Decl> decl) {
    if (!decl) {
        return;
    }
    retained_external_decls_.push_back(std::move(decl));
}
