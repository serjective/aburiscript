#include "collect_templates_internal.h"
#include "../helpers/auto_type_utils.h"
#include "../ast/expr_clone.h"

#include <cstdint>
#include <sstream>

namespace template_sema_internal {
namespace {

std::string pointer_identity_string(const void* ptr) {
    return std::to_string(reinterpret_cast<uintptr_t>(ptr));
}

// Build a string cache key for a compile-time constant value.
// For Object values, recursively encodes each element.
// ASSUMPTION: the ConstValue graph is acyclic — self-referential constant
// aggregates are not supported and would cause infinite recursion here.
// Member pointer keys include raw pointer addresses (via pointer_identity_string),
// so cache keys are only valid within a single compilation session.
void append_const_value_cache_key(std::string& out, const ConstValue& value) {
    switch (value.kind) {
        case ConstValueKind::Invalid:
            out += "invalid";
            return;
        case ConstValueKind::Integer:
            out += value.int_value.is_unsigned ? "u:" : "s:";
            out += std::to_string(value.int_value.is_unsigned
                ? value.int_value.to_unsigned_u64()
                : static_cast<uint64_t>(value.int_value.to_signed_i64()));
            out += ":w";
            out += std::to_string(value.int_value.bit_width);
            return;
        case ConstValueKind::Boolean:
            out += value.bool_value ? "true" : "false";
            return;
        case ConstValueKind::Floating:
            out += "f:";
            out += std::to_string(static_cast<double>(value.float_value.value));
            return;
        case ConstValueKind::NullPointer:
            out += "null";
            return;
        case ConstValueKind::Address:
            out += "addr:";
            out += pointer_identity_string(value.address_value.symbol.get());
            out += ":off";
            out += std::to_string(value.address_value.byte_offset);
            return;
        case ConstValueKind::MemberPointer:
            out += value.member_pointer_value.is_function_member ? "mfn:" : "mdata:";
            out += pointer_identity_string(
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
                    append_const_value_cache_key(out, value.object_value->elements[idx]);
                }
            }
            out += value.object_value &&
                    value.object_value->kind == ConstObjectValueKind::Record
                ? "}"
                : "]";
            return;
    }
}

void append_qualified_expr_info_cache_key(
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
    append_type_cache_key(out, info->qualifier_type);
    out += ":";
    for (size_t idx = 0; idx < info->qualifiers.size(); ++idx) {
        if (idx > 0) {
            out += "::";
        }
        out += info->qualifiers[idx];
    }
}

void append_dependent_lookup_qualifier_cache_key(
    std::string& out,
    const DependentLookupQualifier& qualifier) {
    out += "DLQ:";
    out += qualifier.has_global_qualifier ? "global:" : "relative:";
    out += qualifier.is_type_qualified ? "type:" : "namespace:";
    out += qualifier.is_current_instantiation ? "current:" : "ordinary:";
    append_type_cache_key(out, qualifier.qualifier_type);
    out += ":";
    for (size_t idx = 0; idx < qualifier.qualifiers.size(); ++idx) {
        if (idx > 0) {
            out += "::";
        }
        out += qualifier.qualifiers[idx];
    }
}

void append_expr_cache_key(std::string& out, const Expr* expr) {
    expr = Collect::strip_implicit_casts(const_cast<Expr*>(expr));
    if (!expr) {
        out += "E:null";
        return;
    }
    out += "E";
    out += std::to_string(static_cast<int>(expr->get_kind()));
    out += "(";
    append_type_cache_key(
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
            out += pointer_identity_string(var_ref->symref.get());
            out += ":owner:";
            append_type_cache_key(
                out,
                get_symbol_owner_record_type(var_ref->symref.get()));
            out += ":";
            append_qualified_expr_info_cache_key(
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
            append_dependent_lookup_qualifier_cache_key(
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
                    append_template_argument_cache_key(
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
            append_expr_cache_key(out, unary->operand.get());
            return;
        }
        case StmtKind::UnaryOperation: {
            const auto* unary = static_cast<const UnaryOperation*>(expr);
            out += "u:";
            out += std::to_string(static_cast<int>(unary->uop));
            out += ":";
            append_expr_cache_key(out, unary->exp.get());
            return;
        }
        case StmtKind::ParenExpr: {
            const auto* paren = static_cast<const ParenExpr*>(expr);
            out += "p:";
            append_expr_cache_key(out, paren->subexpr.get());
            return;
        }
        case StmtKind::DependentBinaryExpr: {
            const auto* binary =
                static_cast<const DependentBinaryExpr*>(expr);
            out += "db:";
            out += std::to_string(static_cast<int>(binary->bop));
            out += ":";
            append_expr_cache_key(out, binary->left.get());
            out += ":";
            append_expr_cache_key(out, binary->right.get());
            return;
        }
        case StmtKind::BinaryOperation: {
            const auto* binary = static_cast<const BinaryOperation*>(expr);
            out += "b:";
            out += std::to_string(static_cast<int>(binary->bop));
            out += ":";
            append_expr_cache_key(out, binary->left.get());
            out += ":";
            append_expr_cache_key(out, binary->right.get());
            return;
        }
        case StmtKind::ExplicitCast: {
            const auto* cast = static_cast<const ExplicitCast*>(expr);
            out += "ecast:";
            out += std::to_string(static_cast<int>(cast->cast_kind));
            out += ":";
            append_type_cache_key(out, cast->ctype);
            out += ":";
            append_expr_cache_key(out, cast->expr.get());
            return;
        }
        case StmtKind::ImplicitCast: {
            const auto* cast = static_cast<const ImplicitCast*>(expr);
            out += "icast:";
            out += std::to_string(static_cast<int>(cast->kind));
            out += ":";
            append_type_cache_key(out, cast->ctype);
            out += ":";
            append_expr_cache_key(out, cast->expr.get());
            return;
        }
        default:
            out += "kind-only";
            return;
    }
}

const TemplateDecl* canonical_template_decl_identity(const TemplateDecl* decl) {
    return decl ? get_template_decl_canonical_decl(decl) : nullptr;
}

std::shared_ptr<FunctionType> strip_implicit_object_parameter_from_method_type(
    const std::shared_ptr<FunctionType>& fn_type) {
    if (!fn_type) {
        return nullptr;
    }
    size_t param_start = method_user_param_start(fn_type);
    if (param_start == 0) {
        return fn_type;
    }

    auto rebuilt = std::make_shared<FunctionType>();
    rebuilt->ret_type = fn_type->ret_type;
    rebuilt->parameters.reserve(fn_type->parameters.size() - param_start);
    rebuilt->parameter_pack_flags.reserve(
        fn_type->parameters.size() - param_start);
    for (size_t index = param_start; index < fn_type->parameters.size();
         ++index) {
        rebuilt->push_parameter(
            fn_type->parameters[index],
            fn_type->parameter_is_pack(index));
    }
    rebuilt->is_variadic = fn_type->is_variadic;
    rebuilt->has_prototype = fn_type->has_prototype;
    rebuilt->member_ref_qualifier = fn_type->member_ref_qualifier;
    rebuilt->has_explicit_exception_spec = fn_type->has_explicit_exception_spec;
    rebuilt->exception_spec = fn_type->exception_spec;
    rebuilt->exception_spec_expr = fn_type->exception_spec_expr;
    return rebuilt;
}

QualType canonicalize_member_pointer_actual_type(QualType type,
                                                 const TemplateArgument& argument) {
    if (!type || argument.kind != TemplateArgumentKind::Value || argument.is_dependent ||
        argument.value.kind != ConstValueKind::MemberPointer ||
        !argument.value.member_pointer_value.is_function_member) {
        return type;
    }

    auto canonical = desugar_type(type).as_shared<MemberPointerType>();
    if (!canonical) {
        return type;
    }
    auto method_type =
        desugar_type(canonical->member_type).as_shared<FunctionType>();
    if (!method_type) {
        return type;
    }

    auto surface_method_type =
        strip_implicit_object_parameter_from_method_type(method_type);
    if (!surface_method_type) {
        return type;
    }
    if (surface_method_type.get() == method_type.get()) {
        return type;
    }

    return QualType(std::make_shared<MemberPointerType>(
        canonical->class_type,
        QualType(surface_method_type)));
}

QualType materialization_type_for_template_member_pointer_argument(
    const TemplateArgument& argument) {
    if (argument.kind != TemplateArgumentKind::Value || argument.is_dependent ||
        argument.value.kind != ConstValueKind::MemberPointer ||
        !argument.value.member_pointer_value.is_function_member ||
        !argument.value.member_pointer_value.method_symbol ||
        !argument.value_type) {
        return argument.value_type;
    }

    auto semantic_member_ptr =
        desugar_type(argument.value_type).as_shared<MemberPointerType>();
    if (!semantic_member_ptr) {
        return argument.value_type;
    }

    auto lowered_method_type = argument.value.member_pointer_value.method_symbol->type;
    if (!lowered_method_type ||
        canonical_type_kind(lowered_method_type) != TypeKind::Function) {
        return argument.value_type;
    }

    return QualType(std::make_shared<MemberPointerType>(
        semantic_member_ptr->class_type,
        lowered_method_type));
}

QualType canonicalize_non_type_template_argument_actual_type(
    QualType type,
    const TemplateArgument& argument) {
    if (!type || argument.kind != TemplateArgumentKind::Value || argument.is_dependent) {
        return type;
    }
    if (argument.value.kind == ConstValueKind::MemberPointer) {
        return canonicalize_member_pointer_actual_type(type, argument);
    }

    auto canonical = desugar_type(type);
    if (!canonical || argument.value.kind != ConstValueKind::Address) {
        return type;
    }
    if (auto function = dyn_cast_shared<FunctionType>(canonical.get_shared())) {
        return QualType(std::make_shared<PointerType>(QualType(function)));
    }
    return type;
}

QualType adjust_non_type_template_argument_actual_type_for_placeholder_target(
    QualType target_type,
    QualType actual_type,
    const TemplateArgument& argument) {
    if (!target_type || !actual_type ||
        argument.kind != TemplateArgumentKind::Value ||
        argument.is_dependent) {
        return actual_type;
    }
    if (argument.value.kind != ConstValueKind::Address) {
        return actual_type;
    }

    auto target_ref = desugar_type(target_type).as_shared<ReferenceType>();
    if (!target_ref) {
        return actual_type;
    }
    if (!auto_type_utils::has_cxx_auto_type(
            target_ref->referred_type.get_shared()) &&
        !auto_type_utils::has_gnu_auto_type(
            target_ref->referred_type.get_shared())) {
        return actual_type;
    }
    if (desugar_type(actual_type).as_shared<ReferenceType>()) {
        return actual_type;
    }
    return QualType(std::make_shared<ReferenceType>(
        actual_type,
        target_ref->reference_kind));
}

bool resolve_non_type_template_argument_target_type(TemplateArgument& argument,
                                                    QualType& target_type,
                                                    std::string* error_out) {
    if (!target_type) {
        if (error_out) {
            *error_out = "template value argument has invalid target type";
        }
        return false;
    }

    if (!auto_type_utils::has_cxx_auto_type(target_type.get_shared()) &&
        !auto_type_utils::has_gnu_auto_type(target_type.get_shared())) {
        return true;
    }

    QualType actual_type =
        canonicalize_non_type_template_argument_actual_type(argument.value_type, argument);
    actual_type = adjust_non_type_template_argument_actual_type_for_placeholder_target(
        target_type,
        actual_type,
        argument);
    if (!actual_type) {
        if (error_out) {
            *error_out = "non-type template parameter with placeholder type could not be deduced";
        }
        return false;
    }

    auto deduced =
        auto_type_utils::extract_auto_placeholder_replacement(target_type, actual_type);
    if (!deduced.has_value() || !deduced->get_shared()) {
        if (error_out) {
            *error_out = "non-type template parameter with placeholder type could not be deduced";
        }
        return false;
    }
    if (auto_type_utils::auto_type_flavors_in(deduced->get_shared()) != 0) {
        if (error_out) {
            *error_out =
                "non-type template parameter placeholder deduced to another placeholder type";
        }
        return false;
    }

    target_type = QualType(
        auto_type_utils::replace_auto_placeholder(
            target_type.get_shared(),
            deduced->get_shared()),
        target_type.get_qualifiers());
    return true;
}

} // namespace

const VariableDecl* find_constant_evaluable_template_argument_variable_definition(
    const Symbol* sym) {
    if (!sym || sym->kind != SymbolKind::VARIABLE) {
        return nullptr;
    }
    if (sym->variable_definition && sym->variable_definition->init) {
        return sym->variable_definition;
    }

    if (const auto* specialization_info =
            get_symbol_variable_template_specialization(sym)) {
        ASTContext* ast_ctx = get_side_table_ast_context_for(sym);
        if (!ast_ctx) {
            ast_ctx = get_active_side_table_ast_context();
        }
        if (ast_ctx) {
            const auto* specialization_entry =
                ast_ctx->lookup_variable_template_specialization(
                    specialization_info->primary_template,
                    specialization_info->arguments);
            if (specialization_entry &&
                specialization_entry->specialization_decl &&
                specialization_entry->specialization_decl->init) {
                return specialization_entry->specialization_decl.get();
            }
        }
    }

    QualType owner_type = get_symbol_owner_record_type(sym);
    auto owner_record =
        desugar_type(owner_type).as_shared<ObjectType>();
    auto* owner_decl = owner_record
        ? dyn_cast<ObjectDecl>(owner_record->get_decl())
        : nullptr;
    if (!owner_decl) {
        return nullptr;
    }

    const RecordSemanticState* state = record_semantics_cache_lookup(owner_decl);
    if (!state) {
        return nullptr;
    }

    for (const auto& static_member : state->static_data_members) {
        if (!static_member.decl || !static_member.decl->init) {
            continue;
        }
        if ((static_member.symbol && static_member.symbol.get() == sym) ||
            (static_member.decl->sym &&
             static_member.decl->sym.get() == sym)) {
            return static_member.decl;
        }
    }

    return nullptr;
}

bool is_cpp_constant_static_data_member_for_template_argument(
    const Symbol* sym,
    const VariableDecl* definition) {
    if (!sym || !definition || definition->storage_class != StorageClass::STATIC ||
        !get_symbol_owner_record_type(sym)) {
        return false;
    }

    QualType type = definition->type ? definition->type : sym->type;
    if (!type || !type.is_const()) {
        return false;
    }

    QualType canonical = desugar_type(type);
    return canonical &&
           (canonical->isInteger() || canonical->kind == TypeKind::Enum);
}

bool is_cpp_constant_initialized_integral_or_enum_variable_for_template_argument(
    const Symbol* sym,
    const VariableDecl* definition) {
    if (!sym || !definition || !definition->init) {
        return false;
    }

    QualType type = definition->type ? definition->type : sym->type;
    if (!type || !type.is_const() || type.is_volatile()) {
        return false;
    }

    QualType canonical = desugar_type(remove_reference(type));
    if (!canonical ||
        !(canonical->isInteger() || canonical->kind == TypeKind::Enum)) {
        return false;
    }

    ConstEvalResult eval = evaluate_with_consteval_compat(
        definition->init.get(),
        ConstEvalMode::cpp_core_constant_expression());
    return eval.status == ConstEvalStatus::Constant &&
           eval.value.has_value();
}

std::shared_ptr<Expr> clone_constexpr_variable_initializer_expr(
    const Symbol* sym,
    ASTContext* ast_ctx) {
    const VariableDecl* definition =
        find_constant_evaluable_template_argument_variable_definition(sym);
    if (!definition || !definition->init) {
        return nullptr;
    }
    if (!ast_ctx) {
        ast_ctx = get_side_table_ast_context_for(sym);
    }
    // Some constexpr objects used as NTTP arguments still originate from the
    // active compilation context rather than an owned side-table entry.
    if (!ast_ctx) {
        ast_ctx = get_active_side_table_ast_context();
    }
    if (!ast_ctx) {
        return nullptr;
    }

    std::string clone_error;
    auto cloned =
        clone_expr_tree(definition->init.get(), ast_ctx, &clone_error);
    if (!cloned) {
        return nullptr;
    }
    return std::shared_ptr<Expr>(cloned.release());
}

namespace {

bool try_fold_constexpr_variable_address_to_value(TemplateArgument& argument,
                                                  QualType target_type,
                                                  std::string* error_out) {
    if (argument.kind != TemplateArgumentKind::Value || argument.is_dependent ||
        argument.value.kind != ConstValueKind::Address ||
        !argument.value.address_value.symbol || !target_type) {
        return true;
    }

    auto canonical_target = desugar_type(target_type);
    if (!canonical_target) {
        return true;
    }

    if (canonical_target->kind == TypeKind::Pointer ||
        canonical_target->kind == TypeKind::Reference ||
        canonical_target->kind == TypeKind::MemberPointer ||
        (canonical_target->kind == TypeKind::Builtin &&
         static_cast<const BuiltinType*>(canonical_target.get_shared().get())->builtin_kind ==
             BuiltinTypes::NullPtr)) {
        return true;
    }

    const Symbol* sym = argument.value.address_value.symbol.get();
    const VariableDecl* definition =
        find_constant_evaluable_template_argument_variable_definition(sym);
    bool can_fold_to_value =
        sym->is_constexpr ||
        is_cpp_constant_static_data_member_for_template_argument(
            sym,
            definition) ||
        is_cpp_constant_initialized_integral_or_enum_variable_for_template_argument(
            sym,
            definition);
    if (!can_fold_to_value || !definition || !definition->init) {
        return true;
    }

    ConstEvalResult eval = evaluate_with_consteval_compat(
        definition->init.get(),
        ConstEvalMode::cpp_core_constant_expression());
    if (eval.status != ConstEvalStatus::Constant || !eval.value.has_value()) {
        if (error_out) {
            *error_out =
                "variable initializer is not a valid non-type template argument constant expression";
        }
        return false;
    }

    argument.value = *eval.value;
    if (argument.value.kind == ConstValueKind::Object) {
        if (auto concrete_expr = clone_constexpr_variable_initializer_expr(sym, nullptr)) {
            argument.value_expr = std::move(concrete_expr);
        }
    }
    return true;
}

} // namespace

void append_template_argument_cache_key(std::string& out,
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
                out += pointer_identity_string(
                    argument.pack_expansion_parameters[idx]);
            }
        }
        out += "]";
    }
    switch (argument.kind) {
        case TemplateArgumentKind::Type:
            out += "T(";
            append_type_cache_key(out, argument.type);
            out += ")";
            return;
        case TemplateArgumentKind::Value:
            out += "V(";
            append_type_cache_key(out, argument.value_type);
            out += "):";
            if (argument.is_dependent) {
                if (argument.referenced_parameter) {
                    out += "dep:";
                    out += pointer_identity_string(argument.referenced_parameter);
                } else if (argument.value_expr) {
                    out += "expr:";
                    append_expr_cache_key(out, argument.value_expr.get());
                } else if (!argument.value_spelling.empty()) {
                    out += "sp:";
                    out += argument.value_spelling;
                } else {
                    out += "dep";
                }
                return;
            }
            append_const_value_cache_key(out, argument.value);
            return;
        case TemplateArgumentKind::Template:
            out += "TT:";
            if (argument.is_dependent) {
                if (argument.referenced_parameter) {
                    out += "dep:";
                    out += pointer_identity_string(argument.referenced_parameter);
                } else if (!argument.template_name.empty()) {
                    out += "sp:";
                    out += argument.template_name;
                } else {
                    out += "dep";
                }
                return;
            }
            if (const auto* canonical =
                    canonical_template_decl_identity(argument.template_decl)) {
                out += pointer_identity_string(canonical);
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

bool template_arguments_depend_on_template_parameters(
    const std::vector<TemplateArgument>& arguments) {
    for (const auto& argument : arguments) {
        if (template_argument_depends_on_template_parameters(argument)) {
            return true;
        }
    }
    return false;
}

std::optional<size_t> find_template_parameter_index_by_decl(
    const TemplateParameterDecl* parameter,
    const TemplateParameterList& parameters) {
    if (!parameter) {
        return std::nullopt;
    }
    for (size_t idx = 0; idx < parameters.size(); ++idx) {
        if (parameters[idx].get() == parameter) {
            return idx;
        }
    }
    return std::nullopt;
}

std::optional<size_t> find_pack_binding_size_for_sizeof_expr(
    const SizeOfPackExpr* expr,
    const TemplateParameterList& parameters,
    const TemplateArgumentBindings& bindings,
    std::string* error_out) {
    if (!expr) {
        return std::nullopt;
    }

    for (size_t idx = 0; idx < parameters.size(); ++idx) {
        const auto* parameter = parameters[idx].get();
        if (!expr->matches_parameter(parameter)) {
            continue;
        }
        if (idx >= bindings.size()) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "internal error: missing template argument binding for sizeof... pack";
            }
            return std::nullopt;
        }
        const auto& binding = bindings[idx];
        if (binding.is_pack()) {
            return binding.arguments.size();
        }
        if (binding.is_unbound()) {
            return std::nullopt;
        }
        if (error_out && error_out->empty()) {
            *error_out =
                "internal error: sizeof... operand was not bound as a template parameter pack";
        }
        return std::nullopt;
    }

    return std::nullopt;
}

const TemplateArgument* find_template_argument_for_non_type_parameter_symbol(
    const Symbol* sym,
    const TemplateParameterList& parameters,
    const TemplateArgumentBindings& bindings) {
    if (!sym) {
        return nullptr;
    }
    for (size_t idx = 0; idx < parameters.size() && idx < bindings.size(); ++idx) {
        auto* non_type_parameter =
            dyn_cast<TemplateNonTypeParmDecl>(parameters[idx].get());
        if (!non_type_parameter) {
            continue;
        }
        if (non_type_parameter->sym.get() == sym) {
            return bindings[idx].single_argument();
        }
        if (!non_type_parameter->sym || !sym->is_constexpr) {
            continue;
        }
        if (non_type_parameter->name != sym->name) {
            continue;
        }
        if (!non_type_parameter->type.equals_qualified(sym->type)) {
            continue;
        }
        return bindings[idx].single_argument();
    }
    return nullptr;
}

bool template_argument_has_known_payload(const TemplateArgument& argument) {
    switch (argument.kind) {
        case TemplateArgumentKind::Type:
            return static_cast<bool>(argument.type);
        case TemplateArgumentKind::Value:
            return argument.is_dependent || argument.value.kind != ConstValueKind::Invalid;
        case TemplateArgumentKind::Template:
            return argument.is_dependent ||
                   argument.template_decl != nullptr ||
                   !argument.template_name.empty();
    }
    return false;
}

bool normalize_concrete_template_value_argument(TemplateArgument& argument,
                                                QualType target_type,
                                                std::string* error_out) {
    if (argument.kind != TemplateArgumentKind::Value) {
        if (error_out) {
            *error_out = "template value argument expected";
        }
        return false;
    }
    if (argument.is_dependent) {
        argument.value_type = target_type;
        return true;
    }
    if (!resolve_non_type_template_argument_target_type(
            argument,
            target_type,
            error_out)) {
        return false;
    }
    if (argument.value_expr) {
        auto canonical_target = desugar_type(target_type);
        bool target_prefers_value_constant =
            canonical_target &&
            (canonical_target->kind == TypeKind::Builtin ||
             canonical_target->kind == TypeKind::Enum);
        if (target_prefers_value_constant) {
            ConstEvalResult eval = evaluate_with_consteval_compat(
                argument.value_expr.get(),
                ConstEvalMode::cpp_core_constant_expression());
            if (eval.status == ConstEvalStatus::Constant &&
                eval.value.has_value()) {
                argument.value = *eval.value;
            }
        }
    }
    if (!try_fold_constexpr_variable_address_to_value(
            argument,
            target_type,
            error_out)) {
        return false;
    }
    QualType actual_type =
        canonicalize_non_type_template_argument_actual_type(argument.value_type, argument);
    argument.value_type = target_type;
    auto canonical_target = desugar_type(target_type);
    if (!canonical_target) {
        if (error_out) {
            *error_out = "template value argument has invalid target type";
        }
        return false;
    }
    if (canonical_target->kind == TypeKind::Builtin &&
        static_cast<const BuiltinType*>(canonical_target.get())->builtin_kind ==
            BuiltinTypes::Bool) {
        bool value = false;
        switch (argument.value.kind) {
            case ConstValueKind::Boolean:
                value = argument.value.bool_value;
                break;
            case ConstValueKind::Integer:
                value = argument.value.int_value.to_unsigned_u64() != 0;
                break;
            default:
                if (error_out) {
                    *error_out =
                        "template value argument is not convertible to bool";
                }
                return false;
        }
        argument.value = ConstValue::boolean(value);
        return true;
    }
    if (canonical_target->kind == TypeKind::Pointer) {
        QualType canonical_actual = desugar_type(actual_type);
        QualType comparable_target = canonical_target.without_qualifiers();
        QualType comparable_actual =
            canonical_actual ? canonical_actual.without_qualifiers() : canonical_actual;
        if (argument.value.kind == ConstValueKind::NullPointer) {
            return true;
        }
        if (argument.value.kind != ConstValueKind::Address || !comparable_actual) {
            if (error_out) {
                *error_out =
                    "template value argument is not a supported pointer constant";
            }
            return false;
        }
        if (comparable_actual->kind == TypeKind::Pointer &&
            comparable_actual.equals_qualified(comparable_target)) {
            return true;
        }
        if (comparable_actual->kind == TypeKind::Function) {
            auto function_ptr =
                QualType(std::make_shared<PointerType>(comparable_actual));
            if (desugar_type(function_ptr).equals_qualified(comparable_target)) {
                return true;
            }
        }
        if (error_out) {
            *error_out =
                "template value argument is not convertible to the pointer parameter type";
        }
        return false;
    }
    if (canonical_target->kind == TypeKind::Reference) {
        auto target_ref = dyn_cast_shared<ReferenceType>(canonical_target.get_shared());
        QualType canonical_actual = desugar_type(actual_type);
        if (argument.value.kind != ConstValueKind::Address || !target_ref ||
            !canonical_actual) {
            if (error_out) {
                *error_out =
                    "template value argument is not a supported reference binding";
            }
            return false;
        }
        QualType comparable_actual = canonical_actual;
        if (auto actual_ref = dyn_cast_shared<ReferenceType>(
                canonical_actual.get_shared())) {
            comparable_actual = desugar_type(actual_ref->referred_type);
        }
        QualType target_referred = desugar_type(target_ref->referred_type);
        if (!comparable_actual.equals_qualified(target_referred)) {
            if (error_out) {
                *error_out =
                    "template value argument of type '" +
                    canonical_actual.to_string() +
                    "' is not convertible to the reference parameter type '" +
                    target_referred.to_string() + "'";
            }
            return false;
        }
        return true;
    }
    if (canonical_target->kind == TypeKind::MemberPointer) {
        if (argument.value.kind == ConstValueKind::NullPointer) {
            return true;
        }
        if (argument.value.kind != ConstValueKind::MemberPointer) {
            if (error_out) {
                *error_out =
                    "template value argument is not a member pointer constant";
            }
            return false;
        }
        QualType canonical_actual = desugar_type(actual_type);
        QualType comparable_target = canonical_target.without_qualifiers();
        QualType comparable_actual =
            canonical_actual ? canonical_actual.without_qualifiers() : canonical_actual;
        if (!comparable_actual ||
            !comparable_actual.equals_qualified(comparable_target)) {
            if (error_out) {
                *error_out =
                    "template value argument of type '" +
                    (canonical_actual ? canonical_actual.to_string()
                                      : std::string("<invalid>")) +
                    "' is not convertible to the member pointer parameter type '" +
                    canonical_target.to_string() + "'";
            }
            return false;
        }
        return true;
    }
    if (canonical_target->kind == TypeKind::Builtin &&
        static_cast<const BuiltinType*>(canonical_target.get_shared().get())->builtin_kind ==
            BuiltinTypes::NullPtr) {
        if (argument.value.kind == ConstValueKind::NullPointer) {
            return true;
        }
        if (error_out) {
            *error_out =
                "template value argument is not a null pointer constant";
        }
        return false;
    }
    if (canonical_target->kind == TypeKind::Object ||
        canonical_target->kind == TypeKind::Array) {
        if (!is_supported_non_type_template_parameter_type(target_type)) {
            if (error_out) {
                *error_out =
                    "class-type non-type template parameters currently require a supported structural object or array type";
            }
            return false;
        }
        if (argument.value.kind != ConstValueKind::Object) {
            if (error_out) {
                *error_out =
                    "template value argument is not a supported structural constant";
            }
            return false;
        }
        QualType canonical_actual = desugar_type(actual_type);
        QualType comparable_target = canonical_target.without_qualifiers();
        QualType comparable_actual =
            canonical_actual ? canonical_actual.without_qualifiers() : canonical_actual;
        if (!comparable_actual ||
            !comparable_actual.equals_qualified(comparable_target)) {
            if (error_out) {
                *error_out =
                    "template value argument of type '" +
                    (canonical_actual ? canonical_actual.to_string()
                                      : std::string("<invalid>")) +
                    "' is not convertible to the structural parameter type '" +
                    canonical_target.to_string() + "'";
            }
            return false;
        }
        return true;
    }
    if (!canonical_target->isInteger() && canonical_target->kind != TypeKind::Enum) {
        if (error_out) {
            *error_out =
                "non-type template parameter currently supports only integral, enum, pointer, reference, member pointer, nullptr, structural object, structural array, and placeholder forms";
        }
        return false;
    }

    ConstIntValue source;
    switch (argument.value.kind) {
        case ConstValueKind::Boolean:
            source = ConstIntValue::from_unsigned(argument.value.bool_value ? 1 : 0, 1);
            break;
        case ConstValueKind::Integer:
            source = argument.value.int_value;
            break;
        default:
            if (error_out) {
                *error_out =
                    "template value argument is not an integral constant expression";
            }
            return false;
    }

    uint16_t width = static_cast<uint16_t>(canonical_target->getWidth());
    if (width == 0) {
        width = 64;
    }
    argument.value = ConstValue::integer(
        source.cast(width, canonical_target->isUnsigned()));
    return true;
}

std::unique_ptr<Expr> make_constant_expr_for_template_argument(
    const TemplateArgument& argument,
    ASTContext* ast_ctx,
    SrcLoc loc) {
    if (argument.kind != TemplateArgumentKind::Value ||
        argument.is_dependent ||
        !argument.value_type) {
        return nullptr;
    }
    if (argument.value_expr) {
        std::string clone_error;
        if (auto cloned =
                clone_expr_tree(argument.value_expr.get(), ast_ctx, &clone_error)) {
            auto canonical_target = desugar_type(argument.value_type);
            bool needs_lvalue_materialization =
                canonical_target &&
                (canonical_target->kind == TypeKind::Object ||
                 canonical_target->kind == TypeKind::Array) &&
                !isa<CompoundLiteralExpr>(cloned.get()) &&
                !cloned->isLValue();
            if (needs_lvalue_materialization) {
                return std::make_unique<CompoundLiteralExpr>(
                    argument.value_type,
                    std::move(cloned),
                    loc);
            }
            return cloned;
        }
    }
    switch (argument.value.kind) {
        case ConstValueKind::Boolean:
            return std::make_unique<IntegerLiteral>(
                argument.value.bool_value ? "1" : "0",
                argument.value_type,
                loc);
        case ConstValueKind::Integer:
            return std::make_unique<IntegerLiteral>(
                argument.value.int_value.is_unsigned
                    ? std::to_string(argument.value.int_value.to_unsigned_u64())
                    : std::to_string(argument.value.int_value.to_signed_i64()),
                argument.value_type,
                loc);
        case ConstValueKind::NullPointer: {
            if (!ast_ctx || !ast_ctx->type_ctx) {
                return nullptr;
            }
            auto int_type = ast_ctx->type_ctx->get_builtin(BuiltinTypes::Int);
            return std::make_unique<ExplicitCast>(
                std::make_unique<IntegerLiteral>("0", QualType(int_type), loc),
                argument.value_type,
                loc);
        }
        case ConstValueKind::Address: {
            if (!argument.value.address_value.symbol) {
                return nullptr;
            }
            auto var_ref = std::make_unique<VarRef>(
                argument.value.address_value.symbol,
                loc);
            auto canonical_target = desugar_type(argument.value_type);
            if (canonical_target && canonical_target->kind == TypeKind::Reference) {
                return var_ref;
            }
            auto address_of = std::make_unique<UnaryOperation>(
                UnaryOpTypes::ADDRESS_OF,
                std::move(var_ref),
                loc);
            address_of->ctype = argument.value_type;
            return address_of;
        }
        case ConstValueKind::MemberPointer:
            return std::make_unique<MemberPointerLiteralExpr>(
                materialization_type_for_template_member_pointer_argument(argument),
                argument.value.member_pointer_value.byte_offset,
                argument.value.member_pointer_value.is_function_member,
                argument.value.member_pointer_value.method_symbol,
                argument.value.member_pointer_value.virtual_slot_index,
                argument.value.member_pointer_value.member_name,
                loc);
        case ConstValueKind::Object:
        default:
            return nullptr;
    }
}

void append_type_cache_key(std::string& out, QualType type) {
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
            auto builtin = static_cast<BuiltinType*>(raw.get());
            out += "b";
            out += std::to_string(static_cast<int>(builtin->builtin_kind));
            return;
        }
        case TypeKind::Pointer: {
            auto ptr = static_cast<PointerType*>(raw.get());
            out += "P(";
            append_type_cache_key(out, ptr->pointed_type);
            out += ")";
            return;
        }
        case TypeKind::Reference: {
            auto ref = static_cast<ReferenceType*>(raw.get());
            out += ref->isLValueReference() ? "L(" : "R(";
            append_type_cache_key(out, ref->referred_type);
            out += ")";
            return;
        }
        case TypeKind::MemberPointer: {
            auto mem_ptr = static_cast<MemberPointerType*>(raw.get());
            out += "M(";
            append_type_cache_key(out, mem_ptr->class_type);
            out += ")(";
            append_type_cache_key(out, mem_ptr->member_type);
            out += ")";
            return;
        }
        case TypeKind::BlockPointer: {
            auto blk = static_cast<BlockPointerType*>(raw.get());
            out += "B(";
            append_type_cache_key(out, blk->pointed_type);
            out += ")";
            return;
        }
        case TypeKind::Array: {
            auto arr = static_cast<ArrayType*>(raw.get());
            out += "Arr(";
            append_type_cache_key(out, arr->element_type);
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
            auto func = static_cast<FunctionType*>(raw.get());
            out += "F(";
            append_type_cache_key(out, func->ret_type);
            out += ")(";
            for (size_t idx = 0; idx < func->parameters.size(); ++idx) {
                if (idx > 0) {
                    out += ",";
                }
                append_type_cache_key(out, func->parameters[idx]);
            }
            out += ")";
            out += func->is_variadic ? "V" : "N";
            return;
        }
        case TypeKind::Object: {
            auto object = static_cast<ObjectType*>(raw.get());
            out += "O";
            const void* object_identity =
                object->get_decl()
                    ? static_cast<const void*>(object->get_decl())
                    : static_cast<const void*>(object);
            out += pointer_identity_string(object_identity);
            return;
        }
        case TypeKind::Enum: {
            auto enum_type = static_cast<EnumType*>(raw.get());
            out += "E";
            const void* enum_identity =
                enum_type->get_decl()
                    ? static_cast<const void*>(enum_type->get_decl())
                    : static_cast<const void*>(enum_type);
            out += pointer_identity_string(enum_identity);
            return;
        }
        case TypeKind::CppTypeInfo: {
            auto type_info = static_cast<CppTypeInfoType*>(raw.get());
            out += "TI";
            out += std::to_string(type_info->descriptor_width_bits);
            return;
        }
        case TypeKind::Vector: {
            auto vec = static_cast<VectorType*>(raw.get());
            out += "V(";
            append_type_cache_key(out, vec->element_type);
            out += "):";
            out += std::to_string(vec->total_bytes);
            return;
        }
        case TypeKind::Complex: {
            auto complex = static_cast<ComplexType*>(raw.get());
            out += "C";
            out += std::to_string(static_cast<int>(complex->element_type->builtin_kind));
            return;
        }
        case TypeKind::TemplateTypeParm: {
            auto parm = static_cast<TemplateTypeParmType*>(raw.get());
            out += "TP";
            out += parm->is_parameter_pack ? "P" : "S";
            if (parm->parameter_decl) {
                out += pointer_identity_string(parm->parameter_decl);
                return;
            }
            out += std::to_string(parm->depth);
            out += ":";
            out += std::to_string(parm->index);
            return;
        }
        case TypeKind::TemplateSpecialization: {
            auto specialization = static_cast<TemplateSpecializationType*>(raw.get());
            out += "TS";
            if (specialization->primary_template) {
                out += pointer_identity_string(specialization->primary_template);
            } else {
                out += specialization->template_name;
            }
            out += "<";
            for (size_t idx = 0; idx < specialization->arguments.size(); ++idx) {
                if (idx > 0) {
                    out += ",";
                }
                append_template_argument_cache_key(out, specialization->arguments[idx]);
            }
            out += ">";
            return;
        }
        case TypeKind::DependentName: {
            auto dependent_name = static_cast<DependentNameType*>(raw.get());
            out += "DN(";
            append_type_cache_key(out, dependent_name->qualifier_type);
            out += ")::";
            out += dependent_name->member_name;
            if (!dependent_name->template_arguments.empty()) {
                out += "<";
                for (size_t idx = 0; idx < dependent_name->template_arguments.size();
                     ++idx) {
                    if (idx > 0) {
                        out += ",";
                    }
                    append_template_argument_cache_key(
                        out,
                        dependent_name->template_arguments[idx]);
                }
                out += ">";
            }
            // DependentNameType flags affect semantic interpretation and must
            // be part of the cache key.  Two types with identical qualifier/name/args
            // but different flags are semantically different:
            //   #CI — current instantiation (affects member lookup scope)
            //   #TY — typename keyword required (dependent type resolution)
            //   #TM — template keyword required (dependent template resolution)
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
            auto auto_type = static_cast<AutoType*>(raw.get());
            out += "Auto";
            out += std::to_string(static_cast<int>(auto_type->flavor));
            return;
        }
        case TypeKind::TypeofExpr:
            out += "TypeofExpr";
            return;
        case TypeKind::DecltypeExpr: {
            auto decltype_type = static_cast<DecltypeExprType*>(raw.get());
            out += "DecltypeExpr";
            if (decltype_type->use_declared_type_rule) {
                out += "#decl";
            }
            return;
        }
        case TypeKind::BuiltinTypeTransform: {
            auto transform =
                static_cast<BuiltinTypeTransformType*>(raw.get());
            out += "BTT";
            out += std::to_string(static_cast<int>(transform->transform_kind));
            out += "(";
            append_type_cache_key(out, transform->operand_type);
            out += ")";
            return;
        }
        case TypeKind::BuiltinTypePackElement: {
            auto pack_element =
                static_cast<BuiltinTypePackElementType*>(raw.get());
            out += "BTPE<";
            for (size_t idx = 0; idx < pack_element->arguments.size(); ++idx) {
                if (idx > 0) {
                    out += ",";
                }
                append_template_argument_cache_key(
                    out,
                    pack_element->arguments[idx]);
            }
            out += ">";
            return;
        }
        case TypeKind::Typedef:
        case TypeKind::Other:
        case TypeKind::Placeholder:
            break;
    }

    out += "K";
    out += std::to_string(static_cast<int>(raw->kind));
}

std::string make_class_template_specialization_name(
    const ClassTemplateDecl* class_template,
    const std::vector<TemplateArgument>& arguments) {
    std::ostringstream out;
    const auto* pattern = class_template ? class_template->record_decl() : nullptr;
    out << (pattern ? pattern->name : "<class-template>") << "<";
    for (size_t idx = 0; idx < arguments.size(); ++idx) {
        if (idx > 0) {
            out << ", ";
        }
        out << arguments[idx].to_string();
    }
    out << ">";
    return out.str();
}

std::string make_function_template_specialization_name(
    const FunctionTemplateDecl* function_template,
    const std::vector<TemplateArgument>& arguments) {
    std::ostringstream out;
    const auto* pattern = function_template ? function_template->function_decl() : nullptr;
    out << (pattern ? pattern->name : "<function-template>") << "<";
    for (size_t idx = 0; idx < arguments.size(); ++idx) {
        if (idx > 0) {
            out << ", ";
        }
        out << arguments[idx].to_string();
    }
    out << ">";
    return out.str();
}

} // namespace template_sema_internal

namespace {

void set_template_default_completion_error(std::string* error_out,
                                           std::string message) {
    if (error_out) {
        *error_out = std::move(message);
    }
}

bool mark_template_value_argument_dependent(TemplateArgument& argument,
                                            QualType value_type,
                                            std::string* error_out) {
    if (argument.kind != TemplateArgumentKind::Value) {
        set_template_default_completion_error(
            error_out,
            "template value argument expected");
        return false;
    }
    argument.value_type = value_type;
    argument.is_dependent = true;
    return true;
}

} // namespace

bool Collect::template_value_argument_requires_dependent_normalization(
    const TemplateArgument& argument,
    QualType expected_type) const {
    if (argument.kind != TemplateArgumentKind::Value) {
        return false;
    }

    auto type_is_dependent = [this](QualType type) {
        if (!type) {
            return false;
        }
        auto raw = type.get_shared();
        if (auto_type_utils::has_cxx_auto_type(raw) ||
            auto_type_utils::has_gnu_auto_type(raw)) {
            return false;
        }
        return type_depends_on_template_parameters(type, ast_ctx_.get()) ||
               contains_deferred_semantic_type(raw);
    };

    return argument.is_dependent ||
           type_is_dependent(expected_type) ||
           type_is_dependent(argument.value_type) ||
           (argument.value_expr &&
            expression_depends_on_template_parameters(argument.value_expr.get()));
}

bool Collect::complete_template_argument_bindings_with_substituted_defaults(
    const TemplateDecl* template_decl,
    TemplateArgumentBindings& bindings_out,
    SrcLoc loc,
    std::string* error_out,
    bool allow_unsubstituted_default_parameters) {
    if (!template_decl) {
        set_template_default_completion_error(
            error_out,
            "internal error: null template declaration");
        return false;
    }
    if (bindings_out.size() != template_decl->parameters.size()) {
        set_template_default_completion_error(
            error_out,
            "internal error: template binding count does not match parameter count");
        return false;
    }

    // Complete unbound parameters by substituting their default arguments.
    // The loop runs LEFT-TO-RIGHT by parameter index — this order is a C++
    // semantic requirement, not an optimization: a default for parameter N
    // may reference parameters 0..N-1 (already bound), but forward
    // references to parameters N+1.. are not permitted.
    // Unbound packs receive an empty-pack binding (zero elements).
    const auto* merged_defaults = get_template_decl_default_arguments(template_decl);
    for (size_t idx = 0; idx < template_decl->parameters.size(); ++idx) {
        const auto* parameter = template_decl->parameters[idx].get();
        if (!parameter || !bindings_out[idx].is_unbound()) {
            continue;
        }
        if (parameter->is_parameter_pack) {
            bindings_out[idx] = TemplateArgumentBinding::pack({});
            continue;
        }

        const TemplateArgument* default_argument =
            (merged_defaults && idx < merged_defaults->size() &&
             (*merged_defaults)[idx].has_value())
                ? &(*merged_defaults)[idx].value()
                : nullptr;
        if (!default_argument) {
            set_template_default_completion_error(
                error_out,
                "template argument count does not satisfy parameter defaults");
            return false;
        }
        auto rewritten_defaults =
            substitute_template_arguments_with_bindings(
                {*default_argument},
                template_decl->parameters,
                bindings_out,
                loc,
                allow_unsubstituted_default_parameters);
        if (rewritten_defaults.size() != 1) {
            set_template_default_completion_error(
                error_out,
                "internal error: failed to rewrite default template argument");
            return false;
        }

        TemplateArgument rewritten_default = std::move(rewritten_defaults.front());
        switch (rewritten_default.kind) {
            case TemplateArgumentKind::Type:
                rewritten_default.type =
                    finalize_deferred_semantic_type(rewritten_default.type, loc);
                break;
            case TemplateArgumentKind::Value:
                rewritten_default.value_type =
                    finalize_deferred_semantic_type(
                        rewritten_default.value_type,
                        loc);
                if (auto* non_type_parameter = dyn_cast<TemplateNonTypeParmDecl>(
                        parameter)) {
                    QualType expected_type =
                        substitute_template_type_with_bindings(
                            non_type_parameter->type,
                            template_decl->parameters,
                            bindings_out,
                            loc);
                    expected_type =
                        finalize_deferred_semantic_type(expected_type, loc);
                    if (template_value_argument_requires_dependent_normalization(
                            rewritten_default,
                            expected_type)) {
                        if (!mark_template_value_argument_dependent(
                                rewritten_default,
                                expected_type,
                                error_out)) {
                            return false;
                        }
                    } else {
                        std::string normalize_error;
                        if (!template_sema_internal::
                                normalize_concrete_template_value_argument(
                                rewritten_default,
                                expected_type,
                                &normalize_error)) {
                            set_template_default_completion_error(
                                error_out,
                                normalize_error.empty()
                                    ? "failed to normalize default template value argument"
                                    : normalize_error);
                            return false;
                        }
                    }
                }
                break;
            case TemplateArgumentKind::Template:
                break;
        }

        bindings_out[idx] = TemplateArgumentBinding::single(
            std::move(rewritten_default));
    }

    return true;
}

bool Collect::bind_template_arguments_for_specialization(
    const TemplateDecl* template_decl,
    const std::vector<TemplateArgument>& arguments,
    TemplateArgumentBindings& bindings_out,
    SrcLoc loc,
    std::string* error_out,
    bool allow_unsubstituted_default_parameters) {
    if (!template_decl) {
        set_template_default_completion_error(
            error_out,
            "internal error: null template declaration");
        return false;
    }

    std::string exact_error;
    if (!bind_template_arguments_to_parameters(
            template_decl->parameters,
            arguments,
            bindings_out,
            &exact_error)) {
        if (!bind_explicit_template_arguments_prefix_to_parameters(
                template_decl->parameters,
                arguments,
                bindings_out,
                error_out)) {
            if (error_out && error_out->empty()) {
                *error_out = std::move(exact_error);
            }
            return false;
        }
    }

    return complete_template_argument_bindings_with_substituted_defaults(
        template_decl,
        bindings_out,
        loc,
        error_out,
        allow_unsubstituted_default_parameters);
}

bool Collect::bind_and_normalize_template_arguments_for_specialization(
    const TemplateDecl* template_decl,
    const std::vector<TemplateArgument>& arguments,
    TemplateArgumentBindings& bindings_out,
    std::vector<TemplateArgument>& normalized_arguments_out,
    SrcLoc loc,
    std::string* error_out,
    bool allow_unsubstituted_default_parameters) {
    normalized_arguments_out.clear();
    if (!bind_template_arguments_for_specialization(
            template_decl,
            arguments,
            bindings_out,
            loc,
            error_out,
            allow_unsubstituted_default_parameters)) {
        return false;
    }

    for (const auto& binding : bindings_out) {
        for (const auto& argument : binding.arguments) {
            if (!template_sema_internal::template_argument_has_known_payload(
                    argument)) {
                set_template_default_completion_error(
                    error_out,
                    "template argument has unknown payload");
                return false;
            }
        }
    }

    for (size_t idx = 0; idx < template_decl->parameters.size(); ++idx) {
        auto* non_type_parameter = dyn_cast<TemplateNonTypeParmDecl>(
            template_decl->parameters[idx].get());
        if (!non_type_parameter || idx >= bindings_out.size()) {
            continue;
        }
        if (bindings_out[idx].arguments.empty()) {
            continue;
        }

        QualType expected_type = substitute_template_type_with_bindings(
            non_type_parameter->type,
            template_decl->parameters,
            bindings_out,
            loc);
        expected_type = finalize_deferred_semantic_type(expected_type, loc);
        for (auto& bound_argument : bindings_out[idx].arguments) {
            if (template_value_argument_requires_dependent_normalization(
                    bound_argument,
                    expected_type)) {
                if (!mark_template_value_argument_dependent(
                        bound_argument,
                        expected_type,
                        error_out)) {
                    return false;
                }
                continue;
            }
            std::string normalize_error;
            if (!template_sema_internal::normalize_concrete_template_value_argument(
                    bound_argument,
                    expected_type,
                    &normalize_error)) {
                set_template_default_completion_error(
                    error_out,
                    normalize_error.empty()
                        ? "failed to normalize template value argument"
                        : normalize_error);
                return false;
            }
        }
    }

    normalized_arguments_out = flatten_template_argument_bindings(bindings_out);
    return true;
}

bool Collect::complete_partial_specialization_primary_arguments(
    const TemplateDecl* primary_template,
    const std::vector<TemplateArgument>& written_arguments,
    SrcLoc loc,
    std::vector<TemplateArgument>& completed_arguments_out,
    std::string* error_out) {
    completed_arguments_out.clear();
    if (!primary_template) {
        set_template_default_completion_error(
            error_out,
            "internal error: null primary template");
        return false;
    }

    TemplateArgumentBindings primary_bindings;
    if (!bind_explicit_template_arguments_prefix_to_parameters(
            primary_template->parameters,
            written_arguments,
            primary_bindings,
            error_out)) {
        return false;
    }

    if (!complete_template_argument_bindings_with_substituted_defaults(
            primary_template,
            primary_bindings,
            loc,
            error_out)) {
        return false;
    }

    completed_arguments_out = flatten_template_argument_bindings(primary_bindings);
    return true;
}
