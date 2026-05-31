#include "collect_templates_internal.h"

#include <algorithm>

namespace collect_template_internal {
namespace {

// Dual-lookup strategy for resolving pack parameter references:
// 1. Pointer identity (linear scan): find the parameter by exact object
//    pointer — works across instantiation levels because parameter_decl
//    objects persist.
// 2. Index-based fallback: if pointer lookup fails, try parameters[index],
//    but ONLY if depth, index, is_parameter_pack, and kind all match.
//    These guards prevent false matches when parameter indices collide
//    across different template nesting levels.
// Returns nullptr if neither lookup succeeds — this is not an error but
// signals that the parameter is external to this pack expansion context.
const TemplateParameterDecl* resolve_pack_parameter_reference(
    const TemplateParameterDecl* parameter,
    const TemplateParameterList& parameters) {
    if (!parameter) {
        return nullptr;
    }
    for (const auto& candidate : parameters) {
        if (candidate.get() == parameter) {
            return candidate.get();
        }
    }
    if (parameter->index < parameters.size()) {
        const auto* candidate = parameters[parameter->index].get();
        if (candidate && candidate->depth == parameter->depth &&
            candidate->index == parameter->index &&
            candidate->is_parameter_pack == parameter->is_parameter_pack &&
            candidate->get_kind() == parameter->get_kind()) {
            return candidate;
        }
    }
    return nullptr;
}

Expr* strip_implicit_casts_and_parens(Expr* expr) {
    auto* stripped = Collect::strip_implicit_casts(expr);
    while (auto* paren = dyn_cast<ParenExpr>(stripped)) {
        stripped = Collect::strip_implicit_casts(paren->subexpr.get());
    }
    return stripped;
}

bool is_integer_pack_template_argument(const TemplateArgument& argument) {
    if (argument.kind != TemplateArgumentKind::Value ||
        !argument.expands_parameter_pack ||
        !argument.value_expr) {
        return false;
    }
    auto* stripped = strip_implicit_casts_and_parens(argument.value_expr.get());
    if (const auto* builtin = dyn_cast<BuiltinCallExpr>(stripped)) {
        return builtin->kind == BuiltinKind::INTEGER_PACK;
    }
    if (const auto* dependent_call = dyn_cast<DependentCallExpr>(stripped)) {
        const auto* callee_ref = dyn_cast<VarRef>(
            strip_implicit_casts_and_parens(dependent_call->callee.get()));
        return callee_ref && callee_ref->get_name() == "__integer_pack";
    }
    if (const auto* call = dyn_cast<FuncCall>(stripped)) {
        const auto* callee_ref = dyn_cast<VarRef>(
            strip_implicit_casts_and_parens(call->func.get()));
        return callee_ref && callee_ref->get_name() == "__integer_pack";
    }
    return false;
}

bool add_pack_reference(const TemplateParameterDecl* parameter,
                        const TemplateParameterList& parameters,
                        TemplatePackExpansionShape& shape_out) {
    const auto* resolved = resolve_pack_parameter_reference(parameter, parameters);
    if (!resolved || !resolved->is_parameter_pack) {
        return false;
    }
    if (std::find(
            shape_out.referenced_parameters.begin(),
            shape_out.referenced_parameters.end(),
            resolved) == shape_out.referenced_parameters.end()) {
        shape_out.referenced_parameters.push_back(resolved);
    }
    return true;
}

const TemplateParameterDecl* resolve_non_type_pack_parameter_for_symbol(
    const Symbol* sym,
    const TemplateParameterList& parameters) {
    if (!sym) {
        return nullptr;
    }
    for (const auto& parameter : parameters) {
        const auto* non_type =
            dyn_cast<TemplateNonTypeParmDecl>(parameter.get());
        if (!non_type || !non_type->is_parameter_pack) {
            continue;
        }
        if (non_type->sym.get() == sym) {
            return non_type;
        }
        if (!non_type->sym || non_type->name != sym->name) {
            continue;
        }
        if (non_type->type.equals_qualified(sym->type)) {
            return non_type;
        }
    }
    return nullptr;
}

bool collect_pack_expansion_shape_in_optional_template_arguments(
    const std::optional<std::vector<TemplateArgument>>& arguments,
    const TemplateParameterList& parameters,
    TemplatePackExpansionShape& shape_out) {
    if (!arguments.has_value()) {
        return true;
    }
    return collect_pack_expansion_shape_in_template_arguments(
        *arguments,
        parameters,
        shape_out);
}

void merge_pack_expansion_shape(TemplatePackExpansionShape& destination,
                                const TemplatePackExpansionShape& source) {
    for (const auto* parameter : source.referenced_parameters) {
        if (std::find(
                destination.referenced_parameters.begin(),
                destination.referenced_parameters.end(),
                parameter) == destination.referenced_parameters.end()) {
            destination.referenced_parameters.push_back(parameter);
        }
    }
    destination.has_unsupported_dependency =
        destination.has_unsupported_dependency ||
        source.has_unsupported_dependency;
}

} // namespace

std::optional<size_t> find_template_parameter_index_by_identity(
    const TemplateTypeParmType* parm_type,
    const TemplateParameterList& parameters) {
    if (!parm_type) {
        return std::nullopt;
    }
    if (parm_type->parameter_decl) {
        for (size_t idx = 0; idx < parameters.size(); ++idx) {
            if (parameters[idx].get() == parm_type->parameter_decl) {
                return idx;
            }
        }
    }
    if (parm_type->index < parameters.size()) {
        const auto* candidate =
            dyn_cast<TemplateTypeParmDecl>(parameters[parm_type->index].get());
        if (candidate &&
            candidate->depth == parm_type->depth &&
            candidate->index == parm_type->index &&
            candidate->is_parameter_pack == parm_type->is_parameter_pack) {
            return static_cast<size_t>(parm_type->index);
        }
    }
    return std::nullopt;
}

// Recursively traverse a type to find all template parameter pack references.
// Mutually recursive with collect_pack_expansion_shape_in_expr().
// Sets out.has_unsupported_dependency when a parameter reference is found
// that cannot be resolved in the current context — this is distinct from
// an error; it means "this pack expansion depends on an outer template
// that hasn't been substituted yet."  The caller uses this flag to decide
// whether to defer expansion or report a failure.
bool collect_pack_expansion_shape_in_type(
    QualType type,
    const TemplateParameterList& parameters,
    TemplatePackExpansionShape& shape_out) {
    if (!type) {
        return true;
    }
    auto raw = type.get_shared();
    if (!raw) {
        return true;
    }

    if (auto typedef_type = dyn_cast_shared<TypedefType>(raw)) {
        return collect_pack_expansion_shape_in_type(
            typedef_type->underlying_type,
            parameters,
            shape_out);
    }
    if (auto parm = dyn_cast_shared<TemplateTypeParmType>(raw)) {
        if (!parm->is_parameter_pack) {
            return true;
        }
        if (add_pack_reference(parm->parameter_decl, parameters, shape_out)) {
            return true;
        }
        auto parameter_index =
            find_template_parameter_index_by_identity(parm.get(), parameters);
        if (!parameter_index.has_value()) {
            shape_out.has_unsupported_dependency = true;
            return false;
        }
        return add_pack_reference(
            parameters[*parameter_index].get(),
            parameters,
            shape_out);
    }
    if (auto specialization = dyn_cast_shared<TemplateSpecializationType>(raw)) {
        if (auto* template_parameter = dyn_cast<TemplateTemplateParmDecl>(
                const_cast<Decl*>(specialization->primary_template));
            template_parameter && template_parameter->is_parameter_pack) {
            if (!add_pack_reference(template_parameter, parameters, shape_out)) {
                shape_out.has_unsupported_dependency = true;
                return false;
            }
        }
        return collect_pack_expansion_shape_in_template_arguments(
            specialization->arguments,
            parameters,
            shape_out);
    }
    if (auto dependent_name = dyn_cast_shared<DependentNameType>(raw)) {
        if (!collect_pack_expansion_shape_in_type(
                dependent_name->qualifier_type,
                parameters,
                shape_out)) {
            return false;
        }
        return collect_pack_expansion_shape_in_template_arguments(
            dependent_name->template_arguments,
            parameters,
            shape_out);
    }
    if (auto ptr = dyn_cast_shared<PointerType>(raw)) {
        return collect_pack_expansion_shape_in_type(
            ptr->pointed_type, parameters, shape_out);
    }
    if (auto ref = dyn_cast_shared<ReferenceType>(raw)) {
        return collect_pack_expansion_shape_in_type(
            ref->referred_type, parameters, shape_out);
    }
    if (auto transform = dyn_cast_shared<BuiltinTypeTransformType>(raw)) {
        return collect_pack_expansion_shape_in_type(
            transform->operand_type,
            parameters,
            shape_out);
    }
    if (auto decltype_type = dyn_cast_shared<DecltypeExprType>(raw)) {
        return collect_pack_expansion_shape_in_expr(
            decltype_type->expr.get(),
            parameters,
            shape_out);
    }
    if (auto pack_element =
            dyn_cast_shared<BuiltinTypePackElementType>(raw)) {
        return collect_pack_expansion_shape_in_template_arguments(
            pack_element->arguments,
            parameters,
            shape_out);
    }
    if (auto mem_ptr = dyn_cast_shared<MemberPointerType>(raw)) {
        return collect_pack_expansion_shape_in_type(
                   mem_ptr->class_type, parameters, shape_out) &&
               collect_pack_expansion_shape_in_type(
                   mem_ptr->member_type, parameters, shape_out);
    }
    if (auto blk = dyn_cast_shared<BlockPointerType>(raw)) {
        return collect_pack_expansion_shape_in_type(
            blk->pointed_type, parameters, shape_out);
    }
    if (auto arr = dyn_cast_shared<ArrayType>(raw)) {
        return collect_pack_expansion_shape_in_type(
            arr->element_type, parameters, shape_out);
    }
    if (auto func = dyn_cast_shared<FunctionType>(raw)) {
        if (!collect_pack_expansion_shape_in_type(
                func->ret_type, parameters, shape_out)) {
            return false;
        }
        for (const auto& parameter : func->parameters) {
            if (!collect_pack_expansion_shape_in_type(
                    parameter, parameters, shape_out)) {
                return false;
            }
        }
        return true;
    }
    if (auto vec = dyn_cast_shared<VectorType>(raw)) {
        return collect_pack_expansion_shape_in_type(
            vec->element_type, parameters, shape_out);
    }
    return true;
}

bool collect_pack_expansion_shape_in_template_argument(
    const TemplateArgument& argument,
    const TemplateParameterList& parameters,
    TemplatePackExpansionShape& shape_out) {
    if (is_integer_pack_template_argument(argument)) {
        return true;
    }

    TemplatePackExpansionShape argument_shape;
    auto finish = [&]() {
        merge_pack_expansion_shape(shape_out, argument_shape);
        return !argument_shape.has_unsupported_dependency;
    };

    if (argument.expands_parameter_pack) {
        if (!argument.pack_expansion_parameters.empty()) {
            for (const auto* parameter : argument.pack_expansion_parameters) {
                if (!add_pack_reference(parameter, parameters, argument_shape)) {
                    argument_shape.has_unsupported_dependency = true;
                    return finish();
                }
            }
        } else if (argument.referenced_parameter &&
                   argument.referenced_parameter->is_parameter_pack) {
            if (!add_pack_reference(
                    argument.referenced_parameter,
                    parameters,
                    argument_shape)) {
                argument_shape.has_unsupported_dependency = true;
                return finish();
            }
        }
    }

    auto finish_dependent_value_or_template_argument = [&]() {
        if (argument.referenced_parameter &&
            argument.referenced_parameter->is_parameter_pack) {
            if (!add_pack_reference(
                    argument.referenced_parameter,
                    parameters,
                    argument_shape)) {
                argument_shape.has_unsupported_dependency = true;
                return finish();
            }
        }
        if (!argument_shape.referenced_parameters.empty()) {
            return finish();
        }
        if (template_argument_depends_on_template_parameters(argument)) {
            argument_shape.has_unsupported_dependency = true;
            return finish();
        }
        return finish();
    };

    switch (argument.kind) {
        case TemplateArgumentKind::Type:
            if (!collect_pack_expansion_shape_in_type(
                argument.type,
                parameters,
                argument_shape)) {
                return finish();
            }
            return finish();
        case TemplateArgumentKind::Value:
            if (!collect_pack_expansion_shape_in_type(
                    argument.value_type,
                    parameters,
                    argument_shape)) {
                return finish();
            }
            if (argument.value_expr &&
                !collect_pack_expansion_shape_in_expr(
                    argument.value_expr.get(),
                    parameters,
                    argument_shape)) {
                return finish();
            }
            [[fallthrough]];
        case TemplateArgumentKind::Template:
            return finish_dependent_value_or_template_argument();
    }
    return finish();
}

bool collect_pack_expansion_shape_in_expr(
    const Expr* expr,
    const TemplateParameterList& parameters,
    TemplatePackExpansionShape& shape_out) {
    if (!expr) {
        return true;
    }

    if (!collect_pack_expansion_shape_in_type(
            const_cast<Expr*>(expr)->get_type(),
            parameters,
            shape_out)) {
        return false;
    }

    switch (expr->get_kind()) {
        case StmtKind::IntegerLiteral:
        case StmtKind::FloatingLiteral:
        case StmtKind::CharacterLiteral:
        case StmtKind::StringLiteral:
        case StmtKind::PredefinedExpr:
        case StmtKind::CppThisExpr:
        case StmtKind::LabelAddressExpr:
        case StmtKind::MemberPointerLiteralExpr:
            return true;
        case StmtKind::VarRef:
        case StmtKind::QualifiedVarRef: {
            const auto* var_ref = static_cast<const VarRef*>(expr);
            if (const auto* parameter =
                    resolve_non_type_pack_parameter_for_symbol(
                        var_ref->symref.get(),
                        parameters)) {
                return add_pack_reference(parameter, parameters, shape_out);
            }
            if (const auto* qualified_info = var_ref->get_cpp_qualified_info()) {
                return collect_pack_expansion_shape_in_type(
                    qualified_info->qualifier_type,
                    parameters,
                    shape_out);
            }
            return true;
        }
        case StmtKind::UnresolvedLookupExpr: {
            const auto* lookup =
                static_cast<const UnresolvedLookupExpr*>(expr);
            return collect_pack_expansion_shape_in_type(
                       lookup->qualifier.qualifier_type,
                       parameters,
                       shape_out) &&
                   collect_pack_expansion_shape_in_optional_template_arguments(
                       lookup->explicit_template_arguments,
                       parameters,
                       shape_out);
        }
        case StmtKind::FuncCall: {
            const auto* call = static_cast<const FuncCall*>(expr);
            if (!collect_pack_expansion_shape_in_expr(
                    call->func.get(),
                    parameters,
                    shape_out)) {
                return false;
            }
            for (const auto& argument : call->args) {
                if (!collect_pack_expansion_shape_in_expr(
                        argument.get(),
                        parameters,
                        shape_out)) {
                    return false;
                }
            }
            return true;
        }
        case StmtKind::DependentCallExpr: {
            const auto* call = static_cast<const DependentCallExpr*>(expr);
            if (!collect_pack_expansion_shape_in_expr(
                    call->callee.get(),
                    parameters,
                    shape_out)) {
                return false;
            }
            for (const auto& argument : call->args) {
                if (!collect_pack_expansion_shape_in_expr(
                        argument.get(),
                        parameters,
                        shape_out)) {
                    return false;
                }
            }
            return collect_pack_expansion_shape_in_type(
                call->known_function_type,
                parameters,
                shape_out);
        }
        case StmtKind::DependentArraySubscriptExpr: {
            const auto* subscript =
                static_cast<const DependentArraySubscriptExpr*>(expr);
            return collect_pack_expansion_shape_in_expr(
                       subscript->array.get(),
                       parameters,
                       shape_out) &&
                   collect_pack_expansion_shape_in_expr(
                       subscript->index.get(),
                       parameters,
                       shape_out);
        }
        case StmtKind::DependentUnaryExpr: {
            const auto* unary =
                static_cast<const DependentUnaryExpr*>(expr);
            return collect_pack_expansion_shape_in_expr(
                unary->operand.get(),
                parameters,
                shape_out);
        }
        case StmtKind::DependentBinaryExpr: {
            const auto* binary =
                static_cast<const DependentBinaryExpr*>(expr);
            return collect_pack_expansion_shape_in_expr(
                       binary->left.get(),
                       parameters,
                       shape_out) &&
                   collect_pack_expansion_shape_in_expr(
                       binary->right.get(),
                       parameters,
                       shape_out);
        }
        case StmtKind::DependentMemberPointerAccessExpr: {
            const auto* access =
                static_cast<const DependentMemberPointerAccessExpr*>(expr);
            return collect_pack_expansion_shape_in_expr(
                       access->base.get(),
                       parameters,
                       shape_out) &&
                   collect_pack_expansion_shape_in_expr(
                       access->member_pointer.get(),
                       parameters,
                       shape_out);
        }
        case StmtKind::PackExpansionExpr: {
            const auto* pack = static_cast<const PackExpansionExpr*>(expr);
            return collect_pack_expansion_shape_in_expr(
                pack->pattern.get(),
                parameters,
                shape_out);
        }
        case StmtKind::FoldExpr: {
            const auto* fold = static_cast<const FoldExpr*>(expr);
            return collect_pack_expansion_shape_in_expr(
                       fold->pattern.get(),
                       parameters,
                       shape_out) &&
                   collect_pack_expansion_shape_in_expr(
                       fold->init.get(),
                       parameters,
                       shape_out);
        }
        case StmtKind::ConceptSpecializationExpr: {
            const auto* concept_expr =
                static_cast<const ConceptSpecializationExpr*>(expr);
            return collect_pack_expansion_shape_in_template_arguments(
                concept_expr->arguments,
                parameters,
                shape_out);
        }
        case StmtKind::RequiresExpr: {
            const auto* requires_expr = static_cast<const RequiresExpr*>(expr);
            for (const auto& parameter : requires_expr->parameters) {
                if (!parameter) {
                    continue;
                }
                if (!collect_pack_expansion_shape_in_type(
                        parameter->type,
                        parameters,
                        shape_out) ||
                    !collect_pack_expansion_shape_in_type(
                        QualType(parameter->original_type),
                        parameters,
                        shape_out)) {
                    return false;
                }
                if (const Expr* default_arg =
                        get_param_decl_default_argument(parameter.get())) {
                    if (!collect_pack_expansion_shape_in_expr(
                            default_arg,
                            parameters,
                            shape_out)) {
                        return false;
                    }
                }
            }
            for (const auto& requirement : requires_expr->requirements) {
                if (!collect_pack_expansion_shape_in_expr(
                        requirement.expr.get(),
                        parameters,
                        shape_out) ||
                    !collect_pack_expansion_shape_in_type(
                        requirement.type_requirement,
                        parameters,
                        shape_out)) {
                    return false;
                }
                if (requirement.return_type_constraint &&
                    !collect_pack_expansion_shape_in_template_arguments(
                        requirement.return_type_constraint->template_arguments,
                        parameters,
                        shape_out)) {
                    return false;
                }
            }
            return true;
        }
        case StmtKind::CppMemberCallExpr: {
            const auto* call = static_cast<const CppMemberCallExpr*>(expr);
            return collect_pack_expansion_shape_in_expr(
                call->lowered_call.get(),
                parameters,
                shape_out);
        }
        case StmtKind::CppConstructExpr: {
            const auto* construct = static_cast<const CppConstructExpr*>(expr);
            for (const auto& argument : construct->args) {
                if (!collect_pack_expansion_shape_in_expr(
                        argument.get(),
                        parameters,
                        shape_out)) {
                    return false;
                }
            }
            return true;
        }
        case StmtKind::CppValueInitExpr:
            return collect_pack_expansion_shape_in_type(
                static_cast<const CppValueInitExpr*>(expr)->ctype,
                parameters,
                shape_out);
        case StmtKind::CppFunctionStyleCastExpr: {
            const auto* cast =
                static_cast<const CppFunctionStyleCastExpr*>(expr);
            if (!collect_pack_expansion_shape_in_type(
                    cast->target_type,
                    parameters,
                    shape_out)) {
                return false;
            }
            for (const auto& argument : cast->args) {
                if (!collect_pack_expansion_shape_in_expr(
                        argument.get(),
                        parameters,
                        shape_out)) {
                    return false;
                }
            }
            return true;
        }
        case StmtKind::CppThrowExpr: {
            const auto* throw_expr = static_cast<const CppThrowExpr*>(expr);
            return collect_pack_expansion_shape_in_expr(
                throw_expr->thrown_expr.get(),
                parameters,
                shape_out);
        }
        case StmtKind::CppNewExpr: {
            const auto* new_expr = static_cast<const CppNewExpr*>(expr);
            if (!collect_pack_expansion_shape_in_type(
                    new_expr->allocated_type,
                    parameters,
                    shape_out) ||
                !collect_pack_expansion_shape_in_type(
                    new_expr->result_type,
                    parameters,
                    shape_out)) {
                return false;
            }
            for (const auto& argument : new_expr->placement_args) {
                if (!collect_pack_expansion_shape_in_expr(
                        argument.get(),
                        parameters,
                        shape_out)) {
                    return false;
                }
            }
            if (!collect_pack_expansion_shape_in_expr(
                    new_expr->initializer.get(),
                    parameters,
                    shape_out)) {
                return false;
            }
            for (const auto& argument : new_expr->constructor_args) {
                if (!collect_pack_expansion_shape_in_expr(
                        argument.get(),
                        parameters,
                        shape_out)) {
                    return false;
                }
            }
            return true;
        }
        case StmtKind::CppDeleteExpr: {
            const auto* delete_expr = static_cast<const CppDeleteExpr*>(expr);
            return collect_pack_expansion_shape_in_expr(
                       delete_expr->operand.get(),
                       parameters,
                       shape_out) &&
                   collect_pack_expansion_shape_in_type(
                       delete_expr->destroyed_type,
                       parameters,
                       shape_out);
        }
        case StmtKind::CppPseudoDestructorExpr: {
            const auto* pseudo_dtor =
                static_cast<const CppPseudoDestructorExpr*>(expr);
            return collect_pack_expansion_shape_in_expr(
                       pseudo_dtor->base.get(),
                       parameters,
                       shape_out) &&
                   collect_pack_expansion_shape_in_type(
                       pseudo_dtor->destroyed_type,
                       parameters,
                       shape_out);
        }
        case StmtKind::BlockExpr: {
            const auto* block = static_cast<const BlockExpr*>(expr);
            if (!collect_pack_expansion_shape_in_type(
                    block->block_type,
                    parameters,
                    shape_out) ||
                !collect_pack_expansion_shape_in_type(
                    block->explicit_return_type,
                    parameters,
                    shape_out)) {
                return false;
            }
            return true;
        }
        case StmtKind::CppLambdaExpr: {
            const auto* lambda = static_cast<const CppLambdaExpr*>(expr);
            if (!collect_pack_expansion_shape_in_type(
                    lambda->written_call_operator_type,
                    parameters,
                    shape_out) ||
                !collect_pack_expansion_shape_in_type(
                    lambda->explicit_return_type,
                    parameters,
                    shape_out)) {
                return false;
            }
            if (!collect_pack_expansion_shape_in_expr(
                    lambda->template_requires_clause.get(),
                    parameters,
                    shape_out) ||
                !collect_pack_expansion_shape_in_expr(
                    lambda->trailing_requires_clause.get(),
                    parameters,
                    shape_out)) {
                return false;
            }
            for (const auto& capture : lambda->closure_info.captures) {
                if (!collect_pack_expansion_shape_in_expr(
                        capture.initializer.get(),
                        parameters,
                        shape_out)) {
                    return false;
                }
            }
            return true;
        }
        case StmtKind::CppTypeIdExpr: {
            const auto* typeid_expr = static_cast<const CppTypeIdExpr*>(expr);
            if (typeid_expr->is_type_operand) {
                return collect_pack_expansion_shape_in_type(
                    typeid_expr->type_operand,
                    parameters,
                    shape_out);
            }
            return collect_pack_expansion_shape_in_expr(
                typeid_expr->expr_operand.get(),
                parameters,
                shape_out);
        }
        case StmtKind::CppDynamicCastExpr: {
            const auto* cast_expr =
                static_cast<const CppDynamicCastExpr*>(expr);
            return collect_pack_expansion_shape_in_expr(
                       cast_expr->expr.get(),
                       parameters,
                       shape_out) &&
                   collect_pack_expansion_shape_in_type(
                       cast_expr->target_type,
                       parameters,
                       shape_out);
        }
        case StmtKind::CondExpr: {
            const auto* cond = static_cast<const CondExpr*>(expr);
            return collect_pack_expansion_shape_in_expr(
                       cond->condition.get(),
                       parameters,
                       shape_out) &&
                   collect_pack_expansion_shape_in_expr(
                       cond->true_expr.get(),
                       parameters,
                       shape_out) &&
                   collect_pack_expansion_shape_in_expr(
                       cond->false_expr.get(),
                       parameters,
                       shape_out) &&
                   collect_pack_expansion_shape_in_type(
                       cond->type,
                       parameters,
                       shape_out);
        }
        case StmtKind::ParenExpr: {
            const auto* paren = static_cast<const ParenExpr*>(expr);
            return collect_pack_expansion_shape_in_expr(
                paren->subexpr.get(),
                parameters,
                shape_out);
        }
        case StmtKind::UnaryOperation: {
            const auto* unary = static_cast<const UnaryOperation*>(expr);
            return collect_pack_expansion_shape_in_expr(
                unary->exp.get(),
                parameters,
                shape_out);
        }
        case StmtKind::BinaryOperation: {
            const auto* binary = static_cast<const BinaryOperation*>(expr);
            return collect_pack_expansion_shape_in_expr(
                       binary->left.get(),
                       parameters,
                       shape_out) &&
                   collect_pack_expansion_shape_in_expr(
                       binary->right.get(),
                       parameters,
                       shape_out);
        }
        case StmtKind::CppBuiltinThreeWayCompareExpr: {
            const auto* compare =
                static_cast<const CppBuiltinThreeWayCompareExpr*>(expr);
            return collect_pack_expansion_shape_in_expr(
                       compare->left.get(),
                       parameters,
                       shape_out) &&
                   collect_pack_expansion_shape_in_expr(
                       compare->right.get(),
                       parameters,
                       shape_out);
        }
        case StmtKind::CompoundAssignOperation: {
            const auto* compound =
                static_cast<const CompoundAssignOperation*>(expr);
            return collect_pack_expansion_shape_in_expr(
                       compound->left.get(),
                       parameters,
                       shape_out) &&
                   collect_pack_expansion_shape_in_expr(
                       compound->right.get(),
                       parameters,
                       shape_out);
        }
        case StmtKind::ImplicitCast: {
            const auto* cast = static_cast<const ImplicitCast*>(expr);
            return collect_pack_expansion_shape_in_expr(
                cast->expr.get(),
                parameters,
                shape_out);
        }
        case StmtKind::ExplicitCast: {
            const auto* cast = static_cast<const ExplicitCast*>(expr);
            return collect_pack_expansion_shape_in_expr(
                cast->expr.get(),
                parameters,
                shape_out);
        }
        case StmtKind::ArraySubscriptExpr: {
            const auto* subscript = static_cast<const ArraySubscriptExpr*>(expr);
            return collect_pack_expansion_shape_in_expr(
                       subscript->array.get(),
                       parameters,
                       shape_out) &&
                   collect_pack_expansion_shape_in_expr(
                       subscript->index.get(),
                       parameters,
                       shape_out);
        }
        case StmtKind::MemberExpr: {
            const auto* member = static_cast<const MemberExpr*>(expr);
            return collect_pack_expansion_shape_in_expr(
                       member->base.get(),
                       parameters,
                       shape_out) &&
                   collect_pack_expansion_shape_in_type(
                       member->member_type,
                       parameters,
                       shape_out);
        }
        case StmtKind::UnresolvedMemberExpr: {
            const auto* member = static_cast<const UnresolvedMemberExpr*>(expr);
            return collect_pack_expansion_shape_in_expr(
                       member->base.get(),
                       parameters,
                       shape_out) &&
                   collect_pack_expansion_shape_in_type(
                       member->member_type,
                       parameters,
                       shape_out) &&
                   collect_pack_expansion_shape_in_optional_template_arguments(
                       member->explicit_template_arguments,
                       parameters,
                       shape_out);
        }
        case StmtKind::MemberPointerAccessExpr: {
            const auto* access =
                static_cast<const MemberPointerAccessExpr*>(expr);
            return collect_pack_expansion_shape_in_expr(
                       access->base.get(),
                       parameters,
                       shape_out) &&
                   collect_pack_expansion_shape_in_expr(
                       access->member_pointer.get(),
                       parameters,
                       shape_out) &&
                   collect_pack_expansion_shape_in_type(
                       access->result_type,
                       parameters,
                       shape_out);
        }
        case StmtKind::InitListExpr: {
            const auto* init_list = static_cast<const InitListExpr*>(expr);
            if (!collect_pack_expansion_shape_in_type(
                    init_list->type,
                    parameters,
                    shape_out)) {
                return false;
            }
            for (const auto& element : init_list->elements) {
                for (const auto& designator : element.designators) {
                    if (!collect_pack_expansion_shape_in_expr(
                            designator.index.get(),
                            parameters,
                            shape_out) ||
                        !collect_pack_expansion_shape_in_expr(
                            designator.range_end.get(),
                            parameters,
                            shape_out)) {
                        return false;
                    }
                }
                if (!collect_pack_expansion_shape_in_expr(
                        element.value.get(),
                        parameters,
                        shape_out)) {
                    return false;
                }
            }
            for (const auto& action : init_list->actions) {
                if (!collect_pack_expansion_shape_in_expr(
                        action.value.get(),
                        parameters,
                        shape_out)) {
                    return false;
                }
            }
            for (const auto& [_, mapped_expr] : init_list->mappings) {
                if (!collect_pack_expansion_shape_in_expr(
                        mapped_expr.get(),
                        parameters,
                        shape_out)) {
                    return false;
                }
            }
            return true;
        }
        case StmtKind::CompoundLiteralExpr: {
            const auto* literal =
                static_cast<const CompoundLiteralExpr*>(expr);
            return collect_pack_expansion_shape_in_expr(
                       literal->init.get(),
                       parameters,
                       shape_out) &&
                   collect_pack_expansion_shape_in_type(
                       literal->type,
                       parameters,
                       shape_out);
        }
        case StmtKind::SizeOfExpr: {
            const auto* sizeof_expr = static_cast<const SizeOfExpr*>(expr);
            return collect_pack_expansion_shape_in_expr(
                       sizeof_expr->expr_operand.get(),
                       parameters,
                       shape_out) &&
                   collect_pack_expansion_shape_in_type(
                       sizeof_expr->type_operand,
                       parameters,
                       shape_out) &&
                   collect_pack_expansion_shape_in_type(
                       sizeof_expr->result_type,
                       parameters,
                       shape_out);
        }
        case StmtKind::SizeOfPackExpr: {
            const auto* sizeof_pack = static_cast<const SizeOfPackExpr*>(expr);
            if (!collect_pack_expansion_shape_in_type(
                    sizeof_pack->result_type,
                    parameters,
                    shape_out)) {
                return false;
            }
            if (sizeof_pack->parameter_decl &&
                sizeof_pack->parameter_decl->is_parameter_pack) {
                return add_pack_reference(
                    sizeof_pack->parameter_decl,
                    parameters,
                    shape_out);
            }
            for (const auto& parameter : parameters) {
                if (sizeof_pack->matches_parameter(parameter.get())) {
                    return add_pack_reference(
                        parameter.get(),
                        parameters,
                        shape_out);
                }
            }
            return true;
        }
        case StmtKind::CppNoexceptExpr: {
            const auto* noexcept_expr =
                static_cast<const CppNoexceptExpr*>(expr);
            return collect_pack_expansion_shape_in_expr(
                noexcept_expr->operand.get(),
                parameters,
                shape_out);
        }
        case StmtKind::StmtExpr: {
            const auto* stmt_expr = static_cast<const StmtExpr*>(expr);
            (void)stmt_expr;
            return true;
        }
        default:
            return true;
    }
}

bool collect_pack_expansion_shape_in_template_arguments(
    const std::vector<TemplateArgument>& arguments,
    const TemplateParameterList& parameters,
    TemplatePackExpansionShape& shape_out) {
    TemplatePackExpansionShape accumulated_shape;
    bool has_dependent_non_shape_argument = false;

    // A pack expansion pattern may contain dependent arguments that do not
    // determine arity themselves, such as default template arguments depending
    // on earlier arguments. Defer those until we know whether the surrounding
    // argument list supplied an actual pack reference.
    for (const auto& argument : arguments) {
        TemplatePackExpansionShape argument_shape;
        if (!collect_pack_expansion_shape_in_template_argument(
                argument,
                parameters,
                argument_shape)) {
            if (argument_shape.has_unsupported_dependency &&
                argument_shape.referenced_parameters.empty() &&
                template_argument_depends_on_template_parameters(argument)) {
                has_dependent_non_shape_argument = true;
                continue;
            }
            merge_pack_expansion_shape(accumulated_shape, argument_shape);
            merge_pack_expansion_shape(shape_out, accumulated_shape);
            return false;
        }
        merge_pack_expansion_shape(accumulated_shape, argument_shape);
    }

    if (has_dependent_non_shape_argument &&
        accumulated_shape.referenced_parameters.empty() &&
        shape_out.referenced_parameters.empty()) {
        accumulated_shape.has_unsupported_dependency = true;
        merge_pack_expansion_shape(shape_out, accumulated_shape);
        return false;
    }

    merge_pack_expansion_shape(shape_out, accumulated_shape);
    return true;
}

bool find_unique_parameter_pack_index_in_type(
    QualType type,
    const TemplateParameterList& parameters,
    std::optional<size_t>& found_index) {
    TemplatePackExpansionShape shape;
    if (!collect_pack_expansion_shape_in_type(type, parameters, shape) ||
        shape.has_unsupported_dependency ||
        shape.has_multiple_referenced_packs()) {
        return false;
    }
    auto unique = shape.unique_referenced_parameter();
    if (!unique.has_value()) {
        return true;
    }
    found_index = find_template_parameter_index_by_decl(*unique, parameters);
    return found_index.has_value();
}

TemplatePackReferenceResolution classify_parameter_pack_reference_in_type(
    QualType type,
    const TemplateParameterList& parameters,
    bool allow_unsubstituted_parameters) {
    TemplatePackExpansionShape shape;
    if (!collect_pack_expansion_shape_in_type(type, parameters, shape) ||
        shape.has_unsupported_dependency) {
        if (allow_unsubstituted_parameters &&
            shape.has_unsupported_dependency &&
            shape.referenced_parameters.empty()) {
            return {
                TemplatePackReferenceResolutionKind::PreserveUnsubstituted,
                std::nullopt};
        }
        return {
            TemplatePackReferenceResolutionKind::Unsupported,
            std::nullopt};
    }
    if (shape.has_multiple_referenced_packs()) {
        return {
            TemplatePackReferenceResolutionKind::Unsupported,
            std::nullopt};
    }
    auto unique = shape.unique_referenced_parameter();
    if (!unique.has_value()) {
        return {TemplatePackReferenceResolutionKind::None, std::nullopt};
    }
    auto parameter_index =
        find_template_parameter_index_by_decl(*unique, parameters);
    if (!parameter_index.has_value()) {
        return {
            TemplatePackReferenceResolutionKind::Unsupported,
            std::nullopt};
    }
    return {
        TemplatePackReferenceResolutionKind::ActivePack,
        parameter_index};
}

std::optional<size_t> find_pack_expansion_arity_for_bindings(
    const TemplatePackExpansionShape& shape,
    const TemplateParameterList& parameters,
    const TemplateArgumentBindings& bindings,
    std::string* error_out) {
    if (shape.referenced_parameters.empty()) {
        if (error_out && error_out->empty()) {
            *error_out =
                "pack expansion shape does not reference a template parameter pack";
        }
        return std::nullopt;
    }

    std::optional<size_t> expected_size;
    const TemplateParameterDecl* expected_parameter = nullptr;
    for (const auto* parameter : shape.referenced_parameters) {
        auto parameter_index =
            find_template_parameter_index_by_decl(parameter, parameters);
        if (!parameter_index || *parameter_index >= bindings.size()) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "internal error: missing template argument binding for pack expansion parameter";
            }
            return std::nullopt;
        }
        const auto& binding = bindings[*parameter_index];
        if (binding.is_unbound()) {
            return std::nullopt;
        }
        if (!binding.is_pack()) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "internal error: pack expansion parameter was not bound as a pack";
            }
            return std::nullopt;
        }
        if (!expected_size.has_value()) {
            expected_size = binding.arguments.size();
            expected_parameter = parameter;
            continue;
        }
        if (*expected_size != binding.arguments.size()) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "pack expansion parameters have different arities";
                if (expected_parameter && !expected_parameter->get_name().empty() &&
                    !parameter->get_name().empty()) {
                    *error_out += ": '" + expected_parameter->get_name() + "' has " +
                        std::to_string(*expected_size) + " element(s) but '" +
                        parameter->get_name() + "' has " +
                        std::to_string(binding.arguments.size()) +
                        " element(s)";
                }
            }
            return std::nullopt;
        }
    }
    return expected_size;
}

bool build_pack_element_argument_bindings(
    const TemplateParameterList& parameters,
    const TemplateArgumentBindings& bindings,
    size_t element_index,
    TemplateArgumentBindings& element_bindings,
    std::string* error_out) {
    element_bindings = bindings;
    for (size_t idx = 0; idx < parameters.size(); ++idx) {
        const auto* parameter = parameters[idx].get();
        if (!parameter || !parameter->is_parameter_pack) {
            continue;
        }
        if (idx >= bindings.size()) {
            if (error_out) {
                *error_out =
                    "internal error: missing template argument binding for pack parameter";
            }
            return false;
        }
        const auto& binding = bindings[idx];
        if (!binding.is_pack()) {
            if (error_out) {
                *error_out =
                    "internal error: template parameter pack was not bound as a pack";
            }
            return false;
        }
        if (element_index >= binding.arguments.size()) {
            if (error_out) {
                *error_out =
                    "internal error: template pack expansion index is out of range";
            }
            return false;
        }
        element_bindings[idx] =
            TemplateArgumentBinding::single(binding.arguments[element_index]);
    }
    return true;
}

bool build_pack_element_argument_bindings_for_shape(
    const TemplateParameterList& parameters,
    const TemplateArgumentBindings& bindings,
    const TemplatePackExpansionShape& shape,
    size_t element_index,
    TemplateArgumentBindings& element_bindings,
    std::string* error_out) {
    element_bindings = bindings;
    for (const auto* parameter : shape.referenced_parameters) {
        auto parameter_index =
            find_template_parameter_index_by_decl(parameter, parameters);
        if (!parameter_index || *parameter_index >= bindings.size()) {
            if (error_out) {
                *error_out =
                    "internal error: missing template argument binding for pack expansion parameter";
            }
            return false;
        }
        const auto& binding = bindings[*parameter_index];
        if (!binding.is_pack()) {
            if (error_out) {
                *error_out =
                    "internal error: template parameter pack was not bound as a pack";
            }
            return false;
        }
        if (element_index >= binding.arguments.size()) {
            if (error_out) {
                *error_out =
                    "internal error: template pack expansion index is out of range";
            }
            return false;
        }
        element_bindings[*parameter_index] =
            TemplateArgumentBinding::single(binding.arguments[element_index]);
    }
    return true;
}

std::string make_parameter_pack_element_name(const std::string& base_name,
                                             size_t element_index) {
    if (base_name.empty()) {
        return base_name;
    }
    return base_name + "$" + std::to_string(element_index);
}

} // namespace collect_template_internal
