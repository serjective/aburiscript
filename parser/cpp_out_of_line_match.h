#ifndef ABURI_PARSER_CPP_OUT_OF_LINE_MATCH_H
#define ABURI_PARSER_CPP_OUT_OF_LINE_MATCH_H

#include "../ast/ast.h"

inline const Expr* cpp_out_of_line_strip_implicit_casts(const Expr* expr) {
    auto* current = const_cast<Expr*>(expr);
    while (auto* cast = dyn_cast<ImplicitCast>(current)) {
        if (!cast->expr) {
            break;
        }
        current = cast->expr.get();
    }
    return current;
}

inline bool cpp_out_of_line_template_parameter_matches(
    const TemplateParameterDecl* lhs,
    const TemplateParameterDecl* rhs) {
    if (!lhs || !rhs) {
        return lhs == rhs;
    }
    return lhs->get_kind() == rhs->get_kind() &&
           lhs->depth == rhs->depth &&
           lhs->index == rhs->index &&
           lhs->is_parameter_pack == rhs->is_parameter_pack;
}

inline bool cpp_out_of_line_type_matches(QualType lhs,
                                         QualType rhs,
                                         bool ignore_top_level_qualifiers);

inline bool cpp_out_of_line_template_argument_matches(
    const TemplateArgument& lhs,
    const TemplateArgument& rhs);

inline bool cpp_out_of_line_expr_matches(const Expr* lhs,
                                         const Expr* rhs);

inline bool cpp_out_of_line_template_argument_pack_parameters_match(
    const TemplateArgument& lhs,
    const TemplateArgument& rhs) {
    if (lhs.expands_parameter_pack != rhs.expands_parameter_pack ||
        lhs.pack_expansion_parameters.size() != rhs.pack_expansion_parameters.size()) {
        return false;
    }
    for (size_t idx = 0; idx < lhs.pack_expansion_parameters.size(); ++idx) {
        if (!cpp_out_of_line_template_parameter_matches(
                lhs.pack_expansion_parameters[idx],
                rhs.pack_expansion_parameters[idx])) {
            return false;
        }
    }
    return true;
}

inline bool cpp_out_of_line_template_argument_matches(
    const TemplateArgument& lhs,
    const TemplateArgument& rhs) {
    if (lhs.kind != rhs.kind ||
        !cpp_out_of_line_template_argument_pack_parameters_match(lhs, rhs)) {
        return false;
    }

    switch (lhs.kind) {
        case TemplateArgumentKind::Type:
            return cpp_out_of_line_type_matches(lhs.type, rhs.type, false);
        case TemplateArgumentKind::Value:
            if (!cpp_out_of_line_type_matches(
                    lhs.value_type,
                    rhs.value_type,
                    false) ||
                lhs.is_dependent != rhs.is_dependent) {
                return false;
            }
            if (lhs.is_dependent) {
                if (lhs.referenced_parameter || rhs.referenced_parameter) {
                    return cpp_out_of_line_template_parameter_matches(
                        lhs.referenced_parameter,
                        rhs.referenced_parameter);
                }
                if (lhs.value_expr && rhs.value_expr) {
                    return cpp_out_of_line_expr_matches(
                        lhs.value_expr.get(),
                        rhs.value_expr.get());
                }
                return lhs.value_spelling == rhs.value_spelling;
            }
            return lhs.equals(rhs);
        case TemplateArgumentKind::Template:
            if (lhs.is_dependent != rhs.is_dependent) {
                return false;
            }
            if (lhs.is_dependent) {
                if (lhs.referenced_parameter || rhs.referenced_parameter) {
                    return cpp_out_of_line_template_parameter_matches(
                        lhs.referenced_parameter,
                        rhs.referenced_parameter);
                }
                return lhs.template_name == rhs.template_name;
            }
            return lhs.equals(rhs);
    }
    return false;
}

inline bool cpp_out_of_line_template_argument_list_matches(
    const std::optional<std::vector<TemplateArgument>>& lhs,
    const std::optional<std::vector<TemplateArgument>>& rhs) {
    if (lhs.has_value() != rhs.has_value()) {
        return false;
    }
    if (!lhs.has_value()) {
        return true;
    }
    if (lhs->size() != rhs->size()) {
        return false;
    }
    for (size_t idx = 0; idx < lhs->size(); ++idx) {
        if (!cpp_out_of_line_template_argument_matches(
                (*lhs)[idx],
                (*rhs)[idx])) {
            return false;
        }
    }
    return true;
}

inline bool cpp_out_of_line_dependent_lookup_qualifier_matches(
    const DependentLookupQualifier& lhs,
    const DependentLookupQualifier& rhs) {
    return lhs.has_global_qualifier == rhs.has_global_qualifier &&
           lhs.is_type_qualified == rhs.is_type_qualified &&
           lhs.is_current_instantiation == rhs.is_current_instantiation &&
           lhs.names_dependent_base == rhs.names_dependent_base &&
           lhs.qualifiers == rhs.qualifiers &&
           cpp_out_of_line_type_matches(
               lhs.qualifier_type,
               rhs.qualifier_type,
               false);
}

inline bool cpp_out_of_line_expr_vector_matches(
    const std::vector<std::unique_ptr<Expr>>& lhs,
    const std::vector<std::unique_ptr<Expr>>& rhs) {
    if (lhs.size() != rhs.size()) {
        return false;
    }
    for (size_t idx = 0; idx < lhs.size(); ++idx) {
        if (!cpp_out_of_line_expr_matches(lhs[idx].get(), rhs[idx].get())) {
            return false;
        }
    }
    return true;
}

inline bool cpp_out_of_line_expr_matches(const Expr* lhs,
                                         const Expr* rhs) {
    lhs = cpp_out_of_line_strip_implicit_casts(lhs);
    rhs = cpp_out_of_line_strip_implicit_casts(rhs);
    if (!lhs || !rhs) {
        return lhs == rhs;
    }
    if (lhs->get_kind() != rhs->get_kind()) {
        return false;
    }

    switch (lhs->get_kind()) {
        case StmtKind::VarRef: {
            const auto* lhs_ref = static_cast<const VarRef*>(lhs);
            const auto* rhs_ref = static_cast<const VarRef*>(rhs);
            if (lhs_ref->get_name() != rhs_ref->get_name()) {
                return false;
            }
            const auto* lhs_parameter =
                lhs_ref->symref ? lhs_ref->symref->template_parameter_decl : nullptr;
            const auto* rhs_parameter =
                rhs_ref->symref ? rhs_ref->symref->template_parameter_decl : nullptr;
            if (lhs_parameter || rhs_parameter) {
                return cpp_out_of_line_template_parameter_matches(
                    lhs_parameter,
                    rhs_parameter);
            }
            return lhs_ref->symref == rhs_ref->symref;
        }
        case StmtKind::UnresolvedLookupExpr: {
            const auto* lhs_lookup =
                static_cast<const UnresolvedLookupExpr*>(lhs);
            const auto* rhs_lookup =
                static_cast<const UnresolvedLookupExpr*>(rhs);
            return lhs_lookup->name == rhs_lookup->name &&
                   lhs_lookup->requires_template_keyword ==
                       rhs_lookup->requires_template_keyword &&
                   lhs_lookup->is_dependent == rhs_lookup->is_dependent &&
                   cpp_out_of_line_dependent_lookup_qualifier_matches(
                       lhs_lookup->qualifier,
                       rhs_lookup->qualifier) &&
                   cpp_out_of_line_template_argument_list_matches(
                       lhs_lookup->explicit_template_arguments,
                       rhs_lookup->explicit_template_arguments);
        }
        case StmtKind::FuncCall: {
            const auto* lhs_call = static_cast<const FuncCall*>(lhs);
            const auto* rhs_call = static_cast<const FuncCall*>(rhs);
            return cpp_out_of_line_expr_matches(
                       lhs_call->func.get(),
                       rhs_call->func.get()) &&
                   cpp_out_of_line_expr_vector_matches(
                       lhs_call->args,
                       rhs_call->args);
        }
        case StmtKind::DependentCallExpr: {
            const auto* lhs_call = static_cast<const DependentCallExpr*>(lhs);
            const auto* rhs_call = static_cast<const DependentCallExpr*>(rhs);
            return cpp_out_of_line_expr_matches(
                       lhs_call->callee.get(),
                       rhs_call->callee.get()) &&
                   cpp_out_of_line_expr_vector_matches(
                       lhs_call->args,
                       rhs_call->args);
        }
        case StmtKind::CppMemberCallExpr: {
            const auto* lhs_call = static_cast<const CppMemberCallExpr*>(lhs);
            const auto* rhs_call = static_cast<const CppMemberCallExpr*>(rhs);
            return lhs_call->member_name == rhs_call->member_name &&
                   lhs_call->isArrow == rhs_call->isArrow &&
                   lhs_call->suppress_virtual_dispatch ==
                       rhs_call->suppress_virtual_dispatch &&
                   lhs_call->has_implicit_object_argument ==
                       rhs_call->has_implicit_object_argument &&
                   cpp_out_of_line_expr_matches(
                       lhs_call->lowered_call.get(),
                       rhs_call->lowered_call.get());
        }
        case StmtKind::MemberExpr: {
            const auto* lhs_member = static_cast<const MemberExpr*>(lhs);
            const auto* rhs_member = static_cast<const MemberExpr*>(rhs);
            return lhs_member->isArrow == rhs_member->isArrow &&
                   lhs_member->get_member_name() == rhs_member->get_member_name() &&
                   cpp_out_of_line_expr_matches(
                       lhs_member->base.get(),
                       rhs_member->base.get());
        }
        case StmtKind::UnresolvedMemberExpr: {
            const auto* lhs_member = static_cast<const UnresolvedMemberExpr*>(lhs);
            const auto* rhs_member = static_cast<const UnresolvedMemberExpr*>(rhs);
            return lhs_member->isArrow == rhs_member->isArrow &&
                   lhs_member->is_current_instantiation ==
                       rhs_member->is_current_instantiation &&
                   lhs_member->names_dependent_base ==
                       rhs_member->names_dependent_base &&
                   lhs_member->requires_template_keyword ==
                       rhs_member->requires_template_keyword &&
                   lhs_member->member_name == rhs_member->member_name &&
                   cpp_out_of_line_expr_matches(
                       lhs_member->base.get(),
                       rhs_member->base.get()) &&
                   cpp_out_of_line_template_argument_list_matches(
                       lhs_member->explicit_template_arguments,
                       rhs_member->explicit_template_arguments);
        }
        case StmtKind::UnaryOperation: {
            const auto* lhs_unary = static_cast<const UnaryOperation*>(lhs);
            const auto* rhs_unary = static_cast<const UnaryOperation*>(rhs);
            return lhs_unary->uop == rhs_unary->uop &&
                   cpp_out_of_line_expr_matches(
                       lhs_unary->exp.get(),
                       rhs_unary->exp.get());
        }
        case StmtKind::DependentUnaryExpr: {
            const auto* lhs_unary =
                static_cast<const DependentUnaryExpr*>(lhs);
            const auto* rhs_unary =
                static_cast<const DependentUnaryExpr*>(rhs);
            return lhs_unary->uop == rhs_unary->uop &&
                   cpp_out_of_line_expr_matches(
                       lhs_unary->operand.get(),
                       rhs_unary->operand.get());
        }
        case StmtKind::MemberPointerAccessExpr: {
            const auto* lhs_access =
                static_cast<const MemberPointerAccessExpr*>(lhs);
            const auto* rhs_access =
                static_cast<const MemberPointerAccessExpr*>(rhs);
            return lhs_access->is_arrow == rhs_access->is_arrow &&
                   lhs_access->is_function_member ==
                       rhs_access->is_function_member &&
                   cpp_out_of_line_expr_matches(
                       lhs_access->base.get(),
                       rhs_access->base.get()) &&
                   cpp_out_of_line_expr_matches(
                       lhs_access->member_pointer.get(),
                       rhs_access->member_pointer.get());
        }
        case StmtKind::DependentMemberPointerAccessExpr: {
            const auto* lhs_access =
                static_cast<const DependentMemberPointerAccessExpr*>(lhs);
            const auto* rhs_access =
                static_cast<const DependentMemberPointerAccessExpr*>(rhs);
            return lhs_access->is_arrow == rhs_access->is_arrow &&
                   cpp_out_of_line_expr_matches(
                       lhs_access->base.get(),
                       rhs_access->base.get()) &&
                   cpp_out_of_line_expr_matches(
                       lhs_access->member_pointer.get(),
                       rhs_access->member_pointer.get());
        }
        default:
            return false;
    }
}

inline bool cpp_out_of_line_type_matches(QualType lhs,
                                         QualType rhs,
                                         bool ignore_top_level_qualifiers) {
    if (!lhs || !rhs) {
        return lhs.get_shared() == rhs.get_shared();
    }

    lhs = desugar_typedefs(lhs);
    rhs = desugar_typedefs(rhs);
    if (ignore_top_level_qualifiers) {
        lhs = QualType(lhs.get_shared());
        rhs = QualType(rhs.get_shared());
    } else if (lhs.get_qualifiers() != rhs.get_qualifiers()) {
        return false;
    }

    if (!lhs || !rhs) {
        return lhs.get_shared() == rhs.get_shared();
    }

    auto* lhs_raw = lhs.get();
    auto* rhs_raw = rhs.get();
    if (!lhs_raw || !rhs_raw) {
        return lhs_raw == rhs_raw;
    }
    if (lhs_raw->kind != rhs_raw->kind) {
        return ignore_top_level_qualifiers
            ? lhs.equals_unqualified(rhs)
            : lhs.equals_qualified(rhs);
    }

    if (auto* lhs_parm = dyn_cast<TemplateTypeParmType>(lhs_raw)) {
        auto* rhs_parm = dyn_cast<TemplateTypeParmType>(rhs_raw);
        return rhs_parm &&
               lhs_parm->depth == rhs_parm->depth &&
               lhs_parm->index == rhs_parm->index;
    }
    if (auto* lhs_ptr = dyn_cast<PointerType>(lhs_raw)) {
        auto* rhs_ptr = dyn_cast<PointerType>(rhs_raw);
        return rhs_ptr &&
               cpp_out_of_line_type_matches(
                   lhs_ptr->pointed_type,
                   rhs_ptr->pointed_type,
                   false);
    }
    if (auto* lhs_ref = dyn_cast<ReferenceType>(lhs_raw)) {
        auto* rhs_ref = dyn_cast<ReferenceType>(rhs_raw);
        return rhs_ref &&
               lhs_ref->reference_kind == rhs_ref->reference_kind &&
               cpp_out_of_line_type_matches(
                   lhs_ref->referred_type,
                   rhs_ref->referred_type,
                   false);
    }
    if (auto* lhs_mem_ptr = dyn_cast<MemberPointerType>(lhs_raw)) {
        auto* rhs_mem_ptr = dyn_cast<MemberPointerType>(rhs_raw);
        return rhs_mem_ptr &&
               cpp_out_of_line_type_matches(
                   lhs_mem_ptr->class_type,
                   rhs_mem_ptr->class_type,
                   false) &&
               cpp_out_of_line_type_matches(
                   lhs_mem_ptr->member_type,
                   rhs_mem_ptr->member_type,
                   false);
    }
    if (auto* lhs_block_ptr = dyn_cast<BlockPointerType>(lhs_raw)) {
        auto* rhs_block_ptr = dyn_cast<BlockPointerType>(rhs_raw);
        return rhs_block_ptr &&
               cpp_out_of_line_type_matches(
                   lhs_block_ptr->pointed_type,
                   rhs_block_ptr->pointed_type,
                   false);
    }
    if (auto* lhs_array = dyn_cast<ArrayType>(lhs_raw)) {
        auto* rhs_array = dyn_cast<ArrayType>(rhs_raw);
        if (!rhs_array || lhs_array->size_kind != rhs_array->size_kind) {
            return false;
        }
        if (lhs_array->size_kind == ArraySizeKind::Constant &&
            lhs_array->size.has_value() &&
            rhs_array->size.has_value() &&
            lhs_array->size.value() != rhs_array->size.value()) {
            return false;
        }
        return cpp_out_of_line_type_matches(
            lhs_array->element_type,
            rhs_array->element_type,
            false);
    }
    if (auto* lhs_func = dyn_cast<FunctionType>(lhs_raw)) {
        auto* rhs_func = dyn_cast<FunctionType>(rhs_raw);
        if (!rhs_func ||
            lhs_func->member_ref_qualifier != rhs_func->member_ref_qualifier ||
            lhs_func->has_prototype != rhs_func->has_prototype ||
            lhs_func->is_variadic != rhs_func->is_variadic ||
            !function_exception_specs_equal(*lhs_func, *rhs_func) ||
            lhs_func->parameters.size() != rhs_func->parameters.size()) {
            return false;
        }
        if (!cpp_out_of_line_type_matches(
                lhs_func->ret_type,
                rhs_func->ret_type,
                true)) {
            return false;
        }
        for (size_t idx = 0; idx < lhs_func->parameters.size(); ++idx) {
            if (lhs_func->parameter_is_pack(idx) !=
                rhs_func->parameter_is_pack(idx)) {
                return false;
            }
            if (!cpp_out_of_line_type_matches(
                    lhs_func->parameters[idx],
                    rhs_func->parameters[idx],
                    true)) {
                return false;
            }
        }
        return true;
    }
    if (auto* lhs_specialization = dyn_cast<TemplateSpecializationType>(lhs_raw)) {
        auto* rhs_specialization = dyn_cast<TemplateSpecializationType>(rhs_raw);
        if (!rhs_specialization ||
            lhs_specialization->template_name != rhs_specialization->template_name ||
            lhs_specialization->arguments.size() !=
                rhs_specialization->arguments.size()) {
            return false;
        }
        if (lhs_specialization->primary_template &&
            rhs_specialization->primary_template &&
            !template_decls_share_lookup_identity(
                lhs_specialization->primary_template,
                rhs_specialization->primary_template)) {
            return false;
        }
        for (size_t idx = 0; idx < lhs_specialization->arguments.size(); ++idx) {
            const auto& lhs_argument = lhs_specialization->arguments[idx];
            const auto& rhs_argument = rhs_specialization->arguments[idx];
            if (lhs_argument.kind != rhs_argument.kind) {
                return false;
            }
            if (lhs_argument.kind == TemplateArgumentKind::Type &&
                !cpp_out_of_line_type_matches(
                    lhs_argument.type,
                    rhs_argument.type,
                    false)) {
                return false;
            }
            if (lhs_argument.kind == TemplateArgumentKind::Value &&
                !lhs_argument.equals(rhs_argument)) {
                return false;
            }
        }
        return true;
    }
    if (auto* lhs_dependent = dyn_cast<DependentNameType>(lhs_raw)) {
        auto* rhs_dependent = dyn_cast<DependentNameType>(rhs_raw);
        if (!rhs_dependent ||
            lhs_dependent->member_name != rhs_dependent->member_name ||
            lhs_dependent->template_arguments.size() !=
                rhs_dependent->template_arguments.size()) {
            return false;
        }
        if (!cpp_out_of_line_type_matches(
                lhs_dependent->qualifier_type,
                rhs_dependent->qualifier_type,
                false)) {
            return false;
        }
        for (size_t idx = 0; idx < lhs_dependent->template_arguments.size(); ++idx) {
            const auto& lhs_argument = lhs_dependent->template_arguments[idx];
            const auto& rhs_argument = rhs_dependent->template_arguments[idx];
            if (lhs_argument.kind != rhs_argument.kind) {
                return false;
            }
            if (lhs_argument.kind == TemplateArgumentKind::Type &&
                !cpp_out_of_line_type_matches(
                    lhs_argument.type,
                    rhs_argument.type,
                    false)) {
                return false;
            }
            if (lhs_argument.kind == TemplateArgumentKind::Value &&
                !lhs_argument.equals(rhs_argument)) {
                return false;
            }
        }
        return true;
    }
    if (auto* lhs_decltype = dyn_cast<DecltypeExprType>(lhs_raw)) {
        auto* rhs_decltype = dyn_cast<DecltypeExprType>(rhs_raw);
        return rhs_decltype &&
               lhs_decltype->use_declared_type_rule ==
                   rhs_decltype->use_declared_type_rule &&
               cpp_out_of_line_expr_matches(
                   lhs_decltype->expr.get(),
                   rhs_decltype->expr.get());
    }
    if (auto* lhs_vector = dyn_cast<VectorType>(lhs_raw)) {
        auto* rhs_vector = dyn_cast<VectorType>(rhs_raw);
        return rhs_vector &&
               lhs_vector->total_bytes == rhs_vector->total_bytes &&
               cpp_out_of_line_type_matches(
                   lhs_vector->element_type,
                   rhs_vector->element_type,
                   false);
    }

    return ignore_top_level_qualifiers
        ? lhs.equals_unqualified(rhs)
        : lhs.equals_qualified(rhs);
}

inline bool cpp_primary_template_owner_matches(
    const ClassTemplateDecl* class_template,
    const std::vector<TemplateArgument>& arguments) {
    if (!class_template) {
        return false;
    }
    TemplateArgumentBindings bindings;
    if (!bind_template_arguments_to_parameters(
            class_template->parameters,
            arguments,
            bindings,
            nullptr)) {
        return false;
    }
    if (bindings.size() != class_template->parameters.size()) {
        return false;
    }
    for (size_t idx = 0; idx < bindings.size(); ++idx) {
        const auto* argument = bindings[idx].single_argument();
        if (!argument) {
            return false;
        }
        if (auto* type_parameter =
                dyn_cast<TemplateTypeParmDecl>(class_template->parameters[idx].get())) {
            if (argument->kind != TemplateArgumentKind::Type ||
                !argument->type ||
                argument->type.get_qualifiers() != QUAL_NONE) {
                return false;
            }
            auto argument_type = desugar_typedefs(argument->type);
            auto* argument_parm =
                dyn_cast<TemplateTypeParmType>(argument_type.get());
            const auto* expected_parm = type_parameter->type.get();
            if (!argument_parm || !expected_parm ||
                argument_parm->depth != expected_parm->depth ||
                argument_parm->index != expected_parm->index) {
                return false;
            }
            continue;
        }
        auto* non_type_parameter =
            dyn_cast<TemplateNonTypeParmDecl>(class_template->parameters[idx].get());
        if (!non_type_parameter ||
            argument->kind != TemplateArgumentKind::Value ||
            !argument->is_dependent ||
            !argument->referenced_parameter) {
            return false;
        }
        const auto* referenced_parameter = argument->referenced_parameter;
        if (referenced_parameter->get_kind() != non_type_parameter->get_kind() ||
            referenced_parameter->depth != non_type_parameter->depth ||
            referenced_parameter->index != non_type_parameter->index ||
            referenced_parameter->is_parameter_pack !=
                non_type_parameter->is_parameter_pack) {
            return false;
        }
    }
    return true;
}

#endif // ABURI_PARSER_CPP_OUT_OF_LINE_MATCH_H
