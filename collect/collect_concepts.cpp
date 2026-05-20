#include "collect.h"
#include "collect_templates_internal.h"
#include "../ast/special_members.h"

using template_sema_internal::lookup_symbol_remap_in_clone_context;
using template_sema_internal::clone_symbol_shallow_for_specialization;
using template_sema_internal::make_template_binding_clone_pass_builder;
using template_sema_internal::normalize_concrete_template_value_argument;
using template_sema_internal::template_argument_has_known_payload;
using template_sema_internal::template_arguments_depend_on_template_parameters;

namespace {

bool const_value_to_constraint_bool(const ConstValue& value, bool& out) {
    switch (value.kind) {
        case ConstValueKind::Integer:
            out = value.int_value.to_unsigned_u64() != 0;
            return true;
        case ConstValueKind::Boolean:
            out = value.bool_value;
            return true;
        case ConstValueKind::Floating:
            out = value.float_value.value != 0.0L;
            return true;
        case ConstValueKind::NullPointer:
            out = false;
            return true;
        case ConstValueKind::Address:
        case ConstValueKind::MemberPointer:
            out = true;
            return true;
        default:
            return false;
    }
}

bool evaluate_constraint_expr_to_bool(Expr* expr, SrcLoc loc, bool& out) {
    if (!expr) {
        out = false;
        return false;
    }
    ConstEvalResult eval =
        evaluate_with_consteval_compat(
            expr,
            ConstEvalMode::cpp_core_constant_expression());
    if (eval.status != ConstEvalStatus::Constant ||
        !eval.value.has_value()) {
        out = false;
        return false;
    }
    if (!const_value_to_constraint_bool(*eval.value, out)) {
        out = false;
        return false;
    }
    return true;
}

bool requires_expr_depends_on_template_parameters(
    const RequiresExpr* requires_expr,
    const ASTContext* ast_ctx,
    const Collect& collect) {
    if (!requires_expr) {
        return false;
    }
    for (const auto& parameter : requires_expr->parameters) {
        if (!parameter) {
            continue;
        }
        if (type_depends_on_template_parameters(parameter->type, ast_ctx) ||
            type_depends_on_template_parameters(
                QualType(parameter->original_type),
                ast_ctx)) {
            return true;
        }
        if (const Expr* default_arg =
                get_param_decl_default_argument(parameter.get())) {
            if (collect.expression_depends_on_template_parameters(default_arg)) {
                return true;
            }
        }
    }
    for (const auto& requirement : requires_expr->requirements) {
        if (collect.expression_depends_on_template_parameters(
                requirement.expr.get()) ||
            type_depends_on_template_parameters(
                requirement.type_requirement,
                ast_ctx) ||
            (requirement.return_type_constraint.has_value() &&
             template_arguments_depend_on_template_parameters(
                 requirement.return_type_constraint->template_arguments))) {
            return true;
        }
    }
    return false;
}

bool refresh_constraint_expr_satisfaction(
    Collect& collect,
    Expr* expr,
    SrcLoc loc) {
    if (!expr) {
        return true;
    }

    auto* stripped = Collect::strip_implicit_casts(expr);
    if (!stripped) {
        return true;
    }

    switch (stripped->get_kind()) {
        case StmtKind::ConceptSpecializationExpr: {
            auto* concept_expr =
                static_cast<ConceptSpecializationExpr*>(stripped);
            if (!concept_expr->concept_decl ||
                template_arguments_depend_on_template_parameters(
                    concept_expr->arguments)) {
                return true;
            }
            if (auto satisfaction =
                    collect.evaluate_concept_specialization(
                        concept_expr->concept_decl,
                        concept_expr->arguments,
                        loc)) {
                concept_expr->satisfaction = *satisfaction;
            }
            return true;
        }
        case StmtKind::RequiresExpr: {
            auto* requires_expr = static_cast<RequiresExpr*>(stripped);
            for (const auto& requirement : requires_expr->requirements) {
                if (!refresh_constraint_expr_satisfaction(
                        collect,
                        requirement.expr.get(),
                        requirement.location.isInvalid()
                            ? loc
                            : requirement.location)) {
                    return false;
                }
            }
            if (!collect.expression_depends_on_template_parameters(
                    requires_expr)) {
                if (auto satisfaction =
                        collect.evaluate_requires_expression(
                            requires_expr,
                            loc)) {
                    requires_expr->satisfaction = *satisfaction;
                }
            }
            return true;
        }
        case StmtKind::ParenExpr:
            return refresh_constraint_expr_satisfaction(
                collect,
                static_cast<ParenExpr*>(stripped)->subexpr.get(),
                loc);
        case StmtKind::UnaryOperation:
            return refresh_constraint_expr_satisfaction(
                collect,
                static_cast<UnaryOperation*>(stripped)->exp.get(),
                loc);
        case StmtKind::BinaryOperation: {
            auto* binary = static_cast<BinaryOperation*>(stripped);
            return refresh_constraint_expr_satisfaction(
                       collect,
                       binary->left.get(),
                       loc) &&
                   refresh_constraint_expr_satisfaction(
                       collect,
                       binary->right.get(),
                       loc);
        }
        case StmtKind::CppBuiltinThreeWayCompareExpr: {
            auto* compare =
                static_cast<CppBuiltinThreeWayCompareExpr*>(stripped);
            return refresh_constraint_expr_satisfaction(
                       collect,
                       compare->left.get(),
                       loc) &&
                   refresh_constraint_expr_satisfaction(
                       collect,
                       compare->right.get(),
                       loc);
        }
        case StmtKind::CompoundAssignOperation: {
            auto* compound =
                static_cast<CompoundAssignOperation*>(stripped);
            return refresh_constraint_expr_satisfaction(
                       collect,
                       compound->left.get(),
                       loc) &&
                   refresh_constraint_expr_satisfaction(
                       collect,
                       compound->right.get(),
                       loc);
        }
        case StmtKind::CondExpr: {
            auto* cond = static_cast<CondExpr*>(stripped);
            return refresh_constraint_expr_satisfaction(
                       collect,
                       cond->condition.get(),
                       loc) &&
                   refresh_constraint_expr_satisfaction(
                       collect,
                       cond->true_expr.get(),
                       loc) &&
                   refresh_constraint_expr_satisfaction(
                       collect,
                       cond->false_expr.get(),
                       loc);
        }
        case StmtKind::ExplicitCast:
            return refresh_constraint_expr_satisfaction(
                collect,
                static_cast<ExplicitCast*>(stripped)->expr.get(),
                loc);
        case StmtKind::ArraySubscriptExpr: {
            auto* subscript = static_cast<ArraySubscriptExpr*>(stripped);
            return refresh_constraint_expr_satisfaction(
                       collect,
                       subscript->array.get(),
                       loc) &&
                   refresh_constraint_expr_satisfaction(
                       collect,
                       subscript->index.get(),
                       loc);
        }
        case StmtKind::FuncCall: {
            auto* call = static_cast<FuncCall*>(stripped);
            if (!refresh_constraint_expr_satisfaction(
                    collect,
                    call->func.get(),
                    loc)) {
                return false;
            }
            for (const auto& arg : call->args) {
                if (!refresh_constraint_expr_satisfaction(
                        collect,
                        arg.get(),
                        loc)) {
                    return false;
                }
            }
            return true;
        }
        case StmtKind::CppMemberCallExpr:
            return refresh_constraint_expr_satisfaction(
                collect,
                static_cast<CppMemberCallExpr*>(stripped)->lowered_call.get(),
                loc);
        case StmtKind::CppConstructExpr: {
            auto* construct = static_cast<CppConstructExpr*>(stripped);
            for (const auto& arg : construct->args) {
                if (!refresh_constraint_expr_satisfaction(
                        collect,
                        arg.get(),
                        loc)) {
                    return false;
                }
            }
            return true;
        }
        case StmtKind::CppValueInitExpr:
            return true;
        case StmtKind::CppFunctionStyleCastExpr: {
            auto* cast = static_cast<CppFunctionStyleCastExpr*>(stripped);
            for (const auto& arg : cast->args) {
                if (!refresh_constraint_expr_satisfaction(
                        collect,
                        arg.get(),
                        loc)) {
                    return false;
                }
            }
            return true;
        }
        case StmtKind::MemberExpr:
            return refresh_constraint_expr_satisfaction(
                collect,
                static_cast<MemberExpr*>(stripped)->base.get(),
                loc);
        case StmtKind::InitListExpr: {
            auto* init_list = static_cast<InitListExpr*>(stripped);
            for (const auto& element : init_list->elements) {
                if (!refresh_constraint_expr_satisfaction(
                        collect,
                        element.value.get(),
                        loc)) {
                    return false;
                }
                for (const auto& designator : element.designators) {
                    if (!refresh_constraint_expr_satisfaction(
                            collect,
                            designator.index.get(),
                            loc) ||
                        !refresh_constraint_expr_satisfaction(
                            collect,
                            designator.range_end.get(),
                            loc)) {
                        return false;
                    }
                }
            }
            return true;
        }
        case StmtKind::BuiltinCallExpr: {
            auto* builtin = static_cast<BuiltinCallExpr*>(stripped);
            for (const auto& arg : builtin->args) {
                if (!refresh_constraint_expr_satisfaction(
                        collect,
                        arg.get(),
                        loc)) {
                    return false;
                }
            }
            return true;
        }
        default:
            return true;
    }
}

} // namespace

std::unique_ptr<Expr> Collect::collect_concept_specialization_expression(
    const ConceptDecl* concept_decl,
    std::string concept_name,
    std::vector<TemplateArgument> arguments,
    SrcLoc loc) {
    auto bool_type = QualType(get_builtin_bool());
    auto node = collect_make<ConceptSpecializationExpr>(
        concept_decl,
        std::move(concept_name),
        std::move(arguments),
        bool_type,
        loc);
    if (!node->concept_decl ||
        template_arguments_depend_on_template_parameters(node->arguments)) {
        return node;
    }
    if (auto satisfaction =
            evaluate_concept_specialization(
                node->concept_decl,
                node->arguments,
                loc)) {
        node->satisfaction = *satisfaction;
    }
    return node;
}

std::optional<bool> Collect::evaluate_concept_specialization(
    const ConceptDecl* concept_decl,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc) {
    if (!concept_decl || !ast_ctx_) {
        return std::nullopt;
    }

    const auto* lookup_pattern =
        dyn_cast<ConceptDecl>(
            const_cast<TemplateDecl*>(concept_decl->get_pattern_template_decl()));
    if (!lookup_pattern) {
        lookup_pattern = concept_decl;
    }
    const auto* canonical_concept =
        dyn_cast<ConceptDecl>(
            const_cast<TemplateDecl*>(
                get_template_decl_canonical_decl(lookup_pattern)));
    if (!canonical_concept) {
        canonical_concept = lookup_pattern;
    }

    TemplateArgumentBindings bindings;
    std::string binding_error;
    if (!bind_template_arguments_for_specialization(
            canonical_concept,
            arguments,
            bindings,
            loc,
            &binding_error)) {
        return false;
    }

    for (const auto& argument : arguments) {
        if (!template_argument_has_known_payload(argument)) {
            return false;
        }
    }
    for (size_t idx = 0; idx < canonical_concept->parameters.size(); ++idx) {
        auto* non_type_parameter = dyn_cast<TemplateNonTypeParmDecl>(
            canonical_concept->parameters[idx].get());
        if (!non_type_parameter || idx >= bindings.size()) {
            continue;
        }
        if (bindings[idx].arguments.empty()) {
            continue;
        }
        QualType expected_type = substitute_template_type_with_bindings(
            non_type_parameter->type,
            canonical_concept->parameters,
            bindings,
            loc);
        expected_type = finalize_deferred_semantic_type(expected_type, loc);
        for (auto& bound_argument : bindings[idx].arguments) {
            std::string normalize_error;
            if (!normalize_concrete_template_value_argument(
                    bound_argument,
                    expected_type,
                    &normalize_error)) {
                return false;
            }
        }
    }

    auto normalized_arguments =
        flatten_template_argument_bindings(bindings);
    auto* existing_entry =
        ast_ctx_->lookup_concept_specialization(
            canonical_concept,
            normalized_arguments);
    if (existing_entry) {
        existing_entry->note_first_required_loc(loc);
        if (existing_entry->is_evaluated) {
            return existing_entry->satisfaction;
        }
        if (existing_entry->is_evaluating) {
            return false;
        }
    }

    auto& specialization_entry =
        ast_ctx_->get_or_create_concept_specialization(
            canonical_concept,
            normalized_arguments);
    specialization_entry.note_first_required_loc(loc);
    if (specialization_entry.is_evaluated) {
        return specialization_entry.satisfaction;
    }
    if (specialization_entry.is_evaluating) {
        return false;
    }
    if (!ast_ctx_->push_template_instantiation_frame()) {
        return false;
    }

    specialization_entry.is_evaluating = true;
    struct EvaluationGuard {
        ASTContext* ast_ctx = nullptr;
        ConceptSpecializationEntry* entry = nullptr;
        ~EvaluationGuard() {
            if (entry) {
                entry->is_evaluating = false;
            }
            if (ast_ctx) {
                ast_ctx->pop_template_instantiation_frame();
            }
        }
    } evaluation_guard{ast_ctx_.get(), &specialization_entry};

    if (!are_template_constraints_satisfied_with_bindings(
            canonical_concept,
            bindings,
            loc)) {
        specialization_entry.satisfaction = false;
        specialization_entry.is_evaluated = true;
        return false;
    }

    if (!canonical_concept->constraint_expr) {
        specialization_entry.satisfaction = true;
        specialization_entry.is_evaluated = true;
        return true;
    }

    auto rewrite_constraint_type =
        [&](QualType type) -> QualType {
            auto rewritten =
                substitute_template_type_with_bindings(
                    type,
                    canonical_concept->parameters,
                    bindings,
                    loc);
            return collect_try_realize_deferred_semantic_type(rewritten);
        };
    auto rewrite_constraint_arguments =
        [&](const std::vector<TemplateArgument>& template_arguments)
            -> std::vector<TemplateArgument> {
            return substitute_template_arguments_with_bindings(
                template_arguments,
                canonical_concept->parameters,
                bindings,
                loc);
        };
    auto register_cloned_symbol =
        [&](const std::shared_ptr<Symbol>& sym) {
            collect_add_global_symbol(sym);
        };

    auto clone_pass_builder = make_template_binding_clone_pass_builder(
        ast_ctx_.get(),
        this,
        canonical_concept->parameters,
        bindings,
        loc,
        "concept non-type parameter requires a concrete value",
        rewrite_constraint_type,
        rewrite_constraint_arguments,
        register_cloned_symbol,
        {});
    clone_pass_builder.rewrite_symbol =
        [&](const std::shared_ptr<Symbol>& sym,
            ASTCloneContext& clone_ctx) -> std::shared_ptr<Symbol> {
            if (!sym) {
                return nullptr;
            }
            if (auto remapped =
                    lookup_symbol_remap_in_clone_context(sym, clone_ctx)) {
                return remapped;
            }

            if (const auto* variable_specialization =
                    get_symbol_variable_template_specialization(sym.get());
                variable_specialization &&
                variable_specialization->primary_template) {
                auto rewritten_arguments =
                    substitute_template_arguments_with_bindings(
                        variable_specialization->arguments,
                        canonical_concept->parameters,
                        bindings,
                        loc);
                std::shared_ptr<Symbol> rewritten_symbol = nullptr;
                auto* rewritten_decl =
                    instantiate_variable_template_specialization(
                        variable_specialization->primary_template,
                        rewritten_arguments,
                        loc,
                        &rewritten_symbol);
                if (rewritten_decl && rewritten_symbol) {
                    return rewritten_symbol;
                }
            }

            if (const auto* function_specialization =
                    get_symbol_function_template_specialization(sym.get());
                function_specialization &&
                function_specialization->primary_template) {
                auto rewritten_arguments =
                    substitute_template_arguments_with_bindings(
                        function_specialization->arguments,
                        canonical_concept->parameters,
                        bindings,
                        loc);
                std::shared_ptr<Symbol> rewritten_symbol = nullptr;
                auto* rewritten_decl =
                    instantiate_function_template_specialization(
                        function_specialization->primary_template,
                        rewritten_arguments,
                        loc,
                        &rewritten_symbol,
                        /*instantiate_definition=*/true);
                if (rewritten_decl && rewritten_symbol) {
                    return rewritten_symbol;
                }
            }

            return sym;
        };

    auto clone_pass = clone_pass_builder.build_substitution_pass();
    std::string clone_error;
    auto rewritten_constraint =
        clone_pass.clone_expr(
            canonical_concept->constraint_expr.get(),
            &clone_error);
    if (!rewritten_constraint) {
        specialization_entry.satisfaction = false;
        specialization_entry.evaluation_failed = true;
        specialization_entry.is_evaluated = true;
        return false;
    }

    auto dependent_resolution_pass =
        clone_pass_builder.build_dependent_resolution_pass(
            clone_pass,
            [&](std::unique_ptr<Expr>& expr,
                std::string* error_out) -> bool {
                return resolve_dependent_expr_after_substitution(
                    expr,
                    QualType(nullptr),
                    error_out);
            });
    if (!dependent_resolution_pass.resolve_expr_in_place(
            rewritten_constraint,
            &clone_error)) {
        specialization_entry.satisfaction = false;
        specialization_entry.evaluation_failed = true;
        specialization_entry.is_evaluated = true;
        return false;
    }
    if (!refresh_constraint_expr_satisfaction(
            *this,
            rewritten_constraint.get(),
            loc)) {
        specialization_entry.satisfaction = false;
        specialization_entry.evaluation_failed = true;
        specialization_entry.is_evaluated = true;
        return false;
    }

    bool satisfaction = false;
    if (!evaluate_constraint_expr_to_bool(
            rewritten_constraint.get(),
            loc,
            satisfaction)) {
        satisfaction = false;
    }

    specialization_entry.satisfaction = satisfaction;
    specialization_entry.is_evaluated = true;
    return satisfaction;
}

std::unique_ptr<Expr> Collect::collect_requires_expression(
    std::vector<std::unique_ptr<ParamDecl>> parameters,
    std::vector<ConstraintRequirement> requirements,
    SrcLoc loc) {
    auto bool_type = QualType(get_builtin_bool());
    auto node = collect_make<RequiresExpr>(
        std::move(parameters),
        std::move(requirements),
        bool_type,
        loc);
    if (auto satisfaction = evaluate_requires_expression(node.get(), loc)) {
        node->satisfaction = *satisfaction;
    }
    return node;
}

std::optional<bool> Collect::evaluate_requires_expression(
    const RequiresExpr* requires_expr,
    SrcLoc loc) {
    if (!requires_expr) {
        return std::nullopt;
    }
    if (requires_expr_depends_on_template_parameters(
            requires_expr,
            ast_ctx_.get(),
            *this)) {
        return std::nullopt;
    }

    for (const auto& parameter : requires_expr->parameters) {
        if (!parameter) {
            continue;
        }
        auto parameter_type =
            collect_try_realize_deferred_semantic_type(parameter->type);
        auto original_type =
            collect_try_realize_deferred_semantic_type(
                QualType(parameter->original_type));
        if (!parameter_type ||
            type_depends_on_template_parameters(parameter_type, ast_ctx_.get()) ||
            (original_type &&
             type_depends_on_template_parameters(original_type, ast_ctx_.get()))) {
            return false;
        }
    }

    for (const auto& requirement : requires_expr->requirements) {
        switch (requirement.kind) {
            case ConstraintRequirementKind::Simple:
                if (!requirement.expr || isa<ErrorExpr>(requirement.expr.get())) {
                    return false;
                }
                break;
            case ConstraintRequirementKind::Type: {
                auto realized_type =
                    collect_try_realize_deferred_semantic_type(
                        requirement.type_requirement);
                if (!realized_type ||
                    type_depends_on_template_parameters(
                        realized_type,
                        ast_ctx_.get())) {
                    return false;
                }
                break;
            }
            case ConstraintRequirementKind::Nested: {
                bool nested_satisfied = false;
                if (!evaluate_constraint_expr_to_bool(
                        requirement.expr.get(),
                        requirement.location.isInvalid()
                            ? loc
                            : requirement.location,
                        nested_satisfied) ||
                    !nested_satisfied) {
                    return false;
                }
                break;
            }
            case ConstraintRequirementKind::Compound: {
                if (!requirement.expr ||
                    isa<ErrorExpr>(requirement.expr.get())) {
                    return false;
                }
                if (requirement.is_noexcept &&
                    !cpp_expression_is_known_noexcept(
                        requirement.expr.get(),
                        ast_ctx_.get())) {
                    return false;
                }
                if (requirement.return_type_constraint) {
                    const auto& type_constraint =
                        *requirement.return_type_constraint;
                    if (!type_constraint.concept_decl) {
                        return false;
                    }
                    SrcLoc constraint_loc = type_constraint.location.isInvalid()
                                                ? loc
                                                : type_constraint.location;
                    auto result_type = resolve_decltype_expression_type(
                        requirement.expr.get(),
                        /*use_declared_type_rule=*/false,
                        QualType(),
                        constraint_loc,
                        DeferredTypeResolutionMode::TryRealize);
                    if (!result_type ||
                        type_depends_on_template_parameters(
                            result_type,
                            ast_ctx_.get())) {
                        return false;
                    }

                    std::vector<TemplateArgument> concept_arguments;
                    concept_arguments.push_back(TemplateArgument(result_type));
                    concept_arguments.insert(
                        concept_arguments.end(),
                        type_constraint.template_arguments.begin(),
                        type_constraint.template_arguments.end());
                    auto concept_expr =
                        collect_concept_specialization_expression(
                            type_constraint.concept_decl,
                            type_constraint.concept_name,
                            std::move(concept_arguments),
                            constraint_loc);
                    auto* concept_specialization =
                        dyn_cast<ConceptSpecializationExpr>(
                            concept_expr.get());
                    if (!concept_specialization ||
                        !concept_specialization->satisfaction.has_value() ||
                        !*concept_specialization->satisfaction) {
                        return false;
                    }
                }
                break;
            }
        }
    }

    return true;
}

bool Collect::are_template_constraints_satisfied(
    const TemplateDecl* template_decl,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc) {
    if (!template_decl) {
        return false;
    }

    TemplateArgumentBindings bindings;
    std::string binding_error;
    if (!bind_template_arguments_for_specialization(
            template_decl,
            arguments,
            bindings,
            loc,
            &binding_error)) {
        return false;
    }
    return are_template_constraints_satisfied_with_bindings(
        template_decl,
        bindings,
        loc);
}

bool Collect::are_template_constraints_satisfied_with_bindings(
    const TemplateDecl* template_decl,
    const TemplateArgumentBindings& bindings,
    SrcLoc loc) {
    if (!template_decl) {
        return false;
    }

    auto evaluate_constraint_with_bindings =
        [&](const Expr* constraint_expr) -> bool {
            if (!constraint_expr) {
                return true;
            }

            auto rewrite_constraint_type =
                [&](QualType type) -> QualType {
                    auto rewritten =
                        substitute_template_type_with_bindings(
                            type,
                            template_decl->parameters,
                            bindings,
                            loc);
                    return collect_try_realize_deferred_semantic_type(rewritten);
                };
            auto rewrite_constraint_arguments =
                [&](const std::vector<TemplateArgument>& template_arguments)
                    -> std::vector<TemplateArgument> {
                    return substitute_template_arguments_with_bindings(
                        template_arguments,
                        template_decl->parameters,
                        bindings,
                        loc);
                };
            auto register_cloned_symbol =
                [&](const std::shared_ptr<Symbol>& sym) {
                    collect_add_global_symbol(sym);
                };

            auto clone_pass_builder = make_template_binding_clone_pass_builder(
                ast_ctx_.get(),
                this,
                template_decl->parameters,
                bindings,
                loc,
                "constraint non-type parameter requires a concrete value",
                rewrite_constraint_type,
                rewrite_constraint_arguments,
                register_cloned_symbol,
                {});
            if (auto* function_decl = dyn_cast<FuncDecl>(
                    const_cast<Decl*>(template_decl->get_templated_decl()))) {
                for (const auto& parameter : function_decl->parameters) {
                    auto* param_decl = dyn_cast<ParamDecl>(parameter.get());
                    if (!param_decl || !param_decl->sym) {
                        continue;
                    }
                    QualType rewritten_param_type =
                        rewrite_constraint_type(param_decl->sym->type);
                    if (!rewritten_param_type) {
                        return false;
                    }
                    clone_pass_builder.symbol_remap[param_decl->sym.get()] =
                        clone_symbol_shallow_for_specialization(
                            param_decl->sym,
                            rewritten_param_type);
                }
            }
            clone_pass_builder.rewrite_symbol =
                [&](const std::shared_ptr<Symbol>& sym,
                    ASTCloneContext& clone_ctx) -> std::shared_ptr<Symbol> {
                    if (!sym) {
                        return nullptr;
                    }
                    if (auto remapped =
                            lookup_symbol_remap_in_clone_context(
                                sym,
                                clone_ctx)) {
                        return remapped;
                    }
                    if (const auto* variable_specialization =
                            get_symbol_variable_template_specialization(
                                sym.get());
                        variable_specialization &&
                        variable_specialization->primary_template) {
                        auto rewritten_arguments =
                            substitute_template_arguments_with_bindings(
                                variable_specialization->arguments,
                                template_decl->parameters,
                                bindings,
                                loc);
                        std::shared_ptr<Symbol> rewritten_symbol = nullptr;
                        auto* rewritten_decl =
                            instantiate_variable_template_specialization(
                                variable_specialization->primary_template,
                                rewritten_arguments,
                                loc,
                                &rewritten_symbol);
                        if (rewritten_decl && rewritten_symbol) {
                            return rewritten_symbol;
                        }
                    }
                    if (const auto* function_specialization =
                            get_symbol_function_template_specialization(
                                sym.get());
                        function_specialization &&
                        function_specialization->primary_template) {
                        auto rewritten_arguments =
                            substitute_template_arguments_with_bindings(
                                function_specialization->arguments,
                                template_decl->parameters,
                                bindings,
                                loc);
                        std::shared_ptr<Symbol> rewritten_symbol = nullptr;
                        auto* rewritten_decl =
                            instantiate_function_template_specialization(
                                function_specialization->primary_template,
                                rewritten_arguments,
                                loc,
                                &rewritten_symbol,
                                /*instantiate_definition=*/true);
                        if (rewritten_decl && rewritten_symbol) {
                            return rewritten_symbol;
                        }
                    }
                    return sym;
                };

            auto clone_pass = clone_pass_builder.build_substitution_pass();
            std::string clone_error;
            auto rewritten_constraint =
                clone_pass.clone_expr(constraint_expr, &clone_error);
            if (!rewritten_constraint) {
                return false;
            }

            auto dependent_resolution_pass =
                clone_pass_builder.build_dependent_resolution_pass(
                    clone_pass,
                    [&](std::unique_ptr<Expr>& expr,
                        std::string* error_out) -> bool {
                        return resolve_dependent_expr_after_substitution(
                            expr,
                            QualType(nullptr),
                            error_out);
                    });
            if (!dependent_resolution_pass.resolve_expr_in_place(
                    rewritten_constraint,
                    &clone_error)) {
                return false;
            }
            if (!refresh_constraint_expr_satisfaction(
                    *this,
                    rewritten_constraint.get(),
                    loc)) {
                return false;
            }

            bool satisfied = false;
            if (!evaluate_constraint_expr_to_bool(
                    rewritten_constraint.get(),
                    loc,
                    satisfied)) {
                return false;
            }
            return satisfied;
        };

    for (const auto& parameter : template_decl->parameters) {
        auto* type_parameter =
            dyn_cast<TemplateTypeParmDecl>(parameter.get());
        if (!type_parameter || !type_parameter->type_constraint) {
            continue;
        }
        if (!evaluate_constraint_with_bindings(
                type_parameter->type_constraint.get())) {
            return false;
        }
    }

    if (!evaluate_constraint_with_bindings(
            template_decl->associated_constraint.get())) {
        return false;
    }

    auto* function_decl =
        dyn_cast<FuncDecl>(const_cast<Decl*>(template_decl->get_templated_decl()));
    if (function_decl &&
        function_decl->trailing_requires_clause &&
        !evaluate_constraint_with_bindings(
            function_decl->trailing_requires_clause.get())) {
        return false;
    }

    return true;
}
