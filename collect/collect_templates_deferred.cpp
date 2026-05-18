#include "collect.h"
#include "collect_internal.h"
#include "../ast/expr_clone.h"
#include "../helpers/auto_type_utils.h"

namespace {
enum class VarRefQualifierDependency {
    None,
    Dependent,
    NonDependent,
};

bool decltype_uses_declared_entity_rule(bool use_declared_type_rule,
                                        const Expr* expr) {
    if (!use_declared_type_rule || !expr) {
        return false;
    }
    auto* stripped = Collect::strip_implicit_casts(const_cast<Expr*>(expr));
    return isa<VarRef>(stripped) ||
           isa<MemberExpr>(stripped) ||
           isa<UnresolvedLookupExpr>(stripped) ||
           isa<UnresolvedMemberExpr>(stripped);
}

bool template_arguments_contain_dependency(
    const std::vector<TemplateArgument>& arguments,
    const ASTContext* ast_ctx) {
    for (const auto& argument : arguments) {
        if (template_argument_depends_on_template_parameters(argument, ast_ctx)) {
            return true;
        }
    }
    return false;
}

bool template_arguments_contain_dependency(
    const std::optional<std::vector<TemplateArgument>>& arguments,
    const ASTContext* ast_ctx) {
    if (!arguments.has_value()) {
        return false;
    }
    return template_arguments_contain_dependency(*arguments, ast_ctx);
}

bool symbol_is_non_type_template_parameter(const Symbol* sym) {
    return sym &&
           isa<TemplateNonTypeParmDecl>(sym->template_parameter_decl);
}

VarRefQualifierDependency classify_var_ref_qualifier_dependency(
    const VarRef* var_ref,
    const ASTContext* ast_ctx) {
    if (!var_ref) {
        return VarRefQualifierDependency::None;
    }

    const auto* qualified_info = var_ref->get_cpp_qualified_info();
    if (!qualified_info) {
        return VarRefQualifierDependency::None;
    }
    if (qualified_info->is_current_instantiation ||
        type_depends_on_template_parameters(
            qualified_info->qualifier_type,
            ast_ctx)) {
        return VarRefQualifierDependency::Dependent;
    }
    return VarRefQualifierDependency::NonDependent;
}

bool variable_template_specialization_depends_on_template_parameters(
    const Symbol* sym,
    const ASTContext* ast_ctx) {
    if (!sym) {
        return false;
    }
    const auto* specialization_info =
        get_symbol_variable_template_specialization(sym);
    if (!specialization_info) {
        return false;
    }
    for (const auto& argument : specialization_info->arguments) {
        if (template_argument_depends_on_template_parameters(
                argument,
                ast_ctx)) {
            return true;
        }
    }
    return false;
}

const VariableDecl* find_template_dependent_variable_definition(
    const Symbol* sym) {
    if (!sym || sym->kind != SymbolKind::VARIABLE) {
        return nullptr;
    }
    if (sym->variable_definition && sym->variable_definition->init) {
        return sym->variable_definition;
    }

    QualType owner_type = get_symbol_owner_record_type(sym);
    auto owner_record = desugar_type(owner_type).as_shared<ObjectType>();
    auto* owner_decl =
        owner_record ? dyn_cast<ObjectDecl>(owner_record->get_decl()) : nullptr;
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

bool expr_depends_on_template_parameters_impl(
    const Expr* expr,
    const ASTContext* ast_ctx,
    std::unordered_set<const Symbol*>& active_variable_symbols);

bool dependent_lookup_qualifier_depends_on_template_parameters(
    const DependentLookupQualifier& qualifier,
    const ASTContext* ast_ctx) {
    return qualifier.is_current_instantiation ||
           qualifier.names_dependent_base ||
           type_depends_on_template_parameters(
               qualifier.qualifier_type,
               ast_ctx);
}

bool unresolved_lookup_is_non_dependent_declval(
    const UnresolvedLookupExpr* lookup,
    const ASTContext* ast_ctx) {
    if (!lookup ||
        (lookup->name != "declval" && lookup->name != "__declval") ||
        !lookup->explicit_template_arguments ||
        lookup->explicit_template_arguments->size() != 1) {
        return false;
    }
    return !template_argument_depends_on_template_parameters(
        lookup->explicit_template_arguments->front(),
        ast_ctx);
}

bool dependent_call_expr_depends_on_template_parameters(
    const DependentCallExpr* call,
    const ASTContext* ast_ctx,
    std::unordered_set<const Symbol*>& active_variable_symbols) {
    if (!call || !call->callee) {
        return true;
    }

    const Expr* callee =
        Collect::strip_implicit_casts(const_cast<Expr*>(call->callee.get()));
    if (!callee) {
        return true;
    }

    if (const auto* lookup = dyn_cast<UnresolvedLookupExpr>(callee)) {
        if (!unresolved_lookup_is_non_dependent_declval(lookup, ast_ctx)) {
            if (lookup->is_dependent ||
                dependent_lookup_qualifier_depends_on_template_parameters(
                    lookup->qualifier,
                    ast_ctx)) {
                return true;
            }
        }
        if (template_arguments_contain_dependency(
                lookup->explicit_template_arguments,
                ast_ctx) ||
            type_depends_on_template_parameters(lookup->ctype, ast_ctx)) {
            return true;
        }
    } else if (const auto* member = dyn_cast<UnresolvedMemberExpr>(callee)) {
        if (member->is_current_instantiation ||
            member->names_dependent_base ||
            expr_depends_on_template_parameters_impl(
                member->base.get(),
                ast_ctx,
                active_variable_symbols) ||
            template_arguments_contain_dependency(
                member->explicit_template_arguments,
                ast_ctx) ||
            type_depends_on_template_parameters(member->member_type, ast_ctx) ||
            type_depends_on_template_parameters(
                member->declared_member_type,
                ast_ctx)) {
            return true;
        }
    } else if (expr_depends_on_template_parameters_impl(
                   callee,
                   ast_ctx,
                   active_variable_symbols)) {
        return true;
    }

    for (const auto& arg : call->args) {
        if (expr_depends_on_template_parameters_impl(
                arg.get(),
                ast_ctx,
                active_variable_symbols)) {
            return true;
        }
    }

    return type_depends_on_template_parameters(call->ctype, ast_ctx) ||
           type_depends_on_template_parameters(
               call->known_function_type,
               ast_ctx);
}

bool variable_definition_depends_on_template_parameters(
    const Symbol* sym,
    const ASTContext* ast_ctx,
    std::unordered_set<const Symbol*>& active_variable_symbols) {
    if (!sym || sym->kind != SymbolKind::VARIABLE ||
        !active_variable_symbols.insert(sym).second) {
        return false;
    }

    const VariableDecl* definition = find_template_dependent_variable_definition(sym);
    bool depends = false;
    if (definition) {
        depends =
            type_depends_on_template_parameters(definition->type, ast_ctx) ||
            type_depends_on_template_parameters(
                QualType(definition->original_type),
                ast_ctx) ||
            (definition->init &&
             expr_depends_on_template_parameters_impl(
                 definition->init.get(),
                 ast_ctx,
                 active_variable_symbols));
    }

    active_variable_symbols.erase(sym);
    return depends;
}

bool type_contains_undeduced_cxx_auto(QualType type) {
    return type &&
           (auto_type_utils::auto_type_flavors_in(type.get_shared()) &
            auto_type_utils::kCxxAutoFlavor) != 0;
}

bool expr_constexpr_value_depends_on_template_parameters_impl(
    const Expr* expr,
    const ASTContext* ast_ctx,
    std::unordered_set<const Symbol*>& active_variable_symbols,
    std::unordered_set<const FuncDecl*>& active_functions,
    QualType active_record_lookup_type,
    bool defer_unmaterialized_constexpr_calls);

bool stmt_constexpr_value_depends_on_template_parameters_impl(
    const Stmt* stmt,
    const ASTContext* ast_ctx,
    std::unordered_set<const Symbol*>& active_variable_symbols,
    std::unordered_set<const FuncDecl*>& active_functions,
    QualType active_record_lookup_type,
    bool defer_unmaterialized_constexpr_calls);

bool constexpr_function_call_body_depends_on_template_parameters(
    const FuncCall* call,
    const ASTContext* ast_ctx,
    std::unordered_set<const Symbol*>& active_variable_symbols,
    std::unordered_set<const FuncDecl*>& active_functions,
    QualType active_record_lookup_type,
    bool defer_unmaterialized_constexpr_calls) {
    if (!call || !call->func) {
        return false;
    }

    auto* callee_ref = dyn_cast<VarRef>(
        Collect::strip_implicit_casts(call->func.get()));
    if (!callee_ref || !callee_ref->symref ||
        callee_ref->symref->kind != SymbolKind::FUNCTION) {
        return false;
    }

    const auto& symbol = callee_ref->symref;
    const auto* function_decl =
        dyn_cast<FuncDecl>(symbol->function_definition);
    if (!function_decl) {
        QualType owner_type = get_symbol_owner_record_type(symbol.get());
        return defer_unmaterialized_constexpr_calls &&
               (symbol->is_constexpr || symbol->is_consteval) &&
               static_cast<bool>(owner_type);
    }

    bool is_constexpr_callable =
        function_decl->is_constexpr ||
        symbol->is_constexpr ||
        symbol->is_consteval;
    if (!is_constexpr_callable) {
        return false;
    }

    QualType owner_type = get_func_decl_owner_record_type(function_decl);
    if (!owner_type) {
        owner_type = get_symbol_owner_record_type(symbol.get());
    }
    if (!owner_type &&
        (isa<CppMethodDecl>(function_decl) ||
         isa<CppConstructorDecl>(function_decl) ||
         isa<CppDestructorDecl>(function_decl))) {
        owner_type = active_record_lookup_type;
    }
    bool owner_depends =
        type_depends_on_template_parameters(owner_type, ast_ctx);
    if (!function_decl->body) {
        return (owner_depends || defer_unmaterialized_constexpr_calls) &&
               function_decl_defines_entity(function_decl);
    }

    if (!active_functions.insert(function_decl).second) {
        return false;
    }

    bool depends =
        owner_depends ||
        stmt_constexpr_value_depends_on_template_parameters_impl(
            function_decl->body.get(),
            ast_ctx,
            active_variable_symbols,
            active_functions,
            active_record_lookup_type,
            defer_unmaterialized_constexpr_calls);

    active_functions.erase(function_decl);
    return depends;
}

bool decl_constexpr_value_depends_on_template_parameters_impl(
    const Decl* decl,
    const ASTContext* ast_ctx,
    std::unordered_set<const Symbol*>& active_variable_symbols,
    std::unordered_set<const FuncDecl*>& active_functions,
    QualType active_record_lookup_type,
    bool defer_unmaterialized_constexpr_calls) {
    if (!decl) {
        return false;
    }

    if (const auto* variable = dyn_cast<VariableDecl>(decl)) {
        return type_depends_on_template_parameters(variable->type, ast_ctx) ||
               type_depends_on_template_parameters(
                   QualType(variable->original_type),
                   ast_ctx) ||
               expr_constexpr_value_depends_on_template_parameters_impl(
                   variable->init.get(),
                   ast_ctx,
                   active_variable_symbols,
                   active_functions,
                   active_record_lookup_type,
                   defer_unmaterialized_constexpr_calls);
    }

    if (const auto* static_assert_decl = dyn_cast<StaticAssertDecl>(decl)) {
        return expr_constexpr_value_depends_on_template_parameters_impl(
            static_assert_decl->condition.get(),
            ast_ctx,
            active_variable_symbols,
            active_functions,
            active_record_lookup_type,
            defer_unmaterialized_constexpr_calls);
    }

    return false;
}

bool stmt_constexpr_value_depends_on_template_parameters_impl(
    const Stmt* stmt,
    const ASTContext* ast_ctx,
    std::unordered_set<const Symbol*>& active_variable_symbols,
    std::unordered_set<const FuncDecl*>& active_functions,
    QualType active_record_lookup_type,
    bool defer_unmaterialized_constexpr_calls) {
    if (!stmt) {
        return false;
    }

    if (const auto* expr = dyn_cast<Expr>(stmt)) {
        return expr_constexpr_value_depends_on_template_parameters_impl(
            expr,
            ast_ctx,
            active_variable_symbols,
            active_functions,
            active_record_lookup_type,
            defer_unmaterialized_constexpr_calls);
    }

    switch (stmt->get_kind()) {
        case StmtKind::CompoundStmt: {
            const auto* compound = static_cast<const CompoundStmt*>(stmt);
            for (const auto& child : compound->statements) {
                if (stmt_constexpr_value_depends_on_template_parameters_impl(
                        child.get(),
                        ast_ctx,
                        active_variable_symbols,
                        active_functions,
                        active_record_lookup_type,
                        defer_unmaterialized_constexpr_calls)) {
                    return true;
                }
            }
            return false;
        }
        case StmtKind::Decl2Stmt: {
            const auto* decl_stmt = static_cast<const Decl2Stmt*>(stmt);
            for (const auto& decl : decl_stmt->decls) {
                if (decl_constexpr_value_depends_on_template_parameters_impl(
                        decl.get(),
                        ast_ctx,
                        active_variable_symbols,
                        active_functions,
                        active_record_lookup_type,
                        defer_unmaterialized_constexpr_calls)) {
                    return true;
                }
            }
            return false;
        }
        case StmtKind::ReturnStmt:
            return expr_constexpr_value_depends_on_template_parameters_impl(
                static_cast<const ReturnStmt*>(stmt)->expression.get(),
                ast_ctx,
                active_variable_symbols,
                active_functions,
                active_record_lookup_type,
                defer_unmaterialized_constexpr_calls);
        case StmtKind::IfStmt: {
            const auto* if_stmt = static_cast<const IfStmt*>(stmt);
            return stmt_constexpr_value_depends_on_template_parameters_impl(
                       if_stmt->init_stmt.get(),
                       ast_ctx,
                       active_variable_symbols,
                       active_functions,
                       active_record_lookup_type,
                       defer_unmaterialized_constexpr_calls) ||
                   expr_constexpr_value_depends_on_template_parameters_impl(
                       if_stmt->condition.get(),
                       ast_ctx,
                       active_variable_symbols,
                       active_functions,
                       active_record_lookup_type,
                       defer_unmaterialized_constexpr_calls) ||
                   stmt_constexpr_value_depends_on_template_parameters_impl(
                       if_stmt->then_stmt.get(),
                       ast_ctx,
                       active_variable_symbols,
                       active_functions,
                       active_record_lookup_type,
                       defer_unmaterialized_constexpr_calls) ||
                   stmt_constexpr_value_depends_on_template_parameters_impl(
                       if_stmt->else_stmt.get(),
                       ast_ctx,
                       active_variable_symbols,
                       active_functions,
                       active_record_lookup_type,
                       defer_unmaterialized_constexpr_calls);
        }
        default:
            return false;
    }
}

bool expr_constexpr_value_depends_on_template_parameters_impl(
    const Expr* expr,
    const ASTContext* ast_ctx,
    std::unordered_set<const Symbol*>& active_variable_symbols,
    std::unordered_set<const FuncDecl*>& active_functions,
    QualType active_record_lookup_type,
    bool defer_unmaterialized_constexpr_calls) {
    if (!expr) {
        return false;
    }

    if (expr_depends_on_template_parameters_impl(
            expr,
            ast_ctx,
            active_variable_symbols)) {
        return true;
    }

    auto* stripped = Collect::strip_implicit_casts(const_cast<Expr*>(expr));
    if (!stripped) {
        return false;
    }

    switch (stripped->get_kind()) {
        case StmtKind::FuncCall: {
            const auto* call = static_cast<const FuncCall*>(stripped);
            if (expr_constexpr_value_depends_on_template_parameters_impl(
                    call->func.get(),
                    ast_ctx,
                    active_variable_symbols,
                    active_functions,
                    active_record_lookup_type,
                    defer_unmaterialized_constexpr_calls)) {
                return true;
            }
            for (const auto& arg : call->args) {
                if (expr_constexpr_value_depends_on_template_parameters_impl(
                        arg.get(),
                        ast_ctx,
                        active_variable_symbols,
                        active_functions,
                        active_record_lookup_type,
                        defer_unmaterialized_constexpr_calls)) {
                    return true;
                }
            }
            return constexpr_function_call_body_depends_on_template_parameters(
                call,
                ast_ctx,
                active_variable_symbols,
                active_functions,
                active_record_lookup_type,
                defer_unmaterialized_constexpr_calls);
        }
        case StmtKind::CppMemberCallExpr: {
            const auto* call = static_cast<const CppMemberCallExpr*>(stripped);
            return expr_constexpr_value_depends_on_template_parameters_impl(
                call->lowered_call.get(),
                ast_ctx,
                active_variable_symbols,
                active_functions,
                active_record_lookup_type,
                defer_unmaterialized_constexpr_calls);
        }
        case StmtKind::UnaryOperation:
            return expr_constexpr_value_depends_on_template_parameters_impl(
                static_cast<const UnaryOperation*>(stripped)->exp.get(),
                ast_ctx,
                active_variable_symbols,
                active_functions,
                active_record_lookup_type,
                defer_unmaterialized_constexpr_calls);
        case StmtKind::BinaryOperation: {
            const auto* binary = static_cast<const BinaryOperation*>(stripped);
            return expr_constexpr_value_depends_on_template_parameters_impl(
                       binary->left.get(),
                       ast_ctx,
                       active_variable_symbols,
                       active_functions,
                       active_record_lookup_type,
                       defer_unmaterialized_constexpr_calls) ||
                   expr_constexpr_value_depends_on_template_parameters_impl(
                       binary->right.get(),
                       ast_ctx,
                       active_variable_symbols,
                       active_functions,
                       active_record_lookup_type,
                       defer_unmaterialized_constexpr_calls);
        }
        case StmtKind::CondExpr: {
            const auto* cond = static_cast<const CondExpr*>(stripped);
            return expr_constexpr_value_depends_on_template_parameters_impl(
                       cond->condition.get(),
                       ast_ctx,
                       active_variable_symbols,
                       active_functions,
                       active_record_lookup_type,
                       defer_unmaterialized_constexpr_calls) ||
                   expr_constexpr_value_depends_on_template_parameters_impl(
                       cond->true_expr.get(),
                       ast_ctx,
                       active_variable_symbols,
                       active_functions,
                       active_record_lookup_type,
                       defer_unmaterialized_constexpr_calls) ||
                   expr_constexpr_value_depends_on_template_parameters_impl(
                       cond->false_expr.get(),
                       ast_ctx,
                       active_variable_symbols,
                       active_functions,
                       active_record_lookup_type,
                       defer_unmaterialized_constexpr_calls);
        }
        case StmtKind::ExplicitCast:
            return expr_constexpr_value_depends_on_template_parameters_impl(
                static_cast<const ExplicitCast*>(stripped)->expr.get(),
                ast_ctx,
                active_variable_symbols,
                active_functions,
                active_record_lookup_type,
                defer_unmaterialized_constexpr_calls);
        case StmtKind::CppImmediateInvocationExpr:
            return expr_constexpr_value_depends_on_template_parameters_impl(
                static_cast<const CppImmediateInvocationExpr*>(stripped)
                    ->invocation.get(),
                ast_ctx,
                active_variable_symbols,
                active_functions,
                active_record_lookup_type,
                defer_unmaterialized_constexpr_calls);
        default:
            return false;
    }
}

bool expr_depends_on_template_parameters_impl(const Expr* expr,
                                              const ASTContext* ast_ctx,
                                              std::unordered_set<const Symbol*>&
                                                  active_variable_symbols) {
    if (!expr) {
        return false;
    }

    auto* stripped = Collect::strip_implicit_casts(const_cast<Expr*>(expr));
    if (!stripped) {
        return false;
    }

    if (auto* var_ref = dyn_cast<VarRef>(stripped)) {
        VarRefQualifierDependency qualifier_dependency =
            classify_var_ref_qualifier_dependency(var_ref, ast_ctx);
        if (qualifier_dependency == VarRefQualifierDependency::Dependent) {
            return true;
        }
        if (qualifier_dependency != VarRefQualifierDependency::NonDependent &&
            type_depends_on_template_parameters(
                get_symbol_owner_record_type(var_ref->symref.get()),
                ast_ctx)) {
            return true;
        }
        if (symbol_is_non_type_template_parameter(var_ref->symref.get())) {
            return true;
        }
        if (variable_template_specialization_depends_on_template_parameters(
                var_ref->symref.get(),
                ast_ctx)) {
            return true;
        }
        if (qualifier_dependency != VarRefQualifierDependency::NonDependent &&
            variable_definition_depends_on_template_parameters(
                var_ref->symref.get(),
                ast_ctx,
                active_variable_symbols)) {
            return true;
        }
    }

    if (type_depends_on_template_parameters(stripped->get_type(), ast_ctx)) {
        return true;
    }
    bool is_non_dependent_declval_call = false;
    if (auto* dependent_call = dyn_cast<DependentCallExpr>(stripped)) {
        auto* callee_lookup = dyn_cast<UnresolvedLookupExpr>(
            Collect::strip_implicit_casts(dependent_call->callee.get()));
        is_non_dependent_declval_call =
            unresolved_lookup_is_non_dependent_declval(callee_lookup, ast_ctx);
    }

    // A C++ auto placeholder that survives expression collection is an
    // undeduced placeholder. In templates this can happen for locals whose
    // initializer is dependent; uses of that local must be treated as dependent
    // so semantic checks run after specialization deduces the placeholder.
    if (!is_non_dependent_declval_call &&
        type_contains_undeduced_cxx_auto(stripped->get_type())) {
        return true;
    }

    switch (stripped->get_kind()) {
        case StmtKind::UnresolvedLookupExpr: {
            const auto* lookup =
                static_cast<const UnresolvedLookupExpr*>(stripped);
            return lookup->is_dependent ||
                   template_arguments_contain_dependency(
                       lookup->explicit_template_arguments,
                       ast_ctx);
        }
        case StmtKind::UnresolvedMemberExpr: {
            const auto* member =
                static_cast<const UnresolvedMemberExpr*>(stripped);
            return member->is_current_instantiation ||
                   member->names_dependent_base ||
                   expr_depends_on_template_parameters_impl(
                       member->base.get(),
                       ast_ctx,
                       active_variable_symbols) ||
                   template_arguments_contain_dependency(
                       member->explicit_template_arguments,
                       ast_ctx);
        }
        case StmtKind::DependentCallExpr:
            return dependent_call_expr_depends_on_template_parameters(
                static_cast<const DependentCallExpr*>(stripped),
                ast_ctx,
                active_variable_symbols);
        case StmtKind::DependentArraySubscriptExpr:
        case StmtKind::DependentUnaryExpr:
        case StmtKind::DependentBinaryExpr:
        case StmtKind::DependentMemberPointerAccessExpr:
        case StmtKind::PackExpansionExpr:
        case StmtKind::FoldExpr:
            return true;
        case StmtKind::ConceptSpecializationExpr: {
            const auto* concept_expr =
                static_cast<const ConceptSpecializationExpr*>(stripped);
            for (const auto& argument : concept_expr->arguments) {
                if (template_argument_depends_on_template_parameters(
                        argument,
                        ast_ctx)) {
                    return true;
                }
            }
            return false;
        }
        case StmtKind::RequiresExpr: {
            const auto* requires_expr =
                static_cast<const RequiresExpr*>(stripped);
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
                    if (expr_depends_on_template_parameters_impl(
                            default_arg,
                            ast_ctx,
                            active_variable_symbols)) {
                        return true;
                    }
                }
            }
            for (const auto& requirement : requires_expr->requirements) {
                if (expr_depends_on_template_parameters_impl(
                        requirement.expr.get(),
                        ast_ctx,
                        active_variable_symbols) ||
                    type_depends_on_template_parameters(
                        requirement.type_requirement,
                        ast_ctx) ||
                    (requirement.return_type_constraint.has_value() &&
                     template_arguments_contain_dependency(
                         requirement.return_type_constraint->template_arguments,
                         ast_ctx))) {
                    return true;
                }
            }
            return false;
        }
        case StmtKind::UnaryOperation:
            return expr_depends_on_template_parameters_impl(
                static_cast<const UnaryOperation*>(stripped)->exp.get(),
                ast_ctx,
                active_variable_symbols);
        case StmtKind::BinaryOperation: {
            const auto* binary = static_cast<const BinaryOperation*>(stripped);
            return expr_depends_on_template_parameters_impl(
                       binary->left.get(),
                       ast_ctx,
                       active_variable_symbols) ||
                   expr_depends_on_template_parameters_impl(
                       binary->right.get(),
                       ast_ctx,
                       active_variable_symbols);
        }
        case StmtKind::CppBuiltinThreeWayCompareExpr: {
            const auto* compare =
                static_cast<const CppBuiltinThreeWayCompareExpr*>(stripped);
            return expr_depends_on_template_parameters_impl(
                       compare->left.get(),
                       ast_ctx,
                       active_variable_symbols) ||
                   expr_depends_on_template_parameters_impl(
                       compare->right.get(),
                       ast_ctx,
                       active_variable_symbols);
        }
        case StmtKind::CompoundAssignOperation: {
            const auto* binary =
                static_cast<const CompoundAssignOperation*>(stripped);
            return expr_depends_on_template_parameters_impl(
                       binary->left.get(),
                       ast_ctx,
                       active_variable_symbols) ||
                   expr_depends_on_template_parameters_impl(
                       binary->right.get(),
                       ast_ctx,
                       active_variable_symbols);
        }
        case StmtKind::CondExpr: {
            const auto* cond = static_cast<const CondExpr*>(stripped);
            return expr_depends_on_template_parameters_impl(
                       cond->condition.get(),
                       ast_ctx,
                       active_variable_symbols) ||
                   expr_depends_on_template_parameters_impl(
                       cond->true_expr.get(),
                       ast_ctx,
                       active_variable_symbols) ||
                   expr_depends_on_template_parameters_impl(
                       cond->false_expr.get(),
                       ast_ctx,
                       active_variable_symbols);
        }
        case StmtKind::ExplicitCast:
            return type_depends_on_template_parameters(
                       static_cast<const ExplicitCast*>(stripped)->ctype,
                       ast_ctx) ||
                   expr_depends_on_template_parameters_impl(
                       static_cast<const ExplicitCast*>(stripped)->expr.get(),
                       ast_ctx,
                       active_variable_symbols);
        case StmtKind::ArraySubscriptExpr: {
            const auto* subscript =
                static_cast<const ArraySubscriptExpr*>(stripped);
            return expr_depends_on_template_parameters_impl(
                       subscript->array.get(),
                       ast_ctx,
                       active_variable_symbols) ||
                   expr_depends_on_template_parameters_impl(
                       subscript->index.get(),
                       ast_ctx,
                       active_variable_symbols);
        }
        case StmtKind::FuncCall: {
            const auto* call = static_cast<const FuncCall*>(stripped);
            if (expr_depends_on_template_parameters_impl(
                    call->func.get(),
                    ast_ctx,
                    active_variable_symbols)) {
                return true;
            }
            for (const auto& arg : call->args) {
                if (expr_depends_on_template_parameters_impl(
                        arg.get(),
                        ast_ctx,
                        active_variable_symbols)) {
                    return true;
                }
            }
            return false;
        }
        case StmtKind::CppMemberCallExpr: {
            const auto* call = static_cast<const CppMemberCallExpr*>(stripped);
            return call->lowered_call &&
                   expr_depends_on_template_parameters_impl(
                       call->lowered_call.get(),
                       ast_ctx,
                       active_variable_symbols);
        }
        case StmtKind::CppConstructExpr: {
            const auto* construct =
                static_cast<const CppConstructExpr*>(stripped);
            for (const auto& arg : construct->args) {
                if (expr_depends_on_template_parameters_impl(
                        arg.get(),
                        ast_ctx,
                        active_variable_symbols)) {
                    return true;
                }
            }
            return false;
        }
        case StmtKind::CppValueInitExpr:
            return type_depends_on_template_parameters(
                static_cast<const CppValueInitExpr*>(stripped)->ctype,
                ast_ctx);
        case StmtKind::CppFunctionStyleCastExpr: {
            const auto* cast =
                static_cast<const CppFunctionStyleCastExpr*>(stripped);
            if (type_depends_on_template_parameters(
                    cast->target_type,
                    ast_ctx)) {
                return true;
            }
            for (const auto& arg : cast->args) {
                if (expr_depends_on_template_parameters_impl(
                        arg.get(),
                        ast_ctx,
                        active_variable_symbols)) {
                    return true;
                }
            }
            return false;
        }
        case StmtKind::MemberExpr:
            return expr_depends_on_template_parameters_impl(
                static_cast<const MemberExpr*>(stripped)->base.get(),
                ast_ctx,
                active_variable_symbols);
        case StmtKind::MemberPointerAccessExpr: {
            const auto* access =
                static_cast<const MemberPointerAccessExpr*>(stripped);
            return expr_depends_on_template_parameters_impl(
                       access->base.get(),
                       ast_ctx,
                       active_variable_symbols) ||
                   expr_depends_on_template_parameters_impl(
                       access->member_pointer.get(),
                       ast_ctx,
                       active_variable_symbols);
        }
        case StmtKind::InitListExpr: {
            const auto* init_list = static_cast<const InitListExpr*>(stripped);
            for (const auto& element : init_list->elements) {
                if (expr_depends_on_template_parameters_impl(
                        element.value.get(),
                        ast_ctx,
                        active_variable_symbols)) {
                    return true;
                }
                for (const auto& designator : element.designators) {
                    if (expr_depends_on_template_parameters_impl(
                            designator.index.get(),
                            ast_ctx,
                            active_variable_symbols) ||
                        expr_depends_on_template_parameters_impl(
                            designator.range_end.get(),
                            ast_ctx,
                            active_variable_symbols)) {
                        return true;
                    }
                }
            }
            return false;
        }
        case StmtKind::CompoundLiteralExpr:
            return expr_depends_on_template_parameters_impl(
                static_cast<const CompoundLiteralExpr*>(stripped)->init.get(),
                ast_ctx,
                active_variable_symbols);
        case StmtKind::SizeOfExpr: {
            const auto* sizeof_expr = static_cast<const SizeOfExpr*>(stripped);
            return expr_depends_on_template_parameters_impl(
                       sizeof_expr->expr_operand.get(),
                       ast_ctx,
                       active_variable_symbols) ||
                   type_depends_on_template_parameters(
                       sizeof_expr->type_operand,
                       ast_ctx);
        }
        case StmtKind::SizeOfPackExpr:
            return true;
        case StmtKind::AlignOfExpr: {
            const auto* alignof_expr =
                static_cast<const AlignOfExpr*>(stripped);
            return expr_depends_on_template_parameters_impl(
                       alignof_expr->expr_operand.get(),
                       ast_ctx,
                       active_variable_symbols) ||
                   type_depends_on_template_parameters(
                       alignof_expr->type_operand,
                       ast_ctx);
        }
        case StmtKind::CppNoexceptExpr:
            return expr_depends_on_template_parameters_impl(
                static_cast<const CppNoexceptExpr*>(stripped)->operand.get(),
                ast_ctx,
                active_variable_symbols);
        case StmtKind::CppPseudoDestructorExpr: {
            const auto* pseudo_dtor =
                static_cast<const CppPseudoDestructorExpr*>(stripped);
            return expr_depends_on_template_parameters_impl(
                       pseudo_dtor->base.get(),
                       ast_ctx,
                       active_variable_symbols) ||
                   type_depends_on_template_parameters(
                       pseudo_dtor->destroyed_type,
                       ast_ctx);
        }
        case StmtKind::GenericExpr: {
            const auto* generic = static_cast<const GenericExpr*>(stripped);
            if (expr_depends_on_template_parameters_impl(
                    generic->controlling_expr.get(),
                    ast_ctx,
                    active_variable_symbols)) {
                return true;
            }
            for (const auto& assoc : generic->associations) {
                if (expr_depends_on_template_parameters_impl(
                        assoc.expr.get(),
                        ast_ctx,
                        active_variable_symbols) ||
                    type_depends_on_template_parameters(assoc.type, ast_ctx)) {
                    return true;
                }
            }
            return false;
        }
        case StmtKind::BuiltinCallExpr: {
            const auto* builtin = static_cast<const BuiltinCallExpr*>(stripped);
            for (const auto& arg : builtin->args) {
                if (expr_depends_on_template_parameters_impl(
                        arg.get(),
                        ast_ctx,
                        active_variable_symbols)) {
                    return true;
                }
            }
            for (const auto& type_arg : builtin->type_args) {
                if (type_depends_on_template_parameters(type_arg, ast_ctx)) {
                    return true;
                }
            }
            return false;
        }
        case StmtKind::CppTypeIdExpr:
            return type_depends_on_template_parameters(
                       static_cast<const CppTypeIdExpr*>(stripped)->type_operand,
                       ast_ctx) ||
                   expr_depends_on_template_parameters_impl(
                       static_cast<const CppTypeIdExpr*>(stripped)->expr_operand.get(),
                       ast_ctx,
                       active_variable_symbols);
        case StmtKind::CppDynamicCastExpr: {
            const auto* cast = static_cast<const CppDynamicCastExpr*>(stripped);
            return type_depends_on_template_parameters(cast->target_type, ast_ctx) ||
                   expr_depends_on_template_parameters_impl(
                       cast->expr.get(),
                       ast_ctx,
                       active_variable_symbols);
        }
        default:
            return false;
    }
}

using NoteSpecializationUseForConstantEval =
    std::function<void(const std::shared_ptr<Symbol>&, SrcLoc)>;

void materialize_function_type_exception_spec_for_constant_evaluation(
    const Collect& collect,
    QualType type,
    SrcLoc loc,
    const NoteSpecializationUseForConstantEval& note_specialization_use,
    std::unordered_set<const Expr*>& active_exprs,
    std::unordered_set<const Symbol*>& active_symbols);

void materialize_symbol_for_constant_evaluation(
    const Collect& collect,
    const std::shared_ptr<Symbol>& symbol,
    SrcLoc loc,
    bool materialize_body,
    const NoteSpecializationUseForConstantEval& note_specialization_use,
    std::unordered_set<const Expr*>& active_exprs,
    std::unordered_set<const Symbol*>& active_symbols) {
    if (!symbol || symbol->kind != SymbolKind::FUNCTION) {
        return;
    }
    if (!active_symbols.insert(symbol.get()).second) {
        return;
    }
    if (materialize_body) {
        note_specialization_use(symbol, loc);
    }
    materialize_function_type_exception_spec_for_constant_evaluation(
        collect,
        symbol->type,
        loc,
        note_specialization_use,
        active_exprs,
        active_symbols);
    active_symbols.erase(symbol.get());
}

void materialize_expr_for_constant_evaluation(
    const Collect& collect,
    const Expr* expr,
    SrcLoc loc,
    bool evaluated_context,
    const NoteSpecializationUseForConstantEval& note_specialization_use,
    std::unordered_set<const Expr*>& active_exprs,
    std::unordered_set<const Symbol*>& active_symbols);

void materialize_function_type_exception_spec_for_constant_evaluation(
    const Collect& collect,
    QualType type,
    SrcLoc loc,
    const NoteSpecializationUseForConstantEval& note_specialization_use,
    std::unordered_set<const Expr*>& active_exprs,
    std::unordered_set<const Symbol*>& active_symbols) {
    auto canonical = desugar_type(type);
    if (auto pointer = canonical.as_shared<PointerType>()) {
        canonical = desugar_type(pointer->pointed_type);
    } else if (auto block_pointer = canonical.as_shared<BlockPointerType>()) {
        canonical = desugar_type(block_pointer->pointed_type);
    }
    auto function_type = canonical.as_shared<FunctionType>();
    if (!function_type || !function_type->exception_spec_expr) {
        return;
    }
    materialize_expr_for_constant_evaluation(
        collect,
        function_type->exception_spec_expr.get(),
        loc,
        true,
        note_specialization_use,
        active_exprs,
        active_symbols);
}

void materialize_expr_for_constant_evaluation(
    const Collect& collect,
    const Expr* expr,
    SrcLoc loc,
    bool evaluated_context,
    const NoteSpecializationUseForConstantEval& note_specialization_use,
    std::unordered_set<const Expr*>& active_exprs,
    std::unordered_set<const Symbol*>& active_symbols) {
    if (!expr || !active_exprs.insert(expr).second) {
        return;
    }

    const Expr* stripped =
        Collect::strip_implicit_casts(const_cast<Expr*>(expr));
    if (!stripped) {
        active_exprs.erase(expr);
        return;
    }

    auto visit = [&](const std::unique_ptr<Expr>& child,
                     bool child_evaluated = true) {
        materialize_expr_for_constant_evaluation(
            collect,
            child.get(),
            loc,
            child_evaluated,
            note_specialization_use,
            active_exprs,
            active_symbols);
    };
    auto visit_symbol = [&](const std::shared_ptr<Symbol>& symbol,
                            bool materialize_body) {
        materialize_symbol_for_constant_evaluation(
            collect,
            symbol,
            loc,
            materialize_body,
            note_specialization_use,
            active_exprs,
            active_symbols);
    };
    auto visit_call_target = [&](const Expr* callee) {
        auto* callee_ref = dyn_cast<VarRef>(
            Collect::strip_implicit_casts(const_cast<Expr*>(callee)));
        if (callee_ref) {
            visit_symbol(callee_ref->symref, evaluated_context);
        }
        if (callee) {
            materialize_function_type_exception_spec_for_constant_evaluation(
                collect,
                const_cast<Expr*>(callee)->get_type(),
                loc,
                note_specialization_use,
                active_exprs,
                active_symbols);
        }
    };

    switch (stripped->get_kind()) {
        case StmtKind::FuncCall: {
            const auto* call = static_cast<const FuncCall*>(stripped);
            visit_call_target(call->func.get());
            visit(call->func, evaluated_context);
            for (const auto& arg : call->args) {
                visit(arg, evaluated_context);
            }
            break;
        }
        case StmtKind::CppMemberCallExpr: {
            const auto* call =
                static_cast<const CppMemberCallExpr*>(stripped);
            materialize_expr_for_constant_evaluation(
                collect,
                call->lowered_call.get(),
                loc,
                evaluated_context,
                note_specialization_use,
                active_exprs,
                active_symbols);
            break;
        }
        case StmtKind::CppConstructExpr: {
            const auto* construct =
                static_cast<const CppConstructExpr*>(stripped);
            visit_symbol(construct->ctor_sym, evaluated_context);
            for (const auto& arg : construct->args) {
                visit(arg, evaluated_context);
            }
            break;
        }
        case StmtKind::CppFunctionStyleCastExpr: {
            const auto* cast =
                static_cast<const CppFunctionStyleCastExpr*>(stripped);
            for (const auto& arg : cast->args) {
                visit(arg, evaluated_context);
            }
            break;
        }
        case StmtKind::CppImmediateInvocationExpr:
            visit(static_cast<const CppImmediateInvocationExpr*>(stripped)
                      ->invocation,
                  evaluated_context);
            break;
        case StmtKind::CppNoexceptExpr:
            visit(static_cast<const CppNoexceptExpr*>(stripped)->operand,
                  false);
            break;
        case StmtKind::UnaryOperation:
            visit(static_cast<const UnaryOperation*>(stripped)->exp,
                  evaluated_context);
            break;
        case StmtKind::DependentUnaryExpr:
            visit(static_cast<const DependentUnaryExpr*>(stripped)->operand,
                  evaluated_context);
            break;
        case StmtKind::BinaryOperation: {
            const auto* binary = static_cast<const BinaryOperation*>(stripped);
            visit(binary->left, evaluated_context);
            visit(binary->right, evaluated_context);
            break;
        }
        case StmtKind::DependentBinaryExpr: {
            const auto* binary =
                static_cast<const DependentBinaryExpr*>(stripped);
            visit(binary->left, evaluated_context);
            visit(binary->right, evaluated_context);
            break;
        }
        case StmtKind::CppBuiltinThreeWayCompareExpr: {
            const auto* compare =
                static_cast<const CppBuiltinThreeWayCompareExpr*>(stripped);
            visit(compare->left, evaluated_context);
            visit(compare->right, evaluated_context);
            break;
        }
        case StmtKind::CompoundAssignOperation: {
            const auto* binary =
                static_cast<const CompoundAssignOperation*>(stripped);
            visit(binary->left, evaluated_context);
            visit(binary->right, evaluated_context);
            break;
        }
        case StmtKind::CondExpr: {
            const auto* cond = static_cast<const CondExpr*>(stripped);
            visit(cond->condition, evaluated_context);
            visit(cond->true_expr, evaluated_context);
            visit(cond->false_expr, evaluated_context);
            break;
        }
        case StmtKind::ImplicitCast:
            visit(static_cast<const ImplicitCast*>(stripped)->expr,
                  evaluated_context);
            break;
        case StmtKind::ExplicitCast:
            visit(static_cast<const ExplicitCast*>(stripped)->expr,
                  evaluated_context);
            break;
        case StmtKind::ArraySubscriptExpr: {
            const auto* subscript =
                static_cast<const ArraySubscriptExpr*>(stripped);
            visit(subscript->array, evaluated_context);
            visit(subscript->index, evaluated_context);
            break;
        }
        case StmtKind::DependentArraySubscriptExpr: {
            const auto* subscript =
                static_cast<const DependentArraySubscriptExpr*>(stripped);
            visit(subscript->array, evaluated_context);
            visit(subscript->index, evaluated_context);
            break;
        }
        case StmtKind::MemberExpr:
            visit(static_cast<const MemberExpr*>(stripped)->base,
                  evaluated_context);
            break;
        case StmtKind::UnresolvedMemberExpr:
            visit(static_cast<const UnresolvedMemberExpr*>(stripped)->base,
                  evaluated_context);
            break;
        case StmtKind::MemberPointerLiteralExpr: {
            const auto* literal =
                static_cast<const MemberPointerLiteralExpr*>(stripped);
            visit_symbol(literal->method_symbol, evaluated_context);
            break;
        }
        case StmtKind::MemberPointerAccessExpr: {
            const auto* access =
                static_cast<const MemberPointerAccessExpr*>(stripped);
            visit(access->base, evaluated_context);
            visit(access->member_pointer, evaluated_context);
            break;
        }
        case StmtKind::DependentMemberPointerAccessExpr: {
            const auto* access =
                static_cast<const DependentMemberPointerAccessExpr*>(stripped);
            visit(access->base, evaluated_context);
            visit(access->member_pointer, evaluated_context);
            break;
        }
        case StmtKind::PackExpansionExpr:
            visit(static_cast<const PackExpansionExpr*>(stripped)->pattern,
                  evaluated_context);
            break;
        case StmtKind::FoldExpr: {
            const auto* fold = static_cast<const FoldExpr*>(stripped);
            visit(fold->pattern, evaluated_context);
            visit(fold->init, evaluated_context);
            break;
        }
        case StmtKind::InitListExpr: {
            const auto* init_list = static_cast<const InitListExpr*>(stripped);
            for (const auto& element : init_list->elements) {
                visit(element.value, evaluated_context);
                for (const auto& designator : element.designators) {
                    visit(designator.index, evaluated_context);
                    visit(designator.range_end, evaluated_context);
                }
            }
            break;
        }
        case StmtKind::CompoundLiteralExpr:
            visit(static_cast<const CompoundLiteralExpr*>(stripped)->init,
                  evaluated_context);
            break;
        case StmtKind::SizeOfExpr:
        case StmtKind::AlignOfExpr:
        case StmtKind::CppTypeIdExpr:
            break;
        case StmtKind::GenericExpr: {
            const auto* generic = static_cast<const GenericExpr*>(stripped);
            visit(generic->controlling_expr, evaluated_context);
            if (generic->result_index < generic->associations.size()) {
                materialize_expr_for_constant_evaluation(
                    collect,
                    generic->associations[generic->result_index].expr.get(),
                    loc,
                    evaluated_context,
                    note_specialization_use,
                    active_exprs,
                    active_symbols);
            }
            break;
        }
        case StmtKind::BuiltinCallExpr: {
            const auto* builtin = static_cast<const BuiltinCallExpr*>(stripped);
            for (const auto& arg : builtin->args) {
                visit(arg, evaluated_context);
            }
            break;
        }
        case StmtKind::CppDynamicCastExpr:
            visit(static_cast<const CppDynamicCastExpr*>(stripped)->expr,
                  evaluated_context);
            break;
        case StmtKind::CppThrowExpr:
            visit(static_cast<const CppThrowExpr*>(stripped)->thrown_expr,
                  evaluated_context);
            break;
        case StmtKind::CppNewExpr: {
            const auto* new_expr = static_cast<const CppNewExpr*>(stripped);
            visit_symbol(new_expr->allocator_sym, evaluated_context);
            visit_symbol(new_expr->ctor_sym, evaluated_context);
            for (const auto& arg : new_expr->placement_args) {
                visit(arg, evaluated_context);
            }
            visit(new_expr->initializer, evaluated_context);
            for (const auto& arg : new_expr->constructor_args) {
                visit(arg, evaluated_context);
            }
            break;
        }
        case StmtKind::CppDeleteExpr: {
            const auto* delete_expr =
                static_cast<const CppDeleteExpr*>(stripped);
            visit(delete_expr->operand, evaluated_context);
            visit_symbol(delete_expr->deallocator_sym, evaluated_context);
            visit_symbol(delete_expr->destructor_sym, evaluated_context);
            break;
        }
        case StmtKind::CppPseudoDestructorExpr: {
            const auto* pseudo_dtor =
                static_cast<const CppPseudoDestructorExpr*>(stripped);
            visit(pseudo_dtor->base, evaluated_context);
            visit_symbol(pseudo_dtor->destructor_sym, evaluated_context);
            break;
        }
        case StmtKind::BlockByrefAccessExpr:
            visit(static_cast<const BlockByrefAccessExpr*>(stripped)->cell_expr,
                  evaluated_context);
            break;
        case StmtKind::VaArgExpr:
            visit(static_cast<const VaArgExpr*>(stripped)->va_list_expr,
                  evaluated_context);
            break;
        case StmtKind::VaStartExpr: {
            const auto* va_start = static_cast<const VaStartExpr*>(stripped);
            visit(va_start->va_list_expr, evaluated_context);
            visit(va_start->last_param, evaluated_context);
            break;
        }
        case StmtKind::VaEndExpr:
            visit(static_cast<const VaEndExpr*>(stripped)->va_list_expr,
                  evaluated_context);
            break;
        case StmtKind::VaCopyExpr: {
            const auto* va_copy = static_cast<const VaCopyExpr*>(stripped);
            visit(va_copy->dest, evaluated_context);
            visit(va_copy->src, evaluated_context);
            break;
        }
        default:
            break;
    }

    active_exprs.erase(expr);
}
} // namespace

bool Collect::contains_deferred_semantic_type(
    const std::shared_ptr<CType>& type) const {
    if (!type) {
        return false;
    }
    if (isa<TypeofExprType>(type.get()) ||
        isa<DecltypeExprType>(type.get()) ||
        isa<BuiltinTypeTransformType>(type.get())) {
        return true;
    }
    if (auto typedef_type = dyn_cast_shared<TypedefType>(type)) {
        return contains_deferred_semantic_type(
            typedef_type->underlying_type.get_shared());
    }
    if (auto specialization = dyn_cast_shared<TemplateSpecializationType>(type)) {
        auto resolved_type =
            query_lookup_template_specialization_resolved_type(
                specialization.get());
        if (!resolved_type && !specialization->is_dependent) {
            return true;
        }
        if (resolved_type &&
            contains_deferred_semantic_type(resolved_type.get_shared())) {
            return true;
        }
        for (const auto& argument : specialization->arguments) {
            if (argument.kind == TemplateArgumentKind::Type) {
                if (contains_deferred_semantic_type(argument.type.get_shared())) {
                    return true;
                }
            } else if (contains_deferred_semantic_type(
                           argument.value_type.get_shared())) {
                return true;
            }
        }
        return false;
    }
    if (auto dependent_name = dyn_cast_shared<DependentNameType>(type)) {
        auto resolved_type =
            query_lookup_dependent_name_resolved_type(dependent_name.get());
        if (!resolved_type) {
            return true;
        }
        if (contains_deferred_semantic_type(resolved_type.get_shared())) {
            return true;
        }
        if (contains_deferred_semantic_type(
                dependent_name->qualifier_type.get_shared())) {
            return true;
        }
        for (const auto& argument : dependent_name->template_arguments) {
            if (argument.kind == TemplateArgumentKind::Type) {
                if (contains_deferred_semantic_type(argument.type.get_shared())) {
                    return true;
                }
            } else if (contains_deferred_semantic_type(
                           argument.value_type.get_shared())) {
                return true;
            }
        }
        return false;
    }
    if (auto ptr = dyn_cast_shared<PointerType>(type)) {
        return contains_deferred_semantic_type(ptr->pointed_type.get_shared());
    }
    if (auto ref = dyn_cast_shared<ReferenceType>(type)) {
        return contains_deferred_semantic_type(ref->referred_type.get_shared());
    }
    if (auto mem_ptr = dyn_cast_shared<MemberPointerType>(type)) {
        return contains_deferred_semantic_type(mem_ptr->class_type.get_shared()) ||
               contains_deferred_semantic_type(mem_ptr->member_type.get_shared());
    }
    if (auto blk = dyn_cast_shared<BlockPointerType>(type)) {
        return contains_deferred_semantic_type(blk->pointed_type.get_shared());
    }
    if (auto arr = dyn_cast_shared<ArrayType>(type)) {
        return contains_deferred_semantic_type(arr->element_type.get_shared());
    }
    if (auto func = dyn_cast_shared<FunctionType>(type)) {
        if (contains_deferred_semantic_type(func->ret_type.get_shared())) {
            return true;
        }
        for (const auto& parameter : func->parameters) {
            if (contains_deferred_semantic_type(parameter.get_shared())) {
                return true;
            }
        }
        return false;
    }
    if (auto vec = dyn_cast_shared<VectorType>(type)) {
        return contains_deferred_semantic_type(vec->element_type.get_shared());
    }
    return false;
}

bool Collect::decltype_expression_requires_deferred_resolution(
    const Expr* expr) const {
    if (!expr) {
        return true;
    }

    auto* stripped = strip_implicit_casts(const_cast<Expr*>(expr));
    if (!stripped) {
        return true;
    }

    if (expression_depends_on_template_parameters(stripped)) {
        return true;
    }

    switch (stripped->get_kind()) {
        case StmtKind::UnresolvedLookupExpr:
            return static_cast<const UnresolvedLookupExpr*>(stripped)
                ->is_dependent;
        case StmtKind::DependentCallExpr:
            break;
        case StmtKind::DependentArraySubscriptExpr:
        case StmtKind::DependentUnaryExpr:
        case StmtKind::DependentBinaryExpr:
        case StmtKind::DependentMemberPointerAccessExpr:
        case StmtKind::FoldExpr:
            return true;
        case StmtKind::ConceptSpecializationExpr: {
            const auto* concept_expr =
                static_cast<const ConceptSpecializationExpr*>(stripped);
            for (const auto& argument : concept_expr->arguments) {
                if (template_argument_depends_on_template_parameters(
                        argument,
                        ast_ctx_.get())) {
                    return true;
                }
            }
            return false;
        }
        case StmtKind::RequiresExpr:
            return expression_depends_on_template_parameters(stripped);
        case StmtKind::CppPseudoDestructorExpr: {
            const auto* pseudo_dtor =
                static_cast<const CppPseudoDestructorExpr*>(stripped);
            return (pseudo_dtor->base &&
                    expression_depends_on_template_parameters(
                        pseudo_dtor->base.get())) ||
                   type_depends_on_template_parameters(
                       pseudo_dtor->destroyed_type,
                       ast_ctx_.get());
        }
        case StmtKind::UnresolvedMemberExpr: {
            const auto* member =
                static_cast<const UnresolvedMemberExpr*>(stripped);
            if (member->is_current_instantiation ||
                member->names_dependent_base) {
                return true;
            }
            QualType base_type =
                member->base ? member->base->get_type() : QualType();
            if (type_depends_on_template_parameters(base_type, ast_ctx_.get()) ||
                contains_deferred_semantic_type(base_type.get_shared()) ||
                type_contains_undeduced_cxx_auto(base_type)) {
                return true;
            }
            if (!member->member_type || !member->declared_member_type) {
                return true;
            }
            return type_depends_on_template_parameters(
                       member->member_type,
                       ast_ctx_.get()) ||
                   contains_deferred_semantic_type(
                       member->member_type.get_shared()) ||
                   type_contains_undeduced_cxx_auto(member->member_type) ||
                   type_depends_on_template_parameters(
                       member->declared_member_type,
                       ast_ctx_.get()) ||
                   contains_deferred_semantic_type(
                       member->declared_member_type.get_shared()) ||
                   type_contains_undeduced_cxx_auto(
                       member->declared_member_type);
        }
        default:
            break;
    }

    auto expr_type = stripped->get_type();
    if (!expr_type) {
        return true;
    }

    return type_depends_on_template_parameters(expr_type, ast_ctx_.get()) ||
           contains_deferred_semantic_type(expr_type.get_shared()) ||
           type_contains_undeduced_cxx_auto(expr_type);
}

bool Collect::expression_depends_on_template_parameters(
    const Expr* expr) const {
    std::unordered_set<const Symbol*> active_variable_symbols;
    return expr_depends_on_template_parameters_impl(
        expr,
        ast_ctx_.get(),
        active_variable_symbols);
}

bool Collect::expression_constexpr_value_depends_on_template_parameters(
    const Expr* expr,
    bool defer_unmaterialized_constexpr_calls) const {
    std::unordered_set<const Symbol*> active_variable_symbols;
    std::unordered_set<const FuncDecl*> active_functions;
    return expr_constexpr_value_depends_on_template_parameters_impl(
        expr,
        ast_ctx_.get(),
        active_variable_symbols,
        active_functions,
        session_.current_cpp_record_lookup_type_,
        defer_unmaterialized_constexpr_calls);
}

bool Collect::expression_is_value_dependent_for_constant_evaluation(
    const Expr* expr,
    bool defer_unmaterialized_constexpr_calls) const {
    if (!expr) {
        return false;
    }
    QualType expr_type = const_cast<Expr*>(expr)->get_type();
    return expression_depends_on_template_parameters(expr) ||
           expression_constexpr_value_depends_on_template_parameters(
               expr,
               defer_unmaterialized_constexpr_calls) ||
           (expr_type &&
            type_depends_on_template_parameters(expr_type, ast_ctx_.get()));
}

void Collect::materialize_specialization_uses_for_evaluated_expression(
    const Expr* expr,
    SrcLoc loc) const {
    std::unordered_set<const Expr*> active_exprs;
    std::unordered_set<const Symbol*> active_symbols;
    NoteSpecializationUseForConstantEval note_specialization_use =
        [this](const std::shared_ptr<Symbol>& symbol, SrcLoc use_loc) {
            note_specialization_use_for_symbol(symbol, use_loc);
        };
    materialize_expr_for_constant_evaluation(
        *this,
        expr,
        loc,
        true,
        note_specialization_use,
        active_exprs,
        active_symbols);
}

void Collect::materialize_specialization_uses_for_constant_evaluation(
    const Expr* expr,
    SrcLoc loc) const {
    materialize_specialization_uses_for_evaluated_expression(expr, loc);
}

void Collect::materialize_specialization_uses_for_noexcept_evaluation(
    const Expr* expr,
    SrcLoc loc) const {
    std::unordered_set<const Expr*> active_exprs;
    std::unordered_set<const Symbol*> active_symbols;
    NoteSpecializationUseForConstantEval note_specialization_use =
        [this](const std::shared_ptr<Symbol>& symbol, SrcLoc use_loc) {
            note_specialization_use_for_symbol(symbol, use_loc);
        };
    materialize_expr_for_constant_evaluation(
        *this,
        expr,
        loc,
        false,
        note_specialization_use,
        active_exprs,
        active_symbols);
}

ConstEvalResult Collect::evaluate_constant_expression_demand(
    Expr* expr,
    ConstEvalMode mode,
    SrcLoc loc) const {
    materialize_specialization_uses_for_constant_evaluation(expr, loc);
    return evaluate_with_consteval_compat(expr, mode);
}

std::optional<int64_t> Collect::try_evaluate_constant_expression_demand(
    Expr* expr,
    ConstEvalMode mode,
    SrcLoc loc) const {
    ConstEvalResult result =
        evaluate_constant_expression_demand(expr, mode, loc);
    if (result.status == ConstEvalStatus::Constant &&
        result.int_value.has_value()) {
        return *result.int_value;
    }
    return std::nullopt;
}

QualType Collect::resolve_deferred_decltype_expr_type(
    const DecltypeExprType& decltype_type,
    QualType original_type,
    SrcLoc loc,
    DeferredTypeResolutionMode mode) {
    return resolve_decltype_expression_type(
        decltype_type.expr.get(),
        decltype_type.use_declared_type_rule,
        original_type,
        loc,
        mode);
}

QualType Collect::resolve_decltype_expression_type(
    Expr* expr,
    bool use_declared_type_rule,
    QualType original_type,
    SrcLoc loc,
    DeferredTypeResolutionMode mode) {
    if (!expr) {
        if (mode == DeferredTypeResolutionMode::Finalize) {
            report_error("cannot determine type of expression in decltype", loc);
        }
        return QualType();
    }

    std::unique_ptr<Expr> resolved_expr_owner;
    auto* stripped_expr = strip_implicit_casts(expr);
    auto apply_decltype_qualifiers = [&](QualType resolved_type) -> QualType {
        if (!resolved_type) {
            return resolved_type;
        }
        return QualType(
            resolved_type.get_shared(),
            static_cast<uint8_t>(
                original_type.get_qualifiers() |
                resolved_type.get_qualifiers()));
    };
    auto resolve_declval_argument_type =
        [&](const TemplateArgument& argument) -> QualType {
        if (argument.kind != TemplateArgumentKind::Type ||
            !argument.type) {
            return QualType();
        }
        QualType resolved_type = resolve_deferred_semantic_type_impl(
            argument.type,
            loc,
            mode);
        if (!resolved_type ||
            type_depends_on_template_parameters(resolved_type, ast_ctx_.get()) ||
            contains_deferred_semantic_type(resolved_type.get_shared())) {
            return QualType();
        }
        return resolved_type;
    };
    auto try_declval_call_type = [&](const Expr* candidate) -> QualType {
        candidate = strip_implicit_casts(const_cast<Expr*>(candidate));
        const UnresolvedLookupExpr* lookup = nullptr;
        if (auto* dependent_call = dyn_cast<DependentCallExpr>(candidate)) {
            lookup = dyn_cast<UnresolvedLookupExpr>(
                dependent_call->callee.get());
        } else if (auto* lookup_expr =
                       dyn_cast<UnresolvedLookupExpr>(candidate)) {
            lookup = lookup_expr;
        }
        if (!lookup ||
            (lookup->name != "declval" && lookup->name != "__declval") ||
            !lookup->explicit_template_arguments ||
            lookup->explicit_template_arguments->size() != 1) {
            return QualType();
        }
        QualType value_type = resolve_declval_argument_type(
            lookup->explicit_template_arguments->front());
        if (!value_type) {
            return QualType();
        }
        return make_reference_type(value_type, ReferenceKind::RValue);
    };
    auto try_declval_conditional_type = [&](const Expr* candidate) -> QualType {
        candidate = strip_implicit_casts(const_cast<Expr*>(candidate));
        auto* cond = dyn_cast<CondExpr>(candidate);
        if (!cond || !cond->false_expr) {
            return QualType();
        }
        const Expr* true_operand = cond->true_expr
            ? cond->true_expr.get()
            : cond->condition.get();
        QualType true_type = try_declval_call_type(true_operand);
        QualType false_type = try_declval_call_type(cond->false_expr.get());
        if (!true_type || !false_type) {
            return QualType();
        }
        if (true_type.equals_qualified(false_type)) {
            return true_type;
        }
        QualType true_object = remove_reference(true_type, ast_ctx_.get());
        QualType false_object = remove_reference(false_type, ast_ctx_.get());
        if (true_object.equals_qualified(false_object)) {
            return true_object;
        }
        if (collect_internal::is_arithmetic_adjacent(
                true_object,
                ast_ctx_.get()) &&
            collect_internal::is_arithmetic_adjacent(
                false_object,
                ast_ctx_.get())) {
            return usual_arithmetic_conversion_type(true_object, false_object);
        }
        return QualType();
    };
    if (QualType declval_type = try_declval_call_type(stripped_expr)) {
        return apply_decltype_qualifiers(declval_type);
    }
    if (QualType cond_type = try_declval_conditional_type(stripped_expr)) {
        return apply_decltype_qualifiers(cond_type);
    }
    if (decltype_expression_requires_deferred_resolution(stripped_expr)) {
        std::string clone_error;
        auto cloned_expr =
            clone_expr_tree(expr, ast_ctx_.get(), &clone_error);
        if (cloned_expr) {
            auto checkpoint = diag_engine_
                ? diag_engine_->checkpoint()
                : DiagnosticEngine::Checkpoint{};
            {
                UnevaluatedContextScope unevaluated_scope(
                    this,
                    "deferred decltype resolution");
                std::string resolution_error;
                QualType implicit_this_type =
                    session_.func_state_.current_function_is_cpp_member
                        ? session_.func_state_.current_function_cpp_this_type
                        : QualType();
                if (resolve_dependent_expr_after_substitution(
                        cloned_expr,
                        implicit_this_type,
                        &resolution_error)) {
                    realize_deferred_expr_type_after_substitution(
                        cloned_expr.get(),
                        mode == DeferredTypeResolutionMode::Finalize);
                }
            }
            if (mode == DeferredTypeResolutionMode::TryRealize &&
                diag_engine_) {
                diag_engine_->restore(checkpoint);
            }
            auto* resolved_stripped = strip_implicit_casts(cloned_expr.get());
            if (!decltype_expression_requires_deferred_resolution(
                    resolved_stripped)) {
                resolved_expr_owner = std::move(cloned_expr);
                stripped_expr = resolved_stripped;
            }
        }
    }
    if (decltype_expression_requires_deferred_resolution(stripped_expr)) {
        return original_type;
    }

    auto expr_type = stripped_expr ? stripped_expr->get_type() : QualType();
    expr_type = resolve_deferred_semantic_type_impl(expr_type, loc, mode);
    if (!expr_type) {
        if (mode == DeferredTypeResolutionMode::Finalize) {
            report_error("cannot determine type of expression in decltype", loc);
        }
        return QualType();
    }

    if (decltype_uses_declared_entity_rule(
            use_declared_type_rule,
            stripped_expr)) {
        QualType declared_type = expr_type;
        if (auto* member = dyn_cast<MemberExpr>(stripped_expr)) {
            if (member->declared_member_type) {
                declared_type = resolve_deferred_semantic_type_impl(
                    member->declared_member_type,
                    loc,
                    mode);
            }
        } else if (auto* member = dyn_cast<UnresolvedMemberExpr>(stripped_expr)) {
            if (member->declared_member_type) {
                declared_type = resolve_deferred_semantic_type_impl(
                    member->declared_member_type,
                    loc,
                    mode);
            }
        }
        if (!declared_type) {
            declared_type = expr_type;
        }
        return QualType(
            declared_type.get_shared(),
            static_cast<uint8_t>(
                original_type.get_qualifiers() | declared_type.get_qualifiers()));
    }

    switch (classify_value_category(stripped_expr)) {
        case ValueCategory::LValue:
            expr_type = make_reference_type(expr_type, ReferenceKind::LValue);
            break;
        case ValueCategory::XValue:
            expr_type = make_reference_type(expr_type, ReferenceKind::RValue);
            break;
        case ValueCategory::PRValue:
        case ValueCategory::Unknown:
            break;
    }

    return QualType(
        expr_type.get_shared(),
        static_cast<uint8_t>(
            original_type.get_qualifiers() | expr_type.get_qualifiers()));
}

ObjectDecl* Collect::try_instantiate_class_template_specialization(
    const ClassTemplateDecl* class_template,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc) {
    if (!diag_engine_) {
        return instantiate_class_template_specialization(
            class_template,
            arguments,
            loc);
    }
    auto checkpoint = diag_engine_->checkpoint();
    auto* specialization = instantiate_class_template_specialization(
        class_template,
        arguments,
        loc);
    diag_engine_->restore(checkpoint);
    return specialization;
}

QualType Collect::try_instantiate_alias_template_specialization(
    const AliasTemplateDecl* alias_template,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc) {
    if (!diag_engine_) {
        return instantiate_alias_template_specialization(
            alias_template,
            arguments,
            loc);
    }
    auto checkpoint = diag_engine_->checkpoint();
    auto specialization =
        instantiate_alias_template_specialization(alias_template, arguments, loc);
    diag_engine_->restore(checkpoint);
    return specialization;
}

void Collect::rewrite_deferred_template_arguments_in_place(
    std::vector<TemplateArgument>& arguments,
    SrcLoc loc,
    DeferredTypeResolutionMode mode) {
    for (auto& argument : arguments) {
        if (argument.kind == TemplateArgumentKind::Type) {
            argument.type = resolve_deferred_semantic_type_impl(
                argument.type,
                loc,
                mode);
            argument.is_dependent =
                type_depends_on_template_parameters(
                    argument.type,
                    ast_ctx_.get());
        } else if (argument.kind == TemplateArgumentKind::Value) {
            argument.value_type = resolve_deferred_semantic_type_impl(
                argument.value_type,
                loc,
                mode);
            if (!argument.is_dependent || !argument.value_expr) {
                continue;
            }

            std::string clone_error;
            auto cloned_expr =
                clone_expr_tree(argument.value_expr.get(), ast_ctx_.get(), &clone_error);
            if (!cloned_expr) {
                continue;
            }
            std::string resolve_error;
            if (!resolve_dependent_expr_after_substitution(
                    cloned_expr,
                    QualType(),
                    &resolve_error)) {
                continue;
            }

            bool still_dependent =
                expression_depends_on_template_parameters(cloned_expr.get()) ||
                type_depends_on_template_parameters(
                    cloned_expr->get_type(),
                    ast_ctx_.get()) ||
                type_depends_on_template_parameters(
                    argument.value_type,
                    ast_ctx_.get());
            if (still_dependent) {
                argument.value_expr =
                    std::shared_ptr<Expr>(cloned_expr.release());
                argument.is_dependent = true;
                continue;
            }

            ConstEvalResult eval = evaluate_with_consteval_compat(
                cloned_expr.get(),
                ConstEvalMode::cpp_non_type_template_argument());
            if (eval.status == ConstEvalStatus::Constant &&
                eval.value.has_value() &&
                eval.value->kind != ConstValueKind::Invalid) {
                std::shared_ptr<Expr> concrete_expr = nullptr;
                if (eval.value->kind == ConstValueKind::Object) {
                    concrete_expr = std::shared_ptr<Expr>(cloned_expr.release());
                }
                argument = TemplateArgument::value_argument(
                    argument.value_type,
                    *eval.value,
                    {},
                    std::move(concrete_expr));
            }
        }
    }
}

QualType Collect::resolve_deferred_template_specialization_type(
    TemplateSpecializationType& specialization,
    QualType original_type,
    SrcLoc loc,
    DeferredTypeResolutionMode mode) {
    rewrite_deferred_template_arguments_in_place(
        specialization.arguments,
        loc,
        mode);
    query_publish_template_specialization_resolved_type(
        original_type,
        nullptr);
    specialization.is_dependent = false;
    for (const auto& argument : specialization.arguments) {
        if (template_argument_depends_on_template_parameters(
                argument,
                ast_ctx_.get())) {
            specialization.is_dependent = true;
            break;
        }
    }
    auto resolved_type =
        query_lookup_template_specialization_resolved_type(&specialization);
    if (specialization.is_dependent || resolved_type) {
        return original_type;
    }

    auto* class_template =
        dyn_cast<ClassTemplateDecl>(specialization.primary_template);
    if (class_template) {
        auto* specialization_decl =
            mode == DeferredTypeResolutionMode::Finalize
                ? instantiate_class_template_specialization(
                      class_template,
                      specialization.arguments,
                      loc)
                : try_instantiate_class_template_specialization(
                      class_template,
                      specialization.arguments,
                      loc);
        if (specialization_decl && specialization_decl->get_record_type()) {
            query_publish_template_specialization_resolved_type(
                original_type,
                QualType(specialization_decl->get_record_type()));
            return original_type;
        }
        return QualType();
    }

    auto* alias_template =
        dyn_cast<AliasTemplateDecl>(specialization.primary_template);
    if (!alias_template) {
        return original_type;
    }

    auto resolved_alias_type =
        mode == DeferredTypeResolutionMode::Finalize
            ? instantiate_alias_template_specialization(
                  alias_template,
                  specialization.arguments,
                  loc)
            : try_instantiate_alias_template_specialization(
                  alias_template,
                  specialization.arguments,
                  loc);
    resolved_alias_type =
        resolve_deferred_semantic_type_impl(resolved_alias_type, loc, mode);
    if (resolved_alias_type) {
        query_publish_template_specialization_resolved_type(
            original_type,
            resolved_alias_type);
        return original_type;
    }
    return QualType();
}

QualType Collect::lookup_deferred_dependent_name_type(
    const DependentNameType& dependent_name,
    SrcLoc loc,
    bool* matched_nested_template) {
    bool has_template_argument_list =
        dependent_name.requires_template_keyword ||
        !dependent_name.template_arguments.empty();
    if (has_template_argument_list) {
        return collect_lookup_record_nested_template_type(
            dependent_name.qualifier_type,
            dependent_name.member_name,
            dependent_name.template_arguments,
            loc,
            matched_nested_template);
    }
    if (matched_nested_template) {
        *matched_nested_template = false;
    }
    return collect_lookup_record_nested_type(
        dependent_name.qualifier_type,
        dependent_name.member_name);
}

QualType Collect::handle_unresolved_dependent_name_type_lookup(
    const DependentNameType& dependent_name,
    QualType original_type,
    SrcLoc loc,
    bool matched_nested_template,
    DeferredTypeResolutionMode mode) const {
    if (type_depends_on_template_parameters(
            dependent_name.qualifier_type,
            ast_ctx_.get()) ||
        dependent_name.is_current_instantiation) {
        return original_type;
    }
    if (matched_nested_template) {
        return QualType();
    }
    if (mode == DeferredTypeResolutionMode::Finalize) {
        report_error(
            "'" + dependent_name.qualifier_type.to_string() + "::" +
                dependent_name.member_name +
                "' does not name a type",
            loc);
    }
    return QualType();
}

QualType Collect::resolve_deferred_dependent_name_type(
    DependentNameType& dependent_name,
    QualType original_type,
    SrcLoc loc,
    DeferredTypeResolutionMode mode) {
    dependent_name.qualifier_type = resolve_deferred_semantic_type_impl(
        dependent_name.qualifier_type,
        loc,
        mode);
    rewrite_deferred_template_arguments_in_place(
        dependent_name.template_arguments,
        loc,
        mode);
    if (dependent_name.is_current_instantiation &&
        dependent_name.qualifier_type &&
        !type_depends_on_template_parameters(
            dependent_name.qualifier_type,
            ast_ctx_.get()) &&
        !contains_deferred_semantic_type(
            dependent_name.qualifier_type.get_shared())) {
        dependent_name.is_current_instantiation = false;
    }
    query_publish_dependent_name_resolved_type(original_type, nullptr);
    auto resolved_type =
        query_lookup_dependent_name_resolved_type(&dependent_name);
    if (resolved_type) {
        auto rewritten_resolved_type =
            resolve_deferred_semantic_type_impl(
                resolved_type,
                loc,
                mode);
        query_publish_dependent_name_resolved_type(
            original_type,
            rewritten_resolved_type);
        return original_type;
    }

    bool matched_nested_template = false;
    auto resolved_nested_type = lookup_deferred_dependent_name_type(
        dependent_name,
        loc,
        &matched_nested_template);
    if (!resolved_nested_type) {
        return handle_unresolved_dependent_name_type_lookup(
            dependent_name,
            original_type,
            loc,
            matched_nested_template,
            mode);
    }

    resolved_nested_type = resolve_deferred_semantic_type_impl(
        resolved_nested_type,
        loc,
        mode);
    query_publish_dependent_name_resolved_type(
        original_type,
        resolved_nested_type);
    return original_type;
}

QualType Collect::try_realize_deferred_semantic_type(QualType type) {
    return resolve_deferred_semantic_type_impl(
        type,
        SrcLoc(),
        DeferredTypeResolutionMode::TryRealize);
}

QualType Collect::finalize_deferred_semantic_type(QualType type, SrcLoc loc) {
    return resolve_deferred_semantic_type_impl(
        type,
        loc,
        DeferredTypeResolutionMode::Finalize);
}

QualType Collect::resolve_deferred_semantic_type_impl(
    QualType type,
    SrcLoc loc,
    DeferredTypeResolutionMode mode) {
    if (!type) {
        return type;
    }

    auto raw = type.get_shared();
    if (!raw) {
        return type;
    }

    if (auto typedef_type = dyn_cast_shared<TypedefType>(raw)) {
        typedef_type->underlying_type = resolve_deferred_semantic_type_impl(
            typedef_type->underlying_type,
            loc,
            mode);
        if (!typedef_type->underlying_type) {
            return QualType();
        }
        return type;
    }

    if (auto* typeof_type = dyn_cast<TypeofExprType>(raw.get())) {
        auto expr_type = typeof_type->expr ? typeof_type->expr->get_type() : QualType();
        expr_type = resolve_deferred_semantic_type_impl(expr_type, loc, mode);
        if (!expr_type) {
            if (mode == DeferredTypeResolutionMode::Finalize) {
                report_error("cannot determine type of expression in typeof", loc);
            }
            return QualType();
        }
        return QualType(
            expr_type.get_shared(),
            static_cast<uint8_t>(type.get_qualifiers() | expr_type.get_qualifiers()));
    }

    if (auto* decltype_type = dyn_cast<DecltypeExprType>(raw.get())) {
        return resolve_deferred_decltype_expr_type(
            *decltype_type,
            type,
            loc,
            mode);
    }

    if (auto* transform_type = dyn_cast<BuiltinTypeTransformType>(raw.get())) {
        auto operand_type = resolve_deferred_semantic_type_impl(
            transform_type->operand_type,
            loc,
            mode);
        if (!operand_type) {
            if (mode == DeferredTypeResolutionMode::Finalize) {
                report_error(
                    "cannot determine operand type of builtin type transform",
                    loc);
            }
            return QualType();
        }

        transform_type->operand_type = operand_type;
        if (type_depends_on_template_parameters(operand_type, ast_ctx_.get())) {
            return type;
        }

        auto transformed =
            apply_builtin_type_transform(
                transform_type->transform_kind,
                operand_type,
                ast_ctx_.get());
        if (!transformed) {
            if (mode == DeferredTypeResolutionMode::Finalize) {
                report_error(
                    "cannot resolve builtin type transform",
                    loc);
            }
            return QualType();
        }
        return QualType(
            transformed.get_shared(),
            static_cast<uint8_t>(
                type.get_qualifiers() | transformed.get_qualifiers()));
    }

    if (auto* pack_element_type =
            dyn_cast<BuiltinTypePackElementType>(raw.get())) {
        for (auto& argument : pack_element_type->arguments) {
            if (argument.kind == TemplateArgumentKind::Type) {
                argument.type =
                    resolve_deferred_semantic_type_impl(argument.type, loc, mode);
                if (!argument.type) {
                    if (mode == DeferredTypeResolutionMode::Finalize) {
                        report_error(
                            "cannot determine type argument of __type_pack_element",
                            loc);
                    }
                    return QualType();
                }
            } else if (argument.kind == TemplateArgumentKind::Value) {
                argument.value_type = resolve_deferred_semantic_type_impl(
                    argument.value_type,
                    loc,
                    mode);
            }
        }

        if (template_arguments_contain_dependency(
                pack_element_type->arguments,
                ast_ctx_.get())) {
            return type;
        }

        auto selected_type = apply_builtin_type_pack_element(
            pack_element_type->arguments,
            ast_ctx_.get());
        if (!selected_type) {
            if (mode == DeferredTypeResolutionMode::Finalize) {
                report_error("cannot resolve __type_pack_element", loc);
            }
            return QualType();
        }
        return QualType(
            selected_type.get_shared(),
            static_cast<uint8_t>(
                type.get_qualifiers() | selected_type.get_qualifiers()));
    }

    if (auto object_type = dyn_cast_shared<ObjectType>(raw)) {
        const auto* primary_template =
            object_type->get_primary_class_template();
        if (!primary_template) {
            return type;
        }

        auto rewritten_arguments =
            object_type->get_template_specialization_arguments();
        rewrite_deferred_template_arguments_in_place(
            rewritten_arguments,
            loc,
            mode);
        if (template_arguments_contain_dependency(
                rewritten_arguments,
                ast_ctx_.get())) {
            return type;
        }

        ObjectDecl* specialization_decl =
            mode == DeferredTypeResolutionMode::Finalize
                ? instantiate_class_template_specialization(
                      primary_template,
                      rewritten_arguments,
                      loc)
                : try_instantiate_class_template_specialization(
                      primary_template,
                      rewritten_arguments,
                      loc);
        if (specialization_decl && specialization_decl->get_record_type()) {
            return QualType(
                specialization_decl->get_record_type(),
                type.get_qualifiers());
        }
        return type;
    }

    if (auto specialization = dyn_cast_shared<TemplateSpecializationType>(raw)) {
        return resolve_deferred_template_specialization_type(
            *specialization,
            type,
            loc,
            mode);
    }

    if (auto dependent_name = dyn_cast_shared<DependentNameType>(raw)) {
        return resolve_deferred_dependent_name_type(
            *dependent_name,
            type,
            loc,
            mode);
    }

    if (auto ptr = dyn_cast_shared<PointerType>(raw)) {
        ptr->pointed_type = resolve_deferred_semantic_type_impl(
            ptr->pointed_type,
            loc,
            mode);
        return type;
    }
    if (auto ref = dyn_cast_shared<ReferenceType>(raw)) {
        ref->referred_type = resolve_deferred_semantic_type_impl(
            ref->referred_type,
            loc,
            mode);
        return type;
    }
    if (auto mem_ptr = dyn_cast_shared<MemberPointerType>(raw)) {
        mem_ptr->class_type = resolve_deferred_semantic_type_impl(
            mem_ptr->class_type,
            loc,
            mode);
        mem_ptr->member_type = resolve_deferred_semantic_type_impl(
            mem_ptr->member_type,
            loc,
            mode);
        return type;
    }
    if (auto blk = dyn_cast_shared<BlockPointerType>(raw)) {
        blk->pointed_type = resolve_deferred_semantic_type_impl(
            blk->pointed_type,
            loc,
            mode);
        return type;
    }
    if (auto arr = dyn_cast_shared<ArrayType>(raw)) {
        arr->element_type = resolve_deferred_semantic_type_impl(
            arr->element_type,
            loc,
            mode);
        return type;
    }
    if (auto func = dyn_cast_shared<FunctionType>(raw)) {
        func->ret_type = resolve_deferred_semantic_type_impl(
            func->ret_type,
            loc,
            mode);
        for (auto& parameter : func->parameters) {
            parameter = resolve_deferred_semantic_type_impl(parameter, loc, mode);
        }
        return type;
    }
    if (auto vec = dyn_cast_shared<VectorType>(raw)) {
        vec->element_type = resolve_deferred_semantic_type_impl(
            vec->element_type,
            loc,
            mode);
        return type;
    }

    return type;
}
