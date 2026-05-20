#include "collect_templates_internal.h"
#include "collect_decl_internal.h"
#include "../helpers/auto_type_utils.h"

namespace template_sema_internal {
QualType implicit_this_type_for_specialized_function(const FuncDecl* decl);

namespace {

void strip_redundant_specialization_casts(std::unique_ptr<Expr>& expr) {
    if (!expr) {
        return;
    }
    while (auto* implicit_cast = dyn_cast<ImplicitCast>(expr.get())) {
        if (!implicit_cast->expr) {
            return;
        }
        auto source_type = implicit_cast->expr->get_type();
        auto target_type = implicit_cast->get_type();
        bool redundant_same_type_cast =
            (implicit_cast->kind == ImplicitCastTypes::ARITH_CAST ||
             implicit_cast->kind == ImplicitCastTypes::RAW_CAST) &&
            source_type &&
            target_type &&
            source_type.equals_unqualified(target_type);
        if (!redundant_same_type_cast) {
            return;
        }
        auto owned_cast = std::unique_ptr<ImplicitCast>(
            static_cast<ImplicitCast*>(expr.release()));
        expr = std::move(owned_cast->expr);
    }
}

void strip_stale_object_initializer_cast(std::unique_ptr<Expr>& expr,
                                         QualType target_type) {
    if (!expr || !target_type ||
        canonical_type_kind(target_type) != TypeKind::Object) {
        return;
    }

    while (auto* implicit_cast = dyn_cast<ImplicitCast>(expr.get())) {
        if (!implicit_cast->expr) {
            return;
        }
        bool object_target_cast =
            (implicit_cast->kind == ImplicitCastTypes::ARITH_CAST ||
             implicit_cast->kind == ImplicitCastTypes::RAW_CAST) &&
            implicit_cast->get_type() &&
            (implicit_cast->get_type().equals_unqualified(target_type) ||
             types_equivalent_after_template_argument_canonicalization(
                 implicit_cast->get_type(),
                 target_type,
                 nullptr,
                 /*ignore_top_level_qualifiers=*/true));
        if (!object_target_cast) {
            return;
        }

        auto source_type = implicit_cast->expr->get_type();
        if (source_type &&
            (source_type.equals_unqualified(target_type) ||
             types_equivalent_after_template_argument_canonicalization(
                 source_type,
                 target_type,
                 nullptr,
                 /*ignore_top_level_qualifiers=*/true))) {
            return;
        }

        auto owned_cast = std::unique_ptr<ImplicitCast>(
            static_cast<ImplicitCast*>(expr.release()));
        expr = std::move(owned_cast->expr);
    }
}

QualType specialized_ctor_owner_type(const CppConstructorDecl* ctor_decl) {
    if (!ctor_decl) {
        return QualType();
    }

    if (QualType owner_type = get_func_decl_owner_record_type(ctor_decl)) {
        return owner_type;
    }

    QualType this_type = implicit_this_type_for_specialized_function(ctor_decl);
    auto this_ptr_type = desugar_type(this_type).as_shared<PointerType>();
    if (!this_ptr_type) {
        return QualType();
    }
    return this_ptr_type->pointed_type;
}

QualType lookup_ctor_initializer_target_type(const CppConstructorDecl* ctor_decl,
                                             const CppCtorInitializer& initializer) {
    if (!ctor_decl) {
        return QualType();
    }

    if (initializer.is_delegating_initializer) {
        return specialized_ctor_owner_type(ctor_decl);
    }

    if (!initializer.is_base_initializer) {
        auto* member_expr = dyn_cast<MemberExpr>(initializer.member_expr.get());
        return member_expr ? member_expr->member_type : QualType();
    }

    QualType owner_type = specialized_ctor_owner_type(ctor_decl);
    auto owner_record_type = desugar_type(owner_type).as_shared<ObjectType>();
    const auto* owner_decl =
        owner_record_type ? dyn_cast<ObjectDecl>(owner_record_type->get_decl())
                          : nullptr;
    const auto* owner_state =
        owner_decl ? record_semantics_cache_lookup(owner_decl) : nullptr;
    if (!owner_state) {
        return QualType();
    }

    for (const auto& base : owner_state->bases) {
        if (base.name == initializer.member_name) {
            return base.type;
        }
    }
    for (const auto& virtual_base : owner_state->virtual_bases) {
        if (virtual_base.name == initializer.member_name) {
            return virtual_base.type;
        }
    }
    return QualType();
}

LookupNamespace using_import_lookup_namespace(
    CppUsingImportNamespace lookup_namespace) {
    return lookup_namespace == CppUsingImportNamespace::Tag
        ? LookupNamespace::Tag
        : LookupNamespace::Ordinary;
}

void bind_imported_template_decl(Collect& collect,
                                 const CppUsingDeclarationDecl::ImportedTemplate& imported) {
    collect.collect_bind_template_decl(
        imported.name,
        imported.decl,
        using_import_lookup_namespace(imported.lookup_namespace));
}

void bind_stored_ordinary_using_imports(
    Collect& collect,
    const std::vector<CppUsingDeclarationDecl::ImportedSymbol>& ordinary_symbols,
    const std::vector<CppUsingDeclarationDecl::ImportedTemplate>& template_decls) {
    for (const auto& imported : ordinary_symbols) {
        collect.collect_bind_symbol_in_current_scope(
            imported.name,
            imported.symbol);
    }
    for (const auto& imported : template_decls) {
        if (imported.lookup_namespace != CppUsingImportNamespace::Ordinary) {
            continue;
        }
        bind_imported_template_decl(collect, imported);
    }
}

void bind_stored_tag_using_imports(
    Collect& collect,
    const std::vector<CppUsingDeclarationDecl::ImportedTag>& tag_decls,
    const std::vector<CppUsingDeclarationDecl::ImportedTemplate>& template_decls) {
    for (const auto& imported : tag_decls) {
        collect.collect_add_tag_decl(imported.name, imported.decl);
    }
    for (const auto& imported : template_decls) {
        if (imported.lookup_namespace != CppUsingImportNamespace::Tag) {
            continue;
        }
        bind_imported_template_decl(collect, imported);
    }
}

void bind_template_binding_from_using_lookup(Collect& collect,
                                             const std::string& name,
                                             const DeclBinding* binding,
                                             LookupNamespace lookup_namespace) {
    if (!binding) {
        return;
    }
    if (binding->template_decl) {
        collect.collect_bind_template_decl(
            name,
            binding->template_decl,
            lookup_namespace);
    }
    for (const auto* template_candidate :
         binding->template_overload_candidates) {
        collect.collect_bind_template_decl(
            name,
            template_candidate,
            lookup_namespace);
    }
}

bool replay_ordinary_using_target(
    Collect& collect,
    const CppUsingDeclarationDecl::ReplayTarget& target) {
    if (!target.target_context) {
        return false;
    }
    auto lookup = LookupEngine::lookup_qualified(
        target.name,
        target.target_context,
        LookupNamespace::Ordinary);
    if (lookup.status != LookupEngine::QualifiedLookupStatus::Found ||
        !lookup.binding) {
        return false;
    }

    const auto* binding = lookup.binding;
    if (binding->has_overload_set()) {
        for (const auto& candidate : binding->overload_candidates) {
            collect.collect_bind_symbol_in_current_scope(
                target.name,
                candidate);
        }
    } else {
        collect.collect_bind_symbol_in_current_scope(
            target.name,
            lookup.symbol ? lookup.symbol : binding->symbol);
    }
    bind_template_binding_from_using_lookup(
        collect,
        target.name,
        binding,
        LookupNamespace::Ordinary);
    return true;
}

bool replay_tag_using_target(
    Collect& collect,
    const CppUsingDeclarationDecl::ReplayTarget& target) {
    if (!target.target_context) {
        return false;
    }
    auto lookup = LookupEngine::lookup_qualified(
        target.name,
        target.target_context,
        LookupNamespace::Tag);
    if (lookup.status != LookupEngine::QualifiedLookupStatus::Found ||
        !lookup.binding) {
        return false;
    }

    if (auto* tag_decl = dyn_cast<TagDecl>(lookup.binding->ast_decl)) {
        collect.collect_add_tag_decl(
            target.name,
            const_cast<TagDecl*>(tag_decl));
    }
    bind_template_binding_from_using_lookup(
        collect,
        target.name,
        lookup.binding,
        LookupNamespace::Tag);
    return true;
}

void replay_or_bind_stored_using_target(
    Collect& collect,
    const CppUsingDeclarationDecl::ReplayTarget& target) {
    if (target.import_tag && !replay_tag_using_target(collect, target)) {
        bind_stored_tag_using_imports(
            collect,
            target.tag_decls,
            target.template_decls);
    }
    if (target.import_ordinary &&
        !replay_ordinary_using_target(collect, target)) {
        bind_stored_ordinary_using_imports(
            collect,
            target.ordinary_symbols,
            target.template_decls);
    }
}

bool rebuild_specialized_ctor_initializer_expression(
    Collect& collect,
    CppConstructorDecl* ctor_decl,
    CppCtorInitializer& initializer,
    std::string* error_out) {
    if (!initializer.init_expr) {
        return true;
    }

    strip_redundant_specialization_casts(initializer.member_expr);
    strip_redundant_specialization_casts(initializer.init_expr);

    auto* init_list = dyn_cast<InitListExpr>(initializer.init_expr.get());

    QualType target_type = lookup_ctor_initializer_target_type(ctor_decl, initializer);
    if (!target_type) {
        if (error_out && error_out->empty()) {
            *error_out =
                initializer.is_base_initializer
                    ? "failed to resolve constructor base initializer target type"
                    : "failed to resolve constructor member initializer target type";
        }
        return false;
    }

    bool has_designators = false;
    if (init_list) {
        for (const auto& element : init_list->elements) {
            if (!element.designators.empty()) {
                has_designators = true;
                break;
            }
        }
    }

    std::unique_ptr<Expr> rebuilt_init;
    if (init_list && !has_designators &&
        (init_list->is_paren_init || init_list->elements.empty() ||
         canonical_type_kind(target_type) == TypeKind::Object)) {
        auto owned_list = std::unique_ptr<InitListExpr>(
            static_cast<InitListExpr*>(initializer.init_expr.release()));
        std::vector<std::unique_ptr<Expr>> init_args;
        init_args.reserve(owned_list->elements.size());
        for (auto& element : owned_list->elements) {
            init_args.push_back(std::move(element.value));
        }
        rebuilt_init = collect.collect_member_initializer_expression(
            std::move(init_args),
            target_type,
            !owned_list->is_paren_init,
            initializer.location,
            initializer.is_base_initializer);
    } else if (init_list) {
        rebuilt_init = collect.collect_member_initializer_expression(
            std::move(initializer.init_expr),
            target_type,
            initializer.location);
    } else if (canonical_type_kind(target_type) == TypeKind::Object &&
               !isa<CppConstructExpr>(initializer.init_expr.get())) {
        strip_stale_object_initializer_cast(initializer.init_expr, target_type);
        std::vector<std::unique_ptr<Expr>> init_args;
        init_args.push_back(std::move(initializer.init_expr));
        rebuilt_init = collect.collect_member_initializer_expression(
            std::move(init_args),
            target_type,
            initializer.is_list_init,
            initializer.location,
            initializer.is_base_initializer);
    } else {
        return true;
    }

    if (!rebuilt_init) {
        if (error_out && error_out->empty()) {
            *error_out =
                initializer.is_base_initializer
                    ? "failed to finalize constructor base initializer after template substitution"
                    : "failed to finalize constructor member initializer after template substitution";
        }
        return false;
    }

    initializer.init_expr = std::move(rebuilt_init);
    return true;
}

bool resolve_specialized_condition_after_substitution(
    Collect& collect,
    std::unique_ptr<Expr>& condition,
    const std::string& stmt_name,
    std::string* error_out) {
    if (!condition) {
        return true;
    }

    strip_redundant_specialization_casts(condition);
    auto cpp_this_context = collect.collect_current_cpp_this_context();
    if (!collect.resolve_dependent_expr_after_substitution(
            condition,
            cpp_this_context.this_type,
            error_out)) {
        if (error_out && error_out->empty()) {
            *error_out =
                "failed to resolve dependent " + stmt_name +
                " condition after template substitution";
        }
        return false;
    }
    return true;
}

bool finalize_specialized_condition_expression(
    Collect& collect,
    std::unique_ptr<Expr>& condition,
    SrcLoc loc,
    const std::string& stmt_name,
    std::string* error_out) {
    if (!resolve_specialized_condition_after_substitution(
            collect,
            condition,
            stmt_name,
            error_out)) {
        return false;
    }
    if (!condition) {
        return true;
    }

    condition = collect.collect_condition_expression(
        std::move(condition),
        loc,
        stmt_name);
    if (!condition) {
        if (error_out && error_out->empty()) {
            *error_out =
                "failed to finalize " + stmt_name +
                " condition after template substitution";
        }
        return false;
    }
    return true;
}

bool finalize_specialized_switch_condition_expression(
    Collect& collect,
    std::unique_ptr<Expr>& condition,
    SrcLoc loc,
    std::string* error_out) {
    if (!resolve_specialized_condition_after_substitution(
            collect,
            condition,
            "switch",
            error_out)) {
        return false;
    }
    if (!condition) {
        return true;
    }

    condition = collect.collect_switch_condition(std::move(condition), loc);
    if (!condition) {
        if (error_out && error_out->empty()) {
            *error_out = "failed to finalize switch condition after template substitution";
        }
        return false;
    }
    return true;
}

bool finalize_specialized_control_condition_declaration(
    Collect& collect,
    ControlCondition& condition,
    QualType expected_return_type,
    std::string* error_out) {
    if (!condition.declaration) {
        return true;
    }
    return finalize_specialized_stmt_semantics(
        collect,
        condition.declaration,
        expected_return_type,
        error_out);
}

} // namespace

QualType implicit_this_type_for_specialized_function(const FuncDecl* decl) {
    if (!decl || !decl->type) {
        return QualType();
    }
    if (auto* method = dyn_cast<CppMethodDecl>(decl);
        method && method->storage_class == StorageClass::STATIC) {
        return QualType();
    }
    auto function_type =
        desugar_type(QualType(decl->type)).as_shared<FunctionType>();
    if (!function_type || function_type->parameters.empty()) {
        return QualType();
    }
    return function_type->parameters.front();
}

bool finalize_specialized_decl_semantics(Collect& collect,
                                         std::unique_ptr<Decl>& decl,
                                         std::string* error_out) {
    if (!decl) {
        return true;
    }

    switch (decl->get_kind()) {
        case DeclKind::CppUsingDeclarationDecl: {
            const auto* using_decl =
                static_cast<const CppUsingDeclarationDecl*>(decl.get());
            if (!using_decl->replay_targets.empty()) {
                for (const auto& target : using_decl->replay_targets) {
                    replay_or_bind_stored_using_target(collect, target);
                }
                return true;
            }

            bind_stored_tag_using_imports(
                collect,
                using_decl->tag_decls,
                using_decl->template_decls);
            bind_stored_ordinary_using_imports(
                collect,
                using_decl->ordinary_symbols,
                using_decl->template_decls);
            return true;
        }
        case DeclKind::VariableDecl: {
            auto* variable = static_cast<VariableDecl*>(decl.get());
            if (!variable->init || variable->get_cpp_construct_init()) {
                return true;
            }
            if (variable->original_type &&
                auto_type_utils::auto_type_flavors_in(
                    variable->original_type.get_shared()) != 0) {
                variable->type = variable->original_type;
                if (variable->sym) {
                    variable->sym->type = variable->type;
                }
            }
            strip_redundant_specialization_casts(variable->init);
            if (!collect.resolve_dependent_expr_after_substitution(
                    variable->init,
                    QualType(),
                    error_out)) {
                if (error_out && error_out->empty()) {
                    *error_out =
                        "failed to resolve variable initializer after template substitution";
                }
                return false;
            }
            variable->type =
                collect_decl_internal::clone_top_level_incomplete_array(
                    variable->type);
            if (variable->sym) {
                variable->sym->type = variable->type;
            }
            collect.collect_resolve_auto_variable_type_from_expr(
                variable->type,
                variable->init.get(),
                variable->sym,
                variable->name,
                variable->location);
            auto rebuilt_init = collect.collect_process_initializer_for_type(
                std::move(variable->init),
                variable->type,
                variable->location);
            if (!rebuilt_init) {
                if (error_out && error_out->empty()) {
                    *error_out =
                        "failed to finalize variable initializer after template substitution";
                }
                return false;
            }
            variable->init = std::move(rebuilt_init);
            if (variable->type &&
                canonical_type_kind(variable->type) == TypeKind::Array) {
                auto arr_type =
                    desugar_type(variable->type).as_shared<ArrayType>();
                if (arr_type &&
                    arr_type->size_kind == ArraySizeKind::Incomplete) {
                    if (auto* init_node = dyn_cast<InitListExpr>(variable->init.get())) {
                        arr_type->size_kind = ArraySizeKind::Constant;
                        if (!init_node->mappings.empty()) {
                            arr_type->size = init_node->mappings.rbegin()->first + 1;
                        } else {
                            arr_type->size = 0;
                        }
                    } else if (auto* str_lit =
                                   dyn_cast<StringLiteral>(variable->init.get())) {
                        auto str_lit_type = str_lit->ctype.as_shared<ArrayType>();
                        if (str_lit_type) {
                            arr_type->size_kind = ArraySizeKind::Constant;
                            arr_type->size = str_lit_type->size;
                        }
                    }
                }
            }
            return true;
        }
        case DeclKind::FieldDecl: {
            auto* field = static_cast<FieldDecl*>(decl.get());
            if (!field->default_member_initializer) {
                return true;
            }
            strip_redundant_specialization_casts(
                field->default_member_initializer);
            if (!collect.resolve_dependent_expr_after_substitution(
                    field->default_member_initializer,
                    QualType(),
                    error_out)) {
                if (error_out && error_out->empty()) {
                    *error_out =
                        "failed to resolve field default member initializer after template substitution";
                }
                return false;
            }
            field->type =
                collect_decl_internal::clone_top_level_incomplete_array(
                    field->type);
            auto rebuilt_init = collect.collect_member_initializer_expression(
                std::move(field->default_member_initializer),
                field->type,
                field->location);
            if (!rebuilt_init) {
                if (error_out && error_out->empty()) {
                    *error_out =
                        "failed to finalize field default member initializer after template substitution";
                }
                return false;
            }
            field->default_member_initializer = std::move(rebuilt_init);
            return true;
        }
        case DeclKind::StaticAssertDecl: {
            auto owned_static_assert = std::unique_ptr<StaticAssertDecl>(
                static_cast<StaticAssertDecl*>(decl.release()));
            strip_redundant_specialization_casts(
                owned_static_assert->condition);
            auto rebuilt = collect.collect_static_assert_declaration(
                std::move(owned_static_assert->condition),
                owned_static_assert->message,
                owned_static_assert->has_message != 0,
                owned_static_assert->location);
            if (!rebuilt) {
                if (error_out && error_out->empty()) {
                    *error_out =
                        "failed to finalize static_assert after template substitution";
                }
                return false;
            }
            decl = std::move(rebuilt);
            return true;
        }
        default:
            return true;
    }
}

bool finalize_specialized_stmt_semantics(Collect& collect,
                                         std::unique_ptr<Stmt>& stmt,
                                         QualType expected_return_type,
                                         std::string* error_out) {
    if (!stmt) {
        return true;
    }

    switch (stmt->get_kind()) {
        case StmtKind::CompoundStmt: {
            auto* compound = static_cast<CompoundStmt*>(stmt.get());
            for (auto& child : compound->statements) {
                if (!finalize_specialized_stmt_semantics(
                        collect,
                        child,
                        expected_return_type,
                        error_out)) {
                    return false;
                }
            }
            return true;
        }
        case StmtKind::Decl2Stmt: {
            auto* decl_stmt = static_cast<Decl2Stmt*>(stmt.get());
            for (auto& decl : decl_stmt->decls) {
                if (!finalize_specialized_decl_semantics(
                        collect,
                        decl,
                        error_out)) {
                    return false;
                }
            }
            return true;
        }
        case StmtKind::ReturnStmt: {
            auto owned_return = std::unique_ptr<ReturnStmt>(
                static_cast<ReturnStmt*>(stmt.release()));
            strip_redundant_specialization_casts(owned_return->expression);
            auto cpp_this_context = collect.collect_current_cpp_this_context();
            if (owned_return->expression &&
                !collect.resolve_dependent_expr_after_substitution(
                    owned_return->expression,
                    cpp_this_context.this_type,
                    error_out)) {
                if (error_out && error_out->empty()) {
                    *error_out =
                        "failed to resolve dependent return expression after template substitution";
                }
                return false;
            }
            auto rebuilt = collect.collect_return_statement(
                std::move(owned_return->expression),
                owned_return->location,
                expected_return_type);
            if (!rebuilt) {
                if (error_out && error_out->empty()) {
                    *error_out =
                        "failed to finalize return statement after template substitution";
                }
                return false;
            }
            stmt = std::move(rebuilt);
            return true;
        }
        case StmtKind::IfStmt: {
            auto* if_stmt = static_cast<IfStmt*>(stmt.get());
            if (!finalize_specialized_stmt_semantics(
                    collect,
                    if_stmt->init_stmt,
                    expected_return_type,
                    error_out)) {
                return false;
            }
            if (!finalize_specialized_control_condition_declaration(
                    collect,
                    if_stmt->condition,
                    expected_return_type,
                    error_out)) {
                return false;
            }
            if (if_stmt->condition.expression) {
                if (!resolve_specialized_condition_after_substitution(
                        collect,
                        if_stmt->condition.expression,
                        "if",
                        error_out)) {
                    return false;
                }
                auto condition_info = collect.collect_if_condition(
                    std::move(if_stmt->condition.expression),
                    if_stmt->statement_kind,
                    if_stmt->location);
                if_stmt->condition.expression = std::move(condition_info.condition);
                if (!if_stmt->condition.expression) {
                    if (error_out && error_out->empty()) {
                        *error_out =
                            "failed to finalize if condition after template substitution";
                    }
                    return false;
                }
                if_stmt->constexpr_condition_value =
                    condition_info.constexpr_value;
            }
            if (if_stmt->statement_kind == IfStatementKind::Constexpr) {
                if (if_stmt->constexpr_condition_value.has_value()) {
                    auto& selected_stmt = *if_stmt->constexpr_condition_value
                        ? if_stmt->then_stmt
                        : if_stmt->else_stmt;
                    return finalize_specialized_stmt_semantics(
                        collect,
                        selected_stmt,
                        expected_return_type,
                        error_out);
                }

                struct BranchGuard {
                    Collect& collect;
                    explicit BranchGuard(Collect& collect) : collect(collect) {
                        collect.collect_enter_constexpr_if_branch(
                            CppConstexprIfBranchState::Deferred);
                    }
                    ~BranchGuard() {
                        collect.collect_leave_constexpr_if_branch();
                    }
                };
                {
                    BranchGuard guard(collect);
                    if (!finalize_specialized_stmt_semantics(
                            collect,
                            if_stmt->then_stmt,
                            expected_return_type,
                            error_out)) {
                        return false;
                    }
                }
                {
                    BranchGuard guard(collect);
                    if (!finalize_specialized_stmt_semantics(
                            collect,
                            if_stmt->else_stmt,
                            expected_return_type,
                            error_out)) {
                        return false;
                    }
                }
                return true;
            }
            if (!finalize_specialized_stmt_semantics(
                    collect,
                    if_stmt->then_stmt,
                    expected_return_type,
                    error_out)) {
                return false;
            }
            if (!finalize_specialized_stmt_semantics(
                    collect,
                    if_stmt->else_stmt,
                    expected_return_type,
                    error_out)) {
                return false;
            }
            return true;
        }
        case StmtKind::SwitchStmt: {
            auto* switch_stmt = static_cast<SwitchStmt*>(stmt.get());
            if (!finalize_specialized_control_condition_declaration(
                    collect,
                    switch_stmt->condition,
                    expected_return_type,
                    error_out)) {
                return false;
            }
            if (!finalize_specialized_switch_condition_expression(
                    collect,
                    switch_stmt->condition.expression,
                    switch_stmt->location,
                    error_out)) {
                return false;
            }
            return finalize_specialized_stmt_semantics(
                collect,
                switch_stmt->stmt,
                expected_return_type,
                error_out);
        }
        case StmtKind::WhileStmt: {
            auto* while_stmt = static_cast<WhileStmt*>(stmt.get());
            if (!finalize_specialized_control_condition_declaration(
                    collect,
                    while_stmt->condition,
                    expected_return_type,
                    error_out)) {
                return false;
            }
            if (!finalize_specialized_condition_expression(
                    collect,
                    while_stmt->condition.expression,
                    while_stmt->location,
                    "while",
                    error_out)) {
                return false;
            }
            return finalize_specialized_stmt_semantics(
                collect,
                while_stmt->body_stmt,
                expected_return_type,
                error_out);
        }
        case StmtKind::DoWhileStmt: {
            auto* do_while_stmt = static_cast<DoWhileStmt*>(stmt.get());
            if (!finalize_specialized_stmt_semantics(
                    collect,
                    do_while_stmt->body_stmt,
                    expected_return_type,
                    error_out)) {
                return false;
            }
            if (!finalize_specialized_condition_expression(
                    collect,
                    do_while_stmt->condition,
                    do_while_stmt->location,
                    "do/while",
                    error_out)) {
                return false;
            }
            return true;
        }
        case StmtKind::ForStmt: {
            auto* for_stmt = static_cast<ForStmt*>(stmt.get());
            if (!finalize_specialized_stmt_semantics(
                    collect,
                    for_stmt->init,
                    expected_return_type,
                    error_out)) {
                return false;
            }
            if (!finalize_specialized_control_condition_declaration(
                    collect,
                    for_stmt->cond,
                    expected_return_type,
                    error_out)) {
                return false;
            }
            if (!finalize_specialized_condition_expression(
                    collect,
                    for_stmt->cond.expression,
                    for_stmt->location,
                    "for",
                    error_out)) {
                return false;
            }
            if (for_stmt->action) {
                strip_redundant_specialization_casts(for_stmt->action);
                for_stmt->action = collect.collect_apply_standard_conversions(
                    std::move(for_stmt->action),
                    Collect::ExprUseContext::ExpressionStatement);
            }
            return finalize_specialized_stmt_semantics(
                collect,
                for_stmt->body_stmt,
                expected_return_type,
                error_out);
        }
        case StmtKind::CppRangeForStmt: {
            auto* range_for = static_cast<CppRangeForStmt*>(stmt.get());
            if (!finalize_specialized_stmt_semantics(
                    collect,
                    range_for->init_statement,
                    expected_return_type,
                    error_out)) {
                return false;
            }
            for (auto& decl : range_for->range_declaration_side_decls) {
                if (!finalize_specialized_decl_semantics(
                        collect,
                        decl,
                        error_out)) {
                    return false;
                }
            }
            if (!finalize_specialized_decl_semantics(
                    collect,
                    range_for->range_variable,
                    error_out) ||
                !finalize_specialized_decl_semantics(
                    collect,
                    range_for->begin_variable,
                    error_out) ||
                !finalize_specialized_decl_semantics(
                    collect,
                    range_for->end_variable,
                    error_out) ||
                !finalize_specialized_decl_semantics(
                    collect,
                    range_for->loop_variable,
                    error_out)) {
                return false;
            }
            if (!finalize_specialized_condition_expression(
                    collect,
                    range_for->condition,
                    range_for->location,
                    "range-for",
                    error_out)) {
                return false;
            }
            if (range_for->increment) {
                strip_redundant_specialization_casts(range_for->increment);
                range_for->increment =
                    collect.collect_apply_standard_conversions(
                        std::move(range_for->increment),
                        Collect::ExprUseContext::ExpressionStatement);
            }
            return finalize_specialized_stmt_semantics(
                collect,
                range_for->body_stmt,
                expected_return_type,
                error_out);
        }
        case StmtKind::CaseStmt: {
            auto* case_stmt = static_cast<CaseStmt*>(stmt.get());
            if (case_stmt->const_expr) {
                strip_redundant_specialization_casts(case_stmt->const_expr);
                case_stmt->const_expr = collect.collect_apply_standard_conversions(
                    std::move(case_stmt->const_expr),
                    Collect::ExprUseContext::RValue);
            }
            if (case_stmt->range_end) {
                strip_redundant_specialization_casts(case_stmt->range_end);
                case_stmt->range_end = collect.collect_apply_standard_conversions(
                    std::move(case_stmt->range_end),
                    Collect::ExprUseContext::RValue);
            }
            return finalize_specialized_stmt_semantics(
                collect,
                case_stmt->stmt,
                expected_return_type,
                error_out);
        }
        case StmtKind::DefaultStmt: {
            auto* default_stmt = static_cast<DefaultStmt*>(stmt.get());
            return finalize_specialized_stmt_semantics(
                collect,
                default_stmt->stmt,
                expected_return_type,
                error_out);
        }
        case StmtKind::LabeledStmt: {
            auto* labeled_stmt = static_cast<LabeledStmt*>(stmt.get());
            return finalize_specialized_stmt_semantics(
                collect,
                labeled_stmt->stmt,
                expected_return_type,
                error_out);
        }
        case StmtKind::ComputedGotoStmt: {
            auto* goto_stmt = static_cast<ComputedGotoStmt*>(stmt.get());
            if (goto_stmt->target) {
                strip_redundant_specialization_casts(goto_stmt->target);
                goto_stmt->target = collect.collect_apply_standard_conversions(
                    std::move(goto_stmt->target),
                    Collect::ExprUseContext::RValue);
            }
            return true;
        }
        case StmtKind::CppTryStmt: {
            auto* try_stmt = static_cast<CppTryStmt*>(stmt.get());
            if (!finalize_specialized_stmt_semantics(
                    collect,
                    try_stmt->try_block,
                    expected_return_type,
                    error_out)) {
                return false;
            }
            for (auto& handler : try_stmt->handlers) {
                if (!finalize_specialized_stmt_semantics(
                        collect,
                        handler.handler,
                        expected_return_type,
                        error_out)) {
                    return false;
                }
            }
            return true;
        }
        default:
            break;
    }

    if (auto* expr = dyn_cast<Expr>(stmt.get())) {
        SrcLoc loc = expr->location;
        auto owned_expr = std::unique_ptr<Expr>(static_cast<Expr*>(stmt.release()));
        strip_redundant_specialization_casts(owned_expr);
        auto cpp_this_context = collect.collect_current_cpp_this_context();
        if (owned_expr &&
            !collect.resolve_dependent_expr_after_substitution(
                owned_expr,
                cpp_this_context.this_type,
                error_out)) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to resolve dependent expression statement after template substitution";
            }
            return false;
        }
        auto rebuilt =
            collect.collect_expression_statement(std::move(owned_expr), loc);
        if (!rebuilt) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "failed to finalize expression statement after template substitution";
            }
            return false;
        }
        stmt = std::move(rebuilt);
    }

    return true;
}

bool finalize_specialized_ctor_initializers(Collect& collect,
                                            CppConstructorDecl* ctor_decl,
                                            std::string* error_out) {
    if (!ctor_decl) {
        return true;
    }

    for (auto& initializer : ctor_decl->ctor_initializers) {
        if (!rebuild_specialized_ctor_initializer_expression(
                collect,
                ctor_decl,
                initializer,
                error_out)) {
            return false;
        }
    }

    return true;
}

} // namespace template_sema_internal
