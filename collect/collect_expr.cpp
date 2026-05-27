#include "collect.h"
#include "collect_internal.h"
#include "collect_templates_internal.h"
#include "../ast/ast_clone.h"
#include "../helpers/auto_type_utils.h"
#include "../ast/expr_clone.h"
#include "../ast/special_members.h"
#include "lookup_engine.h"
#include <algorithm>
#include <functional>
#include <limits>
#include <optional>

using namespace collect_internal;

namespace {

bool scope_is_before_current_record_member_lookup(ScopeFlags flags) {
    return scope_flags_contains(flags, ScopeFlags::FunctionScope) ||
           scope_flags_contains(flags, ScopeFlags::BlockScope) ||
           scope_flags_contains(flags, ScopeFlags::PrototypeScope) ||
           scope_flags_contains(flags, ScopeFlags::LoopScope) ||
           scope_flags_contains(flags, ScopeFlags::SwitchScope) ||
           scope_flags_contains(flags, ScopeFlags::TemplateParameterScope);
}

bool ordinary_lookup_blocks_current_record_member_lookup(
    const LookupEngine::UnqualifiedOrdinaryLookupResult& lookup) {
    return lookup.found_in_lookup_context() &&
           lookup.scope &&
           scope_is_before_current_record_member_lookup(lookup.scope->flags);
}

bool template_lookup_blocks_current_record_member_lookup(
    const LookupEngine::UnqualifiedTemplateLookupResult& lookup) {
    return lookup.found_in_lookup_context() &&
           lookup.scope &&
           scope_is_before_current_record_member_lookup(lookup.scope->flags);
}

bool scope_is_within_current_function_body(
    const std::shared_ptr<Scope>& current_scope,
    const std::shared_ptr<Scope>& candidate_scope) {
    for (auto scope = current_scope; scope; scope = scope->parent) {
        if (scope == candidate_scope) {
            return true;
        }
        if (scope_flags_contains(scope->flags, ScopeFlags::FunctionScope)) {
            return false;
        }
    }
    return false;
}

struct CppBasePathAccessSummary {
    size_t accessible_nonvirtual_paths = 0;
    size_t inaccessible_nonvirtual_paths = 0;
    bool accessible_virtual_path = false;
    bool inaccessible_virtual_path = false;

    bool has_any_path() const {
        return accessible_nonvirtual_paths > 0 ||
               inaccessible_nonvirtual_paths > 0 ||
               accessible_virtual_path ||
               inaccessible_virtual_path;
    }

    size_t accessible_subobject_count() const {
        return accessible_nonvirtual_paths + (accessible_virtual_path ? 1 : 0);
    }

    bool has_inaccessible_path() const {
        return inaccessible_nonvirtual_paths > 0 || inaccessible_virtual_path;
    }
};

bool cpp_base_edge_accessible_from_context(
    RecordMemberAccess access,
    const ObjectDecl* edge_owner_decl,
    const ObjectDecl* access_context_decl,
    const ObjectDecl* object_record_decl,
    QualType access_context_type,
    const ASTContext* ast_ctx) {
    switch (access) {
        case RecordMemberAccess::Public:
            return true;
        case RecordMemberAccess::Private:
            return can_access_private_member_in_context(
                edge_owner_decl,
                access_context_decl,
                ast_ctx,
                access_context_type);
        case RecordMemberAccess::Protected:
            return can_access_protected_member_in_context(
                edge_owner_decl,
                access_context_decl,
                object_record_decl,
                false,
                ast_ctx,
                access_context_type);
    }
    return false;
}

void accumulate_cpp_accessible_base_paths(
    const ObjectDecl* current_decl,
    const ObjectDecl* target_base_decl,
    const ObjectDecl* most_derived_decl,
    const ObjectDecl* access_context_decl,
    QualType access_context_type,
    const ASTContext* ast_ctx,
    bool path_accessible,
    bool saw_virtual_edge,
    std::vector<const ObjectDecl*>& active_stack,
    CppBasePathAccessSummary& summary) {
    current_decl = canonical_record_decl(current_decl);
    target_base_decl = canonical_record_decl(target_base_decl);
    most_derived_decl = canonical_record_decl(most_derived_decl);
    if (!current_decl || !target_base_decl) {
        return;
    }

    const RecordSemanticState* state =
        record_semantics_cache_lookup(current_decl, ast_ctx);
    if (!state) {
        return;
    }

    for (const auto& base : state->bases) {
        const ObjectDecl* base_decl = canonical_record_decl(base.record_decl);
        if (!base_decl) {
            continue;
        }

        bool edge_accessible = cpp_base_edge_accessible_from_context(
            base.declared_access,
            current_decl,
            access_context_decl,
            most_derived_decl,
            access_context_type,
            ast_ctx);
        bool next_path_accessible = path_accessible && edge_accessible;
        bool next_saw_virtual_edge = saw_virtual_edge || base.is_virtual;

        if (base_decl == target_base_decl) {
            if (next_path_accessible) {
                if (next_saw_virtual_edge) {
                    summary.accessible_virtual_path = true;
                } else {
                    ++summary.accessible_nonvirtual_paths;
                }
            } else {
                if (next_saw_virtual_edge) {
                    summary.inaccessible_virtual_path = true;
                } else {
                    ++summary.inaccessible_nonvirtual_paths;
                }
            }
            continue;
        }

        if (std::find(active_stack.begin(), active_stack.end(), base_decl) !=
            active_stack.end()) {
            continue;
        }

        active_stack.push_back(base_decl);
        accumulate_cpp_accessible_base_paths(
            base_decl,
            target_base_decl,
            most_derived_decl,
            access_context_decl,
            access_context_type,
            ast_ctx,
            next_path_accessible,
            next_saw_virtual_edge,
            active_stack,
            summary);
        active_stack.pop_back();
    }
}

CppBasePathAccessSummary summarize_cpp_accessible_base_paths(
    const ObjectDecl* derived_decl,
    const ObjectDecl* target_base_decl,
    const ObjectDecl* access_context_decl,
    QualType access_context_type,
    const ASTContext* ast_ctx) {
    CppBasePathAccessSummary summary;
    derived_decl = canonical_record_decl(derived_decl);
    target_base_decl = canonical_record_decl(target_base_decl);
    if (!derived_decl || !target_base_decl || derived_decl == target_base_decl) {
        return summary;
    }

    std::vector<const ObjectDecl*> active_stack;
    active_stack.push_back(derived_decl);
    accumulate_cpp_accessible_base_paths(
        derived_decl,
        target_base_decl,
        derived_decl,
        access_context_decl,
        access_context_type,
        ast_ctx,
        true,
        false,
        active_stack,
        summary);
    return summary;
}

std::optional<QualType> merge_cpp_conditional_glvalue_type(
    QualType lhs_type,
    QualType rhs_type,
    Collect::ValueCategory lhs_category,
    Collect::ValueCategory rhs_category) {
    bool lhs_is_glvalue =
        lhs_category == Collect::ValueCategory::LValue ||
        lhs_category == Collect::ValueCategory::XValue;
    bool rhs_is_glvalue =
        rhs_category == Collect::ValueCategory::LValue ||
        rhs_category == Collect::ValueCategory::XValue;
    if (!lhs_is_glvalue ||
        !rhs_is_glvalue ||
        lhs_category != rhs_category ||
        !lhs_type ||
        !rhs_type) {
        return std::nullopt;
    }

    if (lhs_type.equals_unqualified(rhs_type)) {
        return QualType(
            lhs_type.get_shared(),
            static_cast<uint8_t>(
                lhs_type.get_qualifiers() | rhs_type.get_qualifiers()));
    }

    auto lhs_ref = desugar_type(lhs_type).as_shared<ReferenceType>();
    auto rhs_ref = desugar_type(rhs_type).as_shared<ReferenceType>();
    if (!lhs_ref ||
        !rhs_ref ||
        lhs_ref->reference_kind != rhs_ref->reference_kind ||
        !lhs_ref->referred_type ||
        !rhs_ref->referred_type ||
        !lhs_ref->referred_type.equals_unqualified(rhs_ref->referred_type)) {
        return std::nullopt;
    }

    QualType merged_referred(
        lhs_ref->referred_type.get_shared(),
        static_cast<uint8_t>(
            lhs_ref->referred_type.get_qualifiers() |
            rhs_ref->referred_type.get_qualifiers()));
    return make_reference_type(merged_referred, lhs_ref->reference_kind);
}

QualType known_dependent_unary_result_type(UnaryOpTypes uop,
                                           QualType operand_type,
                                           const ASTContext* ast_ctx) {
    switch (uop) {
        case UnaryOpTypes::DEREFERENCE: {
            auto ptr_type =
                desugar_type(operand_type, ast_ctx).as_shared<PointerType>();
            if (!ptr_type) {
                return nullptr;
            }
            if (auto spelled_ptr = operand_type.as_shared<PointerType>()) {
                return spelled_ptr->pointed_type;
            }
            return ptr_type->pointed_type;
        }
        default:
            return nullptr;
    }
}

bool expression_can_be_addressed_without_overload(const Collect& collect,
                                                  Expr* raw) {
    if (!raw) {
        return false;
    }
    QualType raw_type = raw->get_type();
    if (raw_type && canonical_type_kind(raw_type) == TypeKind::Function) {
        return true;
    }
    return collect.classify_value_category(raw) == Collect::ValueCategory::LValue;
}

Expr* strip_implicit_casts_and_parens(Expr* expr) {
    Expr* current = Collect::strip_implicit_casts(expr);
    while (auto* paren = dyn_cast<ParenExpr>(current)) {
        current = Collect::strip_implicit_casts(paren->subexpr.get());
    }
    return current;
}

QualType strip_atomic_value_qualifier(QualType type) {
    if (!type || !type.is_atomic()) {
        return type;
    }
    return QualType(
        type.get_shared(),
        static_cast<uint8_t>(type.get_qualifiers() & ~QUAL_ATOMIC));
}

QualType atomic_builtin_value_type_from_pointer_arg(Expr* arg,
                                                    const ASTContext* ast_ctx) {
    if (!arg) {
        return {};
    }

    auto ptr = desugar_type(arg->get_type(), ast_ctx).as_shared<PointerType>();
    if (!ptr) {
        return {};
    }
    return strip_atomic_value_qualifier(ptr->pointed_type);
}

void collect_lambda_local_symbols_from_decl(
    const Decl* decl,
    std::unordered_set<const Symbol*>& local_symbols);

void collect_lambda_referenced_symbols_from_expr(
    const Expr* expr,
    std::vector<std::shared_ptr<Symbol>>& referenced_symbols,
    std::unordered_set<const Symbol*>& seen_symbols,
    bool& referenced_this);

void collect_lambda_referenced_symbols_from_decl(
    const Decl* decl,
    std::vector<std::shared_ptr<Symbol>>& referenced_symbols,
    std::unordered_set<const Symbol*>& seen_symbols,
    bool& referenced_this);

void collect_lambda_local_symbols_from_stmt(
    const Stmt* stmt,
    std::unordered_set<const Symbol*>& local_symbols) {
    if (!stmt) {
        return;
    }

    if (auto* compound = dyn_cast<const CompoundStmt>(stmt)) {
        for (const auto& child : compound->statements) {
            collect_lambda_local_symbols_from_stmt(child.get(), local_symbols);
        }
        return;
    }
    if (auto* decl_stmt = dyn_cast<const Decl2Stmt>(stmt)) {
        for (const auto& decl : decl_stmt->decls) {
            collect_lambda_local_symbols_from_decl(decl.get(), local_symbols);
        }
        return;
    }
    if (auto* if_stmt = dyn_cast<const IfStmt>(stmt)) {
        collect_lambda_local_symbols_from_stmt(if_stmt->init_stmt.get(), local_symbols);
        if (if_stmt->statement_kind == IfStatementKind::Constexpr &&
            if_stmt->constexpr_condition_value.has_value()) {
            collect_lambda_local_symbols_from_stmt(
                (*if_stmt->constexpr_condition_value
                     ? if_stmt->then_stmt
                     : if_stmt->else_stmt).get(),
                local_symbols);
        } else {
            collect_lambda_local_symbols_from_stmt(if_stmt->then_stmt.get(), local_symbols);
            collect_lambda_local_symbols_from_stmt(if_stmt->else_stmt.get(), local_symbols);
        }
        return;
    }
    if (auto* switch_stmt = dyn_cast<const SwitchStmt>(stmt)) {
        collect_lambda_local_symbols_from_stmt(switch_stmt->stmt.get(), local_symbols);
        return;
    }
    if (auto* while_stmt = dyn_cast<const WhileStmt>(stmt)) {
        collect_lambda_local_symbols_from_stmt(while_stmt->body_stmt.get(), local_symbols);
        return;
    }
    if (auto* do_stmt = dyn_cast<const DoWhileStmt>(stmt)) {
        collect_lambda_local_symbols_from_stmt(do_stmt->body_stmt.get(), local_symbols);
        return;
    }
    if (auto* for_stmt = dyn_cast<const ForStmt>(stmt)) {
        collect_lambda_local_symbols_from_stmt(for_stmt->init.get(), local_symbols);
        collect_lambda_local_symbols_from_stmt(for_stmt->body_stmt.get(), local_symbols);
        return;
    }
    if (auto* range_for = dyn_cast<const CppRangeForStmt>(stmt)) {
        collect_lambda_local_symbols_from_stmt(
            range_for->init_statement.get(), local_symbols);
        for (const auto& decl : range_for->range_declaration_side_decls) {
            collect_lambda_local_symbols_from_decl(decl.get(), local_symbols);
        }
        collect_lambda_local_symbols_from_decl(
            range_for->range_variable.get(), local_symbols);
        collect_lambda_local_symbols_from_decl(
            range_for->begin_variable.get(), local_symbols);
        collect_lambda_local_symbols_from_decl(
            range_for->end_variable.get(), local_symbols);
        collect_lambda_local_symbols_from_decl(
            range_for->loop_variable.get(), local_symbols);
        collect_lambda_local_symbols_from_stmt(
            range_for->body_stmt.get(), local_symbols);
        return;
    }
    if (auto* labeled = dyn_cast<const LabeledStmt>(stmt)) {
        collect_lambda_local_symbols_from_stmt(labeled->stmt.get(), local_symbols);
        return;
    }
    if (auto* case_stmt = dyn_cast<const CaseStmt>(stmt)) {
        collect_lambda_local_symbols_from_stmt(case_stmt->stmt.get(), local_symbols);
        return;
    }
    if (auto* default_stmt = dyn_cast<const DefaultStmt>(stmt)) {
        collect_lambda_local_symbols_from_stmt(default_stmt->stmt.get(), local_symbols);
        return;
    }
    if (auto* try_stmt = dyn_cast<const CppTryStmt>(stmt)) {
        collect_lambda_local_symbols_from_stmt(try_stmt->try_block.get(), local_symbols);
        for (const auto& handler : try_stmt->handlers) {
            if (handler.exception_symbol) {
                local_symbols.insert(handler.exception_symbol.get());
            }
            collect_lambda_local_symbols_from_stmt(handler.handler.get(), local_symbols);
        }
        return;
    }
}

void collect_lambda_local_symbols_from_decl(
    const Decl* decl,
    std::unordered_set<const Symbol*>& local_symbols) {
    if (!decl) {
        return;
    }

    if (auto* param = dyn_cast<const ParamDecl>(decl)) {
        if (param->sym) {
            local_symbols.insert(param->sym.get());
        }
        return;
    }
    if (auto* variable = dyn_cast<const VariableDecl>(decl)) {
        if (variable->sym) {
            local_symbols.insert(variable->sym.get());
        }
        return;
    }
}

void collect_lambda_referenced_symbols_from_decl(
    const Decl* decl,
    std::vector<std::shared_ptr<Symbol>>& referenced_symbols,
    std::unordered_set<const Symbol*>& seen_symbols,
    bool& referenced_this) {
    if (!decl) {
        return;
    }
    if (auto* variable = dyn_cast<const VariableDecl>(decl)) {
        collect_lambda_referenced_symbols_from_expr(
            variable->init.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        return;
    }
}

void collect_lambda_referenced_symbols_from_stmt(
    const Stmt* stmt,
    std::vector<std::shared_ptr<Symbol>>& referenced_symbols,
    std::unordered_set<const Symbol*>& seen_symbols,
    bool& referenced_this) {
    if (!stmt) {
        return;
    }

    if (auto* expr = dyn_cast<const Expr>(stmt)) {
        collect_lambda_referenced_symbols_from_expr(
            expr,
            referenced_symbols,
            seen_symbols,
            referenced_this);
        return;
    }
    if (auto* compound = dyn_cast<const CompoundStmt>(stmt)) {
        for (const auto& child : compound->statements) {
            collect_lambda_referenced_symbols_from_stmt(
                child.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
        }
        return;
    }
    if (auto* decl_stmt = dyn_cast<const Decl2Stmt>(stmt)) {
        for (const auto& decl : decl_stmt->decls) {
            if (auto* variable = dyn_cast<const VariableDecl>(decl.get())) {
                collect_lambda_referenced_symbols_from_expr(
                    variable->init.get(),
                    referenced_symbols,
                    seen_symbols,
                    referenced_this);
            }
        }
        return;
    }
    if (auto* if_stmt = dyn_cast<const IfStmt>(stmt)) {
        collect_lambda_referenced_symbols_from_stmt(
            if_stmt->init_stmt.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        collect_lambda_referenced_symbols_from_stmt(
            if_stmt->condition.declaration.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        collect_lambda_referenced_symbols_from_expr(
            if_stmt->condition.expression.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        if (if_stmt->statement_kind == IfStatementKind::Constexpr &&
            if_stmt->constexpr_condition_value.has_value()) {
            collect_lambda_referenced_symbols_from_stmt(
                (*if_stmt->constexpr_condition_value
                     ? if_stmt->then_stmt
                     : if_stmt->else_stmt).get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
        } else {
            collect_lambda_referenced_symbols_from_stmt(
                if_stmt->then_stmt.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            collect_lambda_referenced_symbols_from_stmt(
                if_stmt->else_stmt.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
        }
        return;
    }
    if (auto* switch_stmt = dyn_cast<const SwitchStmt>(stmt)) {
        collect_lambda_referenced_symbols_from_stmt(
            switch_stmt->condition.declaration.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        collect_lambda_referenced_symbols_from_expr(
            switch_stmt->condition.expression.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        collect_lambda_referenced_symbols_from_stmt(
            switch_stmt->stmt.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        return;
    }
    if (auto* while_stmt = dyn_cast<const WhileStmt>(stmt)) {
        collect_lambda_referenced_symbols_from_stmt(
            while_stmt->condition.declaration.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        collect_lambda_referenced_symbols_from_expr(
            while_stmt->condition.expression.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        collect_lambda_referenced_symbols_from_stmt(
            while_stmt->body_stmt.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        return;
    }
    if (auto* do_stmt = dyn_cast<const DoWhileStmt>(stmt)) {
        collect_lambda_referenced_symbols_from_stmt(
            do_stmt->body_stmt.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        collect_lambda_referenced_symbols_from_expr(
            do_stmt->condition.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        return;
    }
    if (auto* for_stmt = dyn_cast<const ForStmt>(stmt)) {
        collect_lambda_referenced_symbols_from_stmt(
            for_stmt->init.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        collect_lambda_referenced_symbols_from_stmt(
            for_stmt->cond.declaration.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        collect_lambda_referenced_symbols_from_expr(
            for_stmt->cond.expression.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        collect_lambda_referenced_symbols_from_expr(
            for_stmt->action.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        collect_lambda_referenced_symbols_from_stmt(
            for_stmt->body_stmt.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        return;
    }
    if (auto* range_for = dyn_cast<const CppRangeForStmt>(stmt)) {
        collect_lambda_referenced_symbols_from_stmt(
            range_for->init_statement.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        for (const auto& decl : range_for->range_declaration_side_decls) {
            collect_lambda_referenced_symbols_from_decl(
                decl.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
        }
        collect_lambda_referenced_symbols_from_decl(
            range_for->range_variable.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        collect_lambda_referenced_symbols_from_decl(
            range_for->begin_variable.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        collect_lambda_referenced_symbols_from_decl(
            range_for->end_variable.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        collect_lambda_referenced_symbols_from_decl(
            range_for->loop_variable.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        collect_lambda_referenced_symbols_from_expr(
            range_for->condition.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        collect_lambda_referenced_symbols_from_expr(
            range_for->increment.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        collect_lambda_referenced_symbols_from_stmt(
            range_for->body_stmt.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        return;
    }
    if (auto* ret = dyn_cast<const ReturnStmt>(stmt)) {
        collect_lambda_referenced_symbols_from_expr(
            ret->expression.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        return;
    }
    if (auto* labeled = dyn_cast<const LabeledStmt>(stmt)) {
        collect_lambda_referenced_symbols_from_stmt(
            labeled->stmt.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        return;
    }
    if (auto* case_stmt = dyn_cast<const CaseStmt>(stmt)) {
        collect_lambda_referenced_symbols_from_expr(
            case_stmt->const_expr.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        collect_lambda_referenced_symbols_from_expr(
            case_stmt->range_end.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        collect_lambda_referenced_symbols_from_stmt(
            case_stmt->stmt.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        return;
    }
    if (auto* default_stmt = dyn_cast<const DefaultStmt>(stmt)) {
        collect_lambda_referenced_symbols_from_stmt(
            default_stmt->stmt.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        return;
    }
    if (auto* try_stmt = dyn_cast<const CppTryStmt>(stmt)) {
        collect_lambda_referenced_symbols_from_stmt(
            try_stmt->try_block.get(),
            referenced_symbols,
            seen_symbols,
            referenced_this);
        for (const auto& handler : try_stmt->handlers) {
            collect_lambda_referenced_symbols_from_stmt(
                handler.handler.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
        }
        return;
    }
}

void collect_lambda_referenced_symbols_from_expr(
    const Expr* expr,
    std::vector<std::shared_ptr<Symbol>>& referenced_symbols,
    std::unordered_set<const Symbol*>& seen_symbols,
    bool& referenced_this) {
    if (!expr || isa<CppLambdaExpr>(expr) || isa<BlockExpr>(expr)) {
        return;
    }

    switch (expr->get_kind()) {
        case StmtKind::VarRef:
        case StmtKind::QualifiedVarRef: {
            auto* var_ref = static_cast<const VarRef*>(expr);
            if (var_ref->symref && seen_symbols.insert(var_ref->symref.get()).second) {
                referenced_symbols.push_back(var_ref->symref);
            }
            return;
        }
        case StmtKind::BlockByrefAccessExpr: {
            const auto* byref_expr = static_cast<const BlockByrefAccessExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                byref_expr->cell_expr.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::CppThisExpr:
            referenced_this = true;
            return;
        case StmtKind::FuncCall: {
            const auto* call = static_cast<const FuncCall*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                call->func.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            for (const auto& arg : call->args) {
                collect_lambda_referenced_symbols_from_expr(
                    arg.get(),
                    referenced_symbols,
                    seen_symbols,
                    referenced_this);
            }
            return;
        }
        case StmtKind::DependentCallExpr: {
            const auto* call = static_cast<const DependentCallExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                call->callee.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            for (const auto& arg : call->args) {
                collect_lambda_referenced_symbols_from_expr(
                    arg.get(),
                    referenced_symbols,
                    seen_symbols,
                    referenced_this);
            }
            return;
        }
        case StmtKind::CppMemberCallExpr: {
            const auto* call = static_cast<const CppMemberCallExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                call->lowered_call.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::CppConstructExpr: {
            const auto* construct = static_cast<const CppConstructExpr*>(expr);
            for (const auto& arg : construct->args) {
                collect_lambda_referenced_symbols_from_expr(
                    arg.get(),
                    referenced_symbols,
                    seen_symbols,
                    referenced_this);
            }
            return;
        }
        case StmtKind::CppValueInitExpr:
            return;
        case StmtKind::CppFunctionStyleCastExpr: {
            const auto* cast =
                static_cast<const CppFunctionStyleCastExpr*>(expr);
            for (const auto& arg : cast->args) {
                collect_lambda_referenced_symbols_from_expr(
                    arg.get(),
                    referenced_symbols,
                    seen_symbols,
                    referenced_this);
            }
            return;
        }
        case StmtKind::ParenExpr: {
            const auto* paren = static_cast<const ParenExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                paren->subexpr.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::CppThrowExpr: {
            const auto* throw_expr = static_cast<const CppThrowExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                throw_expr->thrown_expr.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::CppNewExpr: {
            const auto* new_expr = static_cast<const CppNewExpr*>(expr);
            for (const auto& arg : new_expr->placement_args) {
                collect_lambda_referenced_symbols_from_expr(
                    arg.get(),
                    referenced_symbols,
                    seen_symbols,
                    referenced_this);
            }
            collect_lambda_referenced_symbols_from_expr(
                new_expr->initializer.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            for (const auto& arg : new_expr->constructor_args) {
                collect_lambda_referenced_symbols_from_expr(
                    arg.get(),
                    referenced_symbols,
                    seen_symbols,
                    referenced_this);
            }
            return;
        }
        case StmtKind::CppDeleteExpr: {
            const auto* delete_expr = static_cast<const CppDeleteExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                delete_expr->operand.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::UnaryOperation: {
            const auto* unary = static_cast<const UnaryOperation*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                unary->exp.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::DependentUnaryExpr: {
            const auto* unary = static_cast<const DependentUnaryExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                unary->operand.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::BinaryOperation: {
            const auto* binary = static_cast<const BinaryOperation*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                binary->left.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            collect_lambda_referenced_symbols_from_expr(
                binary->right.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::CppBuiltinThreeWayCompareExpr: {
            const auto* compare =
                static_cast<const CppBuiltinThreeWayCompareExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                compare->left.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            collect_lambda_referenced_symbols_from_expr(
                compare->right.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::DependentBinaryExpr: {
            const auto* binary = static_cast<const DependentBinaryExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                binary->left.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            collect_lambda_referenced_symbols_from_expr(
                binary->right.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::CompoundAssignOperation: {
            const auto* binary =
                static_cast<const CompoundAssignOperation*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                binary->left.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            collect_lambda_referenced_symbols_from_expr(
                binary->right.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::ArraySubscriptExpr: {
            const auto* subscript = static_cast<const ArraySubscriptExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                subscript->array.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            collect_lambda_referenced_symbols_from_expr(
                subscript->index.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::DependentArraySubscriptExpr: {
            const auto* subscript =
                static_cast<const DependentArraySubscriptExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                subscript->array.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            collect_lambda_referenced_symbols_from_expr(
                subscript->index.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::MemberExpr: {
            const auto* member = static_cast<const MemberExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                member->base.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::UnresolvedMemberExpr: {
            const auto* member = static_cast<const UnresolvedMemberExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                member->base.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::MemberPointerAccessExpr: {
            const auto* member = static_cast<const MemberPointerAccessExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                member->base.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            collect_lambda_referenced_symbols_from_expr(
                member->member_pointer.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::DependentMemberPointerAccessExpr: {
            const auto* member =
                static_cast<const DependentMemberPointerAccessExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                member->base.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            collect_lambda_referenced_symbols_from_expr(
                member->member_pointer.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::ImplicitCast: {
            const auto* cast = static_cast<const ImplicitCast*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                cast->expr.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::ExplicitCast: {
            const auto* cast = static_cast<const ExplicitCast*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                cast->expr.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::CondExpr: {
            const auto* conditional = static_cast<const CondExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                conditional->condition.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            collect_lambda_referenced_symbols_from_expr(
                conditional->true_expr.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            collect_lambda_referenced_symbols_from_expr(
                conditional->false_expr.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::InitListExpr: {
            const auto* init_list = static_cast<const InitListExpr*>(expr);
            for (const auto& element : init_list->elements) {
                for (const auto& designator : element.designators) {
                    collect_lambda_referenced_symbols_from_expr(
                        designator.index.get(),
                        referenced_symbols,
                        seen_symbols,
                        referenced_this);
                    collect_lambda_referenced_symbols_from_expr(
                        designator.range_end.get(),
                        referenced_symbols,
                        seen_symbols,
                        referenced_this);
                }
                collect_lambda_referenced_symbols_from_expr(
                    element.value.get(),
                    referenced_symbols,
                    seen_symbols,
                    referenced_this);
            }
            for (const auto& action : init_list->actions) {
                collect_lambda_referenced_symbols_from_expr(
                    action.value.get(),
                    referenced_symbols,
                    seen_symbols,
                    referenced_this);
            }
            for (const auto& mapping : init_list->mappings) {
                collect_lambda_referenced_symbols_from_expr(
                    mapping.second.get(),
                    referenced_symbols,
                    seen_symbols,
                    referenced_this);
            }
            return;
        }
        case StmtKind::CompoundLiteralExpr: {
            const auto* literal = static_cast<const CompoundLiteralExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                literal->init.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::StmtExpr: {
            const auto* stmt_expr = static_cast<const StmtExpr*>(expr);
            collect_lambda_referenced_symbols_from_stmt(
                stmt_expr->compound_stmt.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::CppTypeIdExpr: {
            const auto* typeid_expr = static_cast<const CppTypeIdExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                typeid_expr->expr_operand.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::CppDynamicCastExpr: {
            const auto* dyn_cast_expr =
                static_cast<const CppDynamicCastExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                dyn_cast_expr->expr.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::PackExpansionExpr: {
            const auto* pack = static_cast<const PackExpansionExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                pack->pattern.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::FoldExpr: {
            const auto* fold = static_cast<const FoldExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                fold->pattern.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            collect_lambda_referenced_symbols_from_expr(
                fold->init.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::SizeOfExpr: {
            const auto* sizeof_expr = static_cast<const SizeOfExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                sizeof_expr->expr_operand.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::AlignOfExpr: {
            const auto* alignof_expr = static_cast<const AlignOfExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                alignof_expr->expr_operand.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::OffsetOfExpr: {
            const auto* offsetof_expr = static_cast<const OffsetOfExpr*>(expr);
            (void)offsetof_expr;
            return;
        }
        case StmtKind::GenericExpr: {
            const auto* generic_expr = static_cast<const GenericExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                generic_expr->controlling_expr.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            for (const auto& association : generic_expr->associations) {
                collect_lambda_referenced_symbols_from_expr(
                    association.expr.get(),
                    referenced_symbols,
                    seen_symbols,
                    referenced_this);
            }
            return;
        }
        case StmtKind::VaArgExpr: {
            const auto* va_arg_expr = static_cast<const VaArgExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                va_arg_expr->va_list_expr.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::VaStartExpr: {
            const auto* va_start_expr = static_cast<const VaStartExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                va_start_expr->va_list_expr.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            collect_lambda_referenced_symbols_from_expr(
                va_start_expr->last_param.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::VaEndExpr: {
            const auto* va_end_expr = static_cast<const VaEndExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                va_end_expr->va_list_expr.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::VaCopyExpr: {
            const auto* va_copy_expr = static_cast<const VaCopyExpr*>(expr);
            collect_lambda_referenced_symbols_from_expr(
                va_copy_expr->dest.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            collect_lambda_referenced_symbols_from_expr(
                va_copy_expr->src.get(),
                referenced_symbols,
                seen_symbols,
                referenced_this);
            return;
        }
        case StmtKind::BuiltinCallExpr: {
            const auto* builtin_expr = static_cast<const BuiltinCallExpr*>(expr);
            for (const auto& arg : builtin_expr->args) {
                collect_lambda_referenced_symbols_from_expr(
                    arg.get(),
                    referenced_symbols,
                    seen_symbols,
                    referenced_this);
            }
            return;
        }
        default:
            return;
    }
}

std::vector<CppLambdaCapture> build_lambda_semantic_captures(
    const CppLambdaExpr& lambda) {
    std::vector<CppLambdaCapture> captures = lambda.closure_info.captures;
    bool captures_this = false;
    for (const auto& capture : captures) {
        if (capture.captures_this) {
            captures_this = true;
            break;
        }
    }

    std::unordered_set<const Symbol*> lambda_local_symbols;
    for (const auto& parameter : lambda.parameters) {
        collect_lambda_local_symbols_from_decl(
            parameter.get(),
            lambda_local_symbols);
    }
    collect_lambda_local_symbols_from_stmt(lambda.body.get(), lambda_local_symbols);

    std::unordered_set<const Symbol*> captured_symbols;
    for (const auto& capture : captures) {
        if (capture.symbol) {
            captured_symbols.insert(capture.symbol.get());
        }
    }

    std::vector<std::shared_ptr<Symbol>> referenced_symbols;
    std::unordered_set<const Symbol*> seen_symbols;
    bool referenced_this = false;
    collect_lambda_referenced_symbols_from_stmt(
        lambda.body.get(),
        referenced_symbols,
        seen_symbols,
        referenced_this);

    if (lambda.closure_info.default_capture != CppLambdaCaptureDefault::None &&
        referenced_this &&
        !captures_this) {
        CppLambdaCapture capture;
        capture.name = "this";
        capture.captures_this = true;
        capture.location = lambda.location;
        captures.push_back(std::move(capture));
        captures_this = true;
    }

    if (lambda.closure_info.default_capture == CppLambdaCaptureDefault::None) {
        return captures;
    }

    for (const auto& symbol : referenced_symbols) {
        if (!symbol ||
            !is_local_variable_or_parameter_symbol(symbol) ||
            lambda_local_symbols.contains(symbol.get()) ||
            captured_symbols.contains(symbol.get())) {
            continue;
        }

        CppLambdaCapture capture;
        capture.name = symbol->name;
        capture.symbol = symbol;
        capture.by_reference =
            lambda.closure_info.default_capture ==
            CppLambdaCaptureDefault::ByReference;
        captures.push_back(std::move(capture));
        captured_symbols.insert(symbol.get());
    }

    return captures;
}

QualType build_lambda_call_operator_type(const CppLambdaExpr& lambda,
                                         std::string* error_out) {
    auto written_type =
        lambda.written_call_operator_type.as_shared<FunctionType>();
    if (!written_type) {
        if (error_out && error_out->empty()) {
            *error_out =
                "internal error: lambda is missing a written call operator type";
        }
        return nullptr;
    }

    auto closure_owner_type = lambda.semantic_info.closure_type();
    if (!closure_owner_type) {
        if (error_out && error_out->empty()) {
            *error_out =
                "internal error: lambda closure semantic owner has no object type";
        }
        return nullptr;
    }

    auto call_operator_type = std::make_shared<FunctionType>(*written_type);
    uint8_t this_object_quals = lambda.is_mutable ? QUAL_NONE : QUAL_CONST;
    QualType qualified_owner_type(
        closure_owner_type.get_shared(),
        this_object_quals);
    QualType this_type(
        std::make_shared<PointerType>(qualified_owner_type));
    call_operator_type->insert_parameter(0, this_type);
    return QualType(call_operator_type);
}

const ObjectDecl* lambda_this_record_identity(QualType this_type,
                                              const ASTContext* ast_ctx) {
    auto this_ptr = desugar_type(this_type, ast_ctx).as_shared<PointerType>();
    if (!this_ptr) {
        return nullptr;
    }

    QualType pointee = desugar_type(this_ptr->pointed_type, ast_ctx);
    if (auto object = pointee.as_shared<ObjectType>()) {
        if (const ClassTemplateDecl* primary =
                object->get_primary_class_template()) {
            return canonical_record_decl(primary->pattern_semantic_decl());
        }
        return canonical_record_decl(dyn_cast<ObjectDecl>(object->get_decl()));
    }

    if (auto specialization =
            pointee.as_shared<TemplateSpecializationType>()) {
        auto* primary = dyn_cast<ClassTemplateDecl>(
            const_cast<Decl*>(specialization->primary_template));
        return primary
            ? canonical_record_decl(primary->pattern_semantic_decl())
            : nullptr;
    }

    return nullptr;
}

bool lambda_enclosing_this_types_match(QualType rewritten_this_type,
                                       QualType lexical_this_type,
                                       const ASTContext* ast_ctx) {
    if (!rewritten_this_type || !lexical_this_type) {
        return false;
    }
    if (rewritten_this_type.equals_unqualified(lexical_this_type)) {
        return true;
    }

    QualType rewritten_canonical =
        desugar_type(rewritten_this_type, ast_ctx);
    QualType lexical_canonical =
        desugar_type(lexical_this_type, ast_ctx);
    if (rewritten_canonical &&
        lexical_canonical &&
        rewritten_canonical.equals_unqualified(lexical_canonical)) {
        return true;
    }

    const ObjectDecl* rewritten_record =
        lambda_this_record_identity(rewritten_this_type, ast_ctx);
    const ObjectDecl* lexical_record =
        lambda_this_record_identity(lexical_this_type, ast_ctx);
    return rewritten_record && rewritten_record == lexical_record;
}

std::vector<BlockCapture> build_block_semantic_captures(
    const BlockExpr& block,
    const ASTContext* ast_ctx) {
    (void)ast_ctx;

    std::unordered_set<const Symbol*> block_local_symbols;
    for (const auto& parameter : block.parameters) {
        collect_lambda_local_symbols_from_decl(
            parameter.get(),
            block_local_symbols);
    }
    collect_lambda_local_symbols_from_stmt(block.body.get(), block_local_symbols);

    std::vector<std::shared_ptr<Symbol>> referenced_symbols;
    std::unordered_set<const Symbol*> seen_symbols;
    bool referenced_this = false;
    collect_lambda_referenced_symbols_from_stmt(
        block.body.get(),
        referenced_symbols,
        seen_symbols,
        referenced_this);

    std::vector<BlockCapture> captures;
    std::unordered_set<const Symbol*> captured_symbols;
    for (const auto& symbol : referenced_symbols) {
        if (!symbol ||
            !is_local_variable_or_parameter_symbol(symbol) ||
            block_local_symbols.contains(symbol.get()) ||
            !captured_symbols.insert(symbol.get()).second) {
            continue;
        }

        BlockCapture capture;
        capture.name = symbol->name;
        capture.symbol = symbol;
        capture.kind = symbol->is_block_byref
            ? BlockCaptureKind::ByRef
            : BlockCaptureKind::ConstCopy;
        captures.push_back(std::move(capture));
    }
    return captures;
}

QualType build_block_invoke_type(const BlockExpr& block,
                                 std::string* error_out) {
    auto written_type = block.function_type().as_shared<FunctionType>();
    if (!written_type) {
        if (error_out && error_out->empty()) {
            *error_out =
                "internal error: block is missing a written function type";
        }
        return nullptr;
    }

    auto literal_type = block.semantic_info.literal_type();
    if (!literal_type) {
        if (error_out && error_out->empty()) {
            *error_out =
                "internal error: block literal is missing a synthesized storage type";
        }
        return nullptr;
    }

    auto invoke_type = std::make_shared<FunctionType>(*written_type);
    if (invoke_type->parameters.size() == 1 &&
        invoke_type->parameters.front() &&
        invoke_type->parameters.front()->isVoid() &&
        !invoke_type->is_variadic) {
        invoke_type->clear_parameters();
    }
    invoke_type->insert_parameter(
        0,
        QualType(std::make_shared<PointerType>(literal_type)));
    return QualType(invoke_type);
}

} // namespace

std::unique_ptr<Expr> Collect::collect_integer_literal(const std::string& value, std::shared_ptr<CType> int_type, SrcLoc loc) const {
    const std::string* interned_value = ast_ctx_ ? ast_ctx_->intern_identifier(value) : nullptr;
    if (interned_value) {
        return collect_make<IntegerLiteral>(interned_value, std::move(int_type), loc);
    }
    return collect_make<IntegerLiteral>(value, std::move(int_type), loc);
}


std::unique_ptr<Expr> Collect::collect_floating_literal(const std::string& value, std::shared_ptr<CType> float_type, bool is_imaginary, SrcLoc loc) const {

    if (is_imaginary) {
        return collect_make<FloatingLiteral>(value, std::move(float_type), true, loc);
    }
    return collect_make<FloatingLiteral>(value, std::move(float_type), loc);
}


std::unique_ptr<Expr> Collect::collect_character_literal(const std::string& value, int32_t int_value, QualType char_type, SrcLoc loc) const {

    return collect_make<CharacterLiteral>(value, int_value, std::move(char_type), loc);
}


std::unique_ptr<Expr> Collect::collect_string_literal(const std::string& value, QualType array_type, SrcLoc loc) const {

    return collect_make<StringLiteral>(value, std::move(array_type), loc);
}


std::unique_ptr<Expr> Collect::collect_cpp_this_expression(SrcLoc loc) const {

    if (!session_.func_state_.in_function ||
        !session_.func_state_.current_function_is_cpp_member ||
        session_.func_state_.current_function_is_static_cpp_member ||
        !session_.func_state_.current_function_cpp_this_type) {
        report_error("invalid use of 'this' outside of a non-static member function", loc);
        return collect_make<ErrorExpr>("invalid 'this' expression", loc);
    }
    return collect_make<CppThisExpr>(session_.func_state_.current_function_cpp_this_type, loc);
}

std::unique_ptr<Expr> Collect::collect_unqualified_identifier_expression(
    const std::string& name,
    bool looks_like_call,
    bool might_be_template_id,
    SrcLoc loc) {

    auto ordinary_lookup = collect_lookup_variable_symbol_result(name, true);
    auto sym = ordinary_lookup.symbol;
    LookupEngine::UnqualifiedTemplateLookupResult ordinary_template_lookup;
    const DeclBinding* ordinary_template_binding = nullptr;
    if (lang_opts_.is_cxx_mode() && session_.current_scope_) {
        ordinary_template_lookup =
            LookupEngine::lookup_unqualified_template_binding_result(
                name,
                session_.current_scope_,
                true,
                LookupNamespace::Ordinary);
        ordinary_template_binding = ordinary_template_lookup.binding;
    }
    if (lang_opts_.is_cxx_mode() &&
        might_be_template_id &&
        ordinary_template_binding) {
        if (sym &&
            sym->kind == SymbolKind::FUNCTION &&
            ordinary_template_binding &&
            type_depends_on_template_parameters(sym->type, ast_ctx_.get())) {
            // Template definitions keep a transient ordinary function symbol
            // around so recursive parsing inside the pattern can still see the
            // function. Once a real template binding exists, prefer the
            // template name over that dependent function-pattern symbol.
            sym.reset();
        }
    }
    bool symbol_is_local = is_local_variable_or_parameter_symbol(sym);
    bool symbol_is_current_function_local =
        symbol_is_local &&
        scope_is_within_current_function_body(
            session_.current_scope_,
            ordinary_lookup.scope);
    bool symbol_is_template_parameter =
        sym && sym->template_parameter_decl != nullptr;
    bool ordinary_lookup_blocks_record_member_lookup =
        ordinary_lookup_blocks_current_record_member_lookup(ordinary_lookup) ||
        template_lookup_blocks_current_record_member_lookup(
            ordinary_template_lookup);
    if (session_.func_state_.current_function_is_cpp_member &&
        ordinary_lookup_blocks_record_member_lookup &&
        ordinary_lookup.scope &&
        !scope_is_within_current_function_body(
            session_.current_scope_,
            ordinary_lookup.scope)) {
        ordinary_lookup_blocks_record_member_lookup = false;
    }
    bool is_predefined_ident =
        (name == "__func__" || name == "__FUNCTION__" ||
         name == "__PRETTY_FUNCTION__");
    auto build_current_record_qualified_reference =
        [&](QualType current_record_type,
            std::shared_ptr<Symbol> selected_symbol = nullptr)
            -> std::unique_ptr<Expr> {
            if (!current_record_type) {
                return selected_symbol
                    ? collect_identifier_reference(
                          name,
                          std::move(selected_symbol),
                          loc)
                    : collect_identifier_reference(name, nullptr, loc);
            }
            auto qualified_ref = collect_identifier_reference(
                name,
                std::move(selected_symbol),
                loc);
            if (isa<VarRef>(qualified_ref.get())) {
                qualified_ref = attach_cpp_qualified_info_to_expr(
                    std::move(qualified_ref),
                    build_cpp_qualified_expr_info(
                        /*has_global_qualifier=*/false,
                        {},
                        current_record_type,
                        /*is_type_qualified=*/true,
                        /*is_current_instantiation=*/false));
            }
            return qualified_ref;
        };
    auto resolve_static_record_member_lookup =
        [&](const MemberNameLookupResult& member_lookup,
            QualType current_record_type)
            -> std::unique_ptr<Expr> {
            size_t static_callable_matches =
                member_lookup.static_method_matches +
                member_lookup.static_method_template_matches;
            size_t static_template_candidate_matches =
                member_lookup.static_method_template_matches;
            size_t static_candidate_matches =
                member_lookup.static_method_matches +
                static_template_candidate_matches +
                member_lookup.static_data_matches +
                member_lookup.enumerator_matches;
            if (static_candidate_matches == 0) {
                return nullptr;
            }
            if (looks_like_call &&
                static_callable_matches > 0 &&
                member_lookup.static_data_matches == 0 &&
                member_lookup.enumerator_matches == 0) {
                std::shared_ptr<Symbol> selected_symbol = nullptr;
                if (member_lookup.static_method_matches == 1 &&
                    static_template_candidate_matches == 0 &&
                    member_lookup.single_static_method &&
                    member_lookup.single_static_method->symbol) {
                    selected_symbol =
                        member_lookup.single_static_method->symbol;
                }
                return build_current_record_qualified_reference(
                    current_record_type,
                    std::move(selected_symbol));
            }
            if (static_candidate_matches > 1) {
                report_error("member '" + name + "' is ambiguous", loc);
                return collect_make<ErrorExpr>(
                    "ambiguous member lookup", loc);
            }
            if (member_lookup.static_data_matches == 1 &&
                member_lookup.single_static_data_member &&
                member_lookup.single_static_data_member->symbol) {
                return collect_identifier_reference(
                    name,
                    member_lookup.single_static_data_member->symbol,
                    loc);
            }
            if (member_lookup.enumerator_matches == 1 &&
                member_lookup.single_enumerator_member &&
                member_lookup.single_enumerator_member->symbol) {
                return collect_identifier_reference(
                    name,
                    member_lookup.single_enumerator_member->symbol,
                    loc);
            }
            if (member_lookup.single_static_method &&
                member_lookup.single_static_method->symbol) {
                return collect_identifier_reference(
                    name, member_lookup.single_static_method->symbol, loc);
            }
            report_error(
                "internal error: unresolved member function symbol '" + name +
                "'",
                loc);
            return collect_make<ErrorExpr>(
                "unresolved member function symbol", loc);
        };

    if (lang_opts_.is_cxx_mode() && session_.func_state_.current_function_is_cpp_member) {
        auto current_record =
            current_record_for_unqualified_member_lookup(
                session_.current_cpp_record_lookup_type_,
                session_.func_state_.current_function_cpp_this_type,
                ast_ctx_.get());
        auto member_lookup = lookup_record_member_name(current_record.get(), name);
        if (member_lookup.has_member_match() &&
            !ordinary_lookup_blocks_record_member_lookup &&
            !symbol_is_current_function_local &&
            !symbol_is_template_parameter) {
            size_t static_template_candidate_matches =
                member_lookup.static_method_template_matches;
            size_t nonstatic_template_candidate_matches =
                member_lookup.nonstatic_method_template_matches;
            if (session_.func_state_.current_function_is_static_cpp_member) {
                if (member_lookup.field_matches > 0 ||
                    member_lookup.nonstatic_method_matches > 0 ||
                    nonstatic_template_candidate_matches > 0) {
                    report_error(
                        "invalid use of non-static member '" + name +
                        "' in static member function",
                        loc);
                    return collect_make<ErrorExpr>(
                        "invalid use of non-static member", loc);
                }
                return resolve_static_record_member_lookup(
                    member_lookup,
                    current_record ? QualType(current_record) : QualType());
            }

            if (member_lookup.field_matches == 0 &&
                member_lookup.nonstatic_method_matches == 0 &&
                nonstatic_template_candidate_matches == 0 &&
                (member_lookup.static_method_matches > 0 ||
                 static_template_candidate_matches > 0 ||
                 member_lookup.static_data_matches > 0 ||
                 member_lookup.enumerator_matches > 0)) {
                return resolve_static_record_member_lookup(
                    member_lookup,
                    current_record ? QualType(current_record) : QualType());
            }

            if (!session_.func_state_.current_function_cpp_this_type) {
                report_error(
                    "internal error: missing implicit object parameter type",
                    loc);
                return collect_make<ErrorExpr>(
                    "missing implicit object parameter type", loc);
            }

            auto this_expr = collect_make<CppThisExpr>(
                session_.func_state_.current_function_cpp_this_type, loc);
            return collect_member_expression(
                std::move(this_expr), name, true, loc, looks_like_call);
        }
    }

    if (lang_opts_.is_cxx_mode() &&
        session_.current_cpp_record_lookup_type_ &&
        !session_.func_state_.current_function_is_cpp_member &&
        !ordinary_lookup_blocks_record_member_lookup &&
        !symbol_is_current_function_local &&
        !symbol_is_template_parameter) {
        auto current_record =
            desugar_type(session_.current_cpp_record_lookup_type_, ast_ctx_.get())
                .as_shared<ObjectType>();
        auto member_lookup = lookup_record_member_name(current_record.get(), name);
        size_t static_candidate_matches =
            member_lookup.static_method_matches +
            member_lookup.static_method_template_matches +
            member_lookup.static_data_matches +
            member_lookup.enumerator_matches;
        if (member_lookup.field_matches == 0 &&
            member_lookup.nonstatic_method_matches == 0 &&
            member_lookup.nonstatic_method_template_matches == 0 &&
            static_candidate_matches > 0) {
            return resolve_static_record_member_lookup(
                member_lookup,
                session_.current_cpp_record_lookup_type_);
        }
    }

    if (sym || is_predefined_ident) {
        return collect_identifier_reference(name, std::move(sym), loc);
    }
    if (lang_opts_.is_cxx_mode() &&
        might_be_template_id &&
        ordinary_template_binding) {
        return collect_identifier_reference(name, nullptr, loc);
    }
    if (!looks_like_call) {
        report_error("use of undeclared identifier '" + name + "'", loc);
        return collect_make<ErrorExpr>("undeclared identifier", loc);
    }
    return collect_identifier_reference(name, nullptr, loc);
}


std::unique_ptr<Expr> Collect::collect_identifier_reference(const std::string& name, std::shared_ptr<Symbol> sym, SrcLoc loc) const {

    if (name == "__func__" || name == "__FUNCTION__" || name == "__PRETTY_FUNCTION__") {
        PredefinedIdentKind kind = PredefinedIdentKind::Func;
        if (name == "__FUNCTION__") {
            kind = PredefinedIdentKind::Function;
        } else if (name == "__PRETTY_FUNCTION__") {
            kind = PredefinedIdentKind::PrettyFunction;
        }
        std::string value;
        if (session_.func_state_.in_function) {
            if (kind == PredefinedIdentKind::PrettyFunction) {
                value = session_.func_state_.current_pretty_function_name;
            } else {
                value = session_.func_state_.current_function_name;
            }
        }
        size_t len = value.size() + 1;
        auto char_type = get_builtin_char();
        auto arr_type = std::make_shared<ArrayType>(QualType(char_type), len);
        QualType qt(arr_type, QUAL_CONST);
        return collect_make<PredefinedExpr>(kind, value, qt, loc);
    }
    if (sym) {
        return collect_make<VarRef>(std::move(sym), loc);
    }
    if (!ast_ctx_) {
        return collect_make<VarRef>(name, loc);
    }
    return collect_make<VarRef>(ast_ctx_->intern_identifier(name), loc);
}

std::unique_ptr<Expr> Collect::collect_unresolved_lookup_expression(
    std::string name,
    DependentLookupQualifier qualifier,
    bool requires_template_keyword,
    SrcLoc loc) const {
    QualType unresolved_type(
        std::make_shared<AutoType>(AutoTypeFlavor::Cxx));
    return collect_make<UnresolvedLookupExpr>(
        std::move(name),
        std::move(qualifier),
        std::nullopt,
        requires_template_keyword,
        /*is_dependent=*/true,
        unresolved_type,
        loc,
        session_.current_scope_,
        session_.current_decl_context_);
}


Collect::LookupResult Collect::collect_lookup_result(const std::string& name, std::shared_ptr<Symbol> selected) const {

    LookupResult result;
    result.name = name;
    if (selected) {
        result.candidates.push_back(selected);
        result.selected = std::move(selected);
    }
    result.ambiguous = result.candidates.size() > 1;
    return result;
}


std::unique_ptr<Expr> Collect::collect_identifier_reference(LookupResult lookup, SrcLoc loc) const {

    if (lookup.ambiguous) {
        report_error("ambiguous lookup for identifier '" + lookup.name + "'", loc);
        return collect_make<ErrorExpr>("ambiguous identifier lookup", loc);
    }
    return collect_identifier_reference(lookup.name, std::move(lookup.selected), loc);
}


std::unique_ptr<Expr> Collect::collect_error_expression(const std::string& message, SrcLoc loc) const {

    return collect_make<ErrorExpr>(message, loc);
}


std::unique_ptr<Expr> Collect::collect_statement_expression(std::unique_ptr<CompoundStmt> compound_stmt, SrcLoc loc) const {

    auto node = collect_make<StmtExpr>(std::move(compound_stmt), loc);
    QualType result_type = QualType(get_builtin_void());
    if (node->compound_stmt && !node->compound_stmt->statements.empty()) {
        auto* last_stmt = node->compound_stmt->statements.back().get();
        if (auto* last_expr = dyn_cast<Expr>(last_stmt)) {
            auto last_type = last_expr->get_type();
            if (last_type) {
                result_type = last_type;
            }
        }
    }
    node->type = result_type;
    return node;
}

bool Collect::finalize_cpp_lambda_semantics(
    CppLambdaExpr& lambda,
    std::string* error_out) {
    auto fail = [&](const std::string& message, SrcLoc loc) -> bool {
        report_error(message, loc);
        if (error_out && error_out->empty()) {
            *error_out = message;
        }
        return false;
    };

    if (!ast_ctx_) {
        return false;
    }

    QualType call_operator_type =
        build_lambda_call_operator_type(lambda, error_out);
    if (!call_operator_type) {
        return fail(
            error_out && !error_out->empty()
                ? *error_out
                : "internal error: failed to build lambda call operator type",
            lambda.location);
    }

    if (!lambda.semantic_info.closure_record_decl) {
        lambda.semantic_info.closure_record_decl = make_ast<CppRecordDecl>(
            *ast_ctx_,
            CppRecordKind::Class,
            lambda.closure_name(),
            std::vector<CppBaseSpecifier>{},
            std::vector<std::unique_ptr<Decl>>{},
            true,
            lambda.location);
    }

    auto* closure_owner = lambda.closure_semantic_owner();
    if (!closure_owner || !closure_owner->get_record_type()) {
        return fail(
            "internal error: lambda closure is missing a semantic record owner",
            lambda.location);
    }

    auto function_type = call_operator_type.as_shared<FunctionType>();
    if (!function_type || function_type->parameters.empty()) {
        return fail(
            "internal error: lambda call operator type is missing an implicit object parameter",
            lambda.location);
    }

    if (lambda.semantic_info.closure_record_decl) {
        lambda.semantic_info.closure_record_decl->members.clear();
    }
    lambda.semantic_info.capture_fields.clear();
    lambda.semantic_info.this_capture_field = nullptr;
    lambda.semantic_info.capture_initializers.clear();
    lambda.semantic_info.closure_initializer.reset();
    lambda.semantic_info.call_operator_symbol.reset();

    auto semantic_captures = build_lambda_semantic_captures(lambda);
    bool lambda_references_this = false;
    {
        std::vector<std::shared_ptr<Symbol>> referenced_symbols;
        std::unordered_set<const Symbol*> seen_symbols;
        collect_lambda_referenced_symbols_from_stmt(
            lambda.body.get(),
            referenced_symbols,
            seen_symbols,
            lambda_references_this);
    }
    bool has_this_capture = false;
    for (const auto& capture : semantic_captures) {
        if (capture.captures_this) {
            has_this_capture = true;
            break;
        }
    }
    if (lambda_references_this && !has_this_capture) {
        return fail(
            "lambda body references 'this' or a non-static member without capturing 'this'",
            lambda.location);
    }

    std::vector<ObjectType::Field> closure_fields;
    closure_fields.reserve(semantic_captures.size());
    std::unordered_map<const Symbol*, const FieldDecl*> capture_field_by_symbol;
    std::unordered_map<std::string, const FieldDecl*> capture_field_by_uid;
    const FieldDecl* this_capture_field = nullptr;
    std::string this_capture_field_name;

    for (const auto& capture : semantic_captures) {
        QualType field_type = nullptr;
        std::unique_ptr<Expr> capture_initializer;
        std::string field_name = capture.name;

        if (capture.captures_this) {
            const auto& lexical_this_context =
                lambda.semantic_info.lexical_this_context;
            if (!lexical_this_context.is_member_function ||
                lexical_this_context.is_static_member_function ||
                !lexical_this_context.this_type) {
                return fail(
                    "lambda capture 'this' is only valid in a non-static member function",
                    capture.location.isInvalid() ? lambda.location
                                                : capture.location);
            }
            field_type = lexical_this_context.this_type;
            field_name = "__lambda_this_capture";
            capture_initializer = collect_make<CppThisExpr>(
                lexical_this_context.this_type,
                capture.location.isInvalid() ? lambda.location
                                            : capture.location);
        } else if (capture.is_init_capture) {
            if (!capture.symbol) {
                return fail(
                    "lambda init-capture '" + capture.name +
                        "' does not have a synthesized local symbol",
                    capture.location);
            }
            if (!capture.initializer) {
                return fail(
                    "lambda init-capture '" + capture.name +
                        "' is missing an initializer",
                    capture.location);
            }
            field_type = capture.symbol->type;
            std::string init_clone_error;
            capture_initializer = clone_expr_tree(
                capture.initializer.get(),
                ast_ctx_.get(),
                &init_clone_error);
            if (!capture_initializer) {
                return fail(
                    init_clone_error.empty()
                        ? "failed to clone lambda init-capture initializer"
                        : init_clone_error,
                    capture.location);
            }
            if (capture.by_reference) {
                field_type = QualType(
                    std::make_shared<ReferenceType>(
                        remove_reference(field_type, ast_ctx_.get()),
                        ReferenceKind::LValue));
            } else {
                field_type = remove_reference(field_type, ast_ctx_.get());
            }
        } else if (!capture.symbol) {
            return fail(
                "lambda capture '" + capture.name + "' does not name a captured local entity",
                capture.location);
        } else {
            field_type = capture.symbol->type;
            if (capture.by_reference) {
                field_type = QualType(
                    std::make_shared<ReferenceType>(
                        remove_reference(field_type, ast_ctx_.get()),
                        ReferenceKind::LValue));
            } else {
                field_type = remove_reference(field_type, ast_ctx_.get());
            }
            capture_initializer =
                collect_make<VarRef>(capture.symbol, capture.location);
        }

        auto field_decl_base =
            collect_field_declaration(field_type, field_name, capture.location);
        auto* field_decl = dyn_cast<FieldDecl>(field_decl_base.get());
        if (!field_decl) {
            return fail(
                "internal error: lambda capture did not synthesize a field declaration",
                capture.location);
        }

        CppMemberDeclInfo field_member_info;
        field_member_info.declared_access =
            static_cast<uint8_t>(CppAccessSpecifier::Public);
        ast_ctx_->set_cpp_member_decl_info(field_decl->node_id, field_member_info);

        closure_fields.emplace_back(
            field_decl->name,
            field_decl->type,
            0,
            RecordMemberAccess::Public);
        lambda.semantic_info.capture_fields.push_back(field_decl);
        lambda.semantic_info.capture_initializers.push_back(
            std::move(capture_initializer));
        if (capture.captures_this) {
            this_capture_field = field_decl;
            this_capture_field_name = field_decl->name;
            lambda.semantic_info.this_capture_field = field_decl;
        } else {
            capture_field_by_symbol.emplace(capture.symbol.get(), field_decl);
        }
        if (capture.symbol && !capture.symbol->uid.empty()) {
            capture_field_by_uid.emplace(capture.symbol->uid, field_decl);
        }
        lambda.semantic_info.closure_record_decl->members.push_back(
            std::move(field_decl_base));
    }

    auto* closure_owner_type = closure_owner->get_record_type().get();
    CollectRecordBuildContext closure_ctx;
    closure_ctx.record = lambda.semantic_info.closure_record_decl.get();
    closure_ctx.loc = lambda.location;
    closure_ctx.record_name = lambda.closure_name();
    closure_ctx.tag = lambda.closure_name();
    closure_ctx.is_union_record = closure_owner_type->is_union;
    closure_ctx.record_type = closure_owner->get_record_type();
    closure_ctx.semantic_decl = closure_owner;
    closure_ctx.fields = std::move(closure_fields);
    closure_ctx.semantic_state.is_incomplete = false;
    collect_record_compute_layout(closure_ctx);
    collect_record_publish_semantics(closure_ctx);
    RecordSemanticState updated_state = std::move(closure_ctx.semantic_state);

    if (!lambda.semantic_info.capture_initializers.empty()) {
        auto init_list = collect_initializer_list_expression(lambda.location);
        ASTCloneContext init_clone_ctx;
        init_clone_ctx.ast_ctx = ast_ctx_.get();
        init_clone_ctx.finalize_lambda_expr =
            [this](CppLambdaExpr& nested_lambda,
                   std::string* nested_error_out) -> bool {
                return collect_finalize_cpp_lambda_expression(
                    nested_lambda,
                    nested_error_out);
            };
        for (const auto& capture_init : lambda.semantic_info.capture_initializers) {
            if (!capture_init) {
                continue;
            }
            std::string init_clone_error;
            auto cloned_init = clone_expr_with_substitution(
                capture_init.get(),
                init_clone_ctx,
                &init_clone_error);
            if (!cloned_init) {
                return fail(
                    init_clone_error.empty()
                        ? "failed to clone lambda capture initializer"
                        : init_clone_error,
                    capture_init->location);
            }

            InitElement element;
            element.loc = capture_init->location;
            element.value = std::move(cloned_init);
            init_list->elements.push_back(std::move(element));
        }
        lambda.semantic_info.closure_initializer = process_initializer_for_type(
            std::move(init_list),
            lambda.semantic_info.closure_type(),
            lambda.location);
        if (!lambda.semantic_info.closure_initializer) {
            return fail(
                "failed to build lambda closure initializer",
                lambda.location);
        }
    }

    ASTCloneContext clone_ctx;
    clone_ctx.ast_ctx = ast_ctx_.get();
    clone_ctx.preserve_unexpanded_pack_expansions = lambda.is_generic;
    clone_ctx.finalize_lambda_expr =
        [this](CppLambdaExpr& nested_lambda,
               std::string* nested_error_out) -> bool {
            return collect_finalize_cpp_lambda_expression(
                nested_lambda,
                nested_error_out);
        };
    clone_ctx.rewrite_var_ref =
        [&](const VarRef* var_ref, std::string* error_out)
        -> std::unique_ptr<Expr> {
            if (!var_ref || !var_ref->symref) {
                return nullptr;
            }
            auto capture_it = capture_field_by_symbol.find(var_ref->symref.get());
            if ((capture_it == capture_field_by_symbol.end() ||
                 !capture_it->second) &&
                !var_ref->symref->uid.empty()) {
                auto uid_it = capture_field_by_uid.find(var_ref->symref->uid);
                if (uid_it != capture_field_by_uid.end()) {
                    capture_it = capture_field_by_symbol.emplace(
                                     var_ref->symref.get(),
                                     uid_it->second)
                                     .first;
                }
            }
            if (capture_it == capture_field_by_symbol.end() || !capture_it->second) {
                return nullptr;
            }

            auto this_expr = collect_make<CppThisExpr>(
                function_type->parameters.front(),
                var_ref->location);
            auto member_expr = collect_member_expression(
                std::move(this_expr),
                capture_it->second->name,
                true,
                var_ref->location,
                false,
                false);
            if (!member_expr) {
                if (error_out) {
                    *error_out =
                        "failed to rewrite lambda capture reference '" +
                        var_ref->get_name() + "'";
                }
                return collect_make<ErrorExpr>(
                    "failed to rewrite lambda capture reference",
                    var_ref->location);
            }
            return member_expr;
        };
    clone_ctx.rewrite_expr =
        [&](std::unique_ptr<Expr>& expr, std::string* error_out) -> bool {
            if (this_capture_field_name.empty() || !this_capture_field) {
                return true;
            }
            auto* this_expr = dyn_cast<CppThisExpr>(expr.get());
            if (!this_expr) {
                return true;
            }
            if (!lambda.semantic_info.lexical_this_context.this_type ||
                !this_expr->this_type) {
                return true;
            }
            if (!lambda_enclosing_this_types_match(
                    this_expr->this_type,
                    lambda.semantic_info.lexical_this_context.this_type,
                    ast_ctx_.get())) {
                return true;
            }

            auto closure_this_expr = collect_make<CppThisExpr>(
                function_type->parameters.front(),
                this_expr->location);
            auto rewritten_this = collect_member_expression(
                std::move(closure_this_expr),
                this_capture_field_name,
                true,
                this_expr->location,
                false,
                false);
            if (!rewritten_this) {
                if (error_out) {
                    *error_out =
                        "failed to rewrite lambda enclosing 'this' capture";
                }
                return false;
            }
            expr = std::move(rewritten_this);
            return true;
        };

    std::vector<std::unique_ptr<Decl>> method_parameters;
    method_parameters.reserve(lambda.parameters.size() + 1);
    method_parameters.push_back(collect_parameter_declaration(
        function_type->parameters.front(),
        "this",
        nullptr,
        StorageClass::NONE,
        lambda.location));

    for (const auto& parameter : lambda.parameters) {
        std::string clone_error;
        auto cloned_parameter = clone_decl_tree(
            parameter.get(),
            clone_ctx,
            &clone_error);
        if (parameter && !cloned_parameter) {
            return fail(
                clone_error.empty()
                    ? "failed to clone lambda parameter for synthesized call operator"
                    : clone_error,
                parameter->location);
        }

        auto* original_param = dyn_cast<ParamDecl>(parameter.get());
        auto* cloned_param = dyn_cast<ParamDecl>(cloned_parameter.get());
        if (original_param && cloned_param) {
            if (const Expr* default_expr =
                    get_param_decl_default_argument(original_param)) {
                std::string default_clone_error;
                auto cloned_default = clone_expr_with_substitution(
                    default_expr,
                    clone_ctx,
                    &default_clone_error);
                if (!cloned_default) {
                    return fail(
                        default_clone_error.empty()
                            ? "failed to clone lambda default argument"
                            : default_clone_error,
                        default_expr->location);
                }
                if (!rewrite_expr_tree_in_place(
                        cloned_default,
                        clone_ctx,
                        &default_clone_error)) {
                    return fail(
                        default_clone_error.empty()
                            ? "failed to rewrite lambda default argument"
                            : default_clone_error,
                        default_expr->location);
                }
                set_param_decl_default_argument(
                    cloned_param,
                    std::move(cloned_default));
            }
        }

        method_parameters.push_back(std::move(cloned_parameter));
    }

    std::string body_clone_error;
    auto cloned_body_stmt = clone_stmt_tree(
        lambda.body.get(),
        clone_ctx,
        &body_clone_error);
    if (lambda.body && !dyn_cast<CompoundStmt>(cloned_body_stmt.get())) {
        return fail(
            body_clone_error.empty()
                ? "failed to clone lambda body for synthesized call operator"
                : body_clone_error,
            lambda.location);
    }
    if (cloned_body_stmt &&
        !rewrite_stmt_tree_in_place(
            cloned_body_stmt,
            clone_ctx,
            &body_clone_error)) {
        return fail(
            body_clone_error.empty()
                ? "failed to rewrite lambda body for synthesized call operator"
                : body_clone_error,
            lambda.location);
    }
    auto cloned_body = std::unique_ptr<CompoundStmt>(
        dyn_cast<CompoundStmt>(cloned_body_stmt.release()));

    auto synthesized_method = make_ast<CppMethodDecl>(
        *ast_ctx_,
        "operator()",
        call_operator_type.get_shared(),
        std::move(method_parameters),
        std::move(cloned_body),
        lambda.stmt_labels,
        StorageClass::NONE,
        true,
        lambda.location);
    synthesized_method->type = call_operator_type.get_shared();
    synthesized_method->is_constexpr =
        lambda.is_constexpr || lambda.is_consteval ||
        lang_opts_.is_cxx17_or_later();
    synthesized_method->is_consteval = lambda.is_consteval;
    synthesized_method->scope =
        synthesized_method->body
            ? dyn_cast<CompoundStmt>(synthesized_method->body.get())->scope
            : nullptr;
    synthesized_method->set_language_linkage(LanguageLinkage::None);
    auto clone_lambda_constraint =
        [&](const std::unique_ptr<Expr>& constraint,
            const char* description) -> std::unique_ptr<Expr> {
            if (!constraint) {
                return nullptr;
            }
            std::string clone_error;
            auto cloned_constraint =
                clone_expr_with_substitution(
                    constraint.get(),
                    clone_ctx,
                    &clone_error);
            if (!cloned_constraint) {
                fail(
                    clone_error.empty()
                        ? "failed to clone lambda " +
                              std::string(description) + " constraint"
                        : clone_error,
                    constraint->location.isInvalid()
                        ? lambda.location
                        : constraint->location);
            }
            return cloned_constraint;
        };
    if (lambda.trailing_requires_clause) {
        synthesized_method->trailing_requires_clause =
            clone_lambda_constraint(
                lambda.trailing_requires_clause,
                "trailing requires-clause");
        if (!synthesized_method->trailing_requires_clause) {
            return false;
        }
    }

    auto synthesized_method_type =
        QualType(synthesized_method->type).as_shared<FunctionType>();
    auto written_method_type =
        lambda.written_call_operator_type.as_shared<FunctionType>();
    bool needs_post_clone_auto_return_deduction =
        !lambda.is_generic &&
        synthesized_method_type &&
        auto_type_utils::has_cxx_auto_type(
            synthesized_method_type->ret_type.get_shared());
    bool should_finalize_cloned_body =
        !lambda.is_generic && synthesized_method->body != nullptr;
    if (should_finalize_cloned_body) {
        std::string finalize_error;
        if (!with_function_definition_state(
                synthesized_method.get(),
                [&]() {
                    return template_sema_internal::
                        finalize_specialized_stmt_semantics(
                            *this,
                            synthesized_method->body,
                            QualType(synthesized_method->type),
                            &finalize_error);
                })) {
            return fail(
                finalize_error.empty()
                    ? "failed to finalize cloned lambda body after substitution"
                    : finalize_error,
                lambda.location);
        }
        synthesized_method->scope =
            synthesized_method->body
                ? dyn_cast<CompoundStmt>(synthesized_method->body.get())->scope
                : nullptr;
        if (needs_post_clone_auto_return_deduction && written_method_type) {
            written_method_type->ret_type = synthesized_method_type->ret_type;
        }
    }

    set_func_decl_cxx_qualifier_prefix(
        synthesized_method.get(),
        lambda.closure_name());
    set_func_decl_owner_record_type(
        synthesized_method.get(),
        lambda.semantic_info.closure_type());

    CppMemberDeclInfo member_info;
    member_info.declared_access =
        static_cast<uint8_t>(CppAccessSpecifier::Public);
    member_info.is_method = true;
    member_info.is_constexpr = synthesized_method->is_constexpr;
    member_info.is_consteval = synthesized_method->is_consteval;
    ast_ctx_->set_cpp_member_decl_info(synthesized_method->node_id, member_info);

    lambda.semantic_info.call_operator_decl = synthesized_method.get();
    lambda.semantic_info.call_operator_template = nullptr;

    std::shared_ptr<Symbol> synthesized_symbol = nullptr;
    if (!lambda.is_generic) {
        synthesized_symbol = collect_declare_function_symbol(
            synthesized_method->name,
            QualType(synthesized_method->type),
            synthesized_method->storage_class,
            synthesized_method->is_constexpr,
            synthesized_method->is_consteval,
            synthesized_method->is_inline,
            synthesized_method->body != nullptr,
            synthesized_method->location,
            synthesized_method->get_language_linkage(),
            true,
            false,
            false,
            lambda.semantic_info.closure_type(),
            lambda.closure_name());
        if (synthesized_symbol) {
            set_symbol_cxx_qualifier_prefix(
                synthesized_symbol.get(),
                lambda.closure_name());
            set_symbol_owner_record_type(
                synthesized_symbol.get(),
                lambda.semantic_info.closure_type());
            collect_record_register_function_default_arguments(
                synthesized_symbol,
                synthesized_method.get(),
                synthesized_method->location);
            if (synthesized_method->body) {
                synthesized_symbol->function_definition =
                    synthesized_method.get();
            }
        }
        lambda.semantic_info.call_operator_symbol = synthesized_symbol;

        RecordSemanticState::Method semantic_method;
        semantic_method.name = synthesized_method->name;
        semantic_method.type = QualType(synthesized_method->type);
        semantic_method.declared_access = RecordMemberAccess::Public;
        semantic_method.is_static = false;
        semantic_method.is_virtual = false;
        semantic_method.is_override = false;
        semantic_method.is_final = false;
        semantic_method.is_pure = false;
        semantic_method.decl = synthesized_method.get();
        semantic_method.symbol = synthesized_symbol;
        updated_state.methods.push_back(std::move(semantic_method));
        lambda.semantic_info.closure_record_decl->members.push_back(
            std::move(synthesized_method));
    } else {
        if (lambda.call_operator_template_parameters.empty()) {
            return fail(
                "internal error: generic lambda is missing synthesized template parameters",
                lambda.location);
        }

        auto function_template = make_ast<FunctionTemplateDecl>(
            *ast_ctx_,
            std::move(lambda.call_operator_template_parameters),
            std::move(synthesized_method),
            lambda.location);
        if (lambda.template_requires_clause) {
            function_template->associated_constraint =
                clone_lambda_constraint(
                    lambda.template_requires_clause,
                    "template requires-clause");
            if (!function_template->associated_constraint) {
                return false;
            }
        }
        set_template_decl_canonical_decl(
            function_template.get(),
            function_template.get());

        RecordSemanticState::MethodTemplate semantic_method_template;
        semantic_method_template.name = "operator()";
        semantic_method_template.declared_access =
            RecordMemberAccess::Public;
        semantic_method_template.is_static = false;
        semantic_method_template.decl = function_template.get();
        updated_state.method_templates.push_back(
            std::move(semantic_method_template));

        lambda.semantic_info.call_operator_decl =
            function_template->function_decl();
        lambda.semantic_info.call_operator_template = function_template.get();
        lambda.semantic_info.closure_record_decl->members.push_back(
            std::move(function_template));
    }
    collect_record_publish_state(
        closure_owner,
        closure_owner->get_record_type(),
        updated_state);

    bool has_syntactic_captures =
        lambda.closure_info.default_capture != CppLambdaCaptureDefault::None ||
        !lambda.closure_info.captures.empty() ||
        !semantic_captures.empty();

    lambda.semantic_info.function_pointer_invoker_decl.reset();
    if (!lambda.is_generic && !has_syntactic_captures) {
        auto invoker_type = std::make_shared<FunctionType>();
        invoker_type->ret_type = function_type->ret_type;
        invoker_type->parameters.reserve(function_type->parameters.size() - 1);
        invoker_type->parameter_pack_flags.reserve(
            function_type->parameters.size() - 1);
        for (size_t index = 1; index < function_type->parameters.size();
             ++index) {
            invoker_type->push_parameter(
                function_type->parameters[index],
                function_type->parameter_is_pack(index));
        }
        invoker_type->is_variadic = function_type->is_variadic;
        invoker_type->has_prototype = function_type->has_prototype;
        invoker_type->has_explicit_exception_spec =
            function_type->has_explicit_exception_spec;
        invoker_type->exception_spec = function_type->exception_spec;
        invoker_type->exception_spec_expr = function_type->exception_spec_expr;

        std::vector<std::unique_ptr<Decl>> invoker_parameters;
        invoker_parameters.reserve(lambda.parameters.size());
        for (size_t index = 0; index < lambda.parameters.size(); ++index) {
            auto* original_param =
                dyn_cast<ParamDecl>(lambda.parameters[index].get());
            std::string param_name =
                original_param ? original_param->get_name() : "";
            QualType param_type =
                index + 1 < function_type->parameters.size()
                    ? function_type->parameters[index + 1]
                    : (original_param ? original_param->type : QualType());
            invoker_parameters.push_back(collect_parameter_declaration(
                param_type,
                param_name,
                nullptr,
                StorageClass::NONE,
                lambda.parameters[index]
                    ? lambda.parameters[index]->location
                    : lambda.location));
        }

        auto invoker_decl = make_ast<FuncDecl>(
            *ast_ctx_,
            "__invoke",
            invoker_type,
            std::move(invoker_parameters),
            nullptr,
            std::unordered_set<std::string>{},
            StorageClass::STATIC,
            true,
            lambda.location);
        invoker_decl->type = invoker_type;
        invoker_decl->set_language_linkage(LanguageLinkage::None);
        set_func_decl_cxx_qualifier_prefix(
            invoker_decl.get(),
            lambda.closure_name());
        set_func_decl_owner_record_type(
            invoker_decl.get(),
            lambda.semantic_info.closure_type());

        CppLambdaInvokerInfo invoker_info;
        invoker_info.closure_type = lambda.semantic_info.closure_type();
        invoker_info.call_operator_decl = lambda.semantic_info.call_operator_decl;
        ast_ctx_->set_cpp_lambda_invoker_info(
            invoker_decl->node_id,
            std::move(invoker_info));
        lambda.semantic_info.function_pointer_invoker_decl =
            std::move(invoker_decl);
    }

    CppLambdaClosureDeclInfo closure_decl_info;
    closure_decl_info.call_operator_decl = lambda.semantic_info.call_operator_decl;
    closure_decl_info.call_operator_template =
        lambda.semantic_info.call_operator_template;
    closure_decl_info.function_pointer_invoker_decl =
        lambda.semantic_info.function_pointer_invoker_decl.get();
    closure_decl_info.has_syntactic_captures = has_syntactic_captures;
    ast_ctx_->set_cpp_lambda_closure_decl_info(
        closure_owner->node_id,
        std::move(closure_decl_info));
    return true;
}

bool Collect::collect_finalize_cpp_lambda_expression(CppLambdaExpr& lambda,
                                                     std::string* error_out) {
    return finalize_cpp_lambda_semantics(lambda, error_out);
}

bool Collect::collect_finalize_block_expression(BlockExpr& block,
                                                std::string* error_out) {
    auto fail = [&](const std::string& message, SrcLoc loc) -> bool {
        report_error(message, loc);
        if (error_out && error_out->empty()) {
            *error_out = message;
        }
        return false;
    };

    if (!ast_ctx_) {
        return false;
    }

    if (!block.semantic_info.literal_record()) {
        block.semantic_info = make_block_semantic_info(*ast_ctx_, block.location);
    }

    auto invoke_type = build_block_invoke_type(block, error_out);
    if (!invoke_type) {
        return fail(
            error_out && !error_out->empty()
                ? *error_out
                : "internal error: failed to build block invoke type",
            block.location);
    }

    auto* literal_record = block.semantic_info.literal_record();
    if (!literal_record || !literal_record->get_record_type()) {
        return fail(
            "internal error: block literal is missing a synthesized record owner",
            block.location);
    }

    literal_record->fields.clear();
    block.semantic_info.captures.clear();

    auto void_type = QualType(get_builtin_void());
    auto int_type = QualType(get_builtin_int());
    auto void_ptr_type = QualType(std::make_shared<PointerType>(void_type));
    auto invoke_ptr_type = QualType(std::make_shared<PointerType>(invoke_type));

    std::vector<ObjectType::Field> literal_fields;
    auto append_literal_field =
        [&](QualType field_type, const std::string& field_name, SrcLoc loc)
        -> FieldDecl* {
            auto field_decl_base =
                collect_field_declaration(field_type, field_name, loc);
            auto* field_decl = dyn_cast<FieldDecl>(field_decl_base.get());
            if (!field_decl) {
                return nullptr;
            }
            literal_fields.emplace_back(field_decl->name, field_decl->type, 0);
            literal_record->fields.push_back(std::move(field_decl_base));
            return field_decl;
        };

    if (!append_literal_field(void_ptr_type, "__isa", block.location) ||
        !append_literal_field(int_type, "__flags", block.location) ||
        !append_literal_field(int_type, "__reserved", block.location) ||
        !append_literal_field(invoke_ptr_type, "__invoke", block.location) ||
        !append_literal_field(void_ptr_type, "__descriptor", block.location)) {
        return fail(
            "internal error: failed to synthesize block literal header fields",
            block.location);
    }

    auto captures = build_block_semantic_captures(block, ast_ctx_.get());
    for (size_t index = 0; index < captures.size(); ++index) {
        auto& capture = captures[index];
        capture.location = capture.symbol ? capture.symbol->variable_definition
                                               ? capture.symbol->variable_definition->location
                                               : block.location
                                          : block.location;
        QualType field_type =
            remove_reference(capture.symbol ? capture.symbol->type : QualType(),
                             ast_ctx_.get());
        if (capture.kind == BlockCaptureKind::ByRef) {
            field_type = QualType(
                void_ptr_type.get_shared(),
                static_cast<uint8_t>(void_ptr_type.get_qualifiers() | QUAL_CONST));
        } else if (!field_type) {
            return fail(
                "internal error: block capture '" + capture.name +
                    "' is missing a valid type",
                block.location);
        }
        field_type = QualType(
            field_type.get_shared(),
            static_cast<uint8_t>(field_type.get_qualifiers() | QUAL_CONST));
        capture.capture_type = field_type;
        std::string field_name =
            "__capture_" + capture.name + "_" + std::to_string(index);
        auto* field_decl =
            append_literal_field(field_type, field_name, capture.location);
        if (!field_decl) {
            return fail(
                "internal error: failed to synthesize block capture field '" +
                    capture.name + "'",
                capture.location);
        }
        capture.field = field_decl;
        block.semantic_info.captures.push_back(std::move(capture));
    }

    auto* literal_type = literal_record->get_record_type().get();
    CollectRecordBuildContext literal_ctx;
    literal_ctx.loc = block.location;
    literal_ctx.record_name = block.semantic_info.literal_name();
    literal_ctx.tag = literal_record->tag;
    literal_ctx.is_union_record = literal_type->is_union;
    literal_ctx.record_type = literal_record->get_record_type();
    literal_ctx.semantic_decl = literal_record;
    literal_ctx.fields = std::move(literal_fields);
    literal_ctx.semantic_state.is_incomplete = false;
    collect_record_compute_layout(literal_ctx);
    collect_record_publish_semantics(literal_ctx);

    auto* invoke_function_type =
        invoke_type.as_shared<FunctionType>().get();
    if (!invoke_function_type || invoke_function_type->parameters.empty()) {
        return fail(
            "internal error: invalid synthesized block invoke type",
            block.location);
    }

    auto hidden_param_sym = std::make_shared<Symbol>(
        "__block_literal",
        SymbolKind::VARIABLE,
        invoke_function_type->parameters.front(),
        StorageClass::NONE,
        VariableLinkage::NONE);
    hidden_param_sym->uid =
        block.semantic_info.literal_name() + "::__block_literal";

    std::vector<std::unique_ptr<Decl>> invoke_parameters;
    invoke_parameters.reserve(block.parameters.size() + 1);
    invoke_parameters.push_back(collect_parameter_declaration(
        invoke_function_type->parameters.front(),
        "__block_literal",
        hidden_param_sym,
        StorageClass::NONE,
        block.location));

    bool has_void_parameter =
        block.parameters.size() == 1 &&
        block.parameters.front() &&
        dyn_cast<ParamDecl>(block.parameters.front().get()) &&
        dyn_cast<ParamDecl>(block.parameters.front().get())->type &&
        dyn_cast<ParamDecl>(block.parameters.front().get())->type->isVoid();

    ASTCloneContext clone_ctx;
    clone_ctx.ast_ctx = ast_ctx_.get();
    clone_ctx.finalize_lambda_expr =
        [this](CppLambdaExpr& nested_lambda,
               std::string* nested_error_out) -> bool {
            return collect_finalize_cpp_lambda_expression(
                nested_lambda,
                nested_error_out);
        };
    clone_ctx.finalize_block_expr =
        [this](BlockExpr& nested_block,
               std::string* nested_error_out) -> bool {
            return collect_finalize_block_expression(
                nested_block,
                nested_error_out);
        };
    clone_ctx.rewrite_var_ref =
        [&](const VarRef* var_ref, std::string* rewrite_error_out)
        -> std::unique_ptr<Expr> {
            if (!var_ref || !var_ref->symref) {
                return nullptr;
            }
            for (const auto& capture : block.semantic_info.captures) {
                if (!capture.symbol || capture.symbol.get() != var_ref->symref.get() ||
                    !capture.field) {
                    continue;
                }
                auto base_expr = collect_make<VarRef>(hidden_param_sym, var_ref->location);
                auto member_expr = collect_member_expression(
                    std::move(base_expr),
                    capture.field->name,
                    true,
                    var_ref->location,
                    false,
                    false);
                if (!member_expr && rewrite_error_out) {
                    *rewrite_error_out =
                        "failed to rewrite block capture reference '" +
                        var_ref->get_name() + "'";
                }
                if (!member_expr) {
                    return member_expr;
                }
                if (capture.kind == BlockCaptureKind::ByRef) {
                    return collect_make<BlockByrefAccessExpr>(
                        std::move(member_expr),
                        capture.symbol,
                        capture.symbol->type,
                        var_ref->location);
                }
                return member_expr;
            }
            return nullptr;
        };

    if (!has_void_parameter) {
        for (const auto& parameter : block.parameters) {
            std::string clone_error;
            auto cloned_parameter = clone_decl_tree(
                parameter.get(),
                clone_ctx,
                &clone_error);
            if (parameter && !cloned_parameter) {
                return fail(
                    clone_error.empty()
                        ? "failed to clone block parameter for synthesized invoke function"
                        : clone_error,
                    parameter->location);
            }
            invoke_parameters.push_back(std::move(cloned_parameter));
        }
    }

    std::string body_clone_error;
    auto cloned_body_stmt = clone_stmt_tree(
        block.body.get(),
        clone_ctx,
        &body_clone_error);
    if (block.body && !dyn_cast<CompoundStmt>(cloned_body_stmt.get())) {
        return fail(
            body_clone_error.empty()
                ? "failed to clone block body for synthesized invoke function"
                : body_clone_error,
            block.location);
    }
    if (cloned_body_stmt &&
        !rewrite_stmt_tree_in_place(
            cloned_body_stmt,
            clone_ctx,
            &body_clone_error)) {
        return fail(
            body_clone_error.empty()
                ? "failed to rewrite block body for synthesized invoke function"
                : body_clone_error,
            block.location);
    }
    auto cloned_body = std::unique_ptr<CompoundStmt>(
        dyn_cast<CompoundStmt>(cloned_body_stmt.release()));

    auto invoke_decl = make_ast<FuncDecl>(
        *ast_ctx_,
        "__invoke",
        invoke_type.get_shared(),
        std::move(invoke_parameters),
        std::move(cloned_body),
        block.stmt_labels,
        StorageClass::STATIC,
        true,
        block.location);
    invoke_decl->type = invoke_type.get_shared();
    invoke_decl->scope =
        invoke_decl->body
            ? dyn_cast<CompoundStmt>(invoke_decl->body.get())->scope
            : nullptr;
    invoke_decl->set_asm_label(
        "__block_invoke_" + block.semantic_info.literal_name());
    invoke_decl->set_language_linkage(LanguageLinkage::None);
    if (invoke_decl->body) {
        std::string finalize_error;
        if (!with_function_definition_state(
                invoke_decl.get(),
                [&]() {
                    return template_sema_internal::
                        finalize_specialized_stmt_semantics(
                            *this,
                            invoke_decl->body,
                            QualType(invoke_decl->type),
                            &finalize_error);
                })) {
            return fail(
                finalize_error.empty()
                    ? "failed to finalize synthesized block invoke body"
                    : finalize_error,
                block.location);
        }
        invoke_decl->scope =
            invoke_decl->body
                ? dyn_cast<CompoundStmt>(invoke_decl->body.get())->scope
                : nullptr;
    }

    set_func_decl_owner_record_type(
        invoke_decl.get(),
        block.semantic_info.literal_type());
    block.semantic_info.invoke_decl = std::move(invoke_decl);
    return true;
}

std::unique_ptr<Expr> Collect::collect_cpp_lambda_expression(
    LambdaClosureInfo closure_info,
    LambdaSemanticInfo semantic_info,
    QualType written_call_operator_type,
    TemplateParameterList call_operator_template_parameters,
    std::unique_ptr<Expr> template_requires_clause,
    std::unique_ptr<Expr> trailing_requires_clause,
    std::vector<std::unique_ptr<Decl>> parameters,
    std::unique_ptr<CompoundStmt> body,
    std::unordered_set<std::string> stmt_labels,
    QualType explicit_return_type,
    bool has_parameter_clause,
    bool is_mutable,
    bool is_constexpr,
    bool is_consteval,
    bool has_noexcept,
    bool has_trailing_return,
    bool is_generic,
    SrcLoc loc) {
    auto lambda = collect_make<CppLambdaExpr>(
        std::move(closure_info),
        std::move(semantic_info),
        std::move(written_call_operator_type),
        std::move(call_operator_template_parameters),
        std::move(template_requires_clause),
        std::move(trailing_requires_clause),
        std::move(parameters),
        std::move(body),
        std::move(stmt_labels),
        std::move(explicit_return_type),
        has_parameter_clause,
        is_mutable,
        is_constexpr,
        is_consteval,
        has_noexcept,
        has_trailing_return,
        is_generic,
        loc);
    collect_finalize_cpp_lambda_expression(*lambda, nullptr);
    return lambda;
}

std::unique_ptr<Expr> Collect::collect_block_expression(
    BlockSemanticInfo semantic_info,
    QualType block_type,
    std::vector<std::unique_ptr<Decl>> parameters,
    std::unique_ptr<CompoundStmt> body,
    std::unordered_set<std::string> stmt_labels,
    QualType explicit_return_type,
    bool has_parameter_clause,
    bool has_explicit_return_type,
    SrcLoc loc) {
    auto block = collect_make<BlockExpr>(
        std::move(semantic_info),
        std::move(block_type),
        std::move(parameters),
        std::move(body),
        std::move(stmt_labels),
        std::move(explicit_return_type),
        has_parameter_clause,
        has_explicit_return_type,
        loc);
    collect_finalize_block_expression(*block, nullptr);
    return block;
}


std::unique_ptr<Expr> Collect::collect_compound_literal_expression(QualType type, std::unique_ptr<Expr> init, SrcLoc loc) {
    if (type && contains_deferred_semantic_type(type.get_shared())) {
        type = resolve_typeof_types(type, loc);
    }

    if (!type) {
        report_error("compound literal has unknown type", loc);
    } else if (type->isIncomplete() && canonical_type_kind(type) != TypeKind::Array) {
        report_error("compound literal has incomplete type", loc);
    }
    if (init) {
        type = clone_top_level_incomplete_array(type);
        init = process_initializer_for_type(std::move(init), type, loc);
    }
    auto node = collect_make<CompoundLiteralExpr>(std::move(type), std::move(init), loc);
    node->has_static_storage = !session_.func_state_.in_function;
    return node;
}


std::unique_ptr<Expr> Collect::collect_label_address_expression(const std::string& label, SrcLoc loc) {

    collect_register_label_reference(label, loc);
    auto void_ty = QualType(get_builtin_void());
    auto ptr_ty = QualType(std::make_shared<PointerType>(void_ty));
    return collect_make<LabelAddressExpr>(label, ptr_ty, loc);
}


std::unique_ptr<Expr> Collect::collect_va_arg_expression(std::unique_ptr<Expr> va_list_expr, QualType arg_type, SrcLoc loc) {

    if (arg_type && contains_deferred_semantic_type(arg_type.get_shared())) {
        arg_type = resolve_typeof_types(arg_type, loc);
    }
    if (!arg_type) {
        report_error("__builtin_va_arg requires a valid type argument", loc);
        return collect_make<ErrorExpr>("invalid __builtin_va_arg type", loc);
    }
    if (canonical_type_kind(arg_type) == TypeKind::Function) {
        report_error("__builtin_va_arg cannot use function type", loc);
    }
    if (auto builtin = arg_type.as_shared<BuiltinType>()) {
        switch (builtin->builtin_kind) {
            case BuiltinTypes::Char:
            case BuiltinTypes::SChar:
            case BuiltinTypes::UChar:
            case BuiltinTypes::Char16:
            case BuiltinTypes::Short:
            case BuiltinTypes::UShort:
                report_warning(
                    "second argument to 'va_arg' is of promotable integer type; this va_arg has undefined behavior",
                    loc);
                break;
            case BuiltinTypes::Float:
                report_warning(
                    "second argument to 'va_arg' is 'float'; this va_arg has undefined behavior because arguments are promoted to 'double'",
                    loc);
                break;
            default:
                break;
        }
    }
    return collect_make<VaArgExpr>(std::move(va_list_expr), arg_type, loc);
}


std::unique_ptr<Expr> Collect::collect_builtin_types_compatible_expression(QualType lhs, QualType rhs, SrcLoc loc) {

    if (lhs && contains_deferred_semantic_type(lhs.get_shared())) {
        lhs = resolve_typeof_types(lhs, loc);
    }
    if (rhs && contains_deferred_semantic_type(rhs.get_shared())) {
        rhs = resolve_typeof_types(rhs, loc);
    }

    std::vector<std::unique_ptr<Expr>> args;
    std::vector<QualType> type_args = {lhs, rhs};
    auto node = collect_make<BuiltinCallExpr>(BuiltinKind::TYPES_COMPATIBLE_P,
        std::move(args), std::move(type_args), QualType(get_builtin_int()), loc);
    bool compatible = false;
    auto enum_int_compatible = [](QualType enum_ty, QualType int_ty) -> bool {
        auto* en = enum_ty.as<EnumType>();
        auto* bi = int_ty.as<BuiltinType>();
        if (!en || !bi) {
            return false;
        }
        auto underlying = en->semantic_underlying_type();
        if (!underlying) {
            return false;
        }
        return QualType(underlying).equals_unqualified(int_ty);
    };
    if (lhs && rhs) {
        auto lhs_canonical = desugar_type(lhs);
        auto rhs_canonical = desugar_type(rhs);
        // GNU-family semantics ignore qualifiers on the compared type itself
        // while still considering qualifiers nested within the type, such as
        // pointee qualifiers for pointer types.
        auto lhs_compare = lhs_canonical.without_qualifiers();
        auto rhs_compare = rhs_canonical.without_qualifiers();
        if (lhs_compare->kind == TypeKind::Array &&
            rhs_compare->kind == TypeKind::Array) {
            auto lhs_arr = lhs_compare.as_shared<ArrayType>();
            auto rhs_arr = rhs_compare.as_shared<ArrayType>();
            bool elem_compatible = lhs_arr && rhs_arr &&
                lhs_arr->element_type.equals_qualified(rhs_arr->element_type);
            if (elem_compatible) {
                bool lhs_const = lhs_arr->size_kind == ArraySizeKind::Constant && lhs_arr->size.has_value();
                bool rhs_const = rhs_arr->size_kind == ArraySizeKind::Constant && rhs_arr->size.has_value();
                compatible = !(lhs_const && rhs_const) || lhs_arr->size == rhs_arr->size;
            }
        } else if (lhs_compare->kind == TypeKind::Pointer &&
                   rhs_compare->kind == TypeKind::Pointer) {
            compatible = lhs_compare.equals_qualified(rhs_compare);
        } else {
            compatible = lhs_compare.equals_qualified(rhs_compare) ||
                enum_int_compatible(lhs_compare, rhs_compare) ||
                enum_int_compatible(rhs_compare, lhs_compare);
        }
    }
    node->const_value = compatible ? 1 : 0;
    return node;
}

std::optional<bool> Collect::evaluate_builtin_type_trait(
    BuiltinKind kind,
    const std::vector<QualType>& type_args,
    SrcLoc loc) {
    auto trait_source_value_category = [&](QualType source_type) {
        auto source_canonical = desugar_type(source_type, ast_ctx_.get());
        auto ref_type = source_canonical.as_shared<ReferenceType>();
        if (!ref_type) {
            return ValueCategory::PRValue;
        }
        return ref_type->isLValueReference()
            ? ValueCategory::LValue
            : ValueCategory::XValue;
    };

    auto materialize_trait_source_type = [&](QualType source_type) {
        return remove_reference(source_type, ast_ctx_.get());
    };

    auto get_canonical_arg = [&](size_t index) -> std::optional<QualType> {
        if (index >= type_args.size() || !type_args[index]) {
            report_error("builtin type trait is missing a type operand", loc);
            return std::nullopt;
        }
        QualType type_arg = type_args[index];
        if (contains_deferred_semantic_type(type_arg.get_shared())) {
            type_arg = finalize_deferred_semantic_type(type_arg, loc);
            if (!type_arg) {
                report_error(
                    "builtin type trait operand could not be resolved",
                    loc);
                return std::nullopt;
            }
        }
        if (type_depends_on_template_parameters(type_arg, ast_ctx_.get())) {
            return std::nullopt;
        }
        return desugar_type(type_arg, ast_ctx_.get());
    };

    std::function<bool(QualType, QualType)> trait_is_convertible_to_target;
    std::function<bool(QualType, QualType)> trait_is_core_convertible_to_target;

    auto trait_reference_binding_viable = [&](QualType from_type,
                                             QualType to_type) -> bool {
        auto to_ref = desugar_type(to_type, ast_ctx_.get()).as_shared<ReferenceType>();
        if (!to_ref || !to_ref->referred_type) {
            return false;
        }

        QualType source_type = materialize_trait_source_type(from_type);
        QualType target_type = to_ref->referred_type;
        QualType canonical_source_type = desugar_type(source_type, ast_ctx_.get());
        QualType canonical_target_type = desugar_type(target_type, ast_ctx_.get());
        auto source_category = trait_source_value_category(from_type);

        auto direct_binding_matches = [&]() -> bool {
            bool same_qualified_type =
                source_type.equals_qualified(target_type) ||
                (canonical_source_type &&
                 canonical_target_type &&
                 canonical_source_type.equals_qualified(canonical_target_type)) ||
                types_equivalent_after_template_argument_canonicalization(
                    source_type,
                    target_type,
                    ast_ctx_.get(),
                    /*ignore_top_level_qualifiers=*/false);
            if (same_qualified_type) {
                return true;
            }
            bool same_unqualified_type =
                source_type.equals_unqualified(target_type) ||
                (canonical_source_type &&
                 canonical_target_type &&
                 canonical_source_type.equals_unqualified(canonical_target_type)) ||
                types_equivalent_after_template_argument_canonicalization(
                    source_type,
                    target_type,
                    ast_ctx_.get(),
                    /*ignore_top_level_qualifiers=*/true);
            if (same_unqualified_type &&
                target_type.has_all_qualifiers_of(source_type)) {
                return true;
            }
            return can_convert_derived_to_base_object(source_type, target_type);
        };

        auto temporary_binding_matches = [&]() -> bool {
            return build_implicit_conversion_sequence(
                       source_type,
                       target_type,
                       ExprUseContext::CallArgument)
                .viable;
        };

        if (to_ref->isLValueReference()) {
            if (source_category == ValueCategory::LValue) {
                if (direct_binding_matches()) {
                    return true;
                }
                return target_type.is_const() && temporary_binding_matches();
            }
            if (!target_type.is_const()) {
                return false;
            }
            return direct_binding_matches() || temporary_binding_matches();
        }

        if (source_category == ValueCategory::LValue) {
            return false;
        }
        return direct_binding_matches() || temporary_binding_matches();
    };

    auto trait_record_constructible_from =
        [&](QualType target_type,
            const std::vector<QualType>& argument_types,
            bool allow_explicit_constructors,
            bool require_nothrow,
            bool require_trivial) -> bool {
            auto object_type =
                desugar_type(target_type, ast_ctx_.get()).as_shared<ObjectType>();
            if (!object_type) {
                return false;
            }
            const auto* record_decl = canonical_record_decl(
                dyn_cast<ObjectDecl>(object_type->get_decl()));
            if (!record_decl) {
                return false;
            }
            const auto* state = query_lookup_record_semantics(record_decl);
            if (!state || state->is_incomplete) {
                return false;
            }

            auto ctor_matches_requirements =
                [&](const RecordSemanticState::Constructor& ctor) -> bool {
                    if (ctor.is_deleted ||
                        !cpp_access_allows_member(
                            ctor.declared_access,
                            /*allow_protected_access=*/false)) {
                        return false;
                    }
                    if (!allow_explicit_constructors && ctor.is_explicit) {
                        return false;
                    }
                    auto fn_type =
                        desugar_type(ctor.type, ast_ctx_.get()).as_shared<FunctionType>();
                    if (!fn_type) {
                        return false;
                    }
                    if (require_nothrow &&
                        fn_type->exception_spec !=
                            FunctionExceptionSpecKind::NonThrowing) {
                        return false;
                    }
                    if (require_trivial) {
                        bool trivial_ctor = ctor.is_implicit;
                        if (!trivial_ctor &&
                            ctor.decl &&
                            ctor.decl->is_defaulted &&
                            (cpp_constructor_is_copy_constructor(
                                 ctor,
                                 target_type,
                                 ast_ctx_.get()) ||
                             cpp_constructor_is_move_constructor(
                                 ctor,
                                 target_type,
                                 ast_ctx_.get()) ||
                             cpp_compute_constructor_user_param_info(ctor)
                                     .required_user_param_count == 0)) {
                            trivial_ctor = true;
                        }
                        if (!trivial_ctor) {
                            return false;
                        }
                    }

                    CppConstructorUserParamInfo info =
                        cpp_compute_constructor_user_param_info(ctor);
                    if (argument_types.size() < info.required_user_param_count ||
                        argument_types.size() > info.max_user_param_count) {
                        return false;
                    }

                    for (size_t index = 0; index < argument_types.size(); ++index) {
                        size_t param_index = info.user_param_start + index;
                        if (param_index >= fn_type->parameters.size()) {
                            return false;
                        }
                        if (!trait_is_convertible_to_target(
                                argument_types[index],
                                fn_type->parameters[param_index])) {
                            return false;
                        }
                    }
                    return true;
                };

            if (argument_types.empty()) {
                if (!cpp_record_has_viable_default_constructor(
                        state,
                        /*allow_protected_access=*/false)) {
                    return false;
                }
                if (!require_nothrow && !require_trivial) {
                    return true;
                }
                for (const auto& ctor : state->constructors) {
                    if (ctor_matches_requirements(ctor)) {
                        return true;
                    }
                }
                return false;
            }

            for (const auto& ctor : state->constructors) {
                if (ctor_matches_requirements(ctor)) {
                    return true;
                }
            }
            return false;
        };

    std::function<bool(QualType,
                       const std::vector<QualType>&,
                       bool,
                       bool)> trait_is_constructible_from;
    trait_is_constructible_from =
        [&](QualType target_type,
            const std::vector<QualType>& argument_types,
            bool require_nothrow,
            bool require_trivial) -> bool {
            if (!target_type) {
                return false;
            }

            QualType canonical_target = desugar_type(target_type, ast_ctx_.get());
            if (!canonical_target) {
                return false;
            }

            if (canonical_target->kind == TypeKind::Reference) {
                return argument_types.size() == 1 &&
                       trait_reference_binding_viable(
                           argument_types.front(),
                           canonical_target);
            }

            if (canonical_target->isVoid() ||
                canonical_target->kind == TypeKind::Function) {
                return false;
            }

            if (canonical_target->kind == TypeKind::Array) {
                auto array_type = canonical_target.as_shared<ArrayType>();
                if (!array_type ||
                    array_type->size_kind != ArraySizeKind::Constant ||
                    !array_type->size.has_value()) {
                    return false;
                }
                return argument_types.empty() &&
                       trait_is_constructible_from(
                           array_type->element_type,
                           {},
                           require_nothrow,
                           require_trivial);
            }

            if (canonical_target->kind == TypeKind::Object) {
                return trait_record_constructible_from(
                    canonical_target,
                    argument_types,
                    /*allow_explicit_constructors=*/true,
                    require_nothrow,
                    require_trivial);
            }

            if (argument_types.empty()) {
                if (target_type.is_const()) {
                    return false;
                }
                return canonical_target->isScalar() ||
                       canonical_target->kind == TypeKind::Complex ||
                       canonical_target->kind == TypeKind::Vector;
            }

            if (argument_types.size() != 1) {
                return false;
            }

            if (require_trivial &&
                canonical_target->kind == TypeKind::Object) {
                return false;
            }

            return trait_is_convertible_to_target(
                argument_types.front(),
                canonical_target);
        };

    trait_is_convertible_to_target =
        [&](QualType from_type, QualType to_type) -> bool {
            if (!from_type || !to_type) {
                return false;
            }

            QualType source_type = materialize_trait_source_type(from_type);
            QualType canonical_source = desugar_type(source_type, ast_ctx_.get());
            QualType canonical_target = desugar_type(to_type, ast_ctx_.get());
            if (!canonical_source || !canonical_target) {
                return false;
            }

            if (canonical_target->kind == TypeKind::Reference) {
                return trait_reference_binding_viable(from_type, to_type);
            }

            if (canonical_target->isVoid()) {
                return true;
            }
            if (canonical_source->isVoid()) {
                return false;
            }

            if (canonical_target->kind == TypeKind::Object) {
                return trait_record_constructible_from(
                    canonical_target,
                    {from_type},
                    /*allow_explicit_constructors=*/false,
                    /*require_nothrow=*/false,
                    /*require_trivial=*/false);
            }

            return build_implicit_conversion_sequence(
                       source_type,
                       canonical_target,
                       ExprUseContext::CallArgument)
                .viable;
        };

    trait_is_core_convertible_to_target =
        [&](QualType from_type, QualType to_type) -> bool {
            if (!from_type || !to_type) {
                return false;
            }

            QualType source_type = materialize_trait_source_type(from_type);
            QualType canonical_source = desugar_type(source_type, ast_ctx_.get());
            QualType canonical_target = desugar_type(to_type, ast_ctx_.get());
            if (!canonical_source || !canonical_target) {
                return false;
            }

            if (canonical_target->kind == TypeKind::Reference) {
                return trait_reference_binding_viable(from_type, to_type);
            }

            // libc++ uses this builtin to model the "pass the result to a
            // function parameter" form, where any void involvement is
            // immediately ill-formed.
            if (canonical_source->isVoid() || canonical_target->isVoid()) {
                return false;
            }

            if (canonical_target->kind == TypeKind::Object) {
                bool same_unqualified_type =
                    source_type.equals_unqualified(to_type) ||
                    canonical_source.equals_unqualified(canonical_target);
                if (same_unqualified_type) {
                    return true;
                }
                if (can_convert_derived_to_base_object(source_type, to_type)) {
                    return true;
                }
                return trait_record_constructible_from(
                    canonical_target,
                    {from_type},
                    /*allow_explicit_constructors=*/false,
                    /*require_nothrow=*/false,
                    /*require_trivial=*/false);
            }

            return trait_is_convertible_to_target(from_type, to_type);
        };

    auto trait_scalar_assignable_to_target =
        [&](QualType rhs_type, QualType target_type) -> bool {
            if (!rhs_type || !target_type) {
                return false;
            }
            QualType rhs_expression_type =
                materialize_trait_source_type(rhs_type);
            if (!rhs_expression_type) {
                return false;
            }
            auto rhs_expression_kind =
                canonical_type_kind(rhs_expression_type, ast_ctx_.get());
            auto target_kind =
                canonical_type_kind(target_type, ast_ctx_.get());
            if (rhs_expression_type->isVoid() ||
                target_type->isVoid() ||
                rhs_expression_kind == TypeKind::Function ||
                target_kind == TypeKind::Function ||
                target_kind == TypeKind::Array) {
                return false;
            }
            return build_implicit_conversion_sequence(
                       rhs_expression_type,
                       target_type,
                       ExprUseContext::CallArgument)
                .viable;
        };

    std::function<bool(QualType)> trait_is_standard_layout_type;
    std::function<bool(QualType)> trait_is_trivial_type;
    std::function<bool(QualType)> trait_is_trivially_copyable_type;
    std::function<bool(QualType)> trait_has_unique_object_representations_type;
    std::function<bool(QualType)> trait_is_pod_type;

    trait_is_standard_layout_type = [&](QualType type_arg) -> bool {
        if (!type_arg) {
            return false;
        }
        QualType canonical = desugar_type(type_arg, ast_ctx_.get());
        if (!canonical) {
            return false;
        }
        if (canonical->isVoid()) {
            return false;
        }
        switch (canonical->kind) {
            case TypeKind::Function:
            case TypeKind::Reference:
                return false;
            case TypeKind::Array: {
                auto array_type = canonical.as_shared<ArrayType>();
                return array_type &&
                       trait_is_standard_layout_type(array_type->element_type);
            }
            case TypeKind::Object: {
                auto object_type = canonical.as_shared<ObjectType>();
                if (!object_type) {
                    return false;
                }
                const auto* record_decl = canonical_record_decl(
                    dyn_cast<ObjectDecl>(object_type->get_decl()));
                if (!record_decl) {
                    return false;
                }
                const auto* state = query_lookup_record_semantics(record_decl);
                if (!state || state->is_incomplete) {
                    return false;
                }
                if (state->is_polymorphic || !state->virtual_bases.empty()) {
                    return false;
                }
                for (const auto& base : state->bases) {
                    if (base.is_virtual ||
                        base.declared_access != RecordMemberAccess::Public) {
                        return false;
                    }
                }
                return true;
            }
            default:
                return canonical->isScalar() || canonical->kind == TypeKind::Complex;
        }
    };

    trait_is_trivial_type = [&](QualType type_arg) -> bool {
        if (!type_arg) {
            return false;
        }
        QualType canonical = desugar_type(type_arg, ast_ctx_.get());
        if (!canonical) {
            return false;
        }
        if (canonical->isVoid()) {
            return false;
        }
        switch (canonical->kind) {
            case TypeKind::Reference:
            case TypeKind::Function:
                return false;
            case TypeKind::Array: {
                auto array_type = canonical.as_shared<ArrayType>();
                return array_type &&
                       array_type->size_kind == ArraySizeKind::Constant &&
                       array_type->size.has_value() &&
                       trait_is_trivial_type(array_type->element_type);
            }
            case TypeKind::Object: {
                auto object_type = canonical.as_shared<ObjectType>();
                if (!object_type) {
                    return false;
                }
                const auto* record_decl = canonical_record_decl(
                    dyn_cast<ObjectDecl>(object_type->get_decl()));
                if (!record_decl) {
                    return false;
                }
                const auto* state = query_lookup_record_semantics(record_decl);
                if (!state || state->is_incomplete) {
                    return false;
                }
                return trait_is_standard_layout_type(canonical) &&
                       trait_is_constructible_from(
                           canonical,
                           {},
                           /*require_nothrow=*/false,
                           /*require_trivial=*/true) &&
                       trait_is_trivially_copyable_type(canonical) &&
                       cpp_type_is_trivially_destructible(canonical, ast_ctx_.get());
            }
            default:
                return canonical->isScalar() || canonical->kind == TypeKind::Complex;
        }
    };

    trait_is_trivially_copyable_type = [&](QualType type_arg) -> bool {
        if (!type_arg) {
            return false;
        }

        QualType canonical = desugar_type(type_arg, ast_ctx_.get());
        if (!canonical) {
            return false;
        }
        if (canonical->isVoid()) {
            return false;
        }

        switch (canonical->kind) {
            case TypeKind::Reference:
            case TypeKind::Function:
                return false;
            case TypeKind::Array: {
                auto array_type = canonical.as_shared<ArrayType>();
                if (!array_type ||
                    array_type->size_kind != ArraySizeKind::Constant ||
                    !array_type->size.has_value()) {
                    return false;
                }
                return trait_is_trivially_copyable_type(array_type->element_type);
            }
            case TypeKind::Object: {
                auto object_type = canonical.as_shared<ObjectType>();
                if (!object_type) {
                    return false;
                }
                const auto* record_decl = canonical_record_decl(
                    dyn_cast<ObjectDecl>(object_type->get_decl()));
                if (!record_decl) {
                    return false;
                }
                const auto* state = query_lookup_record_semantics(record_decl);
                if (!state || state->is_incomplete) {
                    return false;
                }
                if (state->is_polymorphic || !state->virtual_bases.empty()) {
                    return false;
                }
                if (!cpp_type_is_trivially_destructible(canonical, ast_ctx_.get())) {
                    return false;
                }

                for (const auto& ctor : state->constructors) {
                    if (!cpp_constructor_is_copy_constructor(
                            ctor,
                            canonical,
                            ast_ctx_.get()) &&
                        !cpp_constructor_is_move_constructor(
                            ctor,
                            canonical,
                            ast_ctx_.get())) {
                        continue;
                    }
                    if (ctor.is_deleted) {
                        return false;
                    }
                    if (!ctor.is_implicit &&
                        (!ctor.decl || !ctor.decl->is_defaulted)) {
                        return false;
                    }
                }

                for (const auto& method : state->methods) {
                    if (!cpp_method_is_copy_assignment(
                            method,
                            canonical,
                            ast_ctx_.get()) &&
                        !cpp_method_is_move_assignment(
                            method,
                            canonical,
                            ast_ctx_.get())) {
                        continue;
                    }
                    if (method.is_deleted) {
                        return false;
                    }
                    if (!method.is_implicit &&
                        (!method.decl || !method.decl->is_defaulted)) {
                        return false;
                    }
                }

                for (const auto& base : state->bases) {
                    if (!trait_is_trivially_copyable_type(base.type)) {
                        return false;
                    }
                }
                for (const auto& field : state->fields) {
                    if (field.is_base_subobject || field.is_virtual_base_storage) {
                        continue;
                    }
                    if (!trait_is_trivially_copyable_type(field.type)) {
                        return false;
                    }
                }
                return true;
            }
            default:
                return canonical->isScalar() || canonical->kind == TypeKind::Complex;
        }
    };

    trait_has_unique_object_representations_type =
        [&](QualType type_arg) -> bool {
            if (!type_arg) {
                return false;
            }
            QualType canonical = desugar_type(type_arg, ast_ctx_.get());
            if (!canonical) {
                return false;
            }

            switch (canonical->kind) {
                case TypeKind::Array: {
                    auto array_type = canonical.as_shared<ArrayType>();
                    return array_type &&
                           trait_has_unique_object_representations_type(
                               array_type->element_type);
                }
                case TypeKind::Enum: {
                    auto enum_type = canonical.as_shared<EnumType>();
                    return enum_type &&
                           trait_has_unique_object_representations_type(
                               QualType(enum_type->semantic_underlying_type()));
                }
                case TypeKind::Builtin: {
                    auto builtin = canonical.as_shared<BuiltinType>();
                    return builtin &&
                           builtin->builtin_kind != BuiltinTypes::Bool &&
                           builtin->isInteger();
                }
                default:
                    return false;
            }
        };

    trait_is_pod_type = [&](QualType type_arg) -> bool {
        return trait_is_standard_layout_type(type_arg) &&
               trait_is_trivial_type(type_arg);
    };

    switch (kind) {
        case BuiltinKind::IS_SAME: {
            auto lhs = get_canonical_arg(0);
            auto rhs = get_canonical_arg(1);
            if (!lhs || !rhs) {
                return std::nullopt;
            }
            return lhs->equals_qualified(*rhs);
        }
        case BuiltinKind::IS_FUNCTION: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            return type_arg->get()->kind == TypeKind::Function;
        }
        case BuiltinKind::IS_REFERENCE: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            return type_arg->as_shared<ReferenceType>() != nullptr;
        }
        case BuiltinKind::IS_LVALUE_REFERENCE: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            auto ref_type = type_arg->as_shared<ReferenceType>();
            return ref_type && ref_type->isLValueReference();
        }
        case BuiltinKind::IS_RVALUE_REFERENCE: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            auto ref_type = type_arg->as_shared<ReferenceType>();
            return ref_type && ref_type->isRValueReference();
        }
        case BuiltinKind::HAS_VIRTUAL_DESTRUCTOR: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            auto object_type = type_arg->as_shared<ObjectType>();
            if (!object_type || object_type->is_union) {
                return false;
            }
            const auto* record_decl = canonical_record_decl(
                dyn_cast<ObjectDecl>(object_type->get_decl()));
            if (!record_decl) {
                return false;
            }
            const auto* state = query_lookup_record_semantics(record_decl);
            return state && state->has_virtual_destructor;
        }
        case BuiltinKind::IS_ABSTRACT: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            auto object_type = type_arg->as_shared<ObjectType>();
            if (!object_type || object_type->is_union) {
                return false;
            }
            const auto* record_decl = canonical_record_decl(
                dyn_cast<ObjectDecl>(object_type->get_decl()));
            if (!record_decl) {
                return false;
            }
            const auto* state = query_lookup_record_semantics(record_decl);
            return state && state->is_abstract;
        }
        case BuiltinKind::IS_ARRAY: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            return canonical_type_kind(*type_arg, ast_ctx_.get()) == TypeKind::Array;
        }
        case BuiltinKind::IS_UNION: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            auto object_type = type_arg->as_shared<ObjectType>();
            return object_type && object_type->is_union;
        }
        case BuiltinKind::IS_VOLATILE: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            return !type_arg->as_shared<ReferenceType>() && type_arg->is_volatile();
        }
        case BuiltinKind::IS_CONST: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            return !type_arg->as_shared<ReferenceType>() && type_arg->is_const();
        }
        case BuiltinKind::IS_EMPTY: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            auto object_type = type_arg->as_shared<ObjectType>();
            if (!object_type || object_type->is_union) {
                return false;
            }
            const auto* record_decl = canonical_record_decl(
                dyn_cast<ObjectDecl>(object_type->get_decl()));
            if (!record_decl) {
                return false;
            }
            const auto* state = query_lookup_record_semantics(record_decl);
            if (!state || state->is_incomplete) {
                return false;
            }
            return !state->is_polymorphic &&
                   state->bases.empty() &&
                   state->virtual_bases.empty() &&
                   state->fields.empty();
        }
        case BuiltinKind::IS_ENUM: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            return canonical_type_kind(*type_arg, ast_ctx_.get()) == TypeKind::Enum;
        }
        case BuiltinKind::IS_SCOPED_ENUM: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            return is_scoped_enum_type(*type_arg, ast_ctx_.get());
        }
        case BuiltinKind::IS_FUNDAMENTAL: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            return (*type_arg)->isVoid() ||
                   (*type_arg)->isArithmetic() ||
                   is_nullptr_type(*type_arg, ast_ctx_.get());
        }
        case BuiltinKind::IS_INTEGRAL: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            auto canonical = desugar_type(*type_arg, ast_ctx_.get());
            if (!canonical) {
                return false;
            }
            if (auto builtin = canonical.as_shared<BuiltinType>()) {
                return builtin->isInteger();
            }
            return false;
        }
        case BuiltinKind::IS_UNSIGNED: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            auto canonical = desugar_type(*type_arg, ast_ctx_.get());
            if (!canonical) {
                return false;
            }
            if (auto builtin = canonical.as_shared<BuiltinType>()) {
                return builtin->isInteger() &&
                       builtin->builtin_kind != BuiltinTypes::Bool &&
                       builtin->isUnsigned();
            }
            if (auto enum_type = canonical.as_shared<EnumType>()) {
                QualType underlying(enum_type->semantic_underlying_type());
                auto builtin = underlying.as_shared<BuiltinType>();
                return builtin && builtin->isInteger() && builtin->isUnsigned();
            }
            return false;
        }
        case BuiltinKind::IS_ASSIGNABLE: {
            auto lhs = get_canonical_arg(0);
            auto rhs = get_canonical_arg(1);
            if (!lhs || !rhs) {
                return std::nullopt;
            }
            auto lhs_ref = lhs->as_shared<ReferenceType>();
            if (!lhs_ref || !lhs_ref->isLValueReference()) {
                return false;
            }
            QualType target_type = lhs_ref->referred_type;
            if (!target_type || target_type.is_const()) {
                return false;
            }
            auto target_kind = canonical_type_kind(target_type, ast_ctx_.get());
            if (target_type->isVoid() || target_kind == TypeKind::Function ||
                target_kind == TypeKind::Array) {
                return false;
            }
            if (target_kind == TypeKind::Object) {
                auto target_object =
                    desugar_type(target_type, ast_ctx_.get()).as_shared<ObjectType>();
                const auto* record_decl = canonical_record_decl(
                    dyn_cast<ObjectDecl>(target_object ? target_object->get_decl()
                                                       : nullptr));
                const auto* state =
                    record_decl ? query_lookup_record_semantics(record_decl) : nullptr;
                if (!state || state->is_incomplete) {
                    return false;
                }

                bool rhs_is_lvalue = false;
                if (auto rhs_ref = rhs->as_shared<ReferenceType>()) {
                    rhs_is_lvalue = rhs_ref->isLValueReference();
                }
                const RecordSemanticState::Method* selected_method = nullptr;
                if (!rhs_is_lvalue) {
                    for (const auto& method : state->methods) {
                        if (cpp_method_is_move_assignment(
                                method,
                                target_type,
                                ast_ctx_.get())) {
                            selected_method = &method;
                            break;
                        }
                    }
                }
                if (!selected_method) {
                    for (const auto& method : state->methods) {
                        if (cpp_method_is_copy_assignment(
                                method,
                                target_type,
                                ast_ctx_.get())) {
                            selected_method = &method;
                            break;
                        }
                    }
                }
                return selected_method &&
                       !selected_method->is_deleted &&
                       cpp_access_allows_member(
                           selected_method->declared_access,
                           /*allow_protected_access=*/false);
            }
            return trait_scalar_assignable_to_target(*rhs, target_type);
        }
        case BuiltinKind::IS_TRIVIALLY_ASSIGNABLE:
        case BuiltinKind::IS_NOTHROW_ASSIGNABLE: {
            auto lhs = get_canonical_arg(0);
            auto rhs = get_canonical_arg(1);
            if (!lhs || !rhs) {
                return std::nullopt;
            }
            auto lhs_ref = lhs->as_shared<ReferenceType>();
            if (!lhs_ref || !lhs_ref->isLValueReference()) {
                return false;
            }
            QualType target_type = lhs_ref->referred_type;
            if (!target_type || target_type.is_const()) {
                return false;
            }
            auto target_kind = canonical_type_kind(target_type, ast_ctx_.get());
            if (target_type->isVoid() || target_kind == TypeKind::Function ||
                target_kind == TypeKind::Array) {
                return false;
            }
            if (target_kind == TypeKind::Object) {
                auto target_object =
                    desugar_type(target_type, ast_ctx_.get()).as_shared<ObjectType>();
                const auto* record_decl = canonical_record_decl(
                    dyn_cast<ObjectDecl>(target_object ? target_object->get_decl()
                                                       : nullptr));
                const auto* state =
                    record_decl ? query_lookup_record_semantics(record_decl) : nullptr;
                if (!state || state->is_incomplete) {
                    return false;
                }

                bool rhs_is_lvalue = false;
                if (auto rhs_ref = rhs->as_shared<ReferenceType>()) {
                    rhs_is_lvalue = rhs_ref->isLValueReference();
                }
                const RecordSemanticState::Method* selected_method = nullptr;
                if (!rhs_is_lvalue) {
                    for (const auto& method : state->methods) {
                        if (cpp_method_is_move_assignment(
                                method,
                                target_type,
                                ast_ctx_.get())) {
                            selected_method = &method;
                            break;
                        }
                    }
                }
                if (!selected_method) {
                    for (const auto& method : state->methods) {
                        if (cpp_method_is_copy_assignment(
                                method,
                                target_type,
                                ast_ctx_.get())) {
                            selected_method = &method;
                            break;
                        }
                    }
                }
                if (!selected_method ||
                    selected_method->is_deleted ||
                    !cpp_access_allows_member(
                        selected_method->declared_access,
                        /*allow_protected_access=*/false)) {
                    return false;
                }
                if (kind == BuiltinKind::IS_TRIVIALLY_ASSIGNABLE) {
                    return trait_is_trivially_copyable_type(target_type);
                }
                auto fn_type =
                    desugar_type(selected_method->type, ast_ctx_.get())
                        .as_shared<FunctionType>();
                return fn_type &&
                       fn_type->exception_spec ==
                           FunctionExceptionSpecKind::NonThrowing;
            }
            bool assignable =
                trait_scalar_assignable_to_target(*rhs, target_type);
            if (!assignable) {
                return false;
            }
            if (kind == BuiltinKind::IS_TRIVIALLY_ASSIGNABLE &&
                target_kind == TypeKind::Object) {
                return false;
            }
            return true;
        }
        case BuiltinKind::IS_BASE_OF: {
            auto base = get_canonical_arg(0);
            auto derived = get_canonical_arg(1);
            if (!base || !derived) {
                return std::nullopt;
            }
            auto base_object = base->as_shared<ObjectType>();
            auto derived_object = derived->as_shared<ObjectType>();
            if (!base_object || !derived_object ||
                base_object->is_union || derived_object->is_union) {
                return false;
            }
            const auto* base_decl = canonical_record_decl(
                dyn_cast<ObjectDecl>(base_object->get_decl()));
            const auto* derived_decl = canonical_record_decl(
                dyn_cast<ObjectDecl>(derived_object->get_decl()));
            if (!base_decl || !derived_decl) {
                return false;
            }
            return is_same_record_or_any_access_derived(derived_decl, base_decl);
        }
        case BuiltinKind::IS_CLASS: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            auto object_type = type_arg->as_shared<ObjectType>();
            return object_type && !object_type->is_union;
        }
        case BuiltinKind::IS_FINAL: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            auto object_type = type_arg->as_shared<ObjectType>();
            if (!object_type) {
                return false;
            }
            const auto* record_decl = canonical_record_decl(
                dyn_cast<ObjectDecl>(object_type->get_decl()));
            if (!record_decl) {
                return false;
            }
            const auto* state = query_lookup_record_semantics(record_decl);
            return state && !state->is_incomplete && state->is_final;
        }
        case BuiltinKind::IS_MEMBER_POINTER: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            return canonical_type_kind(*type_arg, ast_ctx_.get()) ==
                TypeKind::MemberPointer;
        }
        case BuiltinKind::IS_MEMBER_OBJECT_POINTER:
        case BuiltinKind::IS_MEMBER_FUNCTION_POINTER: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            auto member_ptr =
                desugar_type(*type_arg, ast_ctx_.get()).as_shared<MemberPointerType>();
            if (!member_ptr || !member_ptr->member_type) {
                return false;
            }
            bool member_is_function =
                canonical_type_kind(member_ptr->member_type, ast_ctx_.get()) ==
                TypeKind::Function;
            return kind == BuiltinKind::IS_MEMBER_FUNCTION_POINTER
                ? member_is_function
                : !member_is_function;
        }
        case BuiltinKind::IS_NULL_POINTER: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            return is_nullptr_type(*type_arg, ast_ctx_.get());
        }
        case BuiltinKind::IS_OBJECT: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            return !(*type_arg)->isVoid() &&
                   canonical_type_kind(*type_arg, ast_ctx_.get()) != TypeKind::Function &&
                   canonical_type_kind(*type_arg, ast_ctx_.get()) != TypeKind::Reference;
        }
        case BuiltinKind::IS_POINTER: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            return canonical_type_kind(*type_arg, ast_ctx_.get()) == TypeKind::Pointer;
        }
        case BuiltinKind::IS_POLYMORPHIC: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            auto object_type = type_arg->as_shared<ObjectType>();
            if (!object_type || object_type->is_union) {
                return false;
            }
            const auto* record_decl = canonical_record_decl(
                dyn_cast<ObjectDecl>(object_type->get_decl()));
            if (!record_decl) {
                return false;
            }
            const auto* state = query_lookup_record_semantics(record_decl);
            return state && state->is_polymorphic;
        }
        case BuiltinKind::IS_STANDARD_LAYOUT: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            return trait_is_standard_layout_type(*type_arg);
        }
        case BuiltinKind::IS_TRIVIAL: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            return trait_is_trivial_type(*type_arg);
        }
        case BuiltinKind::IS_TRIVIALLY_COPYABLE: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            return trait_is_trivially_copyable_type(*type_arg);
        }
        case BuiltinKind::HAS_UNIQUE_OBJECT_REPRESENTATIONS: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            return trait_has_unique_object_representations_type(*type_arg);
        }
        case BuiltinKind::IS_POD: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            return trait_is_pod_type(*type_arg);
        }
        case BuiltinKind::IS_SIGNED: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            auto canonical = desugar_type(*type_arg, ast_ctx_.get());
            if (!canonical) {
                return false;
            }
            if (auto builtin = canonical.as_shared<BuiltinType>()) {
                if (builtin->isFloatingPoint()) {
                    return true;
                }
                return builtin->isInteger() &&
                       builtin->builtin_kind != BuiltinTypes::Bool &&
                       !builtin->isUnsigned();
            }
            if (auto enum_type = canonical.as_shared<EnumType>()) {
                QualType underlying(enum_type->semantic_underlying_type());
                auto builtin = underlying.as_shared<BuiltinType>();
                return builtin && builtin->isInteger() && !builtin->isUnsigned();
            }
            return false;
        }
        case BuiltinKind::IS_CONSTRUCTIBLE:
        case BuiltinKind::IS_TRIVIALLY_CONSTRUCTIBLE:
        case BuiltinKind::IS_NOTHROW_CONSTRUCTIBLE: {
            auto target_type = get_canonical_arg(0);
            if (!target_type) {
                return std::nullopt;
            }
            std::vector<QualType> argument_types;
            argument_types.reserve(type_args.size() > 0 ? type_args.size() - 1 : 0);
            for (size_t index = 1; index < type_args.size(); ++index) {
                auto argument_type = get_canonical_arg(index);
                if (!argument_type) {
                    return std::nullopt;
                }
                argument_types.push_back(*argument_type);
            }
            return trait_is_constructible_from(
                *target_type,
                argument_types,
                kind == BuiltinKind::IS_NOTHROW_CONSTRUCTIBLE,
                kind == BuiltinKind::IS_TRIVIALLY_CONSTRUCTIBLE);
        }
        case BuiltinKind::IS_CONVERTIBLE:
        case BuiltinKind::IS_NOTHROW_CONVERTIBLE: {
            auto from_type = get_canonical_arg(0);
            auto to_type = get_canonical_arg(1);
            if (!from_type || !to_type) {
                return std::nullopt;
            }
            bool convertible = trait_is_convertible_to_target(*from_type, *to_type);
            if (!convertible) {
                return false;
            }
            if (kind == BuiltinKind::IS_NOTHROW_CONVERTIBLE) {
                auto target_object =
                    desugar_type(*to_type, ast_ctx_.get()).as_shared<ObjectType>();
                if (!target_object) {
                    return true;
                }
                return trait_record_constructible_from(
                    *to_type,
                    {*from_type},
                    /*allow_explicit_constructors=*/false,
                    /*require_nothrow=*/true,
                    /*require_trivial=*/false);
            }
            return true;
        }
        case BuiltinKind::IS_CORE_CONVERTIBLE: {
            auto from_type = get_canonical_arg(0);
            auto to_type = get_canonical_arg(1);
            if (!from_type || !to_type) {
                return std::nullopt;
            }
            return trait_is_core_convertible_to_target(*from_type, *to_type);
        }
        case BuiltinKind::IS_DESTRUCTIBLE: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            return cpp_type_is_destructible(*type_arg, false, ast_ctx_.get());
        }
        case BuiltinKind::IS_TRIVIALLY_DESTRUCTIBLE:
        case BuiltinKind::HAS_TRIVIAL_DESTRUCTOR: {
            auto type_arg = get_canonical_arg(0);
            if (!type_arg) {
                return std::nullopt;
            }
            return cpp_type_is_trivially_destructible(
                *type_arg, ast_ctx_.get());
        }
        default:
            return std::nullopt;
    }
}

std::unique_ptr<Expr> Collect::collect_builtin_type_trait_expression(
    BuiltinKind kind,
    std::vector<QualType> type_args,
    SrcLoc loc) {
    for (auto& type_arg : type_args) {
        if (type_arg &&
            contains_deferred_semantic_type(type_arg.get_shared())) {
            type_arg = resolve_typeof_types(type_arg, loc);
        }
    }

    std::vector<std::unique_ptr<Expr>> args;
    auto bool_type = QualType(get_builtin_bool());
    auto node = collect_make<BuiltinCallExpr>(
        kind,
        std::move(args),
        std::move(type_args),
        bool_type,
        loc);
    if (auto value =
            evaluate_builtin_type_trait(node->kind, node->type_args, loc)) {
        node->const_value = *value ? 1 : 0;
    }
    return node;
}


std::unique_ptr<Expr> Collect::collect_builtin_choose_expression(std::unique_ptr<Expr> const_expr, std::unique_ptr<Expr> true_expr, std::unique_ptr<Expr> false_expr, SrcLoc loc) const {

    if (!const_expr) {
        report_error("__builtin_choose_expr requires a constant first argument", loc);
        return collect_make<ErrorExpr>("__builtin_choose_expr requires constant expression", loc);
    }
    const_expr = collect_apply_standard_conversions(std::move(const_expr), ExprUseContext::ConditionalOperand);
    ConstEvalResult const_eval = evaluate_with_consteval_compat(
        const_expr.get(), ConstEvalMode::c_ice());
    if (const_eval.status != ConstEvalStatus::Constant || !const_eval.int_value.has_value()) {
        report_error(
            "__builtin_choose_expr first argument must be a compile-time integer constant expression: " +
                describe_consteval_failure(const_eval),
            loc);
        return collect_make<ErrorExpr>("__builtin_choose_expr requires constant expression", loc);
    }
    if (*const_eval.int_value != 0) {
        if (!true_expr) {
            report_error("__builtin_choose_expr selected missing true branch", loc);
            return collect_make<ErrorExpr>("invalid __builtin_choose_expr true branch", loc);
        }
        return std::move(true_expr);
    }
    if (!false_expr) {
        report_error("__builtin_choose_expr selected missing false branch", loc);
        return collect_make<ErrorExpr>("invalid __builtin_choose_expr false branch", loc);
    }
    return std::move(false_expr);
}

std::unique_ptr<Expr> Collect::collect_builtin_convertvector_expression(std::unique_ptr<Expr> vector_expr, QualType target_type, SrcLoc loc) {

    if (target_type && contains_deferred_semantic_type(target_type.get_shared())) {
        target_type = resolve_typeof_types(target_type, loc);
    }
    vector_expr = collect_apply_standard_conversions(std::move(vector_expr), ExprUseContext::CallArgument);

    QualType source_type = vector_expr ? vector_expr->get_type() : QualType();
    auto source_vector = desugar_type(source_type).as_shared<VectorType>();
    auto target_vector = desugar_type(target_type).as_shared<VectorType>();
    if (!source_vector) {
        report_error("__builtin_convertvector first argument must be a vector type", loc);
        return collect_make<ErrorExpr>("invalid __builtin_convertvector argument", loc);
    }
    if (!target_vector) {
        report_error("__builtin_convertvector second argument must be a vector type", loc);
        return collect_make<ErrorExpr>("invalid __builtin_convertvector type argument", loc);
    }
    if (source_vector->num_elements != target_vector->num_elements) {
        report_error("__builtin_convertvector source and destination vectors must have the same number of elements", loc);
        return collect_make<ErrorExpr>("mismatched __builtin_convertvector element counts", loc);
    }

    std::vector<std::unique_ptr<Expr>> args;
    args.push_back(std::move(vector_expr));
    std::vector<QualType> type_args = {target_type};
    return collect_make<BuiltinCallExpr>(
        BuiltinKind::CONVERTVECTOR, std::move(args), std::move(type_args), target_type, loc);
}


std::unique_ptr<Expr> Collect::collect_offsetof_expression(QualType type_operand, const std::string& member_name, std::vector<OffsetOfComponent> designator_path, SrcLoc loc) {
    auto node = collect_make<OffsetOfExpr>(type_operand, member_name, loc);
    node->designator_path = std::move(designator_path);
    node->result_type = QualType(get_builtin_ulong());
    return finalize_offsetof_node(std::move(node), loc);
}

std::unique_ptr<Expr> Collect::finalize_offsetof_node(
    std::unique_ptr<OffsetOfExpr> node,
    SrcLoc loc) {
    if (!node) {
        return nullptr;
    }

    auto size_t_type = get_builtin_ulong();
    node->result_type = size_t_type ? QualType(size_t_type) : QualType(get_builtin_int());
    if (!node->type_operand) {
        report_error("__builtin_offsetof requires a class/struct/union type", loc);
        return node;
    }

    if (type_depends_on_template_parameters(node->type_operand, ast_ctx_.get())) {
        return node;
    }

    QualType type_operand = finalize_deferred_semantic_type(node->type_operand, loc);
    if (!type_operand ||
        type_depends_on_template_parameters(type_operand, ast_ctx_.get())) {
        node->type_operand = type_operand ? type_operand : node->type_operand;
        return node;
    }
    type_operand = desugar_type(type_operand, ast_ctx_.get());
    node->type_operand = type_operand;

    auto object_type = type_operand.as_shared<ObjectType>();
    if (!object_type) {
        report_error("__builtin_offsetof requires a class/struct/union type", loc);
        return node;
    }
    if (object_type->isIncomplete()) {
        report_error("__builtin_offsetof requires a complete class/struct/union type", loc);
        return node;
    }

    object_type->getWidth();

    FieldLookupResult lookup;
    std::vector<uint32_t> path;
    find_field_recursive(object_type.get(), node->member_name, path, 0, lookup);
    if (lookup.matches == 0 || lookup.field == nullptr) {
        report_error("no member named '" + node->member_name + "' in class/struct/union", loc);
        return node;
    }
    if (lookup.matches > 1) {
        report_error("member '" + node->member_name + "' is ambiguous in __builtin_offsetof", loc);
        return node;
    }

    int64_t offset = static_cast<int64_t>(lookup.byte_offset);
    QualType current_type = lookup.field->type;
    std::unique_ptr<Expr> dynamic_offset_expr;

    auto add_runtime_offset = [&](std::unique_ptr<Expr> term) {
        if (!term) {
            return;
        }
        if (!dynamic_offset_expr) {
            dynamic_offset_expr = std::move(term);
            return;
        }
        dynamic_offset_expr = collect_binary_operation(
            std::move(dynamic_offset_expr), std::move(term), BinOpTypes::ADD, loc);
    };

    for (auto& comp : node->designator_path) {
        current_type = desugar_type(current_type);
        if (comp.array_index >= 0 || comp.array_index_expr) {
            auto arr = current_type.as_shared<ArrayType>();
            if (!arr) {
                report_error("array designator in __builtin_offsetof applied to non-array type", loc);
                return node;
            }
            int64_t elem_size = arr->element_type->getWidthBytes();
            if (elem_size < 0) {
                report_error("array designator in __builtin_offsetof has incomplete element type", loc);
                return node;
            }
            if (comp.array_index_expr) {
                if (expression_depends_on_template_parameters(
                        comp.array_index_expr.get()) ||
                    type_depends_on_template_parameters(
                        comp.array_index_expr->get_type(),
                        ast_ctx_.get())) {
                    return node;
                }
                auto idx_val = try_evaluate_with_consteval_compat(
                    comp.array_index_expr.get(), ConstEvalMode::c_ice());
                if (idx_val.has_value()) {
                    offset += *idx_val * elem_size;
                    comp.array_index = *idx_val;
                    comp.array_index_expr.reset();
                    current_type = arr->element_type;
                    continue;
                }
                auto scale = collect_integer_literal(
                    std::to_string(elem_size), get_builtin_ulong(), loc);
                auto term = collect_binary_operation(
                    std::move(comp.array_index_expr), std::move(scale), BinOpTypes::MULT, loc);
                add_runtime_offset(std::move(term));
            } else {
                offset += comp.array_index * elem_size;
            }
            current_type = arr->element_type;
            continue;
        }
        if (!comp.field_name.empty()) {
            auto nested_obj = current_type.as_shared<ObjectType>();
            if (!nested_obj || nested_obj->isIncomplete()) {
                report_error("field designator in __builtin_offsetof applied to non-class/struct/union type", loc);
                return node;
            }
            nested_obj->getWidth();
            FieldLookupResult nested_lookup;
            std::vector<uint32_t> nested_path;
            find_field_recursive(nested_obj.get(), comp.field_name, nested_path, 0, nested_lookup);
            if (nested_lookup.matches == 0 || nested_lookup.field == nullptr) {
                report_error("no member named '" + comp.field_name + "' in nested class/struct/union", loc);
                return node;
            }
            if (nested_lookup.matches > 1) {
                report_error("member '" + comp.field_name + "' is ambiguous in __builtin_offsetof", loc);
                return node;
            }
            offset += static_cast<int64_t>(nested_lookup.byte_offset);
            current_type = nested_lookup.field->type;
        }
    }

    if (dynamic_offset_expr) {
        if (offset != 0) {
            add_runtime_offset(collect_integer_literal(
                std::to_string(offset), get_builtin_ulong(), loc));
        }
        return collect_explicit_cast(std::move(dynamic_offset_expr), QualType(get_builtin_ulong()), loc);
    }

    node->computed_offset = offset;
    return node;
}

std::unique_ptr<Expr> Collect::collect_explicit_cast(std::unique_ptr<Expr> expr, QualType target_type, SrcLoc loc) {

    if (target_type && contains_deferred_semantic_type(target_type.get_shared())) {
        target_type = resolve_typeof_types(target_type, loc);
    }
    if (canonical_type_kind(target_type, ast_ctx_.get()) == TypeKind::Reference) {
        return collect_make<ExplicitCast>(std::move(expr), target_type, loc);
    }
    expr = collect_apply_standard_conversions(std::move(expr), ExprUseContext::RValue);
    if (expr && canonical_type_kind(target_type) == TypeKind::Vector) {
        auto expr_type = expr->get_type();
        if (expr_type && canonical_type_kind(expr_type) != TypeKind::Vector) {
            auto src_width = expr_type->getWidth();
            auto dst_width = target_type->getWidth();
            if (src_width > 0 && src_width == dst_width) {
                return collect_make<ExplicitCast>(std::move(expr), target_type, loc);
            }
            auto vec_ty = desugar_type(target_type).as_shared<VectorType>();
            if (vec_ty) {
                expr = cast_if_needed(std::move(expr), vec_ty->element_type);
            }
            return collect_make<ImplicitCast>(ImplicitCastTypes::VECTOR_SPLAT, std::move(expr), target_type);
        }
    }
    return collect_make<ExplicitCast>(std::move(expr), target_type, loc);
}

std::unique_ptr<Expr> Collect::collect_cpp_value_init_expression(
    QualType target_type,
    SrcLoc loc) const {
    return collect_make<CppValueInitExpr>(target_type, loc);
}

std::unique_ptr<Expr> Collect::collect_cpp_type_list_initialization_expression(
    QualType target_type,
    std::unique_ptr<InitListExpr> init_list,
    SrcLoc loc) {
    if (!target_type) {
        report_error("type construction requires a valid target type", loc);
        return collect_make<ErrorExpr>("invalid type construction target", loc);
    }

    if (!is_class_template_placeholder_type(target_type) &&
        contains_deferred_semantic_type(target_type.get_shared())) {
        target_type = resolve_typeof_types(target_type, loc);
    }

    if (!init_list) {
        init_list = collect_make<InitListExpr>(loc);
    }

    VariableDeclFlags flags;
    flags.initialization_kind = VariableInitializationKind::DirectList;
    auto temp_decl = collect_variable_declaration(
        target_type,
        "__cpp_type_list_init_tmp",
        std::move(init_list),
        nullptr,
        StorageClass::NONE,
        flags,
        loc);
    auto* temp_var = dyn_cast<VariableDecl>(temp_decl.get());
    if (!temp_var) {
        report_error("internal error: failed to build type construction expression", loc);
        return collect_make<ErrorExpr>("invalid type construction", loc);
    }

    if (temp_var->init) {
        return std::move(temp_var->init);
    }
    return collect_cpp_value_init_expression(target_type, loc);
}

std::unique_ptr<Expr> Collect::collect_cpp_function_style_cast(
    QualType target_type,
    std::vector<std::unique_ptr<Expr>> args,
    SrcLoc loc) {
    if (!target_type) {
        report_error("function-style cast requires a valid target type", loc);
        return collect_make<ErrorExpr>("invalid function-style cast type", loc);
    }

    if (contains_deferred_semantic_type(target_type.get_shared())) {
        target_type = resolve_typeof_types(target_type, loc);
    }

    bool is_dependent =
        type_depends_on_template_parameters(target_type, ast_ctx_.get());
    for (const auto& arg : args) {
        if (!arg) {
            continue;
        }
        if (expression_depends_on_template_parameters(arg.get()) ||
            type_depends_on_template_parameters(arg->get_type(), ast_ctx_.get())) {
            is_dependent = true;
            break;
        }
    }
    if (is_dependent) {
        return collect_make<CppFunctionStyleCastExpr>(
            target_type,
            std::move(args),
            loc);
    }

    auto target_kind = canonical_type_kind(target_type, ast_ctx_.get());
    if (target_type->isVoid()) {
        if (args.empty()) {
            return collect_cpp_value_init_expression(target_type, loc);
        }
        if (args.size() == 1) {
            return collect_explicit_cast(std::move(args.front()), target_type, loc);
        }
        report_error("function-style cast to void requires zero or one argument", loc);
        return collect_make<ErrorExpr>("invalid void function-style cast", loc);
    }

    if (target_kind == TypeKind::Reference) {
        if (args.empty()) {
            report_error("reference type cannot be value-initialized", loc);
            return collect_make<ErrorExpr>("invalid reference value-initialization", loc);
        }
        if (args.size() == 1) {
            return collect_explicit_cast(std::move(args.front()), target_type, loc);
        }
        report_error("function-style cast to reference type requires a single argument", loc);
        return collect_make<ErrorExpr>("invalid reference function-style cast", loc);
    }

    if (target_kind == TypeKind::Object) {
        auto initialized = collect_member_initializer_expression(
            std::move(args),
            target_type,
            false,
            loc,
            false);
        if (auto* init_list = dyn_cast<InitListExpr>(initialized.get());
            init_list && init_list->elements.empty()) {
            return collect_cpp_value_init_expression(target_type, loc);
        }
        return initialized;
    }

    if (target_kind == TypeKind::Array) {
        if (args.empty()) {
            return collect_cpp_value_init_expression(target_type, loc);
        }
        report_error("function-style cast to array type requires an empty initializer", loc);
        return collect_make<ErrorExpr>("invalid array function-style cast", loc);
    }

    if (target_kind == TypeKind::Function) {
        report_error("function type cannot be value-initialized or cast with functional notation", loc);
        return collect_make<ErrorExpr>("invalid function-style cast target", loc);
    }

    if (args.empty()) {
        return collect_cpp_value_init_expression(target_type, loc);
    }
    if (args.size() == 1) {
        return collect_explicit_cast(std::move(args.front()), target_type, loc);
    }
    report_error("function-style cast to non-class type requires zero or one argument", loc);
    return collect_make<ErrorExpr>("invalid function-style cast", loc);
}

std::unique_ptr<Expr> Collect::named_cast_error(
    const std::string& message,
    SrcLoc loc) const {
    report_error(message, loc);
    return collect_error_expression(message, loc);
}

Collect::CppConstCastCheckResult Collect::check_cpp_const_cast(
    Expr* expr,
    QualType target_type,
    std::string* error_out) const {
    auto set_error = [&](const std::string& message) {
        if (error_out) {
            *error_out = message;
        }
        return CppConstCastCheckResult::Invalid;
    };

    auto type_needs_deferred_check = [&](QualType type) {
        return type &&
               (type_depends_on_template_parameters(type, ast_ctx_.get()) ||
                contains_deferred_semantic_type(type.get_shared()));
    };

    bool target_dependent =
        type_needs_deferred_check(target_type);
    bool expr_dependent =
        expr && expression_depends_on_template_parameters(expr);

    if (!expr) {
        return target_dependent
            ? CppConstCastCheckResult::Dependent
            : set_error("const_cast operand has unknown type");
    }

    auto source_type = desugar_type(expr->get_type(), ast_ctx_.get());
    bool source_dependent =
        expr_dependent ||
        type_needs_deferred_check(source_type);
    if (!source_type) {
        return source_dependent || target_dependent
            ? CppConstCastCheckResult::Dependent
            : set_error("const_cast operand has unknown type");
    }

    auto target_no_ref =
        remove_reference_and_desugar(target_type, ast_ctx_.get());
    if (!target_no_ref) {
        return target_dependent
            ? CppConstCastCheckResult::Dependent
            : set_error("named cast requires a valid target type");
    }

    auto source_no_ref =
        remove_reference_and_desugar(source_type, ast_ctx_.get());
    if (!source_no_ref) {
        return source_dependent || target_dependent
            ? CppConstCastCheckResult::Dependent
            : set_error("const_cast operand has unknown type");
    }

    bool target_is_pointer =
        canonical_type_kind(target_type) == TypeKind::Pointer;
    bool source_is_pointer =
        canonical_type_kind(source_type) == TypeKind::Pointer;
    bool target_is_reference =
        canonical_type_kind(target_type) == TypeKind::Reference;
    bool source_is_reference =
        canonical_type_kind(source_type) == TypeKind::Reference;

    if (!(target_is_pointer || target_is_reference)) {
        return target_dependent
            ? CppConstCastCheckResult::Dependent
            : set_error("const_cast requires pointer or reference operand types");
    }
    if (!(source_is_pointer || source_is_reference)) {
        return source_dependent
            ? CppConstCastCheckResult::Dependent
            : set_error("const_cast requires pointer or reference operand types");
    }
    if (!((target_is_pointer && source_is_pointer) ||
          (target_is_reference && source_is_reference))) {
        return target_dependent || source_dependent
            ? CppConstCastCheckResult::Dependent
            : set_error("const_cast requires pointer or reference operand types");
    }

    if (!same_type_ignoring_all_qualifiers(
            target_no_ref,
            source_no_ref,
            ast_ctx_.get())) {
        return target_dependent || source_dependent
            ? CppConstCastCheckResult::Dependent
            : set_error("const_cast target type is not similar to source type");
    }

    if (target_is_reference && source_is_reference) {
        auto target_ref = desugar_type(target_type).as_shared<ReferenceType>();
        auto source_ref = desugar_type(source_type).as_shared<ReferenceType>();
        if (!target_ref || !source_ref ||
            target_ref->reference_kind != source_ref->reference_kind) {
            return target_dependent || source_dependent
                ? CppConstCastCheckResult::Dependent
                : set_error("const_cast target/reference kind mismatch");
        }
    }

    if (target_dependent || source_dependent) {
        return CppConstCastCheckResult::Dependent;
    }

    return CppConstCastCheckResult::Valid;
}

std::unique_ptr<Expr> Collect::cpp_const_named_cast(
    std::unique_ptr<Expr> expr,
    QualType target_type,
    QualType target_no_ref,
    SrcLoc loc) const {
    (void)target_no_ref;
    std::string error;
    auto check = check_cpp_const_cast(expr.get(), target_type, &error);
    if (check == CppConstCastCheckResult::Invalid) {
        return named_cast_error(error, loc);
    }
    if (check == CppConstCastCheckResult::Dependent) {
        return collect_make<ExplicitCast>(
            std::move(expr),
            target_type,
            loc,
            ExplicitCastKind::CppConstCast);
    }

    if (canonical_type_kind(target_type) == TypeKind::Pointer) {
        expr = collect_apply_standard_conversions(
            std::move(expr),
            ExprUseContext::RValue);
    }
    return collect_make<ExplicitCast>(
        std::move(expr),
        target_type,
        loc,
        ExplicitCastKind::CppConstCast);
}

std::unique_ptr<Expr> Collect::cpp_dynamic_named_cast(
    std::unique_ptr<Expr> expr,
    QualType target_type,
    QualType target_no_ref,
    SrcLoc loc) const {
    auto make_dependent_dynamic_cast =
        [&]() -> std::unique_ptr<Expr> {
        return collect_make<CppDynamicCastExpr>(
            std::move(expr),
            target_type,
            loc);
    };
    auto type_needs_deferred_check =
        [&](QualType type) {
        return type &&
               (type_depends_on_template_parameters(type, ast_ctx_.get()) ||
                contains_deferred_semantic_type(type.get_shared()) ||
                auto_type_utils::auto_type_flavors_in(type.get_shared()) != 0);
    };

    QualType raw_source_type = expr->get_type();
    auto source_type = desugar_type(raw_source_type, ast_ctx_.get());
    bool target_dependent =
        type_needs_deferred_check(target_type) ||
        type_needs_deferred_check(target_no_ref);
    bool source_dependent =
        expression_depends_on_template_parameters(expr.get()) ||
        type_needs_deferred_check(raw_source_type) ||
        type_needs_deferred_check(source_type);
    if (!source_type) {
        if (target_dependent || source_dependent) {
            return make_dependent_dynamic_cast();
        }
        return named_cast_error("dynamic_cast operand has unknown type", loc);
    }

    bool target_is_pointer = canonical_type_kind(target_type) == TypeKind::Pointer;
    bool source_is_pointer = canonical_type_kind(source_type) == TypeKind::Pointer;
    bool target_is_reference = canonical_type_kind(target_type) == TypeKind::Reference;
    bool source_is_reference = canonical_type_kind(source_type) == TypeKind::Reference;
    if (!(target_is_pointer || target_is_reference)) {
        if (target_dependent) {
            return make_dependent_dynamic_cast();
        }
        return named_cast_error(
            "dynamic_cast requires pointer or reference operand types", loc);
    }
    if (!(source_is_pointer || source_is_reference)) {
        if (source_dependent) {
            return make_dependent_dynamic_cast();
        }
        return named_cast_error(
            "dynamic_cast requires pointer or reference operand types", loc);
    }
    if (!((target_is_pointer && source_is_pointer) ||
          (target_is_reference && source_is_reference))) {
        return named_cast_error(
            "dynamic_cast requires pointer or reference operand types", loc);
    }

    constexpr const char* runtime_polymorphic_error =
        "dynamic_cast runtime checks require source type to be polymorphic";
    auto require_runtime_polymorphic_source = [&](QualType source_object_type) -> bool {
        const ObjectDecl* source_decl =
            object_decl_from_object_qualtype(source_object_type, ast_ctx_.get());
        if (!source_decl) {
            return true;
        }
        const RecordSemanticState* source_state = record_semantics_cache_lookup(source_decl);
        if (!source_state) {
            return true;
        }
        if (!source_state->is_polymorphic) {
            report_error(runtime_polymorphic_error, loc);
            return false;
        }
        return true;
    };

    if (target_is_pointer && source_is_pointer) {
        expr = collect_apply_standard_conversions(std::move(expr), ExprUseContext::RValue);
        if (!expr) {
            return named_cast_error("dynamic_cast requires a valid expression operand", loc);
        }

        auto source_ptr =
            remove_reference_and_desugar(
                expr->get_type(),
                ast_ctx_.get())
                .as_shared<PointerType>();
        auto target_ptr = target_no_ref.as_shared<PointerType>();
        if (!source_ptr || !target_ptr) {
            if ((source_dependent && !source_ptr) ||
                (target_dependent && !target_ptr)) {
                return make_dependent_dynamic_cast();
            }
            return named_cast_error("dynamic_cast requires pointer operand types", loc);
        }

        auto source_object =
            remove_reference_and_desugar(
                source_ptr->pointed_type,
                ast_ctx_.get());
        if (!source_object.as_shared<ObjectType>()) {
            if (source_dependent ||
                type_needs_deferred_check(source_ptr->pointed_type)) {
                return make_dependent_dynamic_cast();
            }
            return named_cast_error("dynamic_cast requires pointers to class types", loc);
        }

        if (target_ptr->pointed_type && target_ptr->pointed_type->isVoid()) {
            if (!require_runtime_polymorphic_source(source_object)) {
                return collect_error_expression(runtime_polymorphic_error, loc);
            }
            return collect_make<CppDynamicCastExpr>(std::move(expr), target_type, loc);
        }

        auto target_object =
            remove_reference_and_desugar(
                target_ptr->pointed_type,
                ast_ctx_.get());
        if (!target_object.as_shared<ObjectType>()) {
            if (target_dependent ||
                type_needs_deferred_check(target_ptr->pointed_type)) {
                return make_dependent_dynamic_cast();
            }
            return named_cast_error("dynamic_cast requires pointers to class types", loc);
        }

        bool same_type =
            source_object.equals_unqualified(target_object) &&
            target_object.has_all_qualifiers_of(source_object);
        bool safe_upcast = can_convert_derived_to_base_object(source_object, target_object);
        if (same_type || safe_upcast) {
            return collect_make<ImplicitCast>(std::move(expr), target_type);
        }

        if (!require_runtime_polymorphic_source(source_object)) {
            return collect_error_expression(runtime_polymorphic_error, loc);
        }
        return collect_make<CppDynamicCastExpr>(std::move(expr), target_type, loc);
    }

    auto source_ref = desugar_type(source_type).as_shared<ReferenceType>();
    auto target_ref = desugar_type(target_type).as_shared<ReferenceType>();
    if (!source_ref || !target_ref) {
        if ((source_dependent && !source_ref) ||
            (target_dependent && !target_ref)) {
            return make_dependent_dynamic_cast();
        }
        return named_cast_error(
            "dynamic_cast requires pointer or reference operand types", loc);
    }

    auto source_object =
        remove_reference_and_desugar(
            source_ref->referred_type,
            ast_ctx_.get());
    auto target_object =
        remove_reference_and_desugar(
            target_ref->referred_type,
            ast_ctx_.get());
    if (!source_object.as_shared<ObjectType>() ||
        !target_object.as_shared<ObjectType>()) {
        if ((source_dependent ||
             type_needs_deferred_check(source_ref->referred_type)) ||
            (target_dependent ||
             type_needs_deferred_check(target_ref->referred_type))) {
            return make_dependent_dynamic_cast();
        }
        return named_cast_error("dynamic_cast requires references to class types", loc);
    }

    bool same_type =
        source_object.equals_unqualified(target_object) &&
        target_object.has_all_qualifiers_of(source_object);
    bool safe_upcast = can_convert_derived_to_base_object(source_object, target_object);
    if (same_type || safe_upcast) {
        return collect_make<ImplicitCast>(
            ImplicitCastTypes::RAW_CAST, std::move(expr), target_type);
    }

    if (!require_runtime_polymorphic_source(source_object)) {
        return collect_error_expression(runtime_polymorphic_error, loc);
    }
    return collect_make<CppDynamicCastExpr>(std::move(expr), target_type, loc);
}

std::unique_ptr<Expr> Collect::cpp_reinterpret_named_cast(
    std::unique_ptr<Expr> expr,
    QualType source_type,
    QualType target_type,
    QualType target_no_ref,
    SrcLoc loc) const {
    auto type_needs_deferred_check = [&](QualType type) {
        return type &&
               (type_depends_on_template_parameters(type, ast_ctx_.get()) ||
                contains_deferred_semantic_type(type.get_shared()));
    };

    bool target_dependent =
        type_needs_deferred_check(target_type) ||
        type_needs_deferred_check(target_no_ref);
    bool expr_dependent =
        expr && expression_depends_on_template_parameters(expr.get());
    bool source_dependent =
        expr_dependent ||
        type_needs_deferred_check(source_type);
    if (!source_type) {
        if (source_dependent || target_dependent) {
            return collect_make<ExplicitCast>(
                std::move(expr),
                target_type,
                loc,
                ExplicitCastKind::CppReinterpretCast);
        }
        return named_cast_error("named cast operand has unknown type", loc);
    }
    if (!target_no_ref) {
        if (target_dependent) {
            return collect_make<ExplicitCast>(
                std::move(expr),
                target_type,
                loc,
                ExplicitCastKind::CppReinterpretCast);
        }
        return named_cast_error("named cast requires a valid target type", loc);
    }
    if (source_dependent || target_dependent) {
        return collect_make<ExplicitCast>(
            std::move(expr),
            target_type,
            loc,
            ExplicitCastKind::CppReinterpretCast);
    }

    bool source_pointer_like = is_pointer_like_type(source_type, ast_ctx_.get());
    bool target_pointer_like = is_pointer_like_type(target_no_ref, ast_ctx_.get());
    bool source_integer_like =
        is_integer_adjacent(source_type, ast_ctx_.get());
    bool target_integer_like =
        is_integer_adjacent(target_no_ref, ast_ctx_.get());

    bool allowed = (source_pointer_like && target_pointer_like) ||
                   (source_pointer_like && target_integer_like) ||
                   (source_integer_like && target_pointer_like);
    if (!allowed) {
        return named_cast_error("invalid operands to reinterpret_cast", loc);
    }

    if (source_pointer_like && target_integer_like) {
        int64_t source_bits = source_type->getWidth();
        int64_t target_bits = target_no_ref->getWidth();
        if (source_bits > 0 && target_bits > 0 && target_bits < source_bits) {
            return named_cast_error(
                "reinterpret_cast from pointer to smaller integer type loses information",
                loc);
        }
    }

    return collect_make<ExplicitCast>(
        std::move(expr),
        target_type,
        loc,
        ExplicitCastKind::CppReinterpretCast);
}

Collect::CppStaticCastCheckResult Collect::check_cpp_static_cast(
    Expr* expr,
    QualType source_type,
    QualType target_type,
    QualType target_no_ref,
    std::string* error_out) const {
    auto set_error = [&](const std::string& message) {
        if (error_out) {
            *error_out = message;
        }
        return CppStaticCastCheckResult::Invalid;
    };

    auto type_needs_deferred_check = [&](QualType type) {
        return type &&
               (type_depends_on_template_parameters(type, ast_ctx_.get()) ||
                contains_deferred_semantic_type(type.get_shared()));
    };

    auto member_pointer_static_cast_error =
        [](MemberPointerConversionIssue issue) -> std::string {
        switch (issue) {
            case MemberPointerConversionIssue::MemberTypeMismatch:
                return "invalid static_cast between pointer-to-member types with different member types";
            case MemberPointerConversionIssue::QualificationDrops:
                return "static_cast cannot cast away qualifiers in pointer-to-member conversion";
            case MemberPointerConversionIssue::AmbiguousBase:
                return "invalid static_cast between pointer-to-member types across ambiguous base class";
            case MemberPointerConversionIssue::VirtualBase:
                return "invalid static_cast between pointer-to-member types across virtual base class";
            case MemberPointerConversionIssue::InaccessibleBase:
                return "invalid static_cast between pointer-to-member types across inaccessible base class";
            case MemberPointerConversionIssue::UnrelatedClass:
                return "invalid static_cast between unrelated pointer-to-member types";
            case MemberPointerConversionIssue::NotMemberPointerType:
            case MemberPointerConversionIssue::None:
                break;
        }
        return "invalid static_cast between pointer-to-member types";
    };

    bool target_dependent =
        type_needs_deferred_check(target_type) ||
        type_needs_deferred_check(target_no_ref);
    bool expr_dependent =
        expr && expression_depends_on_template_parameters(expr);
    bool source_dependent =
        expr_dependent ||
        type_needs_deferred_check(source_type);

    if (!expr) {
        return target_dependent
            ? CppStaticCastCheckResult::Dependent
            : set_error("named cast requires a valid expression operand");
    }
    if (!source_type) {
        return target_dependent || source_dependent
            ? CppStaticCastCheckResult::Dependent
            : set_error("named cast operand has unknown type");
    }
    if (!target_no_ref) {
        return target_dependent
            ? CppStaticCastCheckResult::Dependent
            : set_error("named cast requires a valid target type");
    }

    if (target_dependent || source_dependent) {
        return CppStaticCastCheckResult::Dependent;
    }

    auto source_ptr = source_type.as_shared<PointerType>();
    auto target_ptr = target_no_ref.as_shared<PointerType>();
    auto source_member_ptr = source_type.as_shared<MemberPointerType>();
    auto target_member_ptr = target_no_ref.as_shared<MemberPointerType>();

    bool source_integer_like = is_integer_or_enum_type(source_type, ast_ctx_.get());
    bool target_integer_like = is_integer_or_enum_type(target_no_ref, ast_ctx_.get());

    if (source_ptr && target_ptr) {
        bool target_points_to_void =
            target_ptr->pointed_type && target_ptr->pointed_type->isVoid();
        bool source_points_to_void =
            source_ptr->pointed_type && source_ptr->pointed_type->isVoid();

        if (target_ptr->pointed_type &&
            source_ptr->pointed_type &&
            !target_ptr->pointed_type.has_all_qualifiers_of(
                source_ptr->pointed_type)) {
            return set_error("static_cast cannot cast away qualifiers");
        }

        bool handled_class_pointer_conversion = false;
        if (!target_points_to_void && !source_points_to_void) {
            const ObjectDecl* source_record_decl =
                object_decl_from_object_qualtype(source_ptr->pointed_type);
            const ObjectDecl* target_record_decl =
                object_decl_from_object_qualtype(target_ptr->pointed_type);
            if (source_record_decl &&
                target_record_decl &&
                canonical_record_decl(source_record_decl) !=
                    canonical_record_decl(target_record_decl)) {
                const ObjectDecl* access_context_decl =
                    current_access_context_record_decl(
                        session_.func_state_.current_function_is_cpp_member,
                        session_.func_state_.current_function_cpp_this_type,
                        session_.func_state_.current_function_cpp_friend_access_type,
                        session_.current_cpp_record_lookup_type_,
                        ast_ctx_.get(),
                        session_.func_state_.current_function_cpp_access_context_type);
                QualType access_context_type =
                    current_access_context_record_type(
                        session_.func_state_.current_function_is_cpp_member,
                        session_.func_state_.current_function_cpp_this_type,
                        session_.func_state_.current_function_cpp_friend_access_type,
                        session_.current_cpp_record_lookup_type_,
                        ast_ctx_.get(),
                        session_.func_state_.current_function_cpp_access_context_type);

                CppBasePathAccessSummary upcast_paths =
                    summarize_cpp_accessible_base_paths(
                        source_record_decl,
                        target_record_decl,
                        access_context_decl,
                        access_context_type,
                        ast_ctx_.get());
                if (upcast_paths.has_any_path()) {
                    handled_class_pointer_conversion = true;
                    size_t accessible_count =
                        upcast_paths.accessible_subobject_count();
                    if (accessible_count == 0 &&
                        upcast_paths.has_inaccessible_path()) {
                        return set_error(
                            "invalid static_cast between pointer types across inaccessible base class");
                    }
                    if (accessible_count > 1) {
                        return set_error(
                            "invalid static_cast between pointer types across ambiguous base class");
                    }
                }

                if (!handled_class_pointer_conversion) {
                    CppBasePathAccessSummary downcast_paths =
                        summarize_cpp_accessible_base_paths(
                            target_record_decl,
                            source_record_decl,
                            access_context_decl,
                            access_context_type,
                            ast_ctx_.get());
                    if (downcast_paths.has_any_path()) {
                        handled_class_pointer_conversion = true;
                        size_t accessible_count =
                            downcast_paths.accessible_subobject_count();
                        if (accessible_count == 0 &&
                            downcast_paths.has_inaccessible_path()) {
                            return set_error(
                                "invalid static_cast between pointer types across inaccessible base class");
                        }
                        if (downcast_paths.accessible_virtual_path) {
                            return set_error(
                                "invalid static_cast between pointer types across virtual base class");
                        }
                        if (accessible_count > 1) {
                            return set_error(
                                "invalid static_cast between pointer types across ambiguous base class");
                        }
                    }
                }
            }
        }

        if (!target_points_to_void &&
            !source_points_to_void &&
            !handled_class_pointer_conversion &&
            !pointers_to_compatible_types(target_no_ref, source_type)) {
            return set_error(
                "invalid static_cast between unrelated pointer types");
        }
    } else if (source_member_ptr && target_member_ptr) {
        auto conversion = analyze_member_pointer_conversion(source_type, target_no_ref);
        if (!conversion.viable) {
            return set_error(member_pointer_static_cast_error(conversion.issue));
        }
    } else if (target_ptr && source_integer_like) {
        if (!is_null_pointer_constant_expr(expr)) {
            return set_error("invalid static_cast from integer to pointer type");
        }
    } else if (target_member_ptr && source_integer_like) {
        if (!is_null_pointer_constant_expr(expr)) {
            return set_error(
                "invalid static_cast from integer to member pointer type");
        }
    } else if (source_ptr && target_integer_like) {
        return set_error("invalid static_cast from pointer to integer type");
    } else if (source_member_ptr && target_integer_like) {
        return set_error(
            "invalid static_cast from member pointer to integer type");
    }

    return CppStaticCastCheckResult::Valid;
}

std::unique_ptr<Expr> Collect::cpp_static_named_cast(
    std::unique_ptr<Expr> expr,
    QualType source_type,
    QualType target_type,
    QualType target_no_ref,
    SrcLoc loc) const {
    std::string static_cast_error;
    auto static_cast_check =
        check_cpp_static_cast(
            expr.get(),
            source_type,
            target_type,
            target_no_ref,
            &static_cast_error);
    if (static_cast_check == CppStaticCastCheckResult::Invalid) {
        return named_cast_error(static_cast_error, loc);
    }
    if (static_cast_check == CppStaticCastCheckResult::Dependent) {
        return collect_make<ExplicitCast>(
            std::move(expr),
            target_type,
            loc,
            ExplicitCastKind::CppStaticCast);
    }

    auto source_object_type =
        source_type.as_shared<ObjectType>();
    auto target_object_type =
        target_no_ref.as_shared<ObjectType>();
    bool target_is_reference =
        canonical_type_kind(target_type, ast_ctx_.get()) == TypeKind::Reference;
    bool same_object_type =
        source_object_type &&
        target_object_type &&
        source_type.equals_unqualified(target_no_ref);
    bool derived_to_base_object =
        source_object_type &&
        target_object_type &&
        can_convert_derived_to_base_object(source_type, target_no_ref);

    if (target_is_reference && (same_object_type || derived_to_base_object)) {
        return collect_make<ExplicitCast>(
            std::move(expr),
            target_type,
            loc,
            ExplicitCastKind::CppStaticCast);
    }

    if (lang_opts_.is_cxx_mode() &&
        (source_object_type || target_object_type)) {
        auto conversion_match =
            const_cast<Collect*>(this)->select_cpp_user_defined_conversion(
                expr.get(),
                target_type,
                /*allow_explicit_constructors=*/true,
                /*allow_explicit_conversion_functions=*/true);
        if (conversion_match.has_value()) {
            return const_cast<Collect*>(this)
                ->build_cpp_selected_user_defined_conversion_expr(
                    std::move(expr),
                    target_type,
                    *conversion_match,
                    loc);
        }

        if (!same_object_type && !derived_to_base_object) {
            return named_cast_error(
                "invalid static_cast between object types",
                loc);
        }
    }

    return collect_make<ExplicitCast>(
        std::move(expr),
        target_type,
        loc,
        ExplicitCastKind::CppStaticCast);
}

std::unique_ptr<Expr> Collect::collect_cpp_named_cast(CppNamedCastKind cast_kind,
                                                      std::unique_ptr<Expr> expr,
                                                      QualType target_type,
                                                      SrcLoc loc) {
    if (!expr) {
        return named_cast_error("named cast requires a valid expression operand", loc);
    }

    if (target_type && contains_deferred_semantic_type(target_type.get_shared())) {
        target_type = resolve_typeof_types(target_type, loc);
    }
    if (!target_type) {
        return named_cast_error("named cast requires a valid target type", loc);
    }

    auto target_no_ref =
        remove_reference_and_desugar(target_type, ast_ctx_.get());
    if (!target_no_ref) {
        return named_cast_error("named cast requires a valid target type", loc);
    }

    if (cast_kind == CppNamedCastKind::Const) {
        return cpp_const_named_cast(
            std::move(expr), target_type, target_no_ref, loc);
    }
    if (cast_kind == CppNamedCastKind::Dynamic) {
        return cpp_dynamic_named_cast(
            std::move(expr), target_type, target_no_ref, loc);
    }

    if (cast_kind == CppNamedCastKind::Reinterpret) {
        if (canonical_type_kind(target_type, ast_ctx_.get()) !=
            TypeKind::Reference) {
            expr = collect_apply_standard_conversions(
                std::move(expr), ExprUseContext::RValue);
            if (!expr) {
                return named_cast_error(
                    "named cast requires a valid expression operand", loc);
            }
        }
        auto source_type =
            remove_reference_and_desugar(expr->get_type(), ast_ctx_.get());
        return cpp_reinterpret_named_cast(
            std::move(expr), source_type, target_type, target_no_ref, loc);
    }
    if (cast_kind == CppNamedCastKind::Static) {
        if (canonical_type_kind(target_type, ast_ctx_.get()) !=
            TypeKind::Reference) {
            expr = collect_apply_standard_conversions(
                std::move(expr), ExprUseContext::RValue);
            if (!expr) {
                return named_cast_error(
                    "named cast requires a valid expression operand", loc);
            }
        }
        auto source_type =
            remove_reference_and_desugar(expr->get_type(), ast_ctx_.get());
        return cpp_static_named_cast(
            std::move(expr), source_type, target_type, target_no_ref, loc);
    }

    return named_cast_error("unknown named cast kind", loc);
}

std::unique_ptr<Expr> Collect::collect_cpp_throw_expression(
    std::unique_ptr<Expr> thrown_expr,
    SrcLoc loc) const {
    bool is_rethrow = !thrown_expr;
    if (thrown_expr) {
        thrown_expr = collect_apply_standard_conversions(
            std::move(thrown_expr),
            ExprUseContext::RValue);
    }
    return collect_make<CppThrowExpr>(
        std::move(thrown_expr),
        QualType(get_builtin_void()),
        is_rethrow,
        loc);
}

std::shared_ptr<Symbol> Collect::make_default_allocation_like_operator_symbol(
    const std::string& operator_name) const {
    auto fn_type = std::make_shared<FunctionType>();
    fn_type->has_prototype = true;
    fn_type->is_variadic = false;
    if (operator_name == "operatornew" || operator_name == "operatornew[]") {
        fn_type->ret_type =
            QualType(std::make_shared<PointerType>(QualType(get_builtin_void())));
        fn_type->push_parameter(QualType(get_builtin_ulong()));
    } else if (operator_name == "operatordelete" ||
               operator_name == "operatordelete[]") {
        fn_type->ret_type = QualType(get_builtin_void());
        fn_type->push_parameter(
            QualType(std::make_shared<PointerType>(QualType(get_builtin_void()))));
    } else {
        return nullptr;
    }
    auto sym = std::make_shared<Symbol>(
        operator_name, SymbolKind::FUNCTION, QualType(fn_type));
    sym->storage_class = StorageClass::EXTERN;
    sym->linkage = VariableLinkage::EXTERNAL;
    sym->set_language_linkage(LanguageLinkage::CXX);
    return sym;
}

std::unique_ptr<Expr> Collect::select_cpp_allocation_like_function(
    const std::string& operator_name,
    const std::shared_ptr<ObjectType>& lookup_record,
    bool force_global_lookup,
    const std::vector<std::unique_ptr<Expr>>& call_args,
    SrcLoc loc,
    std::shared_ptr<Symbol>& selected_symbol_out) {
    selected_symbol_out = nullptr;

    std::vector<OverloadCallCandidate> overload_candidates;
    bool saw_member_match = false;
    bool saw_private_method = false;
    bool saw_protected_method = false;

    if (!force_global_lookup && lookup_record) {
        auto member_candidates = find_record_methods(lookup_record.get(), operator_name);
        if (!member_candidates.empty()) {
            saw_member_match = true;
        }

        const ObjectDecl* access_context_decl =
            lang_opts_.is_cxx_mode()
                ? current_access_context_record_decl(
                      session_.func_state_.current_function_is_cpp_member,
                      session_.func_state_.current_function_cpp_this_type,
                      session_.func_state_.current_function_cpp_friend_access_type,
                      session_.current_cpp_record_lookup_type_,
                      ast_ctx_.get(),
                      session_.func_state_.current_function_cpp_access_context_type)
                : nullptr;
        QualType access_context_type =
            lang_opts_.is_cxx_mode()
                ? current_access_context_record_type(
                      session_.func_state_.current_function_is_cpp_member,
                      session_.func_state_.current_function_cpp_this_type,
                      session_.func_state_.current_function_cpp_friend_access_type,
                      session_.current_cpp_record_lookup_type_,
                      ast_ctx_.get(),
                      session_.func_state_.current_function_cpp_access_context_type)
                : QualType(nullptr);

        for (const auto& member_match : member_candidates) {
            const auto* method = member_match.method;
            if (!method || method->name != operator_name) {
                continue;
            }
            if (!method->is_static) {
                continue;
            }

            bool is_accessible = true;
            if (lang_opts_.is_cxx_mode() &&
                method->declared_access == RecordMemberAccess::Private) {
                if (!can_access_private_member_in_context(
                        member_match.owner_record_decl,
                        access_context_decl,
                        ast_ctx_.get(),
                        access_context_type)) {
                    saw_private_method = true;
                    is_accessible = false;
                }
            } else if (lang_opts_.is_cxx_mode() &&
                       method->declared_access == RecordMemberAccess::Protected) {
                bool protected_ok = can_access_protected_member_in_context(
                    member_match.owner_record_decl,
                    access_context_decl,
                    member_match.owner_record_decl,
                    true,
                    ast_ctx_.get(),
                    access_context_type);
                if (!protected_ok) {
                    saw_protected_method = true;
                    is_accessible = false;
                }
            }
            if (!is_accessible) {
                continue;
            }

            if (!method->symbol) {
                report_error(
                    "internal error: unresolved member function symbol '" +
                        operator_name + "'",
                    loc);
                return collect_error_expression(
                    "unresolved member function symbol", loc);
            }

            OverloadCallCandidate call_candidate;
            call_candidate.symbol = method->symbol;
            call_candidate.implicit_object_arg_kind =
                OverloadImplicitObjectArgKind::None;
            overload_candidates.push_back(std::move(call_candidate));
        }

        if (saw_member_match && overload_candidates.empty()) {
            if (auto inaccessible_error = report_inaccessible_member(
                    operator_name,
                    saw_private_method,
                    saw_protected_method,
                    loc)) {
                return inaccessible_error;
            }
            report_error("inaccessible member '" + operator_name + "'", loc);
            return collect_error_expression("inaccessible member", loc);
        }
    }

    if (!saw_member_match) {
        append_unqualified_overload_candidates(
            operator_name,
            OverloadImplicitObjectArgKind::None,
            overload_candidates);
        append_unqualified_function_template_overload_candidates(
            operator_name,
            nullptr,
            OverloadImplicitObjectArgKind::None,
            call_args,
            overload_candidates,
            loc);
        if (overload_candidates.empty()) {
            auto default_symbol =
                make_default_allocation_like_operator_symbol(operator_name);
            if (default_symbol) {
                OverloadCallCandidate default_candidate;
                default_candidate.symbol = std::move(default_symbol);
                default_candidate.implicit_object_arg_kind =
                    OverloadImplicitObjectArgKind::None;
                overload_candidates.push_back(std::move(default_candidate));
            }
        }
    }

    if (overload_candidates.empty()) {
        report_error("no matching function for call to '" + operator_name + "'", loc);
        return collect_error_expression("no matching overload", loc);
    }

    OverloadImplicitObjectArgKind selected_implicit_arg_kind =
        OverloadImplicitObjectArgKind::None;
    if (auto overload_error = resolve_overloaded_call_candidates(
            operator_name,
            overload_candidates,
            call_args,
            nullptr,
            loc,
            selected_symbol_out,
            selected_implicit_arg_kind)) {
        return overload_error;
    }
    if (auto completion_error =
            complete_selected_function_template_specialization_symbol(
                selected_symbol_out,
                loc,
                "failed to instantiate selected allocation function template specialization")) {
        return completion_error;
    }
    return nullptr;
}

std::unique_ptr<Expr> Collect::collect_cpp_new_expression(
    QualType allocated_type,
    std::vector<std::unique_ptr<Expr>> placement_args,
    std::unique_ptr<Expr> initializer,
    bool is_global_allocation,
    SrcLoc loc) {
    auto type_has_template_dependency = [&](QualType type) {
        return type &&
               (type_depends_on_template_parameters(type, ast_ctx_.get()) ||
                auto_type_utils::auto_type_flavors_in(type.get_shared()) != 0);
    };
    auto type_needs_deferred_new_semantics = [&](QualType type) {
        return type &&
               (type_has_template_dependency(type) ||
                contains_deferred_semantic_type(type.get_shared()));
    };
    auto expr_needs_deferred_new_semantics =
        [&](const std::unique_ptr<Expr>& expr) {
        if (!expr) {
            return false;
        }
        QualType expr_type = expr->get_type();
        return expression_depends_on_template_parameters(expr.get()) ||
               type_needs_deferred_new_semantics(expr_type);
    };
    auto any_expr_needs_deferred_new_semantics =
        [&](const std::vector<std::unique_ptr<Expr>>& exprs) {
        for (const auto& expr : exprs) {
            if (expr_needs_deferred_new_semantics(expr)) {
                return true;
            }
        }
        return false;
    };

    if (!allocated_type) {
        report_error("new-expression requires a valid allocated type", loc);
        return collect_error_expression("new-expression requires a valid allocated type", loc);
    }
    if (contains_deferred_semantic_type(allocated_type.get_shared())) {
        if (type_has_template_dependency(allocated_type)) {
            if (QualType realized_type =
                    try_realize_deferred_semantic_type(allocated_type)) {
                allocated_type = realized_type;
            }
        }
        if (contains_deferred_semantic_type(allocated_type.get_shared()) &&
            !type_has_template_dependency(allocated_type)) {
            allocated_type = finalize_deferred_semantic_type(allocated_type, loc);
        }
    }
    if (!allocated_type) {
        report_error("new-expression requires a valid allocated type", loc);
        return collect_error_expression("new-expression requires a valid allocated type", loc);
    }

    QualType canonical_allocated = desugar_type(allocated_type);
    bool is_array_form = canonical_type_kind(canonical_allocated) == TypeKind::Array;
    bool allocated_type_is_dependent =
        type_needs_deferred_new_semantics(allocated_type);

    QualType pointee_type = allocated_type;
    if (is_array_form) {
        auto array_type = canonical_allocated.as_shared<ArrayType>();
        if (!array_type || !array_type->element_type) {
            report_error("new-expression array type has invalid element type", loc);
            return collect_error_expression("new-expression array type has invalid element type", loc);
        }
        bool has_known_bound = array_type->size_kind == ArraySizeKind::Variable ||
            (array_type->size_kind == ArraySizeKind::Constant &&
             array_type->size.has_value());
        if (!has_known_bound && !allocated_type_is_dependent) {
            report_error("new-expression array type requires a bound", loc);
            return collect_error_expression("new-expression array type requires a bound", loc);
        }
        pointee_type = array_type->element_type;
    }

    pointee_type = remove_reference(pointee_type);
    QualType result_type(std::make_shared<PointerType>(pointee_type));

    if (allocated_type_is_dependent) {
        return collect_make<CppNewExpr>(
            allocated_type,
            result_type,
            std::move(placement_args),
            std::move(initializer),
            std::vector<std::unique_ptr<Expr>>{},
            nullptr,
            nullptr,
            nullptr,
            is_array_form,
            is_global_allocation,
            false,
            loc);
    }

    QualType canonical_pointee = desugar_type(pointee_type);
    auto pointee_kind = canonical_type_kind(canonical_pointee);

    if (!canonical_pointee ||
        pointee_kind == TypeKind::Function ||
        pointee_kind == TypeKind::Reference) {
        report_error("new-expression cannot allocate function or reference type", loc);
        return collect_error_expression(
            "new-expression cannot allocate function or reference type", loc);
    }
    if (canonical_pointee->isVoid()) {
        report_error("new-expression cannot allocate incomplete type 'void'", loc);
        return collect_error_expression(
            "new-expression cannot allocate incomplete type 'void'", loc);
    }
    if (canonical_pointee->isIncomplete()) {
        report_error(
            "new-expression cannot allocate incomplete type '" +
                canonical_pointee.to_string() + "'",
            loc);
        return collect_error_expression("new-expression cannot allocate incomplete type", loc);
    }

    auto pointee_record = canonical_pointee.as_shared<ObjectType>();
    const ObjectDecl* pointee_record_decl =
        pointee_record ? dyn_cast<ObjectDecl>(pointee_record->get_decl()) : nullptr;
    const RecordSemanticState* pointee_record_state =
        pointee_record_decl ? record_semantics_cache_lookup(pointee_record_decl) : nullptr;

    if (lang_opts_.is_cxx_mode() &&
        pointee_record &&
        pointee_record_state &&
        pointee_record_state->is_abstract) {
        report_error(
            "cannot instantiate abstract class type '" +
                canonical_pointee.to_string() + "'",
            loc);
        return collect_error_expression("cannot instantiate abstract class type", loc);
    }

    if (any_expr_needs_deferred_new_semantics(placement_args) ||
        expr_needs_deferred_new_semantics(initializer)) {
        return collect_make<CppNewExpr>(
            allocated_type,
            result_type,
            std::move(placement_args),
            std::move(initializer),
            std::vector<std::unique_ptr<Expr>>{},
            nullptr,
            nullptr,
            nullptr,
            is_array_form,
            is_global_allocation,
            false,
            loc);
    }

    for (auto& placement_arg : placement_args) {
        placement_arg = collect_apply_standard_conversions(
            std::move(placement_arg),
            ExprUseContext::CallArgument);
    }

    std::string allocator_name = is_array_form ? "operatornew[]" : "operatornew";
    std::string deallocator_name = is_array_form ? "operatordelete[]" : "operatordelete";

    std::vector<std::unique_ptr<Expr>> allocator_call_args;
    allocator_call_args.reserve(1 + placement_args.size());
    // First allocator argument is always the computed allocation size; placement
    // arguments are appended after it.
    allocator_call_args.push_back(collect_sizeof_type(allocated_type, loc));
    for (auto& arg : placement_args) {
        allocator_call_args.push_back(std::move(arg));
    }
    placement_args.clear();

    std::shared_ptr<Symbol> selected_allocator_sym = nullptr;
    if (auto alloc_error = select_cpp_allocation_like_function(
            allocator_name,
            pointee_record,
            is_global_allocation,
            allocator_call_args,
            loc,
            selected_allocator_sym)) {
        return alloc_error;
    }
    if (!selected_allocator_sym) {
        report_error("no viable allocation function selected", loc);
        return collect_error_expression("no viable allocation function selected", loc);
    }

    placement_args.reserve(allocator_call_args.size() > 0
        ? allocator_call_args.size() - 1
        : 0);
    for (size_t idx = 1; idx < allocator_call_args.size(); ++idx) {
        placement_args.push_back(std::move(allocator_call_args[idx]));
    }

    std::shared_ptr<Symbol> selected_ctor_sym = nullptr;
    std::vector<std::unique_ptr<Expr>> constructor_args;
    bool is_list_init = false;
    auto should_use_implicit_special_member_ctor =
        [&](const Expr* init_expr) -> bool {
        if (!pointee_record_state || !init_expr) {
            return false;
        }
        if (!pointee_record_state->definition_data.has_copy_constructor &&
            !pointee_record_state->definition_data.has_move_constructor) {
            return false;
        }
        const Expr* source_expr = init_expr;
        if (auto* init_list = dyn_cast<InitListExpr>(init_expr)) {
            if (init_list->elements.size() != 1) {
                return false;
            }
            const auto& element = init_list->elements.front();
            if (!element.value || !element.designators.empty()) {
                return false;
            }
            source_expr = element.value.get();
        }
        QualType source_type =
            source_expr ? const_cast<Expr*>(source_expr)->get_type() : QualType();
        QualType canonical_source =
            remove_reference_and_desugar(source_type, ast_ctx_.get());
        return canonical_source &&
               canonical_source->kind == TypeKind::Object &&
               canonical_source.equals_unqualified(canonical_pointee);
    };

    if (is_array_form &&
        pointee_record &&
        pointee_record_state &&
        (pointee_record_state->definition_data.has_user_declared_constructor ||
         pointee_record_state->definition_data.has_user_declared_destructor)) {
        // Current lowering does not yet synthesize per-element ctor/dtor loops
        // for class arrays; reject before creating partial semantic state.
        report_error(
            "new[] for class types with user-declared constructors/destructors is not supported yet",
            loc);
        return collect_error_expression("new[] class-object initialization not supported yet", loc);
    }

    if (pointee_record &&
        pointee_record_state &&
        !is_array_form &&
        (pointee_record_state->definition_data.has_user_declared_constructor ||
         should_use_implicit_special_member_ctor(initializer.get())) &&
        !pointee_record_state->constructors.empty()) {
        std::vector<std::unique_ptr<Expr>> ctor_input_args;
        bool ctor_is_list_init = false;
        if (initializer) {
            if (auto* init_list = dyn_cast<InitListExpr>(initializer.get())) {
                ctor_is_list_init = !init_list->is_paren_init;
                auto owned_list = std::unique_ptr<InitListExpr>(
                    static_cast<InitListExpr*>(initializer.release()));
                ctor_input_args.reserve(owned_list->elements.size());
                for (auto& elem : owned_list->elements) {
                    if (!elem.designators.empty()) {
                        report_error(
                            "designated initializers are not supported in constructor initialization",
                            elem.loc);
                    }
                    if (!elem.value) {
                        report_error(
                            "missing initializer expression in constructor argument list",
                            elem.loc);
                        continue;
                    }
                    ctor_input_args.push_back(std::move(elem.value));
                }
            } else {
                ctor_input_args.push_back(std::move(initializer));
            }
        }

        bool had_ctor_input_args = !ctor_input_args.empty();
        auto ctor_init_expr = collect_member_initializer_expression(
            std::move(ctor_input_args),
            pointee_type,
            ctor_is_list_init,
            loc,
            false);
        if (!ctor_init_expr) {
            if (had_ctor_input_args) {
                report_error(
                    "internal error: failed to build constructor initialization for new-expression",
                    loc);
                return collect_error_expression(
                    "failed to build constructor initialization for new-expression",
                    loc);
            }
            // Implicit default construction with no explicit constructor call.
            initializer.reset();
        } else {
            if (auto* err = dyn_cast<ErrorExpr>(ctor_init_expr.get())) {
                return std::move(ctor_init_expr);
            }

            if (auto* ctor_expr = dyn_cast<CppConstructExpr>(ctor_init_expr.get())) {
                selected_ctor_sym = ctor_expr->ctor_sym;
                is_list_init = ctor_expr->is_list_init;
                auto owned_ctor_expr = std::unique_ptr<CppConstructExpr>(
                    static_cast<CppConstructExpr*>(ctor_init_expr.release()));
                constructor_args = std::move(owned_ctor_expr->args);
                initializer.reset();
            } else {
                initializer = std::move(ctor_init_expr);
            }
        }
    }

    if (!selected_ctor_sym && initializer) {
        QualType init_target_type = is_array_form ? allocated_type : pointee_type;
        initializer = process_initializer_for_type(
            std::move(initializer),
            init_target_type,
            loc);
        if (initializer && dyn_cast<ErrorExpr>(initializer.get())) {
            return std::move(initializer);
        }
        if (auto* init_list = dyn_cast<InitListExpr>(initializer.get())) {
            is_list_init = !init_list->is_paren_init;
        }
    }

    std::shared_ptr<Symbol> selected_deallocator_sym = nullptr;
    if (selected_ctor_sym) {
        std::vector<std::unique_ptr<Expr>> deallocator_lookup_args;
        deallocator_lookup_args.reserve(1 + placement_args.size());
        deallocator_lookup_args.push_back(
            collect_integer_literal("0", get_builtin_int(), loc));
        for (auto& arg : placement_args) {
            deallocator_lookup_args.push_back(std::move(arg));
        }
        placement_args.clear();

        if (auto dealloc_error = select_cpp_allocation_like_function(
                deallocator_name,
                pointee_record,
                is_global_allocation,
                deallocator_lookup_args,
                loc,
                selected_deallocator_sym)) {
            return dealloc_error;
        }

        placement_args.reserve(deallocator_lookup_args.size() > 0
            ? deallocator_lookup_args.size() - 1
            : 0);
        for (size_t idx = 1; idx < deallocator_lookup_args.size(); ++idx) {
            placement_args.push_back(std::move(deallocator_lookup_args[idx]));
        }
    }

    return collect_make<CppNewExpr>(
        allocated_type,
        result_type,
        std::move(placement_args),
        std::move(initializer),
        std::move(constructor_args),
        std::move(selected_allocator_sym),
        std::move(selected_deallocator_sym),
        std::move(selected_ctor_sym),
        is_array_form,
        is_global_allocation,
        is_list_init,
        loc);
}

std::unique_ptr<Expr> Collect::collect_cpp_delete_expression(
    std::unique_ptr<Expr> operand,
    bool is_array_form,
    bool is_global_delete,
    SrcLoc loc) {
    if (!operand) {
        report_error("delete-expression requires an operand", loc);
        return collect_error_expression("delete-expression requires an operand", loc);
    }

    operand = collect_apply_standard_conversions(
        std::move(operand),
        ExprUseContext::RValue);

    auto type_is_dependent_or_deferred =
        [&](QualType type) {
            return type &&
                   (type_depends_on_template_parameters(type, ast_ctx_.get()) ||
                    contains_deferred_semantic_type(type.get_shared()) ||
                    auto_type_utils::auto_type_flavors_in(type.get_shared()) != 0);
        };
    auto build_dependent_delete =
        [&](std::unique_ptr<Expr> delete_operand,
            QualType dependent_destroyed_type) -> std::unique_ptr<Expr> {
            return collect_make<CppDeleteExpr>(
                std::move(delete_operand),
                QualType(get_builtin_void()),
                dependent_destroyed_type,
                nullptr,
                nullptr,
                CppDeleteExpr::DestructionKind::None,
                is_array_form,
                is_global_delete,
                loc);
        };

    QualType operand_expr_type = operand ? operand->get_type() : QualType();
    if ((operand &&
         expression_depends_on_template_parameters(operand.get())) ||
        type_is_dependent_or_deferred(operand_expr_type)) {
        return build_dependent_delete(std::move(operand), QualType(nullptr));
    }

    QualType destroyed_type = nullptr;
    auto operand_type = operand ? desugar_type(remove_reference(operand_expr_type))
                                : QualType();
    auto pointer_type = operand_type.as_shared<PointerType>();
    if (!pointer_type) {
        if (operand && is_null_pointer_constant_expr(operand.get())) {
            QualType void_ptr(std::make_shared<PointerType>(QualType(get_builtin_void())));
            operand = cast_if_needed(std::move(operand), void_ptr);
            operand_expr_type = operand ? operand->get_type() : QualType();
            pointer_type = desugar_type(remove_reference(
                operand_expr_type)).as_shared<PointerType>();
        }
    }
    if (!pointer_type) {
        report_error("delete-expression requires a pointer operand", loc);
        return collect_error_expression("delete-expression requires a pointer operand", loc);
    }
    destroyed_type = remove_reference(pointer_type->pointed_type);
    if (type_is_dependent_or_deferred(destroyed_type)) {
        return build_dependent_delete(std::move(operand), destroyed_type);
    }
    QualType canonical_destroyed = desugar_type(destroyed_type);
    auto destroyed_kind = canonical_type_kind(canonical_destroyed);

    if (!canonical_destroyed || destroyed_kind == TypeKind::Function ||
        destroyed_kind == TypeKind::Reference) {
        report_error("delete-expression requires a pointer to object type", loc);
        return collect_error_expression(
            "delete-expression requires a pointer to object type",
            loc);
    }

    if (canonical_destroyed->isVoid()) {
        report_warning("deleting 'void *' is undefined", loc);
    } else if (canonical_destroyed->isIncomplete()) {
        report_warning(
            "delete-expression has pointer to incomplete type '" +
                canonical_destroyed.to_string() + "'",
            loc);
    }

    auto destroyed_record = canonical_destroyed.as_shared<ObjectType>();
    const ObjectDecl* destroyed_record_decl =
        destroyed_record ? dyn_cast<ObjectDecl>(destroyed_record->get_decl()) : nullptr;
    const RecordSemanticState* destroyed_record_state =
        destroyed_record_decl ? record_semantics_cache_lookup(destroyed_record_decl)
                              : nullptr;

    std::shared_ptr<Symbol> selected_destructor_sym = nullptr;
    CppDeleteExpr::DestructionKind destruction_kind =
        CppDeleteExpr::DestructionKind::None;
    if (destroyed_record &&
        destroyed_record_state &&
        !destroyed_record_state->destructors.empty()) {
        auto describe_destructor = [](const RecordSemanticState::Destructor& dtor) {
            std::string description = dtor.name + "()";
            if (dtor.is_deleted) {
                description += " = delete";
            }
            if (dtor.declared_access != RecordMemberAccess::Public) {
                description += " [not accessible]";
            }
            return description;
        };
        auto describe_destructor_candidates =
            [&](const std::vector<size_t>& indices) {
                std::string out;
                size_t emitted = 0;
                for (size_t idx : indices) {
                    if (idx >= destroyed_record_state->destructors.size()) {
                        continue;
                    }
                    if (!out.empty()) {
                        out += ", ";
                    }
                    out += describe_destructor(destroyed_record_state->destructors[idx]);
                    ++emitted;
                    if (emitted == 4 && indices.size() > emitted) {
                        out += ", ...";
                        break;
                    }
                }
                return out;
            };

        std::vector<size_t> viable_indices;
        viable_indices.reserve(destroyed_record_state->destructors.size());
        for (size_t idx = 0; idx < destroyed_record_state->destructors.size(); ++idx) {
            const auto& dtor = destroyed_record_state->destructors[idx];
            if (!cpp_destructor_is_viable_candidate(dtor, false)) {
                continue;
            }
            viable_indices.push_back(idx);
        }

        if (viable_indices.empty()) {
            std::vector<size_t> all_indices;
            all_indices.reserve(destroyed_record_state->destructors.size());
            for (size_t idx = 0; idx < destroyed_record_state->destructors.size(); ++idx) {
                all_indices.push_back(idx);
            }
            std::string candidates = describe_destructor_candidates(all_indices);
            report_error(
                "no viable destructor for type '" +
                    canonical_destroyed.to_string() + "'" +
                    (candidates.empty() ? "" : "; candidate destructors: " + candidates),
                loc);
            return collect_error_expression("no viable destructor", loc);
        }
        const auto& selected_destructor =
            destroyed_record_state->destructors[viable_indices.front()];
        selected_destructor_sym = selected_destructor.symbol;
        destruction_kind = selected_destructor.is_virtual
            ? CppDeleteExpr::DestructionKind::Virtual
            : CppDeleteExpr::DestructionKind::Direct;
    } else if (!is_array_form && destroyed_record) {
        destruction_kind = CppDeleteExpr::DestructionKind::Direct;
    }

    if (is_array_form &&
        destroyed_record_state &&
        destroyed_record_state->definition_data.has_user_declared_destructor) {
        report_error(
            "delete[] for class types with user-declared destructor is not supported yet",
            loc);
        return collect_error_expression("delete[] class-object destruction not supported yet", loc);
    }

    std::string deallocator_name = is_array_form ? "operatordelete[]" : "operatordelete";
    std::vector<std::unique_ptr<Expr>> deallocator_call_args;
    deallocator_call_args.push_back(
        collect_integer_literal("0", get_builtin_int(), loc));
    std::shared_ptr<Symbol> selected_deallocator_sym = nullptr;
    if (auto dealloc_error = select_cpp_allocation_like_function(
            deallocator_name,
            destroyed_record,
            is_global_delete,
            deallocator_call_args,
            loc,
            selected_deallocator_sym)) {
        return dealloc_error;
    }

    return collect_make<CppDeleteExpr>(
        std::move(operand),
        QualType(get_builtin_void()),
        destroyed_type,
        std::move(selected_deallocator_sym),
        std::move(selected_destructor_sym),
        destruction_kind,
        is_array_form,
        is_global_delete,
        loc);
}

std::unique_ptr<Expr> Collect::collect_cpp_pseudo_destructor_expression(
    std::unique_ptr<Expr> base,
    QualType destroyed_type,
    bool is_arrow,
    SrcLoc loc) {
    if (!base) {
        report_error(
            "pseudo-destructor expression requires an object operand",
            loc);
        return collect_error_expression(
            "pseudo-destructor expression requires an object operand",
            loc);
    }
    if (destroyed_type &&
        contains_deferred_semantic_type(destroyed_type.get_shared())) {
        destroyed_type = resolve_typeof_types(destroyed_type, loc);
    }
    if (!destroyed_type) {
        report_error(
            "pseudo-destructor expression requires a valid destroyed type",
            loc);
        return collect_error_expression("invalid pseudo-destructor type", loc);
    }

    if (is_arrow) {
        base = collect_apply_standard_conversions(
            std::move(base),
            ExprUseContext::RValue);
    }

    auto build_expr =
        [&](std::unique_ptr<Expr> object_base,
            QualType object_destroyed_type,
            std::shared_ptr<Symbol> destructor_sym)
            -> std::unique_ptr<Expr> {
            return collect_make<CppPseudoDestructorExpr>(
                std::move(object_base),
                object_destroyed_type,
                QualType(get_builtin_void()),
                std::move(destructor_sym),
                is_arrow,
                loc);
        };

    QualType base_type = base->get_type();
    if (!base_type) {
        report_error("pseudo-destructor operand has unknown type", loc);
        return collect_error_expression("pseudo-destructor operand has unknown type", loc);
    }

    QualType object_type = remove_reference(base_type, ast_ctx_.get());
    if (is_arrow) {
        auto pointer_type =
            remove_reference_and_desugar(base_type, ast_ctx_.get())
                .as_shared<PointerType>();
        if (!pointer_type) {
            report_error("pseudo-destructor '->' requires pointer operand", loc);
            return collect_error_expression("invalid pseudo-destructor operand", loc);
        }
        object_type = pointer_type->pointed_type;
    }

    if (type_depends_on_template_parameters(object_type, ast_ctx_.get()) ||
        type_depends_on_template_parameters(destroyed_type, ast_ctx_.get()) ||
        expression_depends_on_template_parameters(base.get())) {
        return build_expr(std::move(base), destroyed_type, nullptr);
    }

    QualType canonical_object_type =
        remove_reference_and_desugar(object_type, ast_ctx_.get());
    QualType canonical_destroyed_type =
        remove_reference_and_desugar(destroyed_type, ast_ctx_.get());
    if (!canonical_object_type || !canonical_destroyed_type ||
        !same_type_ignoring_all_qualifiers(
            canonical_object_type,
            canonical_destroyed_type,
            ast_ctx_.get())) {
        report_error(
            "pseudo-destructor type '" + destroyed_type.to_string() +
                "' does not match object type '" + object_type.to_string() +
                "'",
            loc);
        return collect_error_expression(
            "pseudo-destructor type does not match object type",
            loc);
    }

    if (!cpp_type_is_destructible(destroyed_type, false, ast_ctx_.get())) {
        report_error(
            "type '" + destroyed_type.to_string() +
                "' is not destructible in pseudo-destructor expression",
            loc);
        return collect_error_expression("type is not destructible", loc);
    }

    std::shared_ptr<Symbol> destructor_sym = nullptr;
    auto record_type = canonical_destroyed_type.as_shared<ObjectType>();
    auto* record_decl =
        record_type ? dyn_cast<ObjectDecl>(record_type->get_decl()) : nullptr;
    const RecordSemanticState* record_state =
        record_decl ? record_semantics_cache_lookup(record_decl) : nullptr;
    if (record_state) {
        for (const auto& dtor : record_state->destructors) {
            if (!cpp_destructor_is_viable_candidate(dtor, false)) {
                continue;
            }
            destructor_sym = dtor.symbol;
            break;
        }
    }

    return build_expr(std::move(base), destroyed_type, std::move(destructor_sym));
}

std::unique_ptr<Expr> Collect::collect_cpp_typeid_type(QualType type_operand,
                                                       SrcLoc loc) {
    if (!type_operand) {
        report_error("typeid requires a valid type operand", loc);
        return collect_error_expression("typeid requires a valid type operand", loc);
    }
    // `typeid(T)` is another semantic-demand site for template-id types, so it
    // must instantiate supported class specializations before RTTI/codegen.
    if (contains_deferred_semantic_type(type_operand.get_shared())) {
        type_operand = finalize_deferred_semantic_type(type_operand, loc);
    }

    auto typeinfo_ty = ast_ctx_ && ast_ctx_->type_ctx
        ? ast_ctx_->type_ctx->get_cpp_type_info()
        : nullptr;
    if (!typeinfo_ty) {
        report_error("typeid requires compiler RTTI type support", loc);
        return collect_error_expression("typeid requires compiler RTTI type support", loc);
    }

    QualType result_type(std::make_shared<ReferenceType>(
        QualType(typeinfo_ty, QUAL_CONST),
        ReferenceKind::LValue));
    return collect_make<CppTypeIdExpr>(type_operand, result_type, loc);
}

std::unique_ptr<Expr> Collect::collect_cpp_typeid_expression(std::unique_ptr<Expr> expr_operand,
                                                             SrcLoc loc) {
    if (!expr_operand) {
        report_error("typeid requires a valid expression operand", loc);
        return collect_error_expression("typeid requires a valid expression operand", loc);
    }
    QualType operand_type = expr_operand->get_type();
    if (!operand_type) {
        report_error("typeid operand has unknown type", loc);
        return collect_error_expression("typeid operand has unknown type", loc);
    }
    if (contains_deferred_semantic_type(operand_type.get_shared())) {
        operand_type = finalize_deferred_semantic_type(operand_type, loc);
        if (!operand_type) {
            report_error("typeid operand has unknown type", loc);
            return collect_error_expression("typeid operand has unknown type", loc);
        }
    }

    auto typeinfo_ty = ast_ctx_ && ast_ctx_->type_ctx
        ? ast_ctx_->type_ctx->get_cpp_type_info()
        : nullptr;
    if (!typeinfo_ty) {
        report_error("typeid requires compiler RTTI type support", loc);
        return collect_error_expression("typeid requires compiler RTTI type support", loc);
    }

    QualType result_type(std::make_shared<ReferenceType>(
        QualType(typeinfo_ty, QUAL_CONST),
        ReferenceKind::LValue));
    return collect_make<CppTypeIdExpr>(std::move(expr_operand), result_type, loc);
}


std::unique_ptr<Expr> Collect::collect_sizeof_type(QualType type, SrcLoc loc) {

    auto node = collect_make<SizeOfExpr>(type, loc);
    finalize_sizeof_node(node.get(), type.get_shared(), loc);
    return node;
}

std::unique_ptr<Expr> Collect::collect_sizeof_pack_expression(
    std::string pack_name,
    const TemplateParameterDecl* parameter_pack,
    SrcLoc loc) const {
    if (!parameter_pack || !parameter_pack->is_parameter_pack) {
        report_error("sizeof... requires a template parameter pack", loc);
        return collect_error_expression("invalid sizeof... operand", loc);
    }

    auto node =
        collect_make<SizeOfPackExpr>(std::move(pack_name), parameter_pack, loc);
    auto size_t_type = get_builtin_ulong();
    node->result_type =
        size_t_type ? QualType(size_t_type) : QualType(get_builtin_int());
    return node;
}


std::unique_ptr<Expr> Collect::collect_sizeof_expression(std::unique_ptr<Expr> expr, SrcLoc loc) {

    expr = prepare_unevaluated_operand(std::move(expr), "sizeof");
    std::shared_ptr<CType> target_type = nullptr;
    if (expr) {
        target_type = expr->get_type().get_shared();
    }
    auto node = collect_make<SizeOfExpr>(std::move(expr), loc);
    finalize_sizeof_node(node.get(), target_type, loc);
    return node;
}


std::unique_ptr<Expr> Collect::collect_alignof_type(QualType type, SrcLoc loc) {

    auto node = collect_make<AlignOfExpr>(type.get_shared(), loc);
    finalize_alignof_node(node.get(), type.get_shared(), loc);
    return node;
}


std::unique_ptr<Expr> Collect::collect_alignof_expression(std::unique_ptr<Expr> expr, SrcLoc loc) {

    expr = prepare_unevaluated_operand(std::move(expr), "_Alignof");
    std::shared_ptr<CType> target_type = nullptr;
    if (expr) {
        target_type = expr->get_type().get_shared();
    }
    auto node = collect_make<AlignOfExpr>(std::move(expr), loc);
    node->type_operand = QualType(target_type);
    finalize_alignof_node(node.get(), target_type, loc);
    return node;
}

namespace {
std::shared_ptr<FunctionType> function_type_from_noexcept_callee(
    QualType type) {
    auto canonical = desugar_type(type);
    if (auto pointer = canonical.as_shared<PointerType>()) {
        canonical = desugar_type(pointer->pointed_type);
    } else if (auto block_pointer = canonical.as_shared<BlockPointerType>()) {
        canonical = desugar_type(block_pointer->pointed_type);
    }
    return canonical.as_shared<FunctionType>();
}

std::optional<bool> function_type_is_non_throwing_with_demand(
    Collect& collect,
    QualType type,
    SrcLoc loc) {
    auto function_type = function_type_from_noexcept_callee(type);
    if (!function_type) {
        return std::nullopt;
    }
    if (function_type->exception_spec ==
        FunctionExceptionSpecKind::NonThrowing) {
        return true;
    }
    if (function_type->exception_spec !=
            FunctionExceptionSpecKind::Dependent ||
        !function_type->exception_spec_expr) {
        return false;
    }

    ConstEvalResult eval = collect.evaluate_constant_expression_demand(
        function_type->exception_spec_expr.get(),
        ConstEvalMode::cpp_core_constant_expression(),
        loc);
    if (eval.status != ConstEvalStatus::Constant || !eval.value.has_value()) {
        return std::nullopt;
    }
    switch (eval.value->kind) {
        case ConstValueKind::Boolean:
            return eval.value->bool_value;
        case ConstValueKind::Integer:
            return eval.value->int_value.to_unsigned_u64() != 0;
        default:
            return std::nullopt;
    }
}

std::optional<bool> expression_is_known_noexcept_with_demand(
    Collect& collect,
    Expr* expr,
    SrcLoc loc) {
    auto* stripped = Collect::strip_implicit_casts(expr);
    while (auto* paren = dyn_cast<ParenExpr>(stripped)) {
        stripped = Collect::strip_implicit_casts(paren->subexpr.get());
    }
    if (!stripped) {
        return std::nullopt;
    }
    if (auto* call = dyn_cast<FuncCall>(stripped)) {
        if (!call->func) {
            return std::nullopt;
        }
        return function_type_is_non_throwing_with_demand(
            collect,
            call->func->get_type(),
            loc);
    }
    if (auto* member_call = dyn_cast<CppMemberCallExpr>(stripped)) {
        if (!member_call->lowered_call ||
            !member_call->lowered_call->func) {
            return std::nullopt;
        }
        return function_type_is_non_throwing_with_demand(
            collect,
            member_call->lowered_call->func->get_type(),
            loc);
    }
    if (auto* construct = dyn_cast<CppConstructExpr>(stripped)) {
        if (!construct->ctor_sym) {
            return std::nullopt;
        }
        return function_type_is_non_throwing_with_demand(
            collect,
            construct->ctor_sym->type,
            loc);
    }
    return std::nullopt;
}
} // namespace

std::unique_ptr<Expr> Collect::collect_cpp_noexcept_expression(
    std::unique_ptr<Expr> expr,
    SrcLoc loc) {
    if (!expr) {
        report_error("noexcept requires a valid expression operand", loc);
        return collect_error_expression("invalid noexcept operand", loc);
    }

    expr = prepare_unevaluated_operand(std::move(expr), "noexcept");
    if (!expr) {
        report_error("noexcept requires a valid expression operand", loc);
        return collect_error_expression("invalid noexcept operand", loc);
    }

    auto bool_type = QualType(get_builtin_bool());
    materialize_specialization_uses_for_noexcept_evaluation(expr.get(), loc);
    bool is_noexcept = cpp_expression_is_known_noexcept(expr.get(), ast_ctx_.get());
    if (!is_noexcept) {
        auto demand_noexcept =
            expression_is_known_noexcept_with_demand(*this, expr.get(), loc);
        if (demand_noexcept.has_value()) {
            is_noexcept = *demand_noexcept;
        }
    }
    if (is_noexcept) {
        return collect_integer_literal(
            "1",
            get_builtin_bool(),
            loc);
    }
    if (expression_depends_on_template_parameters(expr.get()) ||
        type_depends_on_template_parameters(expr->get_type(), ast_ctx_.get())) {
        return collect_make<CppNoexceptExpr>(
            std::move(expr),
            bool_type,
            loc);
    }

    return collect_integer_literal(
        "0",
        get_builtin_bool(),
        loc);
}


std::unique_ptr<Expr> Collect::collect_unary_operation(
    UnaryOpTypes uop,
    std::unique_ptr<Expr> expr,
    SrcLoc loc,
    TemplateDependencyCheckMode dependency_mode) {

    if (lang_opts_.is_cxx_mode() &&
        expr &&
        type_can_participate_in_cpp_operator_overload(
            expr->get_type(),
            ast_ctx_.get())) {
        std::string_view op_suffix = unary_operator_function_suffix(uop);
        if (!op_suffix.empty()) {
            std::string op_name = "operator";
            op_name += op_suffix;

            bool had_member_match = false;
            bool saw_private_method = false;
            bool saw_protected_method = false;
            std::vector<OverloadCallCandidate> overload_candidates;

            auto operand_record =
                remove_reference_and_desugar(
                    expr->get_type(),
                    ast_ctx_.get())
                    .as_shared<ObjectType>();
            if (auto candidate_error = append_member_overload_candidates(
                    operand_record.get(),
                    op_name,
                    expr.get(),
                    OverloadImplicitObjectArgKind::Regular,
                    overload_candidates,
                    had_member_match,
                    saw_private_method,
                    saw_protected_method,
                    loc)) {
                return candidate_error;
            }
            std::vector<std::unique_ptr<Expr>> explicit_args;
            if (unary_operator_is_postfix_incdec(uop)) {
                explicit_args.push_back(
                    collect_integer_literal("0", get_builtin_int(), loc));
            }
            append_unqualified_overload_candidates(
                op_name,
                OverloadImplicitObjectArgKind::Regular,
                overload_candidates);
            std::vector<Expr*> adl_args{expr.get()};
            append_adl_friend_overload_candidates(
                op_name,
                OverloadImplicitObjectArgKind::Regular,
                adl_args,
                overload_candidates,
                loc);
            append_unqualified_function_template_overload_candidates(
                op_name,
                expr.get(),
                OverloadImplicitObjectArgKind::Regular,
                explicit_args,
                overload_candidates,
                loc);

            if (overload_candidates.empty() && had_member_match) {
                if (auto inaccessible_error = report_inaccessible_member(
                        op_name,
                        saw_private_method,
                        saw_protected_method,
                        loc)) {
                    return inaccessible_error;
                }
            } else {
                std::shared_ptr<Symbol> selected_symbol = nullptr;
                OverloadImplicitObjectArgKind selected_implicit_object_arg_kind =
                    OverloadImplicitObjectArgKind::None;
                if (auto overload_error = select_overload_candidate(
                        op_name,
                        overload_candidates,
                        explicit_args,
                        expr.get(),
                        loc,
                        selected_symbol,
                        selected_implicit_object_arg_kind)) {
                    return overload_error;
                }

                if (selected_symbol) {
                    if (auto completion_error =
                            complete_selected_function_template_specialization_symbol(
                                selected_symbol,
                                loc,
                                "failed to instantiate selected operator function template specialization")) {
                        return completion_error;
                    }
                    auto implicit_object_arg =
                        build_overload_implicit_object_arg(
                            selected_implicit_object_arg_kind,
                            std::move(expr),
                            /*object_expr_is_pointer=*/false,
                            loc);

                    if (selected_implicit_object_arg_kind !=
                            OverloadImplicitObjectArgKind::None &&
                        implicit_object_arg) {
                        explicit_args.insert(
                            explicit_args.begin(), std::move(implicit_object_arg));
                    }

                    auto callee_expr = make_hidden_overload_callee(
                        std::move(selected_symbol), loc);
                    return collect_function_call(
                        std::move(callee_expr), std::move(explicit_args), loc);
                }
            }
        }
    }

    bool is_incdec = (uop == UnaryOpTypes::INCREMENT_PREFIX ||
        uop == UnaryOpTypes::DECREMENT_PREFIX ||
        uop == UnaryOpTypes::INCREMENT_POSTFIX ||
        uop == UnaryOpTypes::DECREMENT_POSTFIX);

    if (uop == UnaryOpTypes::REAL_PART || uop == UnaryOpTypes::IMAG_PART) {
        auto exp_type = expr ? expr->get_type() : QualType();
        if (!exp_type || !exp_type->isComplex()) {
            expr = collect_apply_standard_conversions(std::move(expr), ExprUseContext::RValue);
        }
    } else if (uop == UnaryOpTypes::LOGICAL_NOT) {
        expr = collect_contextual_bool_conversion(
            std::move(expr),
            loc,
            "logical not");
    } else if (uop != UnaryOpTypes::ADDRESS_OF && !is_incdec) {
        expr = collect_apply_standard_conversions(std::move(expr), ExprUseContext::RValue);
    }

    auto node = collect_make<UnaryOperation>(uop, std::move(expr), loc);
    auto exp_type = node->exp ? node->exp->get_type() : QualType();
    if (!exp_type) {
        return node;
    }

    bool operand_is_dependent = false;
    if (lang_opts_.is_cxx_mode()) {
        if (dependency_mode ==
            TemplateDependencyCheckMode::AfterTemplateSubstitution) {
            operand_is_dependent =
                cpp_expr_still_dependent_after_substitution(
                    node->exp.get(),
                    ast_ctx_.get());
        } else {
            operand_is_dependent =
                type_depends_on_template_parameters(exp_type, ast_ctx_.get()) ||
                expression_depends_on_template_parameters(node->exp.get());
        }
    }
    if (lang_opts_.is_cxx_mode() && operand_is_dependent) {
        QualType dependent_result_type =
            known_dependent_unary_result_type(uop, exp_type, ast_ctx_.get());
        if (!dependent_result_type) {
            dependent_result_type =
                QualType(std::make_shared<AutoType>(
                    AutoTypeFlavor::TemplateNonType));
        }
        return collect_make<DependentUnaryExpr>(
            uop,
            std::move(node->exp),
            dependent_result_type,
            loc);
    }

    switch (uop) {
        case UnaryOpTypes::ADDRESS_OF: {
            auto* raw = strip_implicit_casts_and_parens(node->exp.get());
            bool is_lvalue_operand = raw && raw->isLValue();
            if (lang_opts_.is_cxx_mode() && raw) {
                is_lvalue_operand =
                    classify_value_category(raw) == ValueCategory::LValue;
            }
            if (!raw ||
                (!is_lvalue_operand &&
                 !(raw->get_type() &&
                   canonical_type_kind(raw->get_type()) == TypeKind::Function))) {
                report_error("cannot take address of non-lvalue expression", loc);
            }
            if (auto* member = dyn_cast<MemberExpr>(raw)) {
                if (member->is_bitfield) {
                    report_error("cannot take address of bit-field", loc);
                }
            }
            node->ctype =
                QualType(std::make_shared<PointerType>(remove_reference(exp_type)));
            break;
        }
        case UnaryOpTypes::DEREFERENCE: {
            auto ptr_type = desugar_type(exp_type).as_shared<PointerType>();
            if (ptr_type) {
                // Keep spelled pointee type when available so typedef sugar
                // survives lvalue uses, but still allow typedef-wrapped pointers.
                if (auto spelled_ptr = exp_type.as_shared<PointerType>()) {
                    node->ctype = spelled_ptr->pointed_type;
                } else {
                    node->ctype = ptr_type->pointed_type;
                }
            } else {
                report_error("dereferencing non-pointer type", loc);
            }
            break;
        }
        case UnaryOpTypes::LOGICAL_NOT:
            node->ctype = lang_opts_.is_cxx_mode()
                              ? QualType(get_builtin_bool())
                              : QualType(get_builtin_int());
            break;
        case UnaryOpTypes::NEG:
        case UnaryOpTypes::POSITIVE:
            if (!is_arithmetic_adjacent(exp_type, ast_ctx_.get())) {
                report_error("invalid argument type to unary expression", loc);
            }
            if (allows_integral_promotion(exp_type, ast_ctx_.get())) {
                node->ctype = integer_promotion_type(exp_type);
            } else {
                node->ctype = exp_type;
            }
            break;
        case UnaryOpTypes::BITWISE_NOT:
            if (exp_type->isComplex()) {
                node->ctype = exp_type;
                break;
            }
            if (!is_integer_adjacent(exp_type, ast_ctx_.get())) {
                report_error("invalid argument type to unary expression", loc);
            }
            node->ctype = integer_promotion_type(exp_type);
            break;
        case UnaryOpTypes::INCREMENT_PREFIX:
        case UnaryOpTypes::DECREMENT_PREFIX:
        case UnaryOpTypes::INCREMENT_POSTFIX:
        case UnaryOpTypes::DECREMENT_POSTFIX:
            if (!is_modifiable_lvalue(node->exp.get())) {
                if (is_const_qualified_lvalue(node->exp.get())) {
                    report_error("cannot assign to variable of type '" + exp_type.to_string() + "'", loc);
                } else {
                    report_error("expression is not assignable", loc);
                }
            }
            if (!(is_arithmetic_adjacent(exp_type, ast_ctx_.get()) ||
                  canonical_type_kind(exp_type) == TypeKind::Pointer)) {
                report_error("invalid argument type for increment/decrement", loc);
            }
            node->ctype = exp_type;
            break;
        case UnaryOpTypes::REAL_PART:
        case UnaryOpTypes::IMAG_PART: {
            auto complex_type = exp_type.as_shared<ComplexType>();
            if (complex_type) {
                node->ctype = QualType(complex_type->element_type);
            }
            break;
        }
        default:
            break;
    }
    return node;
}

std::unique_ptr<Expr> Collect::collect_builtin_three_way_compare(
    std::unique_ptr<Expr> lhs,
    std::unique_ptr<Expr> rhs,
    SrcLoc loc) {
    struct CategoryMembers {
        QualType type;
        std::shared_ptr<Symbol> less;
        std::shared_ptr<Symbol> equivalent;
        std::shared_ptr<Symbol> greater;
        std::shared_ptr<Symbol> unordered;
    };

    auto make_error = [&](const std::string& message) -> std::unique_ptr<Expr> {
        report_error(message, loc);
        return collect_make<ErrorExpr>(message, loc);
    };

    auto diagnose_missing_compare = [&](const std::string& category_name)
        -> std::unique_ptr<Expr> {
        return make_error(
            "built-in '<=>' requires 'std::" + category_name +
            "'; include <compare>");
    };

    auto lookup_compare_category_type =
        [&](const std::string& category_name) -> QualType {
        auto current_context = session_.current_decl_context_
            ? session_.current_decl_context_.get()
            : (session_.translation_unit_decl_context_
                   ? session_.translation_unit_decl_context_.get()
                   : nullptr);
        if (!current_context) {
            return QualType();
        }

        LookupEngine::QualifiedNameSpec spec;
        spec.qualifiers = {"std"};
        spec.terminal_name = category_name;

        auto tag_lookup = LookupEngine::lookup_qualified_name(
            spec,
            current_context,
            LookupNamespace::Tag);
        if (tag_lookup.status == LookupEngine::QualifiedLookupStatus::Found &&
            tag_lookup.binding &&
            tag_lookup.binding->type) {
            return tag_lookup.binding->type;
        }

        auto ordinary_lookup = LookupEngine::lookup_qualified_name(
            spec,
            current_context,
            LookupNamespace::Ordinary,
            LookupEngine::OrdinaryFilter::TypedefOnly);
        if (ordinary_lookup.status ==
                LookupEngine::QualifiedLookupStatus::Found &&
            ordinary_lookup.symbol &&
            ordinary_lookup.symbol->type) {
            return ordinary_lookup.symbol->type;
        }
        if (ordinary_lookup.status ==
                LookupEngine::QualifiedLookupStatus::Found &&
            ordinary_lookup.binding &&
            ordinary_lookup.binding->type) {
            return ordinary_lookup.binding->type;
        }
        return QualType();
    };

    auto resolve_category_members =
        [&](CppBuiltinThreeWayCompareCategory category)
            -> std::optional<CategoryMembers> {
        const bool partial =
            category == CppBuiltinThreeWayCompareCategory::Partial;
        const std::string category_name =
            partial ? "partial_ordering" : "strong_ordering";
        QualType category_type = lookup_compare_category_type(category_name);
        if (!category_type) {
            diagnose_missing_compare(category_name);
            return std::nullopt;
        }
        auto record_type =
            desugar_type(category_type, ast_ctx_.get()).as_shared<ObjectType>();
        if (!record_type) {
            diagnose_missing_compare(category_name);
            return std::nullopt;
        }
        if (record_type->isIncomplete()) {
            diagnose_missing_compare(category_name);
            return std::nullopt;
        }

        auto find_static_member =
            [&](const std::string& member_name,
                bool required = true) -> std::shared_ptr<Symbol> {
            auto lookup =
                lookup_record_member_name(record_type.get(), member_name);
            if (lookup.static_data_matches == 1 &&
                lookup.single_static_data_member &&
                lookup.single_static_data_member->symbol) {
                auto member = lookup.single_static_data_member->symbol;
                QualType member_type =
                    remove_reference_and_desugar(member->type, ast_ctx_.get());
                QualType canonical_category =
                    remove_reference_and_desugar(category_type, ast_ctx_.get());
                if (member_type &&
                    canonical_category &&
                    !member_type.equals_unqualified(canonical_category)) {
                    report_error(
                        "'std::" + category_name + "::" + member_name +
                        "' must have type 'std::" + category_name + "'",
                        loc);
                    return nullptr;
                }
                return member;
            }
            if (required) {
                report_error(
                    "built-in '<=>' requires 'std::" + category_name +
                    "::" + member_name + "'; include <compare>",
                    loc);
            }
            return nullptr;
        };

        CategoryMembers members;
        members.type = category_type;
        members.less = find_static_member("less");
        members.greater = find_static_member("greater");
        if (partial) {
            members.equivalent = find_static_member("equivalent");
            members.unordered = find_static_member("unordered");
        } else {
            members.equivalent = find_static_member("equal", false);
            if (!members.equivalent) {
                members.equivalent = find_static_member("equivalent");
            }
        }

        if (!members.less || !members.equivalent || !members.greater ||
            (partial && !members.unordered)) {
            return std::nullopt;
        }
        return members;
    };

    auto make_node =
        [&](CppBuiltinThreeWayCompareCategory category,
            CategoryMembers members) -> std::unique_ptr<Expr> {
        return collect_make<CppBuiltinThreeWayCompareExpr>(
            std::move(lhs),
            std::move(rhs),
            members.type,
            category,
            std::move(members.less),
            std::move(members.equivalent),
            std::move(members.greater),
            std::move(members.unordered),
            loc);
    };

    lhs = collect_apply_standard_conversions(std::move(lhs), ExprUseContext::RValue);
    rhs = collect_apply_standard_conversions(std::move(rhs), ExprUseContext::RValue);
    if (!lhs || !rhs) {
        return make_error("invalid operands to binary expression");
    }

    QualType lhs_ty = lhs->get_type();
    QualType rhs_ty = rhs->get_type();
    auto lhs_kind = canonical_type_kind(lhs_ty, ast_ctx_.get());
    auto rhs_kind = canonical_type_kind(rhs_ty, ast_ctx_.get());
    auto refresh_types = [&]() {
        lhs_ty = lhs ? lhs->get_type() : QualType();
        rhs_ty = rhs ? rhs->get_type() : QualType();
        lhs_kind = canonical_type_kind(lhs_ty, ast_ctx_.get());
        rhs_kind = canonical_type_kind(rhs_ty, ast_ctx_.get());
    };

    auto build_strong = [&]() -> std::unique_ptr<Expr> {
        auto members =
            resolve_category_members(CppBuiltinThreeWayCompareCategory::Strong);
        if (!members) {
            return collect_make<ErrorExpr>("missing comparison category", loc);
        }
        return make_node(
            CppBuiltinThreeWayCompareCategory::Strong,
            std::move(*members));
    };
    auto build_partial = [&]() -> std::unique_ptr<Expr> {
        auto members =
            resolve_category_members(CppBuiltinThreeWayCompareCategory::Partial);
        if (!members) {
            return collect_make<ErrorExpr>("missing comparison category", loc);
        }
        return make_node(
            CppBuiltinThreeWayCompareCategory::Partial,
            std::move(*members));
    };

    if (lhs_kind == TypeKind::MemberPointer ||
        rhs_kind == TypeKind::MemberPointer) {
        return make_error(
            "member pointer operands are not supported for built-in '<=>'");
    }

    bool lhs_nullptr = is_nullptr_type(lhs_ty, ast_ctx_.get());
    bool rhs_nullptr = is_nullptr_type(rhs_ty, ast_ctx_.get());
    if (lhs_kind == TypeKind::Pointer ||
        rhs_kind == TypeKind::Pointer ||
        lhs_nullptr ||
        rhs_nullptr) {
        if (lhs_kind == TypeKind::Pointer && rhs_kind == TypeKind::Pointer) {
            auto lhs_ptr = desugar_type(lhs_ty, ast_ctx_.get()).as_shared<PointerType>();
            auto rhs_ptr = desugar_type(rhs_ty, ast_ctx_.get()).as_shared<PointerType>();
            bool lhs_void = lhs_ptr && lhs_ptr->pointed_type && lhs_ptr->pointed_type->isVoid();
            bool rhs_void = rhs_ptr && rhs_ptr->pointed_type && rhs_ptr->pointed_type->isVoid();
            if (!lhs_void && !rhs_void &&
                !pointers_to_compatible_types(lhs_ty, rhs_ty)) {
                report_warning("comparison of distinct pointer types", loc);
            }
            if (!lhs_ty.equals_unqualified(rhs_ty)) {
                rhs = collect_make<ImplicitCast>(
                    ImplicitCastTypes::RAW_CAST, std::move(rhs), lhs_ty);
                refresh_types();
            }
            return build_strong();
        }

        if (lhs_kind == TypeKind::Pointer &&
            (rhs_nullptr ||
             (is_integer_adjacent(rhs_ty, ast_ctx_.get()) &&
              is_null_pointer_constant_expr(rhs.get())))) {
            rhs = cast_if_needed(std::move(rhs), lhs_ty);
            refresh_types();
            return build_strong();
        }
        if (rhs_kind == TypeKind::Pointer &&
            (lhs_nullptr ||
             (is_integer_adjacent(lhs_ty, ast_ctx_.get()) &&
              is_null_pointer_constant_expr(lhs.get())))) {
            lhs = cast_if_needed(std::move(lhs), rhs_ty);
            refresh_types();
            return build_strong();
        }

        return make_error("invalid operands to binary expression");
    }

    if (lhs_kind == TypeKind::BlockPointer ||
        rhs_kind == TypeKind::BlockPointer) {
        return make_error(
            "block pointer operands are not supported for built-in '<=>'");
    }

    if (lhs_kind == TypeKind::Vector || rhs_kind == TypeKind::Vector ||
        (lhs_ty && lhs_ty->isComplex()) ||
        (rhs_ty && rhs_ty->isComplex())) {
        return make_error("invalid operands to binary expression");
    }

    bool lhs_scoped_enum = is_scoped_enum_type(lhs_ty, ast_ctx_.get());
    bool rhs_scoped_enum = is_scoped_enum_type(rhs_ty, ast_ctx_.get());
    if (lhs_scoped_enum || rhs_scoped_enum) {
        if (lhs_scoped_enum &&
            rhs_scoped_enum &&
            same_unqualified_enum_type(lhs_ty, rhs_ty, ast_ctx_.get())) {
            return build_strong();
        }
        return make_error("invalid operands to binary expression");
    }

    if (!is_arithmetic_adjacent(lhs_ty, ast_ctx_.get()) ||
        !is_arithmetic_adjacent(rhs_ty, ast_ctx_.get())) {
        return make_error("invalid operands to binary expression");
    }

    QualType common = usual_arithmetic_conversion_type(lhs_ty, rhs_ty);
    if (!common) {
        return make_error("invalid operands to binary expression");
    }
    lhs = cast_if_needed(std::move(lhs), common);
    rhs = cast_if_needed(std::move(rhs), common);
    refresh_types();

    if (common->isFloatingPoint()) {
        return build_partial();
    }
    return build_strong();
}

std::unique_ptr<Expr> Collect::collect_binary_operation(
    std::unique_ptr<Expr> lhs,
    std::unique_ptr<Expr> rhs,
    BinOpTypes bop,
    SrcLoc loc) {
    return collect_binary_operation_impl(
        std::move(lhs),
        std::move(rhs),
        bop,
        loc,
        /*allow_cpp_rewritten_candidates=*/true);
}

std::unique_ptr<Expr> Collect::collect_binary_operation_impl(
    std::unique_ptr<Expr> lhs,
    std::unique_ptr<Expr> rhs,
    BinOpTypes bop,
    SrcLoc loc,
    bool allow_cpp_rewritten_candidates) {

    if (is_compound_assignment_binop(bop)) {
        return collect_compound_assign_operation(
            std::move(lhs),
            std::move(rhs),
            bop,
            loc);
    }

    if (bop == BinOpTypes::MEMBER_PTR_DOT ||
        bop == BinOpTypes::MEMBER_PTR_ARROW) {
        return collect_member_pointer_access_expression(
            std::move(lhs),
            std::move(rhs),
            bop == BinOpTypes::MEMBER_PTR_ARROW,
            loc);
    }

    if (lang_opts_.is_cxx_mode()) {
        realize_deferred_expr_type_after_substitution(lhs.get());
        realize_deferred_expr_type_after_substitution(rhs.get());
    }

    bool has_dependent_operand =
        lang_opts_.is_cxx_mode() &&
        (expression_depends_on_template_parameters(lhs.get()) ||
         expression_depends_on_template_parameters(rhs.get()));
    if (has_dependent_operand) {
        auto dependent_assignment_result_type = [&]() -> QualType {
            QualType lhs_type = lhs ? lhs->get_type() : QualType();
            if (canonical_type_kind(lhs_type, ast_ctx_.get()) == TypeKind::Reference) {
                return remove_reference(lhs_type, ast_ctx_.get());
            }
            return lhs_type;
        };
        QualType dependent_result_type;
        if (is_assignment_binop(bop)) {
            dependent_result_type = dependent_assignment_result_type();
        } else if (bop == BinOpTypes::COMMA && rhs) {
            dependent_result_type = rhs->get_type();
        } else if (bop == BinOpTypes::LOGICAL_AND ||
                   bop == BinOpTypes::LOGICAL_OR) {
            dependent_result_type = lang_opts_.is_cxx_mode()
                ? QualType(get_builtin_bool())
                : QualType(get_builtin_int());
        } else if (bop == BinOpTypes::LESS_THAN ||
                   bop == BinOpTypes::GREATER_THAN ||
                   bop == BinOpTypes::LESS_EQUAL_THAN ||
                   bop == BinOpTypes::GREATER_EQUAL_THAN ||
                   bop == BinOpTypes::EQUAL ||
                   bop == BinOpTypes::NOT_EQUAL) {
            dependent_result_type = QualType(get_builtin_int());
        } else {
            dependent_result_type =
                QualType(std::make_shared<AutoType>(AutoTypeFlavor::TemplateNonType));
        }
        return collect_make<DependentBinaryExpr>(
            std::move(lhs),
            std::move(rhs),
            bop,
            dependent_result_type,
            loc);
    }

    // In C++, user-defined operators get first chance before built-in operator
    // typing/conversion rules.
    if (auto overloaded =
            try_cpp_binary_operator_overload(
                lhs,
                rhs,
                bop,
                loc,
                allow_cpp_rewritten_candidates)) {
        return overloaded;
    }

    if (bop == BinOpTypes::THREE_WAY_COMPARE) {
        return collect_builtin_three_way_compare(
            std::move(lhs), std::move(rhs), loc);
    }

    if (bop == BinOpTypes::ASSIGN) {
        rhs = collect_apply_standard_conversions(std::move(rhs), ExprUseContext::RValue);
    } else if (bop == BinOpTypes::LOGICAL_AND ||
               bop == BinOpTypes::LOGICAL_OR) {
        lhs = collect_contextual_bool_conversion(
            std::move(lhs),
            loc,
            "logical operator");
        rhs = collect_contextual_bool_conversion(
            std::move(rhs),
            loc,
            "logical operator");
    } else {
        lhs = collect_apply_standard_conversions(std::move(lhs), ExprUseContext::RValue);
        if (!(lang_opts_.is_cxx_mode() && bop == BinOpTypes::COMMA)) {
            rhs = collect_apply_standard_conversions(std::move(rhs), ExprUseContext::RValue);
        }
    }
    auto node = make_ast<BinaryOperation>(*ast_ctx_, std::move(lhs), std::move(rhs), bop);
    node->location = loc;
    auto lhs_ty = node->left ? node->left->get_type() : QualType();
    auto rhs_ty = node->right ? node->right->get_type() : QualType();
    auto lhs_kind = canonical_type_kind(lhs_ty);
    auto rhs_kind = canonical_type_kind(rhs_ty);
    auto refresh_types = [&]() {
        lhs_ty = node->left ? node->left->get_type() : QualType();
        rhs_ty = node->right ? node->right->get_type() : QualType();
        lhs_kind = canonical_type_kind(lhs_ty);
        rhs_kind = canonical_type_kind(rhs_ty);
    };
    // Coerce both operands to a common arithmetic type via the usual
    // arithmetic conversions (C11 6.3.1.8).  Handles vector-scalar promotion:
    // when one operand is a vector and the other a scalar, the scalar is
    // broadcast to the vector type rather than forcing scalar promotion.
    auto ensure_arithmetic_common = [&]() -> QualType {
        if (lhs_ty && rhs_ty) {
            bool lhs_vector = lhs_kind == TypeKind::Vector;
            bool rhs_vector = rhs_kind == TypeKind::Vector;
            if (lhs_vector ^ rhs_vector) {
                // For vector-scalar arithmetic, broadcast/coerce the scalar to
                // the vector element domain instead of forcing scalar result type.
                QualType vector_type = lhs_vector ? lhs_ty : rhs_ty;
                QualType scalar_type = lhs_vector ? rhs_ty : lhs_ty;
                if (is_arithmetic_adjacent(scalar_type, ast_ctx_.get())) {
                    if (lhs_vector) {
                        node->right = cast_if_needed(std::move(node->right), vector_type);
                    } else {
                        node->left = cast_if_needed(std::move(node->left), vector_type);
                    }
                    refresh_types();
                    return vector_type;
                }
            }
        }
        auto common = usual_arithmetic_conversion_type(lhs_ty, rhs_ty);
        if (!common) {
            return QualType();
        }
        node->left = cast_if_needed(std::move(node->left), common);
        node->right = cast_if_needed(std::move(node->right), common);
        refresh_types();
        return common;
    };
    // Comparison result type: vector comparisons produce a vector of the
    // same width; scalar comparisons produce int.
    auto comparison_result_type = [&]() -> QualType {
        if (lhs_kind == TypeKind::Vector) {
            return lhs_ty;
        }
        if (rhs_kind == TypeKind::Vector) {
            return rhs_ty;
        }
        return QualType(get_builtin_int());
    };

    switch (bop) {
        // --- Assignment ---
        case BinOpTypes::ASSIGN: {
            QualType lhs_assignment_type = lhs_ty;
            if (lhs_kind == TypeKind::Reference) {
                lhs_assignment_type = remove_reference(lhs_ty);
            }
            auto lhs_assignment_kind = canonical_type_kind(lhs_assignment_type);

            if (!is_modifiable_lvalue(node->left.get())) {
                if (is_const_qualified_lvalue(node->left.get())) {
                    report_error("cannot assign to variable of type '" + lhs_ty.to_string() + "'", loc);
                } else {
                    report_error("expression is not assignable", loc);
                }
            }
            if (lhs_ty && rhs_ty &&
                lhs_assignment_kind == TypeKind::MemberPointer &&
                rhs_kind == TypeKind::MemberPointer) {
                if (!member_pointer_convertible_to(rhs_ty, lhs_assignment_type)) {
                    report_error("incompatible member pointer types in assignment ('" +
                        lhs_assignment_type.to_string() + "' from '" + rhs_ty.to_string() + "')",
                        loc);
                }
            } else if (lhs_ty && rhs_ty &&
                lhs_assignment_kind == TypeKind::MemberPointer &&
                is_integer_adjacent(rhs_ty, ast_ctx_.get())) {
                if (!is_null_pointer_constant_expr(node->right.get())) {
                    report_error("incompatible integer to member pointer conversion in assignment",
                                 loc);
                }
            } else if (lhs_ty && rhs_ty &&
                lhs_assignment_kind == TypeKind::Pointer &&
                rhs_kind == TypeKind::Pointer) {
                auto lhs_ptr = desugar_type(lhs_assignment_type).as_shared<PointerType>();
                auto rhs_ptr = desugar_type(rhs_ty).as_shared<PointerType>();
                bool lhs_void = lhs_ptr && lhs_ptr->pointed_type && lhs_ptr->pointed_type->isVoid();
                bool rhs_void = rhs_ptr && rhs_ptr->pointed_type && rhs_ptr->pointed_type->isVoid();
                if (!lhs_void && !rhs_void && !pointers_to_compatible_types(lhs_assignment_type, rhs_ty)) {
                    report_warning("incompatible pointer types in assignment ('" +
                        lhs_assignment_type.to_string() + "' from '" + rhs_ty.to_string() + "')", loc);
                }
            } else if (lhs_ty && rhs_ty &&
                lhs_assignment_kind == TypeKind::Pointer &&
                is_integer_adjacent(rhs_ty, ast_ctx_.get())) {
                if (!is_null_pointer_constant_expr(node->right.get())) {
                    if (lang_opts_.implicit_int) {
                        report_warning("incompatible integer to pointer conversion in assignment", loc);
                    } else {
                        report_error("incompatible integer to pointer conversion in assignment", loc);
                    }
                }
            } else if (lhs_ty && rhs_ty &&
                lhs_assignment_kind == TypeKind::BlockPointer &&
                is_integer_adjacent(rhs_ty, ast_ctx_.get())) {
                if (!is_null_pointer_constant_expr(node->right.get())) {
                    if (lang_opts_.implicit_int) {
                        report_warning("incompatible integer to block pointer conversion in assignment", loc);
                    } else {
                        report_error("incompatible integer to block pointer conversion in assignment", loc);
                    }
                }
            } else if (lhs_ty && rhs_ty &&
                lhs_assignment_type &&
                is_integer_adjacent(lhs_assignment_type, ast_ctx_.get()) &&
                (rhs_kind == TypeKind::Pointer ||
                 rhs_kind == TypeKind::BlockPointer)) {
                // Preserve historical C-extension behavior for implicit-int mode:
                // downgrade pointer->integer assignment diagnostics to warnings.
                bool lhs_is_bool = false;
                if (auto lhs_builtin = lhs_assignment_type.as_shared<BuiltinType>()) {
                    lhs_is_bool = lhs_builtin->builtin_kind == BuiltinTypes::Bool;
                }
                if (!lhs_is_bool) {
                    if (lang_opts_.implicit_int) {
                        report_warning("incompatible pointer to integer conversion in assignment", loc);
                    } else {
                        report_error("incompatible pointer to integer conversion in assignment", loc);
                    }
                }
            }
            if (lhs_ty && rhs_ty &&
                is_scoped_enum_type(lhs_assignment_type, ast_ctx_.get()) &&
                !same_unqualified_enum_type(lhs_assignment_type,
                                            rhs_ty,
                                            ast_ctx_.get())) {
                report_error("assigning to '" + lhs_assignment_type.to_string() +
                                 "' from incompatible type '" +
                                 rhs_ty.to_string() + "'",
                             loc);
            }
            node->right = cast_if_needed(std::move(node->right), lhs_assignment_type);
            node->ctype = lhs_assignment_type ? lhs_assignment_type : rhs_ty;
            break;
        }
        // --- Logical operators ---
        case BinOpTypes::LOGICAL_AND:
        case BinOpTypes::LOGICAL_OR: {
            node->ctype = lang_opts_.is_cxx_mode()
                              ? QualType(get_builtin_bool())
                              : QualType(get_builtin_int());
            break;
        }
        // --- Comparisons (equality + relational) ---
        // Handles: pointer comparison, nullptr adaptation, member-pointer
        // comparison, mixed pointer-integer, and arithmetic comparison.
        // "Ordered" comparisons (<, <=, >, >=) have stricter type rules than
        // equality (==, !=) — e.g., nullptr ordered comparison is invalid.
        case BinOpTypes::EQUAL:
        case BinOpTypes::NOT_EQUAL:
        case BinOpTypes::LESS_THAN:
        case BinOpTypes::LESS_EQUAL_THAN:
        case BinOpTypes::GREATER_THAN:
        case BinOpTypes::GREATER_EQUAL_THAN: {
            bool ordered = (bop == BinOpTypes::LESS_THAN ||
                bop == BinOpTypes::LESS_EQUAL_THAN ||
                bop == BinOpTypes::GREATER_THAN ||
                bop == BinOpTypes::GREATER_EQUAL_THAN);
            bool lhs_nullptr = is_nullptr_type(lhs_ty, ast_ctx_.get());
            bool rhs_nullptr = is_nullptr_type(rhs_ty, ast_ctx_.get());
            auto lhs_cmp_type = remove_reference(lhs_ty, ast_ctx_.get());
            auto rhs_cmp_type = remove_reference(rhs_ty, ast_ctx_.get());
            auto lhs_cmp_kind = canonical_type_kind(lhs_cmp_type, ast_ctx_.get());
            auto rhs_cmp_kind = canonical_type_kind(rhs_cmp_type, ast_ctx_.get());
            if (lhs_ty && rhs_ty &&
                lhs_cmp_kind == TypeKind::CppTypeInfo &&
                rhs_cmp_kind == TypeKind::CppTypeInfo) {
                if (lhs_kind == TypeKind::Reference) {
                    node->left = collect_apply_standard_conversions(
                        std::move(node->left), ExprUseContext::RValue);
                }
                if (rhs_kind == TypeKind::Reference) {
                    node->right = collect_apply_standard_conversions(
                        std::move(node->right), ExprUseContext::RValue);
                }
                refresh_types();
                if (ordered) {
                    report_invalid_binary_operands(
                        "binary expression", lhs_ty, rhs_ty, loc);
                }
                node->ctype = comparison_result_type();
                break;
            }
            if ((lhs_ty && lhs_ty->isComplex()) || (rhs_ty && rhs_ty->isComplex())) {
                if (ordered) {
                    report_error("invalid operands to binary expression (have '" +
                        lhs_ty.to_string() + "' and '" + rhs_ty.to_string() + "')", loc);
                } else {
                    auto common = ensure_arithmetic_common();
                    if (!common) {
                        report_error("invalid operands to binary expression", loc);
                    }
                }
                node->ctype = comparison_result_type();
                break;
            }
            bool lhs_scoped_enum = is_scoped_enum_type(lhs_ty, ast_ctx_.get());
            bool rhs_scoped_enum = is_scoped_enum_type(rhs_ty, ast_ctx_.get());
            if (lhs_ty && rhs_ty &&
                lhs_scoped_enum &&
                rhs_scoped_enum &&
                same_unqualified_enum_type(lhs_ty, rhs_ty, ast_ctx_.get())) {
                node->ctype = comparison_result_type();
                break;
            }
            if ((lhs_ty && lhs_scoped_enum) || (rhs_ty && rhs_scoped_enum)) {
                report_invalid_binary_operands("binary expression", lhs_ty, rhs_ty, loc);
                node->ctype = comparison_result_type();
                break;
            }
            if (lhs_ty && rhs_ty && (lhs_nullptr || rhs_nullptr)) {
                if (ordered) {
                    report_invalid_binary_operands("binary expression", lhs_ty, rhs_ty, loc);
                    node->ctype = comparison_result_type();
                    break;
                }

                // Adapt a nullptr_t operand for comparison with a pointer,
                // member pointer, or integer null constant on the other side.
                // Returns true if adaptation succeeded, false if the types
                // are incompatible.
                auto adapt_nullptr_operand = [&](bool lhs_is_nullptr) {
                    auto& nullptr_operand =
                        lhs_is_nullptr ? node->left : node->right;
                    auto& other_operand =
                        lhs_is_nullptr ? node->right : node->left;
                    QualType nullptr_type = lhs_is_nullptr ? lhs_ty : rhs_ty;
                    QualType other_type = lhs_is_nullptr ? rhs_ty : lhs_ty;
                    auto other_kind = lhs_is_nullptr ? rhs_kind : lhs_kind;

                    if (other_kind == TypeKind::Pointer ||
                        other_kind == TypeKind::MemberPointer ||
                        other_kind == TypeKind::BlockPointer) {
                        nullptr_operand =
                            cast_if_needed(std::move(nullptr_operand), other_type);
                        return true;
                    }
                    if (other_type &&
                        is_integer_adjacent(other_type, ast_ctx_.get()) &&
                        is_null_pointer_constant_expr(other_operand.get())) {
                        other_operand =
                            cast_if_needed(std::move(other_operand), nullptr_type);
                        return true;
                    }
                    return false;
                };

                if (!(lhs_nullptr && rhs_nullptr) &&
                    !adapt_nullptr_operand(lhs_nullptr)) {
                    report_invalid_binary_operands("binary expression", lhs_ty, rhs_ty, loc);
                }
                node->ctype = comparison_result_type();
                break;
            }
            if (lhs_ty && rhs_ty &&
                lhs_kind == TypeKind::MemberPointer &&
                rhs_kind == TypeKind::MemberPointer) {
                if (ordered) {
                    report_invalid_binary_operands("binary expression", lhs_ty, rhs_ty, loc);
                    node->ctype = comparison_result_type();
                    break;
                }
                auto rhs_to_lhs = analyze_member_pointer_conversion(rhs_ty, lhs_ty);
                auto lhs_to_rhs = analyze_member_pointer_conversion(lhs_ty, rhs_ty);
                if (!rhs_to_lhs.viable && !lhs_to_rhs.viable) {
                    report_warning("comparison of distinct member pointer types", loc);
                }
                if (!lhs_ty->equals(*rhs_ty.get_shared())) {
                    if (rhs_to_lhs.viable) {
                        node->right = cast_if_needed(std::move(node->right), lhs_ty);
                    } else if (lhs_to_rhs.viable) {
                        node->left = cast_if_needed(std::move(node->left), rhs_ty);
                    }
                }
                node->ctype = comparison_result_type();
                break;
            }
            if (lhs_ty && rhs_ty &&
                ((lhs_kind == TypeKind::MemberPointer &&
                  is_integer_adjacent(rhs_ty, ast_ctx_.get())) ||
                 (rhs_kind == TypeKind::MemberPointer &&
                  is_integer_adjacent(lhs_ty, ast_ctx_.get())))) {
                if (ordered) {
                    report_invalid_binary_operands("binary expression", lhs_ty, rhs_ty, loc);
                    node->ctype = comparison_result_type();
                    break;
                }
                if (lhs_kind == TypeKind::MemberPointer) {
                    if (!is_null_pointer_constant_expr(node->right.get())) {
                        report_invalid_binary_operands("binary expression", lhs_ty, rhs_ty, loc);
                    }
                    node->right = cast_if_needed(std::move(node->right), lhs_ty);
                } else {
                    if (!is_null_pointer_constant_expr(node->left.get())) {
                        report_invalid_binary_operands("binary expression", lhs_ty, rhs_ty, loc);
                    }
                    node->left = cast_if_needed(std::move(node->left), rhs_ty);
                }
                node->ctype = comparison_result_type();
                break;
            }
            if (lhs_ty && rhs_ty &&
                lhs_kind == TypeKind::BlockPointer &&
                rhs_kind == TypeKind::BlockPointer) {
                if (ordered) {
                    report_invalid_binary_operands("binary expression", lhs_ty, rhs_ty, loc);
                    node->ctype = comparison_result_type();
                    break;
                }
                if (!lhs_ty->equals(*rhs_ty.get_shared())) {
                    report_warning("comparison of distinct block pointer types", loc);
                    node->right = cast_if_needed(std::move(node->right), lhs_ty);
                }
                node->ctype = comparison_result_type();
                break;
            }
            if (lhs_ty && rhs_ty &&
                ((lhs_kind == TypeKind::BlockPointer &&
                  is_integer_adjacent(rhs_ty, ast_ctx_.get())) ||
                 (rhs_kind == TypeKind::BlockPointer &&
                  is_integer_adjacent(lhs_ty, ast_ctx_.get())))) {
                if (ordered) {
                    report_invalid_binary_operands("binary expression", lhs_ty, rhs_ty, loc);
                    node->ctype = comparison_result_type();
                    break;
                }
                if (lhs_kind == TypeKind::BlockPointer) {
                    if (!is_null_pointer_constant_expr(node->right.get())) {
                        report_invalid_binary_operands("binary expression", lhs_ty, rhs_ty, loc);
                    }
                    node->right = cast_if_needed(std::move(node->right), lhs_ty);
                } else {
                    if (!is_null_pointer_constant_expr(node->left.get())) {
                        report_invalid_binary_operands("binary expression", lhs_ty, rhs_ty, loc);
                    }
                    node->left = cast_if_needed(std::move(node->left), rhs_ty);
                }
                node->ctype = comparison_result_type();
                break;
            }
            if (lhs_ty && rhs_ty &&
                lhs_kind == TypeKind::Pointer &&
                rhs_kind == TypeKind::Pointer) {
                auto lhs_ptr = desugar_type(lhs_ty).as_shared<PointerType>();
                auto rhs_ptr = desugar_type(rhs_ty).as_shared<PointerType>();
                bool lhs_void = lhs_ptr && lhs_ptr->pointed_type && lhs_ptr->pointed_type->isVoid();
                bool rhs_void = rhs_ptr && rhs_ptr->pointed_type && rhs_ptr->pointed_type->isVoid();
                if (!lhs_void && !rhs_void && !pointers_to_compatible_types(lhs_ty, rhs_ty)) {
                    report_warning("comparison of distinct pointer types", loc);
                }
                if (!lhs_ty->equals(*rhs_ty.get_shared())) {
                    node->right = collect_make<ImplicitCast>(
                        ImplicitCastTypes::RAW_CAST, std::move(node->right), lhs_ty);
                }
                node->ctype = comparison_result_type();
                break;
            }
            if (lhs_ty && rhs_ty &&
                ((lhs_kind == TypeKind::Pointer &&
                  is_integer_adjacent(rhs_ty, ast_ctx_.get())) ||
                 (rhs_kind == TypeKind::Pointer &&
                  is_integer_adjacent(lhs_ty, ast_ctx_.get())))) {
                if (ordered) {
                    report_warning("ordered comparison between pointer and integer", loc);
                }
                if (is_integer_adjacent(lhs_ty, ast_ctx_.get())) {
                    node->left = cast_if_needed(std::move(node->left), rhs_ty);
                } else {
                    node->right = cast_if_needed(std::move(node->right), lhs_ty);
                }
                node->ctype = comparison_result_type();
                break;
            }
            if ((lhs_ty &&
                 !is_arithmetic_adjacent(lhs_ty, ast_ctx_.get())) ||
                (rhs_ty &&
                 !is_arithmetic_adjacent(rhs_ty, ast_ctx_.get()))) {
                report_invalid_binary_operands("binary expression", lhs_ty, rhs_ty, loc);
            } else {
                auto common = ensure_arithmetic_common();
                if (!common) {
                    report_error("invalid operands to binary expression", loc);
                }
            }
            node->ctype = comparison_result_type();
            break;
        }
        // --- Comma ---
        case BinOpTypes::COMMA:
            node->ctype = rhs_ty ? rhs_ty : lhs_ty;
            break;
        // --- Shift operators ---
        case BinOpTypes::SHIFT_LEFT:
        case BinOpTypes::SHIFT_RIGHT: {
            if ((lhs_ty &&
                 !is_integer_adjacent(lhs_ty, ast_ctx_.get())) ||
                (rhs_ty &&
                 !is_integer_adjacent(rhs_ty, ast_ctx_.get()))) {
                report_invalid_binary_operands("binary shift", lhs_ty, rhs_ty, loc);
            }
            bool lhs_vector = lhs_kind == TypeKind::Vector;
            bool rhs_vector = rhs_kind == TypeKind::Vector;
            if (lhs_vector || rhs_vector) {
                auto common = ensure_arithmetic_common();
                node->ctype = common ? common : (lhs_vector ? lhs_ty : rhs_ty);
                break;
            }
            auto lhs_promoted = integer_promotion_type(lhs_ty);
            auto rhs_promoted = integer_promotion_type(rhs_ty);
            node->left = cast_if_needed(std::move(node->left), lhs_promoted);
            node->right = cast_if_needed(std::move(node->right), rhs_promoted);
            node->ctype = lhs_promoted ? lhs_promoted : QualType(get_builtin_int());
            break;
        }
        // --- Additive operators (pointer arithmetic + arithmetic) ---
        case BinOpTypes::ADD:
        case BinOpTypes::SUB: {
            bool lhs_ptr = lhs_kind == TypeKind::Pointer;
            bool rhs_ptr = rhs_kind == TypeKind::Pointer;
            if (lhs_ptr &&
                is_integer_adjacent(rhs_ty, ast_ctx_.get())) {
                node->ctype = lhs_ty;
                break;
            }
            if (bop == BinOpTypes::ADD &&
                rhs_ptr &&
                is_integer_adjacent(lhs_ty, ast_ctx_.get())) {
                node->ctype = rhs_ty;
                break;
            }
            if (bop == BinOpTypes::SUB && lhs_ptr && rhs_ptr) {
                if (!pointers_to_compatible_types(lhs_ty, rhs_ty)) {
                    report_error("pointer subtraction with different types", loc);
                }
                node->ctype = QualType(get_builtin_long());
                break;
            }
            if ((lhs_ptr || rhs_ptr) && !(lhs_ptr && rhs_ptr && bop == BinOpTypes::SUB)) {
                report_invalid_binary_operands("binary expression", lhs_ty, rhs_ty, loc);
                node->ctype = lhs_ptr ? lhs_ty : rhs_ty;
                break;
            }
            if ((lhs_ty &&
                 !is_arithmetic_adjacent(lhs_ty, ast_ctx_.get())) ||
                (rhs_ty &&
                 !is_arithmetic_adjacent(rhs_ty, ast_ctx_.get()))) {
                report_invalid_binary_operands("binary expression", lhs_ty, rhs_ty, loc);
                node->ctype = QualType(get_builtin_int());
                break;
            }
            auto common = ensure_arithmetic_common();
            node->ctype = common ? common : QualType(get_builtin_int());
            break;
        }
        // --- Integer-only operators ---
        case BinOpTypes::MOD:
        case BinOpTypes::BITWISE_AND:
        case BinOpTypes::BITWISE_XOR:
        case BinOpTypes::BITWISE_OR: {
            if ((lhs_ty &&
                 !is_integer_adjacent(lhs_ty, ast_ctx_.get())) ||
                (rhs_ty &&
                 !is_integer_adjacent(rhs_ty, ast_ctx_.get()))) {
                report_invalid_binary_operands("binary expression", lhs_ty, rhs_ty, loc);
            }
            auto common = ensure_arithmetic_common();
            node->ctype = common ? common : QualType(get_builtin_int());
            break;
        }
        // --- Multiplicative operators ---
        case BinOpTypes::MULT:
        case BinOpTypes::DIV: {
            if ((lhs_ty &&
                 !is_arithmetic_adjacent(lhs_ty, ast_ctx_.get())) ||
                (rhs_ty &&
                 !is_arithmetic_adjacent(rhs_ty, ast_ctx_.get()))) {
                report_invalid_binary_operands("binary expression", lhs_ty, rhs_ty, loc);
            }
            auto common = ensure_arithmetic_common();
            node->ctype = common ? common : QualType(get_builtin_int());
            break;
        }
        default:
            node->ctype = usual_arithmetic_conversion_type(lhs_ty, rhs_ty);
            if (!node->ctype) {
                node->ctype = QualType(get_builtin_int());
            }
            break;
    }
    return node;
}

std::unique_ptr<Expr> Collect::try_cpp_binary_operator_overload(
    std::unique_ptr<Expr>& lhs,
    std::unique_ptr<Expr>& rhs,
    BinOpTypes bop,
    SrcLoc loc,
    bool allow_rewritten_candidates) {
    if (!lang_opts_.is_cxx_mode() ||
        !lhs ||
        !rhs ||
        (!type_can_participate_in_cpp_operator_overload(
             lhs->get_type(),
             ast_ctx_.get()) &&
         !type_can_participate_in_cpp_operator_overload(
             rhs->get_type(),
             ast_ctx_.get()))) {
        return nullptr;
    }

    std::string_view op_suffix = binary_operator_function_suffix(bop);
    if (op_suffix.empty()) {
        return nullptr;
    }

    auto make_operator_name = [](std::string_view suffix) {
        std::string name = "operator";
        name += suffix;
        return name;
    };

    auto function_signature_matches_ignoring_return =
        [&](QualType lhs_type, QualType rhs_type) {
        auto lhs_fn = desugar_type(lhs_type, ast_ctx_.get())
            .as_shared<FunctionType>();
        auto rhs_fn = desugar_type(rhs_type, ast_ctx_.get())
            .as_shared<FunctionType>();
        if (!lhs_fn || !rhs_fn) {
            return false;
        }
        FunctionType rhs_with_lhs_return = *rhs_fn;
        rhs_with_lhs_return.ret_type = lhs_fn->ret_type;
        return lhs_fn->equals(rhs_with_lhs_return);
    };

    auto function_template_primary = [](const std::shared_ptr<Symbol>& symbol)
        -> const FunctionTemplateDecl* {
        const auto* specialization =
            symbol ? get_symbol_function_template_specialization(symbol.get())
                   : nullptr;
        return specialization ? specialization->primary_template : nullptr;
    };

    auto candidate_pattern_type = [&](const OverloadCallCandidate& candidate) {
        if (const auto* primary = function_template_primary(candidate.symbol)) {
            if (auto* fn = primary->function_decl()) {
                return QualType(fn->type);
            }
        }
        return candidate.symbol ? candidate.symbol->type : QualType();
    };

    auto candidate_corresponds_to_symbol =
        [&](const OverloadCallCandidate& candidate,
            const std::shared_ptr<Symbol>& blocker_symbol) {
        if (!blocker_symbol || blocker_symbol->kind != SymbolKind::FUNCTION) {
            return false;
        }
        if (function_template_primary(candidate.symbol)) {
            return false;
        }
        return function_signature_matches_ignoring_return(
            candidate_pattern_type(candidate),
            blocker_symbol->type);
    };

    auto candidate_corresponds_to_template =
        [&](const OverloadCallCandidate& candidate,
            const FunctionTemplateDecl* blocker_template) {
        const auto* candidate_template =
            function_template_primary(candidate.symbol);
        if (!candidate_template || !blocker_template) {
            return false;
        }
        const FuncDecl* candidate_decl = candidate_template->function_decl();
        const FuncDecl* blocker_decl = blocker_template->function_decl();
        if (!candidate_decl || !blocker_decl) {
            return false;
        }
        return function_signature_matches_ignoring_return(
            QualType(candidate_decl->type),
            QualType(blocker_decl->type));
    };

    auto lookup_unqualified_function_templates_for_name =
        [&](std::string_view name) {
        std::vector<const FunctionTemplateDecl*> templates;
        if (!session_.current_scope_) {
            return templates;
        }
        const DeclBinding* binding =
            LookupEngine::lookup_unqualified_template_binding(
                std::string(name),
                session_.current_scope_,
                true,
                LookupNamespace::Ordinary);
        if (!binding) {
            return templates;
        }
        auto append_template = [&](const Decl* decl) {
            const auto* function_template =
                dyn_cast<FunctionTemplateDecl>(decl);
            if (!function_template) {
                return;
            }
            for (const auto* existing : templates) {
                if (existing == function_template) {
                    return;
                }
            }
            templates.push_back(function_template);
        };
        append_template(binding->template_decl);
        for (const auto* decl : binding->template_overload_candidates) {
            append_template(decl);
        }
        return templates;
    };

    auto has_corresponding_not_equal =
        [&](const OverloadCallCandidate& candidate,
            Expr* first_operand,
            Expr* second_operand) {
        QualType owner_type =
            candidate.symbol
                ? get_symbol_owner_record_type(candidate.symbol.get())
                : QualType();
        auto first_operand_record = remove_reference_and_desugar(
            first_operand ? first_operand->get_type() : QualType(),
            ast_ctx_.get()).as_shared<ObjectType>();
        auto owner_record = remove_reference_and_desugar(
            first_operand_record ? QualType(first_operand_record) : owner_type,
            ast_ctx_.get()).as_shared<ObjectType>();
        if (owner_record) {
            for (const auto& method :
                 find_record_methods(owner_record.get(), "operator!=")) {
                if (method.method &&
                    candidate_corresponds_to_symbol(
                        candidate, method.method->symbol)) {
                    return true;
                }
            }
            for (const auto& method_template :
                 find_record_method_templates(owner_record.get(), "operator!=")) {
                if (method_template.method_template &&
                    candidate_corresponds_to_template(
                        candidate,
                        method_template.method_template->decl)) {
                    return true;
                }
            }
        }

        auto function_candidates =
            LookupEngine::lookup_unqualified_function_candidates(
                "operator!=",
                session_.current_scope_,
                true);
        for (const auto& fn_symbol : function_candidates) {
            if (fn_symbol && get_symbol_owner_record_type(fn_symbol.get())) {
                continue;
            }
            if (candidate_corresponds_to_symbol(candidate, fn_symbol)) {
                return true;
            }
        }
        for (const auto* function_template :
             lookup_unqualified_function_templates_for_name("operator!=")) {
            if (candidate_corresponds_to_template(candidate, function_template)) {
                return true;
            }
        }

        std::vector<OverloadCallCandidate> adl_not_equal_candidates;
        std::vector<Expr*> explicit_not_equal_args{second_operand};
        append_adl_overload_candidates(
            "operator!=",
            first_operand,
            OverloadImplicitObjectArgKind::Regular,
            explicit_not_equal_args,
            adl_not_equal_candidates,
            loc);
        for (const auto& adl_candidate : adl_not_equal_candidates) {
            if (candidate_corresponds_to_symbol(
                    candidate, adl_candidate.symbol)) {
                return true;
            }
        }
        return false;
    };

    auto is_bool_type = [&](QualType type) {
        QualType canonical =
            desugar_type(remove_reference(type, ast_ctx_.get()), ast_ctx_.get());
        auto builtin = canonical.as_shared<BuiltinType>();
        return builtin && builtin->builtin_kind == BuiltinTypes::Bool;
    };

    std::string op_name = make_operator_name(op_suffix);

    bool had_member_match = false;
    bool saw_private_method = false;
    bool saw_protected_method = false;
    std::vector<OverloadCallCandidate> overload_candidates;

    auto tag_candidates =
        [&](size_t start,
            OverloadOperatorRewriteKind rewrite_kind,
            bool is_reversed,
            Expr* first_operand,
            Expr* second_operand) {
        for (size_t index = start; index < overload_candidates.size(); ++index) {
            overload_candidates[index].operator_rewrite_kind = rewrite_kind;
            overload_candidates[index].is_synthesized_reversed_operator_candidate =
                is_reversed;
            overload_candidates[index].has_operator_operand_overrides = true;
            overload_candidates[index].operator_implicit_object_arg = first_operand;
            overload_candidates[index].operator_explicit_arg = second_operand;
        }
    };

    auto append_operator_candidates =
        [&](const std::string& candidate_name,
            Expr* first_operand,
            Expr* second_operand,
            OverloadOperatorRewriteKind rewrite_kind,
            bool is_reversed,
            bool require_equality_rewrite_target) -> std::unique_ptr<Expr> {
        size_t operator_candidate_start = overload_candidates.size();
        auto first_record =
            remove_reference_and_desugar(
                first_operand ? first_operand->get_type() : QualType(),
                ast_ctx_.get())
                .as_shared<ObjectType>();

        bool local_had_member_match = false;
        bool local_saw_private_method = false;
        bool local_saw_protected_method = false;
        size_t start = overload_candidates.size();
        if (auto candidate_error = append_member_overload_candidates(
                first_record.get(),
                candidate_name,
                first_operand,
                OverloadImplicitObjectArgKind::Regular,
                overload_candidates,
                local_had_member_match,
                local_saw_private_method,
                local_saw_protected_method,
                loc)) {
            return candidate_error;
        }
        tag_candidates(
            start,
            rewrite_kind,
            is_reversed,
            first_operand,
            second_operand);
        had_member_match |= local_had_member_match;
        saw_private_method |= local_saw_private_method;
        saw_protected_method |= local_saw_protected_method;

        start = overload_candidates.size();
        append_unqualified_overload_candidates(
            candidate_name,
            OverloadImplicitObjectArgKind::Regular,
            overload_candidates);
        tag_candidates(
            start,
            rewrite_kind,
            is_reversed,
            first_operand,
            second_operand);

        start = overload_candidates.size();
        std::vector<Expr*> adl_explicit_args{second_operand};
        append_adl_overload_candidates(
            candidate_name,
            first_operand,
            OverloadImplicitObjectArgKind::Regular,
            adl_explicit_args,
            overload_candidates,
            loc);
        tag_candidates(
            start,
            rewrite_kind,
            is_reversed,
            first_operand,
            second_operand);

        start = overload_candidates.size();
        std::vector<Expr*> probe_args{second_operand};
        append_unqualified_function_template_overload_candidates(
            candidate_name,
            first_operand,
            OverloadImplicitObjectArgKind::Regular,
            probe_args,
            overload_candidates,
            loc);
        tag_candidates(
            start,
            rewrite_kind,
            is_reversed,
            first_operand,
            second_operand);

        if (require_equality_rewrite_target) {
            overload_candidates.erase(
                std::remove_if(
                    overload_candidates.begin() +
                        static_cast<std::ptrdiff_t>(operator_candidate_start),
                    overload_candidates.end(),
                    [&](const OverloadCallCandidate& candidate) {
                        return has_corresponding_not_equal(
                            candidate,
                            first_operand,
                            second_operand);
                    }),
                overload_candidates.end());
        }
        return nullptr;
    };

    if (auto candidate_error = append_operator_candidates(
            op_name,
            lhs.get(),
            rhs.get(),
            OverloadOperatorRewriteKind::None,
            false,
            false)) {
        return candidate_error;
    }

    auto append_equality_rewrites = [&]() -> std::unique_ptr<Expr> {
        std::string equality_name = make_operator_name("==");
        if (bop == BinOpTypes::NOT_EQUAL) {
            if (auto candidate_error = append_operator_candidates(
                    equality_name,
                    lhs.get(),
                    rhs.get(),
                    OverloadOperatorRewriteKind::Equality,
                    false,
                    true)) {
                return candidate_error;
            }
        }
        if (bop == BinOpTypes::EQUAL || bop == BinOpTypes::NOT_EQUAL) {
            if (auto candidate_error = append_operator_candidates(
                    equality_name,
                    rhs.get(),
                    lhs.get(),
                    OverloadOperatorRewriteKind::Equality,
                    true,
                    true)) {
                return candidate_error;
            }
        }
        return nullptr;
    };

    auto append_three_way_rewrites = [&]() -> std::unique_ptr<Expr> {
        std::string three_way_name = make_operator_name("<=>");
        bool is_relational =
            bop == BinOpTypes::LESS_THAN ||
            bop == BinOpTypes::LESS_EQUAL_THAN ||
            bop == BinOpTypes::GREATER_THAN ||
            bop == BinOpTypes::GREATER_EQUAL_THAN;
        if (is_relational) {
            if (auto candidate_error = append_operator_candidates(
                    three_way_name,
                    lhs.get(),
                    rhs.get(),
                    OverloadOperatorRewriteKind::ThreeWay,
                    false,
                    false)) {
                return candidate_error;
            }
        }
        if (is_relational || bop == BinOpTypes::THREE_WAY_COMPARE) {
            if (auto candidate_error = append_operator_candidates(
                    three_way_name,
                    rhs.get(),
                    lhs.get(),
                    OverloadOperatorRewriteKind::ThreeWay,
                    true,
                    false)) {
                return candidate_error;
            }
        }
        return nullptr;
    };
    // see [over.match.oper] in the C++ standard
    if (allow_rewritten_candidates) {
        if (auto candidate_error = append_equality_rewrites()) {
            return candidate_error;
        }
        if (auto candidate_error = append_three_way_rewrites()) {
            return candidate_error;
        }
    }

    auto operator_candidates_are_duplicate =
        [&](const OverloadCallCandidate& lhs_candidate,
            const OverloadCallCandidate& rhs_candidate) {
        if (lhs_candidate.operator_rewrite_kind !=
                rhs_candidate.operator_rewrite_kind ||
            lhs_candidate.is_synthesized_reversed_operator_candidate !=
                rhs_candidate.is_synthesized_reversed_operator_candidate ||
            lhs_candidate.operator_implicit_object_arg !=
                rhs_candidate.operator_implicit_object_arg ||
            lhs_candidate.operator_explicit_arg !=
                rhs_candidate.operator_explicit_arg) {
            return false;
        }
        if (lhs_candidate.symbol == rhs_candidate.symbol) {
            return true;
        }
        const auto* lhs_template =
            function_template_primary(lhs_candidate.symbol);
        const auto* rhs_template =
            function_template_primary(rhs_candidate.symbol);
        return lhs_template &&
               rhs_template &&
               template_decls_share_lookup_identity(lhs_template, rhs_template);
    };

    std::vector<OverloadCallCandidate> unique_operator_candidates;
    unique_operator_candidates.reserve(overload_candidates.size());
    for (auto& candidate : overload_candidates) {
        bool duplicate = false;
        for (const auto& existing : unique_operator_candidates) {
            if (operator_candidates_are_duplicate(existing, candidate)) {
                duplicate = true;
                break;
            }
        }
        if (!duplicate) {
            unique_operator_candidates.push_back(std::move(candidate));
        }
    }
    overload_candidates = std::move(unique_operator_candidates);

    if (overload_candidates.empty()) {
        if (had_member_match) {
            return report_inaccessible_member(
                op_name, saw_private_method, saw_protected_method, loc);
        }
        return nullptr;
    }

    std::vector<Expr*> probe_args{rhs.get()};
    OverloadCandidateSelection selection;
    if (auto overload_error = select_overload_candidate(
            op_name,
            overload_candidates,
            probe_args,
            lhs.get(),
            loc,
            selection)) {
        return overload_error;
    }
    if (!selection.symbol) {
        return nullptr;
    }
    if (auto completion_error =
            complete_selected_function_template_specialization_symbol(
                selection.symbol,
                loc,
                "failed to instantiate selected operator function template specialization")) {
        return completion_error;
    }

    auto build_selected_call =
        [&](OverloadCandidateSelection selected,
            std::unique_ptr<Expr> left,
            std::unique_ptr<Expr> right) -> std::unique_ptr<Expr> {
        if (selected.is_synthesized_reversed_operator_candidate) {
            std::swap(left, right);
        }

        auto implicit_object_arg = build_overload_implicit_object_arg(
            selected.implicit_object_arg_kind,
            std::move(left),
            /*object_expr_is_pointer=*/false,
            loc);

        std::vector<std::unique_ptr<Expr>> explicit_args;
        explicit_args.push_back(std::move(right));
        if (selected.implicit_object_arg_kind != OverloadImplicitObjectArgKind::None &&
            implicit_object_arg) {
            explicit_args.insert(
                explicit_args.begin(),
                std::move(implicit_object_arg));
        }

        auto callee_expr =
            make_hidden_overload_callee(std::move(selected.symbol), loc);
        return collect_function_call(
            std::move(callee_expr),
            std::move(explicit_args),
            loc);
    };

    if (selection.operator_rewrite_kind ==
        OverloadOperatorRewriteKind::Equality) {
        auto equality = build_selected_call(
            selection,
            std::move(lhs),
            std::move(rhs));
        if (!equality || isa<ErrorExpr>(equality.get())) {
            return equality;
        }
        if (!is_bool_type(equality->get_type())) {
            report_error(
                "rewritten 'operator==' candidate must return bool",
                loc);
            return collect_make<ErrorExpr>(
                "invalid rewritten equality candidate", loc);
        }
        if (bop == BinOpTypes::NOT_EQUAL) {
            return collect_unary_operation(
                UnaryOpTypes::LOGICAL_NOT,
                std::move(equality),
                loc);
        }
        return equality;
    }

    if (selection.operator_rewrite_kind ==
        OverloadOperatorRewriteKind::ThreeWay) {
        bool reversed = selection.is_synthesized_reversed_operator_candidate;
        auto three_way = build_selected_call(
            selection,
            std::move(lhs),
            std::move(rhs));
        if (!three_way || isa<ErrorExpr>(three_way.get())) {
            return three_way;
        }
        auto zero = collect_integer_literal("0", get_builtin_int(), loc);
        if (reversed) {
            return collect_binary_operation_impl(
                std::move(zero),
                std::move(three_way),
                bop,
                loc,
                /*allow_cpp_rewritten_candidates=*/false);
        }
        return collect_binary_operation_impl(
            std::move(three_way),
            std::move(zero),
            bop,
            loc,
            /*allow_cpp_rewritten_candidates=*/false);
    }

    return build_selected_call(
        selection,
        std::move(lhs),
        std::move(rhs));
}


std::unique_ptr<Expr> Collect::collect_compound_assign_operation(std::unique_ptr<Expr> lhs, std::unique_ptr<Expr> rhs, BinOpTypes bop, SrcLoc loc) const {
    if (lang_opts_.is_cxx_mode()) {
        QualType lhs_type = lhs ? lhs->get_type() : QualType();
        QualType rhs_type = rhs ? rhs->get_type() : QualType();
        bool has_dependent_operand =
            (lhs && expression_depends_on_template_parameters(lhs.get())) ||
            (rhs && expression_depends_on_template_parameters(rhs.get())) ||
            type_depends_on_template_parameters(lhs_type, ast_ctx_.get()) ||
            type_depends_on_template_parameters(rhs_type, ast_ctx_.get());
        if (has_dependent_operand) {
            QualType dependent_result_type = lhs_type;
            if (canonical_type_kind(dependent_result_type, ast_ctx_.get()) ==
                TypeKind::Reference) {
                dependent_result_type =
                    remove_reference(dependent_result_type, ast_ctx_.get());
            }
            if (!dependent_result_type) {
                dependent_result_type = QualType(
                    std::make_shared<AutoType>(
                        AutoTypeFlavor::TemplateNonType));
            }
            return collect_make<DependentBinaryExpr>(
                std::move(lhs),
                std::move(rhs),
                bop,
                dependent_result_type,
                loc);
        }
    }

    rhs = collect_apply_standard_conversions(std::move(rhs), ExprUseContext::RValue);
    if (!is_modifiable_lvalue(lhs.get())) {
        auto lhs_type = lhs ? lhs->get_type() : QualType();
        if (is_const_qualified_lvalue(lhs.get())) {
            report_error("cannot assign to variable of type '" + lhs_type.to_string() + "'", loc);
        } else {
            report_error("expression is not assignable", loc);
        }
    }
    auto lhs_ty = lhs ? lhs->get_type() : QualType();
    auto rhs_ty = rhs ? rhs->get_type() : QualType();
    QualType op_type = lhs_ty;
    bool lhs_ptr = canonical_type_kind(lhs_ty) == TypeKind::Pointer;
    switch (bop) {
        case BinOpTypes::ASSIGN_ADD:
        case BinOpTypes::ASSIGN_SUB:
            if (lhs_ptr) {
                if (!(rhs_ty &&
                      is_integer_adjacent(rhs_ty, ast_ctx_.get()))) {
                    report_invalid_compound_assign_operands("", lhs_ty, rhs_ty, loc);
                }
                break;
            }
            [[fallthrough]];
        case BinOpTypes::ASSIGN_MUL:
        case BinOpTypes::ASSIGN_DIV: {
            if ((lhs_ty &&
                 !is_arithmetic_adjacent(lhs_ty, ast_ctx_.get())) ||
                (rhs_ty &&
                 !is_arithmetic_adjacent(rhs_ty, ast_ctx_.get()))) {
                report_invalid_compound_assign_operands("", lhs_ty, rhs_ty, loc);
            }
            auto common = usual_arithmetic_conversion_type(lhs_ty, rhs_ty);
            if (common) {
                op_type = common;
            }
            break;
        }
        case BinOpTypes::ASSIGN_MOD:
        case BinOpTypes::ASSIGN_AND:
        case BinOpTypes::ASSIGN_OR:
        case BinOpTypes::ASSIGN_XOR: {
            if ((lhs_ty &&
                 !is_integer_adjacent(lhs_ty, ast_ctx_.get())) ||
                (rhs_ty &&
                 !is_integer_adjacent(rhs_ty, ast_ctx_.get()))) {
                report_invalid_compound_assign_operands("", lhs_ty, rhs_ty, loc);
            }
            auto common = usual_arithmetic_conversion_type(lhs_ty, rhs_ty);
            if (common) {
                op_type = common;
            }
            break;
        }
        case BinOpTypes::ASSIGN_LSHIFT:
        case BinOpTypes::ASSIGN_RSHIFT: {
            if ((lhs_ty &&
                 !is_integer_adjacent(lhs_ty, ast_ctx_.get())) ||
                (rhs_ty &&
                 !is_integer_adjacent(rhs_ty, ast_ctx_.get()))) {
                report_invalid_compound_assign_operands("", lhs_ty, rhs_ty, loc);
            }
            auto rhs_promoted = integer_promotion_type(rhs_ty);
            rhs = cast_if_needed(std::move(rhs), rhs_promoted);
            op_type = integer_promotion_type(lhs_ty);
            if (!op_type) {
                op_type = lhs_ty;
            }
            break;
        }
        default: {
            auto common = usual_arithmetic_conversion_type(lhs_ty, rhs_ty);
            if (common) {
                op_type = common;
            }
            break;
        }
    }
    if (!op_type) {
        op_type = lhs_ty ? lhs_ty : QualType(get_builtin_int());
    }
    return make_ast<CompoundAssignOperation>(*ast_ctx_, std::move(lhs), std::move(rhs), bop, op_type, loc);
}


std::unique_ptr<Expr> Collect::collect_conditional_expression(std::unique_ptr<Expr> cond,
    std::unique_ptr<Expr> true_expr, std::unique_ptr<Expr> false_expr, QualType forced_type, SrcLoc loc) const {

    cond = collect_contextual_bool_conversion(
        std::move(cond),
        loc,
        "conditional expression condition");
    bool preserve_cpp_conditional_operands = lang_opts_.is_cxx_mode();
    if (true_expr && !preserve_cpp_conditional_operands) {
        true_expr = collect_apply_standard_conversions(std::move(true_expr), ExprUseContext::ConditionalOperand);
    }
    if (!preserve_cpp_conditional_operands) {
        false_expr = collect_apply_standard_conversions(std::move(false_expr), ExprUseContext::ConditionalOperand);
    }
    bool cond_is_dependent = false;
    if (cond) {
        auto cond_ty = cond->get_type();
        cond_is_dependent = expression_depends_on_template_parameters(cond.get());
    }

    QualType result_type = forced_type;
    bool preserve_cpp_glvalue_result = false;
    if (!result_type) {
        auto true_ty = true_expr ? true_expr->get_type() : (cond ? cond->get_type() : QualType());
        auto false_ty = false_expr ? false_expr->get_type() : QualType();
        auto true_kind = canonical_type_kind(true_ty);
        auto false_kind = canonical_type_kind(false_ty);
        auto operand_type_is_deferred_or_dependent = [&](QualType type) {
            return type &&
                   (type_depends_on_template_parameters(type, ast_ctx_.get()) ||
                    contains_deferred_semantic_type(type.get_shared()));
        };
        auto operand_is_bool = [&](QualType type) {
            auto builtin =
                desugar_type(type, ast_ctx_.get()).as_shared<BuiltinType>();
            return builtin && builtin->builtin_kind == BuiltinTypes::Bool;
        };
        bool is_operands_dep =
            expression_depends_on_template_parameters(true_expr.get())
            || expression_depends_on_template_parameters(false_expr.get());
        bool operand_type_defdep = operand_type_is_deferred_or_dependent(true_ty)
        || operand_type_is_deferred_or_dependent(false_ty);
        bool template_dependent_conditional = cond_is_dependent ||
            is_operands_dep || operand_type_defdep;
        if (lang_opts_.is_cxx_mode() && template_dependent_conditional) {
            if (true_ty && false_ty && true_ty.equals_qualified(false_ty)) {
                result_type = true_ty;
            } else if (operand_is_bool(true_ty) || operand_is_bool(false_ty)) {
                result_type = QualType(get_builtin_bool());
            } else if (true_ty && false_ty &&
                       ((is_arithmetic_adjacent(true_ty, ast_ctx_.get()) &&
                         is_arithmetic_adjacent(false_ty, ast_ctx_.get())) ||
                        true_ty->isComplex() || false_ty->isComplex())) {
                result_type = usual_arithmetic_conversion_type(true_ty, false_ty);
            } else if (true_ty) {
                result_type = true_ty;
            } else if (false_ty) {
                result_type = false_ty;
            } else {
                result_type =
                    QualType(std::make_shared<AutoType>(
                        AutoTypeFlavor::TemplateNonType));
            }
        } else {
            if (lang_opts_.is_cxx_mode() && true_expr && false_expr) {
                auto true_category = classify_value_category(true_expr.get());
                auto false_category = classify_value_category(false_expr.get());
                if (auto merged_glvalue_type =
                        merge_cpp_conditional_glvalue_type(
                            true_ty,
                            false_ty,
                            true_category,
                            false_category)) {
                    result_type = *merged_glvalue_type;
                    preserve_cpp_glvalue_result = true;
                }
            }
            if (!preserve_cpp_glvalue_result) {
                if (true_ty && false_ty && true_ty.equals_qualified(false_ty)) {
                    result_type = true_ty;
                } else if (true_ty && false_ty &&
                           is_nullptr_type(true_ty, ast_ctx_.get()) &&
                           is_nullptr_type(false_ty, ast_ctx_.get())) {
                    result_type = true_ty;
                } else if ((true_ty &&
                           is_scoped_enum_type(true_ty, ast_ctx_.get())) ||
                           (false_ty &&
                            is_scoped_enum_type(false_ty, ast_ctx_.get()))) {
                    result_type = QualType();
                } else if ((true_ty && true_ty->isVoid()) ||
                           (false_ty && false_ty->isVoid())) {
                    result_type = QualType(get_builtin_void());
                } else if (true_ty && false_ty &&
                           ((is_arithmetic_adjacent(true_ty, ast_ctx_.get()) &&
                             is_arithmetic_adjacent(false_ty, ast_ctx_.get())) ||
                            true_ty->isComplex() || false_ty->isComplex())) {
                    result_type = usual_arithmetic_conversion_type(true_ty, false_ty);
                } else if (true_ty && false_ty &&
                           true_kind == TypeKind::Pointer &&
                           false_kind == TypeKind::Pointer) {
                    auto true_ptr = desugar_type(true_ty).as_shared<PointerType>();
                    auto false_ptr = desugar_type(false_ty).as_shared<PointerType>();
                    bool true_void = true_ptr && true_ptr->pointed_type && true_ptr->pointed_type->isVoid();
                    bool false_void = false_ptr && false_ptr->pointed_type && false_ptr->pointed_type->isVoid();
                    if (!(pointers_to_compatible_types(true_ty, false_ty) || true_void || false_void)) {
                        report_error("incompatible pointer types in conditional expression ('" +
                            true_ty.to_string() + "' and '" + false_ty.to_string() + "')", loc);
                        result_type = true_ty;
                    } else {
                        QualType base = true_void ? false_ptr->pointed_type : true_ptr->pointed_type;
                        if (!base) {
                            base = false_ptr ? false_ptr->pointed_type : QualType();
                        }
                        if (!base) {
                            base = QualType(get_builtin_void());
                        }
                        uint8_t merged_quals = QUAL_NONE;
                        if (true_ptr) merged_quals |= true_ptr->pointed_type.get_qualifiers();
                        if (false_ptr) merged_quals |= false_ptr->pointed_type.get_qualifiers();
                        base = base.with_qualifiers(merged_quals);
                        result_type = QualType(std::make_shared<PointerType>(base));
                    }
                } else if (true_ty && false_ty &&
                           is_nullptr_type(true_ty, ast_ctx_.get()) &&
                           (false_kind == TypeKind::Pointer ||
                            false_kind == TypeKind::MemberPointer ||
                            false_kind == TypeKind::BlockPointer)) {
                    result_type = false_ty;
                } else if (true_ty && false_ty &&
                           is_nullptr_type(false_ty, ast_ctx_.get()) &&
                           (true_kind == TypeKind::Pointer ||
                            true_kind == TypeKind::MemberPointer ||
                            true_kind == TypeKind::BlockPointer)) {
                    result_type = true_ty;
                } else if (true_ty && true_kind == TypeKind::Pointer &&
                           false_ty &&
                           is_integer_adjacent(false_ty, ast_ctx_.get()) &&
                           is_null_pointer_constant_expr(false_expr.get())) {
                    result_type = true_ty;
                } else if (true_ty && true_kind == TypeKind::BlockPointer &&
                           false_ty &&
                           is_integer_adjacent(false_ty, ast_ctx_.get()) &&
                           is_null_pointer_constant_expr(false_expr.get())) {
                    result_type = true_ty;
                } else if (false_ty && false_kind == TypeKind::Pointer &&
                           true_ty &&
                           is_integer_adjacent(true_ty, ast_ctx_.get()) &&
                           is_null_pointer_constant_expr(true_expr.get())) {
                    result_type = false_ty;
                } else if (false_ty && false_kind == TypeKind::BlockPointer &&
                           true_ty &&
                           is_integer_adjacent(true_ty, ast_ctx_.get()) &&
                           is_null_pointer_constant_expr(true_expr.get())) {
                    result_type = false_ty;
                } else {
                    result_type = pick_common_type(true_ty, false_ty);
                }
            }
        }
        if (!result_type) {
            report_error("incompatible operand types in conditional expression", loc);
            result_type = QualType(get_builtin_int());
        }
    }
    if (!preserve_cpp_glvalue_result && lang_opts_.is_cxx_mode()) {
        if (true_expr) {
            true_expr = collect_apply_standard_conversions(
                std::move(true_expr),
                ExprUseContext::ConditionalOperand);
        }
        false_expr = collect_apply_standard_conversions(
            std::move(false_expr),
            ExprUseContext::ConditionalOperand);
    }
    if (!preserve_cpp_glvalue_result &&
        result_type &&
        !result_type->isVoid() &&
        true_expr) {
        true_expr = cast_if_needed(std::move(true_expr), result_type);
    }
    if (!preserve_cpp_glvalue_result &&
        result_type &&
        !result_type->isVoid()) {
        false_expr = cast_if_needed(std::move(false_expr), result_type);
    }
    auto node = make_ast<CondExpr>(*ast_ctx_, std::move(cond), std::move(true_expr), std::move(false_expr), result_type);
    node->location = loc;
    return node;
}


std::unique_ptr<Expr> Collect::collect_generic_expression(std::unique_ptr<Expr> controlling, std::vector<GenericAssociation> associations, SrcLoc loc) {

    // C11 6.5.1.1: the controlling expression is unevaluated.
    {
        UnevaluatedContextScope unevaluated_scope(this, "_Generic selector");
        controlling = collect_apply_standard_conversions(std::move(controlling), ExprUseContext::ConditionalOperand);
    }
    auto controlling_type = controlling ? controlling->get_type() : QualType();
    if (!controlling_type) {
        report_error("_Generic controlling expression has no type", loc);
        return collect_make<ErrorExpr>("_Generic controlling expression has no type", loc);
    }

    int default_index = -1;
    int match_index = -1;

    for (size_t i = 0; i < associations.size(); ++i) {
        const auto& assoc = associations[i];
        if (assoc.is_default) {
            if (default_index >= 0) {
                report_error("duplicate 'default' in _Generic", assoc.loc);
                return collect_make<ErrorExpr>("duplicate 'default' in _Generic", assoc.loc);
            }
            default_index = static_cast<int>(i);
            continue;
        }
        if (!assoc.type) {
            continue;
        }
        if (controlling_type.equals_unqualified(assoc.type)) {
            if (match_index >= 0) {
                // GNU-family behavior: after lvalue conversion strips qualifiers
                // from the controlling expression, multiple qualified variants
                // (e.g. int/const int/volatile int) may all be compatible.
                // Keep the first matching association.
                continue;
            }
            match_index = static_cast<int>(i);
        }
    }

    int selected = (match_index >= 0) ? match_index : default_index;
    if (selected < 0) {
        report_error("_Generic selector of type '" + controlling_type.to_string() +
            "' is not compatible with any association", loc);
        return collect_make<ErrorExpr>("_Generic selector is not compatible with any association", loc);
    }
    // Preserve _Generic semantics by materializing only the selected association
    // expression into the final AST.
    auto selected_expr = std::move(associations[selected].expr);
    if (!selected_expr) {
        report_error("_Generic selected association has no expression", loc);
        return collect_make<ErrorExpr>("_Generic selected association has no expression", loc);
    }
    // Preserve selected-expression value category (lvalue/function designator/rvalue).
    return selected_expr;
}


std::unique_ptr<Expr> Collect::builtin_call_expression_special_cases(
    BuiltinKind kind,
    std::vector<std::unique_ptr<Expr>>& args,
    SrcLoc loc) const {
    auto int_type = QualType(get_builtin_int());
    auto void_type = QualType(get_builtin_void());
    auto void_ptr = QualType(std::make_shared<PointerType>(void_type));
    auto double_type = QualType(get_builtin_double());
    auto complex_double_type =
        QualType(ast_ctx_->type_ctx->get_complex(BuiltinTypes::Double));

    switch (kind) {
        case BuiltinKind::EXPECT:
        case BuiltinKind::EXPECT_WITH_PROBABILITY: {
            QualType result_type = args.empty() ? int_type : args[0]->get_type();
            if (!result_type) {
                result_type = int_type;
            }
            return collect_make<BuiltinCallExpr>(kind, std::move(args), result_type, loc);
        }
        case BuiltinKind::CONSTANT_P: {
            bool is_const = false;
            if (!args.empty() && args[0]) {
                ConstEvalResult eval = evaluate_with_consteval_compat(
                    args[0].get(), ConstEvalMode::builtin_query());
                is_const = eval.status == ConstEvalStatus::Constant;
            }
            auto node = collect_make<BuiltinCallExpr>(kind, std::move(args), int_type, loc);
            node->const_value = is_const ? 1 : 0;
            return node;
        }
        case BuiltinKind::IS_CONSTANT_EVALUATED: {
            auto bool_type = QualType(get_builtin_bool());
            auto node =
                collect_make<BuiltinCallExpr>(kind, std::move(args), bool_type, loc);
            node->const_value = 0;
            return node;
        }
        case BuiltinKind::FPCLASSIFY:
            if (args.size() == 6 && args[5] && args[5]->get_type() &&
                !args[5]->get_type()->isFloatingPoint()) {
                report_error(
                    "__builtin_fpclassify requires a floating-point classification argument",
                    loc);
            }
            return collect_make<BuiltinCallExpr>(kind, std::move(args), int_type, loc);
        case BuiltinKind::SHUFFLEVECTOR: {
            QualType ret = int_type;
            if (!args.empty() && args[0] && args[0]->get_type() &&
                canonical_type_kind(args[0]->get_type()) == TypeKind::Vector) {
                ret = args[0]->get_type();
            } else if (args.size() > 1 && args[1] && args[1]->get_type() &&
                canonical_type_kind(args[1]->get_type()) == TypeKind::Vector) {
                ret = args[1]->get_type();
            }
            return collect_make<BuiltinCallExpr>(kind, std::move(args), ret, loc);
        }
        case BuiltinKind::EXIT:
            if (args.size() != 1) {
                report_error("__builtin_exit requires exactly 1 argument", loc);
            }
            return collect_make<BuiltinCallExpr>(kind, std::move(args), void_type, loc);
        case BuiltinKind::COMPLEX: {
            QualType element_type = double_type;
            if (args.size() >= 2 && args[0] && args[1]) {
                auto lhs = args[0]->get_type();
                auto rhs = args[1]->get_type();
                auto common = pick_common_type(lhs, rhs);
                auto common_builtin = common.as_shared<BuiltinType>();
                if (common_builtin && common_builtin->isArithmetic()) {
                    element_type = common;
                } else if (lhs && lhs->isArithmetic()) {
                    element_type = lhs;
                } else if (rhs && rhs->isArithmetic()) {
                    element_type = rhs;
                }
            }
            auto element_builtin = element_type.as_shared<BuiltinType>();
            if (!element_builtin) {
                element_builtin = ast_ctx_->type_ctx->get_builtin(BuiltinTypes::Double);
            }
            auto complex_type = QualType(
                ast_ctx_->type_ctx->get_complex(element_builtin->builtin_kind));
            return collect_make<BuiltinCallExpr>(kind, std::move(args), complex_type, loc);
        }
        case BuiltinKind::CPOW: {
            QualType ret = complex_double_type;
            if (!args.empty() && args[0] && args[0]->get_type()) {
                ret = args[0]->get_type();
            }
            return collect_make<BuiltinCallExpr>(kind, std::move(args), ret, loc);
        }
        case BuiltinKind::ASSUME_ALIGNED: {
            QualType ret = args.empty() ? void_ptr : args[0]->get_type();
            if (!ret) {
                ret = void_ptr;
            }
            return collect_make<BuiltinCallExpr>(kind, std::move(args), ret, loc);
        }
        case BuiltinKind::ADDRESSOF: {
            if (args.size() != 1 || !args[0]) {
                report_error("__builtin_addressof requires exactly 1 argument", loc);
                return collect_make<BuiltinCallExpr>(kind, std::move(args), void_ptr, loc);
            }

            Expr* raw = strip_implicit_casts_and_parens(args[0].get());
            QualType operand_type = raw ? raw->get_type() : args[0]->get_type();
            if (!expression_can_be_addressed_without_overload(*this, raw)) {
                report_error("__builtin_addressof requires an lvalue operand", loc);
            }
            if (auto* member = dyn_cast<MemberExpr>(raw)) {
                if (member->is_bitfield) {
                    report_error("cannot take address of bit-field", loc);
                }
            }

            QualType pointee_type =
                operand_type ? remove_reference(operand_type, ast_ctx_.get()) : void_type;
            QualType result_type(std::make_shared<PointerType>(pointee_type));
            return collect_make<BuiltinCallExpr>(
                kind, std::move(args), result_type, loc);
        }
        case BuiltinKind::CLASSIFY_TYPE: {
            QualType arg_type = args.empty() ? QualType() : args[0]->get_type();
            auto node = collect_make<BuiltinCallExpr>(kind, std::move(args), int_type, loc);
            node->const_value = classify_type(arg_type);
            return node;
        }
        case BuiltinKind::BUILTIN_LINE: {
            auto node = collect_make<BuiltinCallExpr>(kind, std::move(args), int_type, loc);
            node->const_value = 0;
            return node;
        }
        case BuiltinKind::INTEGER_PACK:
            return collect_make<BuiltinCallExpr>(
                kind,
                std::move(args),
                QualType(get_builtin_ulong()),
                loc);
        case BuiltinKind::ATOMIC_LOAD_N: {
            if (args.size() == 3) {
                // Generic __atomic_load(ptr, out_ptr, order) stores through out_ptr.
                return collect_make<BuiltinCallExpr>(kind, std::move(args), void_type, loc);
            }
            QualType ret = int_type;
            if (!args.empty()) {
                auto value_type =
                    atomic_builtin_value_type_from_pointer_arg(args[0].get(), ast_ctx_.get());
                if (value_type) {
                    ret = value_type;
                }
            }
            return collect_make<BuiltinCallExpr>(kind, std::move(args), ret, loc);
        }
        case BuiltinKind::ATOMIC_EXCHANGE_N: {
            if (args.size() == 4) {
                // Generic __atomic_exchange(ptr, value_ptr, out_ptr, order) has void result.
                return collect_make<BuiltinCallExpr>(kind, std::move(args), void_type, loc);
            }
            QualType ret = int_type;
            if (!args.empty()) {
                auto value_type =
                    atomic_builtin_value_type_from_pointer_arg(args[0].get(), ast_ctx_.get());
                if (value_type) {
                    ret = value_type;
                }
            }
            return collect_make<BuiltinCallExpr>(kind, std::move(args), ret, loc);
        }
        default:
            return nullptr;
    }
}

std::unique_ptr<Expr> Collect::builtin_call_expression_fixed_cases(
    BuiltinKind kind,
    std::vector<std::unique_ptr<Expr>>& args,
    SrcLoc loc) const {
    auto int_type = QualType(get_builtin_int());
    auto uint_type = QualType(get_builtin_uint());
    auto ulong_type = QualType(get_builtin_ulong());
    auto long_type = QualType(get_builtin_long());
    auto longlong_type = QualType(get_builtin_longlong());
    auto void_type = QualType(get_builtin_void());
    auto double_type = QualType(get_builtin_double());
    auto float_type = QualType(get_builtin_float());
    auto long_double_type = QualType(get_builtin_long_double());
    auto complex_float_type =
        QualType(ast_ctx_->type_ctx->get_complex(BuiltinTypes::Float));
    auto complex_double_type =
        QualType(ast_ctx_->type_ctx->get_complex(BuiltinTypes::Double));
    auto void_ptr = QualType(std::make_shared<PointerType>(void_type));
    auto char_ptr = QualType(std::make_shared<PointerType>(QualType(get_builtin_char())));

    switch (kind) {
        case BuiltinKind::UNREACHABLE:
        case BuiltinKind::TRAP:
        case BuiltinKind::ABORT:
        case BuiltinKind::FREE:
        case BuiltinKind::CLEAR_CACHE:
        case BuiltinKind::CLEAR_PADDING:
        case BuiltinKind::PREFETCH:
        case BuiltinKind::ATOMIC_STORE_N:
        case BuiltinKind::C11_ATOMIC_INIT:
        case BuiltinKind::ATOMIC_THREAD_FENCE:
        case BuiltinKind::ATOMIC_SIGNAL_FENCE:
        case BuiltinKind::ATOMIC_CLEAR:
        case BuiltinKind::SYNC_SYNCHRONIZE:
        case BuiltinKind::SYNC_LOCK_RELEASE:
        case BuiltinKind::STACK_RESTORE:
        case BuiltinKind::BCOPY:
        case BuiltinKind::BZERO:
            return collect_make<BuiltinCallExpr>(kind, std::move(args), void_type, loc);
        case BuiltinKind::MALLOC:
        case BuiltinKind::REALLOC:
        case BuiltinKind::CALLOC:
        case BuiltinKind::MEMCPY:
        case BuiltinKind::MEMMOVE:
        case BuiltinKind::MEMSET:
        case BuiltinKind::MEMPCPY:
        case BuiltinKind::MEMCPY_CHK:
        case BuiltinKind::MEMMOVE_CHK:
        case BuiltinKind::MEMSET_CHK:
        case BuiltinKind::MEMCHR:
        case BuiltinKind::RETURN_ADDRESS:
        case BuiltinKind::FRAME_ADDRESS:
        case BuiltinKind::EXTRACT_RETURN_ADDR:
        case BuiltinKind::ALLOCA:
        case BuiltinKind::STACK_SAVE:
            return collect_make<BuiltinCallExpr>(kind, std::move(args), void_ptr, loc);
        case BuiltinKind::TYPES_COMPATIBLE_P:
        case BuiltinKind::AVAILABLE:
        case BuiltinKind::ADD_OVERFLOW:
        case BuiltinKind::SUB_OVERFLOW:
        case BuiltinKind::MUL_OVERFLOW:
        case BuiltinKind::ADD_OVERFLOW_P:
        case BuiltinKind::SUB_OVERFLOW_P:
        case BuiltinKind::CLZ:
        case BuiltinKind::CLZL:
        case BuiltinKind::CLZLL:
        case BuiltinKind::CTZ:
        case BuiltinKind::CTZL:
        case BuiltinKind::CTZLL:
        case BuiltinKind::FFS:
        case BuiltinKind::FFSL:
        case BuiltinKind::FFSLL:
        case BuiltinKind::POPCOUNT:
        case BuiltinKind::POPCOUNTL:
        case BuiltinKind::POPCOUNTLL:
        case BuiltinKind::PRINTF:
        case BuiltinKind::PUTS:
        case BuiltinKind::PUTCHAR:
        case BuiltinKind::FPRINTF:
        case BuiltinKind::SPRINTF:
        case BuiltinKind::SNPRINTF:
        case BuiltinKind::SPRINTF_CHK:
        case BuiltinKind::SNPRINTF_CHK:
        case BuiltinKind::VSPRINTF_CHK:
        case BuiltinKind::VSNPRINTF_CHK:
        case BuiltinKind::ISNAN:
        case BuiltinKind::ISINF:
        case BuiltinKind::ISINF_SIGN:
        case BuiltinKind::ISFINITE:
        case BuiltinKind::ISNORMAL:
        case BuiltinKind::FPCLASSIFY:
        case BuiltinKind::ISEQSIG:
        case BuiltinKind::ISUNORDERED:
        case BuiltinKind::ISLESS:
        case BuiltinKind::ISLESSEQUAL:
        case BuiltinKind::ISGREATER:
        case BuiltinKind::ISGREATEREQUAL:
        case BuiltinKind::ISLESSGREATER:
        case BuiltinKind::SIGNBIT:
        case BuiltinKind::SIGNBITF:
        case BuiltinKind::SIGNBITL:
        case BuiltinKind::CLRSB:
        case BuiltinKind::CLRSBL:
        case BuiltinKind::CLRSBLL:
        case BuiltinKind::PARITY:
        case BuiltinKind::PARITYL:
        case BuiltinKind::PARITYLL:
        case BuiltinKind::ILOGB:
        case BuiltinKind::ILOGBF:
        case BuiltinKind::ILOGBL:
        case BuiltinKind::VA_ARG_PACK:
        case BuiltinKind::STRCMP:
        case BuiltinKind::STRNCMP:
        case BuiltinKind::STRNCASECMP:
        case BuiltinKind::MEMCMP:
        case BuiltinKind::MEMCMP_EQ:
        case BuiltinKind::ABS:
            return collect_make<BuiltinCallExpr>(kind, std::move(args), int_type, loc);
        case BuiltinKind::OBJECT_SIZE:
        case BuiltinKind::DYNAMIC_OBJECT_SIZE:
        case BuiltinKind::STRLEN:
        case BuiltinKind::STRCSPN:
        case BuiltinKind::STRSPN:
            return collect_make<BuiltinCallExpr>(kind, std::move(args), ulong_type, loc);
        case BuiltinKind::BSWAP16:
            return collect_make<BuiltinCallExpr>(
                kind,
                std::move(args),
                QualType(ast_ctx_->type_ctx->get_builtin(BuiltinTypes::UShort)),
                loc);
        case BuiltinKind::BSWAP32:
        case BuiltinKind::IA32_BZHI_SI:
            return collect_make<BuiltinCallExpr>(kind, std::move(args), uint_type, loc);
        case BuiltinKind::BSWAP64:
            return collect_make<BuiltinCallExpr>(
                kind,
                std::move(args),
                QualType(ast_ctx_->type_ctx->get_builtin(BuiltinTypes::ULongLong)),
                loc);
        case BuiltinKind::STRCHR:
        case BuiltinKind::STRRCHR:
        case BuiltinKind::STRSTR:
        case BuiltinKind::STRDUP:
        case BuiltinKind::STPNCPY:
        case BuiltinKind::STRNDUP:
        case BuiltinKind::STRCPY:
        case BuiltinKind::STRNCPY:
        case BuiltinKind::STRCAT:
        case BuiltinKind::STRNCAT:
        case BuiltinKind::STPCPY:
        case BuiltinKind::STRCPY_CHK:
        case BuiltinKind::STPCPY_CHK:
        case BuiltinKind::STRNCPY_CHK:
        case BuiltinKind::STRCAT_CHK:
        case BuiltinKind::STRNCAT_CHK:
        case BuiltinKind::BUILTIN_FILE:
        case BuiltinKind::BUILTIN_FUNCTION:
            return collect_make<BuiltinCallExpr>(kind, std::move(args), char_ptr, loc);
        case BuiltinKind::BUILTIN_HUGE_VAL:
        case BuiltinKind::INF:
        case BuiltinKind::NAN_BUILTIN:
        case BuiltinKind::NANS:
        case BuiltinKind::FABS:
        case BuiltinKind::POW:
        case BuiltinKind::SQRT:
        case BuiltinKind::CBRT:
        case BuiltinKind::SIN:
        case BuiltinKind::COS:
        case BuiltinKind::TAN:
        case BuiltinKind::ASIN:
        case BuiltinKind::ACOS:
        case BuiltinKind::ATAN:
        case BuiltinKind::ATAN2:
        case BuiltinKind::SINH:
        case BuiltinKind::COSH:
        case BuiltinKind::TANH:
        case BuiltinKind::ASINH:
        case BuiltinKind::ACOSH:
        case BuiltinKind::ATANH:
        case BuiltinKind::LOG:
        case BuiltinKind::LOG2:
        case BuiltinKind::LOG10:
        case BuiltinKind::LOG1P:
        case BuiltinKind::LOGB:
        case BuiltinKind::EXP:
        case BuiltinKind::EXP2:
        case BuiltinKind::EXPM1:
        case BuiltinKind::FREXP:
        case BuiltinKind::LDEXP:
        case BuiltinKind::SCALBN:
        case BuiltinKind::SCALBLN:
        case BuiltinKind::CEIL:
        case BuiltinKind::FLOOR:
        case BuiltinKind::ROUND:
        case BuiltinKind::RINT:
        case BuiltinKind::NEARBYINT:
        case BuiltinKind::COPYSIGN:
        case BuiltinKind::HYPOT:
        case BuiltinKind::FMIN:
        case BuiltinKind::FMAX:
        case BuiltinKind::FDIM:
        case BuiltinKind::FMA:
        case BuiltinKind::FMOD:
        case BuiltinKind::REMAINDER:
        case BuiltinKind::REMQUO:
        case BuiltinKind::NEXTAFTER:
        case BuiltinKind::NEXTTOWARD:
        case BuiltinKind::ERF:
        case BuiltinKind::ERFC:
        case BuiltinKind::LGAMMA:
        case BuiltinKind::TGAMMA:
        case BuiltinKind::MODF:
        case BuiltinKind::TRUNC:
            return collect_make<BuiltinCallExpr>(kind, std::move(args), double_type, loc);
        case BuiltinKind::BUILTIN_HUGE_VALF:
        case BuiltinKind::INFF:
        case BuiltinKind::NANF:
        case BuiltinKind::NANSF:
        case BuiltinKind::FABSF:
        case BuiltinKind::POWF:
        case BuiltinKind::SQRTF:
        case BuiltinKind::CBRTF:
        case BuiltinKind::SINF:
        case BuiltinKind::COSF:
        case BuiltinKind::TANF:
        case BuiltinKind::ASINF:
        case BuiltinKind::ACOSF:
        case BuiltinKind::ATANF:
        case BuiltinKind::ATAN2F:
        case BuiltinKind::SINHF:
        case BuiltinKind::COSHF:
        case BuiltinKind::TANHF:
        case BuiltinKind::ASINHF:
        case BuiltinKind::ACOSHF:
        case BuiltinKind::ATANHF:
        case BuiltinKind::LOGF:
        case BuiltinKind::LOG2F:
        case BuiltinKind::LOG10F:
        case BuiltinKind::LOG1PF:
        case BuiltinKind::LOGBF:
        case BuiltinKind::EXPF:
        case BuiltinKind::EXP2F:
        case BuiltinKind::EXPM1F:
        case BuiltinKind::FREXPF:
        case BuiltinKind::LDEXPF:
        case BuiltinKind::SCALBNF:
        case BuiltinKind::SCALBLNF:
        case BuiltinKind::CEILF:
        case BuiltinKind::FLOORF:
        case BuiltinKind::ROUNDF:
        case BuiltinKind::RINTF:
        case BuiltinKind::NEARBYINTF:
        case BuiltinKind::COPYSIGNF:
        case BuiltinKind::HYPOTF:
        case BuiltinKind::FMINF:
        case BuiltinKind::FMAXF:
        case BuiltinKind::FDIMF:
        case BuiltinKind::FMAF:
        case BuiltinKind::FMODF:
        case BuiltinKind::REMAINDERF:
        case BuiltinKind::REMQUOF:
        case BuiltinKind::NEXTAFTERF:
        case BuiltinKind::NEXTTOWARDF:
        case BuiltinKind::ERFF:
        case BuiltinKind::ERFCF:
        case BuiltinKind::LGAMMAF:
        case BuiltinKind::TGAMMAF:
        case BuiltinKind::MODFF:
        case BuiltinKind::TRUNCF:
            return collect_make<BuiltinCallExpr>(kind, std::move(args), float_type, loc);
        case BuiltinKind::CONJF:
            return collect_make<BuiltinCallExpr>(kind, std::move(args), complex_float_type, loc);
        case BuiltinKind::BUILTIN_HUGE_VALL:
        case BuiltinKind::INFL:
        case BuiltinKind::NANL:
        case BuiltinKind::NANSL:
        case BuiltinKind::FABSL:
        case BuiltinKind::POWL:
        case BuiltinKind::SQRTL:
        case BuiltinKind::CBRTL:
        case BuiltinKind::SINL:
        case BuiltinKind::COSL:
        case BuiltinKind::TANL:
        case BuiltinKind::ASINL:
        case BuiltinKind::ACOSL:
        case BuiltinKind::ATANL:
        case BuiltinKind::ATAN2L:
        case BuiltinKind::SINHL:
        case BuiltinKind::COSHL:
        case BuiltinKind::TANHL:
        case BuiltinKind::ASINHL:
        case BuiltinKind::ACOSHL:
        case BuiltinKind::ATANHL:
        case BuiltinKind::LOGL:
        case BuiltinKind::LOG2L:
        case BuiltinKind::LOG10L:
        case BuiltinKind::LOG1PL:
        case BuiltinKind::LOGBL:
        case BuiltinKind::EXPL:
        case BuiltinKind::EXP2L:
        case BuiltinKind::EXPM1L:
        case BuiltinKind::FREXPL:
        case BuiltinKind::LDEXPL:
        case BuiltinKind::SCALBNL:
        case BuiltinKind::SCALBLNL:
        case BuiltinKind::CEILL:
        case BuiltinKind::FLOORL:
        case BuiltinKind::ROUNDL:
        case BuiltinKind::RINTL:
        case BuiltinKind::NEARBYINTL:
        case BuiltinKind::COPYSIGNL:
        case BuiltinKind::HYPOTL:
        case BuiltinKind::FMINL:
        case BuiltinKind::FMAXL:
        case BuiltinKind::FDIML:
        case BuiltinKind::FMAL:
        case BuiltinKind::FMODL:
        case BuiltinKind::REMAINDERL:
        case BuiltinKind::REMQUOL:
        case BuiltinKind::NEXTAFTERL:
        case BuiltinKind::NEXTTOWARDL:
        case BuiltinKind::ERFL:
        case BuiltinKind::ERFCL:
        case BuiltinKind::LGAMMAL:
        case BuiltinKind::TGAMMAL:
        case BuiltinKind::MODFL:
        case BuiltinKind::TRUNCL:
            return collect_make<BuiltinCallExpr>(kind, std::move(args), long_double_type, loc);
        case BuiltinKind::CEXPI:
            return collect_make<BuiltinCallExpr>(kind, std::move(args), complex_double_type, loc);
        case BuiltinKind::LABS:
        case BuiltinKind::LRINT:
        case BuiltinKind::LRINTF:
        case BuiltinKind::LRINTL:
        case BuiltinKind::LROUND:
        case BuiltinKind::LROUNDF:
        case BuiltinKind::LROUNDL:
            return collect_make<BuiltinCallExpr>(kind, std::move(args), long_type, loc);
        case BuiltinKind::LLABS:
        case BuiltinKind::LLRINT:
        case BuiltinKind::LLRINTF:
        case BuiltinKind::LLRINTL:
        case BuiltinKind::LLROUND:
        case BuiltinKind::LLROUNDF:
        case BuiltinKind::LLROUNDL:
            return collect_make<BuiltinCallExpr>(kind, std::move(args), longlong_type, loc);
        default:
            return nullptr;
    }
}

std::unique_ptr<Expr> Collect::builtin_call_expression_atomic_cases(
    BuiltinKind kind,
    std::vector<std::unique_ptr<Expr>>& args,
    SrcLoc loc) const {
    auto int_type = QualType(get_builtin_int());
    auto bool_type = QualType(get_builtin_bool());

    switch (kind) {
        case BuiltinKind::ATOMIC_IS_LOCK_FREE:
            return collect_make<BuiltinCallExpr>(kind, std::move(args), int_type, loc);
        case BuiltinKind::ATOMIC_ALWAYS_LOCK_FREE: {
            auto node = collect_make<BuiltinCallExpr>(kind, std::move(args), int_type, loc);
            if (!node->args.empty() && node->args[0]) {
                auto size = try_evaluate_with_consteval_compat(
                    node->args[0].get(),
                    ConstEvalMode::builtin_query());
                if (size.has_value()) {
                    node->const_value = (*size > 0 && *size <= 16) ? 1 : 0;
                }
            }
            return node;
        }
        case BuiltinKind::ATOMIC_FETCH_ADD:
        case BuiltinKind::ATOMIC_FETCH_SUB:
        case BuiltinKind::C11_ATOMIC_FETCH_ADD:
        case BuiltinKind::C11_ATOMIC_FETCH_SUB:
        case BuiltinKind::ATOMIC_FETCH_AND:
        case BuiltinKind::ATOMIC_FETCH_OR:
        case BuiltinKind::ATOMIC_FETCH_XOR:
        case BuiltinKind::ATOMIC_FETCH_NAND:
        case BuiltinKind::ATOMIC_ADD_FETCH:
        case BuiltinKind::ATOMIC_SUB_FETCH:
        case BuiltinKind::ATOMIC_AND_FETCH:
        case BuiltinKind::ATOMIC_OR_FETCH:
        case BuiltinKind::ATOMIC_XOR_FETCH:
        case BuiltinKind::ATOMIC_NAND_FETCH:
        case BuiltinKind::SYNC_FETCH_AND_ADD:
        case BuiltinKind::SYNC_FETCH_AND_SUB:
        case BuiltinKind::SYNC_FETCH_AND_OR:
        case BuiltinKind::SYNC_FETCH_AND_AND:
        case BuiltinKind::SYNC_FETCH_AND_XOR:
        case BuiltinKind::SYNC_FETCH_AND_NAND:
        case BuiltinKind::SYNC_ADD_AND_FETCH:
        case BuiltinKind::SYNC_SUB_AND_FETCH:
        case BuiltinKind::SYNC_OR_AND_FETCH:
        case BuiltinKind::SYNC_AND_AND_FETCH:
        case BuiltinKind::SYNC_XOR_AND_FETCH:
        case BuiltinKind::SYNC_NAND_AND_FETCH:
        case BuiltinKind::SYNC_LOCK_TEST_AND_SET:
        case BuiltinKind::SYNC_VAL_COMPARE_AND_SWAP: {
            QualType ret = int_type;
            if (!args.empty()) {
                auto value_type =
                    atomic_builtin_value_type_from_pointer_arg(args[0].get(), ast_ctx_.get());
                if (value_type) {
                    ret = value_type;
                }
            }
            return collect_make<BuiltinCallExpr>(kind, std::move(args), ret, loc);
        }
        case BuiltinKind::ATOMIC_COMPARE_EXCHANGE_N:
        case BuiltinKind::ATOMIC_TEST_AND_SET:
        case BuiltinKind::SYNC_BOOL_COMPARE_AND_SWAP:
            return collect_make<BuiltinCallExpr>(kind, std::move(args), bool_type, loc);
        default:
            return nullptr;
    }
}

std::unique_ptr<Expr> Collect::builtin_call_expression(
    BuiltinKind kind,
    std::vector<std::unique_ptr<Expr>> args,
    SrcLoc loc) const {
    if (auto special = builtin_call_expression_special_cases(kind, args, loc)) {
        return special;
    }
    if (auto fixed = builtin_call_expression_fixed_cases(kind, args, loc)) {
        return fixed;
    }
    if (auto atomic = builtin_call_expression_atomic_cases(kind, args, loc)) {
        return atomic;
    }

    auto int_type = QualType(get_builtin_int());
    report_error("unhandled builtin in collect semantic action", loc);
    return collect_make<BuiltinCallExpr>(kind, std::move(args), int_type, loc);
}

std::unique_ptr<Expr> Collect::prepare_unevaluated_operand(std::unique_ptr<Expr> expr,
                                                                    const char* reason) {

    UnevaluatedContextScope unevaluated_scope(this, reason);
    return collect_apply_standard_conversions(std::move(expr), ExprUseContext::Unevaluated);
}


Collect::ValueCategory Collect::classify_value_category(Expr* expr) const {

    if (!expr) {
        return ValueCategory::Unknown;
    }

    if (!lang_opts_.is_cxx_mode()) {
        if (expr->isLValue()) {
            return ValueCategory::LValue;
        }
        return ValueCategory::PRValue;
    }

    if (auto* cast = dyn_cast<ImplicitCast>(expr)) {
        switch (cast->kind) {
            case ImplicitCastTypes::UNKNOWN:
                return classify_value_category(cast->expr.get());
            case ImplicitCastTypes::LVALUE_TO_RVALUE:
            case ImplicitCastTypes::ARITH_CAST:
            case ImplicitCastTypes::RAW_CAST:
            case ImplicitCastTypes::ARRAY_TO_POINTER:
            case ImplicitCastTypes::FUNCTION_TO_POINTER:
            case ImplicitCastTypes::LAMBDA_TO_FUNCTION_POINTER:
            case ImplicitCastTypes::VECTOR_SPLAT:
            case ImplicitCastTypes::REAL_TO_COMPLEX:
            case ImplicitCastTypes::COMPLEX_TO_REAL:
            case ImplicitCastTypes::COMPLEX_TO_COMPLEX:
                if (auto ref = desugar_type(cast->ctype).as_shared<ReferenceType>()) {
                    return ref->isRValueReference() ? ValueCategory::XValue
                                                    : ValueCategory::LValue;
                }
                return ValueCategory::PRValue;
        }
    }

    if (auto* call = dyn_cast<FuncCall>(expr)) {
        auto call_type = desugar_type(call->get_type());
        if (auto ref = call_type.as_shared<ReferenceType>()) {
            return ref->isRValueReference() ? ValueCategory::XValue : ValueCategory::LValue;
        }
        return ValueCategory::PRValue;
    }

    if (auto* call = dyn_cast<CppMemberCallExpr>(expr)) {
        auto call_type = desugar_type(call->get_type());
        if (auto ref = call_type.as_shared<ReferenceType>()) {
            return ref->isRValueReference() ? ValueCategory::XValue : ValueCategory::LValue;
        }
        return ValueCategory::PRValue;
    }

    if (auto* paren = dyn_cast<ParenExpr>(expr)) {
        return classify_value_category(paren->subexpr.get());
    }

    if (auto* dynamic_cast_expr = dyn_cast<CppDynamicCastExpr>(expr)) {
        auto cast_type = desugar_type(dynamic_cast_expr->get_type());
        if (auto ref = cast_type.as_shared<ReferenceType>()) {
            return ref->isRValueReference() ? ValueCategory::XValue : ValueCategory::LValue;
        }
        return ValueCategory::PRValue;
    }

    if (auto* explicit_cast = dyn_cast<ExplicitCast>(expr)) {
        auto cast_type = desugar_type(explicit_cast->get_type());
        if (auto ref = cast_type.as_shared<ReferenceType>()) {
            return ref->isRValueReference() ? ValueCategory::XValue
                                            : ValueCategory::LValue;
        }
        return ValueCategory::PRValue;
    }

    if (auto* function_style_cast = dyn_cast<CppFunctionStyleCastExpr>(expr)) {
        auto cast_type = desugar_type(function_style_cast->get_type());
        if (auto ref = cast_type.as_shared<ReferenceType>()) {
            return ref->isRValueReference() ? ValueCategory::XValue
                                            : ValueCategory::LValue;
        }
        return ValueCategory::PRValue;
    }

    if (auto* unary = dyn_cast<UnaryOperation>(expr)) {
        switch (unary->uop) {
            case UnaryOpTypes::INCREMENT_PREFIX:
            case UnaryOpTypes::DECREMENT_PREFIX:
            case UnaryOpTypes::DEREFERENCE:
                return ValueCategory::LValue;
            case UnaryOpTypes::REAL_PART:
            case UnaryOpTypes::IMAG_PART: {
                auto operand_category = classify_value_category(unary->exp.get());
                if (operand_category == ValueCategory::LValue ||
                    operand_category == ValueCategory::XValue) {
                    return operand_category;
                }
                return ValueCategory::PRValue;
            }
            default:
                return ValueCategory::PRValue;
        }
    }

    if (auto* unary = dyn_cast<DependentUnaryExpr>(expr)) {
        switch (unary->uop) {
            case UnaryOpTypes::DEREFERENCE:
                return ValueCategory::LValue;
            default:
                return ValueCategory::PRValue;
        }
    }

    if (auto* binary = dyn_cast<DependentBinaryExpr>(expr)) {
        if (binary->bop == BinOpTypes::COMMA) {
            return classify_value_category(binary->right.get());
        }
        if (lang_opts_.is_cxx_mode() && is_assignment_binop(binary->bop)) {
            return ValueCategory::LValue;
        }
        return ValueCategory::PRValue;
    }

    if (isa<CppBuiltinThreeWayCompareExpr>(expr)) {
        return ValueCategory::PRValue;
    }

    if (auto* member = dyn_cast<MemberExpr>(expr)) {
        if (!member->isArrow) {
            auto base_category = classify_value_category(member->base.get());
            if (base_category == ValueCategory::XValue) {
                return ValueCategory::XValue;
            }
            if (base_category == ValueCategory::PRValue) {
                return ValueCategory::XValue;
            }
        }
        return ValueCategory::LValue;
    }

    if (auto* member_ptr = dyn_cast<MemberPointerAccessExpr>(expr)) {
        if (member_ptr->is_function_member) {
            return ValueCategory::PRValue;
        }
        if (!member_ptr->is_arrow) {
            auto base_category = classify_value_category(member_ptr->base.get());
            if (base_category == ValueCategory::XValue ||
                base_category == ValueCategory::PRValue) {
                return ValueCategory::XValue;
            }
        }
        return ValueCategory::LValue;
    }

    if (isa<DependentMemberPointerAccessExpr>(expr)) {
        return ValueCategory::LValue;
    }

    if (auto* binary = dyn_cast<BinaryOperation>(expr)) {
        if (binary->bop == BinOpTypes::COMMA) {
            return classify_value_category(binary->right.get());
        }
        if (lang_opts_.is_cxx_mode() &&
            binary->bop == BinOpTypes::ASSIGN) {
            return ValueCategory::LValue;
        }
        return ValueCategory::PRValue;
    }

    if (dyn_cast<CompoundAssignOperation>(expr)) {
        if (lang_opts_.is_cxx_mode()) {
            return ValueCategory::LValue;
        }
        return ValueCategory::PRValue;
    }

    if (auto* cond = dyn_cast<CondExpr>(expr)) {
        Expr* true_operand = cond->true_expr ? cond->true_expr.get() : cond->condition.get();
        auto true_category = classify_value_category(true_operand);
        auto false_category = classify_value_category(cond->false_expr.get());
        auto true_type = true_operand ? true_operand->get_type() : QualType();
        auto false_type = cond->false_expr ? cond->false_expr->get_type() : QualType();
        if (!merge_cpp_conditional_glvalue_type(
                true_type,
                false_type,
                true_category,
                false_category)) {
            return ValueCategory::PRValue;
        }
        return true_category;
    }

    if (auto* error = dyn_cast<ErrorExpr>(expr)) {
        (void)error;
        return ValueCategory::Unknown;
    }

    if (expr->isLValue()) {
        return ValueCategory::LValue;
    }
    return ValueCategory::PRValue;
}


Collect::ImplicitConversionSequence Collect::build_implicit_conversion_sequence(QualType from,
                                                                                 QualType to,
                                                                                 ExprUseContext context) const {

    ImplicitConversionSequence seq;
    seq.from = from;
    seq.to = to;

    if (!from || !to) {
        seq.kind = ConversionSequenceKind::Failed;
        seq.rank = ConversionSequenceRank::NoMatch;
        seq.viable = false;
        seq.note = "missing source or destination type";
        return seq;
    }

    if (from.equals_qualified(to)) {
        seq.kind = ConversionSequenceKind::Identity;
        seq.rank = ConversionSequenceRank::ExactMatch;
        return seq;
    }

        if (from.equals_unqualified(to)) {
            seq.kind = ConversionSequenceKind::Qualification;
            seq.rank = ConversionSequenceRank::ExactMatch;
            seq.exact_subrank = qualification_conversion_exact_subrank(
                from,
                to,
                ast_ctx_.get());
            return seq;
        }

    auto from_canonical = desugar_type(from, ast_ctx_.get());
    auto to_canonical = desugar_type(to, ast_ctx_.get());
    auto from_kind = from_canonical ? from_canonical->kind : TypeKind::Other;
    auto to_kind = to_canonical ? to_canonical->kind : TypeKind::Other;
    bool from_is_nullptr = is_nullptr_type(from, ast_ctx_.get());
    bool to_is_nullptr = is_nullptr_type(to, ast_ctx_.get());

    if (auto to_record = to_canonical.as_shared<ObjectType>();
        to_record && to_record->is_union && to_record->is_transparent_union) {
        for (const auto& field :
             get_record_fields_for_type_matching(to_record.get())) {
            QualType member_type = decay_parameter_type(field.type);
            auto member_seq =
                build_implicit_conversion_sequence(from, member_type, context);
            if (!member_seq.viable) {
                continue;
            }
            seq.kind = member_seq.kind;
            seq.rank = member_seq.rank;
            seq.detail_kind = member_seq.detail_kind;
            seq.exact_subrank = member_seq.exact_subrank;
            seq.note = member_seq.note;
            return seq;
        }
    }

    if (from_kind == TypeKind::Array && to_kind == TypeKind::Pointer) {
        auto from_arr = from_canonical.as_shared<ArrayType>();
        auto to_ptr = to_canonical.as_shared<PointerType>();
        if (from_arr && to_ptr && from_arr->element_type.equals_unqualified(to_ptr->pointed_type)) {
            seq.kind = ConversionSequenceKind::ArrayToPointer;
            seq.rank = ConversionSequenceRank::Conversion;
            return seq;
        }
    }

    if (from_kind == TypeKind::Function && to_kind == TypeKind::Pointer) {
        auto to_ptr = to_canonical.as_shared<PointerType>();
        if (to_ptr && to_ptr->pointed_type.equals_unqualified(from_canonical)) {
            seq.kind = ConversionSequenceKind::FunctionToPointer;
            seq.rank = ConversionSequenceRank::Conversion;
            return seq;
        }
    }

    if ((is_arithmetic_adjacent(from, ast_ctx_.get()) &&
         is_arithmetic_adjacent(to, ast_ctx_.get())) ||
        from->isComplex() || to->isComplex()) {
        auto promoted = integer_promotion_type(from);
        seq.kind = ConversionSequenceKind::Numeric;
        seq.rank = promoted.equals_qualified(to)
            ? ConversionSequenceRank::Promotion
            : ConversionSequenceRank::Conversion;
        return seq;
    }

    if (from_is_nullptr && is_null_pointer_like_type(to, ast_ctx_.get()) && !to_is_nullptr) {
        seq.kind = ConversionSequenceKind::Pointer;
        seq.rank = ConversionSequenceRank::Conversion;
        seq.detail_kind = ConversionSequenceDetailKind::NullPointerConstant;
        return seq;
    }

    if (from_kind == TypeKind::Pointer && to_kind == TypeKind::Pointer) {
        auto from_ptr = from_canonical.as_shared<PointerType>();
        auto to_ptr = to_canonical.as_shared<PointerType>();
        bool to_void = to_ptr && to_ptr->pointed_type && to_ptr->pointed_type->isVoid();
        bool from_void = from_ptr && from_ptr->pointed_type && from_ptr->pointed_type->isVoid();
        bool derived_to_base =
            from_ptr && to_ptr &&
            can_convert_derived_to_base_object(
                from_ptr->pointed_type, to_ptr->pointed_type);
        if (to_void || from_void || pointers_to_compatible_types(from_canonical, to_canonical)) {
            seq.kind = ConversionSequenceKind::Pointer;
            seq.rank = ConversionSequenceRank::Conversion;
            return seq;
        }
        if (derived_to_base) {
            seq.kind = ConversionSequenceKind::Pointer;
            seq.rank = ConversionSequenceRank::Conversion;
            return seq;
        }
    }

    if (from_kind == TypeKind::MemberPointer && to_kind == TypeKind::MemberPointer) {
        if (from.equals_qualified(to)) {
            seq.kind = ConversionSequenceKind::Identity;
            seq.rank = ConversionSequenceRank::ExactMatch;
            return seq;
        }
        if (member_pointer_convertible_to(from_canonical, to_canonical)) {
            seq.kind = from.equals_unqualified(to)
                ? ConversionSequenceKind::Qualification
                : ConversionSequenceKind::Pointer;
            seq.rank = ConversionSequenceRank::Conversion;
            seq.detail_kind = ConversionSequenceDetailKind::MemberPointer;
            return seq;
        }
    }

    if (context == ExprUseContext::Condition &&
        allows_condition_conversion(from, ast_ctx_.get())) {
        seq.kind = ConversionSequenceKind::Numeric;
        seq.rank = ConversionSequenceRank::Conversion;
        return seq;
    }

    seq.kind = ConversionSequenceKind::Failed;
    seq.rank = ConversionSequenceRank::NoMatch;
    seq.viable = false;
    seq.note = "no implicit conversion sequence";
    return seq;
}

Collect::ImplicitConversionSequence Collect::build_cpp_overload_conversion_sequence(Expr* arg,
                                                                                     QualType to,
                                                                                     bool allow_user_defined) {

    ImplicitConversionSequence seq;
    seq.to = to;
    if (!arg || !to) {
        seq.kind = ConversionSequenceKind::Failed;
        seq.rank = ConversionSequenceRank::NoMatch;
        seq.viable = false;
        seq.note = "missing argument expression or destination type";
        return seq;
    }

    auto to_canonical = desugar_type(to, ast_ctx_.get());
    auto to_kind = to_canonical ? to_canonical->kind : TypeKind::Other;
    if (to_kind != TypeKind::Reference) {
        ImplicitConversionSequence braced_init_seq;
        if (probe_cpp_braced_init_argument_conversion(
                arg, to, arg->location, braced_init_seq)) {
            return braced_init_seq;
        }
    }

    QualType from = arg->get_type();
    seq.from = from;
    if (!from) {
        seq.kind = ConversionSequenceKind::Failed;
        seq.rank = ConversionSequenceRank::NoMatch;
        seq.viable = false;
        seq.note = "argument expression has no type";
        return seq;
    }

    if (to_kind == TypeKind::Reference) {
        return build_cpp_overload_reference_conversion_sequence(
            arg, from, to, allow_user_defined);
    }

    return build_cpp_overload_nonreference_conversion_sequence(
        arg, from, to, allow_user_defined);
}

Collect::ImplicitConversionSequence
Collect::build_cpp_overload_reference_conversion_sequence(
    Expr* arg,
    QualType from,
    QualType to,
    bool allow_user_defined) {
    ImplicitConversionSequence seq;
    seq.to = to;

    auto to_ref = desugar_type(to, ast_ctx_.get()).as_shared<ReferenceType>();
    if (!to_ref || !to_ref->referred_type) {
        seq.kind = ConversionSequenceKind::Failed;
        seq.rank = ConversionSequenceRank::NoMatch;
        seq.detail_kind = ConversionSequenceDetailKind::None;
        seq.viable = false;
        seq.note = "reference parameter has invalid referred type";
        return seq;
    }

    QualType source_type = remove_reference(from);
    QualType target_type = to_ref->referred_type;
    seq.from = source_type;
    QualType canonical_source_type = desugar_type(source_type, ast_ctx_.get());
    QualType canonical_target_type = desugar_type(target_type, ast_ctx_.get());
    QualType array_normalized_source_type =
        normalize_array_qualifiers_for_conversion(source_type, ast_ctx_.get());
    QualType array_normalized_target_type =
        normalize_array_qualifiers_for_conversion(target_type, ast_ctx_.get());
    auto arg_category = classify_value_category(strip_implicit_casts(arg));

    auto fail_binding = [&](const std::string& reason) {
        seq.kind = ConversionSequenceKind::Failed;
        seq.rank = ConversionSequenceRank::NoMatch;
        seq.detail_kind =
            ConversionSequenceDetailKind::ReferenceRefQualifierMismatch;
        seq.viable = false;
        seq.note = reason;
        return seq;
    };

    auto try_direct_binding = [&](int identity_subrank,
                                  int qualification_subrank) -> bool {
        bool same_qualified_type =
            source_type.equals_qualified(target_type) ||
            (canonical_source_type &&
             canonical_target_type &&
             canonical_source_type.equals_qualified(canonical_target_type)) ||
            array_normalized_source_type.equals_qualified(
                array_normalized_target_type) ||
            types_equivalent_after_template_argument_canonicalization(
                source_type,
                target_type,
                ast_ctx_.get(),
                /*ignore_top_level_qualifiers=*/false);
        if (same_qualified_type) {
            seq.kind = ConversionSequenceKind::Identity;
            seq.rank = ConversionSequenceRank::ExactMatch;
            seq.detail_kind = ConversionSequenceDetailKind::ReferenceDirectBinding;
            seq.exact_subrank = identity_subrank;
            return true;
        }
        bool same_unqualified_type =
            source_type.equals_unqualified(target_type) ||
            (canonical_source_type &&
             canonical_target_type &&
             canonical_source_type.equals_unqualified(canonical_target_type)) ||
            array_normalized_source_type.equals_unqualified(
                array_normalized_target_type) ||
            types_equivalent_after_template_argument_canonicalization(
                source_type,
                target_type,
                ast_ctx_.get(),
                /*ignore_top_level_qualifiers=*/true);
        if (same_unqualified_type &&
            (target_type.has_all_qualifiers_of(source_type) ||
             array_normalized_target_type.has_all_qualifiers_of(
                 array_normalized_source_type))) {
            seq.kind = ConversionSequenceKind::Qualification;
            seq.rank = ConversionSequenceRank::ExactMatch;
            seq.detail_kind = ConversionSequenceDetailKind::ReferenceDirectBinding;
            seq.exact_subrank = qualification_conversion_exact_subrank(
                source_type,
                target_type,
                ast_ctx_.get(),
                qualification_subrank);
            return true;
        }
        if (can_convert_derived_to_base_object(source_type, target_type)) {
            seq.kind = ConversionSequenceKind::Pointer;
            seq.rank = ConversionSequenceRank::Conversion;
            seq.detail_kind = ConversionSequenceDetailKind::ReferenceDirectBinding;
            seq.exact_subrank = -1;
            return true;
        }
        return false;
    };

    auto try_temporary_conversion = [&]() -> bool {
        auto converted = build_implicit_conversion_sequence(
            source_type,
            target_type,
            ExprUseContext::CallArgument);
        if (!converted.viable) {
            return false;
        }
        seq.kind = converted.kind;
        seq.rank = converted.rank;
        seq.detail_kind = ConversionSequenceDetailKind::ReferenceTemporaryBinding;
        seq.note = converted.note;
        return true;
    };

    auto try_user_defined_conversion = [&]() -> bool {
        if (!allow_user_defined) {
            return false;
        }
        auto conversion_match = select_cpp_user_defined_conversion(
            arg, target_type, /*allow_explicit_constructors=*/false);
        if (!conversion_match.has_value()) {
            return false;
        }
        seq.kind = ConversionSequenceKind::UserDefined;
        seq.rank = ConversionSequenceRank::Conversion;
        seq.detail_kind = ConversionSequenceDetailKind::ReferenceTemporaryBinding;
        seq.exact_subrank = -1;
        seq.note = "user-defined conversion sequence";
        return true;
    };

    if (to_ref->isLValueReference()) {
        if (arg_category == ValueCategory::LValue) {
            if (try_direct_binding(/*identity*/0, /*qualification*/1)) {
                return seq;
            }
            if (!target_type.is_const()) {
                return fail_binding(
                    "lvalue reference requires directly bindable lvalue");
            }
            if (!try_temporary_conversion()) {
                if (try_user_defined_conversion()) {
                    return seq;
                }
                return fail_binding(
                    "const lvalue reference cannot bind to argument");
            }
            if (seq.rank == ConversionSequenceRank::ExactMatch) {
                seq.exact_subrank = 2;
            }
            return seq;
        }

        if (!target_type.is_const()) {
            return fail_binding("non-const lvalue reference cannot bind to temporary");
        }

        if (try_direct_binding(/*identity*/2, /*qualification*/2)) {
            return seq;
        }
        if (!try_temporary_conversion()) {
            if (try_user_defined_conversion()) {
                return seq;
            }
            return fail_binding("const lvalue reference cannot bind to argument");
        }
        if (seq.rank == ConversionSequenceRank::ExactMatch) {
            seq.exact_subrank = 2;
        }
        return seq;
    }

    if (arg_category == ValueCategory::LValue) {
        return fail_binding("rvalue reference cannot bind to lvalue");
    }

    if (try_direct_binding(/*identity*/0, /*qualification*/1)) {
        return seq;
    }
    if (!try_temporary_conversion()) {
        if (try_user_defined_conversion()) {
            return seq;
        }
        return fail_binding("rvalue reference cannot bind to argument");
    }
    return seq;
}

Collect::ImplicitConversionSequence
Collect::build_cpp_overload_nonreference_conversion_sequence(
    Expr* arg,
    QualType from,
    QualType to,
    bool allow_user_defined) {
    ImplicitConversionSequence seq;
    seq.to = to;

    QualType from_for_conversion = remove_reference(from);
    seq.from = from_for_conversion;
    if (!from_for_conversion) {
        seq.kind = ConversionSequenceKind::Failed;
        seq.rank = ConversionSequenceRank::NoMatch;
        seq.detail_kind = ConversionSequenceDetailKind::None;
        seq.viable = false;
        seq.note = "argument expression has invalid source type";
        return seq;
    }

    auto from_canonical = desugar_type(from_for_conversion, ast_ctx_.get());
    auto to_canonical = desugar_type(to, ast_ctx_.get());
    auto from_kind = from_canonical ? from_canonical->kind : TypeKind::Other;
    auto to_kind = to_canonical ? to_canonical->kind : TypeKind::Other;
    bool from_is_nullptr = is_nullptr_type(from_for_conversion, ast_ctx_.get());
    bool to_is_nullptr = is_nullptr_type(to, ast_ctx_.get());

    bool same_qualified_type =
        from_for_conversion.equals_qualified(to) ||
        (from_canonical &&
         to_canonical &&
         from_canonical.equals_qualified(to_canonical)) ||
        types_equivalent_after_template_argument_canonicalization(
            from_for_conversion,
            to,
            ast_ctx_.get(),
            /*ignore_top_level_qualifiers=*/false);
    if (same_qualified_type) {
        seq.kind = ConversionSequenceKind::Identity;
        seq.rank = ConversionSequenceRank::ExactMatch;
        return seq;
    }
    bool same_unqualified_type =
        from_for_conversion.equals_unqualified(to) ||
        (from_canonical &&
         to_canonical &&
         from_canonical.equals_unqualified(to_canonical)) ||
        types_equivalent_after_template_argument_canonicalization(
            from_for_conversion,
            to,
            ast_ctx_.get(),
            /*ignore_top_level_qualifiers=*/true);
    if (same_unqualified_type) {
        seq.kind = ConversionSequenceKind::Qualification;
        seq.rank = ConversionSequenceRank::ExactMatch;
        seq.exact_subrank = qualification_conversion_exact_subrank(
            from_for_conversion,
            to,
            ast_ctx_.get());
        return seq;
    }

    if (from_kind == TypeKind::Array && to_kind == TypeKind::Pointer) {
        auto from_arr = from_canonical.as_shared<ArrayType>();
        auto to_ptr = to_canonical.as_shared<PointerType>();
        if (from_arr && to_ptr &&
            from_arr->element_type.equals_unqualified(to_ptr->pointed_type)) {
            seq.kind = ConversionSequenceKind::ArrayToPointer;
            seq.rank = ConversionSequenceRank::ExactMatch;
            return seq;
        }
    }

    if (from_kind == TypeKind::Function && to_kind == TypeKind::Pointer) {
        auto to_ptr = to_canonical.as_shared<PointerType>();
        if (to_ptr && to_ptr->pointed_type.equals_unqualified(from_canonical)) {
            seq.kind = ConversionSequenceKind::FunctionToPointer;
            seq.rank = ConversionSequenceRank::ExactMatch;
            return seq;
        }
    }

    auto to_builtin = to.as_shared<BuiltinType>();
    if (to_builtin &&
        to_builtin->builtin_kind == BuiltinTypes::Bool &&
        allows_condition_conversion(from_for_conversion, ast_ctx_.get())) {
        seq.kind = ConversionSequenceKind::Numeric;
        seq.rank = ConversionSequenceRank::Conversion;
        return seq;
    }

    if (from_is_nullptr && is_null_pointer_like_type(to, ast_ctx_.get()) && !to_is_nullptr) {
        seq.kind = ConversionSequenceKind::Pointer;
        seq.rank = ConversionSequenceRank::Conversion;
        seq.detail_kind = ConversionSequenceDetailKind::NullPointerConstant;
        return seq;
    }
    if (to_is_nullptr && is_null_pointer_constant_expr(arg)) {
        seq.kind = ConversionSequenceKind::Pointer;
        seq.rank = ConversionSequenceRank::Conversion;
        seq.detail_kind = ConversionSequenceDetailKind::NullPointerConstant;
        return seq;
    }

    if (to_kind == TypeKind::Pointer && is_null_pointer_constant_expr(arg)) {
        seq.kind = ConversionSequenceKind::Pointer;
        seq.rank = ConversionSequenceRank::Conversion;
        seq.detail_kind = ConversionSequenceDetailKind::NullPointerConstant;
        return seq;
    }
    if (to_kind == TypeKind::MemberPointer && is_null_pointer_constant_expr(arg)) {
        seq.kind = ConversionSequenceKind::Pointer;
        seq.rank = ConversionSequenceRank::Conversion;
        seq.detail_kind = ConversionSequenceDetailKind::NullPointerConstant;
        return seq;
    }
    if (to_kind == TypeKind::BlockPointer && is_null_pointer_constant_expr(arg)) {
        seq.kind = ConversionSequenceKind::Pointer;
        seq.rank = ConversionSequenceRank::Conversion;
        seq.detail_kind = ConversionSequenceDetailKind::NullPointerConstant;
        return seq;
    }

    if (from_kind == TypeKind::Pointer && to_kind == TypeKind::Pointer) {
        auto from_ptr = from_canonical.as_shared<PointerType>();
        auto to_ptr = to_canonical.as_shared<PointerType>();
        if (from_ptr && to_ptr) {
            if (has_qualification_preserving_match(
                    from_ptr->pointed_type, to_ptr->pointed_type)) {
                seq.kind = from_ptr->pointed_type.equals_qualified(to_ptr->pointed_type)
                    ? ConversionSequenceKind::Identity
                    : ConversionSequenceKind::Qualification;
                seq.rank = ConversionSequenceRank::ExactMatch;
                if (seq.kind == ConversionSequenceKind::Qualification) {
                    seq.exact_subrank = qualification_conversion_exact_subrank(
                        from_ptr->pointed_type,
                        to_ptr->pointed_type,
                        ast_ctx_.get());
                }
                return seq;
            }
            bool to_void = to_ptr->pointed_type && to_ptr->pointed_type->isVoid();
            bool from_object_pointer = from_ptr->pointed_type &&
                from_ptr->pointed_type->kind != TypeKind::Function;
            if (to_void &&
                from_object_pointer &&
                to_ptr->pointed_type.has_all_qualifiers_of(from_ptr->pointed_type)) {
                seq.kind = ConversionSequenceKind::Pointer;
                seq.rank = ConversionSequenceRank::Conversion;
                return seq;
            }
            if (can_convert_derived_to_base_object(
                    from_ptr->pointed_type, to_ptr->pointed_type)) {
                seq.kind = ConversionSequenceKind::Pointer;
                seq.rank = ConversionSequenceRank::Conversion;
                return seq;
            }
        }
    }

    if (from_kind == TypeKind::BlockPointer && to_kind == TypeKind::BlockPointer) {
        auto from_block = from_canonical.as_shared<BlockPointerType>();
        auto to_block = to_canonical.as_shared<BlockPointerType>();
        if (from_block && to_block &&
            has_qualification_preserving_match(
                from_block->pointed_type, to_block->pointed_type)) {
            seq.kind = from_block->pointed_type.equals_qualified(to_block->pointed_type)
                ? ConversionSequenceKind::Identity
                : ConversionSequenceKind::Qualification;
            seq.rank = ConversionSequenceRank::ExactMatch;
            if (seq.kind == ConversionSequenceKind::Qualification) {
                seq.exact_subrank = qualification_conversion_exact_subrank(
                    from_block->pointed_type,
                    to_block->pointed_type,
                    ast_ctx_.get());
            }
            return seq;
        }
    }

    if (from_kind == TypeKind::MemberPointer && to_kind == TypeKind::MemberPointer) {
        if (from_for_conversion.equals_qualified(to)) {
            seq.kind = ConversionSequenceKind::Identity;
            seq.rank = ConversionSequenceRank::ExactMatch;
            return seq;
        }
        if (member_pointer_convertible_to(from_for_conversion, to)) {
            seq.kind = from_for_conversion.equals_unqualified(to)
                ? ConversionSequenceKind::Qualification
                : ConversionSequenceKind::Pointer;
            seq.rank = ConversionSequenceRank::Conversion;
            seq.detail_kind = ConversionSequenceDetailKind::MemberPointer;
            return seq;
        }
    }

    if ((is_arithmetic_adjacent(from_for_conversion, ast_ctx_.get()) &&
         is_arithmetic_adjacent(to, ast_ctx_.get())) ||
        from_for_conversion->isComplex() || to->isComplex()) {
        bool is_promotion = false;
        auto from_builtin = from_for_conversion.as_shared<BuiltinType>();
        if (from_builtin && to_builtin &&
            from_builtin->builtin_kind == BuiltinTypes::Float &&
            to_builtin->builtin_kind == BuiltinTypes::Double) {
            is_promotion = true;
        } else if (allows_integral_promotion(from_for_conversion, ast_ctx_.get())) {
            auto promoted = integer_promotion_type(from_for_conversion);
            is_promotion = promoted.equals_qualified(to);
        }
        seq.kind = ConversionSequenceKind::Numeric;
        seq.rank = is_promotion
            ? ConversionSequenceRank::Promotion
            : ConversionSequenceRank::Conversion;
        return seq;
    }

    if (allow_user_defined) {
        auto conversion_match = select_cpp_user_defined_conversion(
            arg, to, /*allow_explicit_constructors=*/false);
        if (conversion_match.has_value()) {
            seq.kind = ConversionSequenceKind::UserDefined;
            seq.rank = ConversionSequenceRank::Conversion;
            seq.detail_kind =
                conversion_match->kind ==
                        CppUserDefinedConversionKind::LambdaFunctionPointer
                    ? ConversionSequenceDetailKind::LambdaFunctionPointer
                    : ConversionSequenceDetailKind::None;
            seq.note = "user-defined conversion sequence";
            return seq;
        }
    }

    seq.kind = ConversionSequenceKind::Failed;
    seq.rank = ConversionSequenceRank::NoMatch;
    seq.detail_kind = ConversionSequenceDetailKind::None;
    seq.viable = false;
    seq.note = "no C++ overload conversion sequence";
    return seq;
}
