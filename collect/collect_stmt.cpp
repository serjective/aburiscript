#include "collect.h"
#include "collect_internal.h"
#include "../ast/expr_clone.h"
#include "../helpers/auto_type_utils.h"
#include <atomic>
#include <cctype>

using namespace collect_internal;

namespace {
bool constraint_uses_memory_operand(const std::string& constraint) {
    return constraint.find('m') != std::string::npos ||
           constraint.find('Q') != std::string::npos;
}

const BlockExpr* returned_block_literal_expr(Expr* expr) {
    expr = Collect::strip_implicit_casts(expr);
    return dyn_cast<BlockExpr>(expr);
}

uint64_t next_cpp_range_for_id() {
    static std::atomic<uint64_t> counter{0};
    return counter.fetch_add(1, std::memory_order_relaxed) + 1;
}

std::shared_ptr<Symbol> make_cpp_range_for_hidden_symbol(
    uint64_t loop_id,
    const std::string& suffix,
    QualType type) {
    std::string name =
        "__aburi_range_for_" + std::to_string(loop_id) + "_" + suffix;
    auto sym = std::make_shared<Symbol>(
        name,
        SymbolKind::VARIABLE,
        std::move(type),
        StorageClass::NONE);
    sym->uid = name;
    return sym;
}

bool is_same_type_object_prvalue_return(
    const Collect& collect,
    QualType return_type,
    Expr* expr,
    const ASTContext* ast_ctx) {
    if (!return_type || !expr) {
        return false;
    }
    QualType expr_type = expr->get_type();
    if (!expr_type) {
        return false;
    }

    QualType canonical_return =
        remove_reference_and_desugar(return_type, ast_ctx);
    QualType canonical_expr =
        remove_reference_and_desugar(expr_type, ast_ctx);
    if (!canonical_return ||
        !canonical_expr ||
        canonical_return->kind != TypeKind::Object ||
        canonical_expr->kind != TypeKind::Object ||
        !canonical_expr.equals_unqualified(canonical_return)) {
        return false;
    }

    return collect.classify_value_category(expr) ==
           Collect::ValueCategory::PRValue;
}
}

std::unique_ptr<InitListExpr> Collect::collect_initializer_list_expression(SrcLoc loc) const {

    return collect_make<InitListExpr>(loc);
}


std::unique_ptr<Stmt> Collect::collect_empty_statement(SrcLoc loc) const {

    return collect_make<EmptyStmt>(loc);
}


std::unique_ptr<Stmt> Collect::collect_expression_statement(std::unique_ptr<Expr> expr, SrcLoc loc) const {

    expr = collect_apply_standard_conversions(std::move(expr), ExprUseContext::ExpressionStatement);
    if (expr) {
        expr->location = loc;
    }
    return expr;
}


std::unique_ptr<Stmt> Collect::collect_error_statement(const std::string& message, SrcLoc loc) const {

    return collect_make<ErrorStmt>(message, loc);
}


std::unique_ptr<Decl> Collect::collect_error_declaration(const std::string& message, SrcLoc loc) const {

    return collect_make<ErrorDecl>(message, loc);
}


std::unique_ptr<Decl> Collect::collect_file_scope_asm_declaration(std::string asm_text, SrcLoc loc) const {

    return collect_make<FileScopeAsmDecl>(std::move(asm_text), loc);
}


std::unique_ptr<Stmt> Collect::collect_asm_statement(std::string asm_template, bool is_volatile, bool is_inline, bool is_goto, bool has_colon, std::vector<AsmOperand> outputs, std::vector<AsmOperand> inputs, std::vector<std::string> clobbers, std::vector<std::string> goto_labels, SrcLoc loc) {
    std::unordered_set<std::string> symbolic_names;
    for (size_t i = 0; i < outputs.size(); ++i) {
        auto& out = outputs[i];
        if (out.constraint.empty() ||
            (out.constraint[0] != '=' && out.constraint[0] != '+')) {
            report_error("asm output constraint must start with '=' or '+'", out.loc);
        }
        if (!is_modifiable_lvalue(out.expr.get())) {
            report_error("asm output operand must be an lvalue", out.loc);
        }
        if (!out.symbolic_name.empty()) {
            if (!symbolic_names.insert(out.symbolic_name).second) {
                report_error("duplicate asm operand symbolic name '" + out.symbolic_name + "'", out.loc);
            }
        }
    }
    auto stmt = collect_make<AsmStmt>(
        std::move(asm_template), is_volatile, is_inline, is_goto, has_colon, loc);
    for (auto& in : inputs) {
        if (!in.constraint.empty() &&
            (in.constraint[0] == '=' || in.constraint[0] == '+')) {
            report_error("asm input constraint cannot start with '=' or '+'", in.loc);
        }
        if (!in.constraint.empty() && std::isdigit(static_cast<unsigned char>(in.constraint[0]))) {
            int tied_index = in.constraint[0] - '0';
            if (tied_index < 0 || tied_index >= static_cast<int>(outputs.size())) {
                report_error("asm digit constraint out of range", in.loc);
            }
        }
        if (!in.symbolic_name.empty()) {
            if (!symbolic_names.insert(in.symbolic_name).second) {
                report_error("duplicate asm operand symbolic name '" + in.symbolic_name + "'", in.loc);
            }
        }
        if (!constraint_uses_memory_operand(in.constraint)) {
            in.expr = collect_apply_standard_conversions(std::move(in.expr), ExprUseContext::CallArgument);
        }
    }
    stmt->output_operands = std::move(outputs);
    stmt->input_operands = std::move(inputs);
    stmt->clobbers = std::move(clobbers);
    stmt->goto_labels = std::move(goto_labels);
    if (is_goto) {
        if (stmt->goto_labels.empty()) {
            report_error("asm goto requires at least one goto label", loc);
        }
        for (const auto& label : stmt->goto_labels) {
            collect_register_label_reference(label, loc);
        }
    }
    return stmt;
}


std::unique_ptr<Stmt> Collect::collect_break_statement(SrcLoc loc) const {

    if (session_.func_state_.loop_depth <= 0 && session_.func_state_.switch_depth <= 0) {
        report_error("break statement not in loop or switch statement", loc);
    }
    return collect_make<BreakStmt>(loc);
}


std::unique_ptr<Stmt> Collect::collect_continue_statement(SrcLoc loc) const {

    if (session_.func_state_.loop_depth <= 0) {
        report_error("continue statement not in loop statement", loc);
    }
    return collect_make<ContinueStmt>(loc);
}

bool Collect::should_defer_cpp_conversion_check(const Expr* expr,
                                                QualType target_type) const {
    if (!lang_opts_.is_cxx_mode() || !expr) {
        return false;
    }

    auto* mutable_expr = const_cast<Expr*>(expr);
    QualType expr_type = mutable_expr->get_type();
    return !expr_type ||
           expression_depends_on_template_parameters(expr) ||
           type_depends_on_template_parameters(target_type, ast_ctx_.get()) ||
           type_depends_on_template_parameters(expr_type, ast_ctx_.get()) ||
           (target_type &&
            contains_deferred_semantic_type(target_type.get_shared())) ||
           (expr_type &&
            contains_deferred_semantic_type(expr_type.get_shared())) ||
           (target_type &&
            auto_type_utils::has_cxx_auto_type(target_type.get_shared())) ||
           (expr_type &&
            auto_type_utils::has_cxx_auto_type(expr_type.get_shared()));
}


std::unique_ptr<Stmt> Collect::collect_case_statement(std::unique_ptr<Expr> const_expr, std::unique_ptr<Expr> range_end, std::unique_ptr<Stmt> stmt, SrcLoc loc) {

    if (session_.func_state_.switch_depth <= 0) {
        report_error("case statement not in switch statement", loc);
        const_expr = collect_apply_standard_conversions(std::move(const_expr), ExprUseContext::RValue);
        if (range_end) {
            range_end = collect_apply_standard_conversions(std::move(range_end), ExprUseContext::RValue);
            return collect_make<CaseStmt>(std::move(const_expr), std::move(range_end), std::move(stmt), loc);
        }
        return collect_make<CaseStmt>(std::move(const_expr), std::move(stmt), loc);
    }

    const SwitchContext* switch_ctx = nullptr;
    if (!session_.func_state_.switch_context_stack.empty()) {
        switch_ctx = &session_.func_state_.switch_context_stack.back();
    }

    const_expr = collect_apply_standard_conversions(std::move(const_expr), ExprUseContext::RValue);
    if (switch_ctx && switch_ctx->switch_type &&
        const_expr && const_expr->get_type() &&
        !const_expr->get_type()->equals(*switch_ctx->switch_type.get_shared())) {
        const_expr = collect_make<ImplicitCast>(std::move(const_expr), switch_ctx->switch_type);
    }

    auto low_val_opt = const_expr
        ? try_evaluate_with_consteval_compat(const_expr.get(), ConstEvalMode::c_ice())
        : std::nullopt;
    if (!low_val_opt.has_value()) {
        report_error("case expression is not a constant integer expression", loc);
    }

    if (range_end) {
        range_end = collect_apply_standard_conversions(std::move(range_end), ExprUseContext::RValue);
        if (switch_ctx && switch_ctx->switch_type &&
            range_end && range_end->get_type() &&
            !range_end->get_type()->equals(*switch_ctx->switch_type.get_shared())) {
            range_end = collect_make<ImplicitCast>(std::move(range_end), switch_ctx->switch_type);
        }
        auto high_val_opt = range_end
            ? try_evaluate_with_consteval_compat(range_end.get(), ConstEvalMode::c_ice())
            : std::nullopt;
        if (!high_val_opt.has_value()) {
            report_error("case range endpoint is not a constant integer expression", loc);
        }
        if (low_val_opt.has_value() && high_val_opt.has_value()) {
            int64_t low_val = *low_val_opt;
            int64_t high_val = *high_val_opt;
            bool switch_unsigned = switch_ctx && switch_ctx->switch_type &&
                switch_ctx->switch_type->isUnsigned();
            bool empty_range = false;
            bool range_too_large = false;
            if (switch_unsigned) {
                uint64_t low_u = static_cast<uint64_t>(low_val);
                uint64_t high_u = static_cast<uint64_t>(high_val);
                empty_range = low_u > high_u;
                range_too_large = !empty_range && (high_u - low_u) > 65536ULL;
            } else {
                empty_range = low_val > high_val;
                range_too_large = !empty_range && (high_val - low_val) > 65536LL;
            }
            if (empty_range) {
                report_error("empty range specified", loc);
            } else {
                if (!range_too_large && !session_.func_state_.switch_context_stack.empty()) {
                    materialize_tentative_snapshot_if_needed();
                    auto& mutable_ctx = session_.func_state_.switch_context_stack.back();
                    for (int64_t v = low_val; v <= high_val; ++v) {
                        if (mutable_ctx.case_values.contains(v)) {
                            report_error("duplicate case value", loc);
                            break;
                        }
                        mutable_ctx.case_values.insert(v);
                        if (v == high_val) {
                            break;
                        }
                    }
                }
            }
        }
        return collect_make<CaseStmt>(std::move(const_expr), std::move(range_end), std::move(stmt), loc);
    }

    if (low_val_opt.has_value() && !session_.func_state_.switch_context_stack.empty()) {
        materialize_tentative_snapshot_if_needed();
        auto& mutable_ctx = session_.func_state_.switch_context_stack.back();
        int64_t low_val = *low_val_opt;
        if (mutable_ctx.case_values.contains(low_val)) {
            report_error("duplicate case value", loc);
        } else {
            mutable_ctx.case_values.insert(low_val);
        }
    }
    return collect_make<CaseStmt>(std::move(const_expr), std::move(stmt), loc);
}


std::unique_ptr<Stmt> Collect::collect_default_statement(std::unique_ptr<Stmt> stmt, SrcLoc loc) {

    if (session_.func_state_.switch_depth <= 0) {
        report_error("default statement not in switch statement", loc);
        return collect_make<DefaultStmt>(std::move(stmt), loc);
    }
    if (!session_.func_state_.switch_context_stack.empty()) {
        materialize_tentative_snapshot_if_needed();
        auto& switch_ctx = session_.func_state_.switch_context_stack.back();
        if (switch_ctx.has_default) {
            report_error("multiple default labels in one switch", loc);
        } else {
            switch_ctx.has_default = true;
        }
    }
    return collect_make<DefaultStmt>(std::move(stmt), loc);
}


CppIfConditionInfo Collect::collect_if_condition(std::unique_ptr<Expr> condition,
                                                 IfStatementKind statement_kind,
                                                 SrcLoc loc,
                                                 bool defer_unmaterialized_constexpr_calls) const {
    CppIfConditionInfo info;
    info.condition = collect_condition_expression(std::move(condition), loc, "if");
    if (statement_kind != IfStatementKind::Constexpr || !info.condition) {
        return info;
    }

    info.is_value_dependent =
        expression_is_value_dependent_for_constant_evaluation(
            info.condition.get(),
            defer_unmaterialized_constexpr_calls);
    if (info.is_value_dependent) {
        return info;
    }

    ConstEvalResult eval = evaluate_constant_expression_demand(
        info.condition.get(),
        ConstEvalMode::cpp_core_constant_expression(),
        loc);
    if (eval.status != ConstEvalStatus::Constant ||
        !eval.int_value.has_value()) {
        report_error(
            "constexpr if condition is not a constant expression",
            loc);
        return info;
    }
    info.constexpr_value = *eval.int_value != 0;
    return info;
}

std::unique_ptr<Stmt> Collect::collect_if_statement(std::unique_ptr<Expr> condition, std::unique_ptr<Stmt> then_stmt, std::unique_ptr<Stmt> else_stmt, SrcLoc loc) const {

    auto condition_info =
        collect_if_condition(std::move(condition), IfStatementKind::Runtime, loc);
    condition = std::move(condition_info.condition);
    if (auto* binop = dyn_cast<BinaryOperation>(condition.get())) {
        if (binop->bop == BinOpTypes::ASSIGN) {
            report_warning("using '=' in condition; did you mean '=='?", binop->location);
        }
    }
    return collect_make<IfStmt>(std::move(condition), std::move(then_stmt), std::move(else_stmt), loc);
}

std::unique_ptr<Stmt> Collect::collect_if_statement(
    std::unique_ptr<Stmt> init_stmt,
    std::unique_ptr<Expr> condition,
    std::unique_ptr<Stmt> then_stmt,
    std::unique_ptr<Stmt> else_stmt,
    IfStatementKind statement_kind,
    std::shared_ptr<Scope> scope,
    std::optional<bool> constexpr_condition_value,
    SrcLoc loc) const {

    if (auto* binop = dyn_cast<BinaryOperation>(condition.get())) {
        if (statement_kind == IfStatementKind::Runtime &&
            binop->bop == BinOpTypes::ASSIGN) {
            report_warning("using '=' in condition; did you mean '=='?", binop->location);
        }
    }
    return collect_make<IfStmt>(
        std::move(condition),
        std::move(then_stmt),
        std::move(else_stmt),
        loc,
        statement_kind,
        std::move(init_stmt),
        std::move(scope),
        constexpr_condition_value);
}

void Collect::collect_enter_constexpr_if_branch(
    CppConstexprIfBranchState state) {
    session_.func_state_.constexpr_if_branch_stack.push_back(state);
}

void Collect::collect_leave_constexpr_if_branch() {
    if (!session_.func_state_.constexpr_if_branch_stack.empty()) {
        session_.func_state_.constexpr_if_branch_stack.pop_back();
    }
}


std::unique_ptr<Expr> Collect::collect_switch_condition(std::unique_ptr<Expr> condition, SrcLoc loc) {

    condition = collect_apply_standard_conversions(std::move(condition), ExprUseContext::Condition);
    if (!condition) {
        return nullptr;
    }
    auto cond_type = condition->get_type();
    if (!cond_type) {
        report_error("switch condition has unknown type", loc);
        return condition;
    }
    if (!is_integer_or_enum_type(cond_type, ast_ctx_.get())) {
        report_error("statement requires expression of integer type ('" + cond_type.to_string() + "' invalid)", loc);
        return condition;
    }
    QualType promoted = is_scoped_enum_type(cond_type, ast_ctx_.get())
        ? cond_type
        : integer_promotion_type(cond_type);
    if (promoted && !cond_type->equals(*promoted.get_shared())) {
        condition = collect_make<ImplicitCast>(std::move(condition), promoted);
    }
    if (!session_.func_state_.switch_context_stack.empty()) {
        materialize_tentative_snapshot_if_needed();
        session_.func_state_.switch_context_stack.back().switch_type = promoted ? promoted : cond_type;
    }
    return condition;
}


std::unique_ptr<Stmt> Collect::collect_switch_statement(std::unique_ptr<Expr> condition, std::unique_ptr<Stmt> stmt, SrcLoc loc) const {

    return collect_make<SwitchStmt>(std::move(condition), std::move(stmt), loc);
}


std::unique_ptr<Stmt> Collect::collect_while_statement(std::unique_ptr<Expr> condition, std::unique_ptr<Stmt> body_stmt, SrcLoc loc) const {

    condition = collect_condition_expression(std::move(condition), loc, "while");
    return collect_make<WhileStmt>(std::move(condition), std::move(body_stmt), loc);
}


std::unique_ptr<Stmt> Collect::collect_do_while_statement(std::unique_ptr<Expr> condition, std::unique_ptr<Stmt> body_stmt, SrcLoc loc) const {

    condition = collect_condition_expression(std::move(condition), loc, "do-while");
    return collect_make<DoWhileStmt>(std::move(condition), std::move(body_stmt), loc);
}


std::unique_ptr<Stmt> Collect::collect_for_statement(std::unique_ptr<Stmt> init, std::unique_ptr<Expr> condition, std::unique_ptr<Expr> action, std::unique_ptr<Stmt> body_stmt, std::shared_ptr<Scope> scope, SrcLoc loc) const {

    if (condition) {
        condition = collect_condition_expression(std::move(condition), loc, "for");
    }
    if (action) {
        action = collect_apply_standard_conversions(std::move(action), ExprUseContext::ExpressionStatement);
    }
    return collect_make<ForStmt>(std::move(init),
        std::move(condition),
        std::move(action),
        std::move(body_stmt),
        std::move(scope),
        loc);
}

std::unique_ptr<CppRangeForStmt> Collect::collect_cpp_range_for_statement(
    std::unique_ptr<Stmt> init_statement,
    CppRangeForDeclarationInfo range_declaration,
    std::unique_ptr<Expr> range_initializer,
    std::unique_ptr<Stmt> body_stmt,
    std::shared_ptr<Scope> scope,
    SrcLoc loc) {
    auto fallback_int = QualType(ast_ctx_->type_ctx->get_builtin(BuiltinTypes::Int));
    auto fallback_pointer =
        QualType(std::make_shared<PointerType>(fallback_int));
    auto var_ref = [&](const std::shared_ptr<Symbol>& sym) {
        return collect_make<VarRef>(sym, loc);
    };
    auto expr_type_or_fallback = [&](const std::unique_ptr<Expr>& expr) {
        if (expr && expr->get_type()) {
            return expr->get_type();
        }
        return fallback_pointer;
    };

    if (range_declaration.name.empty()) {
        report_error("range-for declaration requires a variable name", loc);
    }
    if (range_declaration.storage_class != StorageClass::NONE) {
        report_error("range-for declaration cannot use a storage class specifier",
                     range_declaration.loc);
        range_declaration.storage_class = StorageClass::NONE;
    }
    if (range_declaration.is_consteval) {
        report_error("'consteval' can only be applied to function declarations",
                     range_declaration.loc);
    }
    if (range_declaration.is_thread_local) {
        report_error("range-for declaration cannot be thread-local",
                     range_declaration.loc);
    }
    if (range_declaration.is_block_byref) {
        report_error("range-for declaration cannot use '__block'",
                     range_declaration.loc);
    }

    if (!range_initializer || !range_initializer->get_type()) {
        report_error("range-for initializer has no type", loc);
        range_initializer =
            collect_make<ErrorExpr>("invalid range-for initializer", loc);
    }

    QualType range_initializer_type =
        range_initializer && range_initializer->get_type()
            ? range_initializer->get_type()
            : fallback_int;
    ReferenceKind range_ref_kind =
        classify_value_category(range_initializer.get()) == ValueCategory::LValue
            ? ReferenceKind::LValue
            : ReferenceKind::RValue;
    QualType range_ref_type =
        make_reference_type(range_initializer_type, range_ref_kind);

    const uint64_t loop_id = next_cpp_range_for_id();
    auto range_sym =
        make_cpp_range_for_hidden_symbol(loop_id, "range", range_ref_type);
    auto begin_sym =
        make_cpp_range_for_hidden_symbol(loop_id, "begin", fallback_pointer);
    auto end_sym =
        make_cpp_range_for_hidden_symbol(loop_id, "end", fallback_pointer);

    VariableDeclFlags hidden_flags;
    auto range_variable = collect_variable_declaration(
        range_ref_type,
        range_sym->name,
        std::move(range_initializer),
        range_sym,
        StorageClass::NONE,
        hidden_flags,
        loc);

    std::unique_ptr<Expr> begin_expr;
    std::unique_ptr<Expr> end_expr;
    QualType range_object_type =
        desugar_type(remove_reference(range_ref_type, ast_ctx_.get()),
                     ast_ctx_.get());
    auto array_type = range_object_type.as_shared<ArrayType>();
    if (array_type) {
        auto zero = collect_integer_literal(
            "0",
            ast_ctx_->type_ctx->get_builtin(BuiltinTypes::Int),
            loc);
        auto first_element =
            collect_array_subscript(var_ref(range_sym), std::move(zero), loc);
        begin_expr = collect_unary_operation(
            UnaryOpTypes::ADDRESS_OF,
            std::move(first_element),
            loc);
        begin_sym->type = expr_type_or_fallback(begin_expr);

        std::unique_ptr<Expr> size_expr;
        if (array_type->size_kind == ArraySizeKind::Constant &&
            array_type->size.has_value()) {
            size_expr = collect_integer_literal(
                std::to_string(*array_type->size),
                ast_ctx_->type_ctx->get_builtin(BuiltinTypes::Int),
                loc);
        } else if (array_type->size_kind == ArraySizeKind::Variable &&
                   array_type->size_expr) {
            std::string clone_error;
            size_expr = clone_expr_tree(
                array_type->size_expr.get(),
                ast_ctx_.get(),
                &clone_error);
            if (!size_expr) {
                report_error(
                    "range-for failed to clone variable array bound: " +
                        clone_error,
                    loc);
                size_expr = collect_make<ErrorExpr>(
                    "invalid range-for array bound", loc);
            }
        } else {
            report_error("range-for over incomplete array type is not allowed",
                         loc);
            size_expr =
                collect_make<ErrorExpr>("invalid range-for array bound", loc);
        }

        end_expr = collect_binary_operation(
            var_ref(begin_sym),
            std::move(size_expr),
            BinOpTypes::ADD,
            loc);
    } else if (auto record_type = range_object_type.as_shared<ObjectType>();
               record_type &&
               lookup_record_member_name(record_type.get(), "begin")
                   .has_member_match() &&
               lookup_record_member_name(record_type.get(), "end")
                   .has_member_match()) {
        auto begin_member = collect_member_expression(
            var_ref(range_sym),
            "begin",
            false,
            loc,
            true);
        begin_expr = collect_function_call(
            std::move(begin_member),
            std::vector<std::unique_ptr<Expr>>{},
            loc);
        begin_sym->type = expr_type_or_fallback(begin_expr);

        auto end_member = collect_member_expression(
            var_ref(range_sym),
            "end",
            false,
            loc,
            true);
        end_expr = collect_function_call(
            std::move(end_member),
            std::vector<std::unique_ptr<Expr>>{},
            loc);
    } else {
        std::vector<std::unique_ptr<Expr>> begin_args;
        begin_args.push_back(var_ref(range_sym));
        begin_expr = collect_function_call(
            collect_make<VarRef>("begin", loc),
            std::move(begin_args),
            loc);
        begin_sym->type = expr_type_or_fallback(begin_expr);

        std::vector<std::unique_ptr<Expr>> end_args;
        end_args.push_back(var_ref(range_sym));
        end_expr = collect_function_call(
            collect_make<VarRef>("end", loc),
            std::move(end_args),
            loc);
    }

    end_sym->type = expr_type_or_fallback(end_expr);
    auto begin_variable = collect_variable_declaration(
        begin_sym->type,
        begin_sym->name,
        std::move(begin_expr),
        begin_sym,
        StorageClass::NONE,
        hidden_flags,
        loc);
    auto end_variable = collect_variable_declaration(
        end_sym->type,
        end_sym->name,
        std::move(end_expr),
        end_sym,
        StorageClass::NONE,
        hidden_flags,
        loc);

    auto condition = collect_binary_operation(
        var_ref(begin_sym),
        var_ref(end_sym),
        BinOpTypes::NOT_EQUAL,
        loc);
    condition = collect_condition_expression(std::move(condition), loc, "range-for");

    auto increment = collect_unary_operation(
        UnaryOpTypes::INCREMENT_PREFIX,
        var_ref(begin_sym),
        loc);
    increment = collect_apply_standard_conversions(
        std::move(increment),
        ExprUseContext::ExpressionStatement);

    auto loop_sym = collect_declare_variable_symbol(
        range_declaration.name,
        range_declaration.declared_type,
        range_declaration.storage_class,
        range_declaration.is_constexpr,
        range_declaration.loc);
    auto loop_init = collect_unary_operation(
        UnaryOpTypes::DEREFERENCE,
        var_ref(begin_sym),
        range_declaration.loc);
    VariableDeclFlags loop_flags;
    loop_flags.is_constexpr = range_declaration.is_constexpr;
    auto loop_variable = collect_variable_declaration(
        range_declaration.declared_type,
        range_declaration.name,
        std::move(loop_init),
        loop_sym,
        range_declaration.storage_class,
        loop_flags,
        range_declaration.loc);

    return collect_make<CppRangeForStmt>(
        std::move(init_statement),
        std::move(range_declaration.side_decls),
        std::move(range_variable),
        std::move(begin_variable),
        std::move(end_variable),
        std::move(loop_variable),
        std::move(condition),
        std::move(increment),
        std::move(body_stmt),
        std::move(scope),
        loc);
}


std::unique_ptr<Stmt> Collect::collect_goto_statement(const std::string& name, SrcLoc loc) {

    collect_register_label_reference(name, loc);
    return collect_make<GoToStmt>(name, loc);
}


std::unique_ptr<Stmt> Collect::collect_computed_goto_statement(std::unique_ptr<Expr> expr, SrcLoc loc) const {

    expr = collect_apply_standard_conversions(std::move(expr), ExprUseContext::RValue);
    auto expr_type = expr ? expr->get_type() : QualType();
    auto expr_kind = canonical_type_kind(expr_type, ast_ctx_.get());
    if (expr_type && expr_kind != TypeKind::Pointer &&
        expr_kind != TypeKind::BlockPointer) {
        report_error("computed goto requires pointer expression", loc);
    }
    return collect_make<ComputedGotoStmt>(std::move(expr), loc);
}


std::unique_ptr<Stmt> Collect::collect_labeled_statement(const std::string& name, std::unique_ptr<Stmt> stmt, SrcLoc loc) {

    collect_register_label_definition(name, loc);
    return collect_make<LabeledStmt>(name, std::move(stmt), loc);
}


std::unique_ptr<Stmt> Collect::collect_return_statement(std::unique_ptr<Expr> expr, SrcLoc loc, QualType expected_return_type) {

    bool suppress_return_for_constexpr_if =
        current_constexpr_if_branch_suppresses_returns();
    if (session_.func_state_.in_function &&
        !suppress_return_for_constexpr_if) {
        session_.func_state_.current_function_has_return_statement = true;
    }

    QualType return_type = expected_return_type ? expected_return_type : session_.func_state_.current_function_return_type;
    if (expr) {
        if (const auto* block = returned_block_literal_expr(expr.get())) {
            if (!block->semantic_info.captures.empty()) {
                report_error("returning block that lives on the local stack", loc);
            }
        }
    }
    if (session_.func_state_.current_function_has_cxx_auto_return_deduction &&
        session_.func_state_.current_function_cxx_auto_return_pattern) {
        if (suppress_return_for_constexpr_if) {
            if (current_constexpr_if_branch_state() ==
                CppConstexprIfBranchState::Deferred) {
                session_.func_state_.current_function_has_return_statement = true;
                session_.func_state_
                    .current_function_has_deferred_cxx_auto_return_deduction = true;
                session_.func_state_.current_function_return_type =
                    session_.func_state_.current_function_cxx_auto_return_pattern;
                if (auto func_ty =
                        session_.func_state_.current_function_type
                            .as_shared<FunctionType>()) {
                    func_ty->ret_type =
                        session_.func_state_.current_function_return_type;
                }
            }
            return collect_make<ReturnStmt>(std::move(expr), loc);
        }
        bool deferred_template_dependent_return = false;
        auto deduce_auto_return_type = [&](const std::unique_ptr<Expr>& return_expr) -> QualType {
            QualType implicit_void(get_builtin_void());
            QualType fallback_return = implicit_void;
            auto fallback_raw = replace_auto_type(
                session_.func_state_.current_function_cxx_auto_return_pattern.get_shared(),
                implicit_void.get_shared());
            if (fallback_raw) {
                fallback_return = QualType(
                    fallback_raw,
                    session_.func_state_.current_function_cxx_auto_return_pattern.get_qualifiers());
            }

            QualType deduction_source_type = implicit_void;
            if (return_expr) {
                if (isa<InitListExpr>(return_expr.get())) {
                    report_error(
                        "C++ parser unsupported syntax: auto braced-init-list deduction",
                        loc);
                    return fallback_return;
                }
                deduction_source_type = return_expr->get_type();
                if (contains_deferred_semantic_type(deduction_source_type.get_shared())) {
                    deduction_source_type = resolve_typeof_types(deduction_source_type, loc);
                }
                if (!deduction_source_type) {
                    report_error(
                        "cannot deduce return type for function '" +
                            session_.func_state_.current_function_name +
                            "': return expression has no type",
                        loc);
                    return fallback_return;
                }
                if (expression_depends_on_template_parameters(return_expr.get()) ||
                    type_depends_on_template_parameters(
                        deduction_source_type,
                        ast_ctx_.get())) {
                    deferred_template_dependent_return = true;
                    return session_.func_state_.current_function_cxx_auto_return_pattern;
                }
            }

            auto deduced_placeholder = auto_type_utils::extract_auto_placeholder_replacement(
                session_.func_state_.current_function_cxx_auto_return_pattern,
                deduction_source_type);
            if (!deduced_placeholder.has_value() || !deduced_placeholder->get_shared()) {
                if (return_expr) {
                    report_error(
                        "cannot deduce return type '" +
                            session_.func_state_.current_function_cxx_auto_return_pattern.to_string() +
                            "' from return expression of type '" +
                            deduction_source_type.to_string() + "'",
                        loc);
                } else {
                    report_error(
                        "cannot deduce return type '" +
                            session_.func_state_.current_function_cxx_auto_return_pattern.to_string() +
                            "' for function '" + session_.func_state_.current_function_name +
                            "' from 'return;'",
                        loc);
                }
                return fallback_return;
            }

            auto deduced_raw =
                desugar_type(*deduced_placeholder, ast_ctx_.get()).get_shared();
            if (!deduced_raw ||
                auto_type_utils::auto_type_flavors_in(deduced_raw) != 0) {
                report_error(
                    "cannot deduce return type for function '" +
                        session_.func_state_.current_function_name +
                        "': unresolved auto placeholder in return deduction from expression type '" +
                        deduction_source_type.to_string() + "'",
                    loc);
                return fallback_return;
            }

            if (deduced_raw->kind == TypeKind::Array) {
                auto arr = dyn_cast_shared<ArrayType>(deduced_raw);
                deduced_raw = std::make_shared<PointerType>(arr->element_type);
            } else if (deduced_raw->kind == TypeKind::Function) {
                deduced_raw = std::make_shared<PointerType>(QualType(deduced_raw));
            }

            auto replaced_raw = replace_auto_type(
                session_.func_state_.current_function_cxx_auto_return_pattern.get_shared(),
                deduced_raw);
            if (!replaced_raw) {
                return fallback_return;
            }
            return QualType(
                replaced_raw,
                session_.func_state_.current_function_cxx_auto_return_pattern.get_qualifiers());
        };

        if (session_.func_state_.current_function_has_deferred_cxx_auto_return_deduction) {
            return_type = session_.func_state_.current_function_cxx_auto_return_pattern;
        } else {
            QualType deduced_return_type = deduce_auto_return_type(expr);
            if (deferred_template_dependent_return) {
                session_.func_state_.current_function_has_deferred_cxx_auto_return_deduction = true;
                session_.func_state_.current_function_return_type =
                    session_.func_state_.current_function_cxx_auto_return_pattern;
                if (auto func_ty = session_.func_state_.current_function_type.as_shared<FunctionType>()) {
                    func_ty->ret_type = session_.func_state_.current_function_return_type;
                }
            } else if (
                session_.func_state_.current_function_return_type &&
                !auto_type_utils::has_cxx_auto_type(
                    session_.func_state_.current_function_return_type.get_shared())) {
                if (!deduced_return_type.equals_qualified(
                        session_.func_state_.current_function_return_type)) {
                    report_error(
                        "inconsistent deduction for function return type 'auto': '" +
                            session_.func_state_.current_function_return_type.to_string() +
                            "' and then '" +
                            deduced_return_type.to_string() + "'",
                        loc);
                }
            } else {
                session_.func_state_.current_function_return_type = deduced_return_type;
                if (auto func_ty = session_.func_state_.current_function_type.as_shared<FunctionType>()) {
                    func_ty->ret_type = deduced_return_type;
                }
            }
            return_type = session_.func_state_.current_function_return_type;
        }
        if (session_.func_state_.current_function_has_deferred_cxx_auto_return_deduction &&
            return_type &&
            auto_type_utils::has_cxx_auto_type(return_type.get_shared())) {
            return collect_make<ReturnStmt>(std::move(expr), loc);
        }
    }

    if (canonical_type_kind(return_type, ast_ctx_.get()) == TypeKind::Function) {
        auto func_type =
            desugar_type(return_type, ast_ctx_.get()).as_shared<FunctionType>();
        if (func_type) {
            return_type = func_type->ret_type;
        }
    }
    if (!return_type) {
        return collect_make<ReturnStmt>(std::move(expr), loc);
    }
    if (return_type->isVoid()) {
        expr = nullptr;
        return collect_make<ReturnStmt>(nullptr, loc);
    }
    if (!expr) {
        bool gnu_mode = !lang_opts_.standard.empty() &&
            lang_opts_.standard.rfind("gnu", 0) == 0;
        if (gnu_mode || lang_opts_.implicit_function_declarations) {
            report_warning("non-void function should return a value", loc);
        } else {
            report_error("non-void function should return a value", loc);
        }
        return collect_make<ReturnStmt>(nullptr, loc);
    }

    if (isa<InitListExpr>(expr.get())) {
        expr = process_initializer_for_type(std::move(expr), return_type, loc);
    }

    if (should_defer_cpp_conversion_check(expr.get(), return_type)) {
        return collect_make<ReturnStmt>(std::move(expr), loc);
    }

    if (canonical_type_kind(return_type, ast_ctx_.get()) == TypeKind::Reference) {
        auto seq = build_cpp_overload_conversion_sequence(expr.get(), return_type);
        if (!seq.viable) {
            report_conversion_failure(
                "return expression",
                expr ? expr->get_type() : QualType(),
                return_type,
                loc);
        } else if (seq.kind == ConversionSequenceKind::UserDefined) {
            expr = build_cpp_user_defined_conversion_expr(
                std::move(expr), return_type, loc);
        }
        expr = collect_make<ImplicitCast>(std::move(expr), return_type);
        return collect_make<ReturnStmt>(std::move(expr), loc);
    }

    if (lang_opts_.is_cxx_mode() &&
        canonical_type_kind(return_type, ast_ctx_.get()) == TypeKind::Object &&
        expr) {
        auto return_record =
            desugar_type(return_type, ast_ctx_.get()).as_shared<ObjectType>();
        const ObjectDecl* return_record_decl = return_record
            ? dyn_cast<ObjectDecl>(return_record->get_decl())
            : nullptr;
        const RecordSemanticState* return_state = return_record_decl
            ? record_semantics_cache_lookup(return_record_decl)
            : nullptr;

        bool same_type_prvalue_return =
            is_same_type_object_prvalue_return(
                *this,
                return_type,
                expr.get(),
                ast_ctx_.get());
        if (return_state &&
            !same_type_prvalue_return &&
            !return_state->constructors.empty() &&
            return_state->definition_data.has_user_declared_constructor) {
            auto temp_decl = collect_variable_declaration(
                return_type,
                "__return_ctor_init_tmp",
                std::move(expr),
                nullptr,
                StorageClass::NONE,
                {false, false, false, false, false, false, true, true, false},
                loc);
            auto* temp_var = dyn_cast<VariableDecl>(temp_decl.get());
            if (!temp_var) {
                report_error(
                    "internal error: failed to build return object initialization",
                    loc);
                expr = collect_make<ErrorExpr>("invalid return initializer", loc);
            } else {
                expr = std::move(temp_var->init);
            }
            return collect_make<ReturnStmt>(std::move(expr), loc);
        }
    }

    if (lang_opts_.is_cxx_mode() && expr) {
        auto expr_type = expr->get_type();
        bool skip_conversion_check =
            should_defer_cpp_conversion_check(expr.get(), return_type);
        if (!skip_conversion_check) {
            auto seq = build_cpp_overload_conversion_sequence(expr.get(), return_type);
            if (!seq.viable) {
                report_error("no viable conversion from '" + expr_type.to_string() +
                                 "' to '" + return_type.to_string() + "'",
                             loc);
            } else if (seq.kind == ConversionSequenceKind::UserDefined) {
                expr = build_cpp_user_defined_conversion_expr(
                    std::move(expr), return_type, loc);
                expr = cast_if_needed(std::move(expr), return_type);
                return collect_make<ReturnStmt>(std::move(expr), loc);
            }
        }
    }

    expr = collect_apply_standard_conversions(std::move(expr), ExprUseContext::RValue);
    expr = cast_if_needed(std::move(expr), return_type);
    return collect_make<ReturnStmt>(std::move(expr), loc);
}

std::unique_ptr<Stmt> Collect::collect_cpp_try_statement(
    std::unique_ptr<Stmt> try_block,
    std::vector<CppCatchClause> handlers,
    SrcLoc loc) const {
    if (!try_block) {
        report_error("try statement requires a valid try block", loc);
    }
    if (handlers.empty()) {
        report_error("try statement requires at least one catch handler", loc);
    }

    bool saw_catch_all = false;
    for (size_t i = 0; i < handlers.size(); ++i) {
        if (!handlers[i].handler) {
            report_error("catch handler requires a compound statement body",
                handlers[i].location);
        }
        if (handlers[i].is_catch_all) {
            if (saw_catch_all) {
                report_error("duplicate catch-all handler", handlers[i].location);
            }
            if (i + 1 < handlers.size()) {
                report_error("catch-all handler must be the last handler",
                    handlers[i].location);
            }
            saw_catch_all = true;
            continue;
        }

        if (saw_catch_all) {
            report_error("catch-all handler must be the last handler",
                handlers[i].location);
        }
        if (!handlers[i].exception_type) {
            report_error("catch handler requires a valid exception declaration type",
                handlers[i].location);
            continue;
        }

        handlers[i].exception_type = decay_parameter_type(handlers[i].exception_type);
        if (handlers[i].exception_symbol) {
            handlers[i].exception_symbol->type = handlers[i].exception_type;
        }

        QualType catch_type =
            desugar_type(handlers[i].exception_type, ast_ctx_.get());
        if (!catch_type) {
            report_error("catch handler requires a valid exception declaration type",
                handlers[i].location);
            continue;
        }

        if (auto ref_type = catch_type.as_shared<ReferenceType>()) {
            if (ref_type->reference_kind == ReferenceKind::RValue) {
                report_error("cannot catch exceptions by rvalue reference",
                    handlers[i].location);
            }
            catch_type = desugar_type(ref_type->referred_type, ast_ctx_.get());
        }

        if (!catch_type) {
            report_error("catch handler requires a valid exception declaration type",
                handlers[i].location);
            continue;
        }
        if (catch_type->isVoid() || catch_type->isIncomplete()) {
            report_error("cannot catch incomplete type '" + catch_type.to_string() + "'",
                handlers[i].location);
        } else if (canonical_type_kind(catch_type, ast_ctx_.get()) ==
                   TypeKind::Function) {
            report_error("cannot catch function type '" + catch_type.to_string() + "'",
                handlers[i].location);
        }
    }

    return collect_make<CppTryStmt>(
        std::move(try_block),
        std::move(handlers),
        loc);
}


std::unique_ptr<Stmt> Collect::collect_compound_statement(std::vector<std::unique_ptr<Stmt>> stmts, std::shared_ptr<Scope> scope, SrcLoc loc) {

    return collect_make<CompoundStmt>(std::move(stmts), std::move(scope), loc);
}


std::unique_ptr<Stmt> Collect::collect_decl_statement(std::vector<std::unique_ptr<Decl>> decls, SrcLoc loc) const {

    return collect_make<Decl2Stmt>(std::move(decls), loc);
}


std::unique_ptr<Stmt> Collect::collect_decl_statement(std::unique_ptr<Decl> decl, SrcLoc loc) const {

    return collect_make<Decl2Stmt>(std::move(decl), loc);
}
