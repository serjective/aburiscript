#include "collect.h"
#include "collect_internal.h"
#include "../helpers/auto_type_utils.h"
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


std::unique_ptr<Stmt> Collect::collect_if_statement(std::unique_ptr<Expr> condition, std::unique_ptr<Stmt> then_stmt, std::unique_ptr<Stmt> else_stmt, SrcLoc loc) const {

    condition = collect_condition_expression(std::move(condition), loc, "if");
    if (auto* binop = dyn_cast<BinaryOperation>(condition.get())) {
        if (binop->bop == BinOpTypes::ASSIGN) {
            report_warning("using '=' in condition; did you mean '=='?", binop->location);
        }
    }
    return collect_make<IfStmt>(std::move(condition), std::move(then_stmt), std::move(else_stmt), loc);
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

    if (session_.func_state_.in_function) {
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

    if (isa<InitListExpr>(expr.get())) {
        expr = process_initializer_for_type(std::move(expr), return_type, loc);
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

        if (return_state &&
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
            !expr_type ||
            expression_depends_on_template_parameters(expr.get()) ||
            type_depends_on_template_parameters(return_type, ast_ctx_.get()) ||
            type_depends_on_template_parameters(expr_type, ast_ctx_.get()) ||
            contains_deferred_semantic_type(return_type.get_shared()) ||
            contains_deferred_semantic_type(expr_type.get_shared()) ||
            auto_type_utils::has_cxx_auto_type(return_type.get_shared()) ||
            auto_type_utils::has_cxx_auto_type(expr_type.get_shared());
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
