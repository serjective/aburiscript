#include "ast2llvm.h"
#include "../abi/mangle.h"
#include "../constexpr/consteval_compat.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include <algorithm>
#include <array>
#include <cctype>
#include <limits>

namespace {
std::optional<bool> try_fold_stmt_condition(Expr* condition) {
    if (!condition) {
        return std::nullopt;
    }

    Expr* core = condition;
    while (auto* cast = dyn_cast<ImplicitCast>(core)) {
        core = cast->expr.get();
    }
    if (!core) {
        return std::nullopt;
    }

    if (auto* builtin_cond = dyn_cast<BuiltinCallExpr>(core)) {
        if (builtin_cond->kind == BuiltinKind::CONSTANT_P) {
            if (builtin_cond->const_value.has_value()) {
                return *builtin_cond->const_value != 0;
            }
            if (!builtin_cond->args.empty() && builtin_cond->args[0]) {
                ConstEvalResult eval = evaluate_with_consteval_compat(
                    builtin_cond->args[0].get(), ConstEvalMode::builtin_query());
                return eval.status == ConstEvalStatus::Constant;
            }
            return false;
        }
    }

    bool simple_literal_condition =
        isa<IntegerLiteral>(core) ||
        isa<CharacterLiteral>(core);
    if (!simple_literal_condition) {
        return std::nullopt;
    }

    if (auto cond_const = try_evaluate_with_consteval_compat(
            core, ConstEvalMode::c_ice())) {
        return *cond_const != 0;
    }

    return std::nullopt;
}

bool stmt_contains_jump_target(Stmt* stmt) {
    if (!stmt) {
        return false;
    }

    std::vector<Stmt*> worklist;
    worklist.push_back(stmt);
    while (!worklist.empty()) {
        Stmt* current = worklist.back();
        worklist.pop_back();
        if (!current) {
            continue;
        }

        switch (current->get_kind()) {
            case StmtKind::LabeledStmt:
                return true;
            case StmtKind::CaseStmt:
            case StmtKind::DefaultStmt:
                return true;
            case StmtKind::CompoundStmt: {
                auto* compound = static_cast<CompoundStmt*>(current);
                for (auto it = compound->statements.rbegin();
                     it != compound->statements.rend();
                     ++it) {
                    worklist.push_back(it->get());
                }
                break;
            }
            case StmtKind::IfStmt: {
                auto* if_stmt = static_cast<IfStmt*>(current);
                worklist.push_back(if_stmt->init_stmt.get());
                if (if_stmt->statement_kind == IfStatementKind::Constexpr &&
                    if_stmt->constexpr_condition_value.has_value()) {
                    worklist.push_back(
                        (*if_stmt->constexpr_condition_value
                             ? if_stmt->then_stmt
                             : if_stmt->else_stmt).get());
                } else {
                    worklist.push_back(if_stmt->else_stmt.get());
                    worklist.push_back(if_stmt->then_stmt.get());
                }
                break;
            }
            case StmtKind::WhileStmt:
                worklist.push_back(static_cast<WhileStmt*>(current)->body_stmt.get());
                break;
            case StmtKind::DoWhileStmt:
                worklist.push_back(static_cast<DoWhileStmt*>(current)->body_stmt.get());
                break;
            case StmtKind::ForStmt: {
                auto* for_stmt = static_cast<ForStmt*>(current);
                worklist.push_back(for_stmt->init.get());
                worklist.push_back(for_stmt->body_stmt.get());
                break;
            }
            case StmtKind::CppRangeForStmt: {
                auto* range_for = static_cast<CppRangeForStmt*>(current);
                worklist.push_back(range_for->init_statement.get());
                worklist.push_back(range_for->body_stmt.get());
                break;
            }
            case StmtKind::SwitchStmt:
                worklist.push_back(static_cast<SwitchStmt*>(current)->stmt.get());
                break;
            default:
                break;
        }
    }
    return false;
}

class DeadJumpTargetMaterializationScope {
public:
    explicit DeadJumpTargetMaterializationScope(ASTToLLVM& codegen)
        : codegen(codegen), prev(codegen.materializing_dead_jump_targets) {
        codegen.materializing_dead_jump_targets = true;
    }

    ~DeadJumpTargetMaterializationScope() {
        codegen.materializing_dead_jump_targets = prev;
    }

private:
    ASTToLLVM& codegen;
    bool prev;
};
}

void ASTToLLVM::convert_if_statement(IfStmt *stmt) {
    auto *ifStmt = dyn_cast<IfStmt>(stmt);
    if (!ifStmt) { error("unexpected subclass in convert_if_statement()", stmt->location); return; }

    std::shared_ptr<Scope> prev_scope = current_scope;
    bool entered_if_scope = ifStmt->scope || ifStmt->init_stmt;
    if (entered_if_scope) {
        current_scope = ifStmt->scope;
        cleanup_stack.emplace_back();
    }
    auto leave_if_scope = [&]() {
        if (!entered_if_scope) {
            return;
        }
        if (!builder.GetInsertBlock()->getTerminator()) {
            emit_cleanups_for_scope();
        }
        cleanup_stack.pop_back();
        current_scope = prev_scope;
    };

    if (ifStmt->init_stmt) {
        convert_statement(ifStmt->init_stmt.get());
        if (builder.GetInsertBlock()->getTerminator()) {
            leave_if_scope();
            return;
        }
    }

    if (ifStmt->statement_kind == IfStatementKind::Constexpr) {
        std::optional<bool> condition_value = ifStmt->constexpr_condition_value;
        if (!condition_value.has_value()) {
            condition_value = try_fold_stmt_condition(ifStmt->condition.get());
        }
        if (!condition_value.has_value()) {
            error("convert_if_statement(): constexpr if condition was not resolved",
                  stmt->location);
            leave_if_scope();
            return;
        }
        if (*condition_value) {
            convert_statement(ifStmt->then_stmt.get());
        } else if (ifStmt->else_stmt) {
            convert_statement(ifStmt->else_stmt.get());
        }
        leave_if_scope();
        return;
    }

    bool keep_cfg_for_jump_targets =
        stmt_contains_jump_target(ifStmt->then_stmt.get()) ||
        stmt_contains_jump_target(ifStmt->else_stmt.get());
    if (!keep_cfg_for_jump_targets) {
        if (auto folded_cond = try_fold_stmt_condition(ifStmt->condition.get())) {
            auto materialize_dead_branch = [&](Stmt* dead_stmt) {
                if (!dead_stmt || !stmt_contains_jump_target(dead_stmt)) {
                    return;
                }
                DeadJumpTargetMaterializationScope scope(*this);
                convert_statement_after_terminator(dead_stmt, switch_inst != nullptr);
            };
            if (*folded_cond) {
                convert_statement(ifStmt->then_stmt.get());
                if (ifStmt->else_stmt) {
                    materialize_dead_branch(ifStmt->else_stmt.get());
                }
            } else if (ifStmt->else_stmt) {
                convert_statement(ifStmt->else_stmt.get());
                materialize_dead_branch(ifStmt->then_stmt.get());
            } else {
                materialize_dead_branch(ifStmt->then_stmt.get());
            }
            leave_if_scope();
            return;
        }
    }

    llvm::Value* condVal = convert_expression(ifStmt->condition.get());
    if (!condVal) {
        leave_if_scope();
        return;
    }

    condVal = emit_bool_conversion(condVal, "ifcond");

    llvm::Function* function = builder.GetInsertBlock()->getParent();

    llvm::BasicBlock* thenBB = llvm::BasicBlock::Create(*context, "then");
    llvm::BasicBlock* elseBB = llvm::BasicBlock::Create(*context, "else");
    llvm::BasicBlock* mergeBB = llvm::BasicBlock::Create(*context, "ifcont");

    bool hasElse = (ifStmt->else_stmt != nullptr);

    builder.CreateCondBr(condVal, thenBB, hasElse ? elseBB : mergeBB);

    // Emit then value.
    function->insert(function->end(), thenBB);
    builder.SetInsertPoint(thenBB);
    convert_statement(ifStmt->then_stmt.get());

    // Check if the then block already has a terminator (like return)
    if (!builder.GetInsertBlock()->getTerminator()) {
        builder.CreateBr(mergeBB);
    }

    // Codegen of 'Then' can change the current block, update thenBB for the PHI.
    // thenBB = builder.GetInsertBlock();

    if (hasElse) {
        function->insert(function->end(), elseBB);
        builder.SetInsertPoint(elseBB);
        convert_statement(ifStmt->else_stmt.get());

        if (!builder.GetInsertBlock()->getTerminator()) {
            builder.CreateBr(mergeBB);
        }
    } else {
        // No else block, so we don't need to insert it or generate code for it.
        // The CondBr above already jumps to mergeBB if false.
    }

    // Emit merge block.
    function->insert(function->end(), mergeBB);
    builder.SetInsertPoint(mergeBB);
    leave_if_scope();
}

void ASTToLLVM::convert_while_statement(WhileStmt *stmt) {
    llvm::Function* function = builder.GetInsertBlock()->getParent();
    llvm::BasicBlock* prev_cond = condloop;
    llvm::BasicBlock* prev_end = endloop;
    size_t prev_break_depth = break_cleanup_depth;
    size_t prev_continue_depth = continue_cleanup_depth;

    llvm::BasicBlock* condBB = llvm::BasicBlock::Create(*context, "while.cond");
    llvm::BasicBlock* bodyBB = llvm::BasicBlock::Create(*context, "while.body");
    llvm::BasicBlock* endBB = llvm::BasicBlock::Create(*context, "while.end");
    condloop = condBB;
    endloop = endBB;
    break_cleanup_depth = cleanup_stack.size();
    continue_cleanup_depth = cleanup_stack.size();

    builder.CreateBr(condBB);
    function->insert(function->end(), condBB);
    builder.SetInsertPoint(condBB);
    llvm::Value* condVal = convert_expression(stmt->condition.get());
    if (!condVal) {
        error("convert_while_statement(): failed to get value for condition", stmt->location);
        return;
    }
    condVal = emit_bool_conversion(condVal, "whilecond");
    builder.CreateCondBr(condVal, bodyBB, endBB);

    function->insert(function->end(), bodyBB);
    builder.SetInsertPoint(bodyBB);
    convert_statement(stmt->body_stmt.get());
    if (!builder.GetInsertBlock()->getTerminator()) {
        builder.CreateBr(condBB);
    }

    function->insert(function->end(), endBB);
    builder.SetInsertPoint(endBB);

    condloop = prev_cond;
    endloop = prev_end;
    break_cleanup_depth = prev_break_depth;
    continue_cleanup_depth = prev_continue_depth;
}

void ASTToLLVM::convert_do_while_statement(DoWhileStmt *stmt) {
    llvm::Function* function = builder.GetInsertBlock()->getParent();

    llvm::BasicBlock* prev_cond = condloop;
    llvm::BasicBlock* prev_end = endloop;
    size_t prev_break_depth = break_cleanup_depth;
    size_t prev_continue_depth = continue_cleanup_depth;

    llvm::BasicBlock* bodyBB = llvm::BasicBlock::Create(*context, "dowhile.body");
    llvm::BasicBlock* condBB = llvm::BasicBlock::Create(*context, "dowhile.cond");
    llvm::BasicBlock* endBB = llvm::BasicBlock::Create(*context, "dowhile.end");
    condloop = condBB;
    endloop = endBB;
    break_cleanup_depth = cleanup_stack.size();
    continue_cleanup_depth = cleanup_stack.size();

    builder.CreateBr(bodyBB);
    function->insert(function->end(), bodyBB);
    builder.SetInsertPoint(bodyBB);
    convert_statement(stmt->body_stmt.get());
    if (!builder.GetInsertBlock()->getTerminator()) {
        builder.CreateBr(condBB);
    }

    function->insert(function->end(), condBB);
    builder.SetInsertPoint(condBB);
    llvm::Value* condVal = convert_expression(stmt->condition.get());
    if (!condVal) {
        error("convert_do_while_statement(): unable to get value for condition", stmt->location);
        return;
    }
    condVal = emit_bool_conversion(condVal, "dowhilecond");
    builder.CreateCondBr(condVal, bodyBB, endBB);

    function->insert(function->end(), endBB);
    builder.SetInsertPoint(endBB);

    condloop = prev_cond;
    endloop = prev_end;
    break_cleanup_depth = prev_break_depth;
    continue_cleanup_depth = prev_continue_depth;
}
void ASTToLLVM::convert_for_statement(ForStmt *stmt) {
    llvm::Function* function = builder.GetInsertBlock()->getParent();

    llvm::BasicBlock* prev_cond = condloop;
    llvm::BasicBlock* prev_end = endloop;
    size_t prev_break_depth = break_cleanup_depth;
    size_t prev_continue_depth = continue_cleanup_depth;
    std::shared_ptr<Scope> prev_scope = current_scope;
    current_scope = stmt->scope;
    cleanup_stack.emplace_back();

    llvm::BasicBlock* initBB = llvm::BasicBlock::Create(*context, "for.init");
    llvm::BasicBlock* condBB = llvm::BasicBlock::Create(*context, "for.cond");
    llvm::BasicBlock* bodyBB = llvm::BasicBlock::Create(*context, "for.body");
    llvm::BasicBlock* incrBB = llvm::BasicBlock::Create(*context, "for.incr");
    llvm::BasicBlock* endBB = llvm::BasicBlock::Create(*context, "for.end");
    llvm::BasicBlock* cleanupBB = llvm::BasicBlock::Create(*context, "for.cleanup");

    condloop = incrBB; // Continue jumps to increment
    endloop = endBB;   // Break jumps to end
    break_cleanup_depth = cleanup_stack.size() - 1;
    continue_cleanup_depth = cleanup_stack.size();

    // Initializer
    builder.CreateBr(initBB);
    function->insert(function->end(), initBB);
    builder.SetInsertPoint(initBB);
    if (stmt->init) {
        convert_statement(stmt->init.get());
    }
    if (!builder.GetInsertBlock()->getTerminator()) {
        builder.CreateBr(condBB);
    } else {
        error("convert_for_statement(): branching out of a for initalizer", stmt->location);
        return;
    }

    // Condition
    function->insert(function->end(), condBB);
    builder.SetInsertPoint(condBB);
    llvm::Value* condVal = nullptr;
    if (stmt->cond) {
        condVal = convert_expression(stmt->cond.get());
        if (!condVal) {
            error("convert_for_statement(): failed to get value for condition", stmt->location);
            return;
        }
        condVal = emit_bool_conversion(condVal, "forcond");
    } else {
        // If no condition, it's an infinite loop (true)
        condVal = llvm::ConstantInt::get(*context, llvm::APInt(1, 1));
    }
    builder.CreateCondBr(condVal, bodyBB, cleanupBB);

    // Body
    function->insert(function->end(), bodyBB);
    builder.SetInsertPoint(bodyBB);
    convert_statement(stmt->body_stmt.get());
    if (!builder.GetInsertBlock()->getTerminator()) {
        builder.CreateBr(incrBB);
    }

    // Increment
    function->insert(function->end(), incrBB);
    builder.SetInsertPoint(incrBB);
    if (stmt->action) {
        convert_expression(stmt->action.get());
    }
    if (!builder.GetInsertBlock()->getTerminator()) {
        builder.CreateBr(condBB);
    } else {
        error("convert_for_statement(): branching in a for condition", stmt->location);
        return;
    }

    // Cleanup for-scope variables when condition is false
    function->insert(function->end(), cleanupBB);
    builder.SetInsertPoint(cleanupBB);
    emit_cleanups_for_scope();
    builder.CreateBr(endBB);

    // End
    function->insert(function->end(), endBB);
    builder.SetInsertPoint(endBB);

    cleanup_stack.pop_back();
    condloop = prev_cond;
    endloop = prev_end;
    break_cleanup_depth = prev_break_depth;
    continue_cleanup_depth = prev_continue_depth;
    current_scope = prev_scope;
}

void ASTToLLVM::convert_cpp_range_for_statement(CppRangeForStmt *stmt) {
    llvm::Function* function = builder.GetInsertBlock()->getParent();

    llvm::BasicBlock* prev_cond = condloop;
    llvm::BasicBlock* prev_end = endloop;
    size_t prev_break_depth = break_cleanup_depth;
    size_t prev_continue_depth = continue_cleanup_depth;
    std::shared_ptr<Scope> prev_scope = current_scope;
    current_scope = stmt->scope;
    cleanup_stack.emplace_back();

    llvm::BasicBlock* initBB = llvm::BasicBlock::Create(*context, "rangefor.init");
    llvm::BasicBlock* condBB = llvm::BasicBlock::Create(*context, "rangefor.cond");
    llvm::BasicBlock* bodyBB = llvm::BasicBlock::Create(*context, "rangefor.body");
    llvm::BasicBlock* incrBB = llvm::BasicBlock::Create(*context, "rangefor.incr");
    llvm::BasicBlock* cleanupBB = llvm::BasicBlock::Create(*context, "rangefor.cleanup");
    llvm::BasicBlock* endBB = llvm::BasicBlock::Create(*context, "rangefor.end");

    condloop = incrBB;
    endloop = endBB;
    break_cleanup_depth = cleanup_stack.size() - 1;
    continue_cleanup_depth = cleanup_stack.size();

    builder.CreateBr(initBB);
    function->insert(function->end(), initBB);
    builder.SetInsertPoint(initBB);
    if (stmt->init_statement) {
        convert_statement(stmt->init_statement.get());
    }
    for (auto& decl : stmt->range_declaration_side_decls) {
        convert_declaration(decl.get());
    }
    if (stmt->range_variable) {
        convert_declaration(stmt->range_variable.get());
    }
    if (stmt->begin_variable) {
        convert_declaration(stmt->begin_variable.get());
    }
    if (stmt->end_variable) {
        convert_declaration(stmt->end_variable.get());
    }
    if (!builder.GetInsertBlock()->getTerminator()) {
        builder.CreateBr(condBB);
    } else {
        error("convert_cpp_range_for_statement(): branching out of a range-for initializer",
              stmt->location);
        return;
    }

    function->insert(function->end(), condBB);
    builder.SetInsertPoint(condBB);
    llvm::Value* condVal = convert_expression(stmt->condition.get());
    if (!condVal) {
        error("convert_cpp_range_for_statement(): failed to get value for condition",
              stmt->location);
        return;
    }
    condVal = emit_bool_conversion(condVal, "rangeforcond");
    builder.CreateCondBr(condVal, bodyBB, cleanupBB);

    function->insert(function->end(), bodyBB);
    builder.SetInsertPoint(bodyBB);
    cleanup_stack.emplace_back();
    if (stmt->loop_variable) {
        convert_declaration(stmt->loop_variable.get());
    }
    if (stmt->body_stmt) {
        convert_statement(stmt->body_stmt.get());
    }
    if (!builder.GetInsertBlock()->getTerminator()) {
        emit_cleanups_for_scope();
        builder.CreateBr(incrBB);
    }
    cleanup_stack.pop_back();

    function->insert(function->end(), incrBB);
    builder.SetInsertPoint(incrBB);
    if (stmt->increment) {
        convert_expression(stmt->increment.get());
    }
    if (!builder.GetInsertBlock()->getTerminator()) {
        builder.CreateBr(condBB);
    } else {
        error("convert_cpp_range_for_statement(): branching in a range-for increment",
              stmt->location);
        return;
    }

    function->insert(function->end(), cleanupBB);
    builder.SetInsertPoint(cleanupBB);
    emit_cleanups_for_scope();
    builder.CreateBr(endBB);

    function->insert(function->end(), endBB);
    builder.SetInsertPoint(endBB);

    cleanup_stack.pop_back();
    condloop = prev_cond;
    endloop = prev_end;
    break_cleanup_depth = prev_break_depth;
    continue_cleanup_depth = prev_continue_depth;
    current_scope = prev_scope;
}
void ASTToLLVM::convert_continue_statement(Stmt *stmt) {
    if (!condloop) {
        error("continue statement outside of loop (condloop is null)", stmt->location);
        return;
    }
    if (!builder.GetInsertBlock()->getTerminator()) {
        emit_cleanups_to_depth(continue_cleanup_depth);
        builder.CreateBr(condloop);
    }
}
void ASTToLLVM::convert_break_statement(Stmt *stmt) {
    if (!endloop) {
        error("break statement outside of loop", stmt->location);
        return;
    }
    if (!builder.GetInsertBlock()->getTerminator()) {
        emit_cleanups_to_depth(break_cleanup_depth);
        builder.CreateBr(endloop);
    }
}
void ASTToLLVM::convert_switch_statement(SwitchStmt *stmt) {
    llvm::Function* function = builder.GetInsertBlock()->getParent();

    llvm::BasicBlock* prev_end = endloop;
    llvm::SwitchInst* prev_switch = switch_inst;
    llvm::BasicBlock* prev_switch_end = switch_end;
    llvm::BasicBlock* prev_switch_default = switch_default;
    size_t prev_break_depth = break_cleanup_depth;

    llvm::BasicBlock* endBB = llvm::BasicBlock::Create(*context, "switch.end");
    endloop = endBB; // Break jumps to end
    switch_end = endBB;
    break_cleanup_depth = cleanup_stack.size();

    llvm::Value* condVal = convert_expression(stmt->condition.get());
    if (!condVal) {
        error("error in getting switch condition", stmt->location);
        return;
    }

    switch_inst = builder.CreateSwitch(condVal, endBB, 0);
    switch_default = endBB; // Default goes to end unless overridden


    llvm::BasicBlock* bodyBB = llvm::BasicBlock::Create(*context, "switch.body.entry", function);
    // We don't branch to bodyBB from switch_inst.
    builder.SetInsertPoint(bodyBB);

    convert_statement(stmt->stmt.get());

    if (!builder.GetInsertBlock()->getTerminator()) {
        builder.CreateBr(endBB);
    }

    // If we found a default case, `switch_default` would have been updated by `convert_default_statement`.
    // We need to update the SwitchInst's default destination.
    switch_inst->setDefaultDest(switch_default);

    function->insert(function->end(), endBB);
    builder.SetInsertPoint(endBB);

    endloop = prev_end;
    switch_inst = prev_switch;
    switch_end = prev_switch_end;
    switch_default = prev_switch_default;
    break_cleanup_depth = prev_break_depth;
}

void ASTToLLVM::convert_case_statement(CaseStmt *stmt) {
    if (!switch_inst) {
        error("convert_case_statement(): case statement outside of switch", stmt->location);
        return;
    }

    llvm::Function* function = builder.GetInsertBlock()->getParent();
    auto emit_case_label = [&](CaseStmt* current_case) -> bool {
        auto low_eval = try_evaluate_with_consteval_compat(
            current_case->const_expr.get(), ConstEvalMode::c_ice());
        if (!low_eval.has_value()) {
            error("convert_case_statement(): case expression must be constant integer", current_case->location);
            return false;
        }
        auto* switchCondTy = switch_inst->getCondition()->getType();
        bool unsigned_switch = current_case->const_expr &&
            current_case->const_expr->get_type() &&
            current_case->const_expr->get_type()->isUnsigned();
        auto* lowInt = llvm::cast<llvm::ConstantInt>(llvm::ConstantInt::get(
            switchCondTy, static_cast<uint64_t>(*low_eval), !unsigned_switch));

        llvm::BasicBlock* caseBB = llvm::BasicBlock::Create(*context, "switch.case", function);

        // If the previous block (fallthrough) doesn't have a terminator, jump to this case.
        if (!builder.GetInsertBlock()->getTerminator() &&
            !materializing_dead_jump_targets) {
            builder.CreateBr(caseBB);
        }

        builder.SetInsertPoint(caseBB);

        if (current_case->is_range()) {
            auto high_eval = try_evaluate_with_consteval_compat(
                current_case->range_end.get(), ConstEvalMode::c_ice());
            if (!high_eval.has_value()) {
                error("convert_case_statement(): range end must be constant integer", current_case->location);
                return false;
            }
            auto* highInt = llvm::cast<llvm::ConstantInt>(llvm::ConstantInt::get(
                switchCondTy, static_cast<uint64_t>(*high_eval), !unsigned_switch));
            if (unsigned_switch) {
                uint64_t low = lowInt->getZExtValue();
                uint64_t high = highInt->getZExtValue();
                uint64_t span = (high >= low) ? (high - low) : 0;
                if (span > 65536ULL) {
                    auto* caseConst = llvm::cast<llvm::ConstantInt>(
                        llvm::ConstantInt::get(switchCondTy, low, false));
                    switch_inst->addCase(caseConst, caseBB);
                } else {
                    for (uint64_t i = low; i <= high; ++i) {
                        auto* caseConst = llvm::cast<llvm::ConstantInt>(
                            llvm::ConstantInt::get(switchCondTy, i, false));
                        switch_inst->addCase(caseConst, caseBB);
                        if (i == high) break;
                    }
                }
            } else {
                int64_t low = lowInt->getSExtValue();
                int64_t high = highInt->getSExtValue();
                uint64_t span = (high >= low) ? static_cast<uint64_t>(high - low) : 0ULL;
                if (span > 65536ULL) {
                    auto* caseConst = llvm::cast<llvm::ConstantInt>(
                        llvm::ConstantInt::get(switchCondTy, static_cast<uint64_t>(low), true));
                    switch_inst->addCase(caseConst, caseBB);
                } else {
                    for (int64_t i = low; i <= high; ++i) {
                        auto* caseConst = llvm::cast<llvm::ConstantInt>(
                            llvm::ConstantInt::get(switchCondTy, static_cast<uint64_t>(i), true));
                        switch_inst->addCase(caseConst, caseBB);
                        if (i == high) break;
                    }
                }
            }
        } else {
            switch_inst->addCase(lowInt, caseBB);
        }
        return true;
    };

    auto emit_default_label = [&](DefaultStmt* current_default) {
        llvm::BasicBlock* defaultBB = llvm::BasicBlock::Create(*context, "switch.default", function);
        if (!builder.GetInsertBlock()->getTerminator() &&
            !materializing_dead_jump_targets) {
            builder.CreateBr(defaultBB);
        }
        builder.SetInsertPoint(defaultBB);
        switch_default = defaultBB;
    };

    Stmt* next_stmt = stmt;
    while (true) {
        if (auto* case_stmt = dyn_cast<CaseStmt>(next_stmt)) {
            if (!emit_case_label(case_stmt)) {
                return;
            }
            next_stmt = case_stmt->stmt.get();
            continue;
        }
        if (auto* default_stmt = dyn_cast<DefaultStmt>(next_stmt)) {
            emit_default_label(default_stmt);
            next_stmt = default_stmt->stmt.get();
            continue;
        }
        break;
    }
    convert_statement(next_stmt);
}

void ASTToLLVM::convert_default_statement(DefaultStmt *stmt) {
    if (!switch_inst) {
        error("default statement outside of switch", stmt->location);
        return;
    }

    llvm::Function* function = builder.GetInsertBlock()->getParent();
    auto emit_default_label = [&](DefaultStmt* current_default) {
        llvm::BasicBlock* defaultBB = llvm::BasicBlock::Create(*context, "switch.default", function);
        if (!builder.GetInsertBlock()->getTerminator() &&
            !materializing_dead_jump_targets) {
            builder.CreateBr(defaultBB);
        }
        builder.SetInsertPoint(defaultBB);
        switch_default = defaultBB;
    };

    auto emit_case_label = [&](CaseStmt* current_case) -> bool {
        auto low_eval = try_evaluate_with_consteval_compat(
            current_case->const_expr.get(), ConstEvalMode::c_ice());
        if (!low_eval.has_value()) {
            error("convert_case_statement(): case expression must be constant integer", current_case->location);
            return false;
        }
        auto* switchCondTy = switch_inst->getCondition()->getType();
        bool unsigned_switch = current_case->const_expr &&
            current_case->const_expr->get_type() &&
            current_case->const_expr->get_type()->isUnsigned();
        auto* lowInt = llvm::cast<llvm::ConstantInt>(llvm::ConstantInt::get(
            switchCondTy, static_cast<uint64_t>(*low_eval), !unsigned_switch));
        llvm::BasicBlock* caseBB = llvm::BasicBlock::Create(*context, "switch.case", function);
        if (!builder.GetInsertBlock()->getTerminator() &&
            !materializing_dead_jump_targets) {
            builder.CreateBr(caseBB);
        }
        builder.SetInsertPoint(caseBB);

        if (current_case->is_range()) {
            auto high_eval = try_evaluate_with_consteval_compat(
                current_case->range_end.get(), ConstEvalMode::c_ice());
            if (!high_eval.has_value()) {
                error("convert_case_statement(): range end must be constant integer", current_case->location);
                return false;
            }
            auto* highInt = llvm::cast<llvm::ConstantInt>(llvm::ConstantInt::get(
                switchCondTy, static_cast<uint64_t>(*high_eval), !unsigned_switch));
            if (unsigned_switch) {
                uint64_t low = lowInt->getZExtValue();
                uint64_t high = highInt->getZExtValue();
                uint64_t span = (high >= low) ? (high - low) : 0;
                if (span > 65536ULL) {
                    auto* caseConst = llvm::cast<llvm::ConstantInt>(
                        llvm::ConstantInt::get(switchCondTy, low, false));
                    switch_inst->addCase(caseConst, caseBB);
                } else {
                    for (uint64_t i = low; i <= high; ++i) {
                        auto* caseConst = llvm::cast<llvm::ConstantInt>(
                            llvm::ConstantInt::get(switchCondTy, i, false));
                        switch_inst->addCase(caseConst, caseBB);
                        if (i == high) break;
                    }
                }
            } else {
                int64_t low = lowInt->getSExtValue();
                int64_t high = highInt->getSExtValue();
                uint64_t span = (high >= low) ? static_cast<uint64_t>(high - low) : 0ULL;
                if (span > 65536ULL) {
                    auto* caseConst = llvm::cast<llvm::ConstantInt>(
                        llvm::ConstantInt::get(switchCondTy, static_cast<uint64_t>(low), true));
                    switch_inst->addCase(caseConst, caseBB);
                } else {
                    for (int64_t i = low; i <= high; ++i) {
                        auto* caseConst = llvm::cast<llvm::ConstantInt>(
                            llvm::ConstantInt::get(switchCondTy, static_cast<uint64_t>(i), true));
                        switch_inst->addCase(caseConst, caseBB);
                        if (i == high) break;
                    }
                }
            }
        } else {
            switch_inst->addCase(lowInt, caseBB);
        }
        return true;
    };

    Stmt* next_stmt = stmt;
    while (true) {
        if (auto* default_stmt = dyn_cast<DefaultStmt>(next_stmt)) {
            emit_default_label(default_stmt);
            next_stmt = default_stmt->stmt.get();
            continue;
        }
        if (auto* case_stmt = dyn_cast<CaseStmt>(next_stmt)) {
            if (!emit_case_label(case_stmt)) {
                return;
            }
            next_stmt = case_stmt->stmt.get();
            continue;
        }
        break;
    }
    convert_statement(next_stmt);
}
void ASTToLLVM::convert_labeled_statement(LabeledStmt *stmt) {
    llvm::Function* function = builder.GetInsertBlock()->getParent();
    std::string label =  mangleCIdentifier(stmt->name);

    llvm::BasicBlock* labelBB;
    if (label_blocks.find(label) != label_blocks.end()) {
        labelBB = label_blocks[label];
    } else {
        error("couldn't find block in convert_labeled_statement", stmt->location);
        return;
    }
    if (labelBB->getParent() == nullptr) {
        function->insert(function->end(), labelBB);
    } else if (labelBB->getParent() != function) {
        error("convert_labeled_statement(): label belongs to a different function", stmt->location);
        return;
    }
    if (!labelBB->empty()) {
        error("convert_labeled_statement(): already inserted labeled statement", stmt->location);
        return;
    }
    //labelBB->moveAfter(builder.GetInsertBlock());

    // Fallthrough from previous block
    if (!builder.GetInsertBlock()->getTerminator() &&
        !materializing_dead_jump_targets) {
        builder.CreateBr(labelBB);
    }

    builder.SetInsertPoint(labelBB);
    std::vector<size_t> cleanup_counts;
    cleanup_counts.reserve(cleanup_stack.size());
    for (const auto& scope_cleanups : cleanup_stack) {
        cleanup_counts.push_back(scope_cleanups.size());
    }
    label_cleanup_counts[label] = std::move(cleanup_counts);
    convert_statement(stmt->stmt.get());
}

void ASTToLLVM::convert_goto_statement(GoToStmt *stmt) {
    std::string label = mangleCIdentifier(stmt->name);
    llvm::Function* function = builder.GetInsertBlock()->getParent();

    llvm::BasicBlock* targetBB;
    if (label_blocks.find(label) != label_blocks.end()) {
        targetBB = label_blocks[label];
    } else {
        error("couldn't find targeted block in convert_goto_statement()", stmt->location);
        return;
    }

    size_t target_depth = cleanup_stack.size();
    auto target_depth_it = label_cleanup_depths.find(label);
    if (target_depth_it != label_cleanup_depths.end()) {
        target_depth = std::min(target_depth_it->second, cleanup_stack.size());
    }
    uint32_t target_offset = 0;
    auto target_offset_it = label_offsets.find(label);
    if (target_offset_it != label_offsets.end()) {
        target_offset = target_offset_it->second;
    }

    bool used_label_cleanup_counts = false;
    auto target_counts_it = label_cleanup_counts.find(label);
    if (target_counts_it != label_cleanup_counts.end()) {
        const auto& target_counts = target_counts_it->second;
        size_t shared_depth = std::min(cleanup_stack.size(), target_counts.size());

        for (size_t i = cleanup_stack.size(); i > shared_depth; --i) {
            auto& scope = cleanup_stack[i - 1];
            for (auto it = scope.rbegin(); it != scope.rend(); ++it) {
                this->emit_cleanup_entry(*it);
            }
        }
        for (size_t i = shared_depth; i > 0; --i) {
            auto& scope = cleanup_stack[i - 1];
            size_t target_count = std::min(target_counts[i - 1], scope.size());
            for (size_t entry_idx = scope.size(); entry_idx > target_count; --entry_idx) {
                this->emit_cleanup_entry(scope[entry_idx - 1]);
            }
        }
        used_label_cleanup_counts = true;
    }

    if (!used_label_cleanup_counts) {
        for (size_t i = cleanup_stack.size(); i > target_depth; --i) {
            auto& scope = cleanup_stack[i - 1];
            for (auto it = scope.rbegin(); it != scope.rend(); ++it) {
                this->emit_cleanup_entry(*it);
            }
        }

        // Backward/outer goto into the same lexical scope may cross declarations
        // with active cleanups (e.g. VLA stacksave points). Emit those entries
        // declared after the target label before branching.
        if (target_depth > 0 && target_depth <= cleanup_stack.size() &&
            target_offset != 0) {
            auto& target_scope = cleanup_stack[target_depth - 1];
            for (auto it = target_scope.rbegin(); it != target_scope.rend(); ++it) {
                if (it->location.isInvalid()) {
                    continue;
                }
                if (it->location.offset > target_offset) {
                    this->emit_cleanup_entry(*it);
                }
            }
        }
    }

    builder.CreateBr(targetBB);
    llvm::BasicBlock* afterBB = llvm::BasicBlock::Create(*context, "after_goto", function);
    builder.SetInsertPoint(afterBB);

}
void ASTToLLVM::convert_computed_goto_statement(ComputedGotoStmt *stmt) {
    llvm::Function* function = builder.GetInsertBlock()->getParent();
    if (!function) {
        error("convert_computed_goto_statement(): not inside a function", stmt->location);
        return;
    }
    if (label_blocks.empty()) {
        error("convert_computed_goto_statement(): no labels available for indirect branch", stmt->location);
        return;
    }
    llvm::Value* target = convert_expression(stmt->target.get());
    if (!target) {
        error("convert_computed_goto_statement(): invalid target expression", stmt->location);
        return;
    }
    if (!cleanup_stack.empty()) {
        llvm::Function* stackrestore_fn = nullptr;
        for (auto scope_it = cleanup_stack.rbegin(); scope_it != cleanup_stack.rend(); ++scope_it) {
            for (auto it = scope_it->rbegin(); it != scope_it->rend(); ++it) {
                if (it->kind != CleanupEntry::Kind::StackRestore || !it->var_addr) {
                    continue;
                }
                if (!stackrestore_fn) {
                    llvm::Type* ptr_ty = llvm::PointerType::get(*context, 0);
                    stackrestore_fn = llvm::Intrinsic::getDeclaration(
                        module.get(), llvm::Intrinsic::stackrestore, {ptr_ty});
                }
                builder.CreateCall(stackrestore_fn, {it->var_addr});
            }
        }
    }
    auto* indirect = builder.CreateIndirectBr(target, label_blocks.size());
    for (const auto &entry : label_blocks) {
        indirect->addDestination(entry.second);
    }
    llvm::BasicBlock* afterBB = llvm::BasicBlock::Create(*context, "after_goto", function);
    builder.SetInsertPoint(afterBB);
}
