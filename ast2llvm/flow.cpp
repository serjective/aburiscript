#include "ast2llvm.h"
#include "lower_helpers.h"
#include "../abi/darwin_blocks.h"
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
QualType kr_abi_promote_param_type(const QualType& qt, const std::shared_ptr<TypeContext>& type_ctx) {
    auto builtin = qt.as_shared<BuiltinType>();
    if (!builtin || !type_ctx) {
        return qt;
    }

    switch (builtin->builtin_kind) {
        case BuiltinTypes::Float:
            return QualType(type_ctx->get_builtin(BuiltinTypes::Double), qt.get_qualifiers());
        case BuiltinTypes::Bool:
        case BuiltinTypes::Char:
        case BuiltinTypes::SChar:
        case BuiltinTypes::UChar:
        case BuiltinTypes::Char16:
        case BuiltinTypes::Short:
        case BuiltinTypes::UShort:
            return QualType(type_ctx->get_builtin(BuiltinTypes::Int), qt.get_qualifiers());
        default:
            return qt;
    }
}

std::string get_itanium_builtin_type_code(BuiltinTypes kind) {
    switch (kind) {
        case BuiltinTypes::Void:
            return "v";
        case BuiltinTypes::NullPtr:
            return "Dn";
        case BuiltinTypes::Bool:
            return "b";
        case BuiltinTypes::Char:
            return "c";
        case BuiltinTypes::SChar:
            return "a";
        case BuiltinTypes::UChar:
            return "h";
        case BuiltinTypes::WChar:
            return "w";
        case BuiltinTypes::Char16:
            return "Ds";
        case BuiltinTypes::Char32:
            return "Di";
        case BuiltinTypes::Short:
            return "s";
        case BuiltinTypes::UShort:
            return "t";
        case BuiltinTypes::Int:
            return "i";
        case BuiltinTypes::UInt:
            return "j";
        case BuiltinTypes::Long:
            return "l";
        case BuiltinTypes::ULong:
            return "m";
        case BuiltinTypes::LongLong:
            return "x";
        case BuiltinTypes::ULongLong:
            return "y";
        case BuiltinTypes::Int128:
            return "n";
        case BuiltinTypes::UInt128:
            return "o";
        case BuiltinTypes::Float:
            return "f";
        case BuiltinTypes::Double:
            return "d";
        case BuiltinTypes::LongDouble:
            return "e";
        case BuiltinTypes::Float16:
        default:
            return "";
    }
}

const EhRuntimeHooks& get_active_eh_runtime_hooks(const ASTToLLVM& codegen) {
    if (codegen.ast_ctx && codegen.ast_ctx->abi_policy) {
        return codegen.ast_ctx->abi_policy->eh_runtime_hooks;
    }
    static const EhRuntimeHooks defaults =
        eh_runtime_hooks_for_kind(EhRuntimeKind::LLVM);
    return defaults;
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
                worklist.push_back(if_stmt->else_stmt.get());
                worklist.push_back(if_stmt->then_stmt.get());
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
            case StmtKind::SwitchStmt:
                worklist.push_back(static_cast<SwitchStmt*>(current)->stmt.get());
                break;
            default:
                break;
        }
    }
    return false;
}
}

void ASTToLLVM::emit_cleanup_cpp_destructor(const CleanupEntry& entry,
                                            const std::string& context) {
    if (entry.kind != CleanupEntry::Kind::CppDestructor || !entry.var_addr) {
        return;
    }
    if (entry.cxx_destructor_object_type &&
        canonical_type_kind(entry.cxx_destructor_object_type, ast_ctx.get()) ==
            TypeKind::Object) {
        emit_cpp_object_teardown_recursive(
            entry.cxx_destructor_object_type,
            entry.var_addr,
            entry.cxx_destructor_sym,
            entry.location,
            context,
            CppCtorDtorVariant::Complete);
        return;
    }
    emit_cpp_destruct_call(entry.cxx_destructor_sym,
                           entry.var_addr,
                           entry.location,
                           context);
}

void ASTToLLVM::emit_cleanup_entry(const CleanupEntry& entry) {
    switch (entry.kind) {
        case CleanupEntry::Kind::StackRestore: {
            if (!entry.var_addr) {
                return;
            }
            llvm::Type* ptr_ty = llvm::PointerType::get(*context, 0);
            llvm::Function* stackrestore_fn = llvm::Intrinsic::getDeclaration(
                module.get(), llvm::Intrinsic::stackrestore, {ptr_ty});
            builder.CreateCall(stackrestore_fn, {entry.var_addr});
            return;
        }
        case CleanupEntry::Kind::CppDestructor:
            emit_cleanup_cpp_destructor(entry, "emit_cleanup_entry()");
            return;
        case CleanupEntry::Kind::BlockByrefDispose: {
            if (!entry.var_addr) {
                return;
            }
            llvm::Function* dispose_fn = get_or_create_block_object_dispose();
            if (!dispose_fn) {
                return;
            }
            llvm::Value* cell_addr = entry.var_addr;
            llvm::Type* ptr_ty = llvm::PointerType::get(*context, 0);
            if (cell_addr->getType() != ptr_ty) {
                cell_addr = builder.CreatePointerCast(cell_addr, ptr_ty,
                                                     "block.byref.cleanup.addr");
            }
            builder.CreateCall(
                dispose_fn,
                {cell_addr,
                 llvm::ConstantInt::get(
                     llvm::Type::getInt32Ty(*context),
                     darwin_blocks::BLOCK_FIELD_IS_BYREF)});
            return;
        }
        case CleanupEntry::Kind::CallNoArgs: {
            llvm::Function* func = module->getFunction(entry.cleanup_func);
            if (!func) {
                return;
            }
            builder.CreateCall(func);
            return;
        }
        case CleanupEntry::Kind::Call:
        default: {
            llvm::Function* func = module->getFunction(entry.cleanup_func);
            if (!func) {
                return;
            }
            if (func->arg_size() == 0) {
                builder.CreateCall(func);
            } else {
                builder.CreateCall(func, {entry.var_addr});
            }
            return;
        }
    }
}

void ASTToLLVM::emit_cleanups_for_scope() {
    if (cleanup_stack.empty()) return;
    auto& scope = cleanup_stack.back();
    for (auto it = scope.rbegin(); it != scope.rend(); ++it) {
        emit_cleanup_entry(*it);
    }
}

void ASTToLLVM::emit_all_cleanups() {
    for (auto scope_it = cleanup_stack.rbegin(); scope_it != cleanup_stack.rend(); ++scope_it) {
        for (auto it = scope_it->rbegin(); it != scope_it->rend(); ++it) {
            emit_cleanup_entry(*it);
        }
    }
}

void ASTToLLVM::emit_cleanups_to_depth(size_t target_depth) {
    for (size_t i = cleanup_stack.size(); i > target_depth; --i) {
        auto& scope = cleanup_stack[i - 1];
        for (auto it = scope.rbegin(); it != scope.rend(); ++it) {
            emit_cleanup_entry(*it);
        }
    }
}

void ASTToLLVM::collect_label_cleanup_depths(Stmt* stmt, size_t depth) {
    if (!stmt) {
        return;
    }

    std::vector<std::pair<Stmt*, size_t>> worklist;
    worklist.emplace_back(stmt, depth);

    while (!worklist.empty()) {
        auto [current_stmt, current_depth] = worklist.back();
        worklist.pop_back();
        if (!current_stmt) {
            continue;
        }

        if (auto* compound = dyn_cast<CompoundStmt>(current_stmt)) {
            size_t nested_depth = current_depth + 1;
            for (auto it = compound->statements.rbegin();
                 it != compound->statements.rend();
                 ++it) {
                worklist.emplace_back(it->get(), nested_depth);
            }
            continue;
        }
        if (auto* labeled = dyn_cast<LabeledStmt>(current_stmt)) {
            const std::string mangled_label = mangleCIdentifier(labeled->name);
            label_cleanup_depths[mangled_label] = current_depth;
            label_offsets[mangled_label] = labeled->location.offset;
            worklist.emplace_back(labeled->stmt.get(), current_depth);
            continue;
        }
        if (auto* if_stmt = dyn_cast<IfStmt>(current_stmt)) {
            worklist.emplace_back(if_stmt->else_stmt.get(), current_depth);
            worklist.emplace_back(if_stmt->then_stmt.get(), current_depth);
            continue;
        }
        if (auto* while_stmt = dyn_cast<WhileStmt>(current_stmt)) {
            worklist.emplace_back(while_stmt->body_stmt.get(), current_depth);
            continue;
        }
        if (auto* do_while_stmt = dyn_cast<DoWhileStmt>(current_stmt)) {
            worklist.emplace_back(do_while_stmt->body_stmt.get(), current_depth);
            continue;
        }
        if (auto* for_stmt = dyn_cast<ForStmt>(current_stmt)) {
            size_t for_depth = current_depth + 1;
            worklist.emplace_back(for_stmt->body_stmt.get(), for_depth);
            worklist.emplace_back(for_stmt->init.get(), for_depth);
            continue;
        }
        if (auto* switch_stmt = dyn_cast<SwitchStmt>(current_stmt)) {
            worklist.emplace_back(switch_stmt->stmt.get(), current_depth);
            continue;
        }
        if (auto* case_stmt = dyn_cast<CaseStmt>(current_stmt)) {
            worklist.emplace_back(case_stmt->stmt.get(), current_depth);
            continue;
        }
        if (auto* default_stmt = dyn_cast<DefaultStmt>(current_stmt)) {
            worklist.emplace_back(default_stmt->stmt.get(), current_depth);
            continue;
        }
    }
}

// todo: handle situation where we have more statements after a return/goto
// note: we should ALWAYS be writing at the block at is at the end of the function
void ASTToLLVM::convert_return_statement(Stmt *stmt) {
    auto *node = dyn_cast<ReturnStmt>(stmt);
    if (!node) { error("unexpected subclass", stmt->location); return; }
    llvm::Value * retval = nullptr;
    llvm::Function* function = builder.GetInsertBlock()->getParent();
    llvm::Argument* sret_arg = nullptr;
    llvm::Type* sret_value_type = nullptr;
    for (auto& arg : function->args()) {
        if (!arg.hasStructRetAttr()) {
            continue;
        }
        sret_arg = &arg;
        sret_value_type = arg.getParamStructRetType();
        break;
    }
    if (node->expression != nullptr) {
        retval = convert_expression(node->expression.get());
        if (!retval) {
            std::string expr_type =
                node->expression->get_type()
                    ? node->expression->get_type().to_string()
                    : std::string("<null>");
            error(
                "convert_return_statement(): failed to lower return expression of kind " +
                    std::to_string(static_cast<int>(node->expression->get_kind())) +
                    " with type '" + expr_type + "'",
                stmt->location);
            return;
        }
    } else {
        if (sret_arg && sret_value_type) {
            retval = llvm::Constant::getNullValue(sret_value_type);
        } else
        // Return void if function returns void, or 0 if int?
        // We need to check the function return type.
        // For now, assuming int return type as per previous implementation default
        if (function->getReturnType()->isVoidTy()) {
            emit_all_cleanups();
            builder.CreateRetVoid();
            llvm::BasicBlock* afterBB = llvm::BasicBlock::Create(*context, "after_ret", function);
            builder.SetInsertPoint(afterBB);
            return;
        }
        if (function->getReturnType()->isFloatingPointTy()) {
            retval = llvm::ConstantFP::get(function->getReturnType(), 0.0);
        } else if (function->getReturnType()->isIntegerTy()) {
            retval = llvm::ConstantInt::get(function->getReturnType(), 0);
        } else {
            retval = llvm::Constant::getNullValue(function->getReturnType());
        }

    }

    if (sret_arg && sret_value_type) {
        if (retval && retval->getType() != sret_value_type) {
            if (retval->getType()->isStructTy() && sret_value_type->isStructTy()) {
                auto* alloca = builder.CreateAlloca(retval->getType());
                builder.CreateStore(retval, alloca);
                retval = builder.CreateLoad(sret_value_type, alloca);
            } else {
                error("convert_return_statement(): mismatched indirect return and expression types",
                      stmt->location);
                return;
            }
        }

        emit_all_cleanups();
        auto* store = builder.CreateStore(retval, sret_arg);
        store->setAlignment(module->getDataLayout().getABITypeAlign(sret_value_type));
        builder.CreateRetVoid();
        llvm::BasicBlock* afterBB =
            llvm::BasicBlock::Create(*context, "after_ret", function);
        builder.SetInsertPoint(afterBB);
        return;
    }

    // If function is void but we have a value (GCC -fpermissive), just return void
    if (function->getReturnType()->isVoidTy() && retval) {
        emit_all_cleanups();
        builder.CreateRetVoid();
        llvm::BasicBlock* afterBB = llvm::BasicBlock::Create(*context, "after_ret", function);
        builder.SetInsertPoint(afterBB);
        return;
    }

    // Implicit cast if needed (though Sema should have handled it, LLVM is strict)
    if (retval && retval->getType() != function->getReturnType()) {
        if (retval->getType()->isIntegerTy() && function->getReturnType()->isIntegerTy()) {
             retval = builder.CreateIntCast(retval, function->getReturnType(), true);
        } else if (retval->getType()->isFloatingPointTy() && function->getReturnType()->isFloatingPointTy()) {
             retval = builder.CreateFPCast(retval, function->getReturnType());
        } else if (retval->getType()->isPointerTy() && function->getReturnType()->isPointerTy()) {
             // opaque pointers, no cast needed
        } else if (retval->getType()->isStructTy() && function->getReturnType()->isStructTy()) {
             // Struct type mismatch (e.g. from pointer cast + deref) — bitcast via memory
             auto* alloca = builder.CreateAlloca(retval->getType());
             builder.CreateStore(retval, alloca);
             retval = builder.CreateLoad(function->getReturnType(), alloca);
        } else {
             error("convert_return_statement(): mismatched return and function types", stmt->location);
             return;
        }
    }

    emit_all_cleanups();
    builder.CreateRet(retval);
    llvm::BasicBlock* afterBB = llvm::BasicBlock::Create(*context, "after_ret", function);
    builder.SetInsertPoint(afterBB);
}
void ASTToLLVM::convert_empty_stmt(EmptyStmt *stmt) {
   // llvm::Function *func = llvm::Intrinsic::getDeclaration(module.get(), llvm::Intrinsic::donothing);
  //  builder.CreateCall(func);
}
void ASTToLLVM::convert_statement(Stmt *stmt) {
    if (!stmt) {
        error("convert_statement(): nullptr argument");
        return;
    }
    emit_debug_location(stmt);

    switch (stmt->get_kind()) {
        case StmtKind::ReturnStmt:
            convert_return_statement(static_cast<ReturnStmt*>(stmt));
            return;
        case StmtKind::Decl2Stmt: {
            auto* decl_stmt = static_cast<Decl2Stmt*>(stmt);
            for (auto& decl : decl_stmt->decls) {
                convert_declaration(decl.get());
            }
            return;
        }
        case StmtKind::IfStmt:
            convert_if_statement(static_cast<IfStmt*>(stmt));
            return;
        case StmtKind::CompoundStmt:
            convert_compound_statement(static_cast<CompoundStmt*>(stmt));
            return;
        case StmtKind::CppTryStmt:
            convert_cpp_try_statement(static_cast<CppTryStmt*>(stmt));
            return;
        case StmtKind::CaseStmt:
            convert_case_statement(static_cast<CaseStmt*>(stmt));
            return;
        case StmtKind::DefaultStmt:
            convert_default_statement(static_cast<DefaultStmt*>(stmt));
            return;
        case StmtKind::LabeledStmt:
            convert_labeled_statement(static_cast<LabeledStmt*>(stmt));
            return;
        case StmtKind::GoToStmt:
            convert_goto_statement(static_cast<GoToStmt*>(stmt));
            return;
        case StmtKind::ComputedGotoStmt:
            convert_computed_goto_statement(static_cast<ComputedGotoStmt*>(stmt));
            return;
        case StmtKind::SwitchStmt:
            convert_switch_statement(static_cast<SwitchStmt*>(stmt));
            return;
        case StmtKind::WhileStmt:
            convert_while_statement(static_cast<WhileStmt*>(stmt));
            return;
        case StmtKind::DoWhileStmt:
            convert_do_while_statement(static_cast<DoWhileStmt*>(stmt));
            return;
        case StmtKind::ForStmt:
            convert_for_statement(static_cast<ForStmt*>(stmt));
            return;
        case StmtKind::ContinueStmt:
            convert_continue_statement(static_cast<ContinueStmt*>(stmt));
            return;
        case StmtKind::BreakStmt:
            convert_break_statement(static_cast<BreakStmt*>(stmt));
            return;
        case StmtKind::EmptyStmt:
            convert_empty_stmt(static_cast<EmptyStmt*>(stmt));
            return;
        case StmtKind::AsmStmt:
            convert_asm_statement(static_cast<AsmStmt*>(stmt));
            return;
        default:
            break;
    }

    if (Expr::classof(stmt)) {
        convert_expression(static_cast<Expr*>(stmt));
        return;
    }

    error("convert_statement(): unexpected subclass", stmt->location);
}

void ASTToLLVM::convert_statement_after_terminator(Stmt *stmt,
                                                   bool allow_case_labels) {
    if (!stmt) {
        return;
    }

    switch (stmt->get_kind()) {
        case StmtKind::CompoundStmt: {
            auto* compound = static_cast<CompoundStmt*>(stmt);
            std::shared_ptr<Scope> prev_scope = current_scope;
            current_scope = compound->scope;
            cleanup_stack.emplace_back();
            bool waiting_for_dead_restart =
                materializing_dead_jump_targets &&
                !builder.GetInsertBlock()->getTerminator();
            for (auto&& child : compound->statements) {
                if (builder.GetInsertBlock()->getTerminator()) {
                    convert_statement_after_terminator(child.get(), allow_case_labels);
                    continue;
                }
                if (waiting_for_dead_restart) {
                    if (!stmt_contains_jump_target(child.get())) {
                        continue;
                    }
                    convert_statement_after_terminator(child.get(), allow_case_labels);
                    waiting_for_dead_restart = builder.GetInsertBlock()->getTerminator();
                    continue;
                }
                convert_statement(child.get());
            }
            cleanup_stack.pop_back();
            current_scope = prev_scope;
            return;
        }
        case StmtKind::LabeledStmt:
            convert_labeled_statement(static_cast<LabeledStmt*>(stmt));
            return;
        case StmtKind::CaseStmt:
            if (allow_case_labels) {
                convert_case_statement(static_cast<CaseStmt*>(stmt));
            }
            return;
        case StmtKind::DefaultStmt:
            if (allow_case_labels) {
                convert_default_statement(static_cast<DefaultStmt*>(stmt));
            }
            return;
        case StmtKind::IfStmt: {
            auto* if_stmt = static_cast<IfStmt*>(stmt);
            convert_statement_after_terminator(if_stmt->then_stmt.get(),
                                               allow_case_labels);
            if (if_stmt->else_stmt) {
                convert_statement_after_terminator(if_stmt->else_stmt.get(),
                                                   allow_case_labels);
            }
            return;
        }
        case StmtKind::WhileStmt:
            convert_statement_after_terminator(
                static_cast<WhileStmt*>(stmt)->body_stmt.get(),
                allow_case_labels);
            return;
        case StmtKind::DoWhileStmt:
            convert_statement_after_terminator(
                static_cast<DoWhileStmt*>(stmt)->body_stmt.get(),
                allow_case_labels);
            return;
        case StmtKind::ForStmt: {
            auto* for_stmt = static_cast<ForStmt*>(stmt);
            if (for_stmt->init) {
                convert_statement_after_terminator(for_stmt->init.get(),
                                                   allow_case_labels);
            }
            convert_statement_after_terminator(for_stmt->body_stmt.get(),
                                               allow_case_labels);
            return;
        }
        case StmtKind::SwitchStmt:
            // Later cases/defaults belong to the nested switch, not the
            // terminated outer flow. Named labels inside the nested body still
            // need blocks for gotos, so recurse with case labels disabled.
            convert_statement_after_terminator(
                static_cast<SwitchStmt*>(stmt)->stmt.get(), false);
            return;
        default:
            return;
    }
}

void ASTToLLVM::convert_compound_statement(
    Stmt *stmt,
    bool preserve_scope_cleanup_entries) {
    auto *node = dyn_cast<CompoundStmt>(stmt);
    if (!node) { error("unexpected subclass in convert_compound_statement()", stmt->location); return; }
    std::shared_ptr<Scope> prev_scope = current_scope;
    current_scope = node->scope;
    cleanup_stack.emplace_back();
    for (auto&& astate: node->statements) {
        if (builder.GetInsertBlock()->getTerminator()) {
            convert_statement_after_terminator(astate.get(),
                                               switch_inst != nullptr);
            continue;
        }
        convert_statement(astate.get());
    }
    if (!builder.GetInsertBlock()->getTerminator()) {
        emit_cleanups_for_scope();
    }
    if (!preserve_scope_cleanup_entries) {
        cleanup_stack.pop_back();
    }
    current_scope = prev_scope;
}

llvm::Value* ASTToLLVM::convert_stmt_expr(StmtExpr *expr) {
    auto *cstmt = expr->compound_stmt.get();
    auto prev_scope = current_scope;
    current_scope = cstmt->scope;
    cleanup_stack.emplace_back();

    llvm::Value* lastVal = nullptr;
    for (auto &&astate : cstmt->statements) {
        if (auto *e = dyn_cast<Expr>(astate.get())) {
            // Expression statements also need debug locations
            if (e) emit_debug_location(e);
            lastVal = convert_expression(e);
        } else {
            convert_statement(astate.get());
            lastVal = nullptr;
        }
    }

    if (!builder.GetInsertBlock()->getTerminator()) {
        emit_cleanups_for_scope();
    }
    cleanup_stack.pop_back();
    current_scope = prev_scope;
    return lastVal;
}

void ASTToLLVM::emit_function_body(FuncDecl *node,
                                   llvm::Function *mainFunc,
                                   SrcLoc loc,
                                   CppCtorDtorVariant special_member_variant) {
    if (!node || !mainFunc) {
        error("convert_function_declaration(): invalid function body emission target", loc);
        return;
    }
    if (!mainFunc->empty()) {
        // we've already done the function body
        std::string fn_name = mainFunc->getName().str();
        error("convert_function_declaration(): function already defined ('" +
              fn_name + "')", loc);
        return;
    }

    if (builder.GetInsertBlock() != nullptr) {
        // were' already in a function
        error("convert_function_declaration(): nested function", loc);
        return;
    }

    // Keep local value bindings function-scoped. The same AST body can be
    // emitted multiple times for C++ ctor/dtor complete/base variants; if we
    // retain locals globally, repeated emission of the same local UID collides.
    struct NamedValuesRestoreGuard {
        ASTToLLVM* owner = nullptr;
        std::map<std::string, llvm::Value*> saved;
        explicit NamedValuesRestoreGuard(ASTToLLVM* self)
            : owner(self), saved(self ? self->named_values
                                      : std::map<std::string, llvm::Value*>{}) {}
        ~NamedValuesRestoreGuard() {
            if (owner) {
                owner->named_values = std::move(saved);
            }
        }
    } named_values_guard(this);

    // From here on out, we assume we have function body
    vla_size_cache.clear();
    reset_entry_alloca_insertion_state();
    cleanup_stack.clear();
    break_cleanup_depth = 0;
    continue_cleanup_depth = 0;
    // Create a basic block
    llvm::BasicBlock* entryBB = llvm::BasicBlock::Create(*context, "entry", mainFunc);
    builder.SetInsertPoint(entryBB);

    // Create debug info for function definitions (not declarations).
    // This attaches a DISubprogram and sets the builder's debug location
    // so that parameter alloca/store instructions get proper locations.
    create_debug_info_for_function(node, mainFunc);

    // Clear label maps for new function
    label_blocks.clear();
    label_cleanup_depths.clear();
    label_offsets.clear();
    label_cleanup_counts.clear();
    for (const auto &str: node->stmt_labels) {
        std::string mangled = mangleCIdentifier(str); // todo: what if we have multiple gotos in multiple functions with same name
        label_blocks[mangled] = llvm::BasicBlock::Create(*context, mangled, mainFunc);
    }
    // Precompute cleanup depth at each label so gotos can unwind the correct
    // subset of cleanup actions before branching.
    collect_label_cleanup_depths(node->body.get(), 0);

    // Handle parameters: allocate stack space and store initial values
    auto func_ctype_body = dyn_cast_shared<FunctionType>(node->type);
    bool allow_byref_aggregate_params =
        !(func_ctype_body && !func_ctype_body->has_prototype);
    auto uses_raw_kandr_aggregate_storage = [&](const QualType& param_type) {
        if (!(func_ctype_body && !func_ctype_body->has_prototype)) {
            return false;
        }
        auto canonical = desugar_type(param_type, ast_ctx.get());
        return canonical && canonical->kind == TypeKind::Object &&
               (pass_aggregate_by_reference(canonical) ||
                has_direct_aggregate_parameter_abi(canonical));
    };
    unsigned idx = 0;
    for (auto& arg : mainFunc->args()) {
        if (arg.hasStructRetAttr()) {
            continue;
        }
        // Get the parameter declaration from AST
        auto *paramDecl = cast<ParamDecl>(node->parameters[idx].get());
        auto sym = paramDecl->sym;
        if (sym == nullptr) {
            // Unnamed parameter — no symbol, just skip it
            idx++;
            continue;
        }
        std::string uid = sym->uid;
        if (paramDecl) {
            arg.setName(paramDecl->get_name());

            // Add noalias attribute for restrict-qualified pointer parameters
            if (paramDecl->type.is_restrict() && arg.getType()->isPointerTy()) {
                arg.addAttr(llvm::Attribute::NoAlias);
            }

            // Create alloca for the parameter
            std::string mangled = mangleCIdentifier(uid); // Assuming we use mangled names for locals

            if (canonical_type_kind(paramDecl->type, ast_ctx.get()) == TypeKind::Reference) {
                // Reference parameters are already incoming addresses.
                named_values[mangled] = &arg;
                idx++;
                continue;
            }

            if (allow_byref_aggregate_params && pass_aggregate_by_reference(paramDecl->type)) {
                // Large aggregate params are represented as indirect pointers.
                // The caller materializes the by-value copy before the call.
                named_values[mangled] = &arg;
                idx++;
                continue;
            }

            auto canonical_param_type = desugar_type(paramDecl->type, ast_ctx.get());
            llvm::Type* storage_type = nullptr;
            if (canonical_param_type &&
                (canonical_param_type->kind == TypeKind::Array ||
                 canonical_param_type->kind == TypeKind::Function ||
                 canonical_param_type->kind == TypeKind::Reference)) {
                storage_type = convert_param_type(paramDecl->type);
            } else if (uses_raw_kandr_aggregate_storage(paramDecl->type)) {
                storage_type = convert_type(paramDecl->type.get_shared());
            } else {
                storage_type = convert_type(paramDecl->type.get_shared());
            }
            llvm::AllocaInst* alloca = builder.CreateAlloca(storage_type, nullptr, mangled);
            llvm::Value* incoming = &arg;
            if (canonical_param_type && canonical_param_type->kind == TypeKind::Object &&
                has_direct_aggregate_parameter_abi(paramDecl->type) &&
                incoming->getType() != storage_type) {
                store_abi_value_into_aggregate_memory(
                    incoming,
                    alloca,
                    paramDecl->type,
                    paramDecl->location,
                    "emit_function_body()");
                named_values[mangled] = alloca;
                idx++;
                continue;
            }
            if (incoming->getType() != storage_type) {
                incoming = cast_llvm_type(incoming, storage_type, paramDecl->type->isUnsigned());
            }

            // Store the argument value into the alloca
            auto *store = builder.CreateStore(incoming, alloca);
            apply_store_qualifiers(store, paramDecl->type, module->getDataLayout());

            // Register in named_values map
            named_values[mangled] = alloca;
        }
        idx++;
    }

    // Evaluate VLA parameter size expressions (for side effects and sizeof)
    for (const auto& param : node->parameters) {
        auto *paramDecl = dyn_cast<ParamDecl>(param.get());
        if (!paramDecl) continue;
        if (paramDecl->original_type && type_contains_vla(paramDecl->original_type)) {
            cache_vla_sizes_for_type(paramDecl->original_type);
        }
    }

    if (auto* dtor_decl = dyn_cast<CppDestructorDecl>(node)) {
        auto fn_type =
            dyn_cast_shared<FunctionType>(desugar_type(dtor_decl->type, ast_ctx.get()));
        if (fn_type && !fn_type->parameters.empty() && mainFunc->arg_size() > 0) {
            auto this_ptr_type =
                desugar_type(fn_type->parameters.front(), ast_ctx.get())
                    .as_shared<PointerType>();
            if (this_ptr_type &&
                canonical_type_kind(this_ptr_type->pointed_type, ast_ctx.get()) ==
                    TypeKind::Object) {
                llvm::Value* this_addr = mainFunc->getArg(0);
                emit_cpp_vptr_store(
                    this_ptr_type->pointed_type,
                    this_addr,
                    dtor_decl->location,
                    "emit_function_body()");
                auto this_record_type =
                    desugar_type(this_ptr_type->pointed_type, ast_ctx.get())
                        .as_shared<ObjectType>();
                const ObjectDecl* this_record_decl = this_record_type
                    ? canonical_cpp_record_decl(
                        dyn_cast<ObjectDecl>(this_record_type->get_decl()))
                    : nullptr;
                const RecordSemanticState* this_record_state =
                    lookup_cpp_record_state(this_record_decl);
                if (this_record_state && !this_record_state->virtual_bases.empty()) {
                    emit_cpp_construction_vptr_store_from_vtt(
                        this_record_decl,
                        this_record_decl,
                        this_addr,
                        dtor_decl->location,
                        "emit_function_body()");
                }
            }
        }
    }

    auto emit_constructor_member_initializers = [&](CppConstructorDecl* ctor_decl) {
        if (!ctor_decl) {
            return;
        }

        llvm::Value* constructor_this_addr =
            mainFunc->arg_size() > 0 ? mainFunc->getArg(0) : nullptr;
        const ObjectDecl* constructor_record_decl = nullptr;
        const RecordSemanticState* constructor_record_state = nullptr;
        if (constructor_this_addr) {
            auto fn_type =
                dyn_cast_shared<FunctionType>(desugar_type(ctor_decl->type, ast_ctx.get()));
            if (fn_type && !fn_type->parameters.empty()) {
                auto this_ptr_type =
                    desugar_type(fn_type->parameters.front(), ast_ctx.get())
                        .as_shared<PointerType>();
                if (this_ptr_type) {
                    auto this_record_type =
                        desugar_type(this_ptr_type->pointed_type, ast_ctx.get())
                            .as_shared<ObjectType>();
                    if (this_record_type) {
                        constructor_record_decl =
                            canonical_cpp_record_decl(
                                dyn_cast<ObjectDecl>(this_record_type->get_decl()));
                        constructor_record_state =
                            lookup_cpp_record_state(constructor_record_decl);
                    }
                }
            }
        }
        const CppCtorInitializer* delegating_init = nullptr;
        for (const auto& mem_init : ctor_decl->ctor_initializers) {
            if (mem_init.is_delegating_initializer) {
                delegating_init = &mem_init;
                break;
            }
        }
        if (delegating_init) {
            if (!constructor_this_addr) {
                error("emit_function_body(): missing implicit object parameter for delegating constructor",
                      delegating_init->location);
                return;
            }
            auto* delegating_ctor_init =
                dyn_cast<CppConstructExpr>(delegating_init->init_expr.get());
            if (!delegating_ctor_init) {
                error("emit_function_body(): failed to lower delegating constructor initializer expression",
                      delegating_init->location);
                return;
            }
            if (!emit_cpp_construct_call(
                    delegating_ctor_init,
                    constructor_this_addr,
                    delegating_init->location,
                    "emit_function_body()",
                    special_member_variant)) {
                error("emit_function_body(): failed to lower delegating constructor call",
                      delegating_init->location);
            }
            return;
        }

        // Explicit base initializers win; otherwise we may synthesize an
        // implicit default-base constructor call when required by semantics.
        auto find_explicit_base_initializer =
            [&](const std::string& base_name) -> const CppCtorInitializer* {
            for (const auto& mem_init : ctor_decl->ctor_initializers) {
                if (!mem_init.is_base_initializer || !mem_init.init_expr) {
                    continue;
                }
                if (mem_init.member_name == base_name) {
                    return &mem_init;
                }
            }
            return nullptr;
        };
        auto select_default_base_constructor_symbol =
            [&](const ObjectDecl* base_record_decl) -> std::shared_ptr<Symbol> {
            if (!base_record_decl) {
                return nullptr;
            }
            const RecordSemanticState* base_state = lookup_cpp_record_state(base_record_decl);
            return select_record_default_constructor_symbol(
                base_state,
                /*require_public_access=*/false);
        };
        auto compute_base_this_addr =
            [&](const ObjectDecl* base_record_decl,
                bool is_virtual_base,
                const std::string& base_name,
                SrcLoc init_loc) -> llvm::Value* {
            if (!constructor_this_addr) {
                return nullptr;
            }
            llvm::Value* base_this_addr = constructor_this_addr;
            uint64_t subobject_offset = 0;
            bool has_offset = false;

            if (constructor_record_state) {
                if (is_virtual_base) {
                    for (const auto& virtual_base : constructor_record_state->virtual_bases) {
                        if (base_record_decl && virtual_base.record_decl &&
                            virtual_base.record_decl == base_record_decl) {
                            has_offset = virtual_base.has_offset;
                            subobject_offset = static_cast<uint64_t>(virtual_base.offset);
                            break;
                        }
                        if (!base_record_decl &&
                            !base_name.empty() &&
                            virtual_base.name == base_name) {
                            has_offset = virtual_base.has_offset;
                            subobject_offset = static_cast<uint64_t>(virtual_base.offset);
                            break;
                        }
                    }
                } else {
                    for (const auto& base : constructor_record_state->bases) {
                        if (base.is_virtual) {
                            continue;
                        }
                        if (base_record_decl && base.record_decl &&
                            base.record_decl == base_record_decl) {
                            has_offset = base.has_non_virtual_offset;
                            subobject_offset = static_cast<uint64_t>(base.non_virtual_offset);
                            break;
                        }
                        if (!base_record_decl &&
                            !base_name.empty() &&
                            base.name == base_name) {
                            has_offset = base.has_non_virtual_offset;
                            subobject_offset = static_cast<uint64_t>(base.non_virtual_offset);
                            break;
                        }
                    }
                }
            }

            if (!has_offset) {
                if (is_virtual_base) {
                    error("emit_function_body(): missing virtual-base offset for constructor initializer",
                          init_loc);
                } else {
                    error("emit_function_body(): missing direct-base offset for constructor initializer",
                          init_loc);
                }
                return nullptr;
            }
            if (subobject_offset == 0) {
                return base_this_addr;
            }

            llvm::Value* field_offset = llvm::ConstantInt::get(
                llvm::Type::getInt64Ty(*context),
                subobject_offset);
            base_this_addr = builder.CreateInBoundsGEP(
                llvm::Type::getInt8Ty(*context),
                constructor_this_addr,
                field_offset,
                "ctor.base.this");
            if (base_this_addr->getType() != constructor_this_addr->getType()) {
                base_this_addr = cast_llvm_type(
                    base_this_addr,
                    constructor_this_addr->getType(),
                    false);
            }
            return base_this_addr;
        };
        auto emit_base_initializer_call =
            [&](const std::string& base_name,
                const ObjectDecl* base_record_decl,
                bool is_virtual_base,
                const CppCtorInitializer* explicit_init,
                SrcLoc init_loc) {
            if (!constructor_this_addr || !base_record_decl) {
                return;
            }

            llvm::Value* base_this_addr = compute_base_this_addr(
                base_record_decl,
                is_virtual_base,
                base_name,
                init_loc);
            if (!base_this_addr) {
                return;
            }

            const CppConstructExpr* ctor_init = nullptr;
            std::unique_ptr<CppConstructExpr> implicit_ctor_init;
            if (explicit_init && explicit_init->init_expr) {
                ctor_init = dyn_cast<CppConstructExpr>(explicit_init->init_expr.get());
                if (!ctor_init) {
                    // Constructor-less class bases can lower to non-construct AST
                    // forms; in that case there is no callable ctor symbol to emit.
                    return;
                }
            } else {
                std::shared_ptr<Symbol> default_ctor_sym =
                    select_default_base_constructor_symbol(base_record_decl);
                if (!default_ctor_sym) {
                    if (!emit_cpp_object_default_construction_recursive(
                            QualType(base_record_decl->get_record_type()),
                            base_this_addr,
                            init_loc,
                            "emit_function_body()",
                            CppCtorDtorVariant::Base,
                            constructor_record_decl)) {
                        error("emit_function_body(): failed to lower implicit base default construction",
                              init_loc);
                    }
                    return;
                }
                implicit_ctor_init = std::make_unique<CppConstructExpr>(
                    default_ctor_sym,
                    std::vector<std::unique_ptr<Expr>>{},
                    QualType(base_record_decl->get_record_type()),
                    false,
                    init_loc);
                ctor_init = implicit_ctor_init.get();
            }

            if (constructor_record_decl &&
                constructor_record_state &&
                !constructor_record_state->virtual_bases.empty()) {
                emit_cpp_construction_vptr_store_from_vtt(
                    constructor_record_decl,
                    base_record_decl,
                    base_this_addr,
                    init_loc,
                    "emit_function_body()");
            }
            if (!emit_cpp_construct_call(
                    ctor_init,
                    base_this_addr,
                    init_loc,
                    "emit_function_body()",
                    CppCtorDtorVariant::Base)) {
                error("emit_function_body(): failed to lower constructor base initializer call",
                      init_loc);
            }
            if (constructor_record_decl &&
                constructor_record_state &&
                !constructor_record_state->virtual_bases.empty()) {
                emit_cpp_construction_vptr_store_from_vtt(
                    constructor_record_decl,
                    base_record_decl,
                    base_this_addr,
                    init_loc,
                    "emit_function_body()");
            }
        };

        if (constructor_record_state) {
            if (special_member_variant == CppCtorDtorVariant::Complete) {
                for (const auto& virtual_base : constructor_record_state->virtual_bases) {
                    const CppCtorInitializer* explicit_init =
                        find_explicit_base_initializer(virtual_base.name);
                    SrcLoc init_loc = explicit_init ? explicit_init->location
                                                    : ctor_decl->location;
                    emit_base_initializer_call(virtual_base.name,
                                               virtual_base.record_decl,
                                               true,
                                               explicit_init,
                                               init_loc);
                }
            }

            for (const auto& direct_base : constructor_record_state->bases) {
                if (direct_base.is_virtual) {
                    continue;
                }
                const CppCtorInitializer* explicit_init =
                    find_explicit_base_initializer(direct_base.name);
                SrcLoc init_loc = explicit_init ? explicit_init->location
                                                : ctor_decl->location;
                emit_base_initializer_call(direct_base.name,
                                           direct_base.record_decl,
                                           false,
                                           explicit_init,
                                           init_loc);
            }
        } else {
            for (const auto& mem_init : ctor_decl->ctor_initializers) {
                if (!mem_init.is_base_initializer || !mem_init.init_expr) {
                    continue;
                }
                auto* ctor_init = dyn_cast<CppConstructExpr>(mem_init.init_expr.get());
                if (!ctor_init || !constructor_this_addr) {
                    continue;
                }
                if (!emit_cpp_construct_call(
                        ctor_init,
                        constructor_this_addr,
                        mem_init.location,
                        "emit_function_body()",
                        CppCtorDtorVariant::Base)) {
                    error("emit_function_body(): failed to lower constructor base initializer call",
                          mem_init.location);
                }
            }
        }

        if (constructor_this_addr) {
            auto fn_type =
                dyn_cast_shared<FunctionType>(desugar_type(ctor_decl->type, ast_ctx.get()));
            if (fn_type && !fn_type->parameters.empty()) {
                auto this_ptr_type =
                    desugar_type(fn_type->parameters.front(), ast_ctx.get())
                        .as_shared<PointerType>();
                if (this_ptr_type &&
                    canonical_type_kind(this_ptr_type->pointed_type, ast_ctx.get()) ==
                        TypeKind::Object) {
                    emit_cpp_vptr_store(
                        this_ptr_type->pointed_type,
                        constructor_this_addr,
                        ctor_decl->location,
                        "emit_function_body()");
                    if (constructor_record_decl &&
                        constructor_record_state &&
                        !constructor_record_state->virtual_bases.empty()) {
                        emit_cpp_construction_vptr_store_from_vtt(
                            constructor_record_decl,
                            constructor_record_decl,
                            constructor_this_addr,
                            ctor_decl->location,
                            "emit_function_body()");
                    }
                }
            }
        }

        std::vector<const CppCtorInitializer*> ordered_inits;
        ordered_inits.reserve(ctor_decl->ctor_initializers.size());
        for (const auto& mem_init : ctor_decl->ctor_initializers) {
            if (mem_init.is_base_initializer) {
                continue;
            }
            ordered_inits.push_back(&mem_init);
        }

        auto member_order = [](const CppCtorInitializer* mem_init) {
            constexpr uint32_t kUnknownOrder = std::numeric_limits<uint32_t>::max();
            if (!mem_init) {
                return kUnknownOrder;
            }
            auto* member_expr = dyn_cast<MemberExpr>(mem_init->member_expr.get());
            if (!member_expr) {
                return kUnknownOrder;
            }
            if (!member_expr->field_path.empty()) {
                return member_expr->field_path.front();
            }
            return member_expr->field_index;
        };
        std::stable_sort(
            ordered_inits.begin(),
            ordered_inits.end(),
            [&](const auto* lhs, const auto* rhs) {
                return member_order(lhs) < member_order(rhs);
            });

        std::vector<bool> explicit_member_initialized(
            constructor_record_state ? constructor_record_state->fields.size() : 0,
            false);
        for (const auto* mem_init_ptr : ordered_inits) {
            if (!mem_init_ptr) {
                continue;
            }
            const auto& mem_init = *mem_init_ptr;
            auto* member_expr = dyn_cast<MemberExpr>(mem_init.member_expr.get());
            if (!member_expr || !member_expr->member_type || !mem_init.init_expr) {
                continue;
            }
            if (!member_expr->field_path.empty()) {
                size_t top_field_index = member_expr->field_path.front();
                if (top_field_index < explicit_member_initialized.size()) {
                    explicit_member_initialized[top_field_index] = true;
                }
            } else if (member_expr->field_index < explicit_member_initialized.size()) {
                explicit_member_initialized[member_expr->field_index] = true;
            }

            auto member_lvalue = get_lvalue(member_expr);
            llvm::Value* member_addr = member_lvalue.address;
            auto member_type = member_lvalue.type;
            if (!member_addr || !member_type) {
                error("emit_function_body(): failed to lower constructor member initializer destination",
                      mem_init.location);
                continue;
            }

            if (canonical_type_kind(member_type, ast_ctx.get()) == TypeKind::Reference) {
                Expr* binding_expr = unwrap_lvalue_to_rvalue_casts(mem_init.init_expr.get());

                llvm::Value* bound_addr = get_lvalue(binding_expr).address;
                if (!bound_addr) {
                    error("emit_function_body(): reference member initializer did not produce an address",
                          mem_init.location);
                    continue;
                }

                llvm::Type* reference_storage_type = convert_type(member_type);
                if (!reference_storage_type) {
                    error("emit_function_body(): failed to lower reference member type",
                          mem_init.location);
                    continue;
                }
                if (bound_addr->getType() != reference_storage_type) {
                    bound_addr = cast_llvm_type(bound_addr, reference_storage_type, false);
                }

                auto* store = builder.CreateStore(bound_addr, member_addr);
                (void)store;
                continue;
            }

            if (auto* ctor_init = dyn_cast<CppConstructExpr>(mem_init.init_expr.get())) {
                if (!emit_cpp_construct_call(ctor_init,
                                             member_addr,
                                             mem_init.location,
                                             "emit_function_body()")) {
                    error("emit_function_body(): failed to lower constructor member initializer call",
                          mem_init.location);
                }
                continue;
            }

            llvm::Value* init_val = convert_expression(mem_init.init_expr.get());
            if (!init_val) {
                error("emit_function_body(): failed to lower constructor member initializer expression",
                      mem_init.location);
                continue;
            }

            llvm::Type* member_llvm_type = convert_type(member_type);
            if (!member_llvm_type) {
                error("emit_function_body(): failed to lower constructor member initializer type",
                      mem_init.location);
                continue;
            }
            if (init_val->getType() != member_llvm_type) {
                init_val = cast_llvm_type(
                    init_val,
                    member_llvm_type,
                    member_type->isUnsigned());
            }

            auto* store = builder.CreateStore(init_val, member_addr);
            (void)store;
        }

        if (constructor_record_state && constructor_this_addr) {
            for (size_t field_index = 0;
                 field_index < constructor_record_state->fields.size();
                 ++field_index) {
                if (field_index < explicit_member_initialized.size() &&
                    explicit_member_initialized[field_index]) {
                    continue;
                }

                const auto& field = constructor_record_state->fields[field_index];
                if (field.is_bitfield || field.is_base_subobject ||
                    field.is_virtual_base_storage) {
                    continue;
                }

                auto field_record =
                    desugar_type(field.type, ast_ctx.get()).as_shared<ObjectType>();
                if (!field_record) {
                    continue;
                }

                llvm::Value* field_addr = constructor_this_addr;
                if (field.offset != 0) {
                    field_addr = builder.CreateInBoundsGEP(
                        llvm::Type::getInt8Ty(*context),
                        constructor_this_addr,
                        llvm::ConstantInt::get(
                            llvm::Type::getInt64Ty(*context),
                            static_cast<uint64_t>(field.offset)),
                        "ctor.implicit.member.addr");
                }

                if (!emit_cpp_object_default_construction_recursive(
                        field.type,
                        field_addr,
                        ctor_decl->location,
                        "emit_function_body()")) {
                    error("emit_function_body(): failed to lower implicit member default construction",
                          ctor_decl->location);
                }
            }
        }
    };

    bool function_enforces_noexcept_terminate =
        func_ctype_body &&
        func_ctype_body->exception_spec == FunctionExceptionSpecKind::NonThrowing;
    bool saved_noexcept_enforcement = enforce_noexcept_terminate_on_escape;
    enforce_noexcept_terminate_on_escape = function_enforces_noexcept_terminate;

    llvm::BasicBlock* noexcept_lpad_bb = nullptr;
    EhRegionFrame noexcept_region;
    if (function_enforces_noexcept_terminate) {
        llvm::Function* personality = get_or_create_eh_personality();
        if (!personality) {
            error("emit_function_body(): failed to lower EH personality function for noexcept enforcement",
                  loc);
            enforce_noexcept_terminate_on_escape = saved_noexcept_enforcement;
            return;
        }
        mainFunc->setPersonalityFn(personality);
        mainFunc->addFnAttr(
            llvm::Attribute::getWithUWTableKind(*context, llvm::UWTableKind::Sync));
        noexcept_lpad_bb = llvm::BasicBlock::Create(*context, "noexcept.lpad", mainFunc);
        noexcept_region.landing_pad_block = noexcept_lpad_bb;
        noexcept_region.cleanup_depth_snapshot = cleanup_stack.size();
        eh_region_stack.push_back(noexcept_region);
    }

    bool preserved_function_scope_cleanups = false;
    const auto* lambda_invoker_info =
        ast_ctx ? ast_ctx->get_cpp_lambda_invoker_info(node->node_id) : nullptr;
    if (lambda_invoker_info) {
        emit_cpp_lambda_invoker_body(node, mainFunc, loc, *lambda_invoker_info);
    } else if (node->body != nullptr) {
        if (auto* ctor_decl = dyn_cast<CppConstructorDecl>(node)) {
            emit_constructor_member_initializers(ctor_decl);
        }
        preserved_function_scope_cleanups = function_enforces_noexcept_terminate;
        if (auto* body_compound = dyn_cast<CompoundStmt>(node->body.get())) {
            convert_compound_statement(
                body_compound, preserved_function_scope_cleanups);
        } else {
            // Function-try-blocks may surface as a non-compound top-level body.
            // Mirror function-scope cleanup framing so catch cleanups and
            // noexcept escape handling still share the same cleanup stack model.
            cleanup_stack.emplace_back();
            preserved_function_scope_cleanups = true;
            convert_statement(node->body.get());
            if (!builder.GetInsertBlock()->getTerminator()) {
                emit_cleanups_for_scope();
            }
        }
        // empty block with no end return
        if (!builder.GetInsertBlock()->getTerminator()) {
            auto* retTy = mainFunc->getReturnType();
            if (retTy->isVoidTy()) {
                builder.CreateRetVoid();
            } else if (retTy->isPointerTy()) {
                builder.CreateRet(llvm::ConstantPointerNull::get(
                    llvm::cast<llvm::PointerType>(retTy)));
            } else if (retTy->isFloatingPointTy()) {
                builder.CreateRet(llvm::ConstantFP::get(retTy, 0.0));
            } else if (retTy->isIntegerTy()) {
                builder.CreateRet(llvm::ConstantInt::get(retTy, 0));
            } else {
                // Struct/aggregate return types: use zeroinitializer
                builder.CreateRet(llvm::Constant::getNullValue(retTy));
            }
        }
    } else {
        error("convert_function_declaration(): internal error, we shouldn't be here", loc);
        enforce_noexcept_terminate_on_escape = saved_noexcept_enforcement;
        return;
    }

    if (function_enforces_noexcept_terminate) {
        if (eh_region_stack.empty()) {
            error("emit_function_body(): internal EH region stack underflow during noexcept enforcement",
                  loc);
            enforce_noexcept_terminate_on_escape = saved_noexcept_enforcement;
            return;
        }
        eh_region_stack.pop_back();

        builder.SetInsertPoint(noexcept_lpad_bb);
        llvm::Type* ptr_ty = llvm::PointerType::get(*context, 0);
        auto* catch_all_clause = llvm::ConstantPointerNull::get(
            llvm::cast<llvm::PointerType>(ptr_ty));
        auto* lpad_ty = llvm::StructType::get(
            *context,
            {ptr_ty, llvm::Type::getInt32Ty(*context)});
        auto* lpad = builder.CreateLandingPad(lpad_ty, 1, "noexcept.catch");
        lpad->setCleanup(true);
        lpad->addClause(catch_all_clause);
        llvm::Value* exn_obj = builder.CreateExtractValue(lpad, {0}, "noexcept.exn");

        if (noexcept_region.cleanup_depth_snapshot < cleanup_stack.size()) {
            emit_cleanups_to_depth(noexcept_region.cleanup_depth_snapshot);
        }

        llvm::Function* begin_catch_fn = get_or_create_cxa_begin_catch();
        llvm::Function* terminate_fn = get_or_create_cxx_terminate();
        if (!begin_catch_fn || !terminate_fn) {
            error("emit_function_body(): failed to lower terminate hooks for noexcept enforcement",
                  loc);
            enforce_noexcept_terminate_on_escape = saved_noexcept_enforcement;
            return;
        }
        builder.CreateCall(begin_catch_fn, {exn_obj});
        builder.CreateCall(terminate_fn);
        builder.CreateUnreachable();
    }

    if (preserved_function_scope_cleanups && !cleanup_stack.empty()) {
        cleanup_stack.pop_back();
    }
    enforce_noexcept_terminate_on_escape = saved_noexcept_enforcement;
    builder.ClearInsertionPoint();
}

void ASTToLLVM::emit_cpp_lambda_invoker_body(
    FuncDecl* node,
    llvm::Function* mainFunc,
    SrcLoc loc,
    const CppLambdaInvokerInfo& invoker_info) {
    auto emit_fallback_return = [&]() {
        llvm::Type* ret_ty = mainFunc ? mainFunc->getReturnType() : nullptr;
        if (!ret_ty || ret_ty->isVoidTy()) {
            builder.CreateRetVoid();
        } else if (ret_ty->isPointerTy()) {
            builder.CreateRet(llvm::ConstantPointerNull::get(
                llvm::cast<llvm::PointerType>(ret_ty)));
        } else if (ret_ty->isFloatingPointTy()) {
            builder.CreateRet(llvm::ConstantFP::get(ret_ty, 0.0));
        } else if (ret_ty->isIntegerTy()) {
            builder.CreateRet(llvm::ConstantInt::get(ret_ty, 0));
        } else {
            builder.CreateRet(llvm::Constant::getNullValue(ret_ty));
        }
    };

    if (!node || !mainFunc || !invoker_info.call_operator_decl ||
        !invoker_info.closure_type) {
        error("emit_cpp_lambda_invoker_body(): missing synthesized lambda invoker metadata",
              loc);
        emit_fallback_return();
        return;
    }

    std::string call_operator_name =
        get_function_llvm_name(*invoker_info.call_operator_decl);
    llvm::Function* call_operator_fn = module->getFunction(call_operator_name);
    if (!call_operator_fn) {
        auto call_operator_type =
            dyn_cast_shared<FunctionType>(
                desugar_type(invoker_info.call_operator_decl->type, ast_ctx.get()));
        if (!call_operator_type) {
            error("emit_cpp_lambda_invoker_body(): invalid synthesized lambda call operator type",
                  loc);
            emit_fallback_return();
            return;
        }
        std::vector<llvm::Type*> param_types;
        param_types.reserve(call_operator_type->parameters.size());
        for (const auto& param_type : call_operator_type->parameters) {
            param_types.push_back(convert_param_type(param_type));
        }
        llvm::Type* return_type = convert_type(call_operator_type->ret_type);
        llvm::FunctionType* llvm_function_type = llvm::FunctionType::get(
            return_type,
            param_types,
            call_operator_type->is_variadic);
        auto linkage = invoker_info.call_operator_decl->is_inline
            ? llvm::Function::WeakAnyLinkage
            : llvm::Function::ExternalLinkage;
        call_operator_fn = llvm::Function::Create(
            llvm_function_type,
            linkage,
            call_operator_name,
            module.get());
        if (call_operator_type->exception_spec ==
            FunctionExceptionSpecKind::NonThrowing) {
            call_operator_fn->addFnAttr(llvm::Attribute::NoUnwind);
        }
    }

    llvm::Type* closure_llvm_type = convert_type(invoker_info.closure_type);
    if (!closure_llvm_type) {
        error("emit_cpp_lambda_invoker_body(): failed to lower closure type", loc);
        emit_fallback_return();
        return;
    }

    if (call_operator_fn->arg_size() != mainFunc->arg_size() + 1) {
        error("emit_cpp_lambda_invoker_body(): lambda invoker/call-operator ABI mismatch",
              loc);
        emit_fallback_return();
        return;
    }

    llvm::AllocaInst* closure_storage =
        create_entry_alloca(mainFunc, closure_llvm_type, nullptr, "__lambda.invoke.obj");
    if (!closure_storage) {
        error("emit_cpp_lambda_invoker_body(): failed to allocate closure storage", loc);
        emit_fallback_return();
        return;
    }
    builder.CreateStore(llvm::Constant::getNullValue(closure_llvm_type),
                        closure_storage);

    std::vector<llvm::Value*> call_args;
    call_args.reserve(mainFunc->arg_size() + 1);
    call_args.push_back(closure_storage);
    for (auto& arg : mainFunc->args()) {
        call_args.push_back(&arg);
    }

    llvm::CallInst* call_inst = nullptr;
    if (call_operator_fn->getReturnType()->isVoidTy()) {
        call_inst = builder.CreateCall(call_operator_fn, call_args);
        builder.CreateRetVoid();
    } else {
        call_inst = builder.CreateCall(call_operator_fn, call_args, "lambda.invoke");
        builder.CreateRet(call_inst);
    }

    auto call_operator_type =
        dyn_cast_shared<FunctionType>(
            desugar_type(invoker_info.call_operator_decl->type, ast_ctx.get()));
    if (call_inst && call_operator_type) {
        for (size_t param_index = 0;
             param_index < call_operator_type->parameters.size();
             ++param_index) {
            if (!pass_aggregate_by_reference(
                    call_operator_type->parameters[param_index])) {
                continue;
            }
            // Large by-value aggregates are already passed indirectly after an
            // explicit caller-side copy.
        }
    }
}

void ASTToLLVM::convert_function_declaration(Decl *decl) {
    auto llvm_storage = llvm::Function::ExternalLinkage;
    auto *node = dyn_cast<FuncDecl>(decl);
    if (!node) { error("convert_function_declaration(): unexpected subclass", decl->location); return; }
    const bool uses_gnu_inline_semantics = lang_opts.uses_gnu_inline_semantics();
    const bool is_c_inline =
        node->is_inline && !lang_opts.is_cxx_mode();
    const bool suppress_external_definition =
        is_c_inline &&
        node->storage_class != StorageClass::STATIC &&
        ((uses_gnu_inline_semantics && node->storage_class == StorageClass::EXTERN) ||
         (!uses_gnu_inline_semantics &&
          node->storage_class != StorageClass::EXTERN &&
          !node->has_prior_non_inline_declaration));
    if (node->storage_class == StorageClass::STATIC || suppress_external_definition) {
        llvm_storage = llvm::Function::InternalLinkage;
    }

    // Header-only inline definitions that suppress an external definition
    // still need a callable body when we are not running a dedicated inliner.
    // Give them internal linkage so a same-TU call can resolve locally without
    // exporting a global symbol from the object file.
    
    std::string llvm_name = get_function_llvm_name(*node);
    auto mainFunc = module->getFunction(llvm_name);
    // If existing LLVM function has a different param count and the new declaration
    // has a proper prototype (not K&R), replace the function with the correct signature.
    auto func_ctype_check = dyn_cast_shared<FunctionType>(node->type);
    auto get_abi_param_type = [&](const QualType& declared_type) -> QualType {
        if (func_ctype_check && !func_ctype_check->has_prototype) {
            return kr_abi_promote_param_type(declared_type, type_ctx);
        }
        return declared_type;
    };
    auto convert_function_param_type = [&](const QualType& declared_type) -> llvm::Type* {
        QualType abi_type = get_abi_param_type(declared_type);
        // For K&R (non-prototype) functions, keep aggregate params by-value so
        // call sites without prototype information stay ABI-compatible.
        auto abi_canonical = desugar_type(abi_type, ast_ctx.get());
        if (func_ctype_check && !func_ctype_check->has_prototype &&
            abi_canonical && abi_canonical->kind == TypeKind::Object &&
            (pass_aggregate_by_reference(abi_type) ||
             has_direct_aggregate_parameter_abi(abi_type))) {
            return convert_type(abi_type.get_shared());
        }
        return convert_param_type(abi_type);
    };
    size_t ast_param_count = node->parameters.size();
    if (ast_param_count == 1) {
        auto *pd = dyn_cast<ParamDecl>(node->parameters[0].get());
        if (pd && pd->type->isVoid()) ast_param_count = 0;
    }
    if (func_ctype_check && return_aggregate_indirectly(func_ctype_check->ret_type)) {
        ast_param_count += 1;
    }
    bool needs_signature_update =
        mainFunc && func_ctype_check && mainFunc->arg_size() != ast_param_count &&
        (func_ctype_check->has_prototype || ast_param_count > 0);
    if (needs_signature_update) {
        // Prior declaration may have come from empty parens (K&R style) and
        // later definition carries concrete parameters; rebuild with definition signature.
        auto* oldFunc = mainFunc;
        mainFunc = nullptr;

        // Create the new function with the correct signature
        std::vector<llvm::Type*> paramTypes;
        for (const auto& param : node->parameters) {
            auto *paramDecl = cast<ParamDecl>(param.get());
            if (paramDecl->type->isVoid()) break;
            paramTypes.push_back(convert_function_param_type(paramDecl->type));
        }
        auto func_ctype = dyn_cast_shared<FunctionType>(node->type);
        if (func_ctype == nullptr) { error("unexpected subclass in funcdecl->type", node->location); return; }
        prepend_indirect_result_parameter(paramTypes, func_ctype->ret_type);
        llvm::Type* returnType = convert_function_return_type(func_ctype->ret_type);
        llvm::FunctionType* funcType = llvm::FunctionType::get(returnType, paramTypes, func_ctype->is_variadic);
        mainFunc = llvm::Function::Create(funcType, llvm_storage, llvm_name, module.get());
        apply_indirect_result_attributes(mainFunc, 0, func_ctype->ret_type);

        // Replace all uses of the old function with the new one, then erase old
        oldFunc->replaceAllUsesWith(mainFunc);
        oldFunc->eraseFromParent();
        // Reclaim the original name (LLVM may have auto-suffixed the new function)
        mainFunc->setName(llvm_name);
    }
    if (mainFunc) {
        // Preserve an existing internal definition across later extern
        // redeclarations. Header patterns like `static inline` followed by an
        // `extern` prototype should keep the local definition local.
        if (mainFunc->getLinkage() != llvm::Function::InternalLinkage) {
            mainFunc->setLinkage(llvm_storage);
        }
    } else {
        // Create function type with parameters
        std::vector<llvm::Type*> paramTypes;
        for (const auto& param : node->parameters) {
            auto *paramDecl = cast<ParamDecl>(param.get());
            if (paramDecl->type->isVoid()) {
                // This should be the  one and only void, as verified by sema
                break;
            }
            // Use the type from the parameter declaration
            // If type is null (legacy), default to int32
            llvm::Type* type = convert_function_param_type(paramDecl->type);
            paramTypes.push_back(type);
        }
        auto func_ctype = dyn_cast_shared<FunctionType>(node->type);
        if (func_ctype == nullptr) { error("unexpected subclass in funcdecl->type", node->location); return; }
        prepend_indirect_result_parameter(paramTypes, func_ctype->ret_type);
        llvm::Type* returnType = convert_function_return_type(func_ctype->ret_type); // fall back to i32 if not

        llvm::FunctionType* funcType = llvm::FunctionType::get(returnType, paramTypes, func_ctype->is_variadic);
        mainFunc = llvm::Function::Create(funcType, llvm_storage,
            llvm_name, module.get());
        apply_indirect_result_attributes(mainFunc, 0, func_ctype->ret_type);
    }

    if (node->is_inline) {
        mainFunc->addFnAttr(llvm::Attribute::InlineHint);
    }
    if (func_ctype_check &&
        func_ctype_check->exception_spec == FunctionExceptionSpecKind::NonThrowing) {
        mainFunc->addFnAttr(llvm::Attribute::NoUnwind);
    }

    // Apply function attributes from __attribute__ specifiers
    // Pre-check for conflicts to avoid LLVM verification errors
    const auto& node_attrs = ast_ctx->get_attrs(node->node_id);
    bool has_noinline = node_attrs.has(AttributeKind::NOINLINE);
    bool has_cold = node_attrs.has(AttributeKind::COLD);
    for (const auto& attr : node_attrs.attrs) {
        switch (attr.resolved_kind) {
            case AttributeKind::NORETURN:
                mainFunc->addFnAttr(llvm::Attribute::NoReturn);
                break;
            case AttributeKind::NOINLINE:
                mainFunc->addFnAttr(llvm::Attribute::NoInline);
                break;
            case AttributeKind::ALWAYS_INLINE:
                // Skip if noinline is also present (noinline takes precedence)
                if (!has_noinline)
                    mainFunc->addFnAttr(llvm::Attribute::AlwaysInline);
                break;
            case AttributeKind::COLD:
                mainFunc->addFnAttr(llvm::Attribute::Cold);
                break;
            case AttributeKind::HOT:
                // Skip if cold is also present (cold takes precedence)
                if (!has_cold)
                    mainFunc->addFnAttr(llvm::Attribute::Hot);
                break;
            case AttributeKind::NOTHROW:
                mainFunc->addFnAttr(llvm::Attribute::NoUnwind);
                break;
            case AttributeKind::PURE:
                mainFunc->setOnlyReadsMemory();
                mainFunc->addFnAttr(llvm::Attribute::NoUnwind);
                break;
            case AttributeKind::CONST_ATTR:
                mainFunc->setDoesNotAccessMemory();
                mainFunc->addFnAttr(llvm::Attribute::NoUnwind);
                break;
            case AttributeKind::WARN_UNUSED_RESULT:
                // No direct LLVM attribute; handled by sema warnings
                break;
            case AttributeKind::WEAK:
                mainFunc->setLinkage(llvm::Function::WeakAnyLinkage);
                break;
            case AttributeKind::VISIBILITY: {
                if (!attr.args.empty() && attr.args[0].kind == AttributeArg::Kind::STRING) {
                    const auto& vis = attr.args[0].str_value;
                    if (vis == "default") mainFunc->setVisibility(llvm::GlobalValue::DefaultVisibility);
                    else if (vis == "hidden") mainFunc->setVisibility(llvm::GlobalValue::HiddenVisibility);
                    else if (vis == "protected") mainFunc->setVisibility(llvm::GlobalValue::ProtectedVisibility);
                }
                break;
            }
            case AttributeKind::SECTION: {
                if (!attr.args.empty() && attr.args[0].kind == AttributeArg::Kind::STRING) {
                    mainFunc->setSection(attr.args[0].str_value);
                }
                break;
            }
            case AttributeKind::ALIGNED: {
                if (!attr.args.empty() && attr.args[0].kind == AttributeArg::Kind::INTEGER) {
                    mainFunc->setAlignment(llvm::Align(static_cast<uint64_t>(attr.args[0].int_value)));
                }
                break;
            }
            case AttributeKind::CONSTRUCTOR: {
                int priority = 65535;
                if (!attr.args.empty() && attr.args[0].kind == AttributeArg::Kind::INTEGER) {
                    priority = static_cast<int>(attr.args[0].int_value);
                }
                if (node->body != nullptr) {
                    llvm::appendToGlobalCtors(*module, mainFunc, priority);
                }
                break;
            }
            case AttributeKind::DESTRUCTOR: {
                int priority = 65535;
                if (!attr.args.empty() && attr.args[0].kind == AttributeArg::Kind::INTEGER) {
                    priority = static_cast<int>(attr.args[0].int_value);
                }
                if (node->body != nullptr) {
                    llvm::appendToGlobalDtors(*module, mainFunc, priority);
                }
                break;
            }
            case AttributeKind::USED:
                llvm::appendToCompilerUsed(*module, {mainFunc});
                break;
            case AttributeKind::MALLOC_ATTR:
                mainFunc->addRetAttr(llvm::Attribute::NoAlias);
                break;
            case AttributeKind::RETURNS_NONNULL:
                mainFunc->addRetAttr(llvm::Attribute::NonNull);
                break;
            case AttributeKind::NONNULL: {
                if (attr.args.empty()) {
                    // Apply to all pointer parameters
                    for (unsigned i = 0; i < mainFunc->arg_size(); ++i) {
                        if (mainFunc->getArg(i)->getType()->isPointerTy())
                            mainFunc->addParamAttr(i, llvm::Attribute::NonNull);
                    }
                } else {
                    for (const auto& arg : attr.args) {
                        if (arg.kind == AttributeArg::Kind::INTEGER) {
                            unsigned idx = static_cast<unsigned>(arg.int_value - 1);
                            if (idx < mainFunc->arg_size())
                                mainFunc->addParamAttr(idx, llvm::Attribute::NonNull);
                        }
                    }
                }
                break;
            }
            default:
                break;
        }
    }

    llvm::Function* base_variant_func = nullptr;
    auto get_base_variant_name_for_decl = [&](const FuncDecl* fn_decl) -> std::string {
        if (!fn_decl) {
            return "";
        }
        if (isa<CppConstructorDecl>(fn_decl)) {
            return get_cpp_special_member_variant_llvm_name(
                get_function_llvm_name(*fn_decl),
                false,
                CppCtorDtorVariant::Base);
        }
        if (isa<CppDestructorDecl>(fn_decl)) {
            return get_cpp_special_member_variant_llvm_name(
                get_function_llvm_name(*fn_decl),
                true,
                CppCtorDtorVariant::Base);
        }
        return "";
    };
    std::string base_variant_name = get_base_variant_name_for_decl(node);
    if (!base_variant_name.empty() && base_variant_name != llvm_name) {
        base_variant_func = module->getFunction(base_variant_name);
        if (!base_variant_func) {
            base_variant_func = llvm::Function::Create(
                mainFunc->getFunctionType(),
                mainFunc->getLinkage(),
                base_variant_name,
                module.get());
        }
        if (base_variant_func) {
            base_variant_func->setCallingConv(mainFunc->getCallingConv());
            base_variant_func->setAttributes(mainFunc->getAttributes());
            base_variant_func->setVisibility(mainFunc->getVisibility());
            base_variant_func->setUnnamedAddr(mainFunc->getUnnamedAddr());
        }
    }

    const auto* lambda_invoker_info =
        ast_ctx ? ast_ctx->get_cpp_lambda_invoker_info(node->node_id) : nullptr;
    const auto* lambda_closure_info = [&]() -> const CppLambdaClosureDeclInfo* {
        if (!ast_ctx) {
            return nullptr;
        }
        auto owner_type =
            desugar_type(get_func_decl_owner_record_type(node), ast_ctx.get())
                .as_shared<ObjectType>();
        auto* owner_decl =
            owner_type ? dyn_cast<ObjectDecl>(owner_type->get_decl()) : nullptr;
        return owner_decl
            ? ast_ctx->get_cpp_lambda_closure_decl_info(owner_decl->node_id)
            : nullptr;
    }();
    const bool is_lambda_call_operator =
        lambda_closure_info &&
        lambda_closure_info->call_operator_decl == node;
    if ((lambda_invoker_info || is_lambda_call_operator) &&
        builder.GetInsertBlock() != nullptr) {
        if (deferred_inline_set.insert(node).second) {
            deferred_inline_defs.push_back(node);
        }
        return;
    }
    if (node->body == nullptr && !lambda_invoker_info) {
        // this a function declaration, nothing else to do
        return;
    }

    // Header-only inline definitions and unused static inline helpers should
    // only be emitted if they are actually referenced in this translation
    // unit. GNU inline definitions with a prior non-inline declaration still
    // need a real out-of-line definition, so keep emitting those eagerly.
    if (node->is_inline &&
        node->storage_class != StorageClass::EXTERN &&
        (suppress_external_definition ||
         node->storage_class == StorageClass::STATIC) &&
        mainFunc->empty() &&
        mainFunc->use_empty() &&
        (!base_variant_func || base_variant_func->use_empty())) {
        if (deferred_inline_set.insert(node).second) {
            deferred_inline_defs.push_back(node);
        }
        return;
    }

    emit_function_body(
        node, mainFunc, decl->location, CppCtorDtorVariant::Complete);
    if (base_variant_func && base_variant_func != mainFunc &&
        base_variant_func->empty()) {
        emit_function_body(
            node, base_variant_func, decl->location, CppCtorDtorVariant::Base);
    }
}
void ASTToLLVM::convert_declaration(Decl *decl) {
    if (!decl) {
        error("convert_declaration(): nullptr argument");
        return;
    }

    switch (decl->get_kind()) {
        case DeclKind::TemplateTypeParmDecl:
        case DeclKind::TemplateNonTypeParmDecl:
        case DeclKind::TemplateTemplateParmDecl:
        case DeclKind::AliasTemplateDecl:
        case DeclKind::FunctionTemplateDecl:
        case DeclKind::VariableTemplateDecl:
        case DeclKind::VariableTemplatePartialSpecializationDecl:
        case DeclKind::ClassTemplateDecl:
        case DeclKind::ClassTemplatePartialSpecializationDecl:
        case DeclKind::ConceptDecl:
            return;
        case DeclKind::TemplateExplicitSpecializationDecl: {
            auto* explicit_specialization =
                static_cast<TemplateExplicitSpecializationDecl*>(decl);
            convert_declaration(explicit_specialization->get_specialized_decl());
            return;
        }
        case DeclKind::FuncDecl:
        case DeclKind::CppMethodDecl:
        case DeclKind::CppConstructorDecl:
        case DeclKind::CppDestructorDecl:
            convert_function_declaration(static_cast<FuncDecl*>(decl));
            return;
        case DeclKind::VariableDecl:
            convert_variable_declaration(static_cast<VariableDecl*>(decl));
            return;
        case DeclKind::CppRecordDecl: {
            auto* cpp_record = static_cast<CppRecordDecl*>(decl);
            // Class declarations do not emit storage themselves, but method members
            // are lowered as regular functions.
            for (const auto& member : cpp_record->members) {
                switch (member->get_kind()) {
                    case DeclKind::CppMethodDecl:
                    case DeclKind::CppConstructorDecl:
                    case DeclKind::CppDestructorDecl:
                        convert_function_declaration(static_cast<FuncDecl*>(member.get()));
                        break;
                    default:
                        break;
                }
            }
            return;
        }
        case DeclKind::FieldDecl:
        case DeclKind::ObjectDecl:
        case DeclKind::EnumDecl:
        case DeclKind::CppAccessSpecDecl:
        case DeclKind::NamespaceDecl:
        case DeclKind::NopDecl:
            return;
        case DeclKind::TypedefDecl: {
            auto* typedef_decl = static_cast<TypedefDecl*>(decl);
            // Capture VLA bounds when a typedef declaration executes in block scope.
            if (builder.GetInsertBlock() != nullptr &&
                typedef_decl->type &&
                type_contains_vla(typedef_decl->type.get_shared())) {
                cache_vla_sizes_for_type(typedef_decl->type.get_shared());
            }
            return;
        }
        case DeclKind::FileScopeAsmDecl:
            convert_file_scope_asm(static_cast<FileScopeAsmDecl*>(decl));
            return;
        default:
            error("convert_declaration(): unexpected subclass", decl->location);
            return;
    }
}

void ASTToLLVM::emit_deferred_inline_definitions() {
    if (deferred_inline_defs.empty()) {
        return;
    }

    bool changed = true;
    while (changed) {
        changed = false;
        for (auto* node : deferred_inline_defs) {
            const bool is_lambda_invoker =
                ast_ctx && ast_ctx->get_cpp_lambda_invoker_info(node->node_id);
            if (!node || (!node->body && !is_lambda_invoker)) {
                continue;
            }
            std::string llvm_name = get_function_llvm_name(*node);
            auto* fn = module->getFunction(llvm_name);
            bool complete_needs_emission =
                fn && fn->empty() && !fn->use_empty();

            bool base_needs_emission = false;
            if (isa<CppConstructorDecl>(node) || isa<CppDestructorDecl>(node)) {
                std::string base_name = get_cpp_special_member_variant_llvm_name(
                    llvm_name,
                    isa<CppDestructorDecl>(node),
                    CppCtorDtorVariant::Base);
                if (!base_name.empty() && base_name != llvm_name) {
                    if (auto* base_fn = module->getFunction(base_name)) {
                        base_needs_emission = base_fn->empty() && !base_fn->use_empty();
                    }
                }
            }

            if (!complete_needs_emission && !base_needs_emission) {
                continue;
            }
            convert_function_declaration(node);
            changed = true;
        }
    }

    for (auto* node : deferred_inline_defs) {
        if (!node) {
            continue;
        }
        std::string llvm_name = get_function_llvm_name(*node);
        auto* fn = module->getFunction(llvm_name);
        if (fn && fn->empty() && fn->use_empty()) {
            fn->eraseFromParent();
        }
        if (isa<CppConstructorDecl>(node) || isa<CppDestructorDecl>(node)) {
            std::string base_name = get_cpp_special_member_variant_llvm_name(
                llvm_name,
                isa<CppDestructorDecl>(node),
                CppCtorDtorVariant::Base);
            if (!base_name.empty() && base_name != llvm_name) {
                if (auto* base_fn = module->getFunction(base_name);
                    base_fn && base_fn->empty() && base_fn->use_empty()) {
                    base_fn->eraseFromParent();
                }
            }
        }
    }
    deferred_inline_defs.clear();
    deferred_inline_set.clear();
}

void ASTToLLVM::convert_translation_unit(Decl *decl) {
    auto *translation_unit = dyn_cast<TranslationUnit>(decl);
    if (!translation_unit) { error("unexpected subclass in "
                                   "convert_translation_unit()", decl->location); return; }
    ASTContextSideTableScope side_table_scope(ast_ctx.get());

    if (emit_debug_info) {
        module->addModuleFlag(llvm::Module::Warning, "Debug Info Version", llvm::DEBUG_METADATA_VERSION);
        module->addModuleFlag(llvm::Module::Warning, "Dwarf Version", 4);
        di_builder = std::make_unique<llvm::DIBuilder>(*module);
        
        std::string filename = "main.c";
        if (sm) {
            auto loc = sm->getLogicalLocation(decl->location);
            if (!loc.file.empty()) {
                filename = loc.file;
            }
        }
        std::string directory = "."; 
        
        di_cu = di_builder->createCompileUnit(
            llvm::dwarf::DW_LANG_C99,
            di_builder->createFile(filename, directory),
            "Aburiscript",
            optimization_level != "0",
            "",
            0
        );
    }

    for (auto& decls: translation_unit->declarations) {
        deal_global_variable_declaration(decls.get());
    }
    if (ast_ctx) {
        for (const auto& retained_decl : ast_ctx->retained_external_decls()) {
            if (!retained_decl) {
                continue;
            }
            deal_global_variable_declaration(retained_decl.get());
        }
        for (const auto& specialization :
             ast_ctx->class_template_specializations()) {
            if (!specialization || specialization->instantiation_failed) {
                continue;
            }
            for (const auto& member_decl : specialization->member_decls) {
                if (!member_decl) {
                    continue;
                }
                deal_global_variable_declaration(member_decl.get());
            }
        }
    }
    // todo: do a pass just for global declarations with initlizations
    // deal_global_variable_declaration
    is_global_defined.clear();
    for (auto& decls: translation_unit->declarations) {
        convert_declaration(decls.get());
    }
    if (ast_ctx) {
        for (const auto& retained_decl : ast_ctx->retained_external_decls()) {
            if (!retained_decl) {
                continue;
            }
            convert_declaration(retained_decl.get());
        }
        for (const auto& specialization :
             ast_ctx->function_template_specializations()) {
            if (!specialization || !specialization->specialization_decl ||
                specialization->instantiation_failed) {
                continue;
            }
            convert_declaration(specialization->specialization_decl.get());
        }
        for (const auto& specialization :
             ast_ctx->class_template_specializations()) {
            if (!specialization || specialization->instantiation_failed) {
                continue;
            }
            for (const auto& member_decl : specialization->member_decls) {
                if (!member_decl) {
                    continue;
                }
                convert_declaration(member_decl.get());
            }
        }
    }
    emit_deferred_inline_definitions();

    if (emit_debug_info && di_builder) {
        di_builder->finalize();
    }
}

llvm::Function* ASTToLLVM::get_or_create_eh_personality() {
    const auto& hooks = get_active_eh_runtime_hooks(*this);
    auto* fn_ty = llvm::FunctionType::get(
        llvm::Type::getInt32Ty(*context),
        true);
    auto callee = module->getOrInsertFunction(hooks.personality, fn_ty);
    return llvm::dyn_cast<llvm::Function>(callee.getCallee());
}

llvm::Function* ASTToLLVM::get_or_create_cxa_allocate_exception() {
    const auto& hooks = get_active_eh_runtime_hooks(*this);
    llvm::Type* ptr_ty = llvm::PointerType::get(*context, 0);
    auto* fn_ty = llvm::FunctionType::get(
        ptr_ty,
        {llvm::Type::getInt64Ty(*context)},
        false);
    auto callee = module->getOrInsertFunction(hooks.allocate_exception, fn_ty);
    return llvm::dyn_cast<llvm::Function>(callee.getCallee());
}

llvm::Function* ASTToLLVM::get_or_create_cxa_throw() {
    const auto& hooks = get_active_eh_runtime_hooks(*this);
    llvm::Type* ptr_ty = llvm::PointerType::get(*context, 0);
    auto* fn_ty = llvm::FunctionType::get(
        llvm::Type::getVoidTy(*context),
        {ptr_ty, ptr_ty, ptr_ty},
        false);
    auto callee = module->getOrInsertFunction(hooks.throw_exception, fn_ty);
    auto* fn = llvm::dyn_cast<llvm::Function>(callee.getCallee());
    if (fn) {
        fn->addFnAttr(llvm::Attribute::NoReturn);
    }
    return fn;
}

llvm::Function* ASTToLLVM::get_or_create_cxa_rethrow() {
    const auto& hooks = get_active_eh_runtime_hooks(*this);
    auto* fn_ty = llvm::FunctionType::get(
        llvm::Type::getVoidTy(*context),
        false);
    auto callee = module->getOrInsertFunction(hooks.rethrow_exception, fn_ty);
    auto* fn = llvm::dyn_cast<llvm::Function>(callee.getCallee());
    if (fn) {
        fn->addFnAttr(llvm::Attribute::NoReturn);
    }
    return fn;
}

llvm::Function* ASTToLLVM::get_or_create_cxx_dynamic_cast() {
    const auto& hooks = get_active_eh_runtime_hooks(*this);
    llvm::Type* ptr_ty = llvm::PointerType::get(*context, 0);
    llvm::Type* intptr_ty = module->getDataLayout().getIntPtrType(*context, 0);
    auto* fn_ty = llvm::FunctionType::get(
        ptr_ty,
        {ptr_ty, ptr_ty, ptr_ty, intptr_ty},
        false);
    auto callee = module->getOrInsertFunction(hooks.dynamic_cast_symbol, fn_ty);
    auto* fn = llvm::dyn_cast<llvm::Function>(callee.getCallee());
    if (fn) {
        fn->addFnAttr(llvm::Attribute::NoUnwind);
    }
    return fn;
}

llvm::Function* ASTToLLVM::get_or_create_cxa_bad_cast() {
    const auto& hooks = get_active_eh_runtime_hooks(*this);
    auto* fn_ty = llvm::FunctionType::get(
        llvm::Type::getVoidTy(*context),
        false);
    auto callee = module->getOrInsertFunction(hooks.bad_cast, fn_ty);
    auto* fn = llvm::dyn_cast<llvm::Function>(callee.getCallee());
    if (fn) {
        fn->addFnAttr(llvm::Attribute::NoReturn);
    }
    return fn;
}

llvm::Function* ASTToLLVM::get_or_create_cxa_bad_typeid() {
    const auto& hooks = get_active_eh_runtime_hooks(*this);
    auto* fn_ty = llvm::FunctionType::get(
        llvm::Type::getVoidTy(*context),
        false);
    auto callee = module->getOrInsertFunction(hooks.bad_typeid, fn_ty);
    auto* fn = llvm::dyn_cast<llvm::Function>(callee.getCallee());
    if (fn) {
        fn->addFnAttr(llvm::Attribute::NoReturn);
    }
    return fn;
}

llvm::Function* ASTToLLVM::get_or_create_cxa_begin_catch() {
    const auto& hooks = get_active_eh_runtime_hooks(*this);
    llvm::Type* ptr_ty = llvm::PointerType::get(*context, 0);
    auto* fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty}, false);
    auto callee = module->getOrInsertFunction(hooks.begin_catch, fn_ty);
    return llvm::dyn_cast<llvm::Function>(callee.getCallee());
}

llvm::Function* ASTToLLVM::get_or_create_cxa_end_catch() {
    const auto& hooks = get_active_eh_runtime_hooks(*this);
    auto* fn_ty = llvm::FunctionType::get(
        llvm::Type::getVoidTy(*context),
        false);
    auto callee = module->getOrInsertFunction(hooks.end_catch, fn_ty);
    return llvm::dyn_cast<llvm::Function>(callee.getCallee());
}

llvm::Function* ASTToLLVM::get_or_create_cxx_terminate() {
    const auto& hooks = get_active_eh_runtime_hooks(*this);
    auto* fn_ty = llvm::FunctionType::get(
        llvm::Type::getVoidTy(*context),
        false);
    auto callee = module->getOrInsertFunction(hooks.terminate, fn_ty);
    auto* fn = llvm::dyn_cast<llvm::Function>(callee.getCallee());
    if (fn) {
        fn->addFnAttr(llvm::Attribute::NoReturn);
        fn->addFnAttr(llvm::Attribute::NoUnwind);
    }
    return fn;
}

llvm::Function* ASTToLLVM::get_or_create_unwind_resume() {
    const auto& hooks = get_active_eh_runtime_hooks(*this);
    llvm::Type* ptr_ty = llvm::PointerType::get(*context, 0);
    auto* fn_ty = llvm::FunctionType::get(
        llvm::Type::getVoidTy(*context),
        {ptr_ty},
        false);
    auto callee = module->getOrInsertFunction(hooks.unwind_resume, fn_ty);
    auto* fn = llvm::dyn_cast<llvm::Function>(callee.getCallee());
    if (fn) {
        fn->addFnAttr(llvm::Attribute::NoReturn);
    }
    return fn;
}

llvm::Function* ASTToLLVM::get_or_create_block_object_assign() {
    llvm::Type* ptr_ty = llvm::PointerType::get(*context, 0);
    auto* fn_ty = llvm::FunctionType::get(
        llvm::Type::getVoidTy(*context),
        {ptr_ty, ptr_ty, llvm::Type::getInt32Ty(*context)},
        false);
    auto callee = module->getOrInsertFunction("_Block_object_assign", fn_ty);
    return llvm::dyn_cast<llvm::Function>(callee.getCallee());
}

llvm::Function* ASTToLLVM::get_or_create_block_object_dispose() {
    llvm::Type* ptr_ty = llvm::PointerType::get(*context, 0);
    auto* fn_ty = llvm::FunctionType::get(
        llvm::Type::getVoidTy(*context),
        {ptr_ty, llvm::Type::getInt32Ty(*context)},
        false);
    auto callee = module->getOrInsertFunction("_Block_object_dispose", fn_ty);
    return llvm::dyn_cast<llvm::Function>(callee.getCallee());
}

bool ASTToLLVM::block_byref_requires_copy_dispose_helpers(
    QualType value_type) const {
    auto canonical =
        desugar_type(remove_reference(value_type, ast_ctx.get()), ast_ctx.get());
    return canonical && canonical->kind == TypeKind::BlockPointer;
}

uint32_t ASTToLLVM::block_object_field_flags_for_type(
    QualType value_type,
    bool byref_caller) const {
    auto canonical =
        desugar_type(remove_reference(value_type, ast_ctx.get()), ast_ctx.get());
    uint32_t flags = 0;
    if (canonical && canonical->kind == TypeKind::BlockPointer) {
        flags |= darwin_blocks::BLOCK_FIELD_IS_BLOCK;
    }
    if (flags != 0 && byref_caller) {
        flags |= darwin_blocks::BLOCK_BYREF_CALLER;
    }
    return flags;
}

llvm::Value* ASTToLLVM::get_block_byref_cell_address(const Symbol* sym,
                                                     SrcLoc loc,
                                                     const char* context_name) {
    if (!sym) {
        error(std::string(context_name) + ": missing __block symbol", loc);
        return nullptr;
    }
    std::string mangled = mangleCIdentifier(sym->uid);
    auto it = named_values.find(mangled);
    if (it == named_values.end() || !it->second) {
        error(std::string(context_name) + ": __block variable not allocated", loc);
        return nullptr;
    }
    return it->second;
}

llvm::Value* ASTToLLVM::get_block_byref_forwarding_cell(llvm::Value* cell_addr,
                                                        SrcLoc loc,
                                                        const char* context_name) {
    if (!cell_addr) {
        error(std::string(context_name) + ": missing __block cell address", loc);
        return nullptr;
    }

    llvm::Type* ptr_ty = llvm::PointerType::get(*context, 0);
    llvm::Type* i8_ty = llvm::Type::getInt8Ty(*context);
    llvm::Value* cell_i8 = builder.CreatePointerCast(cell_addr, ptr_ty,
                                                     "block.byref.cell");
    llvm::Value* forwarding_slot = builder.CreateConstGEP1_64(
        i8_ty,
        cell_i8,
        darwin_blocks::block_byref_layout().forwarding_offset,
        "block.byref.forwarding.slot");
    return builder.CreateLoad(ptr_ty, forwarding_slot, "block.byref.forwarding");
}

llvm::Value* ASTToLLVM::get_block_byref_payload_address(llvm::Value* cell_addr,
                                                        QualType value_type,
                                                        SrcLoc loc,
                                                        const char* context_name) {
    llvm::Value* forwarding_cell =
        get_block_byref_forwarding_cell(cell_addr, loc, context_name);
    if (!forwarding_cell) {
        return nullptr;
    }
    llvm::Type* i8_ty = llvm::Type::getInt8Ty(*context);
    uint32_t payload_offset = darwin_blocks::block_byref_payload_offset(
        block_byref_requires_copy_dispose_helpers(value_type));
    return builder.CreateConstGEP1_64(
        i8_ty,
        forwarding_cell,
        payload_offset,
        "block.byref.payload");
}

bool ASTToLLVM::should_emit_invoke_for_callee(llvm::Value* callee,
                                              const FunctionType* callee_type) const {
    if (eh_region_stack.empty() || !callee) {
        return false;
    }
    if (!eh_region_stack.back().landing_pad_block) {
        return false;
    }
    if (callee_type &&
        callee_type->exception_spec == FunctionExceptionSpecKind::NonThrowing) {
        return false;
    }
    llvm::Value* stripped = callee->stripPointerCasts();
    if (auto* fn = llvm::dyn_cast<llvm::Function>(stripped)) {
        if (fn->hasFnAttribute(llvm::Attribute::NoUnwind)) {
            return false;
        }
    }
    return true;
}

std::string ASTToLLVM::get_itanium_type_name_encoding(QualType type) const {
    if (!using_itanium_cxx_object_abi()) {
        return "";
    }

    type = desugar_type(remove_reference(type, ast_ctx.get()), ast_ctx.get());

    // EH/typeid matching intentionally ignores top-level qualifiers.
    type = type.without_qualifiers();
    if (!type) {
        return "";
    }

    if (auto builtin = dyn_cast_shared<BuiltinType>(type.get_shared())) {
        return get_itanium_builtin_type_code(builtin->builtin_kind);
    }

    if (auto pointer = dyn_cast_shared<PointerType>(type.get_shared())) {
        // Keep existing pointer support boundary: single-level pointers to
        // builtin pointees with pointee cv/restrict qualifiers.
        QualType pointee = desugar_type(pointer->pointed_type, ast_ctx.get());
        auto pointee_builtin = dyn_cast_shared<BuiltinType>(pointee.get_shared());
        if (!pointee_builtin) {
            return "";
        }

        std::string pointee_code =
            get_itanium_builtin_type_code(pointee_builtin->builtin_kind);
        if (pointee_code.empty()) {
            return "";
        }

        std::string encoding = "P";
        if (pointee.is_const()) {
            encoding += "K";
        }
        if (pointee.is_volatile()) {
            encoding += "V";
        }
        if (pointee.is_restrict()) {
            encoding += "r";
        }
        encoding += pointee_code;
        return encoding;
    }

    if (auto object = dyn_cast_shared<ObjectType>(type.get_shared())) {
        const TagDecl* tag_decl = object->get_decl();
        const ObjectDecl* object_decl =
            tag_decl ? canonical_cpp_record_decl(dyn_cast<ObjectDecl>(tag_decl))
                     : nullptr;
        if (!object_decl || object_decl->get_tag_name().empty()) {
            return "";
        }
        return mangle_type_name_itanium(type);
    }

    return "";
}

std::string ASTToLLVM::get_itanium_typeinfo_symbol(QualType type) const {
    std::string encoding = get_itanium_type_name_encoding(type);
    if (encoding.empty()) {
        return "";
    }
    return "_ZTI" + encoding;
}

llvm::GlobalVariable* ASTToLLVM::get_or_create_itanium_class_typeinfo_global(
    const ObjectDecl* record_decl) {
    if (!using_itanium_cxx_object_abi()) {
        return nullptr;
    }

    const ObjectDecl* canonical_decl = canonical_cpp_record_decl(record_decl);
    if (!canonical_decl) {
        return nullptr;
    }
    auto record_type = canonical_decl->get_record_type();
    if (!record_type) {
        return nullptr;
    }

    std::string type_encoding = get_itanium_type_name_encoding(QualType(record_type));
    if (type_encoding.empty()) {
        return nullptr;
    }
    std::string typeinfo_symbol = "_ZTI" + type_encoding;
    if (auto* existing = module->getNamedGlobal(typeinfo_symbol)) {
        if (existing->hasInitializer()) {
            return existing;
        }
    }

    const RecordSemanticState* state = lookup_cpp_record_state(canonical_decl);
    auto* ptr_ty = llvm::PointerType::get(*context, 0);
    auto* i64_ty = llvm::Type::getInt64Ty(*context);
    auto* i32_ty = llvm::Type::getInt32Ty(*context);

    std::string type_name_symbol = "_ZTS" + type_encoding;
    llvm::GlobalVariable* type_name_global = module->getNamedGlobal(type_name_symbol);
    llvm::Constant* type_name_init =
        llvm::ConstantDataArray::getString(*context, type_encoding, true);
    if (!type_name_global) {
        type_name_global = new llvm::GlobalVariable(
            *module,
            type_name_init->getType(),
            true,
            llvm::GlobalValue::LinkOnceODRLinkage,
            type_name_init,
            type_name_symbol);
        type_name_global->setUnnamedAddr(llvm::GlobalValue::UnnamedAddr::Global);
        type_name_global->setAlignment(llvm::Align(1));
    } else if (!type_name_global->hasInitializer() &&
               type_name_global->getValueType() == type_name_init->getType()) {
        type_name_global->setInitializer(type_name_init);
        type_name_global->setConstant(true);
        type_name_global->setLinkage(llvm::GlobalValue::LinkOnceODRLinkage);
        type_name_global->setUnnamedAddr(llvm::GlobalValue::UnnamedAddr::Global);
        type_name_global->setAlignment(llvm::Align(1));
    }

    std::vector<llvm::Constant*> base_descriptors;
    if (state) {
        base_descriptors.reserve(state->bases.size());
        for (const auto& base : state->bases) {
            if (!base.type || !base.record_decl) {
                continue;
            }
            llvm::GlobalVariable* base_typeinfo =
                get_or_create_itanium_typeinfo_global(base.type);
            if (!base_typeinfo) {
                continue;
            }

            int64_t base_offset = 0;
            if (base.is_virtual) {
                // Keep virtual-base hierarchy metadata explicit even before
                // runtime `dynamic_cast` consumes full vbase-index rules.
                const ObjectDecl* base_decl =
                    canonical_cpp_record_decl(base.record_decl);
                if (base_decl) {
                    for (const auto& virtual_base : state->virtual_bases) {
                        const ObjectDecl* virtual_base_decl =
                            canonical_cpp_record_decl(virtual_base.record_decl);
                        if (virtual_base_decl == base_decl &&
                            virtual_base.has_offset &&
                            virtual_base.offset <=
                                static_cast<size_t>(std::numeric_limits<int64_t>::max())) {
                            base_offset = static_cast<int64_t>(virtual_base.offset);
                            break;
                        }
                    }
                }
            } else if (base.has_non_virtual_offset &&
                       base.non_virtual_offset <=
                           static_cast<size_t>(std::numeric_limits<int64_t>::max())) {
                base_offset = static_cast<int64_t>(base.non_virtual_offset);
            }

            uint64_t flags = 0;
            if (base.is_virtual) {
                flags |= 0x1;
            }
            if (base.declared_access == RecordMemberAccess::Public) {
                flags |= 0x2;
            }

            int64_t offset_flags = static_cast<int64_t>(flags);
            if (base_offset <= std::numeric_limits<int64_t>::max() / 256 &&
                base_offset >= std::numeric_limits<int64_t>::min() / 256) {
                offset_flags = base_offset * 256 + static_cast<int64_t>(flags);
            }

            auto* base_desc_ty = llvm::StructType::get(*context, {ptr_ty, i64_ty});
            llvm::Constant* base_desc = llvm::ConstantStruct::get(
                base_desc_ty,
                {llvm::ConstantExpr::getBitCast(base_typeinfo, ptr_ty),
                 llvm::ConstantInt::get(i64_ty, offset_flags, true)});
            base_descriptors.push_back(base_desc);
        }
    }

    const bool use_vmi = !base_descriptors.empty();
    const char* typeinfo_vtable_symbol = use_vmi
        ? "_ZTVN10__cxxabiv121__vmi_class_type_infoE"
        : "_ZTVN10__cxxabiv117__class_type_infoE";
    llvm::GlobalVariable* typeinfo_vtable = module->getNamedGlobal(typeinfo_vtable_symbol);
    if (!typeinfo_vtable) {
        auto* vtable_ty = llvm::ArrayType::get(ptr_ty, 0);
        typeinfo_vtable = new llvm::GlobalVariable(
            *module,
            vtable_ty,
            false,
            llvm::GlobalValue::ExternalLinkage,
            nullptr,
            typeinfo_vtable_symbol);
    }
    llvm::Constant* addr_point_index =
        llvm::ConstantInt::get(llvm::Type::getInt64Ty(*context), 2);
    std::array<llvm::Constant*, 1> vtable_gep = {addr_point_index};
    llvm::Constant* typeinfo_vptr =
        llvm::ConstantExpr::getInBoundsGetElementPtr(
            ptr_ty,
            typeinfo_vtable,
            llvm::ArrayRef<llvm::Constant*>(vtable_gep));

    llvm::GlobalVariable* typeinfo_global = module->getNamedGlobal(typeinfo_symbol);
    llvm::Constant* typeinfo_init = nullptr;
    llvm::Type* typeinfo_ty = nullptr;
    if (!use_vmi) {
        typeinfo_ty = llvm::StructType::get(*context, {ptr_ty, ptr_ty});
        typeinfo_init = llvm::ConstantStruct::get(
            llvm::cast<llvm::StructType>(typeinfo_ty),
            {typeinfo_vptr,
             llvm::ConstantExpr::getBitCast(type_name_global, ptr_ty)});
    } else {
        auto* base_desc_ty = llvm::StructType::get(*context, {ptr_ty, i64_ty});
        auto* base_array_ty = llvm::ArrayType::get(base_desc_ty, base_descriptors.size());
        auto* base_array_init = llvm::ConstantArray::get(base_array_ty, base_descriptors);
        typeinfo_ty = llvm::StructType::get(
            *context,
            {ptr_ty, ptr_ty, i32_ty, i32_ty, base_array_ty});
        typeinfo_init = llvm::ConstantStruct::get(
            llvm::cast<llvm::StructType>(typeinfo_ty),
            {typeinfo_vptr,
             llvm::ConstantExpr::getBitCast(type_name_global, ptr_ty),
             llvm::ConstantInt::get(i32_ty, 0),
             llvm::ConstantInt::get(i32_ty, static_cast<uint32_t>(base_descriptors.size())),
             base_array_init});
    }

    if (!typeinfo_global) {
        typeinfo_global = new llvm::GlobalVariable(
            *module,
            typeinfo_ty,
            true,
            llvm::GlobalValue::LinkOnceODRLinkage,
            typeinfo_init,
            typeinfo_symbol);
    } else if (!typeinfo_global->hasInitializer() &&
               typeinfo_global->getValueType() == typeinfo_ty) {
        typeinfo_global->setInitializer(typeinfo_init);
        typeinfo_global->setConstant(true);
        typeinfo_global->setLinkage(llvm::GlobalValue::LinkOnceODRLinkage);
    }

    if (typeinfo_global) {
        typeinfo_global->setUnnamedAddr(llvm::GlobalValue::UnnamedAddr::Global);
        typeinfo_global->setAlignment(module->getDataLayout().getPointerABIAlignment(0));
    }
    return typeinfo_global;
}

llvm::GlobalVariable* ASTToLLVM::get_or_create_itanium_typeinfo_global(QualType type) {
    if (!using_itanium_cxx_object_abi()) {
        return nullptr;
    }

    type = desugar_type(remove_reference(type, ast_ctx.get()), ast_ctx.get());
    type = type.without_qualifiers();
    if (!type) {
        return nullptr;
    }

    if (auto object = dyn_cast_shared<ObjectType>(type.get_shared())) {
        const TagDecl* tag_decl = object->get_decl();
        const ObjectDecl* object_decl =
            tag_decl ? canonical_cpp_record_decl(dyn_cast<ObjectDecl>(tag_decl))
                     : nullptr;
        if (object_decl) {
            return get_or_create_itanium_class_typeinfo_global(object_decl);
        }
    }

    std::string typeinfo_symbol = get_itanium_typeinfo_symbol(type);
    if (typeinfo_symbol.empty()) {
        return nullptr;
    }
    if (auto* existing = module->getNamedGlobal(typeinfo_symbol)) {
        return existing;
    }

    return new llvm::GlobalVariable(
        *module,
        llvm::Type::getInt8Ty(*context),
        true,
        llvm::GlobalValue::ExternalLinkage,
        nullptr,
        typeinfo_symbol);
}
