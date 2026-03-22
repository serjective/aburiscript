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
const EhRuntimeHooks& get_active_eh_runtime_hooks(const ASTToLLVM& codegen) {
    if (codegen.ast_ctx && codegen.ast_ctx->abi_policy) {
        return codegen.ast_ctx->abi_policy->eh_runtime_hooks;
    }
    static const EhRuntimeHooks defaults =
        eh_runtime_hooks_for_kind(EhRuntimeKind::LLVM);
    return defaults;
}
}

void ASTToLLVM::convert_cpp_try_statement(CppTryStmt *stmt) {
    if (!stmt || !stmt->try_block) {
        error("convert_cpp_try_statement(): invalid try statement", stmt ? stmt->location : SrcLoc());
        return;
    }
    llvm::Function* function = builder.GetInsertBlock()
        ? builder.GetInsertBlock()->getParent()
        : nullptr;
    if (!function) {
        error("convert_cpp_try_statement(): not inside a function", stmt->location);
        return;
    }

    if (stmt->handlers.empty()) {
        error("convert_cpp_try_statement(): try statement requires at least one catch handler",
            stmt->location);
        return;
    }

    llvm::Function* personality = get_or_create_eh_personality();
    if (!personality) {
        error("convert_cpp_try_statement(): failed to lower EH personality function",
            stmt->location);
        return;
    }
    function->setPersonalityFn(personality);
    function->addFnAttr(
        llvm::Attribute::getWithUWTableKind(*context, llvm::UWTableKind::Sync));
    if (!enforce_noexcept_terminate_on_escape) {
        function->removeFnAttr(llvm::Attribute::NoUnwind);
    }

    auto* try_body_bb = llvm::BasicBlock::Create(*context, "try.body", function);
    auto* lpad_bb = llvm::BasicBlock::Create(*context, "try.lpad", function);
    auto* continue_bb = llvm::BasicBlock::Create(*context, "try.cont", function);

    if (!builder.GetInsertBlock()->getTerminator()) {
        builder.CreateBr(try_body_bb);
    }
    builder.SetInsertPoint(try_body_bb);

    EhRegionFrame region;
    region.landing_pad_block = lpad_bb;
    region.cleanup_depth_snapshot = cleanup_stack.size();
    eh_region_stack.push_back(region);
    convert_statement(stmt->try_block.get());
    eh_region_stack.pop_back();
    if (!builder.GetInsertBlock()->getTerminator()) {
        builder.CreateBr(continue_bb);
    }

    builder.SetInsertPoint(lpad_bb);
    llvm::Type* ptr_ty = llvm::PointerType::get(*context, 0);
    auto* catch_all_clause = llvm::ConstantPointerNull::get(
        llvm::cast<llvm::PointerType>(ptr_ty));

    struct CatchLoweringInfo {
        const CppCatchClause* clause = nullptr;
        llvm::GlobalVariable* typeinfo_global = nullptr;
        llvm::BasicBlock* handler_block = nullptr;
    };
    std::vector<CatchLoweringInfo> catch_infos;
    catch_infos.reserve(stmt->handlers.size());
    size_t landing_pad_clause_count = 0;
    for (const auto& handler : stmt->handlers) {
        CatchLoweringInfo info;
        info.clause = &handler;
        info.handler_block = llvm::BasicBlock::Create(*context, "catch.handler", function);
        if (!handler.is_catch_all) {
            llvm::GlobalVariable* typeinfo_global =
                get_or_create_itanium_typeinfo_global(handler.exception_type);
            if (!typeinfo_global) {
                error("typed catch codegen cannot materialize RTTI typeinfo for handler type",
                    handler.location);
                return;
            }
            info.typeinfo_global = typeinfo_global;
        }
        catch_infos.push_back(info);
        ++landing_pad_clause_count;
    }

    auto* lpad_ty = llvm::StructType::get(
        *context,
        {ptr_ty, llvm::Type::getInt32Ty(*context)});
    auto* lpad = builder.CreateLandingPad(
        lpad_ty, static_cast<unsigned>(landing_pad_clause_count), "lpad");
    lpad->setCleanup(true);
    for (const auto& catch_info : catch_infos) {
        if (catch_info.clause && catch_info.clause->is_catch_all) {
            lpad->addClause(catch_all_clause);
            continue;
        }
        if (!catch_info.typeinfo_global) {
            error("convert_cpp_try_statement(): missing typeinfo for typed catch handler",
                catch_info.clause ? catch_info.clause->location : stmt->location);
            return;
        }
        lpad->addClause(catch_info.typeinfo_global);
    }
    llvm::Value* exn_obj = builder.CreateExtractValue(lpad, {0}, "exn.obj");
    llvm::Value* exn_selector = builder.CreateExtractValue(lpad, {1}, "exn.sel");

    if (region.cleanup_depth_snapshot < cleanup_stack.size()) {
        emit_cleanups_to_depth(region.cleanup_depth_snapshot);
    }

    llvm::Function* begin_catch_fn = get_or_create_cxa_begin_catch();
    llvm::Function* end_catch_fn = get_or_create_cxa_end_catch();
    if (!begin_catch_fn || !end_catch_fn) {
        error("convert_cpp_try_statement(): failed to lower C++ EH runtime hooks",
            stmt->location);
        return;
    }

    auto* eh_typeid_for_fn = llvm::Intrinsic::getDeclaration(
        module.get(), llvm::Intrinsic::eh_typeid_for);
    if (!eh_typeid_for_fn) {
        error("convert_cpp_try_statement(): failed to lower llvm.eh.typeid.for intrinsic",
            stmt->location);
        return;
    }

    auto bind_catch_parameter =
        [&](const CppCatchClause& clause, llvm::Value* catch_obj_addr) {
            if (!clause.exception_symbol || clause.exception_symbol->uid.empty()) {
                return;
            }
            QualType canonical =
                desugar_type(clause.exception_type, ast_ctx.get());
            bool binds_reference =
                canonical_type_kind(canonical, ast_ctx.get()) ==
                TypeKind::Reference;
            QualType payload_type = desugar_type(
                remove_reference(canonical, ast_ctx.get()),
                ast_ctx.get());
            if (!payload_type) {
                error("convert_cpp_try_statement(): invalid typed catch payload type",
                    clause.location);
                return;
            }
            llvm::Type* payload_llvm_type = convert_type(payload_type.get_shared());
            if (!payload_llvm_type) {
                error("convert_cpp_try_statement(): failed to lower typed catch payload type",
                    clause.location);
                return;
            }

            auto* payload_ptr_type = llvm::PointerType::get(*context, 0);
            llvm::Value* payload_addr = builder.CreateBitCast(
                catch_obj_addr, payload_ptr_type, "catch.payload.addr");
            bool payload_is_pointer =
                canonical_type_kind(payload_type, ast_ctx.get()) ==
                TypeKind::Pointer;
            std::string mangled = mangleCIdentifier(clause.exception_symbol->uid);
            if (binds_reference) {
                if (payload_is_pointer) {
                    error("convert_cpp_try_statement(): pointer-reference catch parameters are not yet supported in codegen",
                        clause.location);
                    return;
                }
                named_values[mangled] = payload_addr;
                return;
            }

            llvm::Value* catch_slot = create_entry_alloca(
                function, payload_llvm_type, nullptr, mangled + ".catch.tmp");
            if (!catch_slot) {
                error("convert_cpp_try_statement(): failed to allocate catch slot",
                      clause.location);
                return;
            }
            llvm::Value* payload_value = nullptr;
            if (payload_is_pointer) {
                // For pointer catches __cxa_begin_catch returns the pointer payload
                // value itself, not an address to load a second pointer from.
                payload_value = catch_obj_addr;
                if (payload_value->getType() != payload_llvm_type) {
                    payload_value = builder.CreateBitCast(
                        payload_value, payload_llvm_type, "catch.payload.ptr");
                }
            } else {
                payload_value = builder.CreateLoad(
                    payload_llvm_type, payload_addr, "catch.payload");
            }
            builder.CreateStore(payload_value, catch_slot);
            named_values[mangled] = catch_slot;
        };

    auto emit_handler_body = [&](const CatchLoweringInfo& catch_info) {
        builder.SetInsertPoint(catch_info.handler_block);
        llvm::Value* catch_obj = builder.CreateCall(
            begin_catch_fn, {exn_obj}, "catch.obj");
        if (catch_info.clause && !catch_info.clause->is_catch_all) {
            bind_catch_parameter(*catch_info.clause, catch_obj);
        }

        std::vector<CleanupEntry>* scope_cleanups =
            cleanup_stack.empty() ? nullptr : &cleanup_stack.back();
        size_t scope_cleanup_mark = scope_cleanups ? scope_cleanups->size() : 0;
        if (scope_cleanups) {
            const auto& hooks = get_active_eh_runtime_hooks(*this);
            CleanupEntry catch_cleanup;
            catch_cleanup.kind = CleanupEntry::Kind::CallNoArgs;
            catch_cleanup.cleanup_func = hooks.end_catch;
            catch_cleanup.location = catch_info.clause
                ? catch_info.clause->location
                : stmt->location;
            scope_cleanups->push_back(std::move(catch_cleanup));
        }

        if (catch_info.clause && catch_info.clause->handler) {
            convert_statement(catch_info.clause->handler.get());
        }

        if (scope_cleanups) {
            scope_cleanups->resize(scope_cleanup_mark);
        }
        if (!builder.GetInsertBlock()->getTerminator()) {
            builder.CreateCall(end_catch_fn);
            builder.CreateBr(continue_bb);
        }
    };

    auto* dispatch_bb = llvm::BasicBlock::Create(*context, "catch.dispatch", function);
    builder.CreateBr(dispatch_bb);
    builder.SetInsertPoint(dispatch_bb);

    auto* no_match_bb = llvm::BasicBlock::Create(*context, "catch.nomatch", function);
    for (size_t idx = 0; idx < catch_infos.size(); ++idx) {
        const auto& catch_info = catch_infos[idx];
        if (catch_info.clause && catch_info.clause->is_catch_all) {
            builder.CreateBr(catch_info.handler_block);
            break;
        }
        if (!catch_info.typeinfo_global) {
            error("convert_cpp_try_statement(): typed catch is missing RTTI symbol",
                catch_info.clause ? catch_info.clause->location : stmt->location);
            return;
        }

        llvm::Value* type_id = builder.CreateCall(
            eh_typeid_for_fn,
            {catch_info.typeinfo_global},
            "catch.typeid");
        llvm::Value* matches = builder.CreateICmpEQ(
            exn_selector,
            type_id,
            "catch.match");

        auto* next_dispatch_bb = llvm::BasicBlock::Create(
            *context, "catch.next", function);
        builder.CreateCondBr(matches, catch_info.handler_block, next_dispatch_bb);
        builder.SetInsertPoint(next_dispatch_bb);
    }

    if (!builder.GetInsertBlock()->getTerminator()) {
        builder.CreateBr(no_match_bb);
    }

    builder.SetInsertPoint(no_match_bb);
    if (enforce_noexcept_terminate_on_escape) {
        llvm::Function* begin_catch_fn = get_or_create_cxa_begin_catch();
        llvm::Function* terminate_fn = get_or_create_cxx_terminate();
        if (!begin_catch_fn || !terminate_fn) {
            error("convert_cpp_try_statement(): failed to lower terminate hooks for noexcept escape",
                stmt->location);
            return;
        }
        builder.CreateCall(begin_catch_fn, {exn_obj});
        builder.CreateCall(terminate_fn);
        builder.CreateUnreachable();
    } else {
        builder.CreateResume(lpad);
    }

    for (const auto& catch_info : catch_infos) {
        emit_handler_body(catch_info);
    }

    builder.SetInsertPoint(continue_bb);
}

llvm::Value* ASTToLLVM::convert_cpp_throw_expression(CppThrowExpr *expr) {
    if (!expr) {
        error("convert_cpp_throw_expression(): invalid throw expression");
        return nullptr;
    }
    llvm::Function* function = builder.GetInsertBlock()
        ? builder.GetInsertBlock()->getParent()
        : nullptr;
    if (function) {
        function->addFnAttr(
            llvm::Attribute::getWithUWTableKind(*context, llvm::UWTableKind::Sync));
        if (!enforce_noexcept_terminate_on_escape) {
            function->removeFnAttr(llvm::Attribute::NoUnwind);
        }
    }
    llvm::Type* ptr_ty = llvm::PointerType::get(*context, 0);

    if (expr->is_rethrow) {
        llvm::Function* cxa_rethrow_fn = get_or_create_cxa_rethrow();
        if (!cxa_rethrow_fn) {
            error("convert_cpp_throw_expression(): failed to lower __cxa_rethrow",
                expr->location);
            return nullptr;
        }
        if (should_emit_invoke_for_callee(cxa_rethrow_fn)) {
            auto* cont_bb = llvm::BasicBlock::Create(*context, "rethrow.cont", function);
            auto* unwind_bb = eh_region_stack.back().landing_pad_block;
            builder.CreateInvoke(cxa_rethrow_fn->getFunctionType(),
                cxa_rethrow_fn,
                cont_bb,
                unwind_bb,
                {});
            builder.SetInsertPoint(cont_bb);
        } else {
            builder.CreateCall(cxa_rethrow_fn);
        }
        builder.CreateUnreachable();
        auto* after_throw_bb = llvm::BasicBlock::Create(
            *context, "after_throw", builder.GetInsertBlock()->getParent());
        builder.SetInsertPoint(after_throw_bb);
        return llvm::UndefValue::get(convert_type(expr->get_type()));
    }

    if (!expr->thrown_expr) {
        error("convert_cpp_throw_expression(): missing throw operand", expr->location);
        return nullptr;
    }
    llvm::Value* thrown_val = convert_expression(expr->thrown_expr.get());
    if (!thrown_val) {
        error("convert_cpp_throw_expression(): failed to lower throw operand",
            expr->location);
        return nullptr;
    }

    llvm::GlobalVariable* typeinfo_global =
        get_or_create_itanium_typeinfo_global(expr->thrown_expr->get_type());
    if (!typeinfo_global) {
        error("throw codegen cannot materialize RTTI typeinfo for operand type",
            expr->location);
        return nullptr;
    }

    uint64_t throw_size = module->getDataLayout().getTypeAllocSize(thrown_val->getType());
    llvm::Function* cxa_alloc_fn = get_or_create_cxa_allocate_exception();
    llvm::Function* cxa_throw_fn = get_or_create_cxa_throw();
    if (!cxa_alloc_fn || !cxa_throw_fn) {
        error("convert_cpp_throw_expression(): failed to lower C++ EH runtime hooks",
            expr->location);
        return nullptr;
    }
    llvm::Value* exc_obj = builder.CreateCall(
        cxa_alloc_fn,
        {llvm::ConstantInt::get(llvm::Type::getInt64Ty(*context), throw_size)},
        "exc.obj");
    builder.CreateStore(thrown_val, exc_obj);
    llvm::Value* destructor_fn = llvm::ConstantPointerNull::get(
        llvm::cast<llvm::PointerType>(ptr_ty));
    std::array<llvm::Value*, 3> throw_args = {
        exc_obj,
        typeinfo_global,
        destructor_fn
    };

    if (should_emit_invoke_for_callee(cxa_throw_fn)) {
        auto* cont_bb = llvm::BasicBlock::Create(*context, "throw.cont", function);
        auto* unwind_bb = eh_region_stack.back().landing_pad_block;
        builder.CreateInvoke(cxa_throw_fn->getFunctionType(),
            cxa_throw_fn,
            cont_bb,
            unwind_bb,
            throw_args);
        builder.SetInsertPoint(cont_bb);
    } else {
        builder.CreateCall(cxa_throw_fn, throw_args);
    }

    builder.CreateUnreachable();
    auto* after_throw_bb = llvm::BasicBlock::Create(
        *context, "after_throw", builder.GetInsertBlock()->getParent());
    builder.SetInsertPoint(after_throw_bb);
    return llvm::UndefValue::get(convert_type(expr->get_type()));
}

llvm::Value* ASTToLLVM::emit_cpp_operator_call(
    const std::shared_ptr<Symbol>& callee_sym,
    const std::vector<std::pair<llvm::Value*, QualType>>& args,
    SrcLoc loc,
    const std::string& context_name) {
    if (!callee_sym || callee_sym->kind != SymbolKind::FUNCTION) {
        error(context_name + ": selected operator symbol is invalid", loc);
        return nullptr;
    }

    auto fn_type =
        desugar_type(callee_sym->type, ast_ctx.get()).as_shared<FunctionType>();
    if (!fn_type) {
        auto ptr_type =
            desugar_type(callee_sym->type, ast_ctx.get()).as_shared<PointerType>();
        if (ptr_type) {
            fn_type = desugar_type(ptr_type->pointed_type, ast_ctx.get())
                          .as_shared<FunctionType>();
        }
    }
    if (!fn_type) {
        error(context_name + ": selected operator has non-function type", loc);
        return nullptr;
    }

    bool has_void_param = fn_type->parameters.size() == 1 &&
                          fn_type->parameters[0] &&
                          fn_type->parameters[0]->isVoid();
    size_t named_param_count = has_void_param ? 0 : fn_type->parameters.size();
    if (fn_type->has_prototype) {
        if (fn_type->is_variadic) {
            if (args.size() < named_param_count) {
                error(context_name + ": insufficient operator arguments", loc);
                return nullptr;
            }
        } else if (args.size() != named_param_count) {
            error(context_name + ": operator argument count mismatch after sema", loc);
            return nullptr;
        }
    }

    std::vector<llvm::Type*> param_types;
    if (!has_void_param) {
        param_types.reserve(fn_type->parameters.size());
        for (const auto& param : fn_type->parameters) {
            param_types.push_back(convert_param_type(param));
        }
    }
    llvm::Type* return_type = convert_type(fn_type->ret_type);
    auto* llvm_fn_type = llvm::FunctionType::get(
        return_type,
        param_types,
        fn_type->is_variadic);
    std::string fn_name = get_function_llvm_name(callee_sym, callee_sym->name);
    llvm::FunctionCallee callee = module->getOrInsertFunction(fn_name, llvm_fn_type);
    llvm::Value* callee_value = callee.getCallee();

    std::vector<llvm::Value*> call_args;
    call_args.reserve(args.size());
    for (size_t idx = 0; idx < args.size(); ++idx) {
        llvm::Value* arg_value = args[idx].first;
        if (!arg_value) {
            error(context_name + ": null operator argument during codegen", loc);
            return nullptr;
        }

        if (idx < param_types.size() && arg_value->getType() != param_types[idx]) {
            bool src_unsigned =
                args[idx].second && args[idx].second->isUnsigned();
            arg_value = cast_llvm_type(arg_value, param_types[idx], src_unsigned);
        }
        call_args.push_back(arg_value);
    }

    bool callee_non_throwing =
        fn_type->exception_spec == FunctionExceptionSpecKind::NonThrowing;
    bool callee_has_nounwind = false;
    llvm::Value* stripped_callee = callee_value->stripPointerCasts();
    if (auto* fn = llvm::dyn_cast<llvm::Function>(stripped_callee)) {
        callee_has_nounwind = fn->hasFnAttribute(llvm::Attribute::NoUnwind);
    }

    llvm::CallBase* call_inst = nullptr;
    bool emit_invoke = should_emit_invoke_for_callee(callee_value, fn_type.get());
    if (emit_invoke) {
        llvm::Function* function =
            builder.GetInsertBlock() ? builder.GetInsertBlock()->getParent() : nullptr;
        llvm::BasicBlock* unwind_bb =
            eh_region_stack.empty() ? nullptr : eh_region_stack.back().landing_pad_block;
        if (!function || !unwind_bb) {
            error(context_name + ": operator invoke lowering missing EH context", loc);
            return nullptr;
        }
        auto* continue_bb = llvm::BasicBlock::Create(*context, "invoke.cont", function);
        if (return_type->isVoidTy()) {
            call_inst = builder.CreateInvoke(
                llvm_fn_type, callee_value, continue_bb, unwind_bb, call_args);
        } else {
            call_inst = builder.CreateInvoke(
                llvm_fn_type, callee_value, continue_bb, unwind_bb, call_args, "op.calltmp");
        }
        builder.SetInsertPoint(continue_bb);
    } else if (return_type->isVoidTy()) {
        call_inst = builder.CreateCall(llvm_fn_type, callee_value, call_args);
    } else {
        call_inst = builder.CreateCall(llvm_fn_type, callee_value, call_args, "op.calltmp");
    }

    if (!emit_invoke && call_inst && (callee_non_throwing || callee_has_nounwind)) {
        call_inst->setDoesNotThrow();
    }

    return call_inst;
}

llvm::Value* ASTToLLVM::convert_cpp_new_expression(CppNewExpr* expr) {
    if (!expr) {
        error("convert_cpp_new_expression(): invalid new-expression");
        return nullptr;
    }
    if (!expr->allocator_sym || expr->allocator_sym->kind != SymbolKind::FUNCTION) {
        error("convert_cpp_new_expression(): missing selected allocator symbol",
              expr->location);
        return nullptr;
    }

    llvm::Value* allocation_size = emit_type_size_bytes(
        expr->allocated_type.get_shared(),
        true);
    if (!allocation_size) {
        error("convert_cpp_new_expression(): failed to lower allocation size",
              expr->location);
        return nullptr;
    }

    std::vector<std::pair<llvm::Value*, QualType>> allocator_args;
    allocator_args.reserve(1 + expr->placement_args.size());
    allocator_args.emplace_back(allocation_size, QualType());
    for (const auto& placement_arg : expr->placement_args) {
        llvm::Value* arg_value = placement_arg
            ? convert_expression(placement_arg.get())
            : nullptr;
        if (!arg_value) {
            error("convert_cpp_new_expression(): failed to lower placement argument",
                  expr->location);
            return nullptr;
        }
        allocator_args.emplace_back(arg_value,
                                    placement_arg ? placement_arg->get_type() : QualType());
    }

    llvm::Value* raw_alloc_ptr = emit_cpp_operator_call(
        expr->allocator_sym,
        allocator_args,
        expr->location,
        "convert_cpp_new_expression()");
    if (!raw_alloc_ptr) {
        return nullptr;
    }
    if (!raw_alloc_ptr->getType()->isPointerTy()) {
        error("convert_cpp_new_expression(): allocator does not return pointer type",
              expr->location);
        return nullptr;
    }

    llvm::Type* result_ptr_type = convert_type(expr->result_type.get_shared());
    if (!result_ptr_type || !result_ptr_type->isPointerTy()) {
        error("convert_cpp_new_expression(): invalid result pointer type",
              expr->location);
        return nullptr;
    }
    llvm::Value* typed_ptr = raw_alloc_ptr;
    if (typed_ptr->getType() != result_ptr_type) {
        typed_ptr = cast_llvm_type(typed_ptr, result_ptr_type, false);
    }

    if (expr->ctor_sym) {
        if (expr->is_array_form) {
            error("convert_cpp_new_expression(): new[] with constructor teardown is not supported yet",
                  expr->location);
            return nullptr;
        }
        if (!emit_cpp_construct_call(
                expr->ctor_sym,
                expr->constructor_args,
                typed_ptr,
                expr->location,
                "convert_cpp_new_expression() ctor")) {
            return nullptr;
        }
    } else if (!expr->initializer &&
               !expr->is_array_form &&
               canonical_type_kind(expr->allocated_type, ast_ctx.get()) ==
                   TypeKind::Object) {
        if (!emit_cpp_object_default_construction_recursive(
                expr->allocated_type,
                typed_ptr,
                expr->location,
                "convert_cpp_new_expression() implicit default construction")) {
            return nullptr;
        }
    } else if (expr->initializer) {
        if (expr->is_array_form) {
            error("convert_cpp_new_expression(): array initializer lowering for new[] is not supported yet",
                  expr->location);
            return nullptr;
        }

        auto result_ptr_semantic_type =
            desugar_type(expr->result_type, ast_ctx.get()).as_shared<PointerType>();
        if (!result_ptr_semantic_type || !result_ptr_semantic_type->pointed_type) {
            error("convert_cpp_new_expression(): invalid pointee type for initializer store",
                  expr->location);
            return nullptr;
        }
        llvm::Type* pointee_llvm_type =
            convert_type(result_ptr_semantic_type->pointed_type.get_shared());
        llvm::Value* init_value = convert_expression(expr->initializer.get());
        if (!init_value) {
            error("convert_cpp_new_expression(): failed to lower initializer",
                  expr->location);
            return nullptr;
        }
        if (init_value->getType() != pointee_llvm_type) {
            bool src_unsigned =
                expr->initializer->get_type() && expr->initializer->get_type()->isUnsigned();
            init_value = cast_llvm_type(init_value, pointee_llvm_type, src_unsigned);
        }
        builder.CreateStore(init_value, typed_ptr);
    }

    return typed_ptr;
}

llvm::Value* ASTToLLVM::convert_cpp_delete_expression(CppDeleteExpr* expr) {
    if (!expr || !expr->operand) {
        error("convert_cpp_delete_expression(): invalid delete-expression",
              expr ? expr->location : SrcLoc());
        return nullptr;
    }

    llvm::Value* operand_ptr = convert_expression(expr->operand.get());
    if (!operand_ptr) {
        error("convert_cpp_delete_expression(): failed to lower delete operand",
              expr->location);
        return nullptr;
    }
    if (!operand_ptr->getType()->isPointerTy()) {
        llvm::Type* generic_ptr_ty = llvm::PointerType::get(*context, 0);
        operand_ptr = cast_llvm_type(operand_ptr, generic_ptr_ty, false);
    }

    if (!expr->deallocator_sym || expr->deallocator_sym->kind != SymbolKind::FUNCTION) {
        error("convert_cpp_delete_expression(): missing selected deallocator symbol",
              expr->location);
        return nullptr;
    }

    llvm::Function* function =
        builder.GetInsertBlock() ? builder.GetInsertBlock()->getParent() : nullptr;
    if (!function) {
        error("convert_cpp_delete_expression(): delete-expression outside function",
              expr->location);
        return nullptr;
    }

    auto* nonnull_bb = llvm::BasicBlock::Create(*context, "delete.nonnull", function);
    auto* cont_bb = llvm::BasicBlock::Create(*context, "delete.cont", function);
    llvm::Value* is_nonnull = builder.CreateIsNotNull(operand_ptr, "delete.isnonnull");
    builder.CreateCondBr(is_nonnull, nonnull_bb, cont_bb);

    builder.SetInsertPoint(nonnull_bb);
    llvm::Value* deallocator_ptr = operand_ptr;
    bool emit_deallocator_call = true;
    switch (expr->destruction_kind) {
        case CppDeleteExpr::DestructionKind::None:
            break;
        case CppDeleteExpr::DestructionKind::Direct: {
            bool is_scalar_object_delete =
                !expr->is_array_form &&
                canonical_type_kind(expr->destroyed_type, ast_ctx.get()) ==
                    TypeKind::Object;
            if (is_scalar_object_delete) {
                emit_cpp_object_teardown_recursive(
                    expr->destroyed_type,
                    operand_ptr,
                    expr->destructor_sym,
                    expr->location,
                    "convert_cpp_delete_expression() dtor",
                    CppCtorDtorVariant::Complete);
            } else if (expr->destructor_sym) {
                if (!emit_cpp_destruct_call(
                        expr->destructor_sym,
                        operand_ptr,
                        expr->location,
                        "convert_cpp_delete_expression() dtor")) {
                    return nullptr;
                }
            }
            break;
        }
        case CppDeleteExpr::DestructionKind::Virtual: {
            bool is_scalar_object_delete =
                !expr->is_array_form &&
                canonical_type_kind(expr->destroyed_type, ast_ctx.get()) ==
                    TypeKind::Object;
            if (!is_scalar_object_delete || !expr->destructor_sym) {
                break;
            }

            auto destroyed_record =
                desugar_type(expr->destroyed_type, ast_ctx.get()).as_shared<ObjectType>();
            const ObjectDecl* destroyed_record_decl = destroyed_record
                ? canonical_cpp_record_decl(
                    dyn_cast<ObjectDecl>(destroyed_record->get_decl()))
                : nullptr;
            const RecordSemanticState* destroyed_record_state =
                lookup_cpp_record_state(destroyed_record_decl);
            if (!destroyed_record_decl || !destroyed_record_state) {
                error("convert_cpp_delete_expression(): missing static record state for virtual delete",
                      expr->location);
                return nullptr;
            }

            std::optional<size_t> semantic_dtor_slot_index = std::nullopt;
            for (const auto& dtor : destroyed_record_state->destructors) {
                if (!dtor.is_virtual || dtor.virtual_slot_index < 0) {
                    continue;
                }
                if (dtor.symbol == expr->destructor_sym) {
                    semantic_dtor_slot_index =
                        static_cast<size_t>(dtor.virtual_slot_index);
                    break;
                }
            }
            if (!semantic_dtor_slot_index.has_value()) {
                for (const auto& dtor : destroyed_record_state->destructors) {
                    if (dtor.is_virtual && dtor.virtual_slot_index >= 0) {
                        semantic_dtor_slot_index =
                            static_cast<size_t>(dtor.virtual_slot_index);
                        break;
                    }
                }
            }
            if (!semantic_dtor_slot_index.has_value()) {
                error("convert_cpp_delete_expression(): missing virtual destructor slot",
                      expr->location);
                return nullptr;
            }

            auto dtor_type =
                desugar_type(expr->destructor_sym->type, ast_ctx.get())
                    .as_shared<FunctionType>();
            if (!dtor_type || dtor_type->parameters.empty()) {
                error("convert_cpp_delete_expression(): invalid virtual destructor type",
                      expr->location);
                return nullptr;
            }

            if (expr->is_global_delete) {
                deallocator_ptr = recover_cpp_complete_object_address(
                    operand_ptr,
                    destroyed_record_decl,
                    expr->location,
                    "convert_cpp_delete_expression() global delete",
                    destroyed_record_decl);
            }

            llvm::Type* object_llvm_type = convert_type(expr->destroyed_type);
            auto* object_struct_ty = llvm::dyn_cast<llvm::StructType>(object_llvm_type);
            if (!object_struct_ty || object_struct_ty->getNumElements() == 0) {
                error("convert_cpp_delete_expression(): invalid object layout for virtual delete",
                      expr->location);
                return nullptr;
            }

            auto* ptr_ty = llvm::PointerType::get(*context, 0);
            llvm::Value* vptr_addr = builder.CreateStructGEP(
                object_struct_ty, operand_ptr, 0, "delete.vptr.addr");
            llvm::Value* raw_vptr = builder.CreateLoad(ptr_ty, vptr_addr, "delete.vptr");
            auto* table_ptr_ty = llvm::PointerType::get(ptr_ty, 0);
            llvm::Value* vtable_ptr = builder.CreateBitCast(
                raw_vptr, table_ptr_ty, "delete.vtable.ptr");
            uint64_t physical_slot_index = static_cast<uint64_t>(
                cpp_vtable_physical_slot_index(
                    destroyed_record_state,
                    *semantic_dtor_slot_index,
                    !expr->is_global_delete));
            llvm::Value* slot_addr = builder.CreateInBoundsGEP(
                ptr_ty,
                vtable_ptr,
                llvm::ConstantInt::get(
                    llvm::Type::getInt64Ty(*context),
                    physical_slot_index),
                "delete.vslot.addr");
            llvm::Value* raw_callee = builder.CreateLoad(
                ptr_ty, slot_addr, "delete.vcall.callee");

            std::vector<llvm::Type*> param_types;
            param_types.reserve(dtor_type->parameters.size());
            for (const auto& param : dtor_type->parameters) {
                param_types.push_back(convert_param_type(param));
            }
            llvm::Type* return_type = convert_type(dtor_type->ret_type);
            auto* llvm_fn_type = llvm::FunctionType::get(
                return_type,
                param_types,
                dtor_type->is_variadic);

            llvm::Value* this_arg = operand_ptr;
            if (this_arg->getType() != param_types.front()) {
                this_arg = cast_llvm_type(
                    this_arg,
                    param_types.front(),
                    false);
            }
            std::vector<llvm::Value*> dtor_args{this_arg};

            bool emit_invoke = should_emit_invoke_for_callee(raw_callee, dtor_type.get());
            if (emit_invoke) {
                llvm::Function* current_fn = builder.GetInsertBlock()->getParent();
                auto* continue_bb =
                    llvm::BasicBlock::Create(*context, "invoke.cont", current_fn);
                auto* unwind_bb = eh_region_stack.back().landing_pad_block;
                if (return_type->isVoidTy()) {
                    builder.CreateInvoke(
                        llvm_fn_type,
                        raw_callee,
                        continue_bb,
                        unwind_bb,
                        dtor_args);
                } else {
                    builder.CreateInvoke(
                        llvm_fn_type,
                        raw_callee,
                        continue_bb,
                        unwind_bb,
                        dtor_args,
                        "delete.vdtor.call");
                }
                builder.SetInsertPoint(continue_bb);
            } else {
                llvm::CallBase* call_inst = nullptr;
                if (return_type->isVoidTy()) {
                    call_inst = builder.CreateCall(llvm_fn_type, raw_callee, dtor_args);
                } else {
                    call_inst = builder.CreateCall(
                        llvm_fn_type,
                        raw_callee,
                        dtor_args,
                        "delete.vdtor.call");
                }
                if (call_inst &&
                    dtor_type->exception_spec ==
                        FunctionExceptionSpecKind::NonThrowing) {
                    call_inst->setDoesNotThrow();
                }
            }

            if (!expr->is_global_delete) {
                emit_deallocator_call = false;
            }
            break;
        }
    }

    if (emit_deallocator_call) {
        std::vector<std::pair<llvm::Value*, QualType>> deallocator_args;
        deallocator_args.emplace_back(
            deallocator_ptr,
            expr->operand ? expr->operand->get_type() : QualType());
        if (!emit_cpp_operator_call(
                expr->deallocator_sym,
                deallocator_args,
                expr->location,
                "convert_cpp_delete_expression()")) {
            return nullptr;
        }
    }
    builder.CreateBr(cont_bb);

    builder.SetInsertPoint(cont_bb);
    return llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context), 0);
}
