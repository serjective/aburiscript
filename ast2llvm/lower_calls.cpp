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

llvm::Value* materialize_indirect_aggregate_argument(ASTToLLVM& lower,
                                                     const QualType& param_type,
                                                     Expr* arg_expr,
                                                     SrcLoc loc,
                                                     const char* tmp_name) {
    auto param_canonical = desugar_type(param_type, lower.ast_ctx.get());
    auto record_type = param_canonical.as_shared<ObjectType>();
    if (!record_type || record_type->isIncomplete()) {
        lower.error("materialize_indirect_aggregate_argument(): invalid aggregate parameter",
                    loc);
        return nullptr;
    }

    llvm::Type* agg_ty = lower.convert_type(param_canonical.get_shared());
    if (!agg_ty) {
        lower.error("materialize_indirect_aggregate_argument(): failed to lower aggregate type",
                    loc);
        return nullptr;
    }

    llvm::Function* function = lower.builder.GetInsertBlock()->getParent();
    auto* tmp = lower.create_entry_alloca(function, agg_ty, nullptr, tmp_name);
    if (!tmp) {
        lower.error("materialize_indirect_aggregate_argument(): failed to allocate aggregate temporary",
                    loc);
        return nullptr;
    }

    llvm::Align agg_align = lower.module->getDataLayout().getABITypeAlign(agg_ty);
    tmp->setAlignment(agg_align);

    Expr* lvalue_base = arg_expr;
    while (auto* cast = dyn_cast<ImplicitCast>(lvalue_base)) {
        lvalue_base = cast->expr.get();
    }

    llvm::Value* src_ptr = lower.get_lvalue(lvalue_base).address;
    if (src_ptr) {
        uint64_t size_bytes =
            static_cast<uint64_t>(std::max<int64_t>(0, record_type->getWidthBytes()));
        if (size_bytes > 0) {
            lower.builder.CreateMemCpy(
                tmp, llvm::MaybeAlign(agg_align), src_ptr, llvm::MaybeAlign(1), size_bytes);
        }
        return tmp;
    }

    llvm::Value* arg_val = lower.convert_expression(arg_expr);
    if (!arg_val) {
        lower.error("materialize_indirect_aggregate_argument(): invalid aggregate argument",
                    loc);
        return nullptr;
    }
    if (arg_val->getType() != agg_ty) {
        lower.error("materialize_indirect_aggregate_argument(): aggregate argument type mismatch",
                    loc);
        return nullptr;
    }

    auto* store = lower.builder.CreateStore(arg_val, tmp);
    store->setAlignment(agg_align);
    return tmp;
}

llvm::Value* materialize_direct_aggregate_argument(ASTToLLVM& lower,
                                                   const QualType& param_type,
                                                   Expr* arg_expr,
                                                   SrcLoc loc,
                                                   const char* tmp_name) {
    llvm::Type* abi_type = lower.get_direct_aggregate_parameter_abi_type(param_type);
    auto param_canonical = desugar_type(param_type, lower.ast_ctx.get());
    auto record_type = param_canonical.as_shared<ObjectType>();
    if (!abi_type || !record_type || record_type->isIncomplete()) {
        lower.error("materialize_direct_aggregate_argument(): invalid aggregate parameter",
                    loc);
        return nullptr;
    }

    llvm::Type* agg_ty = lower.convert_type(param_canonical.get_shared());
    if (!agg_ty) {
        lower.error("materialize_direct_aggregate_argument(): failed to lower aggregate type",
                    loc);
        return nullptr;
    }

    Expr* lvalue_base = arg_expr;
    while (auto* cast = dyn_cast<ImplicitCast>(lvalue_base)) {
        lvalue_base = cast->expr.get();
    }

    llvm::Value* src_ptr = lower.get_lvalue(lvalue_base).address;
    if (!src_ptr) {
        llvm::Value* arg_val = lower.convert_expression(arg_expr);
        if (!arg_val) {
            lower.error("materialize_direct_aggregate_argument(): invalid aggregate argument",
                        loc);
            return nullptr;
        }
        if (arg_val->getType() != agg_ty) {
            lower.error("materialize_direct_aggregate_argument(): aggregate argument type mismatch",
                        loc);
            return nullptr;
        }

        llvm::Function* function = lower.builder.GetInsertBlock()->getParent();
        auto* tmp = lower.create_entry_alloca(function, agg_ty, nullptr, tmp_name);
        if (!tmp) {
            lower.error("materialize_direct_aggregate_argument(): failed to allocate aggregate temporary",
                        loc);
            return nullptr;
        }
        llvm::Align agg_align =
            lower.module->getDataLayout().getABITypeAlign(agg_ty);
        tmp->setAlignment(agg_align);
        auto* store = lower.builder.CreateStore(arg_val, tmp);
        store->setAlignment(agg_align);
        src_ptr = tmp;
    }

    return lower.load_aggregate_memory_as_abi_value(
        src_ptr, param_type, abi_type, loc, "materialize_direct_aggregate_argument()");
}

Expr* unwrap_call_target_expr(Expr* expr) {
    Expr* current = expr;
    while (true) {
        if (auto* cast = dyn_cast<ImplicitCast>(current)) {
            if (cast->kind == ImplicitCastTypes::FUNCTION_TO_POINTER ||
                cast->kind == ImplicitCastTypes::LVALUE_TO_RVALUE) {
                current = cast->expr.get();
                continue;
            }
        }
        if (auto* paren = dyn_cast<ParenExpr>(current)) {
            current = paren->subexpr.get();
            continue;
        }
        break;
    }
    return current;
}

} // namespace

llvm::Value* ASTToLLVM::convert_function_call(FuncCall *expr) {
    Expr* raw_member_callee = unwrap_call_target_expr(expr->func.get());

    if (auto* member_ptr_callee = dyn_cast<MemberPointerAccessExpr>(raw_member_callee);
        member_ptr_callee) {
        return emit_member_pointer_dispatch(expr, member_ptr_callee);
    }
    if (auto* callee_ref = dyn_cast<VarRef>(raw_member_callee);
        callee_ref && callee_ref->symref &&
        callee_ref->symref->kind == SymbolKind::FUNCTION) {
        mark_function_symbol_odr_used(callee_ref->symref);
    }

    // ---- Regular (non-member-pointer) function call ----

    llvm::Value* calleeVal = convert_expression(expr->func.get());
    if (!calleeVal) {
        error("convert_function_call(): invalid callee expression", expr->location);
        return nullptr;
    }

    auto callee_type = desugar_type(expr->func->get_type(), ast_ctx.get());
    std::shared_ptr<FunctionType> func_ctype = callee_type.as_shared<FunctionType>();
    bool callee_is_block_pointer = false;
    if (!func_ctype) {
        if (auto ptr_type = callee_type.as_shared<PointerType>()) {
            func_ctype =
                desugar_type(ptr_type->pointed_type, ast_ctx.get()).as_shared<FunctionType>();
        }
    }
    if (!func_ctype) {
        if (auto block_ptr_type = callee_type.as_shared<BlockPointerType>()) {
            func_ctype =
                desugar_type(block_ptr_type->pointed_type, ast_ctx.get()).as_shared<FunctionType>();
            callee_is_block_pointer = func_ctype != nullptr;
        }
    }
    if (!func_ctype) {
        error("convert_function_call(): callee is not a function or function pointer", expr->location);
        return nullptr;
    }

    std::vector<llvm::Type*> paramTypes;
    bool has_void_param = (func_ctype->parameters.size() == 1
        && func_ctype->parameters[0]->isVoid());
    unsigned abi_param_prefix =
        prepend_indirect_result_parameter(paramTypes, func_ctype->ret_type);
    if (callee_is_block_pointer) {
        paramTypes.push_back(llvm::PointerType::getUnqual(*context));
    }
    if (!has_void_param) {
        paramTypes.reserve(paramTypes.size() + func_ctype->parameters.size());
        for (const auto& param : func_ctype->parameters) {
            paramTypes.push_back(convert_param_type(param));
        }
    }
    llvm::Type* returnValueType = convert_type(func_ctype->ret_type);
    llvm::Type* returnType = convert_function_return_type(func_ctype->ret_type);
    llvm::FunctionType* llvmFuncType = llvm::FunctionType::get(returnType, paramTypes, func_ctype->is_variadic);
    bool callee_non_throwing =
        func_ctype->exception_spec == FunctionExceptionSpecKind::NonThrowing;

    if (!func_ctype->has_prototype) {
        // K&R style () — accept any number of arguments
    } else if (func_ctype->is_variadic) {
        size_t named_params = has_void_param ? 0 : func_ctype->parameters.size();
        if (expr->args.size() < named_params) {
            error("Too few arguments passed to variadic function", expr->location);
            return nullptr;
        }
    } else {
        size_t expected = has_void_param ? 0 : func_ctype->parameters.size();
        if (expr->args.size() != expected) {
            error("Incorrect # of arguments passed to function", expr->location);
            return nullptr;
        }
    }

    std::vector<llvm::Value*> argsV;
    argsV.reserve(expr->args.size() + (callee_is_block_pointer ? 1 : 0) +
                  abi_param_prefix);
    llvm::AllocaInst* indirect_result_slot = nullptr;
    if (abi_param_prefix != 0) {
        llvm::Function* function = builder.GetInsertBlock()->getParent();
        indirect_result_slot =
            create_indirect_result_slot(function, func_ctype->ret_type, "call.sret");
        if (!indirect_result_slot) {
            error("convert_function_call(): failed to allocate indirect result slot",
                  expr->location);
            return nullptr;
        }
        argsV.push_back(indirect_result_slot);
    }
    size_t named_params = (!func_ctype->has_prototype || has_void_param) ? 0 : func_ctype->parameters.size();
    std::vector<bool> byref_param;
    byref_param.resize(named_params, false);
    std::vector<bool> direct_aggregate_param;
    direct_aggregate_param.resize(named_params, false);
    std::vector<bool> reference_param;
    reference_param.resize(named_params, false);
    std::vector<QualType> reference_referred_type;
    reference_referred_type.resize(named_params);
    for (size_t i = 0; i < named_params; ++i) {
        auto param_canonical = desugar_type(func_ctype->parameters[i], ast_ctx.get());
        if (auto ref_type = param_canonical.as_shared<ReferenceType>()) {
            reference_param[i] = true;
            reference_referred_type[i] = ref_type->referred_type;
            continue;
        }
        byref_param[i] = pass_aggregate_by_reference(func_ctype->parameters[i]);
        direct_aggregate_param[i] =
            !byref_param[i] &&
            has_direct_aggregate_parameter_abi(func_ctype->parameters[i]);
    }

    for (size_t i = 0; i < expr->args.size(); ++i) {
        Expr* arg_expr = expr->args[i].get();
        if (i < named_params && reference_param[i]) {
            Expr* lvalue_base = unwrap_reference_binding_expr(arg_expr);
            llvm::Value* ref_ptr = get_lvalue(lvalue_base).address;
            if (!ref_ptr) {
                // Temporary materialization for reference binding.
                llvm::Value* arg_val = convert_expression(arg_expr);
                if (!arg_val) {
                    error("argument in convert_function_call invalid", expr->location);
                    return nullptr;
                }

                QualType referred_type = reference_referred_type[i];
                if (!referred_type) {
                    error("convert_function_call(): invalid reference parameter type", expr->location);
                    return nullptr;
                }
                llvm::Type* referred_llvm_type = convert_type(referred_type.get_shared());
                if (!referred_llvm_type) {
                    error("convert_function_call(): failed to lower reference target type", expr->location);
                    return nullptr;
                }
                if (arg_val->getType() != referred_llvm_type) {
                    bool src_unsigned = arg_expr->get_type() && arg_expr->get_type()->isUnsigned();
                    arg_val = cast_llvm_type(arg_val, referred_llvm_type, src_unsigned);
                }

                llvm::Function* func = builder.GetInsertBlock()->getParent();
                llvm::Value* tmp =
                    create_entry_alloca(func, referred_llvm_type, nullptr, "ref.arg.tmp");
                if (!tmp) {
                    error("convert_function_call(): failed to allocate reference argument temporary",
                          expr->location);
                    return nullptr;
                }
                builder.CreateStore(arg_val, tmp);
                ref_ptr = tmp;
            }
            argsV.push_back(ref_ptr);
        } else if (i < named_params && byref_param[i]) {
            llvm::Value* byref_ptr = materialize_indirect_aggregate_argument(
                *this, func_ctype->parameters[i], arg_expr, expr->location, "byref.tmp");
            if (!byref_ptr) {
                return nullptr;
            }
            argsV.push_back(byref_ptr);
        } else if (i < named_params && direct_aggregate_param[i]) {
            llvm::Value* coerced_arg = materialize_direct_aggregate_argument(
                *this, func_ctype->parameters[i], arg_expr, expr->location, "coerce.tmp");
            if (!coerced_arg) {
                return nullptr;
            }
            argsV.push_back(coerced_arg);
        } else {
            llvm::Value* arg_val = convert_expression(arg_expr);
            if (!arg_val) {
                error("argument in convert_function_call invalid", expr->location);
                return nullptr;
            }

            bool is_vararg_arg = func_ctype->is_variadic && i >= named_params;
            if (is_vararg_arg && target && target->va_list_kind == VaListKind::CHAR_PTR) {
                llvm::Type* arg_ty = arg_val->getType();
                if (arg_ty->isAggregateType()) {
                    size_t arg_size = module->getDataLayout().getTypeAllocSize(arg_ty);

                    // Darwin/AArch64 varargs: large aggregates are passed indirectly.
                    if (arg_size > 16) {
                        Expr* lvalue_base = unwrap_reference_binding_expr(arg_expr);
                        llvm::Value* arg_ptr = get_lvalue(lvalue_base).address;
                        if (!arg_ptr) {
                            llvm::Function* func = builder.GetInsertBlock()->getParent();
                            llvm::IRBuilder<> tmpBuilder(&func->getEntryBlock(), func->getEntryBlock().begin());
                            arg_ptr = tmpBuilder.CreateAlloca(arg_ty, nullptr, "vararg.indirect.tmp");
                            builder.CreateStore(arg_val, arg_ptr);
                        }
                        argsV.push_back(arg_ptr);
                        continue;
                    }

                    size_t slot_size = ((arg_size + 7) / 8) * 8;
                    if (slot_size == 0) {
                        slot_size = 8;
                    }

                    auto* blob_ty = llvm::ArrayType::get(llvm::Type::getInt8Ty(*context), slot_size);
                    llvm::Type* coerce_ty = nullptr;
                    if (slot_size == 8) {
                        coerce_ty = llvm::Type::getInt64Ty(*context);
                    } else {
                        coerce_ty = llvm::ArrayType::get(llvm::Type::getInt64Ty(*context), slot_size / 8);
                    }

                    llvm::Function* func = builder.GetInsertBlock()->getParent();
                    llvm::IRBuilder<> tmpBuilder(&func->getEntryBlock(), func->getEntryBlock().begin());
                    llvm::Value* tmp = tmpBuilder.CreateAlloca(arg_ty, nullptr, "vararg.coerce.tmp");
                    llvm::Value* blob_tmp = tmpBuilder.CreateAlloca(blob_ty, nullptr, "vararg.coerce.blob");
                    builder.CreateStore(llvm::Constant::getNullValue(blob_ty), blob_tmp);
                    builder.CreateStore(arg_val, tmp);
                    builder.CreateMemCpy(blob_tmp, llvm::Align(1), tmp, llvm::Align(1), arg_size);
                    llvm::Value* coerced = builder.CreateLoad(coerce_ty, blob_tmp, "vararg.coerce");
                    argsV.push_back(coerced);
                    continue;
                }
            }

            argsV.push_back(arg_val);
        }
    }

    if (callee_is_block_pointer) {
        auto* ptr_ty = llvm::PointerType::getUnqual(*context);
        llvm::Value* block_self = calleeVal;
        if (block_self->getType() != ptr_ty) {
            block_self = cast_llvm_type(block_self, ptr_ty, true);
        }

        auto layout = darwin_blocks::block_literal_header_layout();
        llvm::Value* invoke_slot_addr = builder.CreateInBoundsGEP(
            llvm::Type::getInt8Ty(*context),
            block_self,
            builder.getInt64(layout.invoke_offset),
            "block.invoke.slot");
        auto* invoke_load =
            builder.CreateLoad(ptr_ty, invoke_slot_addr, "block.invoke.ptr");
        invoke_load->setAlignment(
            module->getDataLayout().getABITypeAlign(ptr_ty));
        calleeVal = invoke_load;
        argsV.insert(argsV.begin() + abi_param_prefix, block_self);
    }

    Expr* callee_expr = expr->func.get();
    while (auto* cast = dyn_cast<ImplicitCast>(callee_expr)) {
        if (cast->kind == ImplicitCastTypes::FUNCTION_TO_POINTER ||
            cast->kind == ImplicitCastTypes::LVALUE_TO_RVALUE) {
            callee_expr = cast->expr.get();
            continue;
        }
        break;
    }

    std::string callee_name;
    if (auto* vref = dyn_cast<VarRef>(callee_expr)) {
        if (vref->symref && vref->symref->kind == SymbolKind::FUNCTION) {
            callee_name = vref->symref->asm_label
                ? get_asm_label_name(*vref->symref->asm_label)
                : vref->get_name();
        } else {
            callee_name = vref->get_name();
        }
    }

    // Some platforms (including Darwin) do not provide mempcpy in libc.
    // Lower direct mempcpy calls to memcpy + pointer bump for portability.
    if (callee_name == "mempcpy" && argsV.size() == 3) {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(*context);
        auto* i64_ty = llvm::Type::getInt64Ty(*context);
        auto* memcpy_ft = llvm::FunctionType::get(i8_ptr_ty, {i8_ptr_ty, i8_ptr_ty, i64_ty}, false);
        auto memcpy_callee = module->getOrInsertFunction("memcpy", memcpy_ft);

        llvm::Value* dst = argsV[0];
        llvm::Value* src = argsV[1];
        llvm::Value* n = argsV[2];
        if (dst->getType() != i8_ptr_ty) {
            dst = cast_llvm_type(dst, i8_ptr_ty, true);
        }
        if (src->getType() != i8_ptr_ty) {
            src = cast_llvm_type(src, i8_ptr_ty, true);
        }
        if (n->getType() != i64_ty) {
            n = builder.CreateIntCast(n, i64_ty, false);
        }

        builder.CreateCall(memcpy_callee, {dst, src, n}, "mempcpy.memcpy");
        llvm::Value* end_ptr = builder.CreateInBoundsGEP(llvm::Type::getInt8Ty(*context), dst, n, "mempcpy.end");
        if (returnType->isPointerTy() && end_ptr->getType() != returnType) {
            end_ptr = cast_llvm_type(end_ptr, returnType, true);
        }
        return end_ptr;
    }

    // For K&R functions, the declared type has 0 params but we may pass args.
    // Build the call type from actual arguments so LLVM types match.
    if (!func_ctype->has_prototype && !argsV.empty()) {
        std::vector<llvm::Type*> actualParamTypes;
        actualParamTypes.reserve(argsV.size());
        for (auto* v : argsV) {
            actualParamTypes.push_back(v->getType());
        }
        llvmFuncType = llvm::FunctionType::get(returnType, actualParamTypes, false);
    }

    llvm::CallBase* call_inst = nullptr;
    bool emit_invoke = should_emit_invoke_for_callee(calleeVal, func_ctype.get());
    if (emit_invoke) {
        llvm::Function* function = builder.GetInsertBlock()->getParent();
        auto* continue_bb = llvm::BasicBlock::Create(*context, "invoke.cont", function);
        auto* unwind_bb = eh_region_stack.back().landing_pad_block;
        if (returnType->isVoidTy()) {
            call_inst = builder.CreateInvoke(
                llvmFuncType, calleeVal, continue_bb, unwind_bb, argsV);
        } else {
            call_inst = builder.CreateInvoke(
                llvmFuncType, calleeVal, continue_bb, unwind_bb, argsV, "calltmp");
        }
        builder.SetInsertPoint(continue_bb);
    } else if (returnType->isVoidTy()) {
        call_inst = builder.CreateCall(llvmFuncType, calleeVal, argsV);
    } else {
        call_inst = builder.CreateCall(llvmFuncType, calleeVal, argsV, "calltmp");
    }
    if (!emit_invoke && call_inst) {
        bool callee_has_nounwind = false;
        llvm::Value* stripped = calleeVal->stripPointerCasts();
        if (auto* fn = llvm::dyn_cast<llvm::Function>(stripped)) {
            callee_has_nounwind = fn->hasFnAttribute(llvm::Attribute::NoUnwind);
        }
        if (callee_non_throwing || callee_has_nounwind) {
            call_inst->setDoesNotThrow();
        }
    }
    apply_indirect_result_attributes(call_inst, 0, func_ctype->ret_type);
    if (indirect_result_slot) {
        return builder.CreateLoad(returnValueType, indirect_result_slot,
                                  "call.sret.load");
    }
    return call_inst;
}

llvm::Value* ASTToLLVM::convert_cpp_member_call(CppMemberCallExpr *expr) {
    if (!expr || !expr->lowered_call) {
        error("convert_cpp_member_call(): invalid lowered member call",
              expr ? expr->location : SrcLoc());
        return nullptr;
    }
    auto* lowered_call = expr->lowered_call.get();
    if (!ast_ctx ||
        expr->suppress_virtual_dispatch ||
        !expr->has_implicit_object_argument ||
        !ast_ctx->has_cpp_virtual_call_info(expr->node_id) ||
        lowered_call->args.empty()) {
        return convert_function_call(lowered_call);
    }

    const CppVirtualCallInfo* virtual_info =
        ast_ctx->get_cpp_virtual_call_info(expr->node_id);
    if (!virtual_info) {
        return convert_function_call(lowered_call);
    }
    if (!ensure_supported_cpp_vtable_abi(
            expr->location,
            "convert_cpp_member_call()")) {
        return nullptr;
    }

    std::shared_ptr<Symbol> callee_symbol = virtual_info->static_symbol;
    Expr* callee_expr = lowered_call->func.get();
    while (auto* cast = dyn_cast<ImplicitCast>(callee_expr)) {
        if (cast->kind == ImplicitCastTypes::FUNCTION_TO_POINTER ||
            cast->kind == ImplicitCastTypes::LVALUE_TO_RVALUE) {
            callee_expr = cast->expr.get();
            continue;
        }
        break;
    }
    if (auto* callee_ref = dyn_cast<VarRef>(callee_expr)) {
        if (callee_ref->symref && callee_ref->symref->kind == SymbolKind::FUNCTION) {
            callee_symbol = callee_ref->symref;
        }
    }
    if (!callee_symbol || callee_symbol->kind != SymbolKind::FUNCTION) {
        return convert_function_call(lowered_call);
    }

    auto fn_type =
        desugar_type(callee_symbol->type, ast_ctx.get()).as_shared<FunctionType>();
    if (!fn_type) {
        return convert_function_call(lowered_call);
    }

    bool has_void_param = fn_type->parameters.size() == 1 &&
                          fn_type->parameters[0]->isVoid();
    size_t named_param_count = has_void_param ? 0 : fn_type->parameters.size();
    if (fn_type->has_prototype && !fn_type->is_variadic &&
        lowered_call->args.size() != named_param_count) {
        return convert_function_call(lowered_call);
    }
    if (fn_type->has_prototype && fn_type->is_variadic &&
        lowered_call->args.size() < named_param_count) {
        return convert_function_call(lowered_call);
    }

    auto this_arg_type =
        desugar_type(lowered_call->args.front()->get_type(), ast_ctx.get())
            .as_shared<PointerType>();
    if (!this_arg_type) {
        return convert_function_call(lowered_call);
    }
    auto this_object_type =
        desugar_type(this_arg_type->pointed_type, ast_ctx.get()).as_shared<ObjectType>();
    if (!this_object_type) {
        return convert_function_call(lowered_call);
    }
    const ObjectDecl* arg_record_decl = canonical_cpp_record_decl(
        dyn_cast<ObjectDecl>(this_object_type->get_decl()));
    const ObjectDecl* static_record_decl =
        canonical_cpp_record_decl(virtual_info->static_record_decl);

    llvm::Value* this_ptr = convert_expression(lowered_call->args.front().get());
    if (!this_ptr || !this_ptr->getType()->isPointerTy()) {
        return convert_function_call(lowered_call);
    }
    llvm::Value* call_this_ptr = this_ptr;
    bool apply_this_adjustment = virtual_info->this_adjustment != 0;
    if (apply_this_adjustment && static_record_decl) {
        if (arg_record_decl && static_record_decl &&
            arg_record_decl != static_record_decl) {
            apply_this_adjustment = false;
        }
    }
    if (apply_this_adjustment) {
        llvm::Value* adjust_amount = llvm::ConstantInt::get(
            llvm::Type::getInt64Ty(*context),
            static_cast<int64_t>(virtual_info->this_adjustment),
            true);
        call_this_ptr = builder.CreateInBoundsGEP(
            llvm::Type::getInt8Ty(*context),
            this_ptr,
            adjust_amount,
            "vcall.this.adjust");
        if (call_this_ptr->getType() != this_ptr->getType()) {
            call_this_ptr = cast_llvm_type(call_this_ptr, this_ptr->getType(), false);
        }
    }

    llvm::Type* object_llvm_type = convert_type(this_object_type);
    auto* object_struct_ty = llvm::dyn_cast<llvm::StructType>(object_llvm_type);
    if (!object_struct_ty || object_struct_ty->getNumElements() == 0) {
        return convert_function_call(lowered_call);
    }

    auto* ptr_ty = llvm::PointerType::get(*context, 0);
    llvm::Value* vptr_addr =
        builder.CreateStructGEP(object_struct_ty, this_ptr, 0, "vptr.addr");
    llvm::Value* raw_vptr = builder.CreateLoad(ptr_ty, vptr_addr, "vptr");
    auto* table_ptr_ty = llvm::PointerType::get(ptr_ty, 0);
    llvm::Value* vtable_ptr = builder.CreateBitCast(raw_vptr, table_ptr_ty, "vtable.ptr");
    uint64_t physical_slot_index = static_cast<uint64_t>(virtual_info->slot_index);
    if (const RecordSemanticState* static_record_state =
            lookup_cpp_record_state(static_record_decl)) {
        physical_slot_index = static_cast<uint64_t>(cpp_vtable_physical_slot_index(
            static_record_state,
            static_cast<size_t>(virtual_info->slot_index)));
    }
    llvm::Value* slot_index = llvm::ConstantInt::get(
        llvm::Type::getInt64Ty(*context),
        physical_slot_index);
    llvm::Value* slot_addr = builder.CreateInBoundsGEP(
        ptr_ty, vtable_ptr, slot_index, "vslot.addr");
    llvm::Value* raw_callee = builder.CreateLoad(ptr_ty, slot_addr, "vcall.callee");

    std::vector<llvm::Type*> param_types;
    unsigned abi_param_prefix =
        prepend_indirect_result_parameter(param_types, fn_type->ret_type);
    if (!has_void_param) {
        param_types.reserve(fn_type->parameters.size());
        for (const auto& param : fn_type->parameters) {
            param_types.push_back(convert_param_type(param));
        }
    }
    llvm::Type* return_value_type = convert_type(fn_type->ret_type);
    llvm::Type* return_type = convert_function_return_type(fn_type->ret_type);
    llvm::FunctionType* llvm_fn_type = llvm::FunctionType::get(
        return_type, param_types, fn_type->is_variadic);

    struct ParamInfo {
        bool byref = false;
        bool direct_aggregate = false;
        bool reference = false;
        QualType referred_type;
    };
    std::vector<ParamInfo> param_info(named_param_count);
    for (size_t idx = 0; idx < named_param_count; ++idx) {
        auto param_canonical = desugar_type(fn_type->parameters[idx], ast_ctx.get());
        if (auto ref_type = param_canonical.as_shared<ReferenceType>()) {
            param_info[idx].reference = true;
            param_info[idx].referred_type = ref_type->referred_type;
            continue;
        }
        param_info[idx].byref = pass_aggregate_by_reference(fn_type->parameters[idx]);
        param_info[idx].direct_aggregate =
            !param_info[idx].byref &&
            has_direct_aggregate_parameter_abi(fn_type->parameters[idx]);
    }

    std::vector<llvm::Value*> argsV;
    argsV.reserve(lowered_call->args.size() + abi_param_prefix);
    llvm::AllocaInst* indirect_result_slot = nullptr;
    if (abi_param_prefix != 0) {
        llvm::Function* function = builder.GetInsertBlock()->getParent();
        indirect_result_slot =
            create_indirect_result_slot(function, fn_type->ret_type, "vcall.sret");
        if (!indirect_result_slot) {
            error("convert_cpp_member_call(): failed to allocate indirect result slot",
                  expr->location);
            return nullptr;
        }
        argsV.push_back(indirect_result_slot);
    }
    for (size_t idx = 0; idx < lowered_call->args.size(); ++idx) {
        llvm::Value* arg_val = nullptr;
        if (idx == 0) {
            arg_val = call_this_ptr;
        } else if (idx < named_param_count && param_info[idx].reference) {
            Expr* arg_expr = lowered_call->args[idx].get();
            Expr* lvalue_base = unwrap_reference_binding_expr(arg_expr);
            llvm::Value* ref_ptr = get_lvalue(lvalue_base).address;
            if (!ref_ptr) {
                llvm::Value* materialized_arg = convert_expression(arg_expr);
                if (!materialized_arg) {
                    error("convert_cpp_member_call(): failed to lower reference argument",
                          expr->location);
                    return nullptr;
                }

                QualType referred_type = param_info[idx].referred_type;
                if (!referred_type) {
                    error("convert_cpp_member_call(): invalid reference parameter type",
                          expr->location);
                    return nullptr;
                }
                llvm::Type* referred_llvm_type =
                    convert_type(referred_type.get_shared());
                if (!referred_llvm_type) {
                    error("convert_cpp_member_call(): failed to lower reference target type",
                          expr->location);
                    return nullptr;
                }
                if (materialized_arg->getType() != referred_llvm_type) {
                    bool src_unsigned =
                        arg_expr->get_type() && arg_expr->get_type()->isUnsigned();
                    materialized_arg = cast_llvm_type(
                        materialized_arg,
                        referred_llvm_type,
                        src_unsigned);
                }

                llvm::Function* function = builder.GetInsertBlock()->getParent();
                llvm::Value* tmp =
                    create_entry_alloca(function, referred_llvm_type, nullptr, "vcall.ref.tmp");
                if (!tmp) {
                    error("convert_cpp_member_call(): failed to allocate reference argument temporary",
                          expr->location);
                    return nullptr;
                }
                builder.CreateStore(materialized_arg, tmp);
                ref_ptr = tmp;
            }
            arg_val = ref_ptr;
        } else if (idx < named_param_count && param_info[idx].byref) {
            arg_val = materialize_indirect_aggregate_argument(
                *this,
                fn_type->parameters[idx],
                lowered_call->args[idx].get(),
                expr->location,
                "vcall.byref.tmp");
            if (!arg_val) {
                return nullptr;
            }
        } else if (idx < named_param_count && param_info[idx].direct_aggregate) {
            arg_val = materialize_direct_aggregate_argument(
                *this,
                fn_type->parameters[idx],
                lowered_call->args[idx].get(),
                expr->location,
                "vcall.coerce.tmp");
            if (!arg_val) {
                return nullptr;
            }
        } else {
            arg_val = convert_expression(lowered_call->args[idx].get());
        }
        if (!arg_val) {
            error("convert_cpp_member_call(): failed to lower call argument", expr->location);
            return nullptr;
        }

        size_t llvm_param_index = abi_param_prefix + idx;
        if (llvm_param_index < param_types.size() &&
            !(idx < named_param_count &&
              (param_info[idx].reference ||
               param_info[idx].byref ||
               param_info[idx].direct_aggregate)) &&
            arg_val->getType() != param_types[llvm_param_index]) {
            bool is_unsigned = lowered_call->args[idx]->get_type() &&
                               lowered_call->args[idx]->get_type()->isUnsigned();
            arg_val =
                cast_llvm_type(arg_val, param_types[llvm_param_index], is_unsigned);
        }
        argsV.push_back(arg_val);
    }

    if (!fn_type->has_prototype && !argsV.empty()) {
        std::vector<llvm::Type*> actual_param_types;
        actual_param_types.reserve(argsV.size());
        for (auto* arg : argsV) {
            actual_param_types.push_back(arg->getType());
        }
        llvm_fn_type = llvm::FunctionType::get(return_type, actual_param_types, false);
    }

    bool emit_invoke = should_emit_invoke_for_callee(raw_callee, fn_type.get());
    if (emit_invoke) {
        llvm::Function* function = builder.GetInsertBlock()->getParent();
        auto* continue_bb = llvm::BasicBlock::Create(*context, "invoke.cont", function);
        auto* unwind_bb = eh_region_stack.back().landing_pad_block;
        llvm::CallBase* invoke_inst = nullptr;
        if (return_type->isVoidTy()) {
            invoke_inst = builder.CreateInvoke(
                llvm_fn_type, raw_callee, continue_bb, unwind_bb, argsV);
        } else {
            invoke_inst = builder.CreateInvoke(
                llvm_fn_type, raw_callee, continue_bb, unwind_bb, argsV, "vcalltmp");
        }
        builder.SetInsertPoint(continue_bb);
        return invoke_inst;
    }

    llvm::CallBase* call_inst = nullptr;
    if (return_type->isVoidTy()) {
        call_inst = builder.CreateCall(llvm_fn_type, raw_callee, argsV);
    } else {
        call_inst = builder.CreateCall(llvm_fn_type, raw_callee, argsV, "vcalltmp");
    }

    if (call_inst &&
        fn_type->exception_spec == FunctionExceptionSpecKind::NonThrowing) {
        call_inst->setDoesNotThrow();
    }
    apply_indirect_result_attributes(call_inst, 0, fn_type->ret_type);
    if (indirect_result_slot) {
        return builder.CreateLoad(return_value_type, indirect_result_slot,
                                  "vcall.sret.load");
    }
    return call_inst;
}

// ---------------------------------------------------------------------------
// Member-pointer-to-function dispatch: direct vs. virtual branch with PHI
// node merge, Itanium-style payload decoding, and argument lowering.
//
// The implicit object parameter is the first declared parameter of a
// member-function type.  It carries the `this` pointer (or a pointer to
// the class instance) and is NOT part of the user-visible argument list.
// ---------------------------------------------------------------------------
llvm::Value* ASTToLLVM::emit_member_pointer_dispatch(
    FuncCall *expr,
    MemberPointerAccessExpr *member_ptr_callee) {
    auto callee_type = desugar_type(expr->func->get_type(), ast_ctx.get());
    std::shared_ptr<FunctionType> func_ctype =
        callee_type.as_shared<FunctionType>();
    if (!func_ctype) {
        if (auto ptr_type = callee_type.as_shared<PointerType>()) {
            func_ctype =
                desugar_type(ptr_type->pointed_type, ast_ctx.get())
                    .as_shared<FunctionType>();
        }
    }
    if (!func_ctype) {
        error("emit_member_pointer_dispatch(): callee is not a function type",
              expr->location);
        return nullptr;
    }

    bool has_void_param = (func_ctype->parameters.size() == 1 &&
        func_ctype->parameters[0]->isVoid());
    size_t named_params = has_void_param ? 0 : func_ctype->parameters.size();
    auto member_ptr_type =
        desugar_type(member_ptr_callee->member_pointer->get_type(), ast_ctx.get())
            .as_shared<MemberPointerType>();

    // Detect implicit object parameter: first parameter is a pointer to a
    // class type, consumed by the ABI and not exposed as a user argument.
    bool has_implicit_object_param = false;
    if (member_ptr_type && named_params > 0) {
        auto first_param_ptr = desugar_type(
            remove_reference(func_ctype->parameters[0], ast_ctx.get()),
            ast_ctx.get())
            .as_shared<PointerType>();
        auto first_param_owner = first_param_ptr
            ? desugar_type(first_param_ptr->pointed_type, ast_ctx.get())
                  .as_shared<ObjectType>()
            : nullptr;
        if (first_param_ptr && first_param_owner) {
            has_implicit_object_param = true;
        }
    }

    std::vector<llvm::Type*> paramTypes;
    unsigned abi_param_prefix =
        prepend_indirect_result_parameter(paramTypes, func_ctype->ret_type);
    paramTypes.reserve(paramTypes.size() + named_params);
    for (const auto& param : func_ctype->parameters) {
        paramTypes.push_back(convert_param_type(param));
    }
    if (has_implicit_object_param &&
        (paramTypes.size() <= abi_param_prefix ||
         !paramTypes[abi_param_prefix]->isPointerTy())) {
        error("emit_member_pointer_dispatch(): invalid implicit object parameter type",
              expr->location);
        return nullptr;
    }

    llvm::Type* returnValueType = convert_type(func_ctype->ret_type);
    llvm::Type* returnType = convert_function_return_type(func_ctype->ret_type);
    llvm::FunctionType* llvmFuncType = llvm::FunctionType::get(
        returnType, paramTypes, func_ctype->is_variadic);
    bool callee_non_throwing =
        func_ctype->exception_spec == FunctionExceptionSpecKind::NonThrowing;

    size_t explicit_named_params =
        (has_implicit_object_param && named_params > 0)
            ? named_params - 1
            : named_params;
    if (!func_ctype->has_prototype) {
        // K&R style () — accept any number of explicit arguments
    } else if (func_ctype->is_variadic) {
        if (expr->args.size() < explicit_named_params) {
            error("Too few arguments passed to variadic function", expr->location);
            return nullptr;
        }
    } else if (expr->args.size() != explicit_named_params) {
        error("Incorrect # of arguments passed to function", expr->location);
        return nullptr;
    }

    // --- Evaluate member-pointer payload and object pointer ---
    llvm::Value* member_ptr_value =
        convert_expression(member_ptr_callee->member_pointer.get());
    if (!member_ptr_value) {
        error("emit_member_pointer_dispatch(): failed to evaluate member-function pointer operand",
              expr->location);
        return nullptr;
    }
    auto* member_ptr_struct_ty =
        llvm::dyn_cast<llvm::StructType>(member_ptr_value->getType());
    if (!member_ptr_struct_ty || member_ptr_struct_ty->getNumElements() != 2) {
        error("emit_member_pointer_dispatch(): invalid member-function pointer payload",
              expr->location);
        return nullptr;
    }

    llvm::Value* object_ptr = nullptr;
    if (member_ptr_callee->is_arrow) {
        object_ptr = convert_expression(member_ptr_callee->base.get());
        if (!object_ptr || !object_ptr->getType()->isPointerTy()) {
            error("emit_member_pointer_dispatch(): arrow call requires pointer object operand",
                  expr->location);
            return nullptr;
        }
    } else {
        auto base_lvalue = get_lvalue(member_ptr_callee->base.get());
        object_ptr = base_lvalue.address;
        if (!object_ptr) {
            auto base_object_type =
                desugar_type(member_ptr_callee->base->get_type(), ast_ctx.get())
                    .as_shared<ObjectType>();
            if (!base_object_type) {
                error("emit_member_pointer_dispatch(): dot call requires class object operand",
                      expr->location);
                return nullptr;
            }
            llvm::Value* base_rvalue =
                convert_expression(member_ptr_callee->base.get());
            llvm::Type* base_llvm_type = convert_type(base_object_type);
            llvm::Value* tmp = builder.CreateAlloca(
                base_llvm_type, nullptr, "tmp.dotstar.call.base");
            builder.CreateStore(base_rvalue, tmp);
            object_ptr = tmp;
        }
    }

    // --- Adjust `this` pointer from member-pointer payload ---
    llvm::Value* function_payload = builder.CreateExtractValue(
        member_ptr_value, {0}, "memberfn.payload");
    llvm::Value* this_adjust = builder.CreateExtractValue(
        member_ptr_value, {1}, "memberfn.adjust");
    llvm::Type* i64 = llvm::Type::getInt64Ty(*context);
    if (!this_adjust->getType()->isIntegerTy(64)) {
        this_adjust = cast_llvm_type(this_adjust, i64, false);
    }

    llvm::Value* adjusted_object_ptr = builder.CreateGEP(
        llvm::Type::getInt8Ty(*context),
        object_ptr,
        this_adjust,
        "memberfn.this.adjust");
    if (adjusted_object_ptr->getType() != object_ptr->getType()) {
        adjusted_object_ptr = cast_llvm_type(
            adjusted_object_ptr, object_ptr->getType(), false);
    }

    llvm::Value* call_this_ptr = adjusted_object_ptr;
    if (has_implicit_object_param &&
        call_this_ptr->getType() != paramTypes[abi_param_prefix]) {
        call_this_ptr = cast_llvm_type(
            call_this_ptr, paramTypes[abi_param_prefix], false);
    }

    std::shared_ptr<ObjectType> this_object_type = nullptr;
    if (has_implicit_object_param) {
        auto this_param_ptr_type =
            desugar_type(func_ctype->parameters.front(), ast_ctx.get())
                .as_shared<PointerType>();
        this_object_type = this_param_ptr_type
            ? desugar_type(this_param_ptr_type->pointed_type, ast_ctx.get())
                  .as_shared<ObjectType>()
            : nullptr;
    } else if (member_ptr_type) {
        this_object_type =
            desugar_type(member_ptr_type->class_type, ast_ctx.get())
                .as_shared<ObjectType>();
    }
    if (!this_object_type) {
        error("emit_member_pointer_dispatch(): invalid implicit object type",
              expr->location);
        return nullptr;
    }

    // --- Direct vs. virtual dispatch branch ---
    // Itanium-style member-function pointer payload:
    // low bit set => virtual call; remaining bits encode vtable slot index.
    llvm::Value* function_token = builder.CreatePtrToInt(
        function_payload, i64, "memberfn.token");
    llvm::Value* is_virtual = builder.CreateICmpNE(
        builder.CreateAnd(
            function_token,
            llvm::ConstantInt::get(i64, 1, false),
            "memberfn.token.tag"),
        llvm::ConstantInt::get(i64, 0, false),
        "memberfn.is_virtual");

    llvm::Function* current_fn =
        builder.GetInsertBlock() ? builder.GetInsertBlock()->getParent() : nullptr;
    if (!current_fn) {
        error("emit_member_pointer_dispatch(): call outside of function",
              expr->location);
        return nullptr;
    }

    auto* direct_bb = llvm::BasicBlock::Create(
        *context, "memberfn.direct", current_fn);
    auto* virtual_bb = llvm::BasicBlock::Create(
        *context, "memberfn.virtual", current_fn);
    auto* join_bb = llvm::BasicBlock::Create(
        *context, "memberfn.join", current_fn);
    builder.CreateCondBr(is_virtual, virtual_bb, direct_bb);

    builder.SetInsertPoint(direct_bb);
    llvm::Value* direct_callee = function_payload;
    builder.CreateBr(join_bb);

    builder.SetInsertPoint(virtual_bb);
    if (!ensure_supported_cpp_vtable_abi(
            expr->location,
            "emit_member_pointer_dispatch(virtual dispatch)")) {
        return nullptr;
    }
    llvm::Type* object_llvm_type = convert_type(this_object_type);
    auto* object_struct_ty = llvm::dyn_cast<llvm::StructType>(object_llvm_type);
    if (!object_struct_ty || object_struct_ty->getNumElements() == 0) {
        error("emit_member_pointer_dispatch(): invalid object layout for virtual dispatch",
              expr->location);
        return nullptr;
    }
    auto* ptr_ty = llvm::dyn_cast<llvm::PointerType>(function_payload->getType());
    if (!ptr_ty) {
        error("emit_member_pointer_dispatch(): invalid payload pointer type",
              expr->location);
        return nullptr;
    }
    llvm::Value* typed_this_ptr = call_this_ptr;
    llvm::Type* expected_this_ptr_type = llvm::PointerType::get(*context, 0);
    if (typed_this_ptr->getType() != expected_this_ptr_type) {
        typed_this_ptr = cast_llvm_type(
            typed_this_ptr, expected_this_ptr_type, false);
    }
    llvm::Value* vptr_addr = builder.CreateStructGEP(
        object_struct_ty, typed_this_ptr, 0, "memberfn.vptr.addr");
    llvm::Value* raw_vptr = builder.CreateLoad(ptr_ty, vptr_addr, "memberfn.vptr");
    auto* table_ptr_ty = llvm::PointerType::get(ptr_ty, 0);
    llvm::Value* vtable_ptr = builder.CreateBitCast(
        raw_vptr, table_ptr_ty, "memberfn.vtable.ptr");
    llvm::Value* slot_index = builder.CreateLShr(
        function_token,
        llvm::ConstantInt::get(i64, 1, false),
        "memberfn.slot");
    llvm::Value* slot_addr = builder.CreateInBoundsGEP(
        ptr_ty, vtable_ptr, slot_index, "memberfn.slot.addr");
    llvm::Value* virtual_callee = builder.CreateLoad(
        ptr_ty, slot_addr, "memberfn.virtual.callee");
    builder.CreateBr(join_bb);

    builder.SetInsertPoint(join_bb);
    auto* callee_phi =
        builder.CreatePHI(function_payload->getType(), 2, "memberfn.callee");
    callee_phi->addIncoming(direct_callee, direct_bb);
    callee_phi->addIncoming(virtual_callee, virtual_bb);
    llvm::Value* calleeVal = callee_phi;

    // --- Build argument list with per-parameter metadata ---
    struct ParamInfo {
        bool byref = false;
        bool direct_aggregate = false;
        bool reference = false;
        QualType referred_type;
    };
    std::vector<ParamInfo> param_info(named_params);
    size_t declared_param_base_index = has_implicit_object_param ? 1 : 0;
    for (size_t i = declared_param_base_index; i < named_params; ++i) {
        auto param_canonical = desugar_type(func_ctype->parameters[i], ast_ctx.get());
        if (auto ref_type = param_canonical.as_shared<ReferenceType>()) {
            param_info[i].reference = true;
            param_info[i].referred_type = ref_type->referred_type;
            continue;
        }
        param_info[i].byref = pass_aggregate_by_reference(func_ctype->parameters[i]);
        param_info[i].direct_aggregate =
            !param_info[i].byref &&
            has_direct_aggregate_parameter_abi(func_ctype->parameters[i]);
    }

    std::vector<llvm::Value*> argsV;
    argsV.reserve(expr->args.size() + 1 + abi_param_prefix);
    llvm::AllocaInst* indirect_result_slot = nullptr;
    if (abi_param_prefix != 0) {
        llvm::Function* function = builder.GetInsertBlock()->getParent();
        indirect_result_slot = create_indirect_result_slot(
            function, func_ctype->ret_type, "memberfn.sret");
        if (!indirect_result_slot) {
            error("emit_member_pointer_dispatch(): failed to allocate indirect result slot",
                  expr->location);
            return nullptr;
        }
        argsV.push_back(indirect_result_slot);
    }
    argsV.push_back(call_this_ptr);

    for (size_t i = 0; i < expr->args.size(); ++i) {
        Expr* arg_expr = expr->args[i].get();
        size_t param_index = i + declared_param_base_index;
        bool is_named_param = func_ctype->has_prototype &&
            param_index < named_params;

        if (is_named_param && param_info[param_index].reference) {
            Expr* lvalue_base = unwrap_reference_binding_expr(arg_expr);
            llvm::Value* ref_ptr = get_lvalue(lvalue_base).address;
            if (!ref_ptr) {
                llvm::Value* arg_val = convert_expression(arg_expr);
                if (!arg_val) {
                    error("argument in emit_member_pointer_dispatch invalid", expr->location);
                    return nullptr;
                }

                QualType referred_type = param_info[param_index].referred_type;
                if (!referred_type) {
                    error("emit_member_pointer_dispatch(): invalid reference parameter type",
                          expr->location);
                    return nullptr;
                }
                llvm::Type* referred_llvm_type =
                    convert_type(referred_type.get_shared());
                if (!referred_llvm_type) {
                    error("emit_member_pointer_dispatch(): failed to lower reference target type",
                          expr->location);
                    return nullptr;
                }
                if (arg_val->getType() != referred_llvm_type) {
                    bool src_unsigned =
                        arg_expr->get_type() && arg_expr->get_type()->isUnsigned();
                    arg_val = cast_llvm_type(arg_val, referred_llvm_type, src_unsigned);
                }

                llvm::Function* fn = builder.GetInsertBlock()->getParent();
                llvm::Value* tmp =
                    create_entry_alloca(fn, referred_llvm_type, nullptr, "ref.arg.tmp");
                if (!tmp) {
                    error("emit_member_pointer_dispatch(): failed to allocate reference argument temporary",
                          expr->location);
                    return nullptr;
                }
                builder.CreateStore(arg_val, tmp);
                ref_ptr = tmp;
            }
            argsV.push_back(ref_ptr);
            continue;
        }

        if (is_named_param && param_info[param_index].byref) {
            llvm::Value* byref_ptr = materialize_indirect_aggregate_argument(
                *this,
                func_ctype->parameters[param_index],
                arg_expr,
                expr->location,
                "byref.tmp");
            if (!byref_ptr) {
                return nullptr;
            }
            argsV.push_back(byref_ptr);
            continue;
        }

        if (is_named_param && param_info[param_index].direct_aggregate) {
            llvm::Value* coerced_arg = materialize_direct_aggregate_argument(
                *this,
                func_ctype->parameters[param_index],
                arg_expr,
                expr->location,
                "coerce.tmp");
            if (!coerced_arg) {
                return nullptr;
            }
            argsV.push_back(coerced_arg);
            continue;
        }

        llvm::Value* arg_val = convert_expression(arg_expr);
        if (!arg_val) {
            error("argument in emit_member_pointer_dispatch invalid", expr->location);
            return nullptr;
        }

        bool is_vararg_arg = func_ctype->is_variadic && i >= explicit_named_params;
        if (is_vararg_arg && target && target->va_list_kind == VaListKind::CHAR_PTR) {
            llvm::Type* arg_ty = arg_val->getType();
            if (arg_ty->isAggregateType()) {
                size_t arg_size = module->getDataLayout().getTypeAllocSize(arg_ty);

                if (arg_size > 16) {
                    Expr* lvalue_base = unwrap_reference_binding_expr(arg_expr);
                    llvm::Value* arg_ptr = get_lvalue(lvalue_base).address;
                    if (!arg_ptr) {
                        llvm::Function* fn = builder.GetInsertBlock()->getParent();
                        llvm::IRBuilder<> tmpBuilder(
                            &fn->getEntryBlock(), fn->getEntryBlock().begin());
                        arg_ptr = tmpBuilder.CreateAlloca(
                            arg_ty, nullptr, "vararg.indirect.tmp");
                        builder.CreateStore(arg_val, arg_ptr);
                    }
                    argsV.push_back(arg_ptr);
                    continue;
                }

                size_t slot_size = ((arg_size + 7) / 8) * 8;
                if (slot_size == 0) slot_size = 8;

                auto* blob_ty = llvm::ArrayType::get(
                    llvm::Type::getInt8Ty(*context), slot_size);
                llvm::Type* coerce_ty = nullptr;
                if (slot_size == 8) {
                    coerce_ty = llvm::Type::getInt64Ty(*context);
                } else {
                    coerce_ty = llvm::ArrayType::get(
                        llvm::Type::getInt64Ty(*context), slot_size / 8);
                }

                llvm::Function* fn = builder.GetInsertBlock()->getParent();
                llvm::IRBuilder<> tmpBuilder(
                    &fn->getEntryBlock(), fn->getEntryBlock().begin());
                llvm::Value* tmp = tmpBuilder.CreateAlloca(
                    arg_ty, nullptr, "vararg.coerce.tmp");
                llvm::Value* blob_tmp = tmpBuilder.CreateAlloca(
                    blob_ty, nullptr, "vararg.coerce.blob");
                builder.CreateStore(llvm::Constant::getNullValue(blob_ty), blob_tmp);
                builder.CreateStore(arg_val, tmp);
                builder.CreateMemCpy(
                    blob_tmp, llvm::Align(1), tmp, llvm::Align(1), arg_size);
                llvm::Value* coerced = builder.CreateLoad(
                    coerce_ty, blob_tmp, "vararg.coerce");
                argsV.push_back(coerced);
                continue;
            }
        }

        argsV.push_back(arg_val);
    }

    if ((!func_ctype->has_prototype || !has_implicit_object_param) &&
        !argsV.empty()) {
        std::vector<llvm::Type*> actualParamTypes;
        actualParamTypes.reserve(argsV.size());
        for (auto* v : argsV) {
            actualParamTypes.push_back(v->getType());
        }
        llvmFuncType = llvm::FunctionType::get(returnType, actualParamTypes, false);
    }

    // --- Emit call/invoke ---
    llvm::CallBase* call_inst = nullptr;
    bool emit_invoke = should_emit_invoke_for_callee(calleeVal, func_ctype.get());
    if (emit_invoke) {
        llvm::Function* function = builder.GetInsertBlock()->getParent();
        auto* continue_bb = llvm::BasicBlock::Create(
            *context, "invoke.cont", function);
        auto* unwind_bb = eh_region_stack.back().landing_pad_block;
        if (returnType->isVoidTy()) {
            call_inst = builder.CreateInvoke(
                llvmFuncType, calleeVal, continue_bb, unwind_bb, argsV);
        } else {
            call_inst = builder.CreateInvoke(
                llvmFuncType, calleeVal, continue_bb, unwind_bb, argsV, "calltmp");
        }
        builder.SetInsertPoint(continue_bb);
    } else if (returnType->isVoidTy()) {
        call_inst = builder.CreateCall(llvmFuncType, calleeVal, argsV);
    } else {
        call_inst = builder.CreateCall(llvmFuncType, calleeVal, argsV, "calltmp");
    }

    if (!emit_invoke && call_inst) {
        bool callee_has_nounwind = false;
        llvm::Value* stripped = calleeVal->stripPointerCasts();
        if (auto* fn = llvm::dyn_cast<llvm::Function>(stripped)) {
            callee_has_nounwind = fn->hasFnAttribute(llvm::Attribute::NoUnwind);
        }
        if (callee_non_throwing || callee_has_nounwind) {
            call_inst->setDoesNotThrow();
        }
    }
    apply_indirect_result_attributes(call_inst, 0, func_ctype->ret_type);
    if (indirect_result_slot) {
        return builder.CreateLoad(returnValueType, indirect_result_slot,
                                  "memberfn.sret.load");
    }
    return call_inst;
}
