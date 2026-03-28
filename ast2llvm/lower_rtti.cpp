#include "ast2llvm.h"

namespace {

enum class CppExprValueCategory : uint8_t {
    Unknown,
    LValue,
    XValue,
    PRValue,
};

CppExprValueCategory classify_cpp_expr_value_category(
    Expr* expr,
    const ASTContext* ast_ctx) {
    if (!expr) {
        return CppExprValueCategory::Unknown;
    }

    if (auto* cast = dyn_cast<ImplicitCast>(expr)) {
        switch (cast->kind) {
            case ImplicitCastTypes::UNKNOWN:
                return classify_cpp_expr_value_category(cast->expr.get(), ast_ctx);
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
                if (auto ref = desugar_type(cast->ctype, ast_ctx).as_shared<ReferenceType>()) {
                    return ref->isRValueReference()
                        ? CppExprValueCategory::XValue
                        : CppExprValueCategory::LValue;
                }
                return CppExprValueCategory::PRValue;
        }
    }

    if (auto* cast = dyn_cast<ExplicitCast>(expr)) {
        if (auto ref = desugar_type(cast->get_type(), ast_ctx).as_shared<ReferenceType>()) {
            return ref->isRValueReference()
                ? CppExprValueCategory::XValue
                : CppExprValueCategory::LValue;
        }
        return CppExprValueCategory::PRValue;
    }

    if (auto* call = dyn_cast<FuncCall>(expr)) {
        if (auto ref = desugar_type(call->get_type(), ast_ctx).as_shared<ReferenceType>()) {
            return ref->isRValueReference()
                ? CppExprValueCategory::XValue
                : CppExprValueCategory::LValue;
        }
        return CppExprValueCategory::PRValue;
    }

    if (auto* call = dyn_cast<CppMemberCallExpr>(expr)) {
        if (auto ref = desugar_type(call->get_type(), ast_ctx).as_shared<ReferenceType>()) {
            return ref->isRValueReference()
                ? CppExprValueCategory::XValue
                : CppExprValueCategory::LValue;
        }
        return CppExprValueCategory::PRValue;
    }

    if (auto* dynamic_cast_expr = dyn_cast<CppDynamicCastExpr>(expr)) {
        if (auto ref = desugar_type(dynamic_cast_expr->get_type(), ast_ctx)
                           .as_shared<ReferenceType>()) {
            return ref->isRValueReference()
                ? CppExprValueCategory::XValue
                : CppExprValueCategory::LValue;
        }
        return CppExprValueCategory::PRValue;
    }

    if (auto* unary = dyn_cast<UnaryOperation>(expr)) {
        switch (unary->uop) {
            case UnaryOpTypes::INCREMENT_PREFIX:
            case UnaryOpTypes::DECREMENT_PREFIX:
            case UnaryOpTypes::DEREFERENCE:
                return CppExprValueCategory::LValue;
            case UnaryOpTypes::REAL_PART:
            case UnaryOpTypes::IMAG_PART: {
                auto operand_category =
                    classify_cpp_expr_value_category(unary->exp.get(), ast_ctx);
                if (operand_category == CppExprValueCategory::LValue ||
                    operand_category == CppExprValueCategory::XValue) {
                    return operand_category;
                }
                return CppExprValueCategory::PRValue;
            }
            default:
                return CppExprValueCategory::PRValue;
        }
    }

    if (auto* member = dyn_cast<MemberExpr>(expr)) {
        if (!member->isArrow) {
            auto base_category =
                classify_cpp_expr_value_category(member->base.get(), ast_ctx);
            if (base_category == CppExprValueCategory::XValue ||
                base_category == CppExprValueCategory::PRValue) {
                return CppExprValueCategory::XValue;
            }
        }
        return CppExprValueCategory::LValue;
    }

    if (auto* member_ptr = dyn_cast<MemberPointerAccessExpr>(expr)) {
        if (member_ptr->is_function_member) {
            return CppExprValueCategory::PRValue;
        }
        if (!member_ptr->is_arrow) {
            auto base_category =
                classify_cpp_expr_value_category(member_ptr->base.get(), ast_ctx);
            if (base_category == CppExprValueCategory::XValue ||
                base_category == CppExprValueCategory::PRValue) {
                return CppExprValueCategory::XValue;
            }
        }
        return CppExprValueCategory::LValue;
    }

    if (auto* binary = dyn_cast<BinaryOperation>(expr)) {
        if (binary->bop == BinOpTypes::COMMA) {
            return classify_cpp_expr_value_category(binary->right.get(), ast_ctx);
        }
        return CppExprValueCategory::PRValue;
    }

    if (auto* cond = dyn_cast<CondExpr>(expr)) {
        Expr* true_operand = cond->true_expr ? cond->true_expr.get() : cond->condition.get();
        auto true_category = classify_cpp_expr_value_category(true_operand, ast_ctx);
        auto false_category =
            classify_cpp_expr_value_category(cond->false_expr.get(), ast_ctx);
        bool true_is_glvalue =
            true_category == CppExprValueCategory::LValue ||
            true_category == CppExprValueCategory::XValue;
        bool false_is_glvalue =
            false_category == CppExprValueCategory::LValue ||
            false_category == CppExprValueCategory::XValue;
        if (!true_is_glvalue || !false_is_glvalue || true_category != false_category) {
            return CppExprValueCategory::PRValue;
        }

        auto true_type = true_operand ? true_operand->get_type() : QualType();
        auto false_type = cond->false_expr ? cond->false_expr->get_type() : QualType();
        if (!true_type || !false_type || !true_type.equals_unqualified(false_type)) {
            return CppExprValueCategory::PRValue;
        }
        return true_category;
    }

    if (expr->isLValue()) {
        return CppExprValueCategory::LValue;
    }
    return CppExprValueCategory::PRValue;
}

bool is_cpp_glvalue(Expr* expr, const ASTContext* ast_ctx) {
    CppExprValueCategory category =
        classify_cpp_expr_value_category(expr, ast_ctx);
    return category == CppExprValueCategory::LValue ||
           category == CppExprValueCategory::XValue;
}

} // namespace

llvm::Value* ASTToLLVM::convert_cpp_typeid_expression(CppTypeIdExpr* expr) {
    if (!expr) {
        error("convert_cpp_typeid_expression(): invalid typeid expression");
        return nullptr;
    }
    if (!ensure_supported_cpp_vtable_abi(expr->location, "convert_cpp_typeid_expression()")) {
        return nullptr;
    }

    QualType operand_type = expr->is_type_operand
        ? expr->type_operand
        : (expr->expr_operand ? expr->expr_operand->get_type() : QualType());
    if (!operand_type) {
        error("convert_cpp_typeid_expression(): typeid operand has unknown type",
              expr->location);
        return nullptr;
    }

    QualType normalized_operand_type = desugar_type(
        remove_reference(operand_type, ast_ctx.get()),
        ast_ctx.get()).without_qualifiers();

    bool needs_dynamic_lookup = false;
    std::shared_ptr<ObjectType> operand_object_type;
    const RecordSemanticState* operand_state = nullptr;
    bool operand_is_glvalue =
        !expr->is_type_operand && expr->expr_operand &&
        is_cpp_glvalue(expr->expr_operand.get(), ast_ctx.get());
    if (!expr->is_type_operand && expr->expr_operand && operand_is_glvalue) {
        operand_object_type =
            normalized_operand_type.as_shared<ObjectType>();
        if (operand_object_type) {
            const ObjectDecl* record_decl = canonical_cpp_record_decl(
                dyn_cast<ObjectDecl>(operand_object_type->get_decl()));
            operand_state = lookup_cpp_record_state(record_decl);
            needs_dynamic_lookup = operand_state && operand_state->is_polymorphic;
        }
    }

    auto* ptr_ty = llvm::PointerType::get(*context, 0);
    llvm::Value* typeinfo_ptr = nullptr;

    if (needs_dynamic_lookup) {
        auto lvalue = get_lvalue(expr->expr_operand.get());
        llvm::Value* object_addr = lvalue.address;
        if (!object_addr || !object_addr->getType()->isPointerTy() ||
            !operand_object_type) {
            error("convert_cpp_typeid_expression(): failed to evaluate polymorphic glvalue operand",
                  expr->location);
            return nullptr;
        }

        llvm::Type* object_llvm_type = convert_type(operand_object_type);
        auto* object_struct_ty = llvm::dyn_cast<llvm::StructType>(object_llvm_type);
        if (!object_struct_ty || object_struct_ty->getNumElements() == 0) {
            error("convert_cpp_typeid_expression(): polymorphic type has invalid LLVM layout",
                  expr->location);
            return nullptr;
        }
        llvm::Type* object_ptr_ty = llvm::PointerType::get(object_struct_ty, 0);
        if (object_addr->getType() != object_ptr_ty) {
            object_addr = cast_llvm_type(object_addr, object_ptr_ty, false);
        }

        llvm::Value* null_obj = llvm::ConstantPointerNull::get(
            llvm::cast<llvm::PointerType>(object_ptr_ty));
        llvm::Value* is_null = builder.CreateICmpEQ(object_addr, null_obj, "typeid.obj.isnull");
        auto* current_fn = builder.GetInsertBlock()
            ? builder.GetInsertBlock()->getParent()
            : nullptr;
        if (!current_fn) {
            error("convert_cpp_typeid_expression(): not inside a function",
                  expr->location);
            return nullptr;
        }
        auto* bad_typeid_bb =
            llvm::BasicBlock::Create(*context, "typeid.badtypeid", current_fn);
        auto* continue_bb =
            llvm::BasicBlock::Create(*context, "typeid.continue", current_fn);
        builder.CreateCondBr(is_null, bad_typeid_bb, continue_bb);

        builder.SetInsertPoint(bad_typeid_bb);
        llvm::Function* bad_typeid_fn = get_or_create_cxa_bad_typeid();
        if (!bad_typeid_fn) {
            error("convert_cpp_typeid_expression(): failed to lower __cxa_bad_typeid",
                  expr->location);
            return nullptr;
        }
        if (should_emit_invoke_for_callee(bad_typeid_fn)) {
            auto* invoke_unreachable_bb =
                llvm::BasicBlock::Create(*context, "typeid.badtypeid.invoke.cont", current_fn);
            auto* unwind_bb = eh_region_stack.back().landing_pad_block;
            builder.CreateInvoke(bad_typeid_fn->getFunctionType(),
                                 bad_typeid_fn,
                                 invoke_unreachable_bb,
                                 unwind_bb,
                                 {});
            builder.SetInsertPoint(invoke_unreachable_bb);
            builder.CreateUnreachable();
        } else {
            builder.CreateCall(bad_typeid_fn);
            builder.CreateUnreachable();
        }

        builder.SetInsertPoint(continue_bb);
        llvm::Value* vptr_addr = builder.CreateStructGEP(
            object_struct_ty, object_addr, 0, "typeid.vptr.addr");
        llvm::Value* raw_vptr = builder.CreateLoad(ptr_ty, vptr_addr, "typeid.vptr");
        auto* table_ptr_ty = llvm::PointerType::get(ptr_ty, 0);
        llvm::Value* address_point_ptr = builder.CreateBitCast(
            raw_vptr, table_ptr_ty, "typeid.address.point");
        llvm::Value* typeinfo_index = llvm::ConstantInt::get(
            llvm::Type::getInt64Ty(*context), -1, true);
        llvm::Value* typeinfo_addr = builder.CreateInBoundsGEP(
            ptr_ty, address_point_ptr, typeinfo_index, "typeid.typeinfo.addr");
        typeinfo_ptr = builder.CreateLoad(ptr_ty, typeinfo_addr, "typeid.typeinfo");
    } else {
        llvm::GlobalVariable* static_typeinfo =
            get_or_create_itanium_typeinfo_global(normalized_operand_type);
        if (!static_typeinfo) {
            error("convert_cpp_typeid_expression(): cannot materialize RTTI typeinfo for operand",
                  expr->location);
            return nullptr;
        }
        typeinfo_ptr = llvm::ConstantExpr::getBitCast(static_typeinfo, ptr_ty);
    }

    llvm::Type* result_type = convert_type(expr->get_type());
    if (!result_type) {
        error("convert_cpp_typeid_expression(): failed to lower result type",
              expr->location);
        return nullptr;
    }
    if (typeinfo_ptr->getType() != result_type) {
        typeinfo_ptr = cast_llvm_type(typeinfo_ptr, result_type, false);
    }
    return typeinfo_ptr;
}

llvm::Value* ASTToLLVM::convert_cpp_dynamic_cast_expression(CppDynamicCastExpr* expr) {
    if (!expr) {
        error("convert_cpp_dynamic_cast_expression(): invalid dynamic_cast expression");
        return nullptr;
    }
    if (!ensure_supported_cpp_vtable_abi(expr->location, "convert_cpp_dynamic_cast_expression()")) {
        return nullptr;
    }
    if (!expr->expr) {
        error("convert_cpp_dynamic_cast_expression(): missing dynamic_cast operand", expr->location);
        return nullptr;
    }

    QualType source_type = desugar_type(expr->expr->get_type(), ast_ctx.get());
    QualType target_type = desugar_type(expr->get_type(), ast_ctx.get());
    if (!source_type || !target_type) {
        error("convert_cpp_dynamic_cast_expression(): unknown source or target type",
              expr->location);
        return nullptr;
    }

    auto* ptr_ty = llvm::PointerType::get(*context, 0);
    llvm::Type* intptr_ty = module->getDataLayout().getIntPtrType(*context, 0);

    auto get_class_object_type = [&](QualType type) -> std::shared_ptr<ObjectType> {
        return desugar_type(remove_reference(type, ast_ctx.get()), ast_ctx.get())
            .without_qualifiers()
            .as_shared<ObjectType>();
    };

    auto lower_runtime_dynamic_cast =
        [&](llvm::Value* source_addr,
            QualType source_object_qt,
            QualType target_object_qt,
            const std::string& value_name) -> llvm::Value* {
        if (!source_addr || !source_addr->getType()->isPointerTy()) {
            return nullptr;
        }
        llvm::Function* dynamic_cast_fn = get_or_create_cxx_dynamic_cast();
        if (!dynamic_cast_fn) {
            return nullptr;
        }
        llvm::GlobalVariable* source_typeinfo =
            get_or_create_itanium_typeinfo_global(source_object_qt);
        llvm::GlobalVariable* target_typeinfo =
            get_or_create_itanium_typeinfo_global(target_object_qt);
        if (!source_typeinfo || !target_typeinfo) {
            return nullptr;
        }

        llvm::Value* source_void_ptr = source_addr;
        if (source_void_ptr->getType() != ptr_ty) {
            source_void_ptr = cast_llvm_type(source_void_ptr, ptr_ty, false);
        }
        llvm::Value* source_typeinfo_ptr =
            llvm::ConstantExpr::getBitCast(source_typeinfo, ptr_ty);
        llvm::Value* target_typeinfo_ptr =
            llvm::ConstantExpr::getBitCast(target_typeinfo, ptr_ty);
        llvm::Value* src2dst_offset = llvm::ConstantInt::get(intptr_ty, -1, true);

        return builder.CreateCall(
            dynamic_cast_fn,
            {source_void_ptr, source_typeinfo_ptr, target_typeinfo_ptr, src2dst_offset},
            value_name);
    };

    if (auto target_ptr = target_type.as_shared<PointerType>()) {
        auto source_ptr = source_type.as_shared<PointerType>();
        if (!source_ptr) {
            error("convert_cpp_dynamic_cast_expression(): pointer dynamic_cast requires pointer source",
                  expr->location);
            return nullptr;
        }

        llvm::Value* source_ptr_value = convert_expression(expr->expr.get());
        if (!source_ptr_value || !source_ptr_value->getType()->isPointerTy()) {
            error("convert_cpp_dynamic_cast_expression(): failed to evaluate pointer operand",
                  expr->location);
            return nullptr;
        }

        auto source_object_type = get_class_object_type(source_ptr->pointed_type);
        if (!source_object_type) {
            error("convert_cpp_dynamic_cast_expression(): pointer source is not a class type",
                  expr->location);
            return nullptr;
        }
        const ObjectDecl* source_object_decl = canonical_cpp_record_decl(
            dyn_cast<ObjectDecl>(source_object_type->get_decl()));
        if (!source_object_decl) {
            error("convert_cpp_dynamic_cast_expression(): pointer source is not bound to a class declaration",
                  expr->location);
            return nullptr;
        }
        QualType source_object_qt = desugar_type(
            remove_reference(source_ptr->pointed_type, ast_ctx.get()),
            ast_ctx.get()).without_qualifiers();

        llvm::Type* result_type = convert_type(expr->get_type());
        if (!result_type || !result_type->isPointerTy()) {
            error("convert_cpp_dynamic_cast_expression(): failed to lower pointer result type",
                  expr->location);
            return nullptr;
        }

        if (target_ptr->pointed_type && target_ptr->pointed_type->isVoid()) {
            llvm::Type* source_object_llvm_type = convert_type(source_object_type);
            auto* source_struct_ty = llvm::dyn_cast<llvm::StructType>(source_object_llvm_type);
            if (!source_struct_ty || source_struct_ty->getNumElements() == 0) {
                error("convert_cpp_dynamic_cast_expression(): invalid polymorphic source layout for void* cast",
                      expr->location);
                return nullptr;
            }

            llvm::Type* source_object_ptr_ty = llvm::PointerType::get(source_struct_ty, 0);
            llvm::Value* source_object_ptr = source_ptr_value;
            if (source_object_ptr->getType() != source_object_ptr_ty) {
                source_object_ptr = cast_llvm_type(source_object_ptr, source_object_ptr_ty, false);
            }

            llvm::Value* top_ptr = recover_cpp_complete_object_address(
                source_object_ptr,
                source_object_decl,
                expr->location,
                "convert_cpp_dynamic_cast_expression()");
            if (!top_ptr) {
                error("convert_cpp_dynamic_cast_expression(): failed to recover complete object address for void* cast",
                      expr->location);
                return nullptr;
            }
            if (top_ptr->getType() != result_type) {
                top_ptr = cast_llvm_type(top_ptr, result_type, false);
            }
            return top_ptr;
        }

        auto target_object_type = get_class_object_type(target_ptr->pointed_type);
        if (!target_object_type) {
            error("convert_cpp_dynamic_cast_expression(): pointer target is not a class type",
                  expr->location);
            return nullptr;
        }
        QualType target_object_qt = desugar_type(
            remove_reference(target_ptr->pointed_type, ast_ctx.get()),
            ast_ctx.get()).without_qualifiers();

        auto* current_fn = builder.GetInsertBlock() ? builder.GetInsertBlock()->getParent() : nullptr;
        if (!current_fn) {
            error("convert_cpp_dynamic_cast_expression(): not inside a function", expr->location);
            return nullptr;
        }
        auto* entry_bb = builder.GetInsertBlock();
        llvm::Value* null_source = llvm::ConstantPointerNull::get(
            llvm::cast<llvm::PointerType>(source_ptr_value->getType()));
        llvm::Value* is_null = builder.CreateICmpEQ(
            source_ptr_value, null_source, "dyn.cast.ptr.isnull");
        auto* runtime_cast_bb =
            llvm::BasicBlock::Create(*context, "dyn.cast.ptr.runtime", current_fn);
        auto* merge_bb =
            llvm::BasicBlock::Create(*context, "dyn.cast.ptr.merge", current_fn);
        builder.CreateCondBr(is_null, merge_bb, runtime_cast_bb);

        builder.SetInsertPoint(runtime_cast_bb);
        llvm::Value* cast_result = lower_runtime_dynamic_cast(
            source_ptr_value,
            source_object_qt,
            target_object_qt,
            "dyn.cast.ptr.raw");
        if (!cast_result) {
            error("convert_cpp_dynamic_cast_expression(): failed to lower __dynamic_cast pointer form",
                  expr->location);
            return nullptr;
        }
        if (cast_result->getType() != result_type) {
            cast_result = cast_llvm_type(cast_result, result_type, false);
        }
        builder.CreateBr(merge_bb);
        auto* cast_end_bb = builder.GetInsertBlock();

        builder.SetInsertPoint(merge_bb);
        llvm::Value* null_result = llvm::ConstantPointerNull::get(
            llvm::cast<llvm::PointerType>(result_type));
        auto* phi = builder.CreatePHI(result_type, 2, "dyn.cast.ptr.result");
        phi->addIncoming(null_result, entry_bb);
        phi->addIncoming(cast_result, cast_end_bb);
        return phi;
    }

    auto source_ref = source_type.as_shared<ReferenceType>();
    auto target_ref = target_type.as_shared<ReferenceType>();
    if (!source_ref || !target_ref || !source_ref->referred_type || !target_ref->referred_type) {
        error("convert_cpp_dynamic_cast_expression(): reference dynamic_cast requires reference source and target",
              expr->location);
        return nullptr;
    }

    auto source_object_type = get_class_object_type(source_ref->referred_type);
    auto target_object_type = get_class_object_type(target_ref->referred_type);
    if (!source_object_type || !target_object_type) {
        error("convert_cpp_dynamic_cast_expression(): reference dynamic_cast requires class object types",
              expr->location);
        return nullptr;
    }
    QualType source_object_qt = desugar_type(
        remove_reference(source_ref->referred_type, ast_ctx.get()),
        ast_ctx.get()).without_qualifiers();
    QualType target_object_qt = desugar_type(
        remove_reference(target_ref->referred_type, ast_ctx.get()),
        ast_ctx.get()).without_qualifiers();

    llvm::Value* source_addr = get_lvalue(expr->expr.get()).address;
    if (!source_addr || !source_addr->getType()->isPointerTy()) {
        source_addr = convert_expression(expr->expr.get());
    }
    if (!source_addr || !source_addr->getType()->isPointerTy()) {
        error("convert_cpp_dynamic_cast_expression(): failed to evaluate reference source address",
              expr->location);
        return nullptr;
    }

    llvm::Type* source_object_llvm_type = convert_type(source_object_type);
    if (!source_object_llvm_type) {
        error("convert_cpp_dynamic_cast_expression(): failed to lower reference source object type",
              expr->location);
        return nullptr;
    }
    llvm::Type* source_object_ptr_ty = llvm::PointerType::get(source_object_llvm_type, 0);
    if (source_addr->getType() != source_object_ptr_ty) {
        source_addr = cast_llvm_type(source_addr, source_object_ptr_ty, false);
    }

    llvm::Value* cast_result = lower_runtime_dynamic_cast(
        source_addr,
        source_object_qt,
        target_object_qt,
        "dyn.cast.ref.raw");
    if (!cast_result) {
        error("convert_cpp_dynamic_cast_expression(): failed to lower __dynamic_cast reference form",
              expr->location);
        return nullptr;
    }

    llvm::Value* null_result = llvm::ConstantPointerNull::get(
        llvm::cast<llvm::PointerType>(ptr_ty));
    llvm::Value* is_null = builder.CreateICmpEQ(cast_result, null_result, "dyn.cast.ref.isnull");
    auto* current_fn = builder.GetInsertBlock() ? builder.GetInsertBlock()->getParent() : nullptr;
    if (!current_fn) {
        error("convert_cpp_dynamic_cast_expression(): not inside a function", expr->location);
        return nullptr;
    }

    auto* bad_cast_bb = llvm::BasicBlock::Create(*context, "dyn.cast.ref.badcast", current_fn);
    auto* continue_bb = llvm::BasicBlock::Create(*context, "dyn.cast.ref.continue", current_fn);
    builder.CreateCondBr(is_null, bad_cast_bb, continue_bb);

    builder.SetInsertPoint(bad_cast_bb);
    llvm::Function* bad_cast_fn = get_or_create_cxa_bad_cast();
    if (!bad_cast_fn) {
        error("convert_cpp_dynamic_cast_expression(): failed to lower __cxa_bad_cast",
              expr->location);
        return nullptr;
    }
    if (should_emit_invoke_for_callee(bad_cast_fn)) {
        auto* invoke_unreachable_bb =
            llvm::BasicBlock::Create(*context, "dyn.cast.ref.badcast.invoke.cont", current_fn);
        auto* unwind_bb = eh_region_stack.back().landing_pad_block;
        builder.CreateInvoke(bad_cast_fn->getFunctionType(),
                             bad_cast_fn,
                             invoke_unreachable_bb,
                             unwind_bb,
                             {});
        builder.SetInsertPoint(invoke_unreachable_bb);
        builder.CreateUnreachable();
    } else {
        builder.CreateCall(bad_cast_fn);
        builder.CreateUnreachable();
    }

    builder.SetInsertPoint(continue_bb);
    llvm::Type* result_type = convert_type(expr->get_type());
    if (!result_type || !result_type->isPointerTy()) {
        error("convert_cpp_dynamic_cast_expression(): failed to lower reference result type",
              expr->location);
        return nullptr;
    }
    if (cast_result->getType() != result_type) {
        cast_result = cast_llvm_type(cast_result, result_type, false);
    }
    return cast_result;
}
