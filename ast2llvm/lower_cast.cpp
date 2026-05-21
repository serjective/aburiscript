#include "ast2llvm.h"
#include "lower_helpers.h"
#include "const_lowering.h"
#include "../helpers/casting.h"
#include "../constexpr/consteval_compat.h"
#include "../numeric_utils.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include <algorithm>
#include <cstdlib>
#include <functional>
#include <limits>
#include <optional>
#include <unordered_set>

llvm::Value* ASTToLLVM::convert_implicit_cast(ImplicitCast *expr) {
    if (canonical_type_kind(expr->ctype, ast_ctx.get()) == TypeKind::Reference) {
        auto ref_type =
            desugar_type(expr->ctype, ast_ctx.get()).as_shared<ReferenceType>();
        if (!ref_type || !ref_type->referred_type) {
            error("convert_implicit_cast(): invalid reference cast target", expr->location);
            return nullptr;
        }

        Expr* binding_expr = unwrap_reference_binding_expr(expr->expr.get());

        llvm::Value* bound_addr = get_lvalue(binding_expr).address;
        if (bound_addr) {
            return bound_addr;
        }

        // Reference binds to a temporary object materialized in the caller.
        llvm::Value* bound_val = convert_expression(expr->expr.get());
        if (!bound_val) {
            error("convert_implicit_cast(): invalid reference binding source", expr->location);
            return nullptr;
        }

        llvm::Type* referred_llvm_type = convert_type(ref_type->referred_type.get_shared());
        if (!referred_llvm_type) {
            error("convert_implicit_cast(): failed to lower referred type", expr->location);
            return nullptr;
        }
        if (bound_val->getType() != referred_llvm_type) {
            bool src_unsigned = expr->expr->get_type() && expr->expr->get_type()->isUnsigned();
            bound_val = cast_llvm_type(bound_val, referred_llvm_type, src_unsigned);
        }

        if (!builder.GetInsertBlock()) {
            error("convert_implicit_cast(): cannot materialize reference temporary at global scope",
                  expr->location);
            return nullptr;
        }
        llvm::Function* fn = builder.GetInsertBlock()->getParent();
        llvm::Value* tmp = create_entry_alloca(fn, referred_llvm_type, nullptr, "ref.tmp");
        if (!tmp) {
            error("convert_implicit_cast(): failed to allocate reference temporary",
                  expr->location);
            return nullptr;
        }
        builder.CreateStore(bound_val, tmp);
        return tmp;
    }

    if (expr->kind == ImplicitCastTypes::FUNCTION_TO_POINTER) {
        if (auto* varRef = dyn_cast<VarRef>(expr->expr.get())) {
            if (varRef->symref && varRef->symref->kind == SymbolKind::FUNCTION) {
                llvm::Function* fn =
                    get_or_create_function_symbol(varRef->symref, varRef->get_name());
                if (!fn) {
                    error("convert_implicit_cast(): Unknown function referenced: " +
                              varRef->get_name(),
                          expr->location);
                    return nullptr;
                }
                return fn;
            }
        }
        return convert_expression(expr->expr.get());
    }
    if (expr->kind == ImplicitCastTypes::LAMBDA_TO_FUNCTION_POINTER) {
        if (!expr->expr) {
            error("convert_implicit_cast(): missing lambda conversion source", expr->location);
            return nullptr;
        }
        // Preserve any source-expression side effects before discarding the
        // closure object state for the captureless conversion. For glvalues we
        // only need address computation, not an rvalue load of the closure.
        Expr* side_effect_source = expr->expr.get();
        while (auto* inner_cast = dyn_cast<ImplicitCast>(side_effect_source)) {
            switch (inner_cast->kind) {
                case ImplicitCastTypes::LVALUE_TO_RVALUE:
                case ImplicitCastTypes::ARRAY_TO_POINTER:
                case ImplicitCastTypes::FUNCTION_TO_POINTER:
                case ImplicitCastTypes::ARITH_CAST:
                case ImplicitCastTypes::RAW_CAST:
                    side_effect_source = inner_cast->expr.get();
                    continue;
                default:
                    break;
            }
            break;
        }
        if (side_effect_source && side_effect_source->isLValue()) {
            get_lvalue(side_effect_source);
        } else {
            convert_expression(expr->expr.get());
        }

        auto closure_type =
            desugar_type(
                remove_reference(expr->expr->get_type(), ast_ctx.get()),
                ast_ctx.get())
                .as_shared<ObjectType>();
        auto* closure_decl =
            closure_type ? dyn_cast<ObjectDecl>(closure_type->get_decl()) : nullptr;
        const auto* lambda_info =
            (closure_decl && ast_ctx)
                ? ast_ctx->get_cpp_lambda_closure_decl_info(closure_decl->node_id)
                : nullptr;
        if (!lambda_info || !lambda_info->function_pointer_invoker_decl) {
            error("convert_implicit_cast(): missing captureless lambda invoker",
                  expr->location);
            return nullptr;
        }

        auto* invoker_decl =
            const_cast<FuncDecl*>(lambda_info->function_pointer_invoker_decl);
        convert_function_declaration(invoker_decl);
        std::string invoker_name = get_function_llvm_name(*invoker_decl);
        llvm::Function* invoker_fn = module->getFunction(invoker_name);
        if (!invoker_fn) {
            error("convert_implicit_cast(): failed to emit lambda invoker function",
                  expr->location);
            return nullptr;
        }
        return invoker_fn;
    }
    if (expr->kind == ImplicitCastTypes::LVALUE_TO_RVALUE) {
        return lower_lvalue_to_rvalue(expr);
    }
    if (expr->kind == ImplicitCastTypes::ARRAY_TO_POINTER) {
        // Array to pointer decay
        Expr* array_object_expr = unwrap_reference_binding_expr(expr->expr.get());
        auto lvalue_tup = get_lvalue(array_object_expr);
        llvm::Value* ptr = lvalue_tup.address;
        if (!ptr) return nullptr;

        // We have array. We want pointer to first element.
        // GEP (0, 0)
        QualType source_array_type =
            desugar_type(
                remove_reference(array_object_expr->get_type(), ast_ctx.get()),
                ast_ctx.get());
        auto arrType = source_array_type.as_shared<ArrayType>();
        if (!arrType && lvalue_tup.type) {
            source_array_type = desugar_type(QualType(lvalue_tup.type), ast_ctx.get());
            arrType = source_array_type.as_shared<ArrayType>();
        }
        if (!arrType) {
            error("convert_implicit_cast(): internal error; didn't downcast", expr->location);
            return nullptr;
        }
        if (arrType->size_kind == ArraySizeKind::Variable ||
            type_contains_vla(arrType->element_type.get_shared())) {
            // VLA arrays (including those with inner VLA dims) are already
            // represented as a flat pointer to their scalar elements.
            return ptr;
        }
        llvm::Type* llvmArrType = convert_type(source_array_type.get_shared());

        llvm::Value* zero = llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context), 0);
        llvm::Value* indices[] = {zero, zero};
        return builder.CreateGEP(llvmArrType, ptr, indices, "array_decay");
    }

    // Complex conversions: REAL_TO_COMPLEX, COMPLEX_TO_REAL, COMPLEX_TO_COMPLEX.
    // lower_complex_cast returns nullptr when preconditions aren't met (e.g.,
    // non-arithmetic operand), signalling fall-through to general casting below.
    if (expr->kind == ImplicitCastTypes::REAL_TO_COMPLEX ||
        expr->kind == ImplicitCastTypes::COMPLEX_TO_REAL ||
        expr->kind == ImplicitCastTypes::COMPLEX_TO_COMPLEX) {
        if (llvm::Value* result = lower_complex_cast(expr)) {
            return result;
        }
    }

    // Vector splat: broadcast scalar to all vector lanes
    if (expr->kind == ImplicitCastTypes::VECTOR_SPLAT) {
        llvm::Value* scalar = convert_expression(expr->expr.get());
        if (!scalar) return nullptr;
        auto vec_ctype =
            desugar_type(expr->get_type(), ast_ctx.get()).as_shared<VectorType>();
        if (!vec_ctype) {
            error("convert_implicit_cast(): destination is not a vector type", expr->location);
            return nullptr;
        }
        llvm::Type* llvm_vec = convert_type(vec_ctype);
        unsigned num_elems = vec_ctype->num_elements;

        // Insert scalar into element 0 of undef vector, then shuffle-broadcast
        llvm::Value* undef = llvm::UndefValue::get(llvm_vec);
        llvm::Value* insert = builder.CreateInsertElement(
            undef, scalar, builder.getInt32(0), "splat_insert");
        llvm::SmallVector<int, 16> mask(num_elems, 0);
        return builder.CreateShuffleVector(insert, mask, "splat");
    }

    llvm::Value *val = convert_expression(expr->expr.get());
    if (!val) return nullptr;

    auto adjust_member_pointer_owner_offset =
        [&](llvm::Value* member_ptr_value,
            const std::shared_ptr<MemberPointerType>& source_member_ptr,
            const std::shared_ptr<MemberPointerType>& target_member_ptr) -> llvm::Value* {
        if (!member_ptr_value ||
            !source_member_ptr ||
            !target_member_ptr) {
            return member_ptr_value;
        }

        auto source_member_kind =
            canonical_type_kind(source_member_ptr->member_type, ast_ctx.get());
        auto target_member_kind =
            canonical_type_kind(target_member_ptr->member_type, ast_ctx.get());
        bool function_member_kind =
            source_member_kind == TypeKind::Function &&
            target_member_kind == TypeKind::Function;
        if (source_member_kind != target_member_kind) {
            return member_ptr_value;
        }

        auto source_owner_type =
            desugar_type(source_member_ptr->class_type, ast_ctx.get())
                .as_shared<ObjectType>();
        auto target_owner_type =
            desugar_type(target_member_ptr->class_type, ast_ctx.get())
                .as_shared<ObjectType>();
        auto* source_owner_decl = source_owner_type
            ? canonical_cpp_record_decl(dyn_cast<ObjectDecl>(source_owner_type->get_decl()))
            : nullptr;
        auto* target_owner_decl = target_owner_type
            ? canonical_cpp_record_decl(dyn_cast<ObjectDecl>(target_owner_type->get_decl()))
            : nullptr;
        if (!source_owner_decl || !target_owner_decl || source_owner_decl == target_owner_decl) {
            return member_ptr_value;
        }

        std::optional<size_t> owner_offset = find_cpp_base_subobject_offset(
            target_owner_decl, source_owner_decl);
        if (!owner_offset.has_value() || *owner_offset == 0) {
            return member_ptr_value;
        }
        if (*owner_offset >
            static_cast<size_t>(std::numeric_limits<int64_t>::max())) {
            return member_ptr_value;
        }

        if (function_member_kind) {
            auto* value_struct =
                llvm::dyn_cast<llvm::StructType>(member_ptr_value->getType());
            if (!value_struct || value_struct->getNumElements() != 2) {
                return member_ptr_value;
            }
            llvm::Value* function_payload = builder.CreateExtractValue(
                member_ptr_value, {0}, "memberfn.payload");
            llvm::Value* this_adjust = builder.CreateExtractValue(
                member_ptr_value, {1}, "memberfn.adjust");
            llvm::Type* i64 = llvm::Type::getInt64Ty(*context);
            if (!this_adjust->getType()->isIntegerTy(64)) {
                this_adjust = cast_llvm_type(this_adjust, i64, false);
            }
            llvm::Value* adjusted_this = builder.CreateAdd(
                this_adjust,
                llvm::ConstantInt::get(
                    i64, static_cast<uint64_t>(*owner_offset), false),
                "memberfn.adjusted");
            auto* payload_ptr_ty =
                llvm::dyn_cast<llvm::PointerType>(function_payload->getType());
            if (!payload_ptr_ty) {
                return member_ptr_value;
            }
            llvm::Value* null_payload =
                llvm::ConstantPointerNull::get(payload_ptr_ty);
            llvm::Value* is_null = builder.CreateICmpEQ(
                function_payload, null_payload, "memberfn.isnull");
            llvm::Value* final_adjust = builder.CreateSelect(
                is_null, this_adjust, adjusted_this, "memberfn.adjust.select");
            llvm::Value* adjusted_value = llvm::UndefValue::get(value_struct);
            adjusted_value = builder.CreateInsertValue(
                adjusted_value, function_payload, {0}, "memberfn.out.payload");
            adjusted_value = builder.CreateInsertValue(
                adjusted_value, final_adjust, {1}, "memberfn.out.adjust");
            return adjusted_value;
        }

        if (!member_ptr_value->getType()->isIntegerTy()) {
            return member_ptr_value;
        }
        llvm::Type* value_type = member_ptr_value->getType();
        llvm::Value* null_value = llvm::ConstantInt::get(value_type, 0, false);
        llvm::Value* is_null = builder.CreateICmpEQ(
            member_ptr_value, null_value, "memberptr.isnull");
        llvm::Value* offset_value = llvm::ConstantInt::get(
            value_type, static_cast<uint64_t>(*owner_offset), false);
        llvm::Value* adjusted = builder.CreateAdd(
            member_ptr_value, offset_value, "memberptr.adjust");
        return builder.CreateSelect(is_null, member_ptr_value, adjusted, "memberptr.select");
    };

    auto source_member_ptr_type =
        desugar_type(expr->expr->get_type(), ast_ctx.get()).as_shared<MemberPointerType>();
    auto target_member_ptr_type =
        desugar_type(expr->ctype, ast_ctx.get()).as_shared<MemberPointerType>();
    val = adjust_member_pointer_owner_offset(
        val, source_member_ptr_type, target_member_ptr_type);

    auto src_ptr_type =
        desugar_type(expr->expr->get_type(), ast_ctx.get()).as_shared<PointerType>();
    auto dst_ptr_type =
        desugar_type(expr->ctype, ast_ctx.get()).as_shared<PointerType>();
    if (src_ptr_type && dst_ptr_type &&
        canonical_type_kind(src_ptr_type->pointed_type, ast_ctx.get()) ==
            TypeKind::Object &&
        canonical_type_kind(dst_ptr_type->pointed_type, ast_ctx.get()) ==
            TypeKind::Object) {
        auto src_record_type =
            desugar_type(src_ptr_type->pointed_type, ast_ctx.get())
                .as_shared<ObjectType>();
        auto dst_record_type =
            desugar_type(dst_ptr_type->pointed_type, ast_ctx.get())
                .as_shared<ObjectType>();
        auto* src_record_decl = src_record_type
            ? canonical_cpp_record_decl(dyn_cast<ObjectDecl>(src_record_type->get_decl()))
            : nullptr;
        auto* dst_record_decl = dst_record_type
            ? canonical_cpp_record_decl(dyn_cast<ObjectDecl>(dst_record_type->get_decl()))
            : nullptr;
        if (src_record_decl && dst_record_decl && src_record_decl != dst_record_decl) {
            bool applied_dynamic_adjustment = false;
            const RecordSemanticState* src_state = lookup_cpp_record_state(src_record_decl);
            if (src_state && cpp_record_uses_vptr(src_state) && src_record_type) {
                llvm::Value* adjusted_val = resolve_cpp_virtual_base_subobject_address(
                    val,
                    src_record_decl,
                    dst_record_decl,
                    expr->location,
                    "convert_implicit_cast()");
                if (adjusted_val) {
                    val = adjusted_val;
                    applied_dynamic_adjustment = true;
                }
            }

            if (!applied_dynamic_adjustment) {
                std::optional<size_t> offset = find_cpp_base_subobject_offset(
                    src_record_decl, dst_record_decl);
                if (offset.has_value() && *offset > 0) {
                    val = adjust_cpp_pointer_by_static_offset(
                        val,
                        static_cast<int64_t>(*offset),
                        "upcast.adjust");
                }
            }
        }
    }

    llvm::Type *destType = convert_type(expr->ctype);
    llvm::Type *srcType = val->getType();

    auto dest_member_ptr_type =
        desugar_type(expr->ctype, ast_ctx.get()).as_shared<MemberPointerType>();
    if (dest_member_ptr_type &&
        canonical_type_kind(dest_member_ptr_type->member_type, ast_ctx.get()) ==
            TypeKind::Function &&
        (!source_member_ptr_type || srcType->isIntegerTy())) {
        auto zero_value =
            eval_constexpr_i64(expr->expr.get(), ConstEvalMode::c_ice());
        if (zero_value.has_value() && *zero_value == 0) {
            return llvm::Constant::getNullValue(destType);
        }
        error("convert_implicit_cast(): invalid integer to member-function pointer conversion",
              expr->location);
        return nullptr;
    }

    if (srcType == destType) return val;

    auto innerCType = expr->expr->get_type();
    // for an integer we always want to extend according to the source type
    bool isUnsigned = innerCType ? innerCType->isUnsigned() : false;
    if (srcType->isFloatingPointTy()) {
        // if dest is fp, isUnsigned variable doesn't matter
        // if dest is an int, then we want isUnsigned to be the type of dest type
        isUnsigned = expr->get_type()->isUnsigned();
    }
    return cast_llvm_type(val, destType, isUnsigned);
}
// same as above for now
// ---------------------------------------------------------------------------
// Extracted helpers for convert_implicit_cast
// ---------------------------------------------------------------------------

llvm::Value* ASTToLLVM::lower_lvalue_to_rvalue(ImplicitCast *expr) {
    // Bitfield member access: extract the bitfield value from storage.
    if (auto* member = dyn_cast<MemberExpr>(expr->expr.get())) {
        if (member->is_bitfield) {
            auto* bf_info = ast_ctx->get_bitfield_info(member->node_id);

            llvm::Value* base_ptr = nullptr;
            if (member->isArrow) {
                base_ptr = convert_expression(member->base.get());
            } else {
                auto base_lvalue = get_lvalue(member->base.get());
                base_ptr = base_lvalue.address;
                if (!base_ptr) {
                    // Bitfield read from an rvalue base (e.g. foo().b):
                    // materialize a temporary so we can address the storage unit.
                    auto base_ctype = member->base->get_type();
                    auto base_obj = base_ctype.as_shared<ObjectType>();
                    if (!base_obj) {
                        error("lower_lvalue_to_rvalue(): Cannot materialize non-record base for bitfield", expr->location);
                        return nullptr;
                    }
                    llvm::Value* base_rval = convert_expression(member->base.get());
                    if (!base_rval) return nullptr;
                    llvm::Type* base_llvm_ty = convert_type(base_ctype);
                    llvm::Function* fn = builder.GetInsertBlock()->getParent();
                    llvm::IRBuilder<> tmp_builder(&fn->getEntryBlock(), fn->getEntryBlock().begin());
                    llvm::AllocaInst* tmp_alloca =
                        tmp_builder.CreateAlloca(base_llvm_ty, nullptr, "bitfield.rval.tmp");
                    size_t base_align = base_obj->getAlignment();
                    if (base_align > 0) {
                        tmp_alloca->setAlignment(llvm::Align(base_align));
                    }
                    builder.CreateStore(base_rval, tmp_alloca);
                    base_ptr = tmp_alloca;
                }
            }

            if (!base_ptr) {
                error("lower_lvalue_to_rvalue(): Cannot get base pointer for bitfield", expr->location);
                return nullptr;
            }

            llvm::Value* storage_ptr = get_bitfield_storage_ptr(member, base_ptr, bf_info);
            if (!storage_ptr) return nullptr;

            bool is_signed = !member->member_type->isUnsigned();
            llvm::Value* extracted = extract_bitfield(storage_ptr, bf_info->storage_size,
                bf_info->bit_offset, bf_info->bit_width, is_signed);
            if (!extracted) return nullptr;

            llvm::Type* target_ty = convert_type(expr->ctype);
            if (target_ty && extracted->getType() != target_ty && target_ty->isIntegerTy()) {
                extracted = cast_llvm_type(extracted, target_ty, !is_signed);
            }
            return extracted;
        }
    }

    // Vector subscript read: use extractelement.
    if (auto* subscript = dyn_cast<ArraySubscriptExpr>(expr->expr.get())) {
        auto arr_type = subscript->array->get_type();
        if (canonical_type_kind(arr_type, ast_ctx.get()) == TypeKind::Vector) {
            llvm::Value* vec = convert_expression(subscript->array.get());
            llvm::Value* idx = convert_expression(subscript->index.get());
            return builder.CreateExtractElement(vec, idx, "vec_extract");
        }
    }

    // Regular (non-bitfield, non-vector) lvalue to rvalue conversion.
    // Unwrap nested LVALUE_TO_RVALUE / ARRAY_TO_POINTER casts.
    Expr* lvalue_expr = expr->expr.get();
    while (auto* inner_cast = dyn_cast<ImplicitCast>(lvalue_expr)) {
        if (inner_cast->kind == ImplicitCastTypes::LVALUE_TO_RVALUE ||
            inner_cast->kind == ImplicitCastTypes::ARRAY_TO_POINTER) {
            lvalue_expr = inner_cast->expr.get();
            continue;
        }
        break;
    }

    // IMPORTANT: Template body instantiation can substitute a concrete rvalue
    // literal where the original template had an lvalue VarRef.  The enclosing
    // lvalue-to-rvalue ImplicitCast becomes stale.  We detect this by walking
    // through residual casts and checking isLValue().  If the inner expression
    // is already an rvalue, lower it directly and skip the load.
    // This is not a bug in the AST — it is an expected consequence of
    // substitution operating on partially-typed trees.
    if (!lvalue_expr->isLValue()) {
        llvm::Value* direct_value = convert_expression(lvalue_expr);
        if (!direct_value) return nullptr;
        llvm::Type* target_type = convert_type(expr->ctype);
        if (target_type && direct_value->getType() != target_type) {
            bool src_unsigned = lvalue_expr->get_type() && lvalue_expr->get_type()->isUnsigned();
            direct_value = cast_llvm_type(direct_value, target_type, src_unsigned);
        }
        return direct_value;
    }

    auto lvalue_tup = get_lvalue(lvalue_expr);
    if (!lvalue_tup) {
        // Prefix/postfix inc/dec expressions carry side effects and produce the
        // value directly; they do not have a stable addressable result for
        // generic get_lvalue().
        if (auto* unary = dyn_cast<UnaryOperation>(lvalue_expr)) {
            if (unary->uop == UnaryOpTypes::INCREMENT_PREFIX ||
                unary->uop == UnaryOpTypes::DECREMENT_PREFIX ||
                unary->uop == UnaryOpTypes::INCREMENT_POSTFIX ||
                unary->uop == UnaryOpTypes::DECREMENT_POSTFIX) {
                return convert_unary_expr(unary);
            }
        }
        return nullptr;
    }

    llvm::Value* ptr = lvalue_tup.address;
    auto ctype = lvalue_tup.type;
    if (auto cptr = dyn_cast_shared<PointerType>(ctype)) {
        (void)cptr; // pointer lvalues: keep original type for opaque-ptr load
    }

    if (ctype &&
        canonical_type_kind(QualType(ctype), ast_ctx.get()) ==
            TypeKind::CppTypeInfo) {
        llvm::Type* handle_type = convert_type(expr->ctype);
        if (!handle_type) {
            error("lower_lvalue_to_rvalue(): failed to lower RTTI handle type",
                  expr->location);
            return nullptr;
        }
        if (ptr->getType() != handle_type) {
            ptr = cast_llvm_type(ptr, handle_type, false);
        }
        return ptr;
    }

    llvm::Type* valType = convert_type(ctype);

    // Global/static constant initialization: evaluate lvalue reads without IR
    // by pulling from the referenced global initializer.
    if (builder.GetInsertBlock() == nullptr) {
        if (auto* gvar = llvm::dyn_cast<llvm::GlobalVariable>(ptr)) {
            if (auto* init = gvar->getInitializer()) {
                if (init->getType() == valType) return init;
            }
        }
        if (auto* cst = emit_constant_initializer(lvalue_expr)) {
            if (cst->getType() == valType) return cst;
            bool srcUns = lvalue_expr->get_type() && lvalue_expr->get_type()->isUnsigned();
            if (auto* casted = fold_constant_cast(cst, valType, srcUns, false, module->getDataLayout())) {
                return casted;
            }
        }
        error("lower_lvalue_to_rvalue(): non-constant lvalue in global initializer", expr->location);
        return nullptr;
    }

    auto* load = builder.CreateLoad(valType, ptr, "load_implicit_cast");
    if (dyn_cast<MemberExpr>(lvalue_expr) || dyn_cast<MemberPointerAccessExpr>(lvalue_expr)) {
        // Member reads can come from packed/byte-layout records.
        load->setAlignment(llvm::Align(1));
    }
    apply_load_qualifiers(load, expr->expr->get_type(), module->getDataLayout());
    return load;
}

llvm::Value* ASTToLLVM::lower_complex_cast(ImplicitCast *expr) {
    if (expr->kind == ImplicitCastTypes::REAL_TO_COMPLEX &&
        expr->expr->get_type() && expr->expr->get_type()->isArithmetic()) {
        // Real scalar -> complex: set real part, zero imaginary.
        llvm::Value* real_val = convert_expression(expr->expr.get());
        if (!real_val) return nullptr;
        auto complex_ctype = desugar_type(expr->ctype, ast_ctx.get()).as_shared<ComplexType>();
        if (!complex_ctype) {
            error("lower_complex_cast(): destination is not a complex type", expr->location);
            return nullptr;
        }
        llvm::Type* elem_type = convert_type(complex_ctype->element_type);
        bool elem_is_unsigned = complex_ctype->element_type->isUnsigned();
        if (real_val->getType() != elem_type) {
            bool cast_unsigned = expr->expr->get_type() ? expr->expr->get_type()->isUnsigned() : false;
            if (real_val->getType()->isFloatingPointTy() && elem_type->isIntegerTy())
                cast_unsigned = elem_is_unsigned;
            real_val = cast_llvm_type(real_val, elem_type, cast_unsigned);
        }
        llvm::Value* zero = nullptr;
        if (elem_type->isFloatingPointTy()) zero = llvm::ConstantFP::get(elem_type, 0.0);
        else if (elem_type->isIntegerTy()) zero = llvm::ConstantInt::get(elem_type, 0);
        else {
            error("lower_complex_cast(): unsupported complex element type", expr->location);
            return nullptr;
        }
        llvm::Type* struct_type = convert_type(expr->ctype.get_shared());
        llvm::Value* result = llvm::UndefValue::get(struct_type);
        result = builder.CreateInsertValue(result, real_val, {0}, "cmplx.real");
        result = builder.CreateInsertValue(result, zero, {1}, "cmplx.imag");
        return result;
    }

    if (expr->kind == ImplicitCastTypes::COMPLEX_TO_REAL &&
        expr->ctype && expr->ctype->isArithmetic()) {
        // Complex -> real scalar: discard imaginary part.
        llvm::Value* complex_val = convert_expression(expr->expr.get());
        if (!complex_val) return nullptr;
        llvm::Value* real_part = builder.CreateExtractValue(complex_val, {0}, "creal");
        llvm::Type* dest_type = convert_type(expr->ctype.get_shared());
        if (real_part->getType() != dest_type) {
            auto src_complex = desugar_type(expr->expr->get_type(), ast_ctx.get()).as_shared<ComplexType>();
            bool cast_unsigned = src_complex ? src_complex->element_type->isUnsigned() : false;
            if (real_part->getType()->isFloatingPointTy() && dest_type->isIntegerTy())
                cast_unsigned = expr->ctype ? expr->ctype->isUnsigned() : false;
            real_part = cast_llvm_type(real_part, dest_type, cast_unsigned);
        }
        return real_part;
    }

    if (expr->kind == ImplicitCastTypes::COMPLEX_TO_COMPLEX) {
        // Complex -> complex: convert both parts.
        llvm::Value* complex_val = convert_expression(expr->expr.get());
        if (!complex_val) return nullptr;
        llvm::Value* real_part = builder.CreateExtractValue(complex_val, {0}, "creal");
        llvm::Value* imag_part = builder.CreateExtractValue(complex_val, {1}, "cimag");
        auto src_complex = desugar_type(expr->expr->get_type(), ast_ctx.get()).as_shared<ComplexType>();
        auto dest_complex = desugar_type(expr->ctype, ast_ctx.get()).as_shared<ComplexType>();
        if (!dest_complex) {
            error("lower_complex_cast(): destination is not a complex type", expr->location);
            return nullptr;
        }
        llvm::Type* dest_elem = convert_type(dest_complex->element_type);
        if (real_part->getType() != dest_elem) {
            bool cast_unsigned = src_complex ? src_complex->element_type->isUnsigned() : false;
            if (real_part->getType()->isFloatingPointTy() && dest_elem->isIntegerTy())
                cast_unsigned = dest_complex->element_type->isUnsigned();
            real_part = cast_llvm_type(real_part, dest_elem, cast_unsigned);
            imag_part = cast_llvm_type(imag_part, dest_elem, cast_unsigned);
        }
        llvm::Type* struct_type = convert_type(expr->ctype.get_shared());
        llvm::Value* result = llvm::UndefValue::get(struct_type);
        result = builder.CreateInsertValue(result, real_part, {0}, "cmplx.real");
        result = builder.CreateInsertValue(result, imag_part, {1}, "cmplx.imag");
        return result;
    }

    // Preconditions not met — signal caller to fall through to general casting.
    return nullptr;
}

llvm::Value* ASTToLLVM::convert_explicit_cast(ExplicitCast *expr) {
    if (!expr->expr) {
        error("convert_explicit_cast(): cast expression missing operand", expr->location);
        return nullptr;
    }
    if (canonical_type_kind(expr->ctype, ast_ctx.get()) == TypeKind::Reference) {
        auto ref_type =
            desugar_type(expr->ctype, ast_ctx.get()).as_shared<ReferenceType>();
        if (!ref_type || !ref_type->referred_type) {
            error("convert_explicit_cast(): invalid reference cast target", expr->location);
            return nullptr;
        }

        Expr* binding_expr = unwrap_reference_binding_expr(expr->expr.get());
        llvm::Value* bound_addr = get_lvalue(binding_expr).address;
        if (bound_addr) {
            return bound_addr;
        }

        llvm::Value* bound_val = convert_expression(expr->expr.get());
        if (!bound_val) {
            error("convert_explicit_cast(): invalid reference binding source", expr->location);
            return nullptr;
        }

        llvm::Type* referred_llvm_type = convert_type(ref_type->referred_type.get_shared());
        if (!referred_llvm_type) {
            error("convert_explicit_cast(): failed to lower referred type", expr->location);
            return nullptr;
        }
        if (bound_val->getType() != referred_llvm_type) {
            bool src_unsigned = expr->expr->get_type() && expr->expr->get_type()->isUnsigned();
            bound_val = cast_llvm_type(bound_val, referred_llvm_type, src_unsigned);
        }

        if (!builder.GetInsertBlock()) {
            error("convert_explicit_cast(): cannot materialize reference temporary at global scope",
                  expr->location);
            return nullptr;
        }
        llvm::Function* fn = builder.GetInsertBlock()->getParent();
        llvm::Value* tmp =
            create_entry_alloca(fn, referred_llvm_type, nullptr, "explicit.ref.tmp");
        if (!tmp) {
            error("convert_explicit_cast(): failed to allocate reference temporary",
                  expr->location);
            return nullptr;
        }
        builder.CreateStore(bound_val, tmp);
        return tmp;
    }

    llvm::Value *val = convert_expression(expr->expr.get());
    if (!val) return nullptr;

    auto adjust_member_pointer_owner_offset =
        [&](llvm::Value* member_ptr_value,
            const std::shared_ptr<MemberPointerType>& source_member_ptr,
            const std::shared_ptr<MemberPointerType>& target_member_ptr) -> llvm::Value* {
        if (!member_ptr_value ||
            !source_member_ptr ||
            !target_member_ptr) {
            return member_ptr_value;
        }

        auto source_member_kind =
            canonical_type_kind(source_member_ptr->member_type, ast_ctx.get());
        auto target_member_kind =
            canonical_type_kind(target_member_ptr->member_type, ast_ctx.get());
        bool function_member_kind =
            source_member_kind == TypeKind::Function &&
            target_member_kind == TypeKind::Function;
        if (source_member_kind != target_member_kind) {
            return member_ptr_value;
        }

        auto source_owner_type =
            desugar_type(source_member_ptr->class_type, ast_ctx.get())
                .as_shared<ObjectType>();
        auto target_owner_type =
            desugar_type(target_member_ptr->class_type, ast_ctx.get())
                .as_shared<ObjectType>();
        auto* source_owner_decl = source_owner_type
            ? canonical_cpp_record_decl(dyn_cast<ObjectDecl>(source_owner_type->get_decl()))
            : nullptr;
        auto* target_owner_decl = target_owner_type
            ? canonical_cpp_record_decl(dyn_cast<ObjectDecl>(target_owner_type->get_decl()))
            : nullptr;
        if (!source_owner_decl || !target_owner_decl || source_owner_decl == target_owner_decl) {
            return member_ptr_value;
        }

        std::optional<size_t> owner_offset = find_cpp_base_subobject_offset(
            target_owner_decl, source_owner_decl);
        if (!owner_offset.has_value() || *owner_offset == 0) {
            return member_ptr_value;
        }
        if (*owner_offset >
            static_cast<size_t>(std::numeric_limits<int64_t>::max())) {
            return member_ptr_value;
        }

        if (function_member_kind) {
            auto* value_struct =
                llvm::dyn_cast<llvm::StructType>(member_ptr_value->getType());
            if (!value_struct || value_struct->getNumElements() != 2) {
                return member_ptr_value;
            }
            llvm::Value* function_payload = builder.CreateExtractValue(
                member_ptr_value, {0}, "memberfn.payload");
            llvm::Value* this_adjust = builder.CreateExtractValue(
                member_ptr_value, {1}, "memberfn.adjust");
            llvm::Type* i64 = llvm::Type::getInt64Ty(*context);
            if (!this_adjust->getType()->isIntegerTy(64)) {
                this_adjust = cast_llvm_type(this_adjust, i64, false);
            }
            llvm::Value* adjusted_this = builder.CreateAdd(
                this_adjust,
                llvm::ConstantInt::get(
                    i64, static_cast<uint64_t>(*owner_offset), false),
                "memberfn.adjusted");
            auto* payload_ptr_ty =
                llvm::dyn_cast<llvm::PointerType>(function_payload->getType());
            if (!payload_ptr_ty) {
                return member_ptr_value;
            }
            llvm::Value* null_payload =
                llvm::ConstantPointerNull::get(payload_ptr_ty);
            llvm::Value* is_null = builder.CreateICmpEQ(
                function_payload, null_payload, "memberfn.isnull");
            llvm::Value* final_adjust = builder.CreateSelect(
                is_null, this_adjust, adjusted_this, "memberfn.adjust.select");
            llvm::Value* adjusted_value = llvm::UndefValue::get(value_struct);
            adjusted_value = builder.CreateInsertValue(
                adjusted_value, function_payload, {0}, "memberfn.out.payload");
            adjusted_value = builder.CreateInsertValue(
                adjusted_value, final_adjust, {1}, "memberfn.out.adjust");
            return adjusted_value;
        }

        if (!member_ptr_value->getType()->isIntegerTy()) {
            return member_ptr_value;
        }
        llvm::Type* value_type = member_ptr_value->getType();
        llvm::Value* null_value = llvm::ConstantInt::get(value_type, 0, false);
        llvm::Value* is_null = builder.CreateICmpEQ(
            member_ptr_value, null_value, "memberptr.isnull");
        llvm::Value* offset_value = llvm::ConstantInt::get(
            value_type, static_cast<uint64_t>(*owner_offset), false);
        llvm::Value* adjusted = builder.CreateAdd(
            member_ptr_value, offset_value, "memberptr.adjust");
        return builder.CreateSelect(is_null, member_ptr_value, adjusted, "memberptr.select");
    };

    auto innerCType = desugar_type(expr->expr->get_type(), ast_ctx.get());
    auto destCType = desugar_type(expr->ctype, ast_ctx.get());
    val = adjust_member_pointer_owner_offset(
        val,
        innerCType.as_shared<MemberPointerType>(),
        destCType.as_shared<MemberPointerType>());

    auto source_ptr_type = innerCType.as_shared<PointerType>();
    auto target_ptr_type = destCType.as_shared<PointerType>();
    if (expr->cast_kind == ExplicitCastKind::CppStaticCast &&
        source_ptr_type &&
        target_ptr_type &&
        canonical_type_kind(source_ptr_type->pointed_type, ast_ctx.get()) ==
            TypeKind::Object &&
        canonical_type_kind(target_ptr_type->pointed_type, ast_ctx.get()) ==
            TypeKind::Object) {
        auto source_record_type =
            desugar_type(source_ptr_type->pointed_type, ast_ctx.get())
                .as_shared<ObjectType>();
        auto target_record_type =
            desugar_type(target_ptr_type->pointed_type, ast_ctx.get())
                .as_shared<ObjectType>();
        auto* source_record_decl = source_record_type
            ? canonical_cpp_record_decl(
                  dyn_cast<ObjectDecl>(source_record_type->get_decl()))
            : nullptr;
        auto* target_record_decl = target_record_type
            ? canonical_cpp_record_decl(
                  dyn_cast<ObjectDecl>(target_record_type->get_decl()))
            : nullptr;
        if (source_record_decl &&
            target_record_decl &&
            source_record_decl != target_record_decl) {
            bool applied_dynamic_adjustment = false;
            const RecordSemanticState* source_state =
                lookup_cpp_record_state(source_record_decl);
            if (source_state &&
                cpp_record_uses_vptr(source_state) &&
                source_record_type) {
                llvm::Value* adjusted_val =
                    resolve_cpp_virtual_base_subobject_address(
                        val,
                        source_record_decl,
                        target_record_decl,
                        expr->location,
                        "convert_explicit_cast()");
                if (adjusted_val) {
                    val = adjusted_val;
                    applied_dynamic_adjustment = true;
                }
            }

            if (!applied_dynamic_adjustment) {
                std::optional<size_t> upcast_offset =
                    find_cpp_base_subobject_offset(
                        source_record_decl,
                        target_record_decl);
                if (upcast_offset.has_value()) {
                    if (*upcast_offset > 0 &&
                        *upcast_offset <=
                            static_cast<size_t>(
                                std::numeric_limits<int64_t>::max())) {
                        val = adjust_cpp_pointer_by_static_offset(
                            val,
                            static_cast<int64_t>(*upcast_offset),
                            "static.upcast.adjust");
                    }
                } else {
                    std::optional<size_t> downcast_offset =
                        find_cpp_base_subobject_offset(
                            target_record_decl,
                            source_record_decl);
                    if (downcast_offset.has_value() &&
                        *downcast_offset > 0 &&
                        *downcast_offset <=
                            static_cast<size_t>(
                                std::numeric_limits<int64_t>::max())) {
                        val = adjust_cpp_pointer_by_static_offset(
                            val,
                            -static_cast<int64_t>(*downcast_offset),
                            "static.downcast.adjust");
                    }
                }
            }
        }
    }

    llvm::Type *destType = convert_type(expr->ctype);
    llvm::Type *srcType = val->getType();

    auto dest_member_ptr_type = destCType.as_shared<MemberPointerType>();
    auto source_member_ptr_type = innerCType.as_shared<MemberPointerType>();
    if (dest_member_ptr_type &&
        canonical_type_kind(dest_member_ptr_type->member_type, ast_ctx.get()) ==
            TypeKind::Function &&
        (!source_member_ptr_type || srcType->isIntegerTy())) {
        auto zero_value =
            eval_constexpr_i64(expr->expr.get(), ConstEvalMode::c_ice());
        if (zero_value.has_value() && *zero_value == 0) {
            return llvm::Constant::getNullValue(destType);
        }
        error("convert_explicit_cast(): invalid integer to member-function pointer conversion",
              expr->location);
        return nullptr;
    }

    if (srcType == destType) return val;

    // Cast to void: just discard the value
    if (destType->isVoidTy()) {
        return val; // Value is discarded by caller
    }

    // Vector-to-vector bitcast (same total size)
    if (srcType->isVectorTy() && destType->isVectorTy()) {
        return builder.CreateBitCast(val, destType, "vec_bitcast");
    }

    // Complex cast handling
    bool src_complex = innerCType && innerCType->isComplex();
    bool dest_complex = destCType && destCType->isComplex();
    if (dest_complex && !src_complex && innerCType && innerCType->isArithmetic()) {
        // Real → complex: set real part, imag = 0
        auto complex_ctype = destCType.as_shared<ComplexType>();
        if (!complex_ctype) {
            error("convert_explicit_cast(): destination is not a complex type", expr->location);
            return nullptr;
        }
        llvm::Type* elem_type = convert_type(complex_ctype->element_type);
        bool elem_is_unsigned = complex_ctype->element_type->isUnsigned();
        llvm::Value* real_val = val;
        if (real_val->getType() != elem_type) {
            bool cast_unsigned = innerCType ? innerCType->isUnsigned() : false;
            if (real_val->getType()->isFloatingPointTy() && elem_type->isIntegerTy()) {
                cast_unsigned = elem_is_unsigned;
            }
            real_val = cast_llvm_type(real_val, elem_type, cast_unsigned);
        }
        llvm::Value* zero = nullptr;
        if (elem_type->isFloatingPointTy()) {
            zero = llvm::ConstantFP::get(elem_type, 0.0);
        } else if (elem_type->isIntegerTy()) {
            zero = llvm::ConstantInt::get(elem_type, 0);
        } else {
            error("convert_explicit_cast(): unsupported complex element type", expr->location);
            return nullptr;
        }
        llvm::Value* result = llvm::UndefValue::get(destType);
        result = builder.CreateInsertValue(result, real_val, {0}, "ecast.real");
        result = builder.CreateInsertValue(result, zero, {1}, "ecast.imag");
        return result;
    }
    if (!dest_complex && src_complex && destCType && destCType->isArithmetic()) {
        // Complex → real: extract real part
        llvm::Value* real_part = builder.CreateExtractValue(val, {0}, "ecast.creal");
        if (real_part->getType() != destType) {
            auto src_ct = innerCType.as_shared<ComplexType>();
            bool cast_unsigned = src_ct ? src_ct->element_type->isUnsigned() : false;
            if (real_part->getType()->isFloatingPointTy() && destType->isIntegerTy()) {
                cast_unsigned = destCType ? destCType->isUnsigned() : false;
            }
            real_part = cast_llvm_type(real_part, destType, cast_unsigned);
        }
        return real_part;
    }
    if (dest_complex && src_complex) {
        // Complex → complex: convert both parts
        auto src_ct = innerCType.as_shared<ComplexType>();
        auto dest_ct = destCType.as_shared<ComplexType>();
        if (!dest_ct) {
            error("convert_explicit_cast(): destination is not a complex type", expr->location);
            return nullptr;
        }
        llvm::Type* dest_elem = convert_type(dest_ct->element_type);
        llvm::Value* real_part = builder.CreateExtractValue(val, {0}, "ecast.r");
        llvm::Value* imag_part = builder.CreateExtractValue(val, {1}, "ecast.i");
        if (real_part->getType() != dest_elem) {
            bool cast_unsigned = src_ct ? src_ct->element_type->isUnsigned() : false;
            if (real_part->getType()->isFloatingPointTy() && dest_elem->isIntegerTy()) {
                cast_unsigned = dest_ct->element_type->isUnsigned();
            }
            real_part = cast_llvm_type(real_part, dest_elem, cast_unsigned);
            imag_part = cast_llvm_type(imag_part, dest_elem, cast_unsigned);
        }
        llvm::Value* result = llvm::UndefValue::get(destType);
        result = builder.CreateInsertValue(result, real_part, {0});
        result = builder.CreateInsertValue(result, imag_part, {1});
        return result;
    }

    // GNU union cast extension: (union U)scalar initializes a compatible union
    // member from the scalar and leaves the remaining bytes zeroed.
    if (auto dest_obj = destCType.as_shared<ObjectType>();
        dest_obj && dest_obj->is_union && !dest_obj->semantic_fields().empty() &&
        (srcType->isIntegerTy() || srcType->isFloatingPointTy() || srcType->isPointerTy())) {
        const auto& dest_fields = dest_obj->semantic_fields();
        size_t member_index = 0;
        if (innerCType) {
            for (size_t i = 0; i < dest_fields.size(); ++i) {
                if (innerCType.equals_unqualified(dest_fields[i].type)) {
                    member_index = i;
                    break;
                }
            }
        }

        llvm::Type* member_type = convert_type(dest_fields[member_index].type.get_shared());
        if (!member_type) {
            error("convert_explicit_cast(): cannot lower union member type", expr->location);
            return nullptr;
        }

        bool src_is_unsigned = innerCType ? innerCType->isUnsigned() : false;
        llvm::Value* member_value = val;
        if (member_value->getType() != member_type) {
            member_value = cast_llvm_type(member_value, member_type, src_is_unsigned);
        }

        llvm::Function* fn = builder.GetInsertBlock()->getParent();
        llvm::IRBuilder<> tmpBuilder(&fn->getEntryBlock(), fn->getEntryBlock().begin());
        auto* union_tmp = tmpBuilder.CreateAlloca(destType, nullptr, "union.cast.tmp");

        builder.CreateStore(llvm::Constant::getNullValue(destType), union_tmp);
        builder.CreateStore(member_value, union_tmp);
        return builder.CreateLoad(destType, union_tmp, "union.cast");
    }

    // for an integer we always want to extend according to the source type
    bool isUnsigned = innerCType ? innerCType->isUnsigned() : false;
    if (srcType->isFloatingPointTy()) {
        // if dest is fp, isUnsigned variable doesn't matter
        // if dest is an int, then we want isUnsigned to be the type of dest type
        isUnsigned = expr->get_type()->isUnsigned();
    }
    return cast_llvm_type(val, destType, isUnsigned);
}
