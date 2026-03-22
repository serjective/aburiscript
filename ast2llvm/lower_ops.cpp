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

llvm::Value * ASTToLLVM::convert_unary_expr(Expr *expr) {
    auto* uexpr = dyn_cast<UnaryOperation>(expr);
    if (!uexpr) return nullptr;

    if (uexpr->uop == UnaryOpTypes::ADDRESS_OF) {
        // Operand must be an lvalue.
        // If it's a VarRef, we return the alloca (pointer).
        // If it's a Dereference (*ptr), we return the ptr.
        // We need a way to get the address of an expression without loading it.
        // Let's handle VarRef specifically here, or generalize "get address".
        if (auto* varRef = dyn_cast<VarRef>(uexpr->exp.get())) {
            if (varRef->symref && varRef->symref->kind == SymbolKind::FUNCTION) {
                llvm::Function* fn =
                    get_or_create_function_symbol(varRef->symref, varRef->get_name());
                if (!fn) {
                    error("convert_unary_expr(): Unknown function referenced: " +
                              varRef->get_name(),
                          expr->location);
                    return nullptr;
                }
                return fn;
            }
        }
        auto lvalue_tup = get_lvalue(uexpr->exp.get());
        return lvalue_tup.address;
        // Handle other lvalues (array subscript, struct member) when implemented
        error("convert_unary_expr(): Cannot take address of non-lvalue", expr->location);
        return nullptr;
    }
    if (uexpr->uop == UnaryOpTypes::INCREMENT_PREFIX ||
               uexpr->uop == UnaryOpTypes::DECREMENT_PREFIX ||
               uexpr->uop == UnaryOpTypes::INCREMENT_POSTFIX ||
               uexpr->uop == UnaryOpTypes::DECREMENT_POSTFIX) {
        // Check if this is a bitfield increment/decrement
        MemberExpr* bf_member = nullptr;
        llvm::Value* bf_storage_ptr = nullptr;
        const BitfieldInfo* bf_info = nullptr;

        if (auto* member = dyn_cast<MemberExpr>(uexpr->exp.get())) {
            if (member->is_bitfield) {
                bf_member = member;
                bf_info = ast_ctx->get_bitfield_info(member->node_id);

                // Get base pointer for the bitfield
                llvm::Value* base_ptr = nullptr;
                if (member->isArrow) {
                    base_ptr = convert_expression(member->base.get());
                } else {
                    auto base_lvalue = get_lvalue(member->base.get());
                    base_ptr = base_lvalue.address;
                }

                if (!base_ptr) {
                    error("convert_unary_expr(): Cannot get base pointer for bitfield inc/dec", expr->location);
                    return nullptr;
                }

                bf_storage_ptr = get_bitfield_storage_ptr(member, base_ptr, bf_info);
                if (!bf_storage_ptr) {
                    return nullptr;
                }
            }
        }

        llvm::Value* ptr = nullptr;
        llvm::Type* valType = nullptr;
        llvm::Value* val = nullptr;

        if (bf_member) {
            // Bitfield: use extract_bitfield to get current value
            bool is_signed = !bf_member->member_type->isUnsigned();
            val = extract_bitfield(bf_storage_ptr, bf_info->storage_size,
                                   bf_info->bit_offset, bf_info->bit_width, is_signed);
            valType = val->getType();
        } else {
            // Regular lvalue
            auto lvalue_tup = get_lvalue(uexpr->exp.get());
            ptr = lvalue_tup.address;

            if (!ptr) {
                error("convert_unary_expr(): increment/Decrement requires lvalue", expr->location);
                return nullptr;
            }

            valType = convert_type(lvalue_tup.type);
            val = builder.CreateLoad(valType, ptr, "incdec_load");
            apply_load_qualifiers(llvm::cast<llvm::LoadInst>(val), uexpr->exp->get_type(), module->getDataLayout());
        }

        llvm::Value* one;
        if (valType->isFloatingPointTy()) {
            one = llvm::ConstantFP::get(valType, 1.0);
        } else {
            one = llvm::ConstantInt::get(valType, 1);
        }
        llvm::Value* newVal;
        bool is_increment =
            (uexpr->uop == UnaryOpTypes::INCREMENT_PREFIX ||
             uexpr->uop == UnaryOpTypes::INCREMENT_POSTFIX);

        // Pointer arithmetic for inc/dec?
        if (uexpr->exp->get_type() && uexpr->exp->get_type()->isComplex()) {
            llvm::Value* real = builder.CreateExtractValue(val, {0}, "incdec.real");
            llvm::Value* imag = builder.CreateExtractValue(val, {1}, "incdec.imag");
            llvm::Type* elem_ty = real->getType();
            llvm::Value* real_one = elem_ty->isFloatingPointTy()
                ? static_cast<llvm::Value*>(llvm::ConstantFP::get(elem_ty, 1.0))
                : static_cast<llvm::Value*>(llvm::ConstantInt::get(elem_ty, 1));
            llvm::Value* new_real = nullptr;
            if (elem_ty->isFloatingPointTy()) {
                new_real = is_increment
                    ? builder.CreateFAdd(real, real_one, "incdec.real.inc")
                    : builder.CreateFSub(real, real_one, "incdec.real.dec");
            } else {
                new_real = is_increment
                    ? builder.CreateAdd(real, real_one, "incdec.real.inc")
                    : builder.CreateSub(real, real_one, "incdec.real.dec");
            }
            llvm::Value* rebuilt = llvm::UndefValue::get(valType);
            rebuilt = builder.CreateInsertValue(rebuilt, new_real, {0}, "incdec.set.real");
            rebuilt = builder.CreateInsertValue(rebuilt, imag, {1}, "incdec.set.imag");
            newVal = rebuilt;
        } else if (valType->isPointerTy()) {
             // GEP
            llvm::Type * typ = nullptr;
            if (target->pointer_width == 64) {
                typ = llvm::Type::getInt64Ty(*context);
            } else if (target->pointer_width == 32) {
                typ = llvm::Type::getInt32Ty(*context);
            } else {
                error("Internal error: pointer width size not supported");
            }
            one = llvm::ConstantInt::get(typ, 1);
            auto ptrType =
                desugar_type(uexpr->exp->get_type(), ast_ctx.get())
                    .as_shared<PointerType>();
            if (!ptrType || !ptrType->pointed_type) {
                error("convert_unary_expr(): pointer increment/decrement requires pointer type",
                      expr->location);
                return nullptr;
            }
            llvm::Type* elemType = ptrType->pointed_type->isVoid()
                ? llvm::Type::getInt8Ty(*context)
                : convert_type(ptrType->pointed_type);
            if (is_increment) {
                newVal = builder.CreateGEP(elemType, val, {one}, "inc_ptr");
            } else {
                llvm::Value* negOne =
                    llvm::ConstantInt::get(one->getType(), -1, true);
                newVal = builder.CreateGEP(elemType, val, negOne, "dec_ptr");
            }
        } else if (valType->isFloatingPointTy()) {
            if (is_increment) {
                newVal = builder.CreateFAdd(val, one, "inc");
            } else {
                newVal = builder.CreateFSub(val, one, "dec");
            }
        } else {
            if (is_increment) {
                newVal = builder.CreateAdd(val, one, "inc");
            } else {
                newVal = builder.CreateSub(val, one, "dec");
            }
        }

        // Store the new value
        if (bf_member) {
            store_bitfield(bf_storage_ptr, bf_info->storage_size,
                          bf_info->bit_offset, bf_info->bit_width, newVal);
        } else {
            auto* store = builder.CreateStore(newVal, ptr);
            apply_store_qualifiers(store, uexpr->exp->get_type(), module->getDataLayout());
        }

        return (uexpr->uop == UnaryOpTypes::INCREMENT_PREFIX || uexpr->uop == UnaryOpTypes::DECREMENT_PREFIX) ? newVal : val;
    }
    llvm::Value* operand = convert_expression(uexpr->exp.get());
    if (operand == nullptr) {
        error("convert_unary_expr(): null expr in unary ast", expr->location);
        return nullptr;
    }

    // Apply integer promotions for unary integer operators.
    // This handles cases like ~unsigned char, which should operate in int.
    if ((uexpr->uop == UnaryOpTypes::BITWISE_NOT ||
         uexpr->uop == UnaryOpTypes::POSITIVE ||
         uexpr->uop == UnaryOpTypes::NEG) &&
        operand->getType()->isIntegerTy()) {
        auto* int_type = llvm::cast<llvm::IntegerType>(operand->getType());
        unsigned operand_bits = int_type->getBitWidth();
        unsigned int_bits = 32;
        if (type_ctx && type_ctx->get_builtin(BuiltinTypes::Int)) {
            int_bits = static_cast<unsigned>(type_ctx->get_builtin(BuiltinTypes::Int)->getWidth());
        }
        if (operand_bits < int_bits) {
            llvm::Type* promoted_type = llvm::IntegerType::get(*context, int_bits);
            bool src_unsigned = uexpr->exp->get_type() && uexpr->exp->get_type()->isUnsigned();
            operand = cast_llvm_type(operand, promoted_type, src_unsigned);
        }
    }

    llvm::Value* ret = nullptr;
    if (uexpr->uop == UnaryOpTypes::BITWISE_NOT) {
        if (uexpr->exp->get_type() && uexpr->exp->get_type()->isComplex()) {
            // GCC extension: ~ on complex = complex conjugate (negate imaginary part)
            llvm::Value* real_part = builder.CreateExtractValue(operand, {0}, "conj.r");
            llvm::Value* imag_part = builder.CreateExtractValue(operand, {1}, "conj.i");
            if (imag_part->getType()->isFloatingPointTy()) {
                imag_part = builder.CreateFNeg(imag_part, "conj.i.neg");
            } else {
                imag_part = builder.CreateNeg(imag_part, "conj.i.neg");
            }
            llvm::Value* result = llvm::UndefValue::get(operand->getType());
            result = builder.CreateInsertValue(result, real_part, {0});
            result = builder.CreateInsertValue(result, imag_part, {1});
            ret = result;
        } else {
            // ~ (bitflip)
            ret = builder.CreateNot(operand, "nottmp");
        }
    } else if (uexpr->uop == UnaryOpTypes::POSITIVE) {
        // + (unary plus) — identity operation
        ret = operand;
    } else if (uexpr->uop == UnaryOpTypes::NEG) {
        // - (two complements neg)
        if (uexpr->exp->get_type() && uexpr->exp->get_type()->isComplex()) {
            // Complex negation: negate both real and imaginary parts
            llvm::Value* real_part = builder.CreateExtractValue(operand, {0}, "cneg.r");
            llvm::Value* imag_part = builder.CreateExtractValue(operand, {1}, "cneg.i");
            if (real_part->getType()->isFloatingPointTy()) {
                real_part = builder.CreateFNeg(real_part, "cneg.r.neg");
                imag_part = builder.CreateFNeg(imag_part, "cneg.i.neg");
            } else {
                real_part = builder.CreateNeg(real_part, "cneg.r.neg");
                imag_part = builder.CreateNeg(imag_part, "cneg.i.neg");
            }
            llvm::Value* result = llvm::UndefValue::get(operand->getType());
            result = builder.CreateInsertValue(result, real_part, {0});
            result = builder.CreateInsertValue(result, imag_part, {1});
            ret = result;
        } else if (operand->getType()->isFloatingPointTy()) {
            ret = builder.CreateFNeg(operand, "fnegtmp");
        } else {
            ret = builder.CreateNeg(operand, "negtmp");
        }
    } else if (uexpr->uop == UnaryOpTypes::LOGICAL_NOT) {
        // ! (logical not) - true if value is zero
        llvm::Value *is_nonzero = emit_bool_conversion(operand, "lognot");
        llvm::Value *cmp = builder.CreateNot(is_nonzero, "lognot.not");
        ret = builder.CreateZExt(cmp, llvm::Type::getInt32Ty(*context), "lognot_ext");
    } else if (uexpr->uop == UnaryOpTypes::REAL_PART || uexpr->uop == UnaryOpTypes::IMAG_PART) {
        auto exp_type = uexpr->exp->get_type();
        if (exp_type && exp_type->isComplex()) {
            unsigned idx = (uexpr->uop == UnaryOpTypes::REAL_PART) ? 0 : 1;
            ret = builder.CreateExtractValue(operand, {idx},
                uexpr->uop == UnaryOpTypes::REAL_PART ? "creal" : "cimag");
        } else {
            // Non-complex: __real__ is identity, __imag__ yields 0
            if (uexpr->uop == UnaryOpTypes::REAL_PART) {
                ret = operand;
            } else {
                // __imag__ on real type = 0
                ret = llvm::Constant::getNullValue(operand->getType());
            }
        }
    } else if (uexpr->uop == UnaryOpTypes::DEREFERENCE) {
        // *ptr
        // operand is the pointer. We load from it.
        // We need the type of the element being pointed to.
        // In opaque pointer world, we need to know the type to load.
        auto ptrType =
            desugar_type(uexpr->exp->get_type(), ast_ctx.get())
                .as_shared<PointerType>();
        if (!ptrType) {
            error("convert_unary_expr(): Dereferencing non-pointer type", expr->location);
            return nullptr;
        }
        if (ptrType->pointed_type && ptrType->pointed_type->kind == TypeKind::Function) {
            // Dereferencing a function pointer yields a function designator; no load needed.
            return operand;
        }
        if (ptrType->pointed_type->isVoid()) {
            // GCC extension: *void_ptr is a no-op; just evaluate the pointer
            return operand;
        }
        llvm::Type* elementType = convert_type(ptrType->pointed_type);
        ret = builder.CreateLoad(elementType, operand, "deref");
        apply_load_qualifiers(llvm::cast<llvm::LoadInst>(ret), ptrType->pointed_type, module->getDataLayout());
    }  else {
        error("convert_unary_expr(): unary op " + std::to_string(static_cast<int>(uexpr->uop)) + " not implemented yet", expr->location);
        return nullptr;
    }
    return ret;
}
llvm::Value* ASTToLLVM::emit_bool_conversion(llvm::Value* val, const std::string& name) {
    if (val->getType()->isStructTy()) {
        // Complex type: nonzero if either real or imag is nonzero
        llvm::Value* real_part = builder.CreateExtractValue(val, {0}, name + ".r");
        llvm::Value* imag_part = builder.CreateExtractValue(val, {1}, name + ".i");
        llvm::Value* real_nz = nullptr;
        llvm::Value* imag_nz = nullptr;
        if (real_part->getType()->isFloatingPointTy()) {
            real_nz = builder.CreateFCmpUNE(real_part,
                llvm::ConstantFP::get(real_part->getType(), 0.0), name + ".r.nz");
            imag_nz = builder.CreateFCmpUNE(imag_part,
                llvm::ConstantFP::get(imag_part->getType(), 0.0), name + ".i.nz");
        } else {
            real_nz = builder.CreateICmpNE(real_part,
                llvm::ConstantInt::get(real_part->getType(), 0), name + ".r.nz");
            imag_nz = builder.CreateICmpNE(imag_part,
                llvm::ConstantInt::get(imag_part->getType(), 0), name + ".i.nz");
        }
        return builder.CreateOr(real_nz, imag_nz, name);
    }
    if (val->getType()->isFloatingPointTy()) {
        return builder.CreateFCmpUNE(val,
            llvm::ConstantFP::get(val->getType(), 0.0), name);
    }
    if (val->getType()->isPointerTy()) {
        return builder.CreateIsNotNull(val, name);
    }
    return builder.CreateICmpNE(val,
        llvm::ConstantInt::get(val->getType(), 0), name);
}

llvm::Value * ASTToLLVM::convert_logical_or_expr(BinaryOperation* expr) {
    if (!builder.GetInsertBlock()) {
        auto const_eval = eval_constexpr_i64(expr, ConstEvalMode::c_ice());
        if (!const_eval.has_value()) {
            error("logical || in global initializer must be a constant expression",
                  expr->location);
            return nullptr;
        }
        return llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context),
                                      *const_eval != 0);
    }

    // Logic: Res = L || R
    // 1. Evaluate L
    // 2. If L is true, Short-circuit: Result is 1 (Jump to Merge)
    // 3. If L is false, Evaluate R: Result is R (Jump to Merge)

    llvm::Value *left = convert_expression(expr->left.get());
    if (!left) return nullptr;

    llvm::Value *leftCond = emit_bool_conversion(left, "or.cond");

    llvm::Function *TheFunction = builder.GetInsertBlock()->getParent();
    llvm::BasicBlock *LeftBB = builder.GetInsertBlock();
    llvm::BasicBlock *RightBB = llvm::BasicBlock::Create(*context, "or.rhs");
    llvm::BasicBlock *MergeBB = llvm::BasicBlock::Create(*context, "or.merge");

    // Conditional Jump
    builder.CreateCondBr(leftCond, MergeBB, RightBB);
    // --- Emit Right Block ---
    RightBB->insertInto(TheFunction);
    builder.SetInsertPoint(RightBB);
    llvm::Value *right = convert_expression(expr->right.get());
    if (!right) return nullptr;
    llvm::Value *rightCond = emit_bool_conversion(right, "or.cond.rhs");
    llvm::Value *rightVal = builder.CreateZExt(rightCond, llvm::Type::getInt32Ty(*context), "or.val.rhs");

    builder.CreateBr(MergeBB);
    llvm::BasicBlock *RightEndBB = builder.GetInsertBlock(); // convert_expression might have changed the block

    // --- Emit Merge Block ---
    MergeBB->insertInto(TheFunction);
    builder.SetInsertPoint(MergeBB);
    llvm::PHINode *phi = builder.CreatePHI(llvm::Type::getInt32Ty(*context), 2, "or.res");
    phi->addIncoming(llvm::ConstantInt::get(*context,
        llvm::APInt(32, 1)), LeftBB); // Short-circuited true
    phi->addIncoming(rightVal, RightEndBB); // Result from RHS

    return phi;
}
llvm::Value * ASTToLLVM::convert_logical_and_expr(BinaryOperation* expr) {
    if (!builder.GetInsertBlock()) {
        auto const_eval = eval_constexpr_i64(expr, ConstEvalMode::c_ice());
        if (!const_eval.has_value()) {
            error("logical && in global initializer must be a constant expression",
                  expr->location);
            return nullptr;
        }
        return llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context),
                                      *const_eval != 0);
    }

    // Logic: Res = L && R
    // 1. Evaluate L
    // 2. If L is false, Short-circuit: Result is 0 (Jump to Merge)
    // 3. If L is true, Evaluate R: Result is R (Jump to Merge)

    llvm::Value *left = convert_expression(expr->left.get());
    if (!left) return nullptr;

    llvm::Value *leftCond = emit_bool_conversion(left, "and.cond");

    llvm::Function *TheFunction = builder.GetInsertBlock()->getParent();
    llvm::BasicBlock *LeftBB = builder.GetInsertBlock();
    llvm::BasicBlock *RightBB = llvm::BasicBlock::Create(*context, "and.rhs");
    llvm::BasicBlock *MergeBB = llvm::BasicBlock::Create(*context, "and.merge");

    builder.CreateCondBr(leftCond, RightBB, MergeBB);

    // --- Emit Right Block ---
    RightBB->insertInto(TheFunction);
    builder.SetInsertPoint(RightBB);
    llvm::Value *right = convert_expression(expr->right.get());
    if (!right) return nullptr;

    llvm::Value *rightCond = emit_bool_conversion(right, "and.cond.rhs");
    llvm::Value *rightVal = builder.CreateZExt(rightCond, llvm::Type::getInt32Ty(*context), "and.val.rhs");

    builder.CreateBr(MergeBB);
    llvm::BasicBlock *RightEndBB = builder.GetInsertBlock();

    // --- Emit Merge Block ---
    MergeBB->insertInto(TheFunction);
    builder.SetInsertPoint(MergeBB);
    llvm::PHINode *phi = builder.CreatePHI(llvm::Type::getInt32Ty(*context), 2, "and.res");
    phi->addIncoming(llvm::ConstantInt::get(*context,
        llvm::APInt(32, 0)), LeftBB); // Short-circuited false
    phi->addIncoming(rightVal, RightEndBB); // Result from RHS

    return phi;
}
LValueResult ASTToLLVM::get_lvalue(Expr * expr) {
    // ptr - location of a value
    // ctype - the type of the value we will find AT the location
    // In other words, At address "ptr" we will find a value of type "ctype"
    llvm::Value* ptr = nullptr;
    std::shared_ptr<CType> ctype = nullptr;
    if (auto* varRef = dyn_cast<VarRef>(expr)) {
        auto sym = varRef->symref;
        if (!sym) { error("get_lvalue(): variable not in scope", expr->location); return {}; }
        if (sym->kind == SymbolKind::ENUM_CONSTANT) {
            error("get_lvalue(): Enum constant is not an lvalue", expr->location);
            return {};
        }
        std::string mangled = mangleCIdentifier(sym->uid);
        if (!named_values.contains(mangled)) {
            // If this is a function type, look up or create the function in the module
            if (auto func_ctype = sym->type.as_shared<FunctionType>()) {
                llvm::Function* func =
                    get_or_create_function_symbol(sym, varRef->get_name());
                if (!func) {
                    error("get_lvalue(): failed to materialize function symbol",
                          expr->location);
                    return {};
                }
                return {static_cast<llvm::Value*>(func), sym->type.get_shared()};
            }
            error("get_lvalue(): variable not allocated", expr->location);
            return {};
        }
        ptr = named_values[mangled];
        ctype = sym->type.get_shared();

        if (sym->is_block_byref) {
            ptr = get_block_byref_payload_address(
                ptr,
                sym->type,
                expr->location,
                "get_lvalue()");
            if (!ptr) {
                return {};
            }
            ctype = remove_reference(sym->type, ast_ctx.get()).get_shared();
            return {ptr, ctype};
        }

        if (canonical_type_kind(sym->type, ast_ctx.get()) ==
            TypeKind::Reference) {
            auto ref_type =
                desugar_type(sym->type, ast_ctx.get()).as_shared<ReferenceType>();
            if (!ref_type || !ref_type->referred_type) {
                error("get_lvalue(): invalid reference variable type", expr->location);
                return {};
            }
            ctype = ref_type->referred_type.get_shared();
            llvm::Type* ptr_ty = llvm::PointerType::get(*context, 0);

            // Global/stack slots used to hold the bound address must be
            // loaded once to recover the referent pointer.
            if (auto* gvar = llvm::dyn_cast<llvm::GlobalVariable>(ptr)) {
                if (gvar->getValueType()->isPointerTy()) {
                    if (!builder.GetInsertBlock()) {
                        auto* init = gvar->getInitializer();
                        auto* init_ptr = llvm::dyn_cast_or_null<llvm::Constant>(init);
                        if (!init_ptr || !init_ptr->getType()->isPointerTy()) {
                            error("get_lvalue(): reference global requires pointer initializer", expr->location);
                            return {};
                        }
                        ptr = init_ptr;
                    } else {
                        ptr = builder.CreateLoad(ptr_ty, gvar, "ref.glob.addr");
                    }
                }
            } else if (auto* alloca = llvm::dyn_cast<llvm::AllocaInst>(ptr)) {
                if (alloca->getAllocatedType()->isPointerTy()) {
                    if (!builder.GetInsertBlock()) {
                        error("get_lvalue(): cannot load reference slot in global initializer", expr->location);
                        return {};
                    }
                    ptr = builder.CreateLoad(ptr_ty, alloca, "ref.addr");
                }
            }
            if (!ptr || !ptr->getType()->isPointerTy()) {
                error("get_lvalue(): reference binding does not produce an address", expr->location);
                return {};
            }
        }

    } else if (auto* byref_expr = dyn_cast<BlockByrefAccessExpr>(expr)) {
        llvm::Value* cell_ptr = convert_expression(byref_expr->cell_expr.get());
        if (!cell_ptr) {
            error("get_lvalue(): failed to evaluate __block cell expression",
                  expr->location);
            return {};
        }
        ptr = get_block_byref_payload_address(
            cell_ptr,
            byref_expr->ctype,
            expr->location,
            "get_lvalue()");
        if (!ptr) {
            return {};
        }
        ctype = remove_reference(byref_expr->ctype, ast_ctx.get()).get_shared();
    } else if (auto* cast = dyn_cast<ImplicitCast>(expr)) {
        if (canonical_type_kind(cast->get_type(), ast_ctx.get()) ==
            TypeKind::Reference) {
            auto ref_type =
                desugar_type(cast->get_type(), ast_ctx.get()).as_shared<ReferenceType>();
            if (!ref_type || !ref_type->referred_type) {
                error("get_lvalue(): invalid reference cast type", expr->location);
                return {};
            }
            ptr = convert_implicit_cast(cast);
            ctype = ref_type->referred_type.get_shared();
        }
    } else if (auto* call = dyn_cast<FuncCall>(expr)) {
        if (canonical_type_kind(call->get_type(), ast_ctx.get()) ==
            TypeKind::Reference) {
            auto ref_type =
                desugar_type(call->get_type(), ast_ctx.get()).as_shared<ReferenceType>();
            if (!ref_type || !ref_type->referred_type) {
                error("get_lvalue(): invalid reference return type", expr->location);
                return {};
            }
            ptr = convert_function_call(call);
            ctype = ref_type->referred_type.get_shared();
        }
    } else if (auto* dynamic_cast_expr = dyn_cast<CppDynamicCastExpr>(expr)) {
        if (canonical_type_kind(dynamic_cast_expr->get_type(), ast_ctx.get()) ==
            TypeKind::Reference) {
            auto ref_type = desugar_type(
                                dynamic_cast_expr->get_type(),
                                ast_ctx.get())
                                .as_shared<ReferenceType>();
            if (!ref_type || !ref_type->referred_type) {
                error("get_lvalue(): invalid dynamic_cast reference type", expr->location);
                return {};
            }
            ptr = convert_cpp_dynamic_cast_expression(dynamic_cast_expr);
            ctype = ref_type->referred_type.get_shared();
        }
    } else if (auto* cond = dyn_cast<CondExpr>(expr)) {
        if (!cond->isLValue()) {
            return {};
        }
        Expr* true_operand = cond->true_expr
            ? unwrap_lvalue_to_rvalue_casts(cond->true_expr.get())
            : unwrap_lvalue_to_rvalue_casts(cond->condition.get());
        Expr* false_operand = unwrap_lvalue_to_rvalue_casts(cond->false_expr.get());
        if (!true_operand || !false_operand) {
            error("get_lvalue(): invalid conditional operands", expr->location);
            return {};
        }

        auto cond_val = eval_constexpr_i64(
            cond->condition.get(), ConstEvalMode::c_ice());
        if (cond_val.has_value()) {
            return *cond_val != 0 ? get_lvalue(true_operand)
                                  : get_lvalue(false_operand);
        }
        if (!builder.GetInsertBlock()) {
            error("get_lvalue(): non-constant conditional expression in global initializer",
                  expr->location);
            return {};
        }

        llvm::Value* lowered_cond = convert_expression(cond->condition.get());
        if (!lowered_cond) {
            return {};
        }
        lowered_cond = emit_bool_conversion(lowered_cond, "cond.addr");

        llvm::Function* function = builder.GetInsertBlock()->getParent();
        auto* then_bb = llvm::BasicBlock::Create(*context, "cond.addr.then", function);
        auto* else_bb = llvm::BasicBlock::Create(*context, "cond.addr.else", function);
        auto* merge_bb = llvm::BasicBlock::Create(*context, "cond.addr.merge", function);
        builder.CreateCondBr(lowered_cond, then_bb, else_bb);

        builder.SetInsertPoint(then_bb);
        auto then_lvalue = get_lvalue(true_operand);
        if (!then_lvalue.address) {
            return {};
        }
        builder.CreateBr(merge_bb);
        then_bb = builder.GetInsertBlock();

        builder.SetInsertPoint(else_bb);
        auto else_lvalue = get_lvalue(false_operand);
        if (!else_lvalue.address) {
            return {};
        }
        builder.CreateBr(merge_bb);
        else_bb = builder.GetInsertBlock();

        builder.SetInsertPoint(merge_bb);
        llvm::Type* phi_type = then_lvalue.address->getType();
        if (else_lvalue.address->getType() != phi_type) {
            phi_type = llvm::PointerType::get(*context, 0);
            then_lvalue.address =
                cast_llvm_type(then_lvalue.address, phi_type, false);
            else_lvalue.address =
                cast_llvm_type(else_lvalue.address, phi_type, false);
        }
        auto* phi = builder.CreatePHI(phi_type, 2, "cond.addr");
        phi->addIncoming(then_lvalue.address, then_bb);
        phi->addIncoming(else_lvalue.address, else_bb);
        ptr = phi;
        ctype = cond->get_type().get_shared();
    } else if (auto* bin = dyn_cast<BinaryOperation>(expr)) {
        if (bin->bop == BinOpTypes::COMMA) {
            // C comma operator in lvalue context: evaluate LHS for side effects,
            // then take lvalue of RHS when available.
            convert_expression(bin->left.get());
            Expr* rhs = bin->right.get();
            while (auto* cast = dyn_cast<ImplicitCast>(rhs)) {
                if (cast->kind == ImplicitCastTypes::LVALUE_TO_RVALUE && cast->expr) {
                    rhs = cast->expr.get();
                    continue;
                }
                break;
            }
            return get_lvalue(rhs);
        }
    } else if (auto* deref = dyn_cast<UnaryOperation>(expr)) {
        if (deref->uop == UnaryOpTypes::REAL_PART || deref->uop == UnaryOpTypes::IMAG_PART) {
            // __real__ / __imag__ on complex lvalue: GEP into the struct
            auto inner_lvalue = get_lvalue(deref->exp.get());
            llvm::Value* base_ptr = inner_lvalue.address;
            auto base_ctype = inner_lvalue.type;
            if (!base_ptr || !base_ctype || !base_ctype->isComplex()) {
                error("get_lvalue(): __real__/__imag__ requires complex lvalue", expr->location);
                return {};
            }
            auto complex_type = dyn_cast_shared<ComplexType>(base_ctype);
            llvm::Type* struct_type = convert_type(base_ctype);
            unsigned field_idx = (deref->uop == UnaryOpTypes::REAL_PART) ? 0 : 1;
            ptr = builder.CreateStructGEP(struct_type, base_ptr, field_idx,
                deref->uop == UnaryOpTypes::REAL_PART ? "creal.addr" : "cimag.addr");
            ctype = complex_type->element_type;
        } else if (deref->uop == UnaryOpTypes::DEREFERENCE) {
            Expr* operand = deref->exp.get();
            // Strip any implicit casts that incorrectly turn a pointer into a non-pointer.
            while (auto* cast = dyn_cast<ImplicitCast>(operand)) {
                if (cast->expr && cast->expr->get_type() &&
                    canonical_type_kind(cast->expr->get_type(), ast_ctx.get()) ==
                        TypeKind::Pointer &&
                    canonical_type_kind(cast->get_type(), ast_ctx.get()) !=
                        TypeKind::Pointer) {
                    operand = cast->expr.get();
                    continue;
                }
                break;
            }
            ptr = convert_expression(operand);
            ctype = deref->get_type().get_shared();
        }
    } else if (auto* subscript = dyn_cast<ArraySubscriptExpr>(expr)) {
        // Array subscript is equivalent to *(a + i)
        // But we want the address, so (a + i)

        // Evaluate array (which decays to pointer)
        llvm::Value* arrVal = convert_expression(subscript->array.get());
        llvm::Value* idxVal = convert_expression(subscript->index.get());

        // Get element type
        auto ptrType =
            desugar_type(subscript->array->get_type(), ast_ctx.get())
                .as_shared<PointerType>();
        if (!ptrType) {
             error("get_lvalue(): Subscript on non-pointer type", expr->location);
             return {};
        }

        auto pointed_type = ptrType->pointed_type.get_shared();

        if (type_contains_vla(pointed_type)) {
            // VLA element type: compute stride at runtime, use byte-level GEP
            llvm::Value* stride = emit_type_size_bytes(pointed_type, true);
            if (!stride) {
                error("get_lvalue(): Cannot compute VLA stride", expr->location);
                return {};
            }
            llvm::Type* i64 = llvm::Type::getInt64Ty(*context);
            if (idxVal->getType() != i64) {
                bool isUnsigned = subscript->index->get_type() &&
                                  subscript->index->get_type()->isUnsigned();
                idxVal = builder.CreateIntCast(idxVal, i64, !isUnsigned, "idx_ext");
            }
            llvm::Value* byte_offset = builder.CreateMul(idxVal, stride, "vla_byte_offset");
            llvm::Type* i8 = llvm::Type::getInt8Ty(*context);
            ptr = builder.CreateGEP(i8, arrVal, byte_offset, "vla_array_idx");
        } else {
            // Extend the index to i64 with proper signedness to avoid
            // sign-extension issues (e.g., uint8_t 0xcf being treated as -49)
            llvm::Type* i64 = llvm::Type::getInt64Ty(*context);
            if (idxVal->getType() != i64 && idxVal->getType()->isIntegerTy()) {
                bool isUnsigned = subscript->index->get_type() &&
                                  subscript->index->get_type()->isUnsigned();
                idxVal = builder.CreateIntCast(idxVal, i64, !isUnsigned, "idx_ext");
            }
            llvm::Type* elemType = convert_type(ptrType->pointed_type);
            ptr = builder.CreateGEP(elemType, arrVal, idxVal, "array_idx");
        }
        ctype = subscript->get_type().get_shared();
    } else if (auto* predefined = dyn_cast<PredefinedExpr>(expr)) {
        ptr = builder.CreateGlobalString(predefined->func_name, "__func__");
        ctype = predefined->get_type().get_shared();
    } else if (auto* strLit = dyn_cast<StringLiteral>(expr)) {
        // String literal is an lvalue
        // todo: I don't think we will ever reach here, because of array decay?
        ptr = convert_expression(strLit);
        ctype = strLit->get_type().get_shared();
    } else if (auto* compoundLit = dyn_cast<CompoundLiteralExpr>(expr)) {
        // Compound literals are lvalues
        // convert_compound_literal returns the address (alloca or global)
        ptr = convert_compound_literal(compoundLit);
        ctype = compoundLit->type.get_shared();
    } else if (auto* member = dyn_cast<MemberExpr>(expr)) {
        // Member access: struct.field or ptr->field
        llvm::Value* base_ptr = nullptr;
        std::shared_ptr<ObjectType> record_type = nullptr;

        if (member->isArrow) {
            // Arrow operator: ptr->field
            // base is a pointer to struct, we evaluate it to get the pointer value
            llvm::Value* ptr_val = convert_expression(member->base.get());
            if (!ptr_val) {
                error("get_lvalue(): Cannot evaluate pointer in arrow member access", expr->location);
                return {};
            }

            // Get the pointed-to struct type
            auto base_type = desugar_type(member->base->get_type(), ast_ctx.get());
            auto ptr_type = base_type.as_shared<PointerType>();
            if (!ptr_type) {
                error("get_lvalue(): Arrow operator requires pointer type", expr->location);
                return {};
            }

            record_type =
                desugar_type(ptr_type->pointed_type, ast_ctx.get())
                    .as_shared<ObjectType>();
            if (!record_type) {
                error("get_lvalue(): Arrow operator requires pointer to struct type", expr->location);
                return {};
            }

            base_ptr = ptr_val;
        } else {
            // Dot operator: struct.field
            // Get the address of the base struct
            auto base_lvalue = get_lvalue(member->base.get());
            base_ptr = base_lvalue.address;
            if (!base_ptr) {
                // Base is an rvalue (e.g. function return, cast expression).
                // Materialize a temporary so we can take its address.
                auto base_ctype =
                    desugar_type(member->base->get_type(), ast_ctx.get());
                record_type = base_ctype.as_shared<ObjectType>();
                if (!record_type) {
                    error("get_lvalue(): Cannot get address of base in member access", expr->location);
                    return {};
                }
                llvm::Value* rval = convert_expression(member->base.get());
                llvm::Type* llvm_ty = convert_type(base_ctype.get_shared());
                llvm::Value* tmp = builder.CreateAlloca(llvm_ty, nullptr, "tmp.rval");
                builder.CreateStore(rval, tmp);
                base_ptr = tmp;
            } else {
                // Get the struct type
                auto base_type = base_lvalue.type;
                record_type = dyn_cast_shared<ObjectType>(
                    desugar_type(base_type, ast_ctx.get()));
                if (!record_type) {
                    error("get_lvalue(): Member access on non-struct type", expr->location);
                    return {};
                }
            }
        }

        llvm::Value* member_base_ptr = base_ptr;
        std::shared_ptr<ObjectType> member_record_type = record_type;
        if (!resolve_member_access_base_subobject(
                *this,
                member,
                base_ptr,
                record_type,
                member_base_ptr,
                member_record_type)) {
            return {};
        }

        // For structs with bitfields, use byte-offset GEP since C field indices
        // don't map 1:1 to LLVM struct field indices.
        // For structs without bitfields, use the traditional struct GEP.
        if (member_record_type->is_union && member->field_path.size() <= 1) {
            // For unions with direct (non-nested) member access, all members are at offset 0
            ptr = member_base_ptr;
            ctype = member->member_type.get_shared();
        } else if (record_uses_byte_layout(member_record_type.get())) {
            // Byte-offset GEP for structs represented as byte-layout
            llvm::Type* i8_type = llvm::Type::getInt8Ty(*context);
            llvm::Value* offset = llvm::ConstantInt::get(
                llvm::Type::getInt64Ty(*context), member->byte_offset);
            ptr = builder.CreateInBoundsGEP(i8_type, member_base_ptr, offset, "member_ptr");
            ctype = member->member_type.get_shared();
        } else if (!member->field_path.empty()) {
            // Walk through field_path for anonymous/nested struct members
            std::shared_ptr<ObjectType> current_record = member_record_type;
            ptr = member_base_ptr;
            for (size_t step = 0; step < member->field_path.size(); ++step) {
                if (!current_record) {
                    error("get_lvalue(): Invalid record type in member access", expr->location);
                    return {};
                }
                size_t idx = member->field_path[step];
                const auto& current_fields = current_record->semantic_fields();
                if (idx >= current_fields.size()) {
                    error("get_lvalue(): Member index " + std::to_string(idx) +
                          " out of range (" + current_record->to_string() +
                          " has " + std::to_string(current_fields.size()) +
                          " fields, member='" + member->get_member_name() + "')", expr->location);
                    return {};
                }
                const auto& field = current_fields[idx];
                bool is_last = (step + 1 == member->field_path.size());

                if (current_record->is_union) {
                    ctype = field.type.get_shared();
                    if (is_last) break;
                    current_record =
                        desugar_type(field.type, ast_ctx.get()).as_shared<ObjectType>();
                    if (!current_record) {
                        error("get_lvalue(): Member access on non-struct type inside union", expr->location);
                        return {};
                    }
                    continue;
                }

                if (record_uses_byte_layout(current_record.get())) {
                    // If any intermediate struct uses byte-layout, fall back to byte-offset GEP
                    llvm::Type* i8_type = llvm::Type::getInt8Ty(*context);
                    llvm::Value* offset = llvm::ConstantInt::get(
                        llvm::Type::getInt64Ty(*context), member->byte_offset);
                    ptr = builder.CreateInBoundsGEP(i8_type, member_base_ptr, offset, "member_ptr");
                    ctype = member->member_type.get_shared();
                    goto member_done;
                }

                llvm::Type* struct_llvm_type = convert_type(current_record);
                size_t llvm_idx = map_semantic_field_index_to_llvm_index(current_record.get(), idx);
                llvm::Value* indices[] = {
                    llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context), 0),
                    llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context), llvm_idx)
                };
                ptr = builder.CreateInBoundsGEP(struct_llvm_type, ptr, indices, "member_ptr");
                ctype = field.type.get_shared();
                if (is_last) break;
                current_record =
                    desugar_type(field.type, ast_ctx.get()).as_shared<ObjectType>();
                if (!current_record) {
                    error("get_lvalue(): Member access on non-struct type", expr->location);
                    return {};
                }
            }
            member_done:;
        } else {
            // Direct field index GEP (no bitfields, no field_path)
            llvm::Type* struct_llvm_type = convert_type(member_record_type);
            size_t llvm_idx = map_semantic_field_index_to_llvm_index(
                member_record_type.get(), member->field_index);
            llvm::Value* indices[] = {
                llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context), 0),
                llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context), llvm_idx)
            };
            ptr = builder.CreateInBoundsGEP(struct_llvm_type, member_base_ptr, indices, "member_ptr");
            ctype = member->member_type.get_shared();
        }

        if (canonical_type_kind(ctype, ast_ctx.get()) == TypeKind::Reference) {
            auto ref_type =
                dyn_cast_shared<ReferenceType>(
                    desugar_type(ctype, ast_ctx.get()));
            if (!ref_type || !ref_type->referred_type) {
                error("get_lvalue(): invalid reference member type", expr->location);
                return {};
            }
            if (!ptr || !ptr->getType()->isPointerTy()) {
                error("get_lvalue(): reference member slot did not produce an address",
                      expr->location);
                return {};
            }
            if (!builder.GetInsertBlock()) {
                error("get_lvalue(): cannot materialize reference member outside of function",
                      expr->location);
                return {};
            }
            llvm::Type* ptr_ty = llvm::PointerType::get(*context, 0);
            ptr = builder.CreateLoad(ptr_ty, ptr, "member.ref.addr");
            ctype = ref_type->referred_type.get_shared();
        }
    } else if (auto* member_ptr_access = dyn_cast<MemberPointerAccessExpr>(expr)) {
        if (member_ptr_access->is_function_member) {
            error("get_lvalue(): member-function pointer access is not an lvalue",
                  expr->location);
            return {};
        }

        llvm::Value* base_ptr = nullptr;
        if (member_ptr_access->is_arrow) {
            base_ptr = convert_expression(member_ptr_access->base.get());
            if (!base_ptr || !base_ptr->getType()->isPointerTy()) {
                error("get_lvalue(): arrow-star base did not produce pointer value",
                      expr->location);
                return {};
            }
            auto base_ptr_type =
                desugar_type(
                    member_ptr_access->base->get_type(),
                    ast_ctx.get())
                    .as_shared<PointerType>();
            if (!base_ptr_type || !base_ptr_type->pointed_type) {
                error("get_lvalue(): arrow-star requires pointer-to-object base",
                      expr->location);
                return {};
            }
        } else {
            auto base_lvalue = get_lvalue(member_ptr_access->base.get());
            base_ptr = base_lvalue.address;
            if (!base_ptr) {
                auto base_object_type =
                    desugar_type(
                        member_ptr_access->base->get_type(),
                        ast_ctx.get())
                        .as_shared<ObjectType>();
                if (!base_object_type) {
                    error("get_lvalue(): dot-star requires class/struct/union base",
                          expr->location);
                    return {};
                }
                llvm::Value* base_rvalue =
                    convert_expression(member_ptr_access->base.get());
                llvm::Type* base_llvm_type =
                    convert_type(base_object_type);
                llvm::Value* tmp = builder.CreateAlloca(base_llvm_type, nullptr, "tmp.dotstar.base");
                builder.CreateStore(base_rvalue, tmp);
                base_ptr = tmp;
            }
        }

        llvm::Value* member_ptr_val = convert_expression(member_ptr_access->member_pointer.get());
        if (!member_ptr_val) {
            error("get_lvalue(): failed to evaluate member-pointer operand", expr->location);
            return {};
        }
        llvm::Type* i64 = llvm::Type::getInt64Ty(*context);
        if (member_ptr_val->getType() != i64) {
            member_ptr_val = cast_llvm_type(member_ptr_val, i64, false);
        }

        llvm::Type* i8 = llvm::Type::getInt8Ty(*context);
        llvm::Value* base_i8 = builder.CreateBitCast(base_ptr, llvm::PointerType::get(*context, 0),
                                                     "dotstar.base.raw");
        llvm::Value* field_i8 = builder.CreateGEP(i8, base_i8, member_ptr_val,
                                                  "dotstar.field.raw");
        auto result_ctype = member_ptr_access->get_type().get_shared();
        if (!result_ctype) {
            error("get_lvalue(): member-pointer access has invalid result type",
                  expr->location);
            return {};
        }
        ptr = builder.CreateBitCast(
            field_i8,
            llvm::PointerType::get(*context, 0),
            "dotstar.field.ptr");
        // Keep semantic type so callers load/store with the proper value type.
        ctype = result_ctype;
    }
    return {ptr, ctype};
}
llvm::Value * ASTToLLVM::convert_assign_expr(BinaryOperation* expr) {
    // Check for vector subscript assignment first (before get_lvalue,
    // since vector subscript can't produce a regular pointer lvalue)
    if (auto* subscript = dyn_cast<ArraySubscriptExpr>(expr->left.get())) {
        auto arr_ctype = subscript->array->get_type();
        if (canonical_type_kind(arr_ctype, ast_ctx.get()) == TypeKind::Vector) {
            // Get the alloca/address of the vector variable
            // The subscript's array is wrapped in LVALUE_TO_RVALUE — unwrap it
            Expr* vec_lvalue_expr = subscript->array.get();
            while (auto* cast = dyn_cast<ImplicitCast>(vec_lvalue_expr)) {
                if (cast->kind == ImplicitCastTypes::LVALUE_TO_RVALUE) {
                    vec_lvalue_expr = cast->expr.get();
                    continue;
                }
                break;
            }
            auto vec_lvalue_tup = get_lvalue(vec_lvalue_expr);
            llvm::Value* vec_ptr = vec_lvalue_tup.address;
            auto vec_ctype = vec_lvalue_tup.type;
            if (!vec_ptr) {
                error("convert_assign_expr(): cannot get vector address for subscript assignment", expr->location);
                return nullptr;
            }
            llvm::Type* vec_llvm_type = convert_type(vec_ctype);
            llvm::Value* vec = builder.CreateLoad(vec_llvm_type, vec_ptr, "vec_load_for_insert");
            llvm::Value* idx = convert_expression(subscript->index.get());
            llvm::Value* rhs = convert_expression(expr->right.get());
            llvm::Value* new_vec = builder.CreateInsertElement(vec, rhs, idx, "vec_insert");
            builder.CreateStore(new_vec, vec_ptr);
            return rhs;
        }
    }

    // Left side must be an lvalue.
    // We need the address to store to.
    auto lvalue_tup = get_lvalue(expr->left.get());
    //auto ptr_type = lvalue_tup.type;

    llvm::Value* ptr = lvalue_tup.address;
    auto left_ctype = lvalue_tup.type;
    if (!ptr) {
        error("convert_assign_expr(): Assignment to non-lvalue", expr->location);
        return nullptr;
    }

    // Check if this is a struct assignment
    auto left_type = expr->left->get_type();
    if (left_type &&
        canonical_type_kind(left_type, ast_ctx.get()) == TypeKind::Object) {
        // Struct assignment: need to copy the entire struct
        auto record_type =
            desugar_type(left_type, ast_ctx.get()).as_shared<ObjectType>();
        if (!record_type) {
            error("convert_assign_expr(): Internal error - failed to cast to ObjectType", expr->location);
            return nullptr;
        }

        // Get the address of the RHS struct
        // The RHS might be wrapped in an ImplicitCast (LVALUE_TO_RVALUE), so we need to unwrap it
        Expr* rhs_expr = expr->right.get();
        if (auto* cast = dyn_cast<ImplicitCast>(rhs_expr)) {
            if (cast->kind == ImplicitCastTypes::LVALUE_TO_RVALUE) {
                rhs_expr = cast->expr.get();
            }
        }

        llvm::Value* rhs_ptr = nullptr;

        // Handle chain assignment: if RHS is also an assignment, get the LHS of that assignment
        if (auto* inner_assign = dyn_cast<BinaryOperation>(rhs_expr)) {
            if (is_assignment_binop(inner_assign->bop)) {
                // Execute the inner assignment first
                convert_assign_expr(inner_assign);
                // Now get the address of the LHS of the inner assignment (which holds the result)
                auto inner_lvalue = get_lvalue(inner_assign->left.get());
                rhs_ptr = inner_lvalue.address;
            }
        }

        if (!rhs_ptr) {
            auto rhs_lvalue = get_lvalue(rhs_expr);
            rhs_ptr = rhs_lvalue.address;
        }

        if (!rhs_ptr) {
            // RHS is an rvalue (e.g. function call returning a struct).
            // Evaluate it, store to a temporary, then memcpy from there.
            llvm::Value* rhs_val = convert_expression(expr->right.get());
            if (!rhs_val) {
                error("convert_assign_expr(): Cannot evaluate RHS in struct assignment", expr->location);
                return nullptr;
            }
            llvm::Type* struct_llvm_type = convert_type(record_type);
            llvm::Function* fn = builder.GetInsertBlock()->getParent();
            llvm::IRBuilder<> tmp_builder(&fn->getEntryBlock(), fn->getEntryBlock().begin());
            llvm::AllocaInst* tmp_alloca = tmp_builder.CreateAlloca(struct_llvm_type, nullptr, "struct_rval_tmp");
            tmp_alloca->setAlignment(llvm::Align(record_type->getAlignment()));
            builder.CreateStore(rhs_val, tmp_alloca);
            rhs_ptr = tmp_alloca;
        }

        // Get struct size in bytes
        size_t struct_size = static_cast<size_t>(record_type->getWidth() / 8);
        if (struct_size == 0) {
            // Zero-sized struct (e.g., struct { char c[0]; })
            return llvm::UndefValue::get(convert_type(record_type));
        }

        // Use memcpy to copy the struct
        // In LLVM, we can use CreateMemCpy intrinsic
        builder.CreateMemCpy(ptr, llvm::MaybeAlign(record_type->getAlignment()),
                             rhs_ptr, llvm::MaybeAlign(record_type->getAlignment()),
                             struct_size);

        // Load and return the assigned value (the destination struct)
        llvm::Type* struct_llvm_type = convert_type(record_type);
        return builder.CreateLoad(struct_llvm_type, ptr, "struct_assign_result");
    }

    // Check if this is a bitfield assignment
    if (auto* member = dyn_cast<MemberExpr>(expr->left.get())) {
        if (member->is_bitfield) {
            auto* bf_info = ast_ctx->get_bitfield_info(member->node_id);

            // Get base pointer for the bitfield
            llvm::Value* base_ptr = nullptr;

            if (member->isArrow) {
                // Arrow: base is pointer, evaluate to get pointer value
                base_ptr = convert_expression(member->base.get());
            } else {
                // Dot: base is struct, get its address
                auto base_lvalue = get_lvalue(member->base.get());
                base_ptr = base_lvalue.address;
            }

            if (!base_ptr) {
                error("convert_assign_expr(): Cannot get base pointer for bitfield assignment", expr->location);
                return nullptr;
            }

            // Get pointer to the storage unit
            llvm::Value* storage_ptr = get_bitfield_storage_ptr(member, base_ptr, bf_info);
            if (!storage_ptr) {
                return nullptr;
            }

            // Evaluate RHS
            llvm::Value* right = convert_expression(expr->right.get());
            if (!right) return nullptr;

            // Store the bitfield
            store_bitfield(storage_ptr, bf_info->storage_size,
                          bf_info->bit_offset, bf_info->bit_width, right);

            bool is_signed = member->get_type() && !member->get_type()->isUnsigned();
            llvm::Value* assigned = extract_bitfield(
                storage_ptr,
                bf_info->storage_size,
                bf_info->bit_offset,
                bf_info->bit_width,
                is_signed);
            if (!assigned) {
                return right;
            }
            return assigned;
        }
    }

    // Evaluate RHS
    llvm::Value* right = convert_expression(expr->right.get());
    if (!right) return nullptr;

    llvm::Value* newVal = right;
    llvm::Type* leftValType =
        left_ctype ? convert_type(left_ctype) : convert_type(expr->left->get_type().get_shared());
    if (leftValType && newVal->getType() != leftValType) {
        bool rhs_unsigned = expr->right->get_type() && expr->right->get_type()->isUnsigned();
        newVal = cast_llvm_type(newVal, leftValType, rhs_unsigned);
    }
    if (!newVal) {
        error("convert_assign_expr(): failed to convert RHS to assignment target type", expr->location);
        return nullptr;
    }

    // Store new value
    auto* store = builder.CreateStore(newVal, ptr);
    if (dyn_cast<MemberExpr>(expr->left.get())) {
        // Member writes may target packed/byte-layout fields.
        store->setAlignment(llvm::Align(1));
    }
    apply_store_qualifiers(store, expr->left->get_type(), module->getDataLayout());

    // Assignment expression returns the assigned value
    return newVal;
}
llvm::Value * ASTToLLVM::convert_compound_assignment(Expr *expr) {
    auto* comp_assign = dyn_cast<CompoundAssignOperation>(expr);
    if (!comp_assign) return nullptr;

    // Check if this is a bitfield compound assignment
    MemberExpr* bf_member = nullptr;
    llvm::Value* bf_storage_ptr = nullptr;
    const BitfieldInfo* bf_info = nullptr;
    if (auto* member = dyn_cast<MemberExpr>(comp_assign->left.get())) {
        if (member->is_bitfield) {
            bf_member = member;
            bf_info = ast_ctx->get_bitfield_info(member->node_id);

            // Get base pointer for the bitfield
            llvm::Value* base_ptr = nullptr;
            if (member->isArrow) {
                base_ptr = convert_expression(member->base.get());
            } else {
                auto base_lvalue = get_lvalue(member->base.get());
                base_ptr = base_lvalue.address;
            }

            if (!base_ptr) {
                error("convert_compound_assignment(): Cannot get base pointer for bitfield", expr->location);
                return nullptr;
            }

            bf_storage_ptr = get_bitfield_storage_ptr(member, base_ptr, bf_info);
            if (!bf_storage_ptr) {
                return nullptr;
            }
        }
    }

    // Check for vector subscript compound assignment (before get_lvalue,
    // since vector subscript can't produce a regular pointer lvalue)
    bool is_vec_subscript = false;
    llvm::Value* vec_ptr = nullptr;
    llvm::Type* vec_llvm_type = nullptr;
    llvm::Value* vec_idx = nullptr;
    if (auto* subscript = dyn_cast<ArraySubscriptExpr>(comp_assign->left.get())) {
        auto arr_ctype = subscript->array->get_type();
        if (canonical_type_kind(arr_ctype, ast_ctx.get()) == TypeKind::Vector) {
            is_vec_subscript = true;
            // Unwrap LVALUE_TO_RVALUE to get the vector's address
            Expr* vec_lvalue_expr = subscript->array.get();
            while (auto* cast = dyn_cast<ImplicitCast>(vec_lvalue_expr)) {
                if (cast->kind == ImplicitCastTypes::LVALUE_TO_RVALUE) {
                    vec_lvalue_expr = cast->expr.get();
                    continue;
                }
                break;
            }
            auto vec_lvalue_tup = get_lvalue(vec_lvalue_expr);
            vec_ptr = vec_lvalue_tup.address;
            auto vec_ctype = vec_lvalue_tup.type;
            if (!vec_ptr) {
                error("convert_compound_assignment(): cannot get vector address for subscript", expr->location);
                return nullptr;
            }
            vec_llvm_type = convert_type(vec_ctype);
            vec_idx = convert_expression(subscript->index.get());
        }
    }

    // 1. Evaluate LValue location (E1) - compute address/storage once
    llvm::Value* ptr = nullptr;
    llvm::Type* valType = nullptr;
    llvm::Value* e1Val = nullptr;

    if (!is_vec_subscript && !bf_member) {
        // Regular lvalue
        auto lvalue_tup = get_lvalue(comp_assign->left.get());
        if (!lvalue_tup) return nullptr;
        ptr = lvalue_tup.address;
        valType = convert_type(lvalue_tup.type);
    }

    // 2. Evaluate E2 before reading E1's current value.
    // Compound assignment evaluates the lvalue only once, but the RHS can
    // still affect the stored value observed by the read of E1.
    llvm::Value* e2Val = convert_expression(comp_assign->right.get());
    if (!e2Val) return nullptr;

    // 3. Read E1's current value.
    if (is_vec_subscript) {
        llvm::Value* vec = builder.CreateLoad(vec_llvm_type, vec_ptr, "vec_load_for_cmpd");
        e1Val = builder.CreateExtractElement(vec, vec_idx, "vec_elem_extract");
        valType = e1Val->getType();
    } else if (bf_member) {
        bool is_signed = !bf_member->member_type->isUnsigned();
        e1Val = extract_bitfield(bf_storage_ptr, bf_info->storage_size,
                                 bf_info->bit_offset, bf_info->bit_width, is_signed);
        valType = e1Val->getType();
    } else {
        e1Val = builder.CreateLoad(valType, ptr, "load_comp_assign");
        if (dyn_cast<MemberExpr>(comp_assign->left.get())) {
            llvm::cast<llvm::LoadInst>(e1Val)->setAlignment(llvm::Align(1));
        }
        apply_load_qualifiers(llvm::cast<llvm::LoadInst>(e1Val), comp_assign->left->get_type(), module->getDataLayout());
    }

    // 4. Perform Operation (E1 op E2)
    // Handle pointer arithmetic
    llvm::Value* resultVal = nullptr;
    if (valType->isPointerTy()) {
         auto ptrType = desugar_type(
             comp_assign->left->get_type(), ast_ctx.get()).as_shared<PointerType>();
         if (!ptrType) {
             error("convert_compound_assignment(): missing semantic pointer type",
                 expr->location);
             return nullptr;
         }
         auto pointed = ptrType->pointed_type.get_shared();

         if (type_contains_vla(pointed)) {
             llvm::Value* stride = emit_type_size_bytes(pointed, true);
             llvm::Type* i64 = llvm::Type::getInt64Ty(*context);
             llvm::Value* idx = e2Val;
             if (idx->getType() != i64) {
                 bool isUns = comp_assign->right->get_type() && comp_assign->right->get_type()->isUnsigned();
                 idx = builder.CreateIntCast(idx, i64, !isUns, "cmpd_idx_ext");
             }
             if (comp_assign->bop == BinOpTypes::ADD) {
                 llvm::Value* off = builder.CreateMul(idx, stride, "vla_cmpd_add_off");
                 resultVal = builder.CreateGEP(llvm::Type::getInt8Ty(*context), e1Val, off, "ptr_add_assign");
             } else if (comp_assign->bop == BinOpTypes::SUB) {
                 llvm::Value* negIdx = builder.CreateNeg(idx, "neg_right");
                 llvm::Value* off = builder.CreateMul(negIdx, stride, "vla_cmpd_sub_off");
                 resultVal = builder.CreateGEP(llvm::Type::getInt8Ty(*context), e1Val, off, "ptr_sub_assign");
             } else {
                 error("convert_compound_assignment(): Invalid compound assignment for pointer",
                     expr->location);
                 return nullptr;
             }
         } else {
             llvm::Type* elemType;
             if (ptrType->pointed_type->isVoid()) {
                 elemType = llvm::Type::getInt8Ty(*context);
             } else {
                 elemType = convert_type(ptrType->pointed_type);
             }

             // Match normal pointer arithmetic semantics: extend small integer
             // RHS operands according to their signedness before GEP.
             llvm::Type* i64 = llvm::Type::getInt64Ty(*context);
             llvm::Value* idx = e2Val;
             if (idx->getType() != i64 && idx->getType()->isIntegerTy()) {
                 bool isUns = comp_assign->right->get_type() &&
                              comp_assign->right->get_type()->isUnsigned();
                 idx = builder.CreateIntCast(idx, i64, !isUns, "cmpd_ptr_ext");
             }

             if (comp_assign->bop == BinOpTypes::ADD) {
                 resultVal = builder.CreateGEP(elemType, e1Val, idx, "ptr_add_assign");
             } else if (comp_assign->bop == BinOpTypes::SUB) {
                 llvm::Value* negRight = builder.CreateNeg(idx, "neg_right");
                 resultVal = builder.CreateGEP(elemType, e1Val, negRight, "ptr_sub_assign");
             } else {
                 error("convert_compound_assignment(): Invalid compound assignment for pointer",
                     expr->location);
                 return nullptr;
             }
         }
    } else {
        // Cast operands to the computation type (promoted type)
        llvm::Type* compType = convert_type(comp_assign->ctype);

        // We need to know if we should sign-extend or zero-extend.
        auto leftType = comp_assign->left->get_type();
        auto rightType = comp_assign->right->get_type();

        bool leftUnsigned = leftType ? leftType->isUnsigned() : false;
        bool rightUnsigned = rightType ? rightType->isUnsigned() : false;

        llvm::Value* e1Promoted = cast_llvm_type(e1Val, compType, leftUnsigned);
        llvm::Value* e2Promoted = cast_llvm_type(e2Val, compType, rightUnsigned);

        bool isOpUnsigned = comp_assign->ctype ? comp_assign->ctype->isUnsigned() : false;
        bool isFloating = comp_assign->ctype ? comp_assign->ctype->isFloatingPoint() : false;
        bool isComplex = comp_assign->ctype ? comp_assign->ctype->isComplex() : false;

        if (isComplex) {
            auto complex_type = comp_assign->ctype.as_shared<ComplexType>();
            llvm::Value* l_real = builder.CreateExtractValue(e1Promoted, {0}, "l.real");
            llvm::Value* l_imag = builder.CreateExtractValue(e1Promoted, {1}, "l.imag");
            llvm::Value* r_real = builder.CreateExtractValue(e2Promoted, {0}, "r.real");
            llvm::Value* r_imag = builder.CreateExtractValue(e2Promoted, {1}, "r.imag");
            bool complex_is_floating = l_real->getType()->isFloatingPointTy();
            bool complex_is_unsigned = complex_type && complex_type->element_type->isUnsigned();

            llvm::Value* re = nullptr;
            llvm::Value* im = nullptr;
            switch (comp_assign->bop) {
                case BinOpTypes::ADD:
                    if (complex_is_floating) {
                        re = builder.CreateFAdd(l_real, r_real, "cadd.r");
                        im = builder.CreateFAdd(l_imag, r_imag, "cadd.i");
                    } else {
                        re = builder.CreateAdd(l_real, r_real, "cadd.r");
                        im = builder.CreateAdd(l_imag, r_imag, "cadd.i");
                    }
                    break;
                case BinOpTypes::SUB:
                    if (complex_is_floating) {
                        re = builder.CreateFSub(l_real, r_real, "csub.r");
                        im = builder.CreateFSub(l_imag, r_imag, "csub.i");
                    } else {
                        re = builder.CreateSub(l_real, r_real, "csub.r");
                        im = builder.CreateSub(l_imag, r_imag, "csub.i");
                    }
                    break;
                case BinOpTypes::MULT: {
                    llvm::Value* ac = complex_is_floating
                        ? static_cast<llvm::Value*>(builder.CreateFMul(l_real, r_real, "cmul.ac"))
                        : static_cast<llvm::Value*>(builder.CreateMul(l_real, r_real, "cmul.ac"));
                    llvm::Value* bd = complex_is_floating
                        ? static_cast<llvm::Value*>(builder.CreateFMul(l_imag, r_imag, "cmul.bd"))
                        : static_cast<llvm::Value*>(builder.CreateMul(l_imag, r_imag, "cmul.bd"));
                    llvm::Value* ad = complex_is_floating
                        ? static_cast<llvm::Value*>(builder.CreateFMul(l_real, r_imag, "cmul.ad"))
                        : static_cast<llvm::Value*>(builder.CreateMul(l_real, r_imag, "cmul.ad"));
                    llvm::Value* bc = complex_is_floating
                        ? static_cast<llvm::Value*>(builder.CreateFMul(l_imag, r_real, "cmul.bc"))
                        : static_cast<llvm::Value*>(builder.CreateMul(l_imag, r_real, "cmul.bc"));
                    re = complex_is_floating
                        ? static_cast<llvm::Value*>(builder.CreateFSub(ac, bd, "cmul.r"))
                        : static_cast<llvm::Value*>(builder.CreateSub(ac, bd, "cmul.r"));
                    im = complex_is_floating
                        ? static_cast<llvm::Value*>(builder.CreateFAdd(ad, bc, "cmul.i"))
                        : static_cast<llvm::Value*>(builder.CreateAdd(ad, bc, "cmul.i"));
                    break;
                }
                case BinOpTypes::DIV: {
                    llvm::Value* ac = complex_is_floating
                        ? static_cast<llvm::Value*>(builder.CreateFMul(l_real, r_real, "cdiv.ac"))
                        : static_cast<llvm::Value*>(builder.CreateMul(l_real, r_real, "cdiv.ac"));
                    llvm::Value* bd = complex_is_floating
                        ? static_cast<llvm::Value*>(builder.CreateFMul(l_imag, r_imag, "cdiv.bd"))
                        : static_cast<llvm::Value*>(builder.CreateMul(l_imag, r_imag, "cdiv.bd"));
                    llvm::Value* bc = complex_is_floating
                        ? static_cast<llvm::Value*>(builder.CreateFMul(l_imag, r_real, "cdiv.bc"))
                        : static_cast<llvm::Value*>(builder.CreateMul(l_imag, r_real, "cdiv.bc"));
                    llvm::Value* ad = complex_is_floating
                        ? static_cast<llvm::Value*>(builder.CreateFMul(l_real, r_imag, "cdiv.ad"))
                        : static_cast<llvm::Value*>(builder.CreateMul(l_real, r_imag, "cdiv.ad"));
                    llvm::Value* cc = complex_is_floating
                        ? static_cast<llvm::Value*>(builder.CreateFMul(r_real, r_real, "cdiv.cc"))
                        : static_cast<llvm::Value*>(builder.CreateMul(r_real, r_real, "cdiv.cc"));
                    llvm::Value* dd = complex_is_floating
                        ? static_cast<llvm::Value*>(builder.CreateFMul(r_imag, r_imag, "cdiv.dd"))
                        : static_cast<llvm::Value*>(builder.CreateMul(r_imag, r_imag, "cdiv.dd"));
                    llvm::Value* denom = complex_is_floating
                        ? static_cast<llvm::Value*>(builder.CreateFAdd(cc, dd, "cdiv.den"))
                        : static_cast<llvm::Value*>(builder.CreateAdd(cc, dd, "cdiv.den"));
                    llvm::Value* re_num = complex_is_floating
                        ? static_cast<llvm::Value*>(builder.CreateFAdd(ac, bd, "cdiv.re_num"))
                        : static_cast<llvm::Value*>(builder.CreateAdd(ac, bd, "cdiv.re_num"));
                    llvm::Value* im_num = complex_is_floating
                        ? static_cast<llvm::Value*>(builder.CreateFSub(bc, ad, "cdiv.im_num"))
                        : static_cast<llvm::Value*>(builder.CreateSub(bc, ad, "cdiv.im_num"));
                    if (complex_is_floating) {
                        // Preserve IEEE signed-zero for exactly cancelled imaginary numerators.
                        auto* zero = llvm::ConstantFP::get(im_num->getType(), 0.0);
                        auto* neg_zero = builder.CreateFNeg(zero, "cdiv.neg_zero");
                        auto* im_is_zero = builder.CreateFCmpOEQ(im_num, zero, "cdiv.im_is_zero");
                        auto* bc_is_neg = builder.CreateFCmpOLT(bc, zero, "cdiv.bc_is_neg");
                        auto* signed_zero = builder.CreateSelect(bc_is_neg, neg_zero, zero, "cdiv.im_zero_sign");
                        im_num = builder.CreateSelect(im_is_zero, signed_zero, im_num, "cdiv.im_num_signed");
                    }
                    if (complex_is_floating) {
                        re = builder.CreateFDiv(re_num, denom, "cdiv.r");
                        im = builder.CreateFDiv(im_num, denom, "cdiv.i");
                    } else if (complex_is_unsigned) {
                        re = builder.CreateUDiv(re_num, denom, "cdiv.r");
                        im = builder.CreateUDiv(im_num, denom, "cdiv.i");
                    } else {
                        re = builder.CreateSDiv(re_num, denom, "cdiv.r");
                        im = builder.CreateSDiv(im_num, denom, "cdiv.i");
                    }
                    break;
                }
                default:
                    error("convert_compound_assignment(): Invalid compound assignment op on complex", expr->location);
                    return nullptr;
            }
            resultVal = llvm::UndefValue::get(e1Promoted->getType());
            resultVal = builder.CreateInsertValue(resultVal, re, {0});
            resultVal = builder.CreateInsertValue(resultVal, im, {1});
        } else {

        switch (comp_assign->bop) {
            case BinOpTypes::ADD:
                if (isFloating) resultVal = builder.CreateFAdd(e1Promoted, e2Promoted, "faddtmp");
                else resultVal = builder.CreateAdd(e1Promoted, e2Promoted, "addtmp");
                break;
            case BinOpTypes::SUB:
                if (isFloating) resultVal = builder.CreateFSub(e1Promoted, e2Promoted, "fsubtmp");
                else resultVal = builder.CreateSub(e1Promoted, e2Promoted, "subtmp");
                break;
            case BinOpTypes::MULT:
                if (isFloating) resultVal = builder.CreateFMul(e1Promoted, e2Promoted, "fmultmp");
                else resultVal = builder.CreateMul(e1Promoted, e2Promoted, "multmp");
                break;
            case BinOpTypes::DIV:
                if (isFloating) resultVal = builder.CreateFDiv(e1Promoted, e2Promoted, "fdivtmp");
                else if (isOpUnsigned) resultVal = builder.CreateUDiv(e1Promoted, e2Promoted, "divtmp");
                else resultVal = builder.CreateSDiv(e1Promoted, e2Promoted, "divtmp");
                break;
            case BinOpTypes::MOD:
                if (isFloating) resultVal = builder.CreateFRem(e1Promoted, e2Promoted, "fmodtmp");
                else if (isOpUnsigned) resultVal = builder.CreateURem(e1Promoted, e2Promoted, "modtmp");
                else resultVal = builder.CreateSRem(e1Promoted, e2Promoted, "modtmp");
                break;
            case BinOpTypes::BITWISE_AND:
                resultVal = builder.CreateAnd(e1Promoted, e2Promoted, "andtmp");
                break;
            case BinOpTypes::BITWISE_OR:
                resultVal = builder.CreateOr(e1Promoted, e2Promoted, "ortmp");
                break;
            case BinOpTypes::BITWISE_XOR:
                resultVal = builder.CreateXor(e1Promoted, e2Promoted, "xortmp");
                break;
            case BinOpTypes::SHIFT_LEFT:
                resultVal = builder.CreateShl(e1Promoted, e2Promoted, "shltmp");
                break;
            case BinOpTypes::SHIFT_RIGHT:
                if (isOpUnsigned) resultVal = builder.CreateLShr(e1Promoted, e2Promoted, "shrtmp");
                else resultVal = builder.CreateAShr(e1Promoted, e2Promoted, "shrtmp");
                break;
            default: error("convert_compound_assignment(): Invalid compound assignment op",
                expr->location); return nullptr;
        }
        } // end else (non-complex)
    }

    // 5. Cast result back to E1's type
    llvm::Value* finalVal = resultVal;
    if (finalVal->getType() != valType) {
        bool lhsUnsigned = comp_assign->left->get_type() ? comp_assign->left->get_type()->isUnsigned() : false;
        finalVal = cast_llvm_type(finalVal, valType, lhsUnsigned);
    }

    // 6. Store result
    if (is_vec_subscript) {
        // Vector subscript: load vector, insert element, store vector
        llvm::Value* vec = builder.CreateLoad(vec_llvm_type, vec_ptr, "vec_reload_for_insert");
        llvm::Value* new_vec = builder.CreateInsertElement(vec, finalVal, vec_idx, "vec_cmpd_insert");
        builder.CreateStore(new_vec, vec_ptr);
    } else if (bf_member) {
        // Store to bitfield
        store_bitfield(bf_storage_ptr, bf_info->storage_size,
                      bf_info->bit_offset, bf_info->bit_width, finalVal);
    } else {
        // Regular store
        auto *store = builder.CreateStore(finalVal, ptr);
        apply_store_qualifiers(store, comp_assign->left->get_type(), module->getDataLayout());
    }

    // 7. Return result
    return finalVal;
}
// todo: for comparisions we should check if one is a NAN and return false if true
// LLVM has built in nan but it returns true on the case of a NAN not false
llvm::Value * ASTToLLVM::convert_binary_expr(Expr *expr) {
    auto* bin_exp = dyn_cast<BinaryOperation>(expr);
    if (!bin_exp) return nullptr;
    if (bin_exp->bop == BinOpTypes::LOGICAL_AND) {
        return convert_logical_and_expr(bin_exp);
    } else if (bin_exp->bop == BinOpTypes::LOGICAL_OR) {
        return convert_logical_or_expr(bin_exp);
    } else if (is_assignment_binop(bin_exp->bop)) {
        return convert_assign_expr(bin_exp);
    }
    // For comma operator, the left side may be void (null result)
    if (bin_exp->bop == BinOpTypes::COMMA) {
        convert_expression(bin_exp->left.get()); // evaluate for side effects
        return convert_expression(bin_exp->right.get());
    }
    auto left = convert_expression(bin_exp->left.get());
    auto right = convert_expression(bin_exp->right.get());
    if (!left || !right) {
        throw std::runtime_error("missing expr in binop");
        return nullptr;
    }

    auto left_type = bin_exp->left->get_type();
    auto right_type = bin_exp->right->get_type();
    auto left_semantic = desugar_type(left_type, ast_ctx.get());
    auto right_semantic = desugar_type(right_type, ast_ctx.get());
    auto left_kind = left_semantic ? left_semantic->kind : TypeKind::Other;
    auto right_kind = right_semantic ? right_semantic->kind : TypeKind::Other;

    bool rightUnsigned = right_semantic && right_semantic->isUnsigned();
    bool isUnsigned = false;
    isUnsigned = left_semantic && left_semantic->isUnsigned();
    bool isFloating =
        (left_semantic && left_semantic->isFloatingPoint()) ||
        (right_semantic && right_semantic->isFloatingPoint());

    // Pointer Arithmetic
    if (left_kind == TypeKind::Pointer || right_kind == TypeKind::Pointer) {
        if (bin_exp->bop == BinOpTypes::ADD) {
            // ptr + int or int + ptr
            llvm::Value* ptrOp = left_kind == TypeKind::Pointer ? left : right;
            llvm::Value* intOp = left_kind == TypeKind::Pointer ? right : left;
            auto ptrType = (left_kind == TypeKind::Pointer ? left_semantic : right_semantic).as_shared<PointerType>();
            if (!ptrType) {
                error("convert_binary_expr(): invalid pointer operand in addition", expr->location);
                return nullptr;
            }
            auto pointed = ptrType->pointed_type.get_shared();
            if (type_contains_vla(pointed)) {
                // VLA pointed type: compute stride at runtime, byte-level GEP
                llvm::Value* stride = emit_type_size_bytes(pointed, true);
                llvm::Type* i64 = llvm::Type::getInt64Ty(*context);
                if (intOp->getType() != i64) {
                    auto intSrc = (left_kind == TypeKind::Pointer ? right_semantic : left_semantic);
                    bool isUns = intSrc && intSrc->isUnsigned();
                    intOp = builder.CreateIntCast(intOp, i64, !isUns, "ptr_add_ext");
                }
                llvm::Value* byte_off = builder.CreateMul(intOp, stride, "vla_ptr_add_off");
                return builder.CreateGEP(llvm::Type::getInt8Ty(*context), ptrOp, byte_off, "ptr_add");
            }
            // Extend the integer index to i64 with proper signedness
            llvm::Type* i64 = llvm::Type::getInt64Ty(*context);
            if (intOp->getType() != i64 && intOp->getType()->isIntegerTy()) {
                auto intSrc = (left_kind == TypeKind::Pointer ? right_semantic : left_semantic);
                bool isUns = intSrc && intSrc->isUnsigned();
                intOp = builder.CreateIntCast(intOp, i64, !isUns, "ptr_add_ext");
            }
            llvm::Type* elemType;
            if (ptrType->pointed_type->isVoid()) {
                elemType = llvm::Type::getInt8Ty(*context);
            } else {
                elemType = convert_type(ptrType->pointed_type);
            }

            return builder.CreateGEP(elemType, ptrOp, intOp, "ptr_add");
        } else if (bin_exp->bop == BinOpTypes::SUB) {
            if (left_kind == TypeKind::Pointer && right_kind == TypeKind::Pointer) {
                // ptr - ptr
                // Result is ptrdiff_t (i64)
                // We can use ptrtoint and sub, but that gives byte difference.
                // We need element difference.
                // LLVM provides a way? Or we divide by size.
                // Let's use ptrtoint and divide.

                llvm::Value* leftInt = builder.CreatePtrToInt(left, llvm::Type::getInt64Ty(*context));
                llvm::Value* rightInt = builder.CreatePtrToInt(right, llvm::Type::getInt64Ty(*context));
                llvm::Value* diff = builder.CreateSub(leftInt, rightInt, "ptr_diff_bytes");

                auto ptrType = left_semantic.as_shared<PointerType>();
                if (!ptrType) {
                    error("convert_binary_expr(): invalid pointer operands in subtraction", expr->location);
                    return nullptr;
                }
                auto pointed = ptrType->pointed_type.get_shared();
                llvm::Value* sizeVal;
                if (type_contains_vla(pointed)) {
                    sizeVal = emit_type_size_bytes(pointed, true);
                } else {
                    int64_t elemSize = pointed->getWidth() / 8;
                    if (elemSize == 0) elemSize = 1; // void* or similar?
                    sizeVal = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*context), elemSize);
                }
                return builder.CreateSDiv(diff, sizeVal, "ptr_diff");

            } else if (left_kind == TypeKind::Pointer) {
                // ptr - int
                auto ptrType = left_semantic.as_shared<PointerType>();
                if (!ptrType) {
                    error("convert_binary_expr(): invalid pointer left operand in subtraction", expr->location);
                    return nullptr;
                }
                auto pointed = ptrType->pointed_type.get_shared();
                if (type_contains_vla(pointed)) {
                    llvm::Value* stride = emit_type_size_bytes(pointed, true);
                    llvm::Type* i64 = llvm::Type::getInt64Ty(*context);
                    llvm::Value* negRight = builder.CreateNeg(right, "neg_right");
                    if (negRight->getType() != i64) {
                        negRight = builder.CreateIntCast(negRight, i64, true, "neg_ext");
                    }
                    llvm::Value* byte_off = builder.CreateMul(negRight, stride, "vla_ptr_sub_off");
                    return builder.CreateGEP(llvm::Type::getInt8Ty(*context), left, byte_off, "ptr_sub");
                }
                llvm::Type* elemType;
                if (ptrType->pointed_type->isVoid()) {
                    elemType = llvm::Type::getInt8Ty(*context);
                } else {
                    elemType = convert_type(ptrType->pointed_type);
                }
                // Extend to i64 before negation for proper signedness handling
                llvm::Type* i64 = llvm::Type::getInt64Ty(*context);
                llvm::Value* extRight = right;
                if (right->getType() != i64 && right->getType()->isIntegerTy()) {
                    bool isUns = right_type && right_type->isUnsigned();
                    extRight = builder.CreateIntCast(right, i64, !isUns, "ptr_sub_ext");
                }
                llvm::Value* negRight = builder.CreateNeg(extRight, "neg_right");
                return builder.CreateGEP(elemType, left, negRight, "ptr_sub");
            }
        }
    }

    // Complex arithmetic
    if (left_semantic && right_semantic &&
        left_semantic->isComplex() && right_semantic->isComplex()) {
        auto complex_type = left_semantic.as_shared<ComplexType>();
        llvm::Value* l_real = builder.CreateExtractValue(left, {0}, "l.real");
        llvm::Value* l_imag = builder.CreateExtractValue(left, {1}, "l.imag");
        llvm::Value* r_real = builder.CreateExtractValue(right, {0}, "r.real");
        llvm::Value* r_imag = builder.CreateExtractValue(right, {1}, "r.imag");
        bool complex_is_floating = l_real->getType()->isFloatingPointTy();
        bool complex_is_unsigned = complex_type && complex_type->element_type->isUnsigned();

        switch (bin_exp->bop) {
            case BinOpTypes::ADD: {
                llvm::Value* re = complex_is_floating
                    ? static_cast<llvm::Value*>(builder.CreateFAdd(l_real, r_real, "cadd.r"))
                    : static_cast<llvm::Value*>(builder.CreateAdd(l_real, r_real, "cadd.r"));
                llvm::Value* im = complex_is_floating
                    ? static_cast<llvm::Value*>(builder.CreateFAdd(l_imag, r_imag, "cadd.i"))
                    : static_cast<llvm::Value*>(builder.CreateAdd(l_imag, r_imag, "cadd.i"));
                llvm::Value* result = llvm::UndefValue::get(left->getType());
                result = builder.CreateInsertValue(result, re, {0});
                result = builder.CreateInsertValue(result, im, {1});
                return result;
            }
            case BinOpTypes::SUB: {
                llvm::Value* re = complex_is_floating
                    ? static_cast<llvm::Value*>(builder.CreateFSub(l_real, r_real, "csub.r"))
                    : static_cast<llvm::Value*>(builder.CreateSub(l_real, r_real, "csub.r"));
                bool lhs_from_real_to_complex = false;
                if (auto* lhs_cast = dyn_cast<ImplicitCast>(bin_exp->left.get())) {
                    lhs_from_real_to_complex =
                        lhs_cast->kind == ImplicitCastTypes::REAL_TO_COMPLEX;
                }
                llvm::Value* im = nullptr;
                if (lhs_from_real_to_complex) {
                    // Preserve signed-zero behavior for real-complex subtraction:
                    // x - (a + bi) must yield imaginary part -b (including -0.0).
                    im = complex_is_floating
                        ? static_cast<llvm::Value*>(builder.CreateFNeg(r_imag, "csub.i"))
                        : static_cast<llvm::Value*>(builder.CreateNeg(r_imag, "csub.i"));
                } else {
                    im = complex_is_floating
                        ? static_cast<llvm::Value*>(builder.CreateFSub(l_imag, r_imag, "csub.i"))
                        : static_cast<llvm::Value*>(builder.CreateSub(l_imag, r_imag, "csub.i"));
                }
                llvm::Value* result = llvm::UndefValue::get(left->getType());
                result = builder.CreateInsertValue(result, re, {0});
                result = builder.CreateInsertValue(result, im, {1});
                return result;
            }
            case BinOpTypes::MULT: {
                // (a+bi)(c+di) = (ac-bd) + (ad+bc)i
                llvm::Value* ac = complex_is_floating
                    ? static_cast<llvm::Value*>(builder.CreateFMul(l_real, r_real, "cmul.ac"))
                    : static_cast<llvm::Value*>(builder.CreateMul(l_real, r_real, "cmul.ac"));
                llvm::Value* bd = complex_is_floating
                    ? static_cast<llvm::Value*>(builder.CreateFMul(l_imag, r_imag, "cmul.bd"))
                    : static_cast<llvm::Value*>(builder.CreateMul(l_imag, r_imag, "cmul.bd"));
                llvm::Value* ad = complex_is_floating
                    ? static_cast<llvm::Value*>(builder.CreateFMul(l_real, r_imag, "cmul.ad"))
                    : static_cast<llvm::Value*>(builder.CreateMul(l_real, r_imag, "cmul.ad"));
                llvm::Value* bc = complex_is_floating
                    ? static_cast<llvm::Value*>(builder.CreateFMul(l_imag, r_real, "cmul.bc"))
                    : static_cast<llvm::Value*>(builder.CreateMul(l_imag, r_real, "cmul.bc"));
                llvm::Value* re = complex_is_floating
                    ? static_cast<llvm::Value*>(builder.CreateFSub(ac, bd, "cmul.r"))
                    : static_cast<llvm::Value*>(builder.CreateSub(ac, bd, "cmul.r"));
                llvm::Value* im = complex_is_floating
                    ? static_cast<llvm::Value*>(builder.CreateFAdd(ad, bc, "cmul.i"))
                    : static_cast<llvm::Value*>(builder.CreateAdd(ad, bc, "cmul.i"));
                llvm::Value* result = llvm::UndefValue::get(left->getType());
                result = builder.CreateInsertValue(result, re, {0});
                result = builder.CreateInsertValue(result, im, {1});
                return result;
            }
            case BinOpTypes::DIV: {
                // (a+bi)/(c+di) = ((ac+bd) + (bc-ad)i) / (c^2+d^2)
                llvm::Value* ac = complex_is_floating
                    ? static_cast<llvm::Value*>(builder.CreateFMul(l_real, r_real, "cdiv.ac"))
                    : static_cast<llvm::Value*>(builder.CreateMul(l_real, r_real, "cdiv.ac"));
                llvm::Value* bd = complex_is_floating
                    ? static_cast<llvm::Value*>(builder.CreateFMul(l_imag, r_imag, "cdiv.bd"))
                    : static_cast<llvm::Value*>(builder.CreateMul(l_imag, r_imag, "cdiv.bd"));
                llvm::Value* bc = complex_is_floating
                    ? static_cast<llvm::Value*>(builder.CreateFMul(l_imag, r_real, "cdiv.bc"))
                    : static_cast<llvm::Value*>(builder.CreateMul(l_imag, r_real, "cdiv.bc"));
                llvm::Value* ad = complex_is_floating
                    ? static_cast<llvm::Value*>(builder.CreateFMul(l_real, r_imag, "cdiv.ad"))
                    : static_cast<llvm::Value*>(builder.CreateMul(l_real, r_imag, "cdiv.ad"));
                llvm::Value* cc = complex_is_floating
                    ? static_cast<llvm::Value*>(builder.CreateFMul(r_real, r_real, "cdiv.cc"))
                    : static_cast<llvm::Value*>(builder.CreateMul(r_real, r_real, "cdiv.cc"));
                llvm::Value* dd = complex_is_floating
                    ? static_cast<llvm::Value*>(builder.CreateFMul(r_imag, r_imag, "cdiv.dd"))
                    : static_cast<llvm::Value*>(builder.CreateMul(r_imag, r_imag, "cdiv.dd"));
                llvm::Value* denom = complex_is_floating
                    ? static_cast<llvm::Value*>(builder.CreateFAdd(cc, dd, "cdiv.den"))
                    : static_cast<llvm::Value*>(builder.CreateAdd(cc, dd, "cdiv.den"));
                llvm::Value* re_num = complex_is_floating
                    ? static_cast<llvm::Value*>(builder.CreateFAdd(ac, bd, "cdiv.re_num"))
                    : static_cast<llvm::Value*>(builder.CreateAdd(ac, bd, "cdiv.re_num"));
                llvm::Value* im_num = complex_is_floating
                    ? static_cast<llvm::Value*>(builder.CreateFSub(bc, ad, "cdiv.im_num"))
                    : static_cast<llvm::Value*>(builder.CreateSub(bc, ad, "cdiv.im_num"));
                if (complex_is_floating) {
                    // Preserve IEEE signed-zero for exactly cancelled imaginary numerators.
                    auto* zero = llvm::ConstantFP::get(im_num->getType(), 0.0);
                    auto* neg_zero = builder.CreateFNeg(zero, "cdiv.neg_zero");
                    auto* im_is_zero = builder.CreateFCmpOEQ(im_num, zero, "cdiv.im_is_zero");
                    auto* bc_is_neg = builder.CreateFCmpOLT(bc, zero, "cdiv.bc_is_neg");
                    auto* signed_zero = builder.CreateSelect(bc_is_neg, neg_zero, zero, "cdiv.im_zero_sign");
                    im_num = builder.CreateSelect(im_is_zero, signed_zero, im_num, "cdiv.im_num_signed");
                }
                llvm::Value* re = nullptr;
                llvm::Value* im = nullptr;
                if (complex_is_floating) {
                    re = builder.CreateFDiv(re_num, denom, "cdiv.r");
                    im = builder.CreateFDiv(im_num, denom, "cdiv.i");
                } else if (complex_is_unsigned) {
                    re = builder.CreateUDiv(re_num, denom, "cdiv.r");
                    im = builder.CreateUDiv(im_num, denom, "cdiv.i");
                } else {
                    re = builder.CreateSDiv(re_num, denom, "cdiv.r");
                    im = builder.CreateSDiv(im_num, denom, "cdiv.i");
                }
                llvm::Value* result = llvm::UndefValue::get(left->getType());
                result = builder.CreateInsertValue(result, re, {0});
                result = builder.CreateInsertValue(result, im, {1});
                return result;
            }
            case BinOpTypes::EQUAL: {
                llvm::Value* re_eq = complex_is_floating
                    ? static_cast<llvm::Value*>(builder.CreateFCmpOEQ(l_real, r_real, "ceq.r"))
                    : static_cast<llvm::Value*>(builder.CreateICmpEQ(l_real, r_real, "ceq.r"));
                llvm::Value* im_eq = complex_is_floating
                    ? static_cast<llvm::Value*>(builder.CreateFCmpOEQ(l_imag, r_imag, "ceq.i"))
                    : static_cast<llvm::Value*>(builder.CreateICmpEQ(l_imag, r_imag, "ceq.i"));
                auto* both = builder.CreateAnd(re_eq, im_eq, "ceq");
                return builder.CreateZExt(both, llvm::Type::getInt32Ty(*context), "ceq_ext");
            }
            case BinOpTypes::NOT_EQUAL: {
                llvm::Value* re_ne = complex_is_floating
                    ? static_cast<llvm::Value*>(builder.CreateFCmpUNE(l_real, r_real, "cne.r"))
                    : static_cast<llvm::Value*>(builder.CreateICmpNE(l_real, r_real, "cne.r"));
                llvm::Value* im_ne = complex_is_floating
                    ? static_cast<llvm::Value*>(builder.CreateFCmpUNE(l_imag, r_imag, "cne.i"))
                    : static_cast<llvm::Value*>(builder.CreateICmpNE(l_imag, r_imag, "cne.i"));
                auto* either = builder.CreateOr(re_ne, im_ne, "cne");
                return builder.CreateZExt(either, llvm::Type::getInt32Ty(*context), "cne_ext");
            }
            default:
                error("invalid binary operator on complex types", expr->location);
                return nullptr;
        }
    }

    if (!left_semantic.equals_unqualified(right_semantic) &&
        bin_exp->bop != BinOpTypes::COMMA) {
        // technically we should be comparign the llvm types but we want stronger guarantee as two same ints can be dif
        // we should have checked this in sema but this is extra assurance
        if (bin_exp->bop == BinOpTypes::SHIFT_LEFT || bin_exp->bop == BinOpTypes::SHIFT_RIGHT) {
            // the right side of a shift just has to be an integer
            // right should be positive, if not result is undefined regarldess
            right = cast_llvm_type(right, left->getType(), rightUnsigned);
        } else if (left_kind == TypeKind::Pointer && right_kind == TypeKind::Pointer) {
            // Pointer types differing only in qualifiers are identical at LLVM IR level (opaque pointers)
        } else {
            error("convert_binary_expr(): types not equal",expr->location);
            return nullptr;
        }
    }

    if (left_kind == TypeKind::MemberPointer &&
        right_kind == TypeKind::MemberPointer &&
        (bin_exp->bop == BinOpTypes::EQUAL ||
         bin_exp->bop == BinOpTypes::NOT_EQUAL)) {
        bool is_not_equal = (bin_exp->bop == BinOpTypes::NOT_EQUAL);
        llvm::Value* cmp = nullptr;

        if (left->getType()->isStructTy()) {
            auto* payload_ty = llvm::dyn_cast<llvm::StructType>(left->getType());
            if (!payload_ty || payload_ty->getNumElements() != 2) {
                error("convert_binary_expr(): invalid member-function pointer payload type",
                      expr->location);
            }

            llvm::Value* lhs_payload =
                builder.CreateExtractValue(left, {0}, "memberfn_cmp.lhs.payload");
            llvm::Value* rhs_payload =
                builder.CreateExtractValue(right, {0}, "memberfn_cmp.rhs.payload");
            llvm::Value* lhs_adjust =
                builder.CreateExtractValue(left, {1}, "memberfn_cmp.lhs.adjust");
            llvm::Value* rhs_adjust =
                builder.CreateExtractValue(right, {1}, "memberfn_cmp.rhs.adjust");

            llvm::Value* payload_eq =
                builder.CreateICmpEQ(lhs_payload, rhs_payload, "memberfn_cmp.payload_eq");
            llvm::Value* adjust_eq =
                builder.CreateICmpEQ(lhs_adjust, rhs_adjust, "memberfn_cmp.adjust_eq");
            llvm::Value* both_eq =
                builder.CreateAnd(payload_eq, adjust_eq, "memberfn_cmp.both_eq");

            // Null function member pointers compare equal regardless of adjust payload.
            llvm::Value* lhs_is_null =
                builder.CreateIsNull(lhs_payload, "memberfn_cmp.lhs_null");
            llvm::Value* rhs_is_null =
                builder.CreateIsNull(rhs_payload, "memberfn_cmp.rhs_null");
            llvm::Value* both_null =
                builder.CreateAnd(lhs_is_null, rhs_is_null, "memberfn_cmp.both_null");
            cmp = builder.CreateOr(both_eq, both_null, "memberfn_cmp.eq");
        } else {
            cmp = builder.CreateICmpEQ(left, right, "memberptr_cmp.eq");
        }

        if (is_not_equal) {
            cmp = builder.CreateNot(cmp, "memberptr_cmp.ne");
        }
        return builder.CreateZExt(
            cmp,
            llvm::Type::getInt32Ty(*context),
            is_not_equal ? "memberptr_ne_ext" : "memberptr_eq_ext");
    }


    auto vector_cmp_result_type = [&](llvm::Value* vec_value) -> llvm::Type* {
        auto* vec_ty = llvm::dyn_cast<llvm::VectorType>(vec_value->getType());
        if (!vec_ty) {
            return nullptr;
        }
        // GCC vector comparisons produce integer vectors with the same lane width
        // as operands (all-bits-one for true, zero for false).
        llvm::Type* elem_ty = vec_ty->getScalarType();
        unsigned elem_bits = elem_ty->getPrimitiveSizeInBits();
        if (elem_bits == 0) {
            elem_bits = 32;
        }
        llvm::Type* int_elem_ty = llvm::Type::getIntNTy(*context, elem_bits);
        if (auto* fixed = llvm::dyn_cast<llvm::FixedVectorType>(vec_ty)) {
            return llvm::FixedVectorType::get(int_elem_ty, fixed->getNumElements());
        }
        if (auto* scalable = llvm::dyn_cast<llvm::ScalableVectorType>(vec_ty)) {
            return llvm::ScalableVectorType::get(int_elem_ty, scalable);
        }
        return nullptr;
    };

    switch (bin_exp->bop) {
        case BinOpTypes::COMMA:
            return right;
        case BinOpTypes::ADD:
            if (isFloating) {
                auto try_emit_fmuladd = [&](llvm::Value* maybe_mul, llvm::Value* addend) -> llvm::Value* {
                    // Pattern-match `(a*b)+c` to `llvm.fmuladd` when the FMul is
                    // already present and types align.
                    auto* mul_inst = llvm::dyn_cast<llvm::Instruction>(maybe_mul);
                    if (!mul_inst || mul_inst->getOpcode() != llvm::Instruction::FMul) {
                        return nullptr;
                    }
                    if (mul_inst->getType() != addend->getType()) {
                        return nullptr;
                    }
                    llvm::Function* fma = llvm::Intrinsic::getDeclaration(
                        module.get(),
                        llvm::Intrinsic::fmuladd,
                        {addend->getType()});
                    return builder.CreateCall(
                        fma,
                        {mul_inst->getOperand(0), mul_inst->getOperand(1), addend},
                        "fmaaddtmp");
                };
                if (llvm::Value* fused = try_emit_fmuladd(left, right)) {
                    return fused;
                }
                if (llvm::Value* fused = try_emit_fmuladd(right, left)) {
                    return fused;
                }
                return builder.CreateFAdd(left, right, "faddtmp");
            }
            return builder.CreateAdd(left, right, "addtmp");
        case BinOpTypes::SUB:
            if (isFloating) return builder.CreateFSub(left, right, "fsubtmp");
            return builder.CreateSub(left, right, "subtmp");
        case BinOpTypes::MULT:
            if (isFloating) return builder.CreateFMul(left, right, "fmultmp");
            return builder.CreateMul(left, right, "multmp");
        case BinOpTypes::DIV:
            if (isFloating) return builder.CreateFDiv(left, right, "fdivtmp");
            if (isUnsigned) {
                return builder.CreateUDiv(left, right, "divtmp");
            } else {
                return builder.CreateSDiv(left, right, "divtmp");
            }
        case BinOpTypes::MOD:
            if (isFloating) return builder.CreateFRem(left, right, "fmodtmp");
            if (isUnsigned) {
                return builder.CreateURem(left, right, "modtmp");
            } else {
                return builder.CreateSRem(left, right, "modtmp");
            }
        case BinOpTypes::BITWISE_AND:
            return builder.CreateAnd(left, right, "andtmp");
        case BinOpTypes::BITWISE_OR:
            return builder.CreateOr(left, right, "ortmp");
        case BinOpTypes::BITWISE_XOR:
            return builder.CreateXor(left, right, "xortmp");
        case BinOpTypes::SHIFT_LEFT:
            return builder.CreateShl(left, right, "shltmp");
        case BinOpTypes::SHIFT_RIGHT:
            if (isUnsigned) {
                return builder.CreateLShr(left, right, "shrtmp");
            } else {
                return builder.CreateAShr(left, right, "shrtmp");
            }
            // Comparison operators return i1 (boolean), but in C they return int (0 or 1).
            // For vectors: sext <N x i1> -> <N x iW> (0/-1 semantics per GCC vector extensions).
            // For scalars: ZExt to i32.
        case BinOpTypes::EQUAL: {
            llvm::Value* cmp;
            if (isFloating) cmp = builder.CreateFCmpOEQ(left, right, "feqtmp");
            else cmp = builder.CreateICmpEQ(left, right, "eqtmp");
            if (left->getType()->isVectorTy()) {
                llvm::Type* dest = vector_cmp_result_type(left);
                if (!dest) {
                    error("convert_binary_expr(): invalid vector comparison result type", expr->location);
                }
                return builder.CreateSExt(cmp, dest, "vec_eq_sext");
            }
            return builder.CreateZExt(cmp, llvm::Type::getInt32Ty(*context), "eq_ext");
        }
        case BinOpTypes::NOT_EQUAL: {
            llvm::Value* cmp;
            if (isFloating) cmp = builder.CreateFCmpUNE(left, right, "fnetmp");
            else cmp = builder.CreateICmpNE(left, right, "netmp");
            if (left->getType()->isVectorTy()) {
                llvm::Type* dest = vector_cmp_result_type(left);
                if (!dest) {
                    error("convert_binary_expr(): invalid vector comparison result type", expr->location);
                }
                return builder.CreateSExt(cmp, dest, "vec_ne_sext");
            }
            return builder.CreateZExt(cmp, llvm::Type::getInt32Ty(*context), "ne_ext");
        }
        case BinOpTypes::LESS_THAN: {
            llvm::Value* cmp;
            if (isFloating) cmp = builder.CreateFCmpOLT(left, right, "flttmp");
            else if (isUnsigned) cmp = builder.CreateICmpULT(left, right, "lttmp");
            else cmp = builder.CreateICmpSLT(left, right, "lttmp");
            if (left->getType()->isVectorTy()) {
                llvm::Type* dest = vector_cmp_result_type(left);
                if (!dest) {
                    error("convert_binary_expr(): invalid vector comparison result type", expr->location);
                }
                return builder.CreateSExt(cmp, dest, "vec_lt_sext");
            }
            return builder.CreateZExt(cmp, llvm::Type::getInt32Ty(*context), "lt_ext");
        }
        case BinOpTypes::LESS_EQUAL_THAN: {
            llvm::Value* cmp;
            if (isFloating) cmp = builder.CreateFCmpOLE(left, right, "fletmp");
            else if (isUnsigned) cmp = builder.CreateICmpULE(left, right, "letmp");
            else cmp = builder.CreateICmpSLE(left, right, "letmp");
            if (left->getType()->isVectorTy()) {
                llvm::Type* dest = vector_cmp_result_type(left);
                if (!dest) {
                    error("convert_binary_expr(): invalid vector comparison result type", expr->location);
                }
                return builder.CreateSExt(cmp, dest, "vec_le_sext");
            }
            return builder.CreateZExt(cmp, llvm::Type::getInt32Ty(*context), "le_ext");
        }
        case BinOpTypes::GREATER_THAN: {
            llvm::Value* cmp;
            if (isFloating) cmp = builder.CreateFCmpOGT(left, right, "fgttmp");
            else if (isUnsigned) cmp = builder.CreateICmpUGT(left, right, "gttmp");
            else cmp = builder.CreateICmpSGT(left, right, "gttmp");
            if (left->getType()->isVectorTy()) {
                llvm::Type* dest = vector_cmp_result_type(left);
                if (!dest) {
                    error("convert_binary_expr(): invalid vector comparison result type", expr->location);
                }
                return builder.CreateSExt(cmp, dest, "vec_gt_sext");
            }
            return builder.CreateZExt(cmp, llvm::Type::getInt32Ty(*context), "gt_ext");
        }
        case BinOpTypes::GREATER_EQUAL_THAN: {
            llvm::Value* cmp;
            if (isFloating) cmp = builder.CreateFCmpOGE(left, right, "fgetmp");
            else if (isUnsigned) cmp = builder.CreateICmpUGE(left, right, "getmp");
            else cmp = builder.CreateICmpSGE(left, right, "getmp");
            if (left->getType()->isVectorTy()) {
                llvm::Type* dest = vector_cmp_result_type(left);
                if (!dest) {
                    error("convert_binary_expr(): invalid vector comparison result type", expr->location);
                }
                return builder.CreateSExt(cmp, dest, "vec_ge_sext");
            }
            return builder.CreateZExt(cmp, llvm::Type::getInt32Ty(*context), "ge_ext");
        }
        default: break;
    }
    error("convert_binary_expr(): invalid operator", expr->location); // Should not be reached if all BinOpTypes are handled
    return nullptr;
}
llvm::Value* ASTToLLVM::convert_conditional_expr(CondExpr *expr) {
    if (!expr) return nullptr;

    // If the condition is a compile-time constant, short-circuit to the
    // selected branch.  This is required at global scope (where basic blocks
    // cannot be created) and beneficial inside functions (it produces LLVM
    // constants for use in static initializers, etc.).
    auto cond_val = eval_constexpr_i64(
        expr->condition.get(), ConstEvalMode::c_ice());
    if (cond_val.has_value()) {
        if (*cond_val != 0) {
            // GCC extension: omitted middle operand — use condition value
            if (!expr->true_expr)
                return convert_expression(expr->condition.get());
            return convert_expression(expr->true_expr.get());
        } else {
            return convert_expression(expr->false_expr.get());
        }
    }
    if (!builder.GetInsertBlock()) {
        error("ternary condition in global initializer must be a constant expression",
              expr->location);
        return nullptr;
    }

    auto common_type = expr->type;
    bool is_void = common_type && common_type->isVoid();
    llvm::Type* llvm_common_type = is_void ? nullptr : convert_type(common_type);
    llvm::Value* condVal = convert_expression(expr->condition.get());
    if (!condVal) return nullptr;

    // Convert condition to bool (i1)
    condVal = emit_bool_conversion(condVal, "cond");

    llvm::Function* function = builder.GetInsertBlock()->getParent();

    llvm::BasicBlock* thenBB = llvm::BasicBlock::Create(*context, "cond.then");
    llvm::BasicBlock* elseBB = llvm::BasicBlock::Create(*context, "cond.else");
    llvm::BasicBlock* mergeBB = llvm::BasicBlock::Create(*context, "cond.merge");

    builder.CreateCondBr(condVal, thenBB, elseBB);

    // Then block
    function->insert(function->end(), thenBB);
    builder.SetInsertPoint(thenBB);
    llvm::Value* thenVal;
    if (expr->true_expr) {
        thenVal = convert_expression(expr->true_expr.get());
    } else {
        // GCC extension: omitted middle operand — re-evaluate condition as the value
        thenVal = convert_expression(expr->condition.get());
        // Cast to the common type if needed (e.g., uint32_t condition with uint64_t result)
        if (llvm_common_type && thenVal->getType() != llvm_common_type) {
            if (thenVal->getType()->isIntegerTy() && llvm_common_type->isIntegerTy()) {
                thenVal = builder.CreateIntCast(thenVal, llvm_common_type, false);
            } else if (thenVal->getType()->isPointerTy() || llvm_common_type->isPointerTy()) {
                thenVal = builder.CreateBitCast(thenVal, llvm_common_type);
            }
        }
    }
    if (!thenVal) return nullptr;
    builder.CreateBr(mergeBB); // should we check for terminator?
    thenBB = builder.GetInsertBlock(); // Update in case of block change

    // Else block
    function->insert(function->end(), elseBB);
    builder.SetInsertPoint(elseBB);
    llvm::Value* elseVal = convert_expression(expr->false_expr.get());
    if (!elseVal) return nullptr;
    builder.CreateBr(mergeBB);
    elseBB = builder.GetInsertBlock();

    // Merge block
    function->insert(function->end(), mergeBB);
    builder.SetInsertPoint(mergeBB);

    // Void ternary (e.g., assert macro): no PHI needed
    if (is_void) {
        return llvm::UndefValue::get(llvm::Type::getInt32Ty(*context));
    }

    // Ensure both values match the PHI type (insert cast before the branch terminator)
    auto ensure_type = [&](llvm::Value*& val, llvm::BasicBlock* bb) {
        if (val->getType() != llvm_common_type) {
            // Cast in predecessor blocks so the PHI always receives values of the
            // exact common type selected for the conditional expression.
            // Insert before the terminator (branch) of this block
            builder.SetInsertPoint(bb->getTerminator());
            if (val->getType()->isIntegerTy() && llvm_common_type->isIntegerTy()) {
                val = builder.CreateIntCast(val, llvm_common_type, false);
            } else if (val->getType()->isFloatingPointTy() && llvm_common_type->isFloatingPointTy()) {
                val = builder.CreateFPCast(val, llvm_common_type);
            } else if (val->getType()->isIntegerTy() && llvm_common_type->isFloatingPointTy()) {
                val = builder.CreateSIToFP(val, llvm_common_type);
            } else if (val->getType()->isFloatingPointTy() && llvm_common_type->isIntegerTy()) {
                val = builder.CreateFPToSI(val, llvm_common_type);
            } else if (val->getType()->isIntegerTy() && llvm_common_type->isPointerTy()) {
                val = builder.CreateIntToPtr(val, llvm_common_type);
            } else if (val->getType()->isPointerTy() && llvm_common_type->isIntegerTy()) {
                val = builder.CreatePtrToInt(val, llvm_common_type);
            }
            builder.SetInsertPoint(mergeBB);
        }
    };
    ensure_type(thenVal, thenBB);
    ensure_type(elseVal, elseBB);

    // Create PHI node
    llvm::PHINode* phi = builder.CreatePHI(llvm_common_type, 2, "condtmp");
    phi->addIncoming(thenVal, thenBB);
    phi->addIncoming(elseVal, elseBB);

    return phi;
}
