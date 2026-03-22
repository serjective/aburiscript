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

llvm::Value* ASTToLLVM::convert_member_expr(MemberExpr *expr) {
    auto lvalue_tup = get_lvalue(expr);
    llvm::Value* ptr = lvalue_tup.address;
    std::shared_ptr<CType> ctype = lvalue_tup.type;
    if (!ptr || !ctype) {
        return nullptr;
    }

    if (expr->is_bitfield) {
        // Bitfield rvalue extraction requires explicit lvalue-to-rvalue
        // cast semantics to preserve width/sign behavior.
        error("convert_member_expr(): unexpected direct bitfield rvalue access", expr->location);
        return nullptr;
    }

    llvm::Type* val_type = convert_type(ctype);
    if (!val_type) {
        error("convert_member_expr(): failed to lower member type", expr->location);
        return nullptr;
    }
    return builder.CreateLoad(val_type, ptr, "member_load");
}

llvm::Value* ASTToLLVM::convert_member_pointer_literal_expr(
    MemberPointerLiteralExpr* expr) {
    if (!expr || !expr->ctype) {
        return nullptr;
    }
    auto mp_type =
        desugar_type(expr->ctype, ast_ctx.get()).as_shared<MemberPointerType>();
    if (!mp_type) {
        error("convert_member_pointer_literal_expr(): invalid member-pointer type",
              expr ? expr->location : SrcLoc());
        return nullptr;
    }
    auto member_kind = canonical_type_kind(mp_type->member_type, ast_ctx.get());
    llvm::Type* llvm_type = convert_type(expr->ctype);
    if (member_kind == TypeKind::Function || expr->is_function_member) {
        auto* struct_type = llvm::dyn_cast<llvm::StructType>(llvm_type);
        if (!struct_type || struct_type->getNumElements() != 2) {
            error("convert_member_pointer_literal_expr(): expected function member-pointer payload type",
                  expr->location);
            return nullptr;
        }
        auto* ptr_type =
            llvm::dyn_cast<llvm::PointerType>(struct_type->getElementType(0));
        llvm::Type* adj_type = struct_type->getElementType(1);
        if (!ptr_type || !adj_type->isIntegerTy(64)) {
            error("convert_member_pointer_literal_expr(): invalid function member-pointer payload layout",
                  expr->location);
            return nullptr;
        }

        llvm::Constant* function_payload =
            llvm::ConstantPointerNull::get(ptr_type);
        if (expr->virtual_slot_index >= 0) {
            size_t physical_slot_index =
                static_cast<size_t>(expr->virtual_slot_index);
            auto class_record =
                desugar_type(mp_type->class_type, ast_ctx.get()).as_shared<ObjectType>();
            const ObjectDecl* class_record_decl = class_record
                ? canonical_cpp_record_decl(
                    dyn_cast<ObjectDecl>(class_record->get_decl()))
                : nullptr;
            if (const RecordSemanticState* class_state =
                    lookup_cpp_record_state(class_record_decl)) {
                physical_slot_index = cpp_vtable_physical_slot_index(
                    class_state,
                    static_cast<size_t>(expr->virtual_slot_index));
            }
            uint64_t encoded_slot =
                (static_cast<uint64_t>(physical_slot_index) << 1U) | 1U;
            function_payload = llvm::ConstantExpr::getIntToPtr(
                llvm::ConstantInt::get(
                    llvm::Type::getInt64Ty(*context), encoded_slot, false),
                ptr_type);
        } else if (expr->method_symbol) {
            if (expr->method_symbol->kind != SymbolKind::FUNCTION) {
                error("convert_member_pointer_literal_expr(): invalid method symbol kind",
                      expr->location);
                return nullptr;
            }
            llvm::Function* fn = get_or_create_function_symbol(
                expr->method_symbol, expr->method_symbol->name);
            if (!fn) {
                error("convert_member_pointer_literal_expr(): unresolved method type",
                      expr->location);
                return nullptr;
            }
            function_payload = llvm::ConstantExpr::getBitCast(fn, ptr_type);
        }

        llvm::Constant* this_adjust_payload = llvm::ConstantInt::getSigned(
            adj_type, expr->byte_offset);
        return llvm::ConstantStruct::get(
            struct_type, {function_payload, this_adjust_payload});
    }

    if (!llvm_type || !llvm_type->isIntegerTy()) {
        error("convert_member_pointer_literal_expr(): expected integer payload type",
              expr->location);
        return nullptr;
    }
    return llvm::ConstantInt::getSigned(llvm_type, expr->byte_offset);
}

llvm::Value* ASTToLLVM::convert_member_pointer_access_expr(
    MemberPointerAccessExpr* expr) {
    if (expr && expr->is_function_member) {
        return convert_expression(expr->member_pointer.get());
    }
    auto lvalue_tup = get_lvalue(expr);
    llvm::Value* ptr = lvalue_tup.address;
    std::shared_ptr<CType> ctype = lvalue_tup.type;
    if (!ptr || !ctype) {
        return nullptr;
    }
    llvm::Type* val_type = convert_type(ctype);
    if (!val_type) {
        error("convert_member_pointer_access_expr(): failed to lower member type",
              expr->location);
        return nullptr;
    }
    return builder.CreateLoad(val_type, ptr, "member_ptr_load");
}

llvm::Value* ASTToLLVM::convert_sizeof_expr(SizeOfExpr *expr) {
    // For non-VLA types, sizeof is a compile-time constant
    if (!expr->is_runtime_sizeof) {
        std::shared_ptr<CType> target_type = expr->getTargetType().get_shared();
        if (!target_type) {
            error("convert_sizeof_expr(): No target type", expr->location);
            return nullptr;
        }

        int64_t size_bytes = target_type->getWidthBytes();

        // Return as size_t (unsigned long)
        llvm::Type* result_llvm_type = convert_type(expr->result_type);
        return llvm::ConstantInt::get(result_llvm_type, size_bytes, false);
    }

    std::shared_ptr<CType> target_type = expr->getTargetType().get_shared();
    if (!target_type) {
        error("convert_sizeof_expr(): No target type", expr->location);
        return nullptr;
    }
    bool use_cache = expr->expr_operand != nullptr;
    llvm::Value* size_val = emit_type_size_bytes(target_type, use_cache);
    if (!size_val) return nullptr;

    llvm::Type* result_llvm_type = convert_type(expr->result_type);
    if (size_val->getType() != result_llvm_type) {
        size_val = builder.CreateIntCast(size_val, result_llvm_type, false, "sizeof_cast");
    }
    return size_val;
}

llvm::Value* ASTToLLVM::convert_alignof_expr(AlignOfExpr *expr) {
    auto target_type = expr->type_operand;
    if (!target_type) {
        error("convert_alignof_expr(): No target type", expr->location);
        return nullptr;
    }
    uint64_t alignment = 0;

    if (expr->expr_operand) {
        Expr* raw = expr->expr_operand.get();
        while (auto* cast = dyn_cast<ImplicitCast>(raw)) {
            raw = cast->expr.get();
        }
        if (auto* vref = dyn_cast<VarRef>(raw)) {
            if (vref->symref) {
                if (vref->symref->kind == SymbolKind::FUNCTION) {
                    std::string fn_name = get_function_llvm_name(vref->symref, vref->get_name());
                    if (llvm::Function* fn = module->getFunction(fn_name)) {
                        if (auto fn_align = fn->getAlign()) {
                            alignment = fn_align->value();
                        }
                    }
                } else if (vref->symref->kind == SymbolKind::VARIABLE) {
                    const auto* aligned_attr = vref->symref->sym_attrs.find(AttributeKind::ALIGNED);
                    if (aligned_attr && !aligned_attr->args.empty() &&
                        aligned_attr->args[0].kind == AttributeArg::Kind::INTEGER &&
                        aligned_attr->args[0].int_value > 0) {
                        alignment = static_cast<uint64_t>(aligned_attr->args[0].int_value);
                    }
                }
            }
        }
    }

    if (alignment == 0) {
        alignment = semantic_type_alignment(target_type.get_shared());
    }
    if (alignment == 0) {
        llvm::Type* llvm_type = convert_type(target_type);
        alignment = module->getDataLayout().getABITypeAlign(llvm_type).value();
    }

    llvm::Type* result_llvm_type = convert_type(expr->result_type);
    return llvm::ConstantInt::get(result_llvm_type, alignment, false);
}

llvm::Value* ASTToLLVM::convert_offsetof_expr(OffsetOfExpr *expr) {
    if (expr->computed_offset < 0) {
        error("convert_offsetof_expr(): offset not computed", expr->location);
        return nullptr;
    }
    llvm::Type* result_llvm_type = convert_type(expr->result_type);
    return llvm::ConstantInt::get(result_llvm_type, expr->computed_offset, false);
}

llvm::Value* ASTToLLVM::convert_compound_literal(CompoundLiteralExpr *expr) {
    // Compound literals create an unnamed object with a specified type and initializer.
    // The result is an lvalue (address of the object).
    // Storage duration depends on context:
    // - File scope: static storage (global variable)
    // - Block scope: automatic storage (alloca)

    llvm::Type* varType = convert_type(expr->type);
    if (!varType) {
        error("convert_compound_literal(): Cannot convert type", expr->location);
        return nullptr;
    }

    llvm::Value* initVal = nullptr;
    InitListExpr* initListExpr = nullptr;
    if (expr->init) {
        if (auto* initList = dyn_cast<InitListExpr>(expr->init.get())) {
            initListExpr = initList;
            if (expr->has_static_storage) {
                initVal = convert_init_list(initList, varType);
            }
        } else {
            initVal = convert_expression(expr->init.get());
        }
    }

    if (expr->has_static_storage) {
        // File scope: create a global variable with internal linkage
        llvm::Constant* initConst = nullptr;
        if (initVal) {
            initConst = llvm::dyn_cast<llvm::Constant>(initVal);
            if (!initConst) {
                error("convert_compound_literal(): File-scope compound literal requires constant initializer",
                      expr->location);
                return nullptr;
            }
        } else {
            initConst = llvm::Constant::getNullValue(varType);
        }

        // Create a unique name for the compound literal
        static int compound_literal_counter = 0;
        std::string name = ".compoundlit." + std::to_string(compound_literal_counter++);

        auto* gVar = new llvm::GlobalVariable(
            *module,
            varType,
            false,  // not constant (compound literals are modifiable)
            llvm::GlobalValue::InternalLinkage,
            initConst,
            name
        );

        return gVar;
    } else {
        // Block scope: create an alloca
        llvm::Function* function = builder.GetInsertBlock()->getParent();
        llvm::IRBuilder<> tmpBuilder(&function->getEntryBlock(), function->getEntryBlock().begin());

        // Create a unique name for the compound literal
        static int compound_literal_local_counter = 0;
        std::string name = "compoundlit." + std::to_string(compound_literal_local_counter++);

        llvm::AllocaInst* alloca = tmpBuilder.CreateAlloca(varType, nullptr, name);

        // Store the initializer
        if (initListExpr) {
            if (canonical_type_kind(expr->type, ast_ctx.get()) == TypeKind::Vector) {
                if (auto* vec_const = convert_init_list(initListExpr, varType)) {
                    builder.CreateStore(vec_const, alloca);
                } else {
                    emit_init_list_store(initListExpr, alloca, expr->type.get_shared(),
                                         expr->type.is_volatile(), expr->type.is_atomic());
                }
            } else {
                emit_init_list_store(initListExpr, alloca, expr->type.get_shared(),
                                     expr->type.is_volatile(), expr->type.is_atomic());
            }
        } else if (initVal) {
            builder.CreateStore(initVal, alloca);
        }

        return alloca;
    }
}

// ============ Variadic Function Support ============

llvm::Value* ASTToLLVM::convert_va_arg_expr(VaArgExpr *expr) {
    // va_arg(ap, type) - get the next argument from va_list
    auto [va_list_ptr, va_list_ctype] = get_lvalue(expr->va_list_expr.get());
    if (!va_list_ptr) {
        error("convert_va_arg_expr(): Cannot get va_list lvalue", expr->location);
        return nullptr;
    }
    llvm::Type* arg_type = convert_type(expr->arg_type);
    if (!arg_type) {
        error("convert_va_arg_expr(): Failed to convert argument type", expr->location);
        return nullptr;
    }

    // On targets where va_list is a plain byte pointer (e.g. Apple ARM64),
    // lower va_arg manually. LLVM's va_arg instruction can crash for aggregates
    // in AArch64 backend lowering.
    if (target && target->va_list_kind == VaListKind::CHAR_PTR) {
        auto& dl = module->getDataLayout();
        size_t arg_size = dl.getTypeAllocSize(arg_type);
        size_t arg_align = dl.getABITypeAlign(arg_type).value();
        bool indirect_aggregate = arg_type->isAggregateType() && arg_size > 16;

        size_t slot_align = indirect_aggregate ? 8 : (arg_align < 8 ? 8 : arg_align);
        size_t slot_size = indirect_aggregate ? 8 : ((arg_size + 7) / 8) * 8;
        if (!indirect_aggregate && slot_size == 0) {
            // A zero-sized aggregate still consumes one vararg slot.
            slot_size = 8;
        }

        llvm::Type* ptr_ty = llvm::PointerType::get(*context, 0);
        llvm::Type* i64_ty = llvm::Type::getInt64Ty(*context);

        llvm::Value* current_ptr = builder.CreateLoad(ptr_ty, va_list_ptr, "va_cur");
        llvm::Value* current_i64 = builder.CreatePtrToInt(current_ptr, i64_ty, "va_cur_i");

        uint64_t align_mask = static_cast<uint64_t>(slot_align - 1);
        llvm::Value* aligned_i64 = current_i64;
        if (align_mask != 0) {
            llvm::Value* plus = builder.CreateAdd(
                current_i64, llvm::ConstantInt::get(i64_ty, align_mask), "va_align_add");
            llvm::Value* mask = llvm::ConstantInt::get(i64_ty, ~align_mask);
            aligned_i64 = builder.CreateAnd(plus, mask, "va_aligned_i");
        }

        llvm::Value* aligned_ptr = builder.CreateIntToPtr(aligned_i64, ptr_ty, "va_aligned_ptr");
        llvm::Value* next_i64 = builder.CreateAdd(
            aligned_i64, llvm::ConstantInt::get(i64_ty, slot_size), "va_next_i");
        llvm::Value* next_ptr = builder.CreateIntToPtr(next_i64, ptr_ty, "va_next_ptr");
        builder.CreateStore(next_ptr, va_list_ptr);

        if (indirect_aggregate) {
            llvm::Value* indirect_ptr = builder.CreateLoad(ptr_ty, aligned_ptr, "va_indirect_ptr");
            auto* load = builder.CreateLoad(arg_type, indirect_ptr, "va_arg");
            if (arg_align > 0) {
                load->setAlignment(llvm::Align(arg_align));
            }
            return load;
        }

        auto* load = builder.CreateLoad(arg_type, aligned_ptr, "va_arg");
        if (arg_align > 0) {
            load->setAlignment(llvm::Align(arg_align));
        }
        return load;
    }

    return builder.CreateVAArg(va_list_ptr, arg_type, "va_arg");
}

llvm::Value* ASTToLLVM::convert_va_start_expr(VaStartExpr *expr) {
    // va_start(ap, last_named) - initialize va_list
    // Uses llvm.va_start intrinsic which takes a i8* (pointer to va_list)
    auto [va_list_ptr, va_list_ctype] = get_lvalue(expr->va_list_expr.get());
    if (!va_list_ptr) {
        error("convert_va_start_expr(): Cannot get va_list lvalue", expr->location);
        return nullptr;
    }
    llvm::Function* va_start_fn = llvm::Intrinsic::getDeclaration(
        module.get(), llvm::Intrinsic::vastart);
    return builder.CreateCall(va_start_fn, {va_list_ptr});
}

llvm::Value* ASTToLLVM::convert_va_end_expr(VaEndExpr *expr) {
    // va_end(ap) - cleanup va_list
    // Uses llvm.va_end intrinsic which takes a i8* (pointer to va_list)
    auto [va_list_ptr, va_list_ctype] = get_lvalue(expr->va_list_expr.get());
    if (!va_list_ptr) {
        error("convert_va_end_expr(): Cannot get va_list lvalue", expr->location);
        return nullptr;
    }
    llvm::Function* va_end_fn = llvm::Intrinsic::getDeclaration(
        module.get(), llvm::Intrinsic::vaend);
    return builder.CreateCall(va_end_fn, {va_list_ptr});
}

llvm::Value* ASTToLLVM::convert_va_copy_expr(VaCopyExpr *expr) {
    // va_copy(dest, src) - copy va_list state
    // Uses llvm.va_copy intrinsic which takes two i8* (pointers to va_lists)
    auto [dest_ptr, dest_ctype] = get_lvalue(expr->dest.get());
    if (!dest_ptr) {
        error("convert_va_copy_expr(): Cannot get dest va_list lvalue", expr->location);
        return nullptr;
    }
    auto [src_ptr, src_ctype] = get_lvalue(expr->src.get());
    if (!src_ptr) {
        error("convert_va_copy_expr(): Cannot get src va_list lvalue", expr->location);
        return nullptr;
    }
    llvm::Function* va_copy_fn = llvm::Intrinsic::getDeclaration(
        module.get(), llvm::Intrinsic::vacopy);
    return builder.CreateCall(va_copy_fn, {dest_ptr, src_ptr});
}

// ============ Bitfield Support ============

llvm::Value* ASTToLLVM::get_bitfield_storage_ptr(MemberExpr* member, llvm::Value* base_ptr, const BitfieldInfo* bf) {
    // Get the byte offset of the storage unit from the ObjectType::Field
    // We need to find the field in the record type to get its byte offset

    std::shared_ptr<ObjectType> record_type = nullptr;

    if (member->isArrow) {
        // Arrow: base is pointer to struct
        auto base_type = desugar_type(member->base->get_type(), ast_ctx.get());
        auto ptr_type = base_type.as_shared<PointerType>();
        if (ptr_type) {
            record_type = desugar_type(ptr_type->pointed_type, ast_ctx.get())
                              .as_shared<ObjectType>();
        }
    } else {
        // Dot: base is struct
        record_type = desugar_type(member->base->get_type(), ast_ctx.get())
                          .as_shared<ObjectType>();
    }

    if (!record_type) {
        error("get_bitfield_storage_ptr(): Cannot determine struct type", member->location);
        return nullptr;
    }

    llvm::Value* storage_base_ptr = base_ptr;
    std::shared_ptr<ObjectType> storage_record_type = record_type;
    if (!resolve_member_access_base_subobject(
            *this,
            member,
            base_ptr,
            record_type,
            storage_base_ptr,
            storage_record_type)) {
        return nullptr;
    }

    if (bf->storage_size == 0 || (bf->storage_size % 8) != 0) {
        error("get_bitfield_storage_ptr(): Invalid storage size", member->location);
        return nullptr;
    }

    // Calculate pointer to the byte start of the storage window:
    // 1. Cast base_ptr to i8*
    // 2. GEP by field.offset bytes
    llvm::Type* i8_type = llvm::Type::getInt8Ty(*context);

    // GEP to the byte offset
    llvm::Value* byte_offset = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*context), member->byte_offset);
    llvm::Value* storage_ptr = builder.CreateGEP(
        i8_type,
        storage_base_ptr,
        byte_offset,
        "bitfield_storage_ptr");

    return storage_ptr;
}

llvm::Value* ASTToLLVM::extract_bitfield(llvm::Value* storage_ptr, uint32_t storage_size,
                                          uint32_t bit_offset, uint32_t bit_width, bool is_signed) {
    if (storage_size == 0 || bit_width == 0 || bit_width > storage_size) {
        return nullptr;
    }
    llvm::Type* storage_type = llvm::IntegerType::get(*context, storage_size);

    llvm::Value* storage_val = builder.CreateAlignedLoad(
        storage_type, storage_ptr, llvm::Align(1), "bitfield_storage");

    // Shift right by bit_offset to position the bitfield at the LSB
    if (bit_offset > 0) {
        llvm::Value* shift_amount = llvm::ConstantInt::get(storage_type, bit_offset);
        storage_val = builder.CreateLShr(storage_val, shift_amount, "bitfield_shifted");
    }

    // Mask to extract only bit_width bits
    if (bit_width < storage_size) {
        llvm::APInt mask = llvm::APInt::getLowBitsSet(storage_size, bit_width);
        llvm::Value* mask_val = llvm::ConstantInt::get(storage_type, mask);
        storage_val = builder.CreateAnd(storage_val, mask_val, "bitfield_masked");
    }

    // Sign-extend or zero-extend to the declared type width
    // For signed bitfields, we need to sign-extend from bit_width
    if (is_signed && bit_width < storage_size) {
        // Use the sign bit of the bitfield to extend
        // shift left to move sign bit to MSB, then arithmetic shift right
        uint32_t shift_amt = storage_size - bit_width;
        llvm::Value* shift_val = llvm::ConstantInt::get(storage_type, shift_amt);
        storage_val = builder.CreateShl(storage_val, shift_val, "bitfield_shl");
        storage_val = builder.CreateAShr(storage_val, shift_val, "bitfield_sext");
    }

    return storage_val;
}

void ASTToLLVM::store_bitfield(llvm::Value* storage_ptr, uint32_t storage_size,
                                uint32_t bit_offset, uint32_t bit_width, llvm::Value* value) {
    if (storage_size == 0 || bit_width == 0 || bit_width > storage_size) {
        return;
    }
    llvm::Type* storage_type = llvm::IntegerType::get(*context, storage_size);

    // Truncate/extend value to storage unit size
    llvm::Value* new_val = value;
    if (value->getType()->getIntegerBitWidth() != storage_size) {
        new_val = builder.CreateZExtOrTrunc(value, storage_type, "bitfield_val_sized");
    }

    if (bit_width == storage_size && bit_offset == 0) {
        builder.CreateAlignedStore(new_val, storage_ptr, llvm::Align(1));
        return;
    }

    // Mask the value to bit_width bits (truncate if larger)
    llvm::APInt value_mask = llvm::APInt::getLowBitsSet(storage_size, bit_width);
    new_val = builder.CreateAnd(
        new_val, llvm::ConstantInt::get(storage_type, value_mask), "bitfield_val_masked");

    // Shift value to correct position
    if (bit_offset > 0) {
        llvm::Value* shift_amount = llvm::ConstantInt::get(storage_type, bit_offset);
        new_val = builder.CreateShl(new_val, shift_amount, "bitfield_val_shifted");
    }

    // Load current storage unit value
    llvm::Value* old_storage = builder.CreateAlignedLoad(
        storage_type, storage_ptr, llvm::Align(1), "bitfield_old_storage");

    // Create mask to clear the bitfield bits: ~(((1 << bit_width) - 1) << bit_offset)
    llvm::APInt clear_mask = ~(value_mask << bit_offset);
    llvm::Value* cleared = builder.CreateAnd(old_storage,
        llvm::ConstantInt::get(storage_type, clear_mask), "bitfield_cleared");

    // OR in the new value
    llvm::Value* new_storage = builder.CreateOr(cleared, new_val, "bitfield_new_storage");

    // Store the updated storage unit
    builder.CreateAlignedStore(new_storage, storage_ptr, llvm::Align(1));
}
