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
// Recursively serialize an LLVM constant to a byte buffer (little-endian)
void ASTToLLVM::serialize_constant_to_bytes(llvm::Constant* c, std::vector<uint8_t>& bytes,
                                             size_t offset, size_t bufSize) {
    const llvm::DataLayout& DL = module->getDataLayout();
    if (auto* ci = llvm::dyn_cast<llvm::ConstantInt>(c)) {
        size_t sz = DL.getTypeAllocSize(ci->getType());
        uint64_t val = ci->getZExtValue();
        for (size_t b = 0; b < sz && (offset + b) < bufSize; ++b) {
            bytes[offset + b] = (val >> (b * 8)) & 0xFF;
        }
    } else if (auto* cf = llvm::dyn_cast<llvm::ConstantFP>(c)) {
        llvm::APInt api = cf->getValueAPF().bitcastToAPInt();
        size_t sz = DL.getTypeAllocSize(cf->getType());
        uint64_t val = api.getZExtValue();
        for (size_t b = 0; b < sz && (offset + b) < bufSize; ++b) {
            bytes[offset + b] = (val >> (b * 8)) & 0xFF;
        }
    } else if (auto* cda = llvm::dyn_cast<llvm::ConstantDataArray>(c)) {
        size_t elemSize = DL.getTypeAllocSize(cda->getElementType());
        for (unsigned i = 0; i < cda->getNumElements(); ++i) {
            serialize_constant_to_bytes(cda->getElementAsConstant(i), bytes, offset + i * elemSize, bufSize);
        }
    } else if (auto* ca = llvm::dyn_cast<llvm::ConstantArray>(c)) {
        auto* arrTy = ca->getType();
        size_t elemSize = DL.getTypeAllocSize(arrTy->getElementType());
        for (unsigned i = 0; i < ca->getNumOperands(); ++i) {
            serialize_constant_to_bytes(llvm::cast<llvm::Constant>(ca->getOperand(i)),
                                       bytes, offset + i * elemSize, bufSize);
        }
    } else if (auto* cs = llvm::dyn_cast<llvm::ConstantStruct>(c)) {
        auto* stTy = cs->getType();
        const llvm::StructLayout* sl = DL.getStructLayout(stTy);
        for (unsigned i = 0; i < cs->getNumOperands(); ++i) {
            size_t elemOff = sl->getElementOffset(i);
            serialize_constant_to_bytes(llvm::cast<llvm::Constant>(cs->getOperand(i)),
                                       bytes, offset + elemOff, bufSize);
        }
    } else if (llvm::isa<llvm::ConstantAggregateZero>(c)) {
        // Already zeroed
    } else if (llvm::isa<llvm::ConstantPointerNull>(c)) {
        // Null pointer — already zero
    } else if (auto* ce = llvm::dyn_cast<llvm::ConstantExpr>(c)) {
        // Handle constant expressions like inttoptr, ptrtoint, bitcast
        if (ce->getOpcode() == llvm::Instruction::IntToPtr) {
            // inttoptr: serialize the integer operand as pointer-sized bytes
            if (auto* ci = llvm::dyn_cast<llvm::ConstantInt>(ce->getOperand(0))) {
                size_t ptrSize = DL.getPointerSize();
                uint64_t val = ci->getZExtValue();
                for (size_t b = 0; b < ptrSize && (offset + b) < bufSize; ++b) {
                    bytes[offset + b] = (val >> (b * 8)) & 0xFF;
                }
            }
        } else if (ce->getOpcode() == llvm::Instruction::PtrToInt) {
            // ptrtoint: recurse on the result as an integer
            serialize_constant_to_bytes(llvm::cast<llvm::Constant>(ce->getOperand(0)), bytes, offset, bufSize);
        } else if (ce->getOpcode() == llvm::Instruction::BitCast) {
            serialize_constant_to_bytes(llvm::cast<llvm::Constant>(ce->getOperand(0)), bytes, offset, bufSize);
        }
    }
}

static void collect_pointer_constants_with_offsets(
    llvm::Constant* c,
    const llvm::DataLayout& DL,
    size_t offset,
    std::vector<std::pair<size_t, llvm::Constant*>>& pointer_fields) {
    if (!c) {
        return;
    }

    llvm::Type* ty = c->getType();
    if (ty->isPointerTy()) {
        if (!llvm::isa<llvm::ConstantPointerNull>(c)) {
            pointer_fields.push_back({offset, c});
        }
        return;
    }

    if (auto* cs = llvm::dyn_cast<llvm::ConstantStruct>(c)) {
        const llvm::StructLayout* sl = DL.getStructLayout(cs->getType());
        for (unsigned i = 0; i < cs->getNumOperands(); ++i) {
            auto* op = llvm::dyn_cast<llvm::Constant>(cs->getOperand(i));
            if (!op) continue;
            collect_pointer_constants_with_offsets(
                op, DL, offset + sl->getElementOffset(i), pointer_fields);
        }
        return;
    }

    if (auto* ca = llvm::dyn_cast<llvm::ConstantArray>(c)) {
        auto* arrTy = ca->getType();
        size_t elemSize = DL.getTypeAllocSize(arrTy->getElementType());
        for (unsigned i = 0; i < ca->getNumOperands(); ++i) {
            auto* op = llvm::dyn_cast<llvm::Constant>(ca->getOperand(i));
            if (!op) continue;
            collect_pointer_constants_with_offsets(
                op, DL, offset + i * elemSize, pointer_fields);
        }
        return;
    }

    if (auto* cv = llvm::dyn_cast<llvm::ConstantVector>(c)) {
        auto* vecTy = llvm::cast<llvm::FixedVectorType>(cv->getType());
        size_t elemSize = DL.getTypeAllocSize(vecTy->getElementType());
        for (unsigned i = 0; i < cv->getNumOperands(); ++i) {
            auto* op = llvm::dyn_cast<llvm::Constant>(cv->getOperand(i));
            if (!op) continue;
            collect_pointer_constants_with_offsets(
                op, DL, offset + i * elemSize, pointer_fields);
        }
        return;
    }
}

static llvm::Constant* rebuild_constant_from_serialized_bytes(
    llvm::LLVMContext& context,
    const llvm::DataLayout& DL,
    llvm::Type* ty,
    const std::vector<uint8_t>& bytes,
    size_t offset,
    const std::vector<std::pair<size_t, llvm::Constant*>>& pointer_fields) {
    if (!ty) {
        return nullptr;
    }

    if (ty->isPointerTy()) {
        auto* ptr_ty = llvm::cast<llvm::PointerType>(ty);
        for (const auto& [field_offset, constant] : pointer_fields) {
            if (field_offset != offset || !constant) {
                continue;
            }
            if (constant->getType() == ty) {
                return constant;
            }
            if (constant->getType()->isPointerTy()) {
                return llvm::ConstantExpr::getPointerBitCastOrAddrSpaceCast(
                    constant, ptr_ty);
            }
        }
        unsigned ptr_bits = DL.getPointerSizeInBits(ptr_ty->getAddressSpace());
        auto* int_ty = llvm::IntegerType::get(context, ptr_bits);
        llvm::APInt raw(ptr_bits, 0);
        unsigned byte_width = static_cast<unsigned>(DL.getTypeAllocSize(ty));
        for (unsigned b = 0; b < byte_width && (offset + b) < bytes.size(); ++b) {
            raw |= llvm::APInt(ptr_bits, bytes[offset + b]) << (b * 8);
        }
        if (raw.isZero()) {
            return llvm::ConstantPointerNull::get(ptr_ty);
        }
        return llvm::ConstantExpr::getIntToPtr(
            llvm::ConstantInt::get(int_ty, raw), ptr_ty);
    }

    if (ty->isIntegerTy()) {
        unsigned bit_width = llvm::cast<llvm::IntegerType>(ty)->getBitWidth();
        unsigned byte_width = static_cast<unsigned>(DL.getTypeAllocSize(ty));
        llvm::APInt raw(bit_width, 0);
        for (unsigned b = 0; b < byte_width && (offset + b) < bytes.size(); ++b) {
            raw |= llvm::APInt(bit_width, bytes[offset + b]) << (b * 8);
        }
        return llvm::ConstantInt::get(ty, raw);
    }

    if (ty->isFloatingPointTy()) {
        unsigned byte_width = static_cast<unsigned>(DL.getTypeAllocSize(ty));
        unsigned bit_width = byte_width * 8;
        llvm::APInt raw(bit_width, 0);
        for (unsigned b = 0; b < byte_width && (offset + b) < bytes.size(); ++b) {
            raw |= llvm::APInt(bit_width, bytes[offset + b]) << (b * 8);
        }
        llvm::APFloat value(ty->isFloatTy()
                                ? llvm::APFloat::IEEEsingle()
                                : llvm::APFloat::IEEEdouble(),
                            raw);
        return llvm::ConstantFP::get(context, value);
    }

    if (auto* arr_ty = llvm::dyn_cast<llvm::ArrayType>(ty)) {
        llvm::Type* elem_ty = arr_ty->getElementType();
        size_t elem_size = DL.getTypeAllocSize(elem_ty);
        size_t elem_count = arr_ty->getNumElements();

        if (elem_ty->isIntegerTy(8)) {
            std::vector<uint8_t> arr_bytes(elem_count, 0);
            for (size_t i = 0; i < elem_count && (offset + i) < bytes.size(); ++i) {
                arr_bytes[i] = bytes[offset + i];
            }
            return llvm::ConstantDataArray::get(
                context, llvm::ArrayRef<uint8_t>(arr_bytes.data(), arr_bytes.size()));
        }

        std::vector<llvm::Constant*> elems;
        elems.reserve(elem_count);
        for (size_t i = 0; i < elem_count; ++i) {
            auto* elem = rebuild_constant_from_serialized_bytes(
                context,
                DL,
                elem_ty,
                bytes,
                offset + i * elem_size,
                pointer_fields);
            if (!elem) {
                elem = llvm::Constant::getNullValue(elem_ty);
            }
            elems.push_back(elem);
        }
        return llvm::ConstantArray::get(arr_ty, elems);
    }

    if (auto* struct_ty = llvm::dyn_cast<llvm::StructType>(ty)) {
        const llvm::StructLayout* layout = DL.getStructLayout(struct_ty);
        std::vector<llvm::Constant*> elems;
        elems.reserve(struct_ty->getNumElements());
        for (unsigned i = 0; i < struct_ty->getNumElements(); ++i) {
            llvm::Type* elem_ty = struct_ty->getElementType(i);
            auto* elem = rebuild_constant_from_serialized_bytes(
                context,
                DL,
                elem_ty,
                bytes,
                offset + layout->getElementOffset(i),
                pointer_fields);
            if (!elem) {
                elem = llvm::Constant::getNullValue(elem_ty);
            }
            elems.push_back(elem);
        }
        return llvm::ConstantStruct::get(struct_ty, elems);
    }

    return llvm::Constant::getNullValue(ty);
}

llvm::Constant* ASTToLLVM::convert_init_list(InitListExpr* initList, llvm::Type* type) {
    if (!initList || !type) {
        return nullptr;
    }

    // Prefer constexpr-compatible lowering first so integer/fp casts follow
    // language constant-expression rules before generic fallback casting.
    auto lower_scalar_from_consteval = [&](Expr* expr, llvm::Type* target_type,
                                           bool target_is_unsigned) -> llvm::Constant* {
        if (!expr || !target_type) {
            return nullptr;
        }
        auto* lowered = lower_consteval_to_llvm_constant(
            expr, target_type, target_is_unsigned, ConstEvalMode::c_static_initializer());
        if (!lowered) {
            return nullptr;
        }
        if (lowered->getType() != target_type) {
            bool src_uns = expr->get_type() && expr->get_type()->isUnsigned();
            lowered = fold_constant_cast(
                lowered, target_type, src_uns, target_is_unsigned, module->getDataLayout());
        }
        if (!lowered || lowered->getType() != target_type) {
            return nullptr;
        }
        return lowered;
    };

    if (type->isVectorTy()) {
        auto* vecType = llvm::cast<llvm::FixedVectorType>(type);
        llvm::Type* elemType = vecType->getElementType();
        unsigned numElems = vecType->getNumElements();
        std::vector<llvm::Constant*> elems;
        for (unsigned i = 0; i < numElems; ++i) {
            if (initList->mappings.count(i)) {
                auto& elemExpr = initList->mappings[i];
                if (auto* cst = emit_constant_initializer(elemExpr.get())) {
                    if (cst->getType() != elemType) {
                        bool srcUns = elemExpr->get_type() && elemExpr->get_type()->isUnsigned();
                        cst = fold_constant_cast(cst, elemType, srcUns, false,
                                                 module->getDataLayout());
                    }
                    if (cst) elems.push_back(cst);
                    else {
                        return nullptr;
                    }
                } else {
                    llvm::Value* val = convert_expression(elemExpr.get());
                    if (auto* c = llvm::dyn_cast<llvm::Constant>(val)) {
                        elems.push_back(c);
                    } else {
                        return nullptr;
                    }
                }
            } else {
                elems.push_back(llvm::Constant::getNullValue(elemType));
            }
        }
        return llvm::ConstantVector::get(elems);
    }
    if (type->isArrayTy()) {
        llvm::ArrayType* arrType = llvm::cast<llvm::ArrayType>(type);
        std::vector<llvm::Constant*> elements;
        size_t numElements = arrType->getNumElements();
        llvm::Type* elemType = arrType->getElementType();
        bool array_elem_is_unsigned = false;
        if (auto arr_ctype = initList->type ? initList->type.as_shared<ArrayType>() : nullptr) {
            if (arr_ctype->element_type) {
                array_elem_is_unsigned = arr_ctype->element_type->isUnsigned();
            }
        }

        // Brace-wrapped string literal can initialize the whole array.
        // Example: wchar_t accra[] = {L"aba"};
        if (initList->mappings.size() == 1) {
            auto only_it = initList->mappings.find(0);
            if (only_it != initList->mappings.end()) {
                if (auto* strLit = unwrap_string_literal_expr(only_it->second.get())) {
                    if (auto* arr_const = build_string_literal_array_constant(strLit, numElements);
                        arr_const && arr_const->getType() == arrType) {
                        return arr_const;
                    }
                }
            }
        }

        for (size_t i = 0; i < numElements; ++i) {
            if (initList->mappings.count(i)) {
                auto& expr = initList->mappings[i];
                if (auto* subList = dyn_cast<InitListExpr>(expr.get())) {
                    elements.push_back(convert_init_list(subList, elemType));
                } else if (auto* strLit = unwrap_string_literal_expr(expr.get());
                           strLit && elemType->isArrayTy()) {
                    // String literal initializing an array element
                    // (e.g. char x[][4] = {"Jan", ...}).
                    auto* destArr = llvm::cast<llvm::ArrayType>(elemType);
                    size_t destLen = destArr->getNumElements();
                    auto* arr_const = build_string_literal_array_constant(strLit, destLen);
                    if (!arr_const || arr_const->getType() != destArr) {
                        error("convert_init_list(): string literal array element type mismatch", expr->location);
                        return nullptr;
                    }
                    elements.push_back(arr_const);
                } else {
                    if (auto* lowered = lower_scalar_from_consteval(
                            expr.get(), elemType, array_elem_is_unsigned)) {
                        elements.push_back(lowered);
                    } else if (auto* cst = emit_constant_initializer(expr.get())) {
                        if (cst->getType() != elemType) {
                            bool srcUns = expr->get_type() && expr->get_type()->isUnsigned();
                            cst = fold_constant_cast(cst, elemType, srcUns, array_elem_is_unsigned,
                                                     module->getDataLayout());
                        }
                        if (cst) elements.push_back(cst);
                        else {
                            error("convert_init_list(): Initializer element is not constant", expr->location);
                            return nullptr;
                        }
                    } else {
                        llvm::Value* val = convert_expression(expr.get());
                        if (auto* constant = llvm::dyn_cast<llvm::Constant>(val)) {
                            elements.push_back(constant);
                        } else {
                            error("convert_init_list(): Initializer element is not constant", expr->location);
                            return nullptr;
                        }
                    }
                }
            } else {
                elements.push_back(llvm::Constant::getNullValue(elemType));
            }
        }
        return llvm::ConstantArray::get(arrType, elements);
    } else if (type->isStructTy()) {
        llvm::StructType* structType = llvm::cast<llvm::StructType>(type);

        // Check if this is a union type.
        auto objType = initList->type
            ? desugar_type(initList->type, ast_ctx.get()).as_shared<ObjectType>()
            : nullptr;
        if (objType && objType->is_union) {
            const llvm::DataLayout& DL = module->getDataLayout();
            size_t unionSize = objType->getWidthBytes();
            std::vector<uint8_t> bytes(unionSize, 0);
            std::vector<std::pair<size_t, llvm::Constant*>> pointer_fields;
            llvm::Constant* activeFieldConst = nullptr;
            const auto& obj_fields = objType->semantic_fields();

            size_t init_field_idx = 0;
            bool has_init = false;
            std::shared_ptr<Expr> init_expr;

            // Track one active union field initializer at a time; nested
            // designator paths are folded into synthetic sub InitListExpr nodes.
            auto set_active_initializer = [&](size_t idx, const std::shared_ptr<Expr>& expr) {
                if (!expr || idx >= obj_fields.size()) {
                    return;
                }
                init_field_idx = idx;
                init_expr = expr;
                has_init = true;
            };

            for (const auto& [idx, expr] : initList->mappings) {
                if (idx < obj_fields.size()) {
                    set_active_initializer(idx, expr);
                }
            }

            auto assign_nested_path = [&](const std::shared_ptr<InitListExpr>& root,
                                          const std::vector<size_t>& path,
                                          const std::shared_ptr<Expr>& value,
                                          SrcLoc loc) {
                if (!root || path.empty() || !value) {
                    return;
                }
                InitListExpr* cur = root.get();
                for (size_t depth = 0; depth + 1 < path.size(); ++depth) {
                    size_t idx = path[depth];
                    auto it = cur->mappings.find(idx);
                    if (it == cur->mappings.end() || !isa<InitListExpr>(it->second.get())) {
                        auto next = std::make_shared<InitListExpr>(loc);
                        cur->mappings[idx] = next;
                        cur = next.get();
                    } else {
                        cur = static_cast<InitListExpr*>(it->second.get());
                    }
                }
                cur->mappings[path.back()] = value;
            };

            std::map<size_t, std::shared_ptr<InitListExpr>> nested_union_inits;
            for (const auto& action : initList->actions) {
                for (const auto& path : action.paths) {
                    if (path.empty() || !action.value) {
                        continue;
                    }
                    size_t idx = path[0];
                    if (idx >= obj_fields.size()) {
                        continue;
                    }
                    if (path.size() == 1) {
                        set_active_initializer(idx, action.value);
                        continue;
                    }
                    auto& nested = nested_union_inits[idx];
                    if (!nested) {
                        nested = std::make_shared<InitListExpr>(action.loc);
                        nested->type = obj_fields[idx].type;
                    }
                    std::vector<size_t> subpath(path.begin() + 1, path.end());
                    assign_nested_path(nested, subpath, action.value, action.loc);
                    set_active_initializer(idx, nested);
                }
            }

            if (has_init) {
                auto expr = init_expr;
                const auto& field = obj_fields[init_field_idx];
                auto fieldCType = field.type.get_shared();
                llvm::Type* fieldLLVMType = convert_type(fieldCType);
                bool field_is_unsigned = fieldCType && fieldCType->isUnsigned();

                llvm::Constant* fieldConst = nullptr;
                if (auto* subList = dyn_cast<InitListExpr>(expr.get())) {
                    fieldConst = convert_init_list(subList, fieldLLVMType);
                } else if (auto* strLit = unwrap_string_literal_expr(expr.get());
                           strLit && fieldLLVMType->isArrayTy()) {
                    // String literal initializing an array field in union.
                    auto* destArr = llvm::cast<llvm::ArrayType>(fieldLLVMType);
                    size_t destLen = destArr->getNumElements();
                    fieldConst = build_string_literal_array_constant(strLit, destLen);
                    if (!fieldConst || fieldConst->getType() != destArr) {
                        error("convert_init_list(): union string literal array field type mismatch",
                              expr->location);
                        return nullptr;
                    }
                } else {
                    fieldConst = lower_scalar_from_consteval(
                        expr.get(), fieldLLVMType, field_is_unsigned);
                    if (!fieldConst) {
                        fieldConst = emit_constant_initializer(expr.get());
                    }
                    if (!fieldConst) {
                        llvm::Value* val = convert_expression(expr.get());
                        fieldConst = llvm::dyn_cast<llvm::Constant>(val);
                    }
                }

                if (fieldConst) {
                    activeFieldConst = fieldConst;
                    collect_pointer_constants_with_offsets(fieldConst, DL, 0, pointer_fields);
                    serialize_constant_to_bytes(fieldConst, bytes, 0, unionSize);
                }
            }

            if (structType->getNumElements() == 0) {
                return llvm::ConstantAggregateZero::get(structType);
            }

            std::vector<llvm::Constant*> unionElems;
            unionElems.reserve(structType->getNumElements());

            llvm::Type* storageTy = structType->getElementType(0);
            size_t storageBytes = DL.getTypeAllocSize(storageTy);
            if (activeFieldConst && activeFieldConst->getType() == storageTy) {
                unionElems.push_back(activeFieldConst);
            } else if (storageTy->isStructTy() || storageTy->isArrayTy()) {
                auto* rebuilt = rebuild_constant_from_serialized_bytes(
                    *context, DL, storageTy, bytes, 0, pointer_fields);
                unionElems.push_back(
                    rebuilt ? rebuilt : llvm::Constant::getNullValue(storageTy));
            } else if (storageTy->isPointerTy()) {
                auto* ptrTy = llvm::cast<llvm::PointerType>(storageTy);
                llvm::Constant* storageConst = nullptr;

                for (const auto& [off, cst] : pointer_fields) {
                    if (off != 0 || !cst) {
                        continue;
                    }
                    if (cst->getType() == storageTy) {
                        storageConst = cst;
                    } else if (cst->getType()->isPointerTy()) {
                        storageConst =
                            llvm::ConstantExpr::getPointerBitCastOrAddrSpaceCast(cst, ptrTy);
                    }
                    if (storageConst) {
                        break;
                    }
                }

                if (!storageConst) {
                    size_t ptrBytes = DL.getTypeAllocSize(storageTy);
                    if (ptrBytes > unionSize) {
                        ptrBytes = unionSize;
                    }

                    uint64_t rawVal = 0;
                    size_t copyBytes = ptrBytes;
                    if (copyBytes > sizeof(rawVal)) {
                        copyBytes = sizeof(rawVal);
                    }
                    for (size_t b = 0; b < copyBytes; ++b) {
                        rawVal |= static_cast<uint64_t>(bytes[b]) << (b * 8);
                    }

                    unsigned ptrBits = DL.getPointerSizeInBits(ptrTy->getAddressSpace());
                    auto* intTy = llvm::IntegerType::get(*context, ptrBits);
                    storageConst = llvm::ConstantExpr::getIntToPtr(
                        llvm::ConstantInt::get(intTy, rawVal), ptrTy);
                }

                unionElems.push_back(storageConst);
            } else if (storageTy->isArrayTy()) {
                auto* arrTy = llvm::cast<llvm::ArrayType>(storageTy);
                size_t arrLen = arrTy->getNumElements();
                std::vector<uint8_t> arrBytes(arrLen, 0);
                size_t copyLen = std::min(arrLen, unionSize);
                for (size_t i = 0; i < copyLen; ++i) {
                    arrBytes[i] = bytes[i];
                }
                unionElems.push_back(llvm::ConstantDataArray::get(
                    *context, llvm::ArrayRef<uint8_t>(arrBytes.data(), arrBytes.size())));
            } else if (storageTy->isIntegerTy()) {
                unsigned bitWidth = storageTy->getIntegerBitWidth();
                unsigned byteWidth = bitWidth / 8;
                uint64_t rawVal = 0;
                size_t copyLen = std::min(static_cast<size_t>(byteWidth), unionSize);
                for (size_t b = 0; b < copyLen; ++b) {
                    rawVal |= static_cast<uint64_t>(bytes[b]) << (b * 8);
                }
                unionElems.push_back(llvm::ConstantInt::get(storageTy, rawVal));
            } else {
                unionElems.push_back(llvm::Constant::getNullValue(storageTy));
            }

            size_t bytePos = std::min(storageBytes, unionSize);
            for (unsigned elemIdx = 1; elemIdx < structType->getNumElements(); ++elemIdx) {
                llvm::Type* elemTy = structType->getElementType(elemIdx);
                if (auto* arrTy = llvm::dyn_cast<llvm::ArrayType>(elemTy);
                    arrTy && arrTy->getElementType()->isIntegerTy(8)) {
                    size_t arrLen = arrTy->getNumElements();
                    std::vector<uint8_t> arrBytes(arrLen, 0);
                    size_t copyLen = arrLen;
                    if (bytePos + copyLen > unionSize) {
                        copyLen = unionSize > bytePos ? unionSize - bytePos : 0;
                    }
                    for (size_t i = 0; i < copyLen; ++i) {
                        arrBytes[i] = bytes[bytePos + i];
                    }
                    unionElems.push_back(llvm::ConstantDataArray::get(
                        *context, llvm::ArrayRef<uint8_t>(arrBytes.data(), arrBytes.size())));
                    bytePos += arrLen;
                } else {
                    unionElems.push_back(llvm::Constant::getNullValue(elemTy));
                    bytePos += DL.getTypeAllocSize(elemTy);
                }
            }

            return llvm::ConstantStruct::get(structType, unionElems);
        }

        // Byte-layout structs serialize field constants into a byte buffer.
        if (objType && record_uses_byte_layout(objType.get())) {
            size_t structSize = objType->getWidthBytes();
            std::vector<uint8_t> bytes(structSize, 0);
            std::vector<std::pair<size_t, llvm::Constant*>> pointer_fields;
            const auto& obj_fields = objType->semantic_fields();

            for (const auto& [fieldIdx, expr] : initList->mappings) {
                if (fieldIdx >= obj_fields.size()) continue;
                const auto& field = obj_fields[fieldIdx];

                if (field.is_bitfield) {
                    // Pack bitfield value into the byte buffer.
                    if (field.storage_size == 0 || (field.storage_size % 8) != 0 ||
                        field.bit_width == 0 || field.bit_width > field.storage_size ||
                        (field.bit_offset + field.bit_width) > field.storage_size) {
                        continue;
                    }

                    auto field_ctype = field.type.get_shared();
                    bool field_is_unsigned = field_ctype && field_ctype->isUnsigned();
                    auto* storage_ty = llvm::IntegerType::get(*context, field.storage_size);

                    llvm::Constant* bitfield_const = lower_scalar_from_consteval(
                        expr.get(), storage_ty, field_is_unsigned);
                    if (!bitfield_const) {
                        bitfield_const = emit_constant_initializer(expr.get());
                    }
                    if (!bitfield_const) {
                        llvm::Value* val = convert_expression(expr.get());
                        bitfield_const = llvm::dyn_cast_or_null<llvm::Constant>(val);
                    }
                    if (!bitfield_const) {
                        continue;
                    }

                    if (bitfield_const->getType() != storage_ty) {
                        bool src_uns = expr->get_type() && expr->get_type()->isUnsigned();
                        bitfield_const = fold_constant_cast(
                            bitfield_const,
                            storage_ty,
                            src_uns,
                            field_is_unsigned,
                            module->getDataLayout());
                    }

                    auto* bitfield_int = llvm::dyn_cast_or_null<llvm::ConstantInt>(bitfield_const);
                    if (!bitfield_int) {
                        continue;
                    }

                    llvm::APInt val = bitfield_int->getValue();
                    if (val.getBitWidth() != field.storage_size) {
                        val = field_is_unsigned
                            ? val.zextOrTrunc(field.storage_size)
                            : val.sextOrTrunc(field.storage_size);
                    }

                    llvm::APInt value_mask =
                        llvm::APInt::getLowBitsSet(field.storage_size, field.bit_width);
                    val &= value_mask;

                    // Read the storage unit from the byte buffer.
                    size_t byte_off = field.offset;
                    uint32_t storage_bytes = field.storage_size / 8;
                    llvm::APInt storage_val(field.storage_size, 0);
                    for (uint32_t b = 0; b < storage_bytes && (byte_off + b) < structSize; ++b) {
                        storage_val |=
                            (llvm::APInt(field.storage_size, bytes[byte_off + b]) << (b * 8));
                    }

                    llvm::APInt shifted_val = val << field.bit_offset;
                    llvm::APInt clear_mask = ~(value_mask << field.bit_offset);
                    storage_val = (storage_val & clear_mask) | shifted_val;

                    // Write back the storage unit.
                    for (uint32_t b = 0; b < storage_bytes && (byte_off + b) < structSize; ++b) {
                        bytes[byte_off + b] =
                            static_cast<uint8_t>(storage_val.lshr(b * 8).getZExtValue() & 0xFFu);
                    }
                } else {
                    // Non-bitfield field: serialize to the correct byte offset
                    size_t byte_off = field.offset;
                    auto fieldCType = field.type.get_shared();
                    llvm::Type* fieldTy = convert_type(fieldCType);

                    llvm::Constant* fieldConst = nullptr;
                    if (auto* subList = dyn_cast<InitListExpr>(expr.get())) {
                        fieldConst = convert_init_list(subList, fieldTy);
                    } else if (auto* strLit = unwrap_string_literal_expr(expr.get());
                               strLit && fieldTy->isArrayTy()) {
                        // String literal initializing an array field.
                        auto* destArr = llvm::cast<llvm::ArrayType>(fieldTy);
                        size_t destLen = destArr->getNumElements();
                        fieldConst = build_string_literal_array_constant(strLit, destLen);
                        if (!fieldConst || fieldConst->getType() != destArr) {
                            error("convert_init_list(): struct string literal array field type mismatch",
                                  expr->location);
                            return nullptr;
                        }
                    } else {
                        fieldConst = lower_scalar_from_consteval(
                            expr.get(), fieldTy, field.type.get_shared() &&
                                                 field.type.get_shared()->isUnsigned());
                        if (!fieldConst) fieldConst = emit_constant_initializer(expr.get());
                        if (!fieldConst) {
                            llvm::Value* val = convert_expression(expr.get());
                            fieldConst = llvm::dyn_cast_or_null<llvm::Constant>(val);
                        }
                    }
                    if (fieldConst) {
                        collect_pointer_constants_with_offsets(
                            fieldConst, module->getDataLayout(), byte_off, pointer_fields);
                        serialize_constant_to_bytes(fieldConst, bytes, byte_off, structSize);
                    }
                }
            }

            // Build the LLVM struct constant from the byte buffer
            // The LLVM struct type is either { iA, [N-A x i8] } or { [N x i8] }
            size_t numElements = structType->getNumElements();
            std::vector<llvm::Constant*> elements;
            size_t bytePos = 0;
            for (size_t i = 0; i < numElements; ++i) {
                llvm::Type* elemType = structType->getElementType(i);
                if (elemType->isArrayTy()) {
                    auto* arrType = llvm::cast<llvm::ArrayType>(elemType);
                    size_t arrLen = arrType->getNumElements();
                    llvm::Type* arrElemTy = arrType->getElementType();
                    const llvm::DataLayout& DL = module->getDataLayout();
                    size_t elemSize = DL.getTypeAllocSize(arrElemTy);

                    if (arrElemTy->isIntegerTy() &&
                        llvm::cast<llvm::IntegerType>(arrElemTy)->getBitWidth() == 8) {
                        llvm::ArrayRef<uint8_t> slice(bytes.data() + bytePos, arrLen);
                        elements.push_back(llvm::ConstantDataArray::get(*context, slice));
                        bytePos += arrLen;
                    } else {
                        std::vector<llvm::Constant*> arrElems;
                        arrElems.reserve(arrLen);
                        for (size_t ai = 0; ai < arrLen; ++ai) {
                            size_t elemOff = bytePos + ai * elemSize;
                            if (arrElemTy->isIntegerTy()) {
                                unsigned bitWidth = arrElemTy->getIntegerBitWidth();
                                unsigned byteWidth = bitWidth / 8;
                                uint64_t rawVal = 0;
                                for (unsigned b = 0; b < byteWidth && (elemOff + b) < structSize; ++b) {
                                    rawVal |= static_cast<uint64_t>(bytes[elemOff + b]) << (b * 8);
                                }
                                arrElems.push_back(llvm::ConstantInt::get(arrElemTy, rawVal));
                            } else if (arrElemTy->isFloatingPointTy()) {
                                unsigned byteWidth = DL.getTypeAllocSize(arrElemTy);
                                unsigned bitWidth = byteWidth * 8;
                                llvm::APInt rawBits(bitWidth, 0);
                                for (unsigned b = 0; b < byteWidth && (elemOff + b) < structSize; ++b) {
                                    rawBits |= llvm::APInt(bitWidth, bytes[elemOff + b]) << (b * 8);
                                }
                                llvm::APFloat fpVal(arrElemTy->isFloatTy()
                                    ? llvm::APFloat::IEEEsingle()
                                    : llvm::APFloat::IEEEdouble(),
                                    rawBits);
                                arrElems.push_back(llvm::ConstantFP::get(*context, fpVal));
                            } else if (arrElemTy->isPointerTy()) {
                                llvm::Constant* ptr_const = llvm::ConstantPointerNull::get(
                                    llvm::cast<llvm::PointerType>(arrElemTy));
                                for (const auto& [off, cst] : pointer_fields) {
                                    if (off == elemOff) {
                                        ptr_const = cst;
                                        break;
                                    }
                                }
                                arrElems.push_back(ptr_const);
                            } else {
                                arrElems.push_back(llvm::Constant::getNullValue(arrElemTy));
                            }
                        }
                        elements.push_back(llvm::ConstantArray::get(arrType, arrElems));
                        bytePos += arrLen * elemSize;
                    }
                } else if (elemType->isIntegerTy()) {
                    unsigned bitWidth = elemType->getIntegerBitWidth();
                    unsigned byteWidth = bitWidth / 8;
                    uint64_t rawVal = 0;
                    for (unsigned b = 0; b < byteWidth && (bytePos + b) < structSize; ++b) {
                        rawVal |= static_cast<uint64_t>(bytes[bytePos + b]) << (b * 8);
                    }
                    elements.push_back(llvm::ConstantInt::get(elemType, rawVal));
                    bytePos += byteWidth;
                } else if (elemType->isFloatingPointTy()) {
                    unsigned byteWidth = module->getDataLayout().getTypeAllocSize(elemType);
                    unsigned bitWidth = byteWidth * 8;
                    llvm::APInt rawBits(bitWidth, 0);
                    for (unsigned b = 0; b < byteWidth && (bytePos + b) < structSize; ++b) {
                        rawBits |= llvm::APInt(bitWidth, bytes[bytePos + b]) << (b * 8);
                    }
                    llvm::APFloat fpVal(elemType->isFloatTy()
                        ? llvm::APFloat::IEEEsingle()
                        : llvm::APFloat::IEEEdouble(),
                        rawBits);
                    elements.push_back(llvm::ConstantFP::get(*context, fpVal));
                    bytePos += byteWidth;
                } else if (elemType->isPointerTy()) {
                    llvm::Constant* ptr_const = llvm::ConstantPointerNull::get(
                        llvm::cast<llvm::PointerType>(elemType));
                    for (const auto& [off, cst] : pointer_fields) {
                        if (off == bytePos) {
                            ptr_const = cst;
                            break;
                        }
                    }
                    elements.push_back(ptr_const);
                    bytePos += module->getDataLayout().getTypeAllocSize(elemType);
                } else if (elemType->isStructTy()) {
                    auto* nestedTy = llvm::cast<llvm::StructType>(elemType);
                    const llvm::StructLayout* nestedLayout = module->getDataLayout().getStructLayout(nestedTy);
                    std::vector<llvm::Constant*> nestedElems;
                    nestedElems.reserve(nestedTy->getNumElements());
                    for (size_t ni = 0; ni < nestedTy->getNumElements(); ++ni) {
                        llvm::Type* nestedElemTy = nestedTy->getElementType(ni);
                        size_t nestedOff = bytePos + nestedLayout->getElementOffset(ni);
                        if (nestedElemTy->isIntegerTy()) {
                            unsigned bitWidth = nestedElemTy->getIntegerBitWidth();
                            unsigned byteWidth = bitWidth / 8;
                            uint64_t rawVal = 0;
                            for (unsigned b = 0; b < byteWidth && (nestedOff + b) < structSize; ++b) {
                                rawVal |= static_cast<uint64_t>(bytes[nestedOff + b]) << (b * 8);
                            }
                            nestedElems.push_back(llvm::ConstantInt::get(nestedElemTy, rawVal));
                        } else if (nestedElemTy->isFloatingPointTy()) {
                            unsigned byteWidth = module->getDataLayout().getTypeAllocSize(nestedElemTy);
                            unsigned bitWidth = byteWidth * 8;
                            llvm::APInt rawBits(bitWidth, 0);
                            for (unsigned b = 0; b < byteWidth && (nestedOff + b) < structSize; ++b) {
                                rawBits |= llvm::APInt(bitWidth, bytes[nestedOff + b]) << (b * 8);
                            }
                            llvm::APFloat fpVal(nestedElemTy->isFloatTy()
                                ? llvm::APFloat::IEEEsingle()
                                : llvm::APFloat::IEEEdouble(),
                                rawBits);
                            nestedElems.push_back(llvm::ConstantFP::get(*context, fpVal));
                        } else if (nestedElemTy->isPointerTy()) {
                            llvm::Constant* ptr_const = llvm::ConstantPointerNull::get(
                                llvm::cast<llvm::PointerType>(nestedElemTy));
                            for (const auto& [off, cst] : pointer_fields) {
                                if (off == nestedOff) {
                                    ptr_const = cst;
                                    break;
                                }
                            }
                            nestedElems.push_back(ptr_const);
                        } else {
                            nestedElems.push_back(llvm::Constant::getNullValue(nestedElemTy));
                        }
                    }
                    elements.push_back(llvm::ConstantStruct::get(nestedTy, nestedElems));
                    bytePos += module->getDataLayout().getTypeAllocSize(elemType);
                } else {
                    elements.push_back(llvm::Constant::getNullValue(elemType));
                    bytePos += module->getDataLayout().getTypeAllocSize(elemType);
                }
            }
            return llvm::ConstantStruct::get(structType, elements);
        }

        // Regular struct initialization (no bitfields), with explicit semantic
        // padding slots in LLVM layout.
        std::vector<llvm::Constant*> elements;
        size_t current_offset = 0;

        auto get_union_field_type = [&](size_t i) -> std::shared_ptr<ObjectType> {
            if (!objType || i >= objType->semantic_fields().size()) return nullptr;
            auto fieldType = objType->semantic_fields()[i].type.get_shared();
            auto fieldObj = dyn_cast_shared<ObjectType>(fieldType);
            if (fieldObj && fieldObj->is_union) return fieldObj;
            return nullptr;
        };

        auto recover_field_expr_from_actions = [&](size_t field_idx) -> std::shared_ptr<Expr> {
            auto mapping_it = initList->mappings.find(field_idx);
            if (mapping_it != initList->mappings.end()) {
                return mapping_it->second;
            }

            std::shared_ptr<InitListExpr> recovered_nested;
            std::shared_ptr<Expr> recovered_direct;

            auto assign_nested_path = [&](const std::shared_ptr<InitListExpr>& root,
                                          const std::vector<size_t>& path,
                                          const std::shared_ptr<Expr>& value,
                                          SrcLoc loc) {
                if (!root || path.empty() || !value) {
                    return;
                }
                InitListExpr* cur = root.get();
                for (size_t depth = 0; depth + 1 < path.size(); ++depth) {
                    size_t idx = path[depth];
                    auto it = cur->mappings.find(idx);
                    if (it == cur->mappings.end() || !isa<InitListExpr>(it->second.get())) {
                        auto next = std::make_shared<InitListExpr>(loc);
                        cur->mappings[idx] = next;
                        cur = next.get();
                    } else {
                        cur = static_cast<InitListExpr*>(it->second.get());
                    }
                }
                cur->mappings[path.back()] = value;
            };

            for (const auto& action : initList->actions) {
                for (const auto& path : action.paths) {
                    if (path.empty() || path[0] != field_idx || !action.value) {
                        continue;
                    }
                    if (path.size() == 1) {
                        recovered_direct = action.value;
                        continue;
                    }
                    if (!recovered_nested) {
                        recovered_nested = std::make_shared<InitListExpr>(action.loc);
                        if (objType && field_idx < objType->semantic_fields().size()) {
                            recovered_nested->type = objType->semantic_fields()[field_idx].type;
                        }
                    }
                    std::vector<size_t> subpath(path.begin() + 1, path.end());
                    assign_nested_path(recovered_nested, subpath, action.value, action.loc);
                }
            }

            if (recovered_nested) {
                return recovered_nested;
            }
            return recovered_direct;
        };

        auto build_field_constant = [&](size_t field_idx, llvm::Type* elemType) -> llvm::Constant* {
            auto field_expr = recover_field_expr_from_actions(field_idx);
            if (!field_expr) {
                return llvm::Constant::getNullValue(elemType);
            }
            if (auto* subList = dyn_cast<InitListExpr>(field_expr.get())) {
                return convert_init_list(subList, elemType);
            }
            bool elem_is_complex = false;
            if (objType && field_idx < objType->semantic_fields().size()) {
                auto field_ctype = objType->semantic_fields()[field_idx].type.get_shared();
                elem_is_complex = field_ctype && field_ctype->isComplex();
            } else if (field_expr->get_type()) {
                elem_is_complex = field_expr->get_type()->isComplex();
            }
            if (auto* cst = emit_constant_initializer(field_expr.get())) {
                if (cst->getType() == elemType) {
                    return cst;
                }
            }
            if (elemType->isStructTy() && !elem_is_complex) {
                auto wrapped = std::make_shared<InitListExpr>(field_expr->location);
                if (objType && field_idx < objType->semantic_fields().size()) {
                    wrapped->type = objType->semantic_fields()[field_idx].type;
                }
                wrapped->mappings[0] = field_expr;
                return convert_init_list(wrapped.get(), elemType);
            }
            if (auto* strLit = dyn_cast<StringLiteral>(field_expr.get());
                strLit && elemType->isArrayTy()) {
                auto* destArr = llvm::cast<llvm::ArrayType>(elemType);
                size_t destLen = destArr->getNumElements();
                std::string padded = strLit->value;
                padded.resize(destLen, '\0');
                return llvm::ConstantDataArray::getString(*context, padded, false);
            }
            if (get_union_field_type(field_idx)) {
                auto wrapped = std::make_shared<InitListExpr>(field_expr->location);
                if (objType && field_idx < objType->semantic_fields().size()) {
                    wrapped->type = objType->semantic_fields()[field_idx].type;
                }
                wrapped->mappings[0] = field_expr;
                if (auto* unionConst = convert_init_list(wrapped.get(), elemType)) {
                    return unionConst;
                }
            }

            bool elem_is_unsigned = false;
            if (objType && field_idx < objType->semantic_fields().size()) {
                auto field_ty = objType->semantic_fields()[field_idx].type.get_shared();
                elem_is_unsigned = field_ty && field_ty->isUnsigned();
            } else if (field_expr->get_type()) {
                elem_is_unsigned = field_expr->get_type()->isUnsigned();
            }
            if (auto* lowered = lower_scalar_from_consteval(
                    field_expr.get(), elemType, elem_is_unsigned)) {
                return lowered;
            }
            if (auto* cst = emit_constant_initializer(field_expr.get())) {
                if (cst->getType() != elemType) {
                    bool srcUns = field_expr->get_type() && field_expr->get_type()->isUnsigned();
                    cst = fold_constant_cast(cst, elemType, srcUns, elem_is_unsigned,
                                             module->getDataLayout());
                }
                if (cst && cst->getType() == elemType) return cst;
            }
            llvm::Value* val = convert_expression(field_expr.get());
            if (auto* constant = llvm::dyn_cast<llvm::Constant>(val)) {
                if (constant->getType() == elemType) {
                    return constant;
                }
                if (auto* casted = fold_constant_cast(
                        constant,
                        elemType,
                        field_expr->get_type() && field_expr->get_type()->isUnsigned(),
                        false,
                        module->getDataLayout())) {
                    return casted;
                }
            }
            error("convert_init_list(): Struct initializer element is not constant", field_expr->location);
            return nullptr;
        };

        if (!objType) {
            size_t numElements = structType->getNumElements();
            for (size_t i = 0; i < numElements; ++i) {
                llvm::Type* elemType = structType->getElementType(i);
                llvm::Constant* fieldConst = build_field_constant(i, elemType);
                if (!fieldConst) {
                    return nullptr;
                }
                elements.push_back(fieldConst);
            }
            return llvm::ConstantStruct::get(structType, elements);
        }

        const auto& obj_fields = objType->semantic_fields();
        const llvm::DataLayout& DL = module->getDataLayout();
        for (size_t field_idx = 0; field_idx < obj_fields.size(); ++field_idx) {
            const auto& field = obj_fields[field_idx];
            if (field.offset > current_offset) {
                size_t pad = field.offset - current_offset;
                elements.push_back(llvm::ConstantAggregateZero::get(
                    llvm::ArrayType::get(llvm::Type::getInt8Ty(*context), pad)));
                current_offset += pad;
            }
            llvm::Type* elemType = nullptr;
            size_t llvm_idx =
                map_semantic_field_index_to_llvm_index(objType.get(), field_idx);
            if (llvm_idx < structType->getNumElements()) {
                elemType = structType->getElementType(llvm_idx);
            } else if (field.is_base_subobject || field.storage_size_override > 0) {
                elemType = llvm::ArrayType::get(
                    llvm::Type::getInt8Ty(*context),
                    object_field_storage_size_bytes(field));
            } else {
                elemType = convert_type(field.type.get_shared());
            }
            llvm::Constant* fieldConst = build_field_constant(field_idx, elemType);
            if (!fieldConst) {
                return nullptr;
            }
            elements.push_back(fieldConst);
            current_offset += DL.getTypeAllocSize(elemType);
        }
        size_t total_size = DL.getTypeAllocSize(structType);
        if (total_size < current_offset) {
            total_size = current_offset;
        }
        if (total_size > current_offset) {
            size_t tail = total_size - current_offset;
            elements.push_back(llvm::ConstantAggregateZero::get(
                llvm::ArrayType::get(llvm::Type::getInt8Ty(*context), tail)));
        }
        return llvm::ConstantStruct::get(structType, elements);
    } else {
        // Scalar initialization with braces
        if (initList->mappings.count(0)) {
            auto& expr = initList->mappings[0];
            if (auto* subList = dyn_cast<InitListExpr>(expr.get())) {
                return convert_init_list(subList, type);
            } else {
                if (auto* cst = emit_constant_initializer(expr.get())) {
                    if (cst->getType() != type) {
                        bool srcUns = expr->get_type() && expr->get_type()->isUnsigned();
                        cst = fold_constant_cast(cst, type, srcUns, false,
                                                 module->getDataLayout());
                    }
                    if (cst) return cst;
                }
                llvm::Value* val = convert_expression(expr.get());
                if (auto* constant = llvm::dyn_cast<llvm::Constant>(val)) {
                    return constant;
                } else {
                    error("convert_init_list(): Initializer element is not constant", expr->location);
                    return nullptr;
                }
            }
        }
        return llvm::Constant::getNullValue(type);
    }
}

void ASTToLLVM::emit_init_list_store(InitListExpr* initList, llvm::Value* base_ptr,
                                     std::shared_ptr<CType> type, bool is_volatile, bool is_atomic) {
    if (!initList || !base_ptr || !type) {
        return;
    }
    auto semantic_type = desugar_type(type, ast_ctx.get());
    if (!semantic_type) {
        return;
    }

    const bool is_aggregate =
        semantic_type->kind == TypeKind::Array ||
        semantic_type->kind == TypeKind::Object;

    // Vector init list: build vector with insertelement and store
    if (semantic_type->kind == TypeKind::Vector) {
        auto vt = dyn_cast_shared<VectorType>(semantic_type);
        if (!vt) {
            error("emit_init_list_store(): invalid vector initializer type", initList->location);
            return;
        }
        llvm::Type* llvm_vec = convert_type(vt);
        llvm::Value* vec = llvm::UndefValue::get(llvm_vec);
        // Zero-fill first for elements not explicitly initialized
        vec = llvm::Constant::getNullValue(llvm_vec);
        for (const auto& action : initList->actions) {
            llvm::Value* val = convert_expression(action.value.get());
            if (!val) continue;
            for (const auto& path : action.paths) {
                if (path.size() == 1) {
                    vec = builder.CreateInsertElement(vec, val,
                        builder.getInt32(path[0]), "vec_init");
                }
            }
        }
        builder.CreateStore(vec, base_ptr);
        return;
    }

    struct InitPathInfo {
        llvm::Value* ptr = nullptr;
        std::shared_ptr<CType> type;
        const ObjectType::Field* bitfield = nullptr;
    };

    auto resolve_path = [&](llvm::Value* ptr, std::shared_ptr<CType> cur_type,
                             const std::vector<size_t>& path, SrcLoc loc) -> InitPathInfo {
        InitPathInfo info;
        llvm::Value* cur_ptr = ptr;
        std::shared_ptr<CType> cur = cur_type;
        llvm::Type* i32 = llvm::Type::getInt32Ty(*context);
        for (size_t depth = 0; depth < path.size(); ++depth) {
            size_t idx = path[depth];
            bool last = (depth + 1 == path.size());
            if (!cur) {
                error("emit_init_list_store(): null type in init path", loc);
                return info;
            }
            cur = desugar_type(cur, ast_ctx.get());
            if (cur->kind == TypeKind::Array) {
                auto arr = dyn_cast_shared<ArrayType>(cur);
                if (!arr) {
                    error("emit_init_list_store(): invalid array type in init path", loc);
                    return info;
                }
                llvm::Type* arrTy = convert_type(arr);
                llvm::Value* zero = llvm::ConstantInt::get(i32, 0);
                llvm::Value* index = llvm::ConstantInt::get(i32, static_cast<uint64_t>(idx));
                llvm::Value* indices[] = {zero, index};
                cur_ptr = builder.CreateInBoundsGEP(arrTy, cur_ptr, indices, "init_arr_gep");
                cur = arr->element_type.get_shared();
                continue;
            }
            if (cur->kind == TypeKind::Object) {
                auto record = dyn_cast_shared<ObjectType>(cur);
                if (!record || idx >= record->semantic_fields().size()) {
                    error("emit_init_list_store(): field index out of bounds in init path", loc);
                    return info;
                }
                const auto& field = record->semantic_fields()[idx];
                if (last && field.is_bitfield) {
                    llvm::Type* i8 = llvm::Type::getInt8Ty(*context);
                    llvm::Value* byte_offset =
                        llvm::ConstantInt::get(llvm::Type::getInt64Ty(*context),
                                               static_cast<uint64_t>(field.offset));
                    llvm::Value* storage_ptr =
                        builder.CreateGEP(i8, cur_ptr, byte_offset, "bitfield_storage_ptr");
                    info.ptr = storage_ptr;
                    info.type = field.type.get_shared();
                    info.bitfield = &field;
                    return info;
                }

                if (!record->is_union) {
                    if (record_uses_byte_layout(record.get())) {
                        // Use byte-offset GEP for structs represented as byte-layout
                        llvm::Type* i8 = llvm::Type::getInt8Ty(*context);
                        llvm::Value* byte_off =
                            llvm::ConstantInt::get(llvm::Type::getInt64Ty(*context),
                                                   static_cast<uint64_t>(field.offset));
                        cur_ptr = builder.CreateInBoundsGEP(i8, cur_ptr, byte_off, "init_field_gep");
                    } else {
                        llvm::Type* structTy = convert_type(record);
                        size_t llvm_idx = map_semantic_field_index_to_llvm_index(record.get(), idx);
                        llvm::Value* zero = llvm::ConstantInt::get(i32, 0);
                        llvm::Value* index = llvm::ConstantInt::get(i32, static_cast<uint64_t>(llvm_idx));
                        llvm::Value* indices[] = {zero, index};
                        cur_ptr = builder.CreateInBoundsGEP(structTy, cur_ptr, indices, "init_field_gep");
                    }
                }
                cur = field.type.get_shared();
                continue;
            }
            error("emit_init_list_store(): init path on non-aggregate type", loc);
            return info;
        }
        info.ptr = cur_ptr;
        info.type = cur;
        return info;
    };

    auto store_scalar = [&](const InitPathInfo& info, llvm::Value* value, bool src_unsigned, SrcLoc loc) {
        if (!info.ptr) {
            error("emit_init_list_store(): null destination pointer", loc);
            return;
        }
        if (info.bitfield) {
            store_bitfield(info.ptr, info.bitfield->storage_size,
                          info.bitfield->bit_offset, info.bitfield->bit_width, value);
            return;
        }
        llvm::Type* destType = info.type ? convert_type(info.type) : nullptr;
        llvm::Value* storeVal = value;
        if (destType && value->getType()->isPointerTy() && !destType->isPointerTy()) {
            storeVal = builder.CreateLoad(destType, value, "initlist.load");
        }
        if (destType && storeVal->getType() != destType) {
            storeVal = cast_llvm_type(storeVal, destType, src_unsigned);
        }
        if (!storeVal) {
            error("emit_init_list_store(): failed to convert scalar initializer to destination type", loc);
            return;
        }
        auto* store = builder.CreateStore(storeVal, info.ptr);
        if (is_volatile) {
            store->setVolatile(true);
        }
        if (is_atomic && (storeVal->getType()->isIntegerTy() || storeVal->getType()->isPointerTy())) {
            store->setAtomic(llvm::AtomicOrdering::SequentiallyConsistent);
            store->setAlignment(llvm::Align(module->getDataLayout().getTypeAllocSize(storeVal->getType())));
        }
    };

    auto store_reference_binding =
        [&](const InitPathInfo& info, Expr* init_expr, SrcLoc loc) -> bool {
            auto ref_type =
                dyn_cast_shared<ReferenceType>(
                    desugar_type(info.type, ast_ctx.get()));
            if (!ref_type || !ref_type->referred_type) {
                return false;
            }

            Expr* binding_expr = unwrap_lvalue_to_rvalue_casts(init_expr);

            llvm::Value* bound_addr = get_lvalue(binding_expr).address;
            if (!bound_addr) {
                error("emit_init_list_store(): reference initializer did not produce address",
                      loc);
                return true;
            }

            llvm::Type* dest_type = convert_type(info.type);
            llvm::Value* stored_addr = bound_addr;
            if (dest_type && stored_addr->getType() != dest_type) {
                stored_addr = cast_llvm_type(stored_addr, dest_type, false);
            }
            if (!stored_addr) {
                error("emit_init_list_store(): failed to lower reference initializer",
                      loc);
                return true;
            }

            auto* store = builder.CreateStore(stored_addr, info.ptr);
            if (is_volatile) {
                store->setVolatile(true);
            }
            return true;
        };

    if (!is_aggregate) {
        // Scalar fallback: store the first available initializer
        if (!initList->actions.empty() && initList->actions.front().value) {
            InitPathInfo info;
            info.ptr = base_ptr;
            info.type = semantic_type;
            if (canonical_type_kind(info.type, ast_ctx.get()) ==
                TypeKind::Reference) {
                store_reference_binding(
                    info,
                    initList->actions.front().value.get(),
                    initList->location);
            } else {
                llvm::Value* val =
                    convert_expression(initList->actions.front().value.get());
                if (val) {
                    bool src_unsigned =
                        initList->actions.front().value->get_type() &&
                        initList->actions.front().value->get_type()->isUnsigned();
                    store_scalar(info, val, src_unsigned, initList->location);
                }
            }
        } else if (initList->mappings.count(0) && initList->mappings.at(0)) {
            InitPathInfo info;
            info.ptr = base_ptr;
            info.type = semantic_type;
            if (canonical_type_kind(info.type, ast_ctx.get()) ==
                TypeKind::Reference) {
                store_reference_binding(
                    info,
                    initList->mappings.at(0).get(),
                    initList->location);
            } else {
                llvm::Value* val = convert_expression(initList->mappings.at(0).get());
                if (val) {
                    bool src_unsigned =
                        initList->mappings.at(0)->get_type() &&
                        initList->mappings.at(0)->get_type()->isUnsigned();
                    store_scalar(info, val, src_unsigned, initList->location);
                }
            }
        }
        return;
    }

    llvm::Type* llvmType = convert_type(semantic_type);
    if (!llvmType) {
        return;
    }
    llvm::Constant* zero = llvm::Constant::getNullValue(llvmType);
    auto* zeroStore = builder.CreateStore(zero, base_ptr);
    if (is_volatile) {
        zeroStore->setVolatile(true);
    }
    if (is_atomic && (llvmType->isIntegerTy() || llvmType->isPointerTy())) {
        zeroStore->setAtomic(llvm::AtomicOrdering::SequentiallyConsistent);
        zeroStore->setAlignment(llvm::Align(module->getDataLayout().getTypeAllocSize(llvmType)));
    }

    const std::vector<InitAction>* actions = &initList->actions;
    std::vector<InitAction> fallback_actions;
    if (actions->empty() && !initList->mappings.empty()) {
        fallback_actions.reserve(initList->mappings.size());
        for (const auto& [idx, expr] : initList->mappings) {
            InitAction action;
            action.paths.push_back({idx});
            action.value = expr;
            action.loc = initList->location;
            fallback_actions.push_back(std::move(action));
        }
        actions = &fallback_actions;
    }

    for (const auto& action : *actions) {
        if (action.paths.empty() || !action.value) {
            continue;
        }
        bool is_range = action.paths.size() > 1;
        if (auto* subList = dyn_cast<InitListExpr>(action.value.get())) {
            if (!is_range) {
                InitPathInfo info = resolve_path(base_ptr, semantic_type, action.paths[0], action.loc);
                if (!info.ptr) {
                    return;
                }
                if (info.bitfield) {
                    error("emit_init_list_store(): bitfield initialized with initializer list", action.loc);
                    return;
                }
                emit_init_list_store(subList, info.ptr, info.type, is_volatile, is_atomic);
                continue;
            }

            InitPathInfo info = resolve_path(base_ptr, semantic_type, action.paths[0], action.loc);
            if (!info.ptr || !info.type) {
                return;
            }
            if (info.bitfield) {
                error("emit_init_list_store(): bitfield range initialized with initializer list", action.loc);
                return;
            }
            llvm::Type* elemTy = convert_type(info.type);
            if (!elemTy) return;
            llvm::Function* function = builder.GetInsertBlock()->getParent();
            llvm::IRBuilder<> tmpBuilder(&function->getEntryBlock(), function->getEntryBlock().begin());
            llvm::AllocaInst* tmp = tmpBuilder.CreateAlloca(elemTy, nullptr, "init.range.tmp");
            emit_init_list_store(subList, tmp, info.type, is_volatile, is_atomic);

            uint64_t size_bytes = static_cast<uint64_t>(info.type->getWidthBytes());
            if (size_bytes == 0) {
                continue;
            }
            llvm::Value* sizeVal = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*context), size_bytes);
            llvm::MaybeAlign align = module->getDataLayout().getABITypeAlign(elemTy);

            for (const auto& path : action.paths) {
                InitPathInfo dest = resolve_path(base_ptr, semantic_type, path, action.loc);
                if (!dest.ptr) {
                    return;
                }
                builder.CreateMemCpy(dest.ptr, align, tmp, align, sizeVal);
            }
            continue;
        }

        if (auto* strLit = unwrap_string_literal_expr(action.value.get())) {
            bool all_array_targets = true;
            std::vector<InitPathInfo> dest_infos;
            dest_infos.reserve(action.paths.size());
            for (const auto& path : action.paths) {
                InitPathInfo info = resolve_path(base_ptr, semantic_type, path, action.loc);
                if (!info.ptr) {
                    return;
                }
                if (info.bitfield) {
                    error("emit_init_list_store(): bitfield initialized with string literal", action.loc);
                    return;
                }
                llvm::Type* target_ty = info.type ? convert_type(info.type) : nullptr;
                if (!target_ty || !target_ty->isArrayTy()) {
                    all_array_targets = false;
                    break;
                }
                dest_infos.push_back(info);
            }
            if (all_array_targets) {
                for (const auto& info : dest_infos) {
                    auto* dest_arr_ty = llvm::dyn_cast<llvm::ArrayType>(convert_type(info.type));
                    if (!dest_arr_ty) {
                        error("emit_init_list_store(): expected array type for string literal target",
                              action.loc);
                        return;
                    }
                    size_t dest_len = dest_arr_ty->getNumElements();
                    auto* arr_const = build_string_literal_array_constant(strLit, dest_len);
                    if (!arr_const || arr_const->getType() != dest_arr_ty) {
                        error("emit_init_list_store(): string literal target array type mismatch", action.loc);
                        return;
                    }
                    auto* store = builder.CreateStore(arr_const, info.ptr);
                    if (is_volatile) {
                        store->setVolatile(true);
                    }
                }
                continue;
            }
        }

        if (auto* ctor_init = dyn_cast<CppConstructExpr>(action.value.get())) {
            for (const auto& path : action.paths) {
                InitPathInfo info = resolve_path(base_ptr, semantic_type, path, action.loc);
                if (!info.ptr) {
                    return;
                }
                if (info.bitfield) {
                    error("emit_init_list_store(): bitfield initialized with constructor expression",
                          action.loc);
                    return;
                }
                if (!emit_cpp_construct_call(
                        ctor_init,
                        info.ptr,
                        action.loc,
                        "emit_init_list_store()")) {
                    error("emit_init_list_store(): failed to lower aggregate element constructor",
                          action.loc);
                    return;
                }
            }
            continue;
        }

        llvm::Value* val = nullptr;
        bool lowered_value = false;
        bool src_unsigned =
            action.value->get_type() && action.value->get_type()->isUnsigned();
        for (const auto& path : action.paths) {
            InitPathInfo info = resolve_path(base_ptr, semantic_type, path, action.loc);
            if (!info.ptr) {
                return;
            }
            if (canonical_type_kind(info.type, ast_ctx.get()) ==
                TypeKind::Reference) {
                if (store_reference_binding(info, action.value.get(), action.loc)) {
                    continue;
                }
            }
            if (!lowered_value) {
                val = convert_expression(action.value.get());
                lowered_value = true;
                if (!val) {
                    return;
                }
            }
            store_scalar(info, val, src_unsigned, action.loc);
        }
    }
}
