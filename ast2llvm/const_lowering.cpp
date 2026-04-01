#include "const_lowering.h"

#include "../constexpr/consteval_engine.h"
#include "../constexpr/const_value.h"
#include "../lang_options.h"

#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/APInt.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Type.h"

#include <cmath>
#include <cstdint>
#include <limits>
#include <optional>

namespace {
ConstIntValue make_bool_int(bool value) {
    return ConstIntValue::from_signed(value ? 1 : 0, 64);
}

std::optional<ConstIntValue> try_to_int_like(const ConstValue& value) {
    switch (value.kind) {
        case ConstValueKind::Integer:
            return value.int_value;
        case ConstValueKind::Boolean:
            return make_bool_int(value.bool_value);
        case ConstValueKind::Floating: {
            long double fp = value.float_value.value;
            if (!std::isfinite(fp)) {
                return std::nullopt;
            }
            long double trunc = std::trunc(fp);
            if (trunc < static_cast<long double>(std::numeric_limits<int64_t>::min()) ||
                trunc > static_cast<long double>(std::numeric_limits<int64_t>::max())) {
                return std::nullopt;
            }
            return ConstIntValue::from_signed(static_cast<int64_t>(trunc), 64);
        }
        default:
            return std::nullopt;
    }
}

std::optional<long double> try_to_fp_like(const ConstValue& value) {
    switch (value.kind) {
        case ConstValueKind::Floating:
            return value.float_value.value;
        case ConstValueKind::Boolean:
            return value.bool_value ? 1.0L : 0.0L;
        case ConstValueKind::Integer:
            if (value.int_value.is_unsigned) {
                return static_cast<long double>(value.int_value.to_unsigned_u64());
            }
            return static_cast<long double>(value.int_value.to_signed_i64());
        default:
            return std::nullopt;
    }
}

llvm::Constant* lower_integer_constant(
    const ConstValue& value,
    llvm::Type* target_type,
    bool target_is_unsigned) {
    auto int_like = try_to_int_like(value);
    auto* int_type = llvm::dyn_cast<llvm::IntegerType>(target_type);
    if (!int_like.has_value() || !int_type) {
        return nullptr;
    }

    unsigned target_bits = int_type->getBitWidth();
    if (target_bits == 0) {
        return nullptr;
    }

    if (target_is_unsigned) {
        uint64_t u = int_like->cast(64, true).to_unsigned_u64();
        llvm::APInt ap(target_bits, u, false);
        return llvm::ConstantInt::get(int_type, ap);
    }

    int64_t s = int_like->cast(64, false).to_signed_i64();
    llvm::APInt ap(target_bits, static_cast<uint64_t>(s), true);
    return llvm::ConstantInt::get(int_type, ap);
}

llvm::Constant* lower_floating_constant(const ConstValue& value, llvm::Type* target_type) {
    if (!target_type || !target_type->isFloatingPointTy()) {
        return nullptr;
    }

    auto fp_like = try_to_fp_like(value);
    if (!fp_like.has_value()) {
        return nullptr;
    }

    llvm::APFloat ap(static_cast<double>(*fp_like));
    bool ignored = false;
    const llvm::fltSemantics* semantics = nullptr;
    if (target_type->isHalfTy()) {
        semantics = &llvm::APFloat::IEEEhalf();
    } else if (target_type->isBFloatTy()) {
        semantics = &llvm::APFloat::BFloat();
    } else if (target_type->isFloatTy()) {
        semantics = &llvm::APFloat::IEEEsingle();
    } else if (target_type->isDoubleTy()) {
        semantics = &llvm::APFloat::IEEEdouble();
    } else if (target_type->isX86_FP80Ty()) {
        semantics = &llvm::APFloat::x87DoubleExtended();
    } else if (target_type->isFP128Ty()) {
        semantics = &llvm::APFloat::IEEEquad();
    } else if (target_type->isPPC_FP128Ty()) {
        semantics = &llvm::APFloat::PPCDoubleDouble();
    }
    if (!semantics) {
        return nullptr;
    }
    ap.convert(*semantics, llvm::APFloat::rmNearestTiesToEven, &ignored);
    return llvm::ConstantFP::get(target_type->getContext(), ap);
}

llvm::Constant* lower_pointer_constant(const ConstValue& value, llvm::Type* target_type) {
    auto* ptr_type = llvm::dyn_cast<llvm::PointerType>(target_type);
    if (!ptr_type) {
        return nullptr;
    }

    if (value.kind == ConstValueKind::NullPointer) {
        return llvm::ConstantPointerNull::get(ptr_type);
    }

    auto int_like = try_to_int_like(value);
    if (!int_like.has_value()) {
        return nullptr;
    }

    if (int_like->cast(64, true).to_unsigned_u64() == 0) {
        return llvm::ConstantPointerNull::get(ptr_type);
    }

    // Keep non-zero integer-to-pointer lowering on the existing codegen path
    // until pointer-sized constant semantics are fully unified.
    return nullptr;
}

llvm::Constant* lower_value_constant(const ConstValue& value,
                                     llvm::Type* target_type,
                                     bool target_is_unsigned);

llvm::Constant* lower_array_constant(const ConstValue& value, llvm::Type* target_type) {
    auto* array_type = llvm::dyn_cast<llvm::ArrayType>(target_type);
    if (!array_type ||
        value.kind != ConstValueKind::Object ||
        !value.object_value ||
        value.object_value->kind != ConstObjectValueKind::Array ||
        value.object_value->elements.size() != array_type->getNumElements()) {
        return nullptr;
    }

    std::vector<llvm::Constant*> elements;
    elements.reserve(value.object_value->elements.size());
    llvm::Type* element_type = array_type->getElementType();
    for (const auto& element : value.object_value->elements) {
        llvm::Constant* lowered = lower_value_constant(
            element,
            element_type,
            element.kind == ConstValueKind::Integer && element.int_value.is_unsigned);
        if (!lowered) {
            return nullptr;
        }
        elements.push_back(lowered);
    }
    return llvm::ConstantArray::get(array_type, elements);
}

llvm::Constant* lower_struct_constant(const ConstValue& value, llvm::Type* target_type) {
    auto* struct_type = llvm::dyn_cast<llvm::StructType>(target_type);
    if (!struct_type ||
        value.kind != ConstValueKind::Object ||
        !value.object_value ||
        value.object_value->kind != ConstObjectValueKind::Record ||
        value.object_value->elements.size() != struct_type->getNumElements()) {
        return nullptr;
    }

    std::vector<llvm::Constant*> elements;
    elements.reserve(value.object_value->elements.size());
    for (size_t index = 0; index < value.object_value->elements.size(); ++index) {
        const auto& element = value.object_value->elements[index];
        llvm::Type* field_type = struct_type->getElementType(static_cast<unsigned>(index));
        llvm::Constant* lowered = lower_value_constant(
            element,
            field_type,
            element.kind == ConstValueKind::Integer && element.int_value.is_unsigned);
        if (!lowered) {
            return nullptr;
        }
        elements.push_back(lowered);
    }
    return llvm::ConstantStruct::get(struct_type, elements);
}

llvm::Constant* lower_value_constant(const ConstValue& value,
                                     llvm::Type* target_type,
                                     bool target_is_unsigned) {
    if (!target_type) {
        return nullptr;
    }

    if (target_type->isIntegerTy()) {
        return lower_integer_constant(value, target_type, target_is_unsigned);
    }
    if (target_type->isFloatingPointTy()) {
        return lower_floating_constant(value, target_type);
    }
    if (target_type->isPointerTy()) {
        return lower_pointer_constant(value, target_type);
    }
    if (target_type->isArrayTy()) {
        return lower_array_constant(value, target_type);
    }
    if (target_type->isStructTy()) {
        return lower_struct_constant(value, target_type);
    }

    return nullptr;
}
}

llvm::Constant* lower_consteval_to_llvm_constant(
    Expr* expr,
    llvm::Type* target_type,
    bool target_is_unsigned,
    ConstEvalMode mode) {
    if (!expr || !target_type) {
        return nullptr;
    }

    LangOptions options;
    options.enable_consteval_engine = true;
    options.enable_consteval_function_interpreter = true;
    ConstEvalEngine engine(options);
    ConstEvalResult eval_result = engine.evaluate(expr, mode);
    if (eval_result.status != ConstEvalStatus::Constant || !eval_result.value.has_value()) {
        return nullptr;
    }

    const ConstValue& value = eval_result.value.value();
    return lower_value_constant(value, target_type, target_is_unsigned);
}
