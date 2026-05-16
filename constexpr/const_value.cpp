#include "const_value.h"

#include "../ast/symbols.h"
#include "../ast/types.h"

#include <limits>
#include <sstream>

namespace {
uint16_t normalize_width(uint16_t width) {
    if (width == 0) {
        return 1;
    }
    if (width > 64) {
        return 64;
    }
    return width;
}

uint64_t width_mask(uint16_t width) {
    width = normalize_width(width);
    if (width == 64) {
        return std::numeric_limits<uint64_t>::max();
    }
    return (uint64_t(1) << width) - 1;
}

uint64_t sign_extend_u64(uint64_t value, uint16_t width) {
    width = normalize_width(width);
    value &= width_mask(width);
    if (width == 64) {
        return value;
    }
    const uint64_t sign_bit = uint64_t(1) << (width - 1);
    if ((value & sign_bit) == 0) {
        return value;
    }
    return value | ~width_mask(width);
}

ConstIntValue make_int_from_bits(uint64_t bits, uint16_t width, bool is_unsigned) {
    ConstIntValue out;
    out.bit_width = normalize_width(width);
    out.is_unsigned = is_unsigned;
    out.bits = bits & width_mask(out.bit_width);
    return out;
}

bool const_object_equals(const std::shared_ptr<ConstObjectValue>& lhs,
                         const std::shared_ptr<ConstObjectValue>& rhs);
}

ConstIntValue ConstIntValue::from_unsigned(uint64_t value, uint16_t width) {
    ConstIntValue out;
    out.bit_width = normalize_width(width);
    out.is_unsigned = true;
    out.bits = value & width_mask(out.bit_width);
    return out;
}

ConstIntValue ConstIntValue::from_signed(int64_t value, uint16_t width) {
    ConstIntValue out;
    out.bit_width = normalize_width(width);
    out.is_unsigned = false;
    out.bits = static_cast<uint64_t>(value) & width_mask(out.bit_width);
    return out;
}

uint64_t ConstIntValue::to_unsigned_u64() const {
    return bits & width_mask(bit_width);
}

int64_t ConstIntValue::to_signed_i64() const {
    uint64_t extended = sign_extend_u64(bits, bit_width);
    return static_cast<int64_t>(extended);
}

ConstIntValue ConstIntValue::cast(uint16_t new_width, bool new_unsigned) const {
    new_width = normalize_width(new_width);

    ConstIntValue out;
    out.bit_width = new_width;
    out.is_unsigned = new_unsigned;
    uint64_t source_value = is_unsigned
        ? to_unsigned_u64()
        : static_cast<uint64_t>(to_signed_i64());
    out.bits = source_value & width_mask(out.bit_width);
    return out;
}

ConstValue ConstValue::object(ConstObjectValueKind object_kind,
                              std::vector<ConstValue> elements) {
    ConstValue out;
    out.kind = ConstValueKind::Object;
    out.object_value = std::make_shared<ConstObjectValue>();
    out.object_value->kind = object_kind;
    out.object_value->elements = std::move(elements);
    return out;
}

std::optional<int64_t> ConstValue::try_as_int64() const {
    switch (kind) {
        case ConstValueKind::Integer:
            return int_value.to_signed_i64();
        case ConstValueKind::Boolean:
            return bool_value ? 1 : 0;
        case ConstValueKind::NullPointer:
            return 0;
        default:
            return std::nullopt;
    }
}

bool const_value_equals(const ConstValue& lhs, const ConstValue& rhs) {
    if (lhs.kind != rhs.kind) {
        return false;
    }

    switch (lhs.kind) {
        case ConstValueKind::Invalid:
            return true;
        case ConstValueKind::Integer:
            return lhs.int_value.bits == rhs.int_value.bits &&
                   lhs.int_value.bit_width == rhs.int_value.bit_width &&
                   lhs.int_value.is_unsigned == rhs.int_value.is_unsigned;
        case ConstValueKind::Boolean:
            return lhs.bool_value == rhs.bool_value;
        case ConstValueKind::Floating:
            return lhs.float_value.value == rhs.float_value.value &&
                   lhs.float_value.bit_width == rhs.float_value.bit_width;
        case ConstValueKind::NullPointer:
            return true;
        case ConstValueKind::Address:
            return lhs.address_value.symbol.get() == rhs.address_value.symbol.get() &&
                   lhs.address_value.byte_offset == rhs.address_value.byte_offset;
        case ConstValueKind::MemberPointer:
            return lhs.member_pointer_value.byte_offset ==
                       rhs.member_pointer_value.byte_offset &&
                   lhs.member_pointer_value.method_symbol.get() ==
                       rhs.member_pointer_value.method_symbol.get() &&
                   lhs.member_pointer_value.virtual_slot_index ==
                       rhs.member_pointer_value.virtual_slot_index &&
                   lhs.member_pointer_value.member_name ==
                       rhs.member_pointer_value.member_name &&
                   lhs.member_pointer_value.is_function_member ==
                       rhs.member_pointer_value.is_function_member;
        case ConstValueKind::Object:
            return const_object_equals(lhs.object_value, rhs.object_value);
    }
    return false;
}

namespace {
bool const_object_equals(const std::shared_ptr<ConstObjectValue>& lhs,
                         const std::shared_ptr<ConstObjectValue>& rhs) {
    if (lhs == rhs) {
        return true;
    }
    if (!lhs || !rhs) {
        return false;
    }
    if (lhs->kind != rhs->kind || lhs->elements.size() != rhs->elements.size()) {
        return false;
    }
    for (size_t idx = 0; idx < lhs->elements.size(); ++idx) {
        if (!const_value_equals(lhs->elements[idx], rhs->elements[idx])) {
            return false;
        }
    }
    return true;
}

std::string const_value_to_string_impl(const ConstValue& value,
                                       const QualType* value_type) {
    switch (value.kind) {
        case ConstValueKind::Invalid:
            return "<invalid-const-value>";
        case ConstValueKind::Integer:
            return value.int_value.is_unsigned
                ? std::to_string(value.int_value.to_unsigned_u64())
                : std::to_string(value.int_value.to_signed_i64());
        case ConstValueKind::Boolean:
            return value.bool_value ? "true" : "false";
        case ConstValueKind::Floating:
            return std::to_string(static_cast<double>(value.float_value.value));
        case ConstValueKind::NullPointer:
            return "nullptr";
        case ConstValueKind::Address:
            if (value.address_value.symbol &&
                !value.address_value.symbol->name.empty()) {
                return "&" + value.address_value.symbol->name;
            }
            return "<address-const-value>";
        case ConstValueKind::MemberPointer:
            if (value.member_pointer_value.method_symbol &&
                !value.member_pointer_value.method_symbol->name.empty()) {
                return "&" + value.member_pointer_value.method_symbol->name;
            }
            if (value.member_pointer_value.member_name &&
                !value.member_pointer_value.member_name->empty()) {
                return "&" + *value.member_pointer_value.member_name;
            }
            return "<member-pointer-const-value>";
        case ConstValueKind::Object:
            break;
    }

    std::ostringstream out;
    if (value_type && *value_type) {
        out << value_type->to_string();
    }
    if (value.object_value &&
        value.object_value->kind == ConstObjectValueKind::Record) {
        out << "{";
    } else {
        out << "[";
    }
    if (value.object_value) {
        for (size_t idx = 0; idx < value.object_value->elements.size(); ++idx) {
            if (idx > 0) {
                out << ", ";
            }
            out << const_value_to_string_impl(value.object_value->elements[idx], nullptr);
        }
    }
    if (value.object_value &&
        value.object_value->kind == ConstObjectValueKind::Record) {
        out << "}";
    } else {
        out << "]";
    }
    return out.str();
}
} // namespace

std::string const_value_to_string(const ConstValue& value,
                                  const QualType* value_type) {
    return const_value_to_string_impl(value, value_type);
}

ConstIntOpResult const_int_div(ConstIntValue lhs, ConstIntValue rhs) {
    if (rhs.to_unsigned_u64() == 0) {
        return ConstIntOpResult::fail(ConstIntOpError::DivisionByZero);
    }

    if (lhs.is_unsigned) {
        uint64_t q = lhs.to_unsigned_u64() / rhs.to_unsigned_u64();
        return ConstIntOpResult::ok(ConstIntValue::from_unsigned(q, lhs.bit_width));
    }

    int64_t q = lhs.to_signed_i64() / rhs.to_signed_i64();
    return ConstIntOpResult::ok(ConstIntValue::from_signed(q, lhs.bit_width));
}

ConstIntOpResult const_int_mod(ConstIntValue lhs, ConstIntValue rhs) {
    if (rhs.to_unsigned_u64() == 0) {
        return ConstIntOpResult::fail(ConstIntOpError::DivisionByZero);
    }

    if (lhs.is_unsigned) {
        uint64_t r = lhs.to_unsigned_u64() % rhs.to_unsigned_u64();
        return ConstIntOpResult::ok(ConstIntValue::from_unsigned(r, lhs.bit_width));
    }

    int64_t r = lhs.to_signed_i64() % rhs.to_signed_i64();
    return ConstIntOpResult::ok(ConstIntValue::from_signed(r, lhs.bit_width));
}

ConstIntValue const_int_neg(ConstIntValue value) {
    return make_int_from_bits(
        uint64_t(0) - value.to_unsigned_u64(),
        value.bit_width,
        value.is_unsigned);
}

ConstIntValue const_int_add(ConstIntValue lhs, ConstIntValue rhs) {
    return make_int_from_bits(
        lhs.to_unsigned_u64() + rhs.to_unsigned_u64(),
        lhs.bit_width,
        lhs.is_unsigned);
}

ConstIntValue const_int_sub(ConstIntValue lhs, ConstIntValue rhs) {
    return make_int_from_bits(
        lhs.to_unsigned_u64() - rhs.to_unsigned_u64(),
        lhs.bit_width,
        lhs.is_unsigned);
}

ConstIntValue const_int_mul(ConstIntValue lhs, ConstIntValue rhs) {
    return make_int_from_bits(
        lhs.to_unsigned_u64() * rhs.to_unsigned_u64(),
        lhs.bit_width,
        lhs.is_unsigned);
}

ConstIntOpResult const_int_shl(ConstIntValue lhs, ConstIntValue rhs) {
    uint64_t shift = rhs.to_unsigned_u64();
    if (shift >= lhs.bit_width) {
        return ConstIntOpResult::fail(ConstIntOpError::InvalidShiftAmount);
    }

    uint64_t base = lhs.to_unsigned_u64();
    uint64_t shifted = (base << shift);
    return ConstIntOpResult::ok(make_int_from_bits(
        shifted,
        lhs.bit_width,
        lhs.is_unsigned));
}

ConstIntOpResult const_int_shr(ConstIntValue lhs, ConstIntValue rhs) {
    uint64_t shift = rhs.to_unsigned_u64();
    if (shift >= lhs.bit_width) {
        return ConstIntOpResult::fail(ConstIntOpError::InvalidShiftAmount);
    }

    if (lhs.is_unsigned) {
        return ConstIntOpResult::ok(ConstIntValue::from_unsigned(
            lhs.to_unsigned_u64() >> shift,
            lhs.bit_width));
    }
    return ConstIntOpResult::ok(ConstIntValue::from_signed(
        lhs.to_signed_i64() >> shift,
        lhs.bit_width));
}
