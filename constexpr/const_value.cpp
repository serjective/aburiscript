#include "const_value.h"

#include "../numeric/floating_point.h"

#include <limits>
#include <sstream>

namespace {
using uint128_t = unsigned __int128;

uint16_t normalize_width(uint16_t width) {
    return ConstIntValue::normalized_width(width);
}

uint128_t width_mask(uint16_t width) {
    return ConstIntValue::width_mask(width);
}

ConstIntValue make_int_from_bits(uint128_t bits, uint16_t width, bool is_unsigned) {
    return ConstIntValue::from_bits128(bits, width, is_unsigned);
}

bool const_object_equals(const std::shared_ptr<ConstObjectValue>& lhs,
                         const std::shared_ptr<ConstObjectValue>& rhs);
bool const_meta_info_equals(const std::shared_ptr<ConstMetaInfoValue>& lhs,
                            const std::shared_ptr<ConstMetaInfoValue>& rhs);
}

bool const_int_value_representable(ConstIntValue value,
                                   uint16_t target_bit_width,
                                   bool target_is_unsigned) {
    target_bit_width = normalize_width(target_bit_width);
    const uint128_t target_unsigned_max = width_mask(target_bit_width);
    const uint128_t target_signed_max =
        (uint128_t{1} << (target_bit_width - 1)) - 1;

    if (value.is_unsigned) {
        uint128_t raw = value.to_unsigned_u128();
        return target_is_unsigned
            ? raw <= target_unsigned_max
            : raw <= target_signed_max;
    }

    __int128 raw = value.to_signed_i128();
    if (target_is_unsigned) {
        return raw >= 0 && static_cast<uint128_t>(raw) <= target_unsigned_max;
    }
    const __int128 signed_max = static_cast<__int128>(target_signed_max);
    const __int128 signed_min = -signed_max - 1;
    return raw >= signed_min && raw <= signed_max;
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
            return int_value.try_as_int64();
        case ConstValueKind::Boolean:
            return bool_value ? 1 : 0;
        case ConstValueKind::Null:
            return null_kind == ConstNullKind::Pointer
                ? std::optional<int64_t>(0)
                : std::nullopt;
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
            return lhs.int_value == rhs.int_value;
        case ConstValueKind::Boolean:
            return lhs.bool_value == rhs.bool_value;
        case ConstValueKind::Floating:
            return lhs.float_value.value == rhs.float_value.value;
        case ConstValueKind::Complex:
            if (lhs.complex_value.has_integer_components !=
                rhs.complex_value.has_integer_components) {
                return false;
            }
            if (lhs.complex_value.has_integer_components) {
                return const_value_equals(
                           ConstValue::integer(lhs.complex_value.integer_real),
                           ConstValue::integer(rhs.complex_value.integer_real)) &&
                       const_value_equals(
                           ConstValue::integer(lhs.complex_value.integer_imag),
                           ConstValue::integer(rhs.complex_value.integer_imag));
            }
            return lhs.complex_value.real == rhs.complex_value.real &&
                   lhs.complex_value.imag == rhs.complex_value.imag;
        case ConstValueKind::Null:
            return lhs.null_kind == rhs.null_kind;
        case ConstValueKind::Address:
            return lhs.address_value.entity == rhs.address_value.entity &&
                   lhs.address_value.allocation_id == rhs.address_value.allocation_id &&
                   lhs.address_value.byte_offset == rhs.address_value.byte_offset;
        case ConstValueKind::MemberPointer:
            return lhs.member_pointer_value.byte_offset ==
                       rhs.member_pointer_value.byte_offset &&
                   lhs.member_pointer_value.method_entity ==
                       rhs.member_pointer_value.method_entity &&
                   lhs.member_pointer_value.virtual_slot_index ==
                       rhs.member_pointer_value.virtual_slot_index &&
                   lhs.member_pointer_value.member_name ==
                       rhs.member_pointer_value.member_name &&
                   lhs.member_pointer_value.is_function_member ==
                       rhs.member_pointer_value.is_function_member;
        case ConstValueKind::Object:
            return const_object_equals(lhs.object_value, rhs.object_value);
        case ConstValueKind::MetaInfo:
            return const_meta_info_equals(lhs.meta_info_value,
                                          rhs.meta_info_value);
        case ConstValueKind::Void:
            return true;
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
    if (lhs->kind != rhs->kind ||
        lhs->active_union_member != rhs->active_union_member ||
        lhs->elements.size() != rhs->elements.size()) {
        return false;
    }
    for (size_t idx = 0; idx < lhs->elements.size(); ++idx) {
        if (!const_value_equals(lhs->elements[idx], rhs->elements[idx])) {
            return false;
        }
    }
    return true;
}

bool const_meta_info_equals(const std::shared_ptr<ConstMetaInfoValue>& lhs,
                            const std::shared_ptr<ConstMetaInfoValue>& rhs) {
    if (lhs == rhs) {
        return true;
    }

    aburi::cir::MetaInfoKind lhs_kind =
        lhs ? lhs->kind : aburi::cir::MetaInfoKind::Null;
    aburi::cir::MetaInfoKind rhs_kind =
        rhs ? rhs->kind : aburi::cir::MetaInfoKind::Null;
    if (lhs_kind != rhs_kind) {
        return false;
    }
    switch (lhs_kind) {
        case aburi::cir::MetaInfoKind::Null:
            return true;
        case aburi::cir::MetaInfoKind::Type:
            return lhs->type == rhs->type;
        case aburi::cir::MetaInfoKind::Entity:
        case aburi::cir::MetaInfoKind::Namespace:
        case aburi::cir::MetaInfoKind::Template:
            return lhs->entity == rhs->entity;
        case aburi::cir::MetaInfoKind::Value:
            return lhs->boxed_type == rhs->boxed_type &&
                   lhs->boxed && rhs->boxed &&
                   const_value_equals(*lhs->boxed, *rhs->boxed);
    }
    return false;
}

std::string const_value_to_string_impl(const ConstValue& value) {
    switch (value.kind) {
        case ConstValueKind::Invalid:
            return "<invalid-const-value>";
        case ConstValueKind::Integer:
            return value.int_value.decimal();
        case ConstValueKind::Boolean:
            return value.bool_value ? "true" : "false";
        case ConstValueKind::Floating:
            return aburi::floating::display(value.float_value.value);
        case ConstValueKind::Complex:
            if (value.complex_value.has_integer_components) {
                return const_value_to_string_impl(
                           ConstValue::integer(
                               value.complex_value.integer_real)) +
                       "+" + const_value_to_string_impl(
                           ConstValue::integer(
                               value.complex_value.integer_imag)) +
                       "i";
            }
            return aburi::floating::display(value.complex_value.real) + "+" +
                   aburi::floating::display(value.complex_value.imag) + "i";
        case ConstValueKind::Null:
            return "nullptr";
        case ConstValueKind::Address:
            return "<address-const-value>";
        case ConstValueKind::MemberPointer:
            if (value.member_pointer_value.member_name &&
                !value.member_pointer_value.member_name->empty()) {
                return "&" + *value.member_pointer_value.member_name;
            }
            return "<member-pointer-const-value>";
        case ConstValueKind::Object:
            break;
        case ConstValueKind::MetaInfo:
            return "<meta-info>";
        case ConstValueKind::Void:
            return "<void-const-value>";
    }

    std::ostringstream out;
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
            out << const_value_to_string_impl(value.object_value->elements[idx]);
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

std::string const_value_to_string(const ConstValue& value) {
    return const_value_to_string_impl(value);
}

ConstIntOpResult const_int_div(ConstIntValue lhs, ConstIntValue rhs) {
    if (rhs.to_unsigned_u128() == 0) {
        return ConstIntOpResult::fail(ConstIntOpError::DivisionByZero);
    }

    if (lhs.is_unsigned) {
        uint128_t q = lhs.to_unsigned_u128() / rhs.to_unsigned_u128();
        return ConstIntOpResult::ok(ConstIntValue::from_unsigned(q, lhs.bit_width));
    }

    __int128 q = lhs.to_signed_i128() / rhs.to_signed_i128();
    return ConstIntOpResult::ok(ConstIntValue::from_signed(q, lhs.bit_width));
}

ConstIntOpResult const_int_mod(ConstIntValue lhs, ConstIntValue rhs) {
    if (rhs.to_unsigned_u128() == 0) {
        return ConstIntOpResult::fail(ConstIntOpError::DivisionByZero);
    }

    if (lhs.is_unsigned) {
        uint128_t r = lhs.to_unsigned_u128() % rhs.to_unsigned_u128();
        return ConstIntOpResult::ok(ConstIntValue::from_unsigned(r, lhs.bit_width));
    }

    __int128 r = lhs.to_signed_i128() % rhs.to_signed_i128();
    return ConstIntOpResult::ok(ConstIntValue::from_signed(r, lhs.bit_width));
}

ConstIntValue const_int_neg(ConstIntValue value) {
    return make_int_from_bits(
        uint128_t{0} - value.to_unsigned_u128(),
        value.bit_width,
        value.is_unsigned);
}

ConstIntValue const_int_add(ConstIntValue lhs, ConstIntValue rhs) {
    return make_int_from_bits(
        lhs.to_unsigned_u128() + rhs.to_unsigned_u128(),
        lhs.bit_width,
        lhs.is_unsigned);
}

ConstIntValue const_int_sub(ConstIntValue lhs, ConstIntValue rhs) {
    return make_int_from_bits(
        lhs.to_unsigned_u128() - rhs.to_unsigned_u128(),
        lhs.bit_width,
        lhs.is_unsigned);
}

ConstIntValue const_int_mul(ConstIntValue lhs, ConstIntValue rhs) {
    return make_int_from_bits(
        lhs.to_unsigned_u128() * rhs.to_unsigned_u128(),
        lhs.bit_width,
        lhs.is_unsigned);
}

ConstIntOpResult const_int_shl(ConstIntValue lhs, ConstIntValue rhs) {
    std::optional<uint64_t> shift = rhs.try_as_uint64();
    if (!shift.has_value() || *shift >= lhs.bit_width) {
        return ConstIntOpResult::fail(ConstIntOpError::InvalidShiftAmount);
    }

    uint128_t shifted = lhs.to_unsigned_u128() << *shift;
    return ConstIntOpResult::ok(make_int_from_bits(
        shifted,
        lhs.bit_width,
        lhs.is_unsigned));
}

ConstIntOpResult const_int_shr(ConstIntValue lhs, ConstIntValue rhs) {
    std::optional<uint64_t> shift = rhs.try_as_uint64();
    if (!shift.has_value() || *shift >= lhs.bit_width) {
        return ConstIntOpResult::fail(ConstIntOpError::InvalidShiftAmount);
    }

    if (lhs.is_unsigned) {
        return ConstIntOpResult::ok(make_int_from_bits(
            lhs.to_unsigned_u128() >> *shift,
            lhs.bit_width,
            true));
    }
    return ConstIntOpResult::ok(make_int_from_bits(
        static_cast<uint128_t>(lhs.to_signed_i128() >> *shift),
        lhs.bit_width,
        false));
}
