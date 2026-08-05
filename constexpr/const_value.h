#ifndef ABURI_CONST_VALUE_H
#define ABURI_CONST_VALUE_H

#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <vector>

#include "../cir/ids.h"
#include "../cir/type.h"
#include "../numeric/integer_value.h"

enum class ConstValueKind {
    Invalid,
    Integer,
    Boolean,
    Floating,
    Complex,
    Null,
    Address,
    MemberPointer,
    Object,
    MetaInfo,
    Void,
};

enum class ConstNullKind {
    None,
    Nullptr,
    Pointer,
    MemberPointer,
};

using ConstIntValue = aburi::numeric::IntegerValue;

struct ConstFloatValue {
    aburi::cir::FloatingValue value;
};

struct ConstComplexValue {
    aburi::cir::FloatingValue real;
    aburi::cir::FloatingValue imag;
    ConstIntValue integer_real{};
    ConstIntValue integer_imag{};
    bool has_integer_components = false;

    bool valid() const {
        if (has_integer_components) {
            return integer_real.bit_width == integer_imag.bit_width &&
                   integer_real.is_unsigned == integer_imag.is_unsigned;
        }
        return real.valid() && imag.valid() &&
               real.semantics == imag.semantics;
    }
};

struct ConstSubobjectPathEntry {
    aburi::cir::EntityId entity{};
    uint64_t array_index = 0;
    bool is_array_element = false;
    int64_t containing_object_offset = 0;
};

struct ConstAddressValue {
    aburi::cir::EntityId entity{};
    uint64_t allocation_id = 0;
    int64_t byte_offset = 0;
    aburi::cir::InstId string_literal{};
    std::vector<ConstSubobjectPathEntry> subobjects;
    aburi::cir::EntityId bitfield_entity{};
    uint32_t bit_offset = 0;
    uint32_t bit_width = 0;
    uint32_t bit_storage_bits = 0;
    int64_t containing_object_offset = 0;

    bool same_base(const ConstAddressValue& other) const {
        if (entity != other.entity || string_literal != other.string_literal) {
            return false;
        }
        if (allocation_id == other.allocation_id) {
            return true;
        }

        return entity.valid() &&
               (allocation_id == 0 || other.allocation_id == 0);
    }
};

struct ConstMemberPointerValue {
    int64_t byte_offset = 0;
    aburi::cir::EntityId method_entity{};
    int32_t virtual_slot_index = -1;
    const std::string* member_name = nullptr;
    bool is_function_member = false;
};

enum class ConstObjectValueKind : uint8_t {
    Record,
    Array,
};

struct ConstObjectValue;

struct ConstValue;

struct ConstMetaInfoValue {
    aburi::cir::MetaInfoKind kind = aburi::cir::MetaInfoKind::Null;
    aburi::cir::TypeRef type{};
    aburi::cir::EntityId entity{};
    std::shared_ptr<ConstValue> boxed{};
    aburi::cir::TypeRef boxed_type{};
};

struct ConstValue {
    ConstValueKind kind = ConstValueKind::Invalid;
    ConstNullKind null_kind = ConstNullKind::None;
    ConstIntValue int_value{};
    bool bool_value = false;
    ConstFloatValue float_value{};
    ConstComplexValue complex_value{};
    ConstAddressValue address_value{};
    ConstMemberPointerValue member_pointer_value{};
    std::shared_ptr<ConstObjectValue> object_value{};
    std::shared_ptr<ConstMetaInfoValue> meta_info_value{};

    static ConstValue invalid() {
        return {};
    }

    static ConstValue integer(ConstIntValue value) {
        ConstValue out;
        out.kind = ConstValueKind::Integer;
        out.int_value = value;
        return out;
    }

    static ConstValue boolean(bool value) {
        ConstValue out;
        out.kind = ConstValueKind::Boolean;
        out.bool_value = value;
        return out;
    }

    static ConstValue floating(aburi::cir::FloatingValue value) {
        ConstValue out;
        out.kind = ConstValueKind::Floating;
        out.float_value = {value};
        return out;
    }

    static ConstValue complex(aburi::cir::FloatingValue real,
                              aburi::cir::FloatingValue imag) {
        ConstValue out;
        out.kind = ConstValueKind::Complex;
        out.complex_value.real = real;
        out.complex_value.imag = imag;
        return out;
    }

    static ConstValue complex_integer(ConstIntValue real,
                                      ConstIntValue imag) {
        ConstValue out;
        out.kind = ConstValueKind::Complex;
        out.complex_value.integer_real = real;
        out.complex_value.integer_imag = imag;
        out.complex_value.has_integer_components = true;
        return out;
    }

    static ConstValue null_pointer() {
        ConstValue out;
        out.kind = ConstValueKind::Null;
        out.null_kind = ConstNullKind::Pointer;
        return out;
    }

    static ConstValue null_member_pointer() {
        ConstValue out;
        out.kind = ConstValueKind::Null;
        out.null_kind = ConstNullKind::MemberPointer;
        return out;
    }

    static ConstValue nullptr_value() {
        ConstValue out;
        out.kind = ConstValueKind::Null;
        out.null_kind = ConstNullKind::Nullptr;
        return out;
    }

    static ConstValue void_value() {
        ConstValue out;
        out.kind = ConstValueKind::Void;
        return out;
    }

    static ConstValue address_value_of(ConstAddressValue value) {
        ConstValue out;
        out.kind = ConstValueKind::Address;
        out.address_value = value;
        return out;
    }

    static ConstValue address(aburi::cir::EntityId entity,
                              int64_t byte_offset = 0) {
        ConstValue out;
        out.kind = ConstValueKind::Address;
        out.address_value.entity = entity;
        out.address_value.byte_offset = byte_offset;
        return out;
    }

    static ConstValue allocation_address(uint64_t allocation_id,
                                         int64_t byte_offset = 0) {
        ConstValue out;
        out.kind = ConstValueKind::Address;
        out.address_value.allocation_id = allocation_id;
        out.address_value.byte_offset = byte_offset;
        return out;
    }

    static ConstValue member_pointer(int64_t byte_offset,
                                     bool is_function_member,
                                     aburi::cir::EntityId method_entity = {},
                                     int32_t virtual_slot_index = -1,
                                     const std::string* member_name = nullptr) {
        ConstValue out;
        out.kind = ConstValueKind::MemberPointer;
        out.member_pointer_value.byte_offset = byte_offset;
        out.member_pointer_value.method_entity = method_entity;
        out.member_pointer_value.virtual_slot_index = virtual_slot_index;
        out.member_pointer_value.member_name = member_name;
        out.member_pointer_value.is_function_member = is_function_member;
        return out;
    }

    static ConstValue object(ConstObjectValueKind object_kind,
                             std::vector<ConstValue> elements);

    static ConstValue meta_info(ConstMetaInfoValue value) {
        ConstValue out;
        out.kind = ConstValueKind::MetaInfo;
        out.meta_info_value =
            std::make_shared<ConstMetaInfoValue>(std::move(value));
        return out;
    }

    static ConstValue meta_info_null() {
        return meta_info(ConstMetaInfoValue{});
    }

    static ConstValue meta_info_type(aburi::cir::TypeRef type) {
        ConstMetaInfoValue value;
        value.kind = aburi::cir::MetaInfoKind::Type;
        value.type = type;
        return meta_info(std::move(value));
    }

    static ConstValue meta_info_entity(aburi::cir::MetaInfoKind kind,
                                       aburi::cir::EntityId entity) {
        ConstMetaInfoValue value;
        value.kind = kind;
        value.entity = entity;
        return meta_info(std::move(value));
    }

    bool is_null(ConstNullKind flavor) const {
        return kind == ConstValueKind::Null && null_kind == flavor;
    }

    bool is_any_null() const {
        return kind == ConstValueKind::Null &&
               null_kind != ConstNullKind::None;
    }

    std::optional<int64_t> try_as_int64() const;
};

struct ConstObjectValue {
    ConstObjectValueKind kind = ConstObjectValueKind::Record;
    aburi::cir::EntityId active_union_member{};
    std::vector<ConstValue> elements;
};

enum class ConstIntOpError {
    None,
    DivisionByZero,
    InvalidShiftAmount
};

struct ConstIntOpResult {
    std::optional<ConstIntValue> value;
    ConstIntOpError error = ConstIntOpError::None;

    static ConstIntOpResult ok(ConstIntValue value) {
        return {value, ConstIntOpError::None};
    }

    static ConstIntOpResult fail(ConstIntOpError error) {
        return {std::nullopt, error};
    }
};

ConstIntOpResult const_int_div(ConstIntValue lhs, ConstIntValue rhs);
ConstIntOpResult const_int_mod(ConstIntValue lhs, ConstIntValue rhs);
ConstIntValue const_int_neg(ConstIntValue value);
ConstIntValue const_int_add(ConstIntValue lhs, ConstIntValue rhs);
ConstIntValue const_int_sub(ConstIntValue lhs, ConstIntValue rhs);
ConstIntValue const_int_mul(ConstIntValue lhs, ConstIntValue rhs);
ConstIntOpResult const_int_shl(ConstIntValue lhs, ConstIntValue rhs);
ConstIntOpResult const_int_shr(ConstIntValue lhs, ConstIntValue rhs);
bool const_int_value_representable(ConstIntValue value,
                                   uint16_t target_bit_width,
                                   bool target_is_unsigned);

bool const_value_equals(const ConstValue& lhs, const ConstValue& rhs);
std::string const_value_to_string(const ConstValue& value);

#endif // ABURI_CONST_VALUE_H
