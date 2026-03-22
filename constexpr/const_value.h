#ifndef ABURI_CONST_VALUE_H
#define ABURI_CONST_VALUE_H

#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <vector>

struct Symbol;
struct QualType;

enum class ConstValueKind {
    Invalid,
    Integer,
    Boolean,
    Floating,
    NullPointer,
    Address,
    MemberPointer,
    Object,
};

struct ConstIntValue {
    uint64_t bits = 0;
    uint16_t bit_width = 64;
    bool is_unsigned = false;

    static ConstIntValue from_unsigned(uint64_t value, uint16_t width);
    static ConstIntValue from_signed(int64_t value, uint16_t width);

    uint64_t to_unsigned_u64() const;
    int64_t to_signed_i64() const;

    ConstIntValue cast(uint16_t new_width, bool new_unsigned) const;
};

struct ConstFloatValue {
    long double value = 0.0L;
    uint16_t bit_width = 64;
};

struct ConstAddressValue {
    std::shared_ptr<Symbol> symbol = nullptr;
    int64_t byte_offset = 0;
};

struct ConstMemberPointerValue {
    int64_t byte_offset = 0;
    std::shared_ptr<Symbol> method_symbol = nullptr;
    int32_t virtual_slot_index = -1;
    const std::string* member_name = nullptr;
    bool is_function_member = false;
};

enum class ConstObjectValueKind : uint8_t {
    Record,
    Array,
};

struct ConstObjectValue;

struct ConstValue {
    ConstValueKind kind = ConstValueKind::Invalid;
    ConstIntValue int_value{};
    bool bool_value = false;
    ConstFloatValue float_value{};
    ConstAddressValue address_value{};
    ConstMemberPointerValue member_pointer_value{};
    std::shared_ptr<ConstObjectValue> object_value{};

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

    static ConstValue floating(long double value, uint16_t width = 64) {
        ConstValue out;
        out.kind = ConstValueKind::Floating;
        out.float_value = {value, width};
        return out;
    }

    static ConstValue null_pointer() {
        ConstValue out;
        out.kind = ConstValueKind::NullPointer;
        return out;
    }

    static ConstValue address(std::shared_ptr<Symbol> symbol,
                              int64_t byte_offset = 0) {
        ConstValue out;
        out.kind = ConstValueKind::Address;
        out.address_value.symbol = std::move(symbol);
        out.address_value.byte_offset = byte_offset;
        return out;
    }

    static ConstValue member_pointer(int64_t byte_offset,
                                     bool is_function_member,
                                     std::shared_ptr<Symbol> method_symbol = nullptr,
                                     int32_t virtual_slot_index = -1,
                                     const std::string* member_name = nullptr) {
        ConstValue out;
        out.kind = ConstValueKind::MemberPointer;
        out.member_pointer_value.byte_offset = byte_offset;
        out.member_pointer_value.method_symbol = std::move(method_symbol);
        out.member_pointer_value.virtual_slot_index = virtual_slot_index;
        out.member_pointer_value.member_name = member_name;
        out.member_pointer_value.is_function_member = is_function_member;
        return out;
    }

    static ConstValue object(ConstObjectValueKind object_kind,
                             std::vector<ConstValue> elements);

    std::optional<int64_t> try_as_int64() const;
};

struct ConstObjectValue {
    ConstObjectValueKind kind = ConstObjectValueKind::Record;
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
ConstIntOpResult const_int_shl(ConstIntValue lhs, ConstIntValue rhs);

bool const_value_equals(const ConstValue& lhs, const ConstValue& rhs);
std::string const_value_to_string(const ConstValue& value,
                                  const QualType* value_type = nullptr);

#endif // ABURI_CONST_VALUE_H
