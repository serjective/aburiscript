#ifndef ABURI_NUMERIC_FLOATING_POINT_H
#define ABURI_NUMERIC_FLOATING_POINT_H

#include <cstdint>
#include <string>
#include <string_view>

namespace aburi::numeric {

enum class FloatFormat : uint8_t {
    Invalid,
    IEEEBinary16,
    IEEEBinary32,
    IEEEBinary64,
    X87Extended80,
    IEEEBinary128,
};

struct FloatFormatDescriptor {
    uint16_t storage_bits = 0;
    uint16_t precision = 0;
    uint16_t significand_storage_bits = 0;
    uint8_t exponent_bits = 0;
    int32_t exponent_bias = 0;
    bool explicit_integer_bit = false;

    int32_t min_normal_exponent() const {
        return 1 - exponent_bias;
    }

    int32_t max_normal_exponent() const {
        return ((int32_t{1} << exponent_bits) - 2) - exponent_bias;
    }
};

const FloatFormatDescriptor* descriptor(FloatFormat format);

struct FloatValue {
    FloatFormat semantics = FloatFormat::Invalid;
    uint64_t low_bits = 0;
    uint64_t high_bits = 0;

    bool valid() const { return semantics != FloatFormat::Invalid; }
    uint16_t bit_width() const;
    bool canonical() const;

    friend bool operator==(const FloatValue&, const FloatValue&) = default;
};

enum class FloatClass : uint8_t {
    Invalid,
    Zero,
    Subnormal,
    Normal,
    Infinity,
    QuietNaN,
    SignalingNaN,
};

enum class RoundingMode : uint8_t {
    NearestTiesToEven,
    NearestTiesAway,
    TowardZero,
    TowardPositive,
    TowardNegative,
};

enum class TininessMode : uint8_t {
    BeforeRounding,
    AfterRounding,
};

struct FloatControl {
    RoundingMode rounding = RoundingMode::NearestTiesToEven;
    TininessMode tininess = TininessMode::AfterRounding;
};

enum class FloatStatusFlag : uint8_t {
    Invalid = 1u << 0,
    DivideByZero = 1u << 1,
    Overflow = 1u << 2,
    Underflow = 1u << 3,
    Inexact = 1u << 4,
};

struct FloatStatus {
    uint8_t bits = 0;

    bool has(FloatStatusFlag flag) const {
        return (bits & static_cast<uint8_t>(flag)) != 0;
    }

    void set(FloatStatusFlag flag) {
        bits |= static_cast<uint8_t>(flag);
    }

    void merge(FloatStatus other) {
        bits |= other.bits;
    }

    bool empty() const { return bits == 0; }
};

enum class FloatError : uint8_t {
    None,
    InvalidFormat,
    InvalidEncoding,
    FormatMismatch,
    InvalidIntegerWidth,
    IntegerOutOfRange,
};

struct FloatResult {
    FloatValue value;
    FloatStatus status;
    FloatError error = FloatError::None;

    bool has_value() const { return error == FloatError::None && value.valid(); }
    explicit operator bool() const { return has_value(); }
    const FloatValue& operator*() const { return value; }
    FloatValue& operator*() { return value; }
    const FloatValue* operator->() const { return &value; }
    FloatValue* operator->() { return &value; }
};

struct ComplexFloatValue {
    FloatValue real;
    FloatValue imag;

    bool valid() const {
        return real.valid() && imag.valid() &&
               real.semantics == imag.semantics;
    }
};

struct ComplexFloatResult {
    ComplexFloatValue value;
    FloatStatus status;
    FloatError error = FloatError::None;

    bool has_value() const {
        return error == FloatError::None && value.valid();
    }
    explicit operator bool() const { return has_value(); }
};

enum class ParseError : uint8_t {
    None,
    InvalidFormat,
    InvalidSyntax,
    InvalidPayload,
};

struct FloatParseResult {
    FloatValue value;
    FloatStatus status;
    ParseError error = ParseError::None;

    bool has_value() const { return error == ParseError::None && value.valid(); }
    explicit operator bool() const { return has_value(); }
    const FloatValue& operator*() const { return value; }
    FloatValue& operator*() { return value; }
    const FloatValue* operator->() const { return &value; }
    FloatValue* operator->() { return &value; }
};

enum class BinaryOperation : uint8_t {
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
};

enum class CompareResult : uint8_t {
    Less,
    Equal,
    Greater,
    Unordered,
};

struct FloatCompareResult {
    CompareResult value = CompareResult::Unordered;
    FloatStatus status;
    FloatError error = FloatError::None;

    bool has_value() const { return error == FloatError::None; }
    explicit operator bool() const { return has_value(); }
    CompareResult operator*() const { return value; }
};

struct FloatIntegerResult {
    unsigned __int128 value = 0;
    FloatStatus status;
    FloatError error = FloatError::None;

    bool has_value() const { return error == FloatError::None; }
    explicit operator bool() const { return has_value(); }
    unsigned __int128 operator*() const { return value; }
};

FloatParseResult parse(std::string_view spelling,
                       FloatFormat format,
                       FloatControl control = {});
FloatValue zero(FloatFormat format, bool negative = false);
FloatValue infinity(FloatFormat format, bool negative = false);
FloatParseResult nan(FloatFormat format,
                     std::string_view payload,
                     bool signaling = false,
                     bool negative = false);

FloatValue negate(FloatValue value);
FloatResult convert(FloatValue value,
                    FloatFormat format,
                    FloatControl control = {});
FloatResult scale_by_power_of_two(FloatValue value,
                                 int64_t exponent,
                                 FloatControl control = {});
FloatResult binary(BinaryOperation operation,
                   FloatValue lhs,
                   FloatValue rhs,
                   FloatControl control = {});
ComplexFloatResult complex_multiply(ComplexFloatValue lhs,
                                    ComplexFloatValue rhs,
                                    FloatControl control = {});
ComplexFloatResult complex_divide(ComplexFloatValue lhs,
                                  ComplexFloatValue rhs,
                                  FloatControl control = {});
FloatCompareResult compare(FloatValue lhs, FloatValue rhs);

FloatResult from_integer(unsigned __int128 bits,
                         uint16_t bit_width,
                         bool is_signed,
                         FloatFormat format,
                         FloatControl control = {});
FloatIntegerResult to_integer(FloatValue value,
                              uint16_t bit_width,
                              bool is_signed);

FloatClass classify(FloatValue value);
bool is_zero(FloatValue value);
bool is_nan(FloatValue value);
bool is_infinity(FloatValue value);
bool is_negative(FloatValue value);

std::string display(FloatValue value);
std::string hex_display(FloatValue value);
std::string bit_pattern_hex(FloatValue value);

} // namespace aburi::numeric

namespace aburi::floating {
using numeric::BinaryOperation;
using numeric::CompareResult;
using numeric::ComplexFloatResult;
using numeric::ComplexFloatValue;
using numeric::FloatClass;
using numeric::FloatCompareResult;
using numeric::FloatControl;
using numeric::FloatError;
using numeric::FloatFormat;
using numeric::FloatFormatDescriptor;
using numeric::FloatIntegerResult;
using numeric::FloatParseResult;
using numeric::FloatResult;
using numeric::FloatStatus;
using numeric::FloatStatusFlag;
using numeric::RoundingMode;
using numeric::TininessMode;
using numeric::binary;
using numeric::bit_pattern_hex;
using numeric::classify;
using numeric::compare;
using numeric::complex_divide;
using numeric::complex_multiply;
using numeric::convert;
using numeric::descriptor;
using numeric::display;
using numeric::from_integer;
using numeric::hex_display;
using numeric::infinity;
using numeric::is_infinity;
using numeric::is_nan;
using numeric::is_negative;
using numeric::is_zero;
using numeric::nan;
using numeric::negate;
using numeric::parse;
using numeric::scale_by_power_of_two;
using numeric::to_integer;
using numeric::zero;
} // namespace aburi::floating

#endif // ABURI_NUMERIC_FLOATING_POINT_H
