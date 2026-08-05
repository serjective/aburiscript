#include "floating_point.h"

#include <algorithm>
#include <array>
#include <cctype>
#include <iomanip>
#include <limits>
#include <sstream>
#include <utility>
#include <vector>

namespace aburi::numeric {

namespace {

using uint128_t = unsigned __int128;

class BigUInt {
public:
    BigUInt() = default;
    explicit BigUInt(uint128_t value) {
        if (uint64_t low = static_cast<uint64_t>(value); low != 0) {
            words_.push_back(low);
        } else if ((value >> 64) != 0) {
            words_.push_back(0);
        }
        if (uint64_t high = static_cast<uint64_t>(value >> 64); high != 0) {
            words_.push_back(high);
        }
    }

    bool is_zero() const { return words_.empty(); }
    bool is_odd() const { return !words_.empty() && (words_[0] & 1u) != 0; }
    size_t word_count() const { return words_.size(); }

    size_t bit_width() const {
        if (words_.empty()) {
            return 0;
        }
        uint64_t top = words_.back();
        return (words_.size() - 1) * 64 +
            (64 - static_cast<size_t>(__builtin_clzll(top)));
    }

    bool bit(size_t index) const {
        size_t word = index / 64;
        return word < words_.size() &&
            (words_[word] & (uint64_t{1} << (index % 64))) != 0;
    }

    void set_bit(size_t index) {
        size_t word = index / 64;
        if (words_.size() <= word) {
            words_.resize(word + 1, 0);
        }
        words_[word] |= uint64_t{1} << (index % 64);
    }

    int compare(const BigUInt& other) const {
        if (words_.size() != other.words_.size()) {
            return words_.size() < other.words_.size() ? -1 : 1;
        }
        for (size_t i = words_.size(); i-- > 0;) {
            if (words_[i] != other.words_[i]) {
                return words_[i] < other.words_[i] ? -1 : 1;
            }
        }
        return 0;
    }

    BigUInt shifted_left(size_t bits) const {
        if (is_zero() || bits == 0) {
            return *this;
        }
        size_t whole = bits / 64;
        unsigned part = static_cast<unsigned>(bits % 64);
        BigUInt out;
        out.words_.assign(words_.size() + whole + (part ? 1 : 0), 0);
        for (size_t i = 0; i < words_.size(); ++i) {
            out.words_[i + whole] |= words_[i] << part;
            if (part != 0) {
                out.words_[i + whole + 1] |= words_[i] >> (64 - part);
            }
        }
        out.normalize();
        return out;
    }

    BigUInt shifted_right(size_t bits, bool* discarded = nullptr) const {
        if (discarded) {
            *discarded = false;
        }
        if (is_zero() || bits == 0) {
            return *this;
        }
        size_t whole = bits / 64;
        unsigned part = static_cast<unsigned>(bits % 64);
        if (discarded) {
            for (size_t i = 0; i < std::min(whole, words_.size()); ++i) {
                *discarded |= words_[i] != 0;
            }
            if (part != 0 && whole < words_.size()) {
                *discarded |=
                    (words_[whole] & ((uint64_t{1} << part) - 1)) != 0;
            }
        }
        if (whole >= words_.size()) {
            return {};
        }
        BigUInt out;
        out.words_.assign(words_.size() - whole, 0);
        for (size_t i = whole; i < words_.size(); ++i) {
            size_t target = i - whole;
            out.words_[target] |= words_[i] >> part;
            if (part != 0 && i + 1 < words_.size()) {
                out.words_[target] |= words_[i + 1] << (64 - part);
            }
        }
        out.normalize();
        return out;
    }

    void shift_right_one() {
        uint64_t carry = 0;
        for (size_t i = words_.size(); i-- > 0;) {
            uint64_t next = words_[i] << 63;
            words_[i] = (words_[i] >> 1) | carry;
            carry = next;
        }
        normalize();
    }

    void add(const BigUInt& other) {
        size_t size = std::max(words_.size(), other.words_.size());
        words_.resize(size, 0);
        uint128_t carry = 0;
        for (size_t i = 0; i < size; ++i) {
            uint128_t sum = static_cast<uint128_t>(words_[i]) +
                (i < other.words_.size() ? other.words_[i] : 0) + carry;
            words_[i] = static_cast<uint64_t>(sum);
            carry = sum >> 64;
        }
        if (carry != 0) {
            words_.push_back(static_cast<uint64_t>(carry));
        }
    }

    void add_small(uint32_t value) {
        if (value == 0) {
            return;
        }
        if (words_.empty()) {
            words_.push_back(value);
            return;
        }
        uint128_t carry = value;
        for (size_t i = 0; i < words_.size() && carry != 0; ++i) {
            uint128_t sum = static_cast<uint128_t>(words_[i]) + carry;
            words_[i] = static_cast<uint64_t>(sum);
            carry = sum >> 64;
        }
        if (carry != 0) {
            words_.push_back(static_cast<uint64_t>(carry));
        }
    }
    void subtract(const BigUInt& other) {
        uint64_t borrow = 0;
        for (size_t i = 0; i < words_.size(); ++i) {
            uint64_t rhs = i < other.words_.size() ? other.words_[i] : 0;
            uint64_t prior = words_[i];
            uint64_t with_borrow = rhs + borrow;
            bool rhs_overflow = with_borrow < rhs;
            words_[i] = prior - with_borrow;
            borrow = rhs_overflow || prior < with_borrow;
        }
        normalize();
    }

    void multiply_small(uint32_t value) {
        if (value == 0 || is_zero()) {
            words_.clear();
            return;
        }
        uint128_t carry = 0;
        for (uint64_t& word : words_) {
            uint128_t product = static_cast<uint128_t>(word) * value + carry;
            word = static_cast<uint64_t>(product);
            carry = product >> 64;
        }
        if (carry != 0) {
            words_.push_back(static_cast<uint64_t>(carry));
        }
    }

    static BigUInt multiply(const BigUInt& lhs, const BigUInt& rhs) {
        if (lhs.is_zero() || rhs.is_zero()) {
            return {};
        }
        BigUInt out;
        out.words_.assign(lhs.words_.size() + rhs.words_.size(), 0);
        for (size_t i = 0; i < lhs.words_.size(); ++i) {
            uint128_t carry = 0;
            for (size_t j = 0; j < rhs.words_.size(); ++j) {
                size_t index = i + j;
                uint128_t product = static_cast<uint128_t>(lhs.words_[i]) *
                    rhs.words_[j] + out.words_[index] + carry;
                out.words_[index] = static_cast<uint64_t>(product);
                carry = product >> 64;
            }
            size_t index = i + rhs.words_.size();
            while (carry != 0) {
                uint128_t sum = static_cast<uint128_t>(out.words_[index]) + carry;
                out.words_[index] = static_cast<uint64_t>(sum);
                carry = sum >> 64;
                ++index;
                if (index == out.words_.size() && carry != 0) {
                    out.words_.push_back(0);
                }
            }
        }
        out.normalize();
        return out;
    }

    static std::pair<BigUInt, BigUInt> divmod(BigUInt numerator,
                                               const BigUInt& denominator) {
        BigUInt quotient;
        if (denominator.is_zero() || numerator.compare(denominator) < 0) {
            return {quotient, numerator};
        }
        size_t shift = numerator.bit_width() - denominator.bit_width();
        BigUInt shifted = denominator.shifted_left(shift);
        for (size_t index = shift + 1; index-- > 0;) {
            if (numerator.compare(shifted) >= 0) {
                numerator.subtract(shifted);
                quotient.set_bit(index);
            }
            if (index != 0) {
                shifted.shift_right_one();
            }
        }
        quotient.normalize();
        numerator.normalize();
        return {quotient, numerator};
    }

    uint32_t divide_small(uint32_t divisor) {
        uint128_t remainder = 0;
        for (size_t i = words_.size(); i-- > 0;) {
            uint128_t current = (remainder << 64) | words_[i];
            words_[i] = static_cast<uint64_t>(current / divisor);
            remainder = current % divisor;
        }
        normalize();
        return static_cast<uint32_t>(remainder);
    }

    uint128_t to_u128() const {
        uint128_t result = words_.empty() ? 0 : words_[0];
        if (words_.size() > 1) {
            result |= static_cast<uint128_t>(words_[1]) << 64;
        }
        return result;
    }

    std::string to_decimal() const {
        if (is_zero()) {
            return "0";
        }
        BigUInt copy = *this;
        std::vector<uint32_t> chunks;
        while (!copy.is_zero()) {
            chunks.push_back(copy.divide_small(1'000'000'000));
        }
        std::ostringstream out;
        out << chunks.back();
        for (size_t i = chunks.size() - 1; i-- > 0;) {
            out << std::setw(9) << std::setfill('0') << chunks[i];
        }
        return out.str();
    }

    std::string to_hex() const {
        if (is_zero()) {
            return "0";
        }
        std::ostringstream out;
        out << std::hex << std::nouppercase;
        out << words_.back();
        for (size_t i = words_.size() - 1; i-- > 0;) {
            out << std::setw(16) << std::setfill('0') << words_[i];
        }
        return out.str();
    }

private:
    void normalize() {
        while (!words_.empty() && words_.back() == 0) {
            words_.pop_back();
        }
    }

    std::vector<uint64_t> words_;
};

constexpr std::array<FloatFormatDescriptor, 6> kFormats = {{
    {},
    {16, 11, 10, 5, 15, false},
    {32, 24, 23, 8, 127, false},
    {64, 53, 52, 11, 1023, false},
    {80, 64, 64, 15, 16383, true},
    {128, 113, 112, 15, 16383, false},
}};

uint128_t low_mask(unsigned bits) {
    if (bits == 0) {
        return 0;
    }
    if (bits >= 128) {
        return ~uint128_t{0};
    }
    return (uint128_t{1} << bits) - 1;
}

uint128_t raw_bits(FloatValue value) {
    return static_cast<uint128_t>(value.low_bits) |
        (static_cast<uint128_t>(value.high_bits) << 64);
}

FloatValue from_raw(FloatFormat format, uint128_t raw) {
    FloatValue value;
    value.semantics = format;
    value.low_bits = static_cast<uint64_t>(raw);
    value.high_bits = static_cast<uint64_t>(raw >> 64);
    const FloatFormatDescriptor* fmt = descriptor(format);
    if (!fmt) {
        return {};
    }
    if (fmt->storage_bits < 128) {
        raw &= low_mask(fmt->storage_bits);
        value.low_bits = static_cast<uint64_t>(raw);
        value.high_bits = static_cast<uint64_t>(raw >> 64);
    }
    return value;
}

uint128_t exponent_mask(const FloatFormatDescriptor& fmt) {
    return low_mask(fmt.exponent_bits);
}

uint128_t exponent_field(FloatValue value,
                         const FloatFormatDescriptor& fmt) {
    return (raw_bits(value) >> fmt.significand_storage_bits) &
        exponent_mask(fmt);
}

uint128_t significand_field(FloatValue value,
                            const FloatFormatDescriptor& fmt) {
    return raw_bits(value) & low_mask(fmt.significand_storage_bits);
}

bool sign_field(FloatValue value, const FloatFormatDescriptor& fmt) {
    return ((raw_bits(value) >> (fmt.storage_bits - 1)) & 1u) != 0;
}

uint128_t sign_bits(bool negative, const FloatFormatDescriptor& fmt) {
    return negative ? uint128_t{1} << (fmt.storage_bits - 1) : 0;
}

struct DecodedFloat {
    FloatClass classification = FloatClass::Invalid;
    bool negative = false;
    BigUInt significand;
    BigUInt payload;
    int32_t exponent = 0; // value = significand * 2^exponent
};

DecodedFloat decode(FloatValue value) {
    DecodedFloat out;
    const FloatFormatDescriptor* fmt = descriptor(value.semantics);
    if (!fmt || !value.canonical()) {
        return out;
    }
    out.negative = sign_field(value, *fmt);
    uint128_t exponent = exponent_field(value, *fmt);
    uint128_t significand = significand_field(value, *fmt);
    uint128_t max_exponent = exponent_mask(*fmt);
    uint128_t integer_bit = fmt->explicit_integer_bit
        ? uint128_t{1} << (fmt->precision - 1)
        : 0;
    uint128_t fraction_mask = fmt->explicit_integer_bit
        ? integer_bit - 1
        : low_mask(fmt->significand_storage_bits);

    if (exponent == max_exponent) {
        if (fmt->explicit_integer_bit && (significand & integer_bit) == 0) {
            return out;
        }
        uint128_t fraction = significand & fraction_mask;
        if (fraction == 0) {
            out.classification = FloatClass::Infinity;
            return out;
        }
        uint128_t quiet_bit = uint128_t{1} <<
            (fmt->explicit_integer_bit ? fmt->precision - 2
                                       : fmt->significand_storage_bits - 1);
        out.classification = (fraction & quiet_bit) != 0
            ? FloatClass::QuietNaN
            : FloatClass::SignalingNaN;
        out.payload = BigUInt(fraction & ~quiet_bit);
        return out;
    }

    if (exponent == 0) {
        if (significand == 0) {
            out.classification = FloatClass::Zero;
            return out;
        }
        // x87 pseudo-denormals are the same mathematical values as the
        // corresponding exponent-one normal and are normalized on import.
        if (fmt->explicit_integer_bit && (significand & integer_bit) != 0) {
            out.classification = FloatClass::Normal;
        } else {
            out.classification = FloatClass::Subnormal;
        }
        out.significand = BigUInt(significand);
        out.exponent = fmt->min_normal_exponent() - (fmt->precision - 1);
        return out;
    }

    if (fmt->explicit_integer_bit && (significand & integer_bit) == 0) {
        return out;
    }
    out.classification = FloatClass::Normal;
    uint128_t full_significand = fmt->explicit_integer_bit
        ? significand
        : significand | (uint128_t{1} << (fmt->precision - 1));
    out.significand = BigUInt(full_significand);
    int32_t unbiased = static_cast<int32_t>(exponent) - fmt->exponent_bias;
    out.exponent = unbiased - (fmt->precision - 1);
    return out;
}

FloatValue maximum_finite(FloatFormat format, bool negative) {
    const FloatFormatDescriptor* fmt = descriptor(format);
    if (!fmt) {
        return {};
    }
    uint128_t exponent = exponent_mask(*fmt) - 1;
    uint128_t significand = low_mask(fmt->significand_storage_bits);
    return from_raw(format,
                    sign_bits(negative, *fmt) |
                    (exponent << fmt->significand_storage_bits) |
                    significand);
}

FloatValue minimum_subnormal(FloatFormat format, bool negative) {
    const FloatFormatDescriptor* fmt = descriptor(format);
    if (!fmt) {
        return {};
    }
    return from_raw(format, sign_bits(negative, *fmt) | 1u);
}

FloatValue make_nan(FloatFormat format,
                    bool negative,
                    bool signaling,
                    const BigUInt& payload) {
    const FloatFormatDescriptor* fmt = descriptor(format);
    if (!fmt) {
        return {};
    }
    unsigned quiet_position = fmt->explicit_integer_bit
        ? fmt->precision - 2
        : fmt->significand_storage_bits - 1;
    uint128_t quiet_bit = uint128_t{1} << quiet_position;
    uint128_t payload_mask = quiet_bit - 1;
    uint128_t fraction = payload.to_u128() & payload_mask;
    if (signaling) {
        if (fraction == 0) {
            fraction = 1;
        }
    } else {
        fraction |= quiet_bit;
    }
    if (fmt->explicit_integer_bit) {
        fraction |= uint128_t{1} << (fmt->precision - 1);
    }
    uint128_t exponent = exponent_mask(*fmt);
    return from_raw(format,
                    sign_bits(negative, *fmt) |
                    (exponent << fmt->significand_storage_bits) |
                    fraction);
}

FloatResult error_result(FloatError error) {
    FloatResult result;
    result.error = error;
    return result;
}

FloatResult overflow_result(FloatFormat format,
                            bool negative,
                            FloatControl control) {
    FloatResult result;
    result.status.set(FloatStatusFlag::Overflow);
    result.status.set(FloatStatusFlag::Inexact);
    bool to_infinity = false;
    switch (control.rounding) {
        case RoundingMode::NearestTiesToEven:
        case RoundingMode::NearestTiesAway:
            to_infinity = true;
            break;
        case RoundingMode::TowardZero:
            break;
        case RoundingMode::TowardPositive:
            to_infinity = !negative;
            break;
        case RoundingMode::TowardNegative:
            to_infinity = negative;
            break;
    }
    result.value = to_infinity ? infinity(format, negative)
                               : maximum_finite(format, negative);
    return result;
}

FloatResult tiny_nonzero_result(FloatFormat format,
                                bool negative,
                                FloatControl control) {
    FloatResult result;
    result.status.set(FloatStatusFlag::Underflow);
    result.status.set(FloatStatusFlag::Inexact);
    bool away = (control.rounding == RoundingMode::TowardPositive && !negative) ||
        (control.rounding == RoundingMode::TowardNegative && negative);
    result.value = away ? minimum_subnormal(format, negative)
                        : zero(format, negative);
    return result;
}

int compare_scaled(const BigUInt& lhs,
                   int64_t lhs_shift,
                   const BigUInt& rhs,
                   int64_t rhs_shift) {
    if (lhs.is_zero() || rhs.is_zero()) {
        if (lhs.is_zero() == rhs.is_zero()) {
            return 0;
        }
        return lhs.is_zero() ? -1 : 1;
    }
    int64_t lhs_top = static_cast<int64_t>(lhs.bit_width()) + lhs_shift;
    int64_t rhs_top = static_cast<int64_t>(rhs.bit_width()) + rhs_shift;
    if (lhs_top != rhs_top) {
        return lhs_top < rhs_top ? -1 : 1;
    }
    int64_t minimum = std::min(lhs_shift, rhs_shift);
    BigUInt left = lhs.shifted_left(static_cast<size_t>(lhs_shift - minimum));
    BigUInt right = rhs.shifted_left(static_cast<size_t>(rhs_shift - minimum));
    return left.compare(right);
}

std::pair<BigUInt, BigUInt> scaled_division(const BigUInt& numerator,
                                             const BigUInt& denominator,
                                             int64_t binary_shift,
                                             BigUInt& effective_denominator) {
    BigUInt effective_numerator = numerator;
    effective_denominator = denominator;
    if (binary_shift >= 0) {
        effective_numerator =
            numerator.shifted_left(static_cast<size_t>(binary_shift));
    } else {
        effective_denominator =
            denominator.shifted_left(static_cast<size_t>(-binary_shift));
    }
    return BigUInt::divmod(std::move(effective_numerator),
                           effective_denominator);
}

FloatResult round_rational(bool negative,
                           const BigUInt& numerator,
                           const BigUInt& denominator,
                           int64_t binary_exponent,
                           FloatFormat format,
                           FloatControl control) {
    const FloatFormatDescriptor* fmt = descriptor(format);
    if (!fmt) {
        return error_result(FloatError::InvalidFormat);
    }
    if (numerator.is_zero()) {
        return FloatResult{zero(format, negative), {}, FloatError::None};
    }
    if (denominator.is_zero()) {
        return error_result(FloatError::InvalidEncoding);
    }

    int64_t candidate_exponent =
        static_cast<int64_t>(numerator.bit_width()) -
        static_cast<int64_t>(denominator.bit_width()) + binary_exponent;
    int scale_compare = compare_scaled(
        numerator, 0, denominator,
        static_cast<int64_t>(numerator.bit_width()) -
            static_cast<int64_t>(denominator.bit_width()));
    int64_t exponent = candidate_exponent - (scale_compare < 0 ? 1 : 0);
    int64_t minimum_subnormal_exponent =
        static_cast<int64_t>(fmt->min_normal_exponent()) -
        (fmt->precision - 1);

    if (exponent > static_cast<int64_t>(fmt->max_normal_exponent()) + 1) {
        return overflow_result(format, negative, control);
    }
    if (exponent < minimum_subnormal_exponent - 1) {
        return tiny_nonzero_result(format, negative, control);
    }

    bool tiny_before = exponent < fmt->min_normal_exponent();
    int64_t unit_exponent = tiny_before
        ? minimum_subnormal_exponent
        : exponent - (fmt->precision - 1);
    BigUInt effective_denominator;
    auto [rounded_significand, remainder] = scaled_division(
        numerator, denominator, binary_exponent - unit_exponent,
        effective_denominator);

    bool inexact = !remainder.is_zero();
    bool increment = false;
    if (inexact) {
        switch (control.rounding) {
            case RoundingMode::NearestTiesToEven:
            case RoundingMode::NearestTiesAway: {
                BigUInt twice = remainder;
                twice.multiply_small(2);
                int half = twice.compare(effective_denominator);
                increment = half > 0 ||
                    (half == 0 &&
                     (control.rounding == RoundingMode::NearestTiesAway ||
                      rounded_significand.is_odd()));
                break;
            }
            case RoundingMode::TowardZero:
                break;
            case RoundingMode::TowardPositive:
                increment = !negative;
                break;
            case RoundingMode::TowardNegative:
                increment = negative;
                break;
        }
    }
    if (increment) {
        rounded_significand.add_small(1);
    }

    uint128_t normal_limit = uint128_t{1} << fmt->precision;
    uint128_t minimum_normal = uint128_t{1} << (fmt->precision - 1);
    uint128_t significand = rounded_significand.to_u128();
    bool normal = !tiny_before;
    if (normal && significand >= normal_limit) {
        significand >>= 1;
        ++exponent;
    } else if (tiny_before && significand >= minimum_normal) {
        normal = true;
        exponent = fmt->min_normal_exponent();
    }

    if (normal && exponent > fmt->max_normal_exponent()) {
        return overflow_result(format, negative, control);
    }

    uint128_t raw = sign_bits(negative, *fmt);
    bool tiny_after = !normal;
    if (normal) {
        uint128_t stored = fmt->explicit_integer_bit
            ? significand
            : significand & (minimum_normal - 1);
        uint128_t biased = static_cast<uint128_t>(
            exponent + fmt->exponent_bias);
        raw |= biased << fmt->significand_storage_bits;
        raw |= stored;
    } else {
        raw |= significand;
    }

    FloatResult result;
    result.value = from_raw(format, raw);
    if (inexact) {
        result.status.set(FloatStatusFlag::Inexact);
        bool tiny = control.tininess == TininessMode::BeforeRounding
            ? tiny_before
            : tiny_after;
        if (tiny) {
            result.status.set(FloatStatusFlag::Underflow);
        }
    }
    return result;
}

FloatResult propagate_nan(FloatValue lhs,
                          const DecodedFloat& left,
                          FloatValue rhs,
                          const DecodedFloat& right) {
    const DecodedFloat* selected = nullptr;
    FloatFormat format = lhs.semantics;
    if (left.classification == FloatClass::QuietNaN ||
        left.classification == FloatClass::SignalingNaN) {
        selected = &left;
    } else if (right.classification == FloatClass::QuietNaN ||
               right.classification == FloatClass::SignalingNaN) {
        selected = &right;
        format = rhs.semantics;
    }
    FloatResult result;
    if (!selected) {
        result.value = make_nan(format, false, false, BigUInt{});
        result.status.set(FloatStatusFlag::Invalid);
        return result;
    }
    result.value = make_nan(format, selected->negative, false,
                            selected->payload);
    if (left.classification == FloatClass::SignalingNaN ||
        right.classification == FloatClass::SignalingNaN) {
        result.status.set(FloatStatusFlag::Invalid);
    }
    return result;
}

FloatResult invalid_operation(FloatFormat format) {
    FloatResult result;
    result.value = make_nan(format, false, false, BigUInt{});
    result.status.set(FloatStatusFlag::Invalid);
    return result;
}

bool is_nan_class(FloatClass value) {
    return value == FloatClass::QuietNaN ||
        value == FloatClass::SignalingNaN;
}

FloatResult add_values(FloatValue lhs,
                       FloatValue rhs,
                       bool subtract,
                       FloatControl control) {
    if (lhs.semantics != rhs.semantics) {
        return error_result(FloatError::FormatMismatch);
    }
    DecodedFloat left = decode(lhs);
    DecodedFloat right = decode(rhs);
    if (left.classification == FloatClass::Invalid ||
        right.classification == FloatClass::Invalid) {
        return error_result(FloatError::InvalidEncoding);
    }
    if (subtract) {
        right.negative = !right.negative;
    }
    if (is_nan_class(left.classification) ||
        is_nan_class(right.classification)) {
        return propagate_nan(lhs, left, rhs, right);
    }
    if (left.classification == FloatClass::Infinity ||
        right.classification == FloatClass::Infinity) {
        if (left.classification == FloatClass::Infinity &&
            right.classification == FloatClass::Infinity &&
            left.negative != right.negative) {
            return invalid_operation(lhs.semantics);
        }
        bool negative = left.classification == FloatClass::Infinity
            ? left.negative
            : right.negative;
        return FloatResult{infinity(lhs.semantics, negative), {},
                           FloatError::None};
    }
    if (left.classification == FloatClass::Zero &&
        right.classification == FloatClass::Zero) {
        bool negative = left.negative == right.negative
            ? left.negative
            : control.rounding == RoundingMode::TowardNegative;
        return FloatResult{zero(lhs.semantics, negative), {}, FloatError::None};
    }
    if (left.classification == FloatClass::Zero) {
        FloatValue result = rhs;
        if (subtract) {
            result = negate(result);
        }
        return FloatResult{result, {}, FloatError::None};
    }
    if (right.classification == FloatClass::Zero) {
        return FloatResult{lhs, {}, FloatError::None};
    }

    int32_t common_exponent = std::min(left.exponent, right.exponent);
    BigUInt left_integer = left.significand.shifted_left(
        static_cast<size_t>(left.exponent - common_exponent));
    BigUInt right_integer = right.significand.shifted_left(
        static_cast<size_t>(right.exponent - common_exponent));
    bool negative = false;
    BigUInt magnitude;
    if (left.negative == right.negative) {
        magnitude = left_integer;
        magnitude.add(right_integer);
        negative = left.negative;
    } else {
        int ordering = left_integer.compare(right_integer);
        if (ordering == 0) {
            negative = control.rounding == RoundingMode::TowardNegative;
            return FloatResult{zero(lhs.semantics, negative), {},
                               FloatError::None};
        }
        if (ordering > 0) {
            magnitude = left_integer;
            magnitude.subtract(right_integer);
            negative = left.negative;
        } else {
            magnitude = right_integer;
            magnitude.subtract(left_integer);
            negative = right.negative;
        }
    }
    return round_rational(negative, magnitude, BigUInt(1), common_exponent,
                          lhs.semantics, control);
}

FloatResult multiply_values(FloatValue lhs,
                            FloatValue rhs,
                            FloatControl control) {
    if (lhs.semantics != rhs.semantics) {
        return error_result(FloatError::FormatMismatch);
    }
    DecodedFloat left = decode(lhs);
    DecodedFloat right = decode(rhs);
    if (left.classification == FloatClass::Invalid ||
        right.classification == FloatClass::Invalid) {
        return error_result(FloatError::InvalidEncoding);
    }
    if (is_nan_class(left.classification) ||
        is_nan_class(right.classification)) {
        return propagate_nan(lhs, left, rhs, right);
    }
    bool negative = left.negative != right.negative;
    bool left_zero = left.classification == FloatClass::Zero;
    bool right_zero = right.classification == FloatClass::Zero;
    bool left_inf = left.classification == FloatClass::Infinity;
    bool right_inf = right.classification == FloatClass::Infinity;
    if ((left_zero && right_inf) || (left_inf && right_zero)) {
        return invalid_operation(lhs.semantics);
    }
    if (left_inf || right_inf) {
        return FloatResult{infinity(lhs.semantics, negative), {},
                           FloatError::None};
    }
    if (left_zero || right_zero) {
        return FloatResult{zero(lhs.semantics, negative), {}, FloatError::None};
    }
    BigUInt product = BigUInt::multiply(left.significand, right.significand);
    return round_rational(negative, product, BigUInt(1),
                          static_cast<int64_t>(left.exponent) + right.exponent,
                          lhs.semantics, control);
}

FloatResult divide_values(FloatValue lhs,
                          FloatValue rhs,
                          FloatControl control) {
    if (lhs.semantics != rhs.semantics) {
        return error_result(FloatError::FormatMismatch);
    }
    DecodedFloat left = decode(lhs);
    DecodedFloat right = decode(rhs);
    if (left.classification == FloatClass::Invalid ||
        right.classification == FloatClass::Invalid) {
        return error_result(FloatError::InvalidEncoding);
    }
    if (is_nan_class(left.classification) ||
        is_nan_class(right.classification)) {
        return propagate_nan(lhs, left, rhs, right);
    }
    bool negative = left.negative != right.negative;
    bool left_zero = left.classification == FloatClass::Zero;
    bool right_zero = right.classification == FloatClass::Zero;
    bool left_inf = left.classification == FloatClass::Infinity;
    bool right_inf = right.classification == FloatClass::Infinity;
    if ((left_zero && right_zero) || (left_inf && right_inf)) {
        return invalid_operation(lhs.semantics);
    }
    if (right_zero) {
        FloatResult result;
        result.value = infinity(lhs.semantics, negative);
        result.status.set(FloatStatusFlag::DivideByZero);
        return result;
    }
    if (left_inf) {
        return FloatResult{infinity(lhs.semantics, negative), {},
                           FloatError::None};
    }
    if (right_inf || left_zero) {
        return FloatResult{zero(lhs.semantics, negative), {}, FloatError::None};
    }
    return round_rational(negative, left.significand, right.significand,
                          static_cast<int64_t>(left.exponent) - right.exponent,
                          lhs.semantics, control);
}

FloatResult remainder_values(FloatValue lhs,
                             FloatValue rhs,
                             FloatControl control) {
    if (lhs.semantics != rhs.semantics) {
        return error_result(FloatError::FormatMismatch);
    }
    DecodedFloat left = decode(lhs);
    DecodedFloat right = decode(rhs);
    if (left.classification == FloatClass::Invalid ||
        right.classification == FloatClass::Invalid) {
        return error_result(FloatError::InvalidEncoding);
    }
    if (is_nan_class(left.classification) ||
        is_nan_class(right.classification)) {
        return propagate_nan(lhs, left, rhs, right);
    }
    if (left.classification == FloatClass::Infinity ||
        right.classification == FloatClass::Zero) {
        return invalid_operation(lhs.semantics);
    }
    if (left.classification == FloatClass::Zero ||
        right.classification == FloatClass::Infinity) {
        return FloatResult{lhs, {}, FloatError::None};
    }

    int32_t common = std::min(left.exponent, right.exponent);
    BigUInt dividend = left.significand.shifted_left(
        static_cast<size_t>(left.exponent - common));
    BigUInt divisor = right.significand.shifted_left(
        static_cast<size_t>(right.exponent - common));
    BigUInt remainder = BigUInt::divmod(std::move(dividend), divisor).second;
    if (remainder.is_zero()) {
        return FloatResult{zero(lhs.semantics, left.negative), {},
                           FloatError::None};
    }
    return round_rational(left.negative, remainder, BigUInt(1), common,
                          lhs.semantics, control);
}

BigUInt power_of_five(size_t exponent) {
    BigUInt value(1);
    for (size_t i = 0; i < exponent; ++i) {
        value.multiply_small(5);
    }
    return value;
}

int digit_value(char character, unsigned base) {
    int value = -1;
    if (character >= '0' && character <= '9') {
        value = character - '0';
    } else if (character >= 'a' && character <= 'f') {
        value = 10 + character - 'a';
    } else if (character >= 'A' && character <= 'F') {
        value = 10 + character - 'A';
    }
    return value >= 0 && static_cast<unsigned>(value) < base ? value : -1;
}

bool parse_big_digits(std::string_view digits,
                      unsigned base,
                      BigUInt& value) {
    if (digits.empty()) {
        return false;
    }
    value = BigUInt{};
    for (char character : digits) {
        int digit = digit_value(character, base);
        if (digit < 0) {
            return false;
        }
        value.multiply_small(base);
        value.add_small(static_cast<uint32_t>(digit));
    }
    return true;
}

bool case_equal(std::string_view lhs, std::string_view rhs) {
    if (lhs.size() != rhs.size()) {
        return false;
    }
    for (size_t i = 0; i < lhs.size(); ++i) {
        if (std::tolower(static_cast<unsigned char>(lhs[i])) !=
            std::tolower(static_cast<unsigned char>(rhs[i]))) {
            return false;
        }
    }
    return true;
}

std::string normalize_spelling(std::string_view spelling) {
    std::string normalized;
    normalized.reserve(spelling.size());
    for (char character : spelling) {
        if (character != '\'') {
            normalized.push_back(character);
        }
    }
    if (!normalized.empty() &&
        (normalized.back() == 'i' || normalized.back() == 'I' ||
         normalized.back() == 'j' || normalized.back() == 'J')) {
        normalized.pop_back();
    }
    std::string_view unsigned_spelling(normalized);
    if (!unsigned_spelling.empty() &&
        (unsigned_spelling.front() == '+' ||
         unsigned_spelling.front() == '-')) {
        unsigned_spelling.remove_prefix(1);
    }
    if (case_equal(unsigned_spelling, "inf") ||
        case_equal(unsigned_spelling, "infinity") ||
        case_equal(unsigned_spelling, "nan")) {
        return normalized;
    }
    constexpr std::array<std::string_view, 10> suffixes = {
        "bf16", "BF16", "f128", "F128", "f64", "F64", "f32", "F32",
        "f16", "F16",
    };
    for (std::string_view suffix : suffixes) {
        if (normalized.size() > suffix.size() &&
            normalized.ends_with(suffix)) {
            normalized.resize(normalized.size() - suffix.size());
            return normalized;
        }
    }
    if (!normalized.empty() &&
        (normalized.back() == 'f' || normalized.back() == 'F' ||
         normalized.back() == 'l' || normalized.back() == 'L')) {
        normalized.pop_back();
    }
    return normalized;
}

bool parse_exponent(std::string_view text, int64_t& exponent) {
    if (text.empty()) {
        return false;
    }
    bool negative = false;
    size_t index = 0;
    if (text[index] == '+' || text[index] == '-') {
        negative = text[index] == '-';
        ++index;
    }
    if (index == text.size()) {
        return false;
    }
    constexpr int64_t limit = 1'000'000'000;
    int64_t value = 0;
    for (; index < text.size(); ++index) {
        if (!std::isdigit(static_cast<unsigned char>(text[index]))) {
            return false;
        }
        int digit = text[index] - '0';
        if (value > (limit - digit) / 10) {
            value = limit;
        } else {
            value = value * 10 + digit;
        }
    }
    exponent = negative ? -value : value;
    return true;
}

FloatParseResult from_float_result(FloatResult result) {
    FloatParseResult parsed;
    parsed.value = result.value;
    parsed.status = result.status;
    if (result.error != FloatError::None) {
        parsed.error = ParseError::InvalidFormat;
    }
    return parsed;
}

std::string increment_decimal(std::string value) {
    for (size_t i = value.size(); i-- > 0;) {
        if (value[i] != '9') {
            ++value[i];
            return value;
        }
        value[i] = '0';
    }
    value.insert(value.begin(), '1');
    return value;
}

std::string candidate_spelling(std::string coefficient,
                               int64_t scientific_exponent,
                               bool negative) {
    while (coefficient.size() > 1 && coefficient.back() == '0') {
        coefficient.pop_back();
    }
    std::string scientific;
    scientific.push_back(coefficient[0]);
    if (coefficient.size() > 1) {
        scientific.push_back('.');
        scientific.append(coefficient.substr(1));
    }
    if (scientific_exponent != 0) {
        scientific.push_back('e');
        scientific.append(std::to_string(scientific_exponent));
    }

    int64_t point = scientific_exponent + 1;
    std::string fixed;
    if (point <= 0) {
        fixed = "0.";
        fixed.append(static_cast<size_t>(-point), '0');
        fixed.append(coefficient);
    } else if (point >= static_cast<int64_t>(coefficient.size())) {
        fixed = coefficient;
        fixed.append(static_cast<size_t>(
            point - static_cast<int64_t>(coefficient.size())), '0');
    } else {
        fixed = coefficient.substr(0, static_cast<size_t>(point));
        fixed.push_back('.');
        fixed.append(coefficient.substr(static_cast<size_t>(point)));
    }
    std::string result = fixed.size() <= scientific.size() ? fixed : scientific;
    if (negative) {
        result.insert(result.begin(), '-');
    }
    return result;
}

} // namespace

const FloatFormatDescriptor* descriptor(FloatFormat format) {
    size_t index = static_cast<size_t>(format);
    if (index == 0 || index >= kFormats.size()) {
        return nullptr;
    }
    return &kFormats[index];
}

uint16_t FloatValue::bit_width() const {
    const FloatFormatDescriptor* fmt = descriptor(semantics);
    return fmt ? fmt->storage_bits : 0;
}

bool FloatValue::canonical() const {
    const FloatFormatDescriptor* fmt = descriptor(semantics);
    if (!fmt) {
        return false;
    }
    if (fmt->storage_bits <= 64) {
        return high_bits == 0 &&
            (fmt->storage_bits == 64 ||
             (low_bits >> fmt->storage_bits) == 0);
    }
    unsigned high_width = fmt->storage_bits - 64;
    return high_width == 64 || (high_bits >> high_width) == 0;
}

FloatValue zero(FloatFormat format, bool negative) {
    const FloatFormatDescriptor* fmt = descriptor(format);
    return fmt ? from_raw(format, sign_bits(negative, *fmt)) : FloatValue{};
}

FloatValue infinity(FloatFormat format, bool negative) {
    const FloatFormatDescriptor* fmt = descriptor(format);
    if (!fmt) {
        return {};
    }
    uint128_t significand = fmt->explicit_integer_bit
        ? uint128_t{1} << (fmt->precision - 1)
        : 0;
    return from_raw(format,
                    sign_bits(negative, *fmt) |
                    (exponent_mask(*fmt) << fmt->significand_storage_bits) |
                    significand);
}

FloatParseResult nan(FloatFormat format,
                     std::string_view payload_text,
                     bool signaling,
                     bool negative) {
    FloatParseResult result;
    if (!descriptor(format)) {
        result.error = ParseError::InvalidFormat;
        return result;
    }
    unsigned base = 10;
    if (payload_text.size() > 2 && payload_text[0] == '0' &&
        (payload_text[1] == 'x' || payload_text[1] == 'X')) {
        base = 16;
        payload_text.remove_prefix(2);
    }
    BigUInt payload;
    if (!payload_text.empty() &&
        (!parse_big_digits(payload_text, base, payload) ||
         payload.bit_width() > 128)) {
        result.error = ParseError::InvalidPayload;
        return result;
    }
    result.value = make_nan(format, negative, signaling, payload);
    return result;
}

FloatParseResult parse(std::string_view spelling,
                       FloatFormat format,
                       FloatControl control) {
    FloatParseResult result;
    if (!descriptor(format)) {
        result.error = ParseError::InvalidFormat;
        return result;
    }
    std::string normalized = normalize_spelling(spelling);
    bool negative = false;
    if (!normalized.empty() &&
        (normalized.front() == '+' || normalized.front() == '-')) {
        negative = normalized.front() == '-';
        normalized.erase(normalized.begin());
    }
    if (case_equal(normalized, "inf") ||
        case_equal(normalized, "infinity")) {
        result.value = infinity(format, negative);
        return result;
    }
    if (case_equal(normalized, "nan")) {
        return nan(format, {}, false, negative);
    }
    if (normalized.size() >= 5 &&
        std::tolower(static_cast<unsigned char>(normalized[0])) == 'n' &&
        std::tolower(static_cast<unsigned char>(normalized[1])) == 'a' &&
        std::tolower(static_cast<unsigned char>(normalized[2])) == 'n' &&
        normalized[3] == '(' && normalized.back() == ')') {
        return nan(format,
                   std::string_view(normalized).substr(4,
                                                       normalized.size() - 5),
                   false, negative);
    }

    bool hexadecimal = normalized.size() >= 2 && normalized[0] == '0' &&
        (normalized[1] == 'x' || normalized[1] == 'X');
    size_t exponent_position = hexadecimal
        ? normalized.find_first_of("pP", 2)
        : normalized.find_first_of("eE");
    std::string_view significand_text(normalized);
    std::string_view exponent_text;
    if (exponent_position != std::string::npos) {
        significand_text = std::string_view(normalized).substr(0,
                                                              exponent_position);
        exponent_text = std::string_view(normalized).substr(exponent_position + 1);
        if (exponent_text.empty()) {
            result.error = ParseError::InvalidSyntax;
            return result;
        }
    } else if (hexadecimal) {
        result.error = ParseError::InvalidSyntax;
        return result;
    }
    int64_t explicit_exponent = 0;
    if (!exponent_text.empty() &&
        !parse_exponent(exponent_text, explicit_exponent)) {
        result.error = ParseError::InvalidSyntax;
        return result;
    }

    if (hexadecimal) {
        significand_text.remove_prefix(2);
    }
    size_t point = significand_text.find('.');
    if (point != std::string_view::npos &&
        significand_text.find('.', point + 1) != std::string_view::npos) {
        result.error = ParseError::InvalidSyntax;
        return result;
    }
    size_t fractional_digits = point == std::string_view::npos
        ? 0
        : significand_text.size() - point - 1;
    std::string digits(significand_text);
    if (point != std::string_view::npos) {
        digits.erase(point, 1);
    }
    BigUInt significand;
    unsigned base = hexadecimal ? 16 : 10;
    if (!parse_big_digits(digits, base, significand)) {
        result.error = ParseError::InvalidSyntax;
        return result;
    }
    if (significand.is_zero()) {
        result.value = zero(format, negative);
        return result;
    }

    if (hexadecimal) {
        int64_t binary_exponent = explicit_exponent -
            static_cast<int64_t>(fractional_digits) * 4;
        return from_float_result(round_rational(
            negative, significand, BigUInt(1), binary_exponent, format,
            control));
    }

    int64_t decimal_exponent = explicit_exponent -
        static_cast<int64_t>(fractional_digits);
    int64_t adjusted_decimal_exponent =
        static_cast<int64_t>(digits.size()) + decimal_exponent - 1;
    if (adjusted_decimal_exponent > 6000) {
        return from_float_result(overflow_result(format, negative, control));
    }
    if (adjusted_decimal_exponent < -6000) {
        return from_float_result(tiny_nonzero_result(format, negative,
                                                     control));
    }

    BigUInt numerator = significand;
    BigUInt denominator(1);
    int64_t binary_exponent = decimal_exponent;
    if (decimal_exponent >= 0) {
        numerator = BigUInt::multiply(
            numerator, power_of_five(static_cast<size_t>(decimal_exponent)));
    } else {
        denominator = power_of_five(static_cast<size_t>(-decimal_exponent));
    }
    return from_float_result(round_rational(
        negative, numerator, denominator, binary_exponent, format, control));
}

FloatValue negate(FloatValue value) {
    const FloatFormatDescriptor* fmt = descriptor(value.semantics);
    if (!fmt || !value.canonical()) {
        return {};
    }
    return from_raw(value.semantics,
                    raw_bits(value) ^
                        (uint128_t{1} << (fmt->storage_bits - 1)));
}

FloatResult convert(FloatValue value,
                    FloatFormat format,
                    FloatControl control) {
    if (!descriptor(format)) {
        return error_result(FloatError::InvalidFormat);
    }
    DecodedFloat decoded = decode(value);
    if (decoded.classification == FloatClass::Invalid) {
        return error_result(FloatError::InvalidEncoding);
    }
    if (decoded.classification == FloatClass::Zero) {
        return FloatResult{zero(format, decoded.negative), {}, FloatError::None};
    }
    if (decoded.classification == FloatClass::Infinity) {
        return FloatResult{infinity(format, decoded.negative), {},
                           FloatError::None};
    }
    if (is_nan_class(decoded.classification)) {
        FloatResult result;
        result.value = make_nan(format, decoded.negative, false,
                                decoded.payload);
        if (decoded.classification == FloatClass::SignalingNaN) {
            result.status.set(FloatStatusFlag::Invalid);
        }
        return result;
    }
    return round_rational(decoded.negative, decoded.significand, BigUInt(1),
                          decoded.exponent, format, control);
}

FloatResult scale_by_power_of_two(FloatValue value,
                                 int64_t exponent,
                                 FloatControl control) {
    DecodedFloat decoded = decode(value);
    if (decoded.classification == FloatClass::Invalid) {
        return error_result(FloatError::InvalidEncoding);
    }
    if (decoded.classification == FloatClass::Zero ||
        decoded.classification == FloatClass::Infinity ||
        is_nan_class(decoded.classification)) {
        return convert(value, value.semantics, control);
    }
    if (exponent > 1'000'000) {
        return overflow_result(value.semantics, decoded.negative, control);
    }
    if (exponent < -1'000'000) {
        return tiny_nonzero_result(value.semantics, decoded.negative, control);
    }
    return round_rational(decoded.negative, decoded.significand, BigUInt(1),
                          decoded.exponent + exponent,
                          value.semantics, control);
}

FloatResult binary(BinaryOperation operation,
                   FloatValue lhs,
                   FloatValue rhs,
                   FloatControl control) {
    switch (operation) {
        case BinaryOperation::Add:
            return add_values(lhs, rhs, false, control);
        case BinaryOperation::Subtract:
            return add_values(lhs, rhs, true, control);
        case BinaryOperation::Multiply:
            return multiply_values(lhs, rhs, control);
        case BinaryOperation::Divide:
            return divide_values(lhs, rhs, control);
        case BinaryOperation::Modulo:
            return remainder_values(lhs, rhs, control);
    }
    return error_result(FloatError::InvalidEncoding);
}

ComplexFloatResult complex_multiply(ComplexFloatValue lhs,
                                    ComplexFloatValue rhs,
                                    FloatControl control) {
    ComplexFloatResult result;
    if (!lhs.valid() || !rhs.valid() ||
        lhs.real.semantics != rhs.real.semantics) {
        result.error = lhs.valid() && rhs.valid()
            ? FloatError::FormatMismatch
            : FloatError::InvalidEncoding;
        return result;
    }
    FloatFormat format = lhs.real.semantics;
    auto calculate = [&](BinaryOperation operation,
                         FloatValue left,
                         FloatValue right,
                         FloatStatus& status,
                         FloatError& error) {
        FloatResult operation_result = binary(operation, left, right, control);
        status.merge(operation_result.status);
        if (!operation_result && error == FloatError::None) {
            error = operation_result.error;
        }
        return operation_result.value;
    };
    auto evaluate = [&](ComplexFloatValue left,
                        ComplexFloatValue right,
                        FloatStatus& status,
                        FloatError& error) {
        FloatValue ac = calculate(BinaryOperation::Multiply,
                                  left.real, right.real, status, error);
        FloatValue bd = calculate(BinaryOperation::Multiply,
                                  left.imag, right.imag, status, error);
        FloatValue ad = calculate(BinaryOperation::Multiply,
                                  left.real, right.imag, status, error);
        FloatValue bc = calculate(BinaryOperation::Multiply,
                                  left.imag, right.real, status, error);
        return ComplexFloatValue{
            calculate(BinaryOperation::Subtract, ac, bd, status, error),
            calculate(BinaryOperation::Add, ad, bc, status, error)};
    };

    FloatStatus initial_status;
    FloatError initial_error = FloatError::None;
    result.value = evaluate(lhs, rhs, initial_status, initial_error);
    result.status = initial_status;
    result.error = initial_error;
    if (result.error != FloatError::None ||
        !is_nan(result.value.real) || !is_nan(result.value.imag)) {
        return result;
    }

    bool recalculate = false;
    auto signed_unit_or_zero = [&](FloatValue value) {
        FloatValue magnitude = is_infinity(value)
            ? from_integer(1, 1, false, format).value
            : zero(format);
        return is_negative(value) ? negate(magnitude) : magnitude;
    };
    if (is_infinity(lhs.real) || is_infinity(lhs.imag)) {
        lhs.real = signed_unit_or_zero(lhs.real);
        lhs.imag = signed_unit_or_zero(lhs.imag);
        if (is_nan(rhs.real)) {
            rhs.real = zero(format, is_negative(rhs.real));
        }
        if (is_nan(rhs.imag)) {
            rhs.imag = zero(format, is_negative(rhs.imag));
        }
        recalculate = true;
    }
    if (is_infinity(rhs.real) || is_infinity(rhs.imag)) {
        rhs.real = signed_unit_or_zero(rhs.real);
        rhs.imag = signed_unit_or_zero(rhs.imag);
        if (is_nan(lhs.real)) {
            lhs.real = zero(format, is_negative(lhs.real));
        }
        if (is_nan(lhs.imag)) {
            lhs.imag = zero(format, is_negative(lhs.imag));
        }
        recalculate = true;
    }
    if (!recalculate) {
        FloatStatus ignored_status;
        FloatError ignored_error = FloatError::None;
        FloatValue ac = calculate(BinaryOperation::Multiply,
                                  lhs.real, rhs.real,
                                  ignored_status, ignored_error);
        FloatValue bd = calculate(BinaryOperation::Multiply,
                                  lhs.imag, rhs.imag,
                                  ignored_status, ignored_error);
        FloatValue ad = calculate(BinaryOperation::Multiply,
                                  lhs.real, rhs.imag,
                                  ignored_status, ignored_error);
        FloatValue bc = calculate(BinaryOperation::Multiply,
                                  lhs.imag, rhs.real,
                                  ignored_status, ignored_error);
        if (is_infinity(ac) || is_infinity(bd) ||
            is_infinity(ad) || is_infinity(bc)) {
            if (is_nan(lhs.real)) {
                lhs.real = zero(format, is_negative(lhs.real));
            }
            if (is_nan(lhs.imag)) {
                lhs.imag = zero(format, is_negative(lhs.imag));
            }
            if (is_nan(rhs.real)) {
                rhs.real = zero(format, is_negative(rhs.real));
            }
            if (is_nan(rhs.imag)) {
                rhs.imag = zero(format, is_negative(rhs.imag));
            }
            recalculate = true;
        }
    }
    if (!recalculate) {
        return result;
    }

    FloatStatus recovery_status;
    FloatError recovery_error = FloatError::None;
    ComplexFloatValue finite = evaluate(lhs, rhs,
                                        recovery_status, recovery_error);
    FloatValue positive_infinity = infinity(format);
    result.value.real = calculate(BinaryOperation::Multiply,
                                  positive_infinity, finite.real,
                                  recovery_status, recovery_error);
    result.value.imag = calculate(BinaryOperation::Multiply,
                                  positive_infinity, finite.imag,
                                  recovery_status, recovery_error);
    result.status = recovery_status;
    result.error = recovery_error;
    return result;
}

ComplexFloatResult complex_divide(ComplexFloatValue lhs,
                                  ComplexFloatValue rhs,
                                  FloatControl control) {
    ComplexFloatResult result;
    if (!lhs.valid() || !rhs.valid() ||
        lhs.real.semantics != rhs.real.semantics) {
        result.error = lhs.valid() && rhs.valid()
            ? FloatError::FormatMismatch
            : FloatError::InvalidEncoding;
        return result;
    }
    FloatFormat format = lhs.real.semantics;
    auto calculate = [&](BinaryOperation operation,
                         FloatValue left,
                         FloatValue right) {
        FloatResult operation_result = binary(operation, left, right, control);
        result.status.merge(operation_result.status);
        if (!operation_result && result.error == FloatError::None) {
            result.error = operation_result.error;
        }
        return operation_result.value;
    };
    auto scale = [&](FloatValue value, int64_t exponent) {
        FloatResult scaled = scale_by_power_of_two(value, exponent, control);
        result.status.merge(scaled.status);
        if (!scaled && result.error == FloatError::None) {
            result.error = scaled.error;
        }
        return scaled.value;
    };

    DecodedFloat c_decoded = decode(rhs.real);
    DecodedFloat d_decoded = decode(rhs.imag);
    auto magnitude_exponent = [](const DecodedFloat& value) {
        if (value.classification == FloatClass::Zero) {
            return std::numeric_limits<int64_t>::min();
        }
        return static_cast<int64_t>(value.exponent) +
            static_cast<int64_t>(value.significand.bit_width()) - 1;
    };
    bool finite_denominator =
        c_decoded.classification != FloatClass::Invalid &&
        d_decoded.classification != FloatClass::Invalid &&
        !is_nan_class(c_decoded.classification) &&
        !is_nan_class(d_decoded.classification) &&
        c_decoded.classification != FloatClass::Infinity &&
        d_decoded.classification != FloatClass::Infinity;
    int64_t scale_exponent = 0;
    if (finite_denominator &&
        (c_decoded.classification != FloatClass::Zero ||
         d_decoded.classification != FloatClass::Zero)) {
        scale_exponent = std::max(magnitude_exponent(c_decoded),
                                  magnitude_exponent(d_decoded));
        rhs.real = scale(rhs.real, -scale_exponent);
        rhs.imag = scale(rhs.imag, -scale_exponent);
    }
    DecodedFloat a_decoded = decode(lhs.real);
    DecodedFloat b_decoded = decode(lhs.imag);
    bool finite_numerator =
        a_decoded.classification != FloatClass::Invalid &&
        b_decoded.classification != FloatClass::Invalid &&
        !is_nan_class(a_decoded.classification) &&
        !is_nan_class(b_decoded.classification) &&
        a_decoded.classification != FloatClass::Infinity &&
        b_decoded.classification != FloatClass::Infinity;
    int64_t numerator_scale_exponent = 0;
    if (finite_numerator &&
        (a_decoded.classification != FloatClass::Zero ||
         b_decoded.classification != FloatClass::Zero)) {
        numerator_scale_exponent =
            std::max(magnitude_exponent(a_decoded),
                     magnitude_exponent(b_decoded));
        lhs.real = scale(lhs.real, -numerator_scale_exponent);
        lhs.imag = scale(lhs.imag, -numerator_scale_exponent);
    }

    FloatValue cc = calculate(BinaryOperation::Multiply,
                              rhs.real, rhs.real);
    FloatValue dd = calculate(BinaryOperation::Multiply,
                              rhs.imag, rhs.imag);
    FloatValue denominator = calculate(BinaryOperation::Add, cc, dd);
    FloatValue ac = calculate(BinaryOperation::Multiply,
                              lhs.real, rhs.real);
    FloatValue bd = calculate(BinaryOperation::Multiply,
                              lhs.imag, rhs.imag);
    FloatValue bc = calculate(BinaryOperation::Multiply,
                              lhs.imag, rhs.real);
    FloatValue ad = calculate(BinaryOperation::Multiply,
                              lhs.real, rhs.imag);
    result.value.real = calculate(
        BinaryOperation::Divide,
        calculate(BinaryOperation::Add, ac, bd), denominator);
    result.value.imag = calculate(
        BinaryOperation::Divide,
        calculate(BinaryOperation::Subtract, bc, ad), denominator);
    int64_t result_scale = numerator_scale_exponent - scale_exponent;
    if (finite_denominator && result_scale != 0) {
        result.value.real = scale(result.value.real, result_scale);
        result.value.imag = scale(result.value.imag, result_scale);
    }
    if (result.error != FloatError::None ||
        !is_nan(result.value.real) || !is_nan(result.value.imag)) {
        return result;
    }

    bool denominator_zero = is_zero(rhs.real) && is_zero(rhs.imag);
    bool numerator_has_number = !is_nan(lhs.real) || !is_nan(lhs.imag);
    if (denominator_zero && numerator_has_number) {
        FloatValue signed_infinity = infinity(
            format, is_negative(rhs.real));
        result.value.real = calculate(BinaryOperation::Multiply,
                                      signed_infinity, lhs.real);
        result.value.imag = calculate(BinaryOperation::Multiply,
                                      signed_infinity, lhs.imag);
        return result;
    }
    bool numerator_infinite = is_infinity(lhs.real) || is_infinity(lhs.imag);
    if (numerator_infinite && finite_denominator) {
        auto boxed = [&](FloatValue value) {
            FloatValue magnitude = is_infinity(value)
                ? from_integer(1, 1, false, format).value
                : zero(format);
            return is_negative(value) ? negate(magnitude) : magnitude;
        };
        lhs.real = boxed(lhs.real);
        lhs.imag = boxed(lhs.imag);
        FloatValue positive_infinity = infinity(format);
        result.value.real = calculate(
            BinaryOperation::Multiply, positive_infinity,
            calculate(BinaryOperation::Add,
                      calculate(BinaryOperation::Multiply,
                                lhs.real, rhs.real),
                      calculate(BinaryOperation::Multiply,
                                lhs.imag, rhs.imag)));
        result.value.imag = calculate(
            BinaryOperation::Multiply, positive_infinity,
            calculate(BinaryOperation::Subtract,
                      calculate(BinaryOperation::Multiply,
                                lhs.imag, rhs.real),
                      calculate(BinaryOperation::Multiply,
                                lhs.real, rhs.imag)));
        return result;
    }
    bool denominator_infinite =
        is_infinity(rhs.real) || is_infinity(rhs.imag);
    bool numerator_finite = !is_infinity(lhs.real) &&
        !is_infinity(lhs.imag) && !is_nan(lhs.real) && !is_nan(lhs.imag);
    if (denominator_infinite && numerator_finite) {
        auto boxed = [&](FloatValue value) {
            FloatValue magnitude = is_infinity(value)
                ? from_integer(1, 1, false, format).value
                : zero(format);
            return is_negative(value) ? negate(magnitude) : magnitude;
        };
        rhs.real = boxed(rhs.real);
        rhs.imag = boxed(rhs.imag);
        FloatValue positive_zero = zero(format);
        result.value.real = calculate(
            BinaryOperation::Multiply, positive_zero,
            calculate(BinaryOperation::Add,
                      calculate(BinaryOperation::Multiply,
                                lhs.real, rhs.real),
                      calculate(BinaryOperation::Multiply,
                                lhs.imag, rhs.imag)));
        result.value.imag = calculate(
            BinaryOperation::Multiply, positive_zero,
            calculate(BinaryOperation::Subtract,
                      calculate(BinaryOperation::Multiply,
                                lhs.imag, rhs.real),
                      calculate(BinaryOperation::Multiply,
                                lhs.real, rhs.imag)));
    }
    return result;
}

FloatCompareResult compare(FloatValue lhs, FloatValue rhs) {
    FloatCompareResult result;
    if (lhs.semantics != rhs.semantics) {
        result.error = FloatError::FormatMismatch;
        return result;
    }
    DecodedFloat left = decode(lhs);
    DecodedFloat right = decode(rhs);
    if (left.classification == FloatClass::Invalid ||
        right.classification == FloatClass::Invalid) {
        result.error = FloatError::InvalidEncoding;
        return result;
    }
    if (is_nan_class(left.classification) ||
        is_nan_class(right.classification)) {
        result.value = CompareResult::Unordered;
        if (left.classification == FloatClass::SignalingNaN ||
            right.classification == FloatClass::SignalingNaN) {
            result.status.set(FloatStatusFlag::Invalid);
        }
        return result;
    }
    if (left.classification == FloatClass::Zero &&
        right.classification == FloatClass::Zero) {
        result.value = CompareResult::Equal;
        return result;
    }
    if (left.negative != right.negative) {
        result.value = left.negative ? CompareResult::Less
                                     : CompareResult::Greater;
        return result;
    }
    auto magnitude_compare = [&]() {
        if (left.classification == FloatClass::Infinity ||
            right.classification == FloatClass::Infinity) {
            if (left.classification == right.classification) {
                return 0;
            }
            return left.classification == FloatClass::Infinity ? 1 : -1;
        }
        if (left.classification == FloatClass::Zero ||
            right.classification == FloatClass::Zero) {
            if (left.classification == right.classification) {
                return 0;
            }
            return left.classification == FloatClass::Zero ? -1 : 1;
        }
        return compare_scaled(left.significand, left.exponent,
                              right.significand, right.exponent);
    };
    int ordering = magnitude_compare();
    if (left.negative) {
        ordering = -ordering;
    }
    result.value = ordering < 0 ? CompareResult::Less
        : ordering > 0 ? CompareResult::Greater
                       : CompareResult::Equal;
    return result;
}

FloatResult from_integer(unsigned __int128 bits,
                         uint16_t bit_width,
                         bool is_signed,
                         FloatFormat format,
                         FloatControl control) {
    if (!descriptor(format)) {
        return error_result(FloatError::InvalidFormat);
    }
    if (bit_width == 0 || bit_width > 128) {
        return error_result(FloatError::InvalidIntegerWidth);
    }
    uint128_t mask = low_mask(bit_width);
    bits &= mask;
    bool negative = is_signed &&
        (bits & (uint128_t{1} << (bit_width - 1))) != 0;
    uint128_t magnitude = negative ? ((~bits + 1) & mask) : bits;
    return round_rational(negative, BigUInt(magnitude), BigUInt(1), 0,
                          format, control);
}

FloatIntegerResult to_integer(FloatValue value,
                              uint16_t bit_width,
                              bool is_signed) {
    FloatIntegerResult result;
    if (bit_width == 0 || bit_width > 128) {
        result.error = FloatError::InvalidIntegerWidth;
        return result;
    }
    DecodedFloat decoded = decode(value);
    if (decoded.classification == FloatClass::Invalid) {
        result.error = FloatError::InvalidEncoding;
        return result;
    }
    if (decoded.classification == FloatClass::Infinity ||
        is_nan_class(decoded.classification)) {
        result.error = FloatError::IntegerOutOfRange;
        result.status.set(FloatStatusFlag::Invalid);
        return result;
    }
    BigUInt magnitude = decoded.significand;
    bool discarded = false;
    if (decoded.exponent >= 0) {
        magnitude = magnitude.shifted_left(
            static_cast<size_t>(decoded.exponent));
    } else {
        magnitude = magnitude.shifted_right(
            static_cast<size_t>(-decoded.exponent), &discarded);
    }
    if (discarded) {
        result.status.set(FloatStatusFlag::Inexact);
    }

    BigUInt limit;
    if (is_signed) {
        limit = BigUInt(uint128_t{1} << (bit_width - 1));
        BigUInt positive_limit = limit;
        positive_limit.subtract(BigUInt(1));
        if ((!decoded.negative && magnitude.compare(positive_limit) > 0) ||
            (decoded.negative && magnitude.compare(limit) > 0)) {
            result.error = FloatError::IntegerOutOfRange;
            result.status.set(FloatStatusFlag::Invalid);
            return result;
        }
    } else {
        if (decoded.negative && !magnitude.is_zero()) {
            result.error = FloatError::IntegerOutOfRange;
            result.status.set(FloatStatusFlag::Invalid);
            return result;
        }
        limit = BigUInt(low_mask(bit_width));
        if (magnitude.compare(limit) > 0) {
            result.error = FloatError::IntegerOutOfRange;
            result.status.set(FloatStatusFlag::Invalid);
            return result;
        }
    }
    uint128_t raw = magnitude.to_u128() & low_mask(bit_width);
    if (decoded.negative && raw != 0) {
        raw = (~raw + 1) & low_mask(bit_width);
    }
    result.value = raw;
    return result;
}

FloatClass classify(FloatValue value) {
    return decode(value).classification;
}

bool is_zero(FloatValue value) {
    return classify(value) == FloatClass::Zero;
}

bool is_nan(FloatValue value) {
    FloatClass value_class = classify(value);
    return value_class == FloatClass::QuietNaN ||
        value_class == FloatClass::SignalingNaN;
}

bool is_infinity(FloatValue value) {
    return classify(value) == FloatClass::Infinity;
}

bool is_negative(FloatValue value) {
    const FloatFormatDescriptor* fmt = descriptor(value.semantics);
    return fmt && value.canonical() && sign_field(value, *fmt);
}

std::string bit_pattern_hex(FloatValue value) {
    if (!value.canonical()) {
        return {};
    }
    std::ostringstream out;
    out << std::hex << std::nouppercase << std::setfill('0');
    switch (value.semantics) {
        case FloatFormat::IEEEBinary16:
            out << std::setw(4) << static_cast<uint16_t>(value.low_bits);
            break;
        case FloatFormat::IEEEBinary32:
            out << std::setw(8) << static_cast<uint32_t>(value.low_bits);
            break;
        case FloatFormat::IEEEBinary64:
            out << std::setw(16) << value.low_bits;
            break;
        case FloatFormat::X87Extended80:
            out << std::setw(4) << static_cast<uint16_t>(value.high_bits)
                << std::setw(16) << value.low_bits;
            break;
        case FloatFormat::IEEEBinary128:
            out << std::setw(16) << value.high_bits
                << std::setw(16) << value.low_bits;
            break;
        case FloatFormat::Invalid:
            break;
    }
    return out.str();
}

std::string hex_display(FloatValue value) {
    DecodedFloat decoded = decode(value);
    if (decoded.classification == FloatClass::Invalid) {
        return "<invalid-floating-value>";
    }
    if (is_nan_class(decoded.classification)) {
        return (decoded.negative ? "-nan(0x" : "nan(0x") +
            bit_pattern_hex(value) + ")";
    }
    if (decoded.classification == FloatClass::Infinity) {
        return decoded.negative ? "-inf" : "inf";
    }
    if (decoded.classification == FloatClass::Zero) {
        return decoded.negative ? "-0x0p0" : "0x0p0";
    }
    return std::string(decoded.negative ? "-0x" : "0x") +
        decoded.significand.to_hex() + "p" +
        std::to_string(decoded.exponent);
}

std::string display(FloatValue value) {
    DecodedFloat decoded = decode(value);
    const FloatFormatDescriptor* fmt = descriptor(value.semantics);
    if (!fmt || decoded.classification == FloatClass::Invalid) {
        return "<invalid-floating-value>";
    }
    if (is_nan_class(decoded.classification)) {
        return (decoded.negative ? "-nan(0x" : "nan(0x") +
            bit_pattern_hex(value) + ")";
    }
    if (decoded.classification == FloatClass::Infinity) {
        return decoded.negative ? "-inf" : "inf";
    }
    if (decoded.classification == FloatClass::Zero) {
        return decoded.negative ? "-0" : "0";
    }

    BigUInt decimal_integer = decoded.significand;
    size_t decimal_scale = 0;
    if (decoded.exponent >= 0) {
        decimal_integer = decimal_integer.shifted_left(
            static_cast<size_t>(decoded.exponent));
    } else {
        decimal_scale = static_cast<size_t>(-decoded.exponent);
        decimal_integer = BigUInt::multiply(decimal_integer,
                                             power_of_five(decimal_scale));
    }
    std::string exact_digits = decimal_integer.to_decimal();
    int64_t scientific_exponent =
        static_cast<int64_t>(exact_digits.size()) -
        static_cast<int64_t>(decimal_scale) - 1;
    size_t max_digits =
        (static_cast<size_t>(fmt->precision) * 30103 + 99999) / 100000 + 1;

    for (size_t count = 1; count <= max_digits; ++count) {
        std::string prefix = exact_digits.substr(0, std::min(count,
                                                              exact_digits.size()));
        if (prefix.size() < count) {
            prefix.append(count - prefix.size(), '0');
        }
        bool tail_nonzero = false;
        if (count < exact_digits.size()) {
            tail_nonzero = std::any_of(exact_digits.begin() + count,
                                       exact_digits.end(),
                                       [](char digit) { return digit != '0'; });
        }
        std::vector<std::string> coefficients;
        coefficients.push_back(prefix);
        if (tail_nonzero) {
            coefficients.push_back(increment_decimal(prefix));
            char first_discarded = exact_digits[count];
            bool later_nonzero = std::any_of(exact_digits.begin() + count + 1,
                                             exact_digits.end(),
                                             [](char digit) {
                                                 return digit != '0';
                                             });
            bool round_up = first_discarded > '5' ||
                (first_discarded == '5' &&
                 (later_nonzero || ((prefix.back() - '0') & 1) != 0));
            coefficients.push_back(round_up ? increment_decimal(prefix)
                                            : prefix);
        }
        std::sort(coefficients.begin(), coefficients.end());
        coefficients.erase(std::unique(coefficients.begin(), coefficients.end()),
                           coefficients.end());

        std::string best;
        for (std::string coefficient : coefficients) {
            int64_t candidate_exponent = scientific_exponent;
            if (coefficient.size() > count) {
                coefficient.pop_back();
                ++candidate_exponent;
            }
            std::string candidate = candidate_spelling(
                coefficient, candidate_exponent, decoded.negative);
            FloatParseResult parsed = parse(candidate, value.semantics);
            if (parsed && parsed.value == value &&
                (best.empty() || candidate.size() < best.size() ||
                 (candidate.size() == best.size() && candidate < best))) {
                best = std::move(candidate);
            }
        }
        if (!best.empty()) {
            return best;
        }
    }
    return hex_display(value);
}

} // namespace aburi::numeric
