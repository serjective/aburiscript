#ifndef ABURI_NUMERIC_INTEGER_VALUE_H
#define ABURI_NUMERIC_INTEGER_VALUE_H

#include <cstdint>
#include <limits>
#include <optional>
#include <string>

namespace aburi::numeric {

struct IntegerValue {
    uint64_t low_bits = 0;
    uint64_t high_bits = 0;
    uint16_t bit_width = 64;
    bool is_unsigned = false;

    static uint16_t normalized_width(uint16_t width) {
        if (width == 0) {
            return 1;
        }
        return width > 128 ? 128 : width;
    }

    static unsigned __int128 width_mask(uint16_t width) {
        width = normalized_width(width);
        if (width == 128) {
            return ~static_cast<unsigned __int128>(0);
        }
        return (static_cast<unsigned __int128>(1) << width) - 1;
    }

    static IntegerValue from_bits128(unsigned __int128 bits,
                                     uint16_t width,
                                     bool unsigned_value) {
        IntegerValue out;

        out.bit_width = width == 0 ? 1 : width;
        out.is_unsigned = unsigned_value;
        bits &= width_mask(width);
        out.low_bits = static_cast<uint64_t>(bits);
        out.high_bits = static_cast<uint64_t>(bits >> 64);
        return out;
    }

    static IntegerValue from_words(uint64_t low,
                                   uint64_t high,
                                   uint16_t width,
                                   bool unsigned_value) {
        return from_bits128(
            (static_cast<unsigned __int128>(high) << 64) | low,
            width,
            unsigned_value);
    }

    static IntegerValue from_unsigned(unsigned __int128 value,
                                      uint16_t width) {
        return from_bits128(value, width, true);
    }

    static IntegerValue from_signed(__int128 value, uint16_t width) {
        return from_bits128(static_cast<unsigned __int128>(value),
                            width,
                            false);
    }

    unsigned __int128 to_unsigned_u128() const {
        unsigned __int128 bits =
            (static_cast<unsigned __int128>(high_bits) << 64) | low_bits;
        return bits & width_mask(bit_width);
    }

    __int128 to_signed_i128() const {
        unsigned __int128 bits = to_unsigned_u128();
        uint16_t width = normalized_width(bit_width);
        if (width < 128 &&
            (bits & (static_cast<unsigned __int128>(1) << (width - 1)))) {
            bits |= ~width_mask(width);
        }
        return static_cast<__int128>(bits);
    }

    uint64_t to_unsigned_u64() const {
        return low_bits;
    }

    int64_t to_signed_i64() const {
        return static_cast<int64_t>(to_signed_i128());
    }

    std::optional<uint64_t> try_as_uint64() const {
        if (is_unsigned) {
            return high_bits == 0 ? std::optional<uint64_t>(low_bits)
                                  : std::nullopt;
        }
        __int128 value = to_signed_i128();
        if (value < 0 ||
            static_cast<unsigned __int128>(value) >
                std::numeric_limits<uint64_t>::max()) {
            return std::nullopt;
        }
        return static_cast<uint64_t>(value);
    }

    std::optional<int64_t> try_as_int64() const {
        if (is_unsigned) {
            unsigned __int128 value = to_unsigned_u128();
            if (value > static_cast<unsigned __int128>(
                            std::numeric_limits<int64_t>::max())) {
                return std::nullopt;
            }
            return static_cast<int64_t>(value);
        }
        __int128 value = to_signed_i128();
        if (value < std::numeric_limits<int64_t>::min() ||
            value > std::numeric_limits<int64_t>::max()) {
            return std::nullopt;
        }
        return static_cast<int64_t>(value);
    }

    IntegerValue cast(uint16_t new_width, bool new_unsigned) const {
        unsigned __int128 value = is_unsigned
            ? to_unsigned_u128()
            : static_cast<unsigned __int128>(to_signed_i128());
        return from_bits128(value, new_width, new_unsigned);
    }

    bool canonical() const {
        return bit_width >= 1 && bit_width <= 128 &&
            *this == from_words(low_bits, high_bits, bit_width, is_unsigned);
    }

    bool is_zero() const {
        return low_bits == 0 && high_bits == 0;
    }

    bool is_negative() const {
        return !is_unsigned && to_signed_i128() < 0;
    }

    std::string decimal() const {
        bool negative = is_negative();
        unsigned __int128 magnitude;
        if (negative) {
            unsigned __int128 bits = to_unsigned_u128();
            magnitude = (~bits + 1) & width_mask(bit_width);
        } else {
            magnitude = to_unsigned_u128();
        }
        char buffer[40];
        char* end = buffer + sizeof(buffer);
        char* current = end;
        do {
            unsigned digit = static_cast<unsigned>(magnitude % 10);
            *--current = static_cast<char>('0' + digit);
            magnitude /= 10;
        } while (magnitude != 0);
        std::string out;
        if (negative) {
            out.push_back('-');
        }
        out.append(current, end);
        return out;
    }

    friend bool operator==(const IntegerValue&, const IntegerValue&) = default;
};

} // namespace aburi::numeric

#endif // ABURI_NUMERIC_INTEGER_VALUE_H
