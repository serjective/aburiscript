#ifndef ABURI_ABI_ENDIAN_H
#define ABURI_ABI_ENDIAN_H

#include <cstddef>
#include <cstdint>
#include <cstring>

#include "target_info.h"

namespace aburi::abi {

struct ScalarBits {
    uint64_t low = 0;
    uint64_t high = 0;
};

inline void write_scalar_bits(uint8_t* out,
                              size_t size_bytes,
                              uint64_t low,
                              uint64_t high,
                              EndiannessKind order,
                              uint8_t fill = 0x00) {
    for (size_t index = 0; index < size_bytes; ++index) {
        uint8_t byte;
        if (index < 8) {
            byte = static_cast<uint8_t>((low >> (index * 8)) & 0xff);
        } else if (index < 16) {
            byte = static_cast<uint8_t>((high >> ((index - 8) * 8)) & 0xff);
        } else {
            byte = fill;
        }
        size_t position =
            order == EndiannessKind::Big ? size_bytes - 1 - index : index;
        out[position] = byte;
    }
}

inline ScalarBits read_scalar_bits(const uint8_t* in,
                                   size_t size_bytes,
                                   EndiannessKind order) {
    ScalarBits bits;
    for (size_t index = 0; index < size_bytes && index < 16; ++index) {
        size_t position =
            order == EndiannessKind::Big ? size_bytes - 1 - index : index;
        uint64_t byte = in[position];
        if (index < 8) {
            bits.low |= byte << (index * 8);
        } else {
            bits.high |= byte << ((index - 8) * 8);
        }
    }
    return bits;
}

inline void write_f32_bits(uint8_t* out, float value, EndiannessKind order) {
    uint32_t bits;
    std::memcpy(&bits, &value, sizeof(bits));
    write_scalar_bits(out, sizeof(bits), bits, 0, order);
}

inline void write_f64_bits(uint8_t* out, double value, EndiannessKind order) {
    uint64_t bits;
    std::memcpy(&bits, &value, sizeof(bits));
    write_scalar_bits(out, sizeof(bits), bits, 0, order);
}

inline float read_f32_bits(const uint8_t* in, EndiannessKind order) {
    uint32_t bits = static_cast<uint32_t>(read_scalar_bits(in, 4, order).low);
    float value;
    std::memcpy(&value, &bits, sizeof(value));
    return value;
}

inline double read_f64_bits(const uint8_t* in, EndiannessKind order) {
    uint64_t bits = read_scalar_bits(in, 8, order).low;
    double value;
    std::memcpy(&value, &bits, sizeof(value));
    return value;
}

} // namespace aburi::abi

#endif // ABURI_ABI_ENDIAN_H
