#ifndef ABURI_BUILTIN_ARM_NEON_H
#define ABURI_BUILTIN_ARM_NEON_H

#include <stdint.h>

typedef float float32_t;
typedef double float64_t;

typedef int8_t int8x8_t __attribute__((vector_size(8)));
typedef int8_t int8x16_t __attribute__((vector_size(16)));
typedef int16_t int16x4_t __attribute__((vector_size(8)));
typedef int16_t int16x8_t __attribute__((vector_size(16)));
typedef int32_t int32x2_t __attribute__((vector_size(8)));
typedef int32_t int32x4_t __attribute__((vector_size(16)));
typedef int64_t int64x1_t __attribute__((vector_size(8)));
typedef int64_t int64x2_t __attribute__((vector_size(16)));

typedef uint8_t uint8x8_t __attribute__((vector_size(8)));
typedef uint8_t uint8x16_t __attribute__((vector_size(16)));
typedef uint16_t uint16x4_t __attribute__((vector_size(8)));
typedef uint16_t uint16x8_t __attribute__((vector_size(16)));
typedef uint32_t uint32x2_t __attribute__((vector_size(8)));
typedef uint32_t uint32x4_t __attribute__((vector_size(16)));
typedef uint64_t uint64x1_t __attribute__((vector_size(8)));
typedef uint64_t uint64x2_t __attribute__((vector_size(16)));

typedef struct {
    uint32x4_t val[2];
} uint32x4x2_t;

typedef float32_t float32x2_t __attribute__((vector_size(8)));
typedef float32_t float32x4_t __attribute__((vector_size(16)));
typedef float64_t float64x1_t __attribute__((vector_size(8)));
typedef float64_t float64x2_t __attribute__((vector_size(16)));

typedef uint8_t poly8_t;
typedef uint16_t poly16_t;
typedef uint64_t poly64_t;
typedef uint8_t poly8x8_t __attribute__((vector_size(8)));
typedef uint8_t poly8x16_t __attribute__((vector_size(16)));
typedef uint16_t poly16x4_t __attribute__((vector_size(8)));
typedef uint16_t poly16x8_t __attribute__((vector_size(16)));
typedef uint64_t poly64x1_t __attribute__((vector_size(8)));
typedef uint64_t poly64x2_t __attribute__((vector_size(16)));
typedef uint64_t poly128_t __attribute__((vector_size(16)));

static inline uint8x16_t vld1q_u8(const uint8_t* ptr) {
    return (uint8x16_t){ptr[0], ptr[1], ptr[2], ptr[3], ptr[4], ptr[5], ptr[6], ptr[7],
                        ptr[8], ptr[9], ptr[10], ptr[11], ptr[12], ptr[13], ptr[14], ptr[15]};
}

static inline uint8x8_t vld1_u8(const uint8_t* ptr) {
    return (uint8x8_t){ptr[0], ptr[1], ptr[2], ptr[3], ptr[4], ptr[5], ptr[6], ptr[7]};
}

static inline uint32x4_t vld1q_u32(const uint32_t* ptr) {
    return (uint32x4_t){ptr[0], ptr[1], ptr[2], ptr[3]};
}

static inline void vst1q_u32(uint32_t* ptr, uint32x4_t value) {
    ptr[0] = value[0];
    ptr[1] = value[1];
    ptr[2] = value[2];
    ptr[3] = value[3];
}

static inline void vst1q_u8(uint8_t* ptr, uint8x16_t value) {
    ptr[0] = value[0];
    ptr[1] = value[1];
    ptr[2] = value[2];
    ptr[3] = value[3];
    ptr[4] = value[4];
    ptr[5] = value[5];
    ptr[6] = value[6];
    ptr[7] = value[7];
    ptr[8] = value[8];
    ptr[9] = value[9];
    ptr[10] = value[10];
    ptr[11] = value[11];
    ptr[12] = value[12];
    ptr[13] = value[13];
    ptr[14] = value[14];
    ptr[15] = value[15];
}

static inline uint64x2_t vreinterpretq_u64_u8(uint8x16_t value) {
    union {
        uint8x16_t in;
        uint64x2_t out;
    } bits = { value };
    return bits.out;
}

static inline uint32x4_t vreinterpretq_u32_u64(uint64x2_t value) {
    union {
        uint64x2_t in;
        uint32x4_t out;
    } bits = { value };
    return bits.out;
}

static inline uint64x2_t vreinterpretq_u64_u32(uint32x4_t value) {
    union {
        uint32x4_t in;
        uint64x2_t out;
    } bits = { value };
    return bits.out;
}

static inline uint32x2_t vget_low_u32(uint32x4_t value) {
    return (uint32x2_t){value[0], value[1]};
}

static inline uint32x2_t vget_high_u32(uint32x4_t value) {
    return (uint32x2_t){value[2], value[3]};
}

static inline uint64x2_t vaddq_u64(uint64x2_t lhs, uint64x2_t rhs) {
    return (uint64x2_t){lhs[0] + rhs[0], lhs[1] + rhs[1]};
}

static inline uint64x2_t veorq_u64(uint64x2_t lhs, uint64x2_t rhs) {
    return (uint64x2_t){lhs[0] ^ rhs[0], lhs[1] ^ rhs[1]};
}

static inline uint64x2_t vextq_u64(uint64x2_t lhs, uint64x2_t rhs, const int lane) {
    if (lane <= 0) {
        return lhs;
    }
    return (uint64x2_t){lhs[1], rhs[0]};
}

static inline uint8x16_t vextq_u8(uint8x16_t lhs, uint8x16_t rhs, const int lane) {
    uint8x16_t result = (uint8x16_t){0};
    for (int i = 0; i < 16; ++i) {
        int source = i + lane;
        result[i] = source < 16 ? lhs[source] : rhs[source - 16];
    }
    return result;
}

static inline uint32x4_t vshlq_n_u32(uint32x4_t value, const int amount) {
    return (uint32x4_t){
        value[0] << amount,
        value[1] << amount,
        value[2] << amount,
        value[3] << amount
    };
}

static inline uint32x4_t vshrq_n_u32(uint32x4_t value, const int amount) {
    return (uint32x4_t){
        value[0] >> amount,
        value[1] >> amount,
        value[2] >> amount,
        value[3] >> amount
    };
}

static inline int8x16_t vshrq_n_s8(int8x16_t value, const int amount) {
    return (int8x16_t){
        (int8_t)(value[0] >> amount),
        (int8_t)(value[1] >> amount),
        (int8_t)(value[2] >> amount),
        (int8_t)(value[3] >> amount),
        (int8_t)(value[4] >> amount),
        (int8_t)(value[5] >> amount),
        (int8_t)(value[6] >> amount),
        (int8_t)(value[7] >> amount),
        (int8_t)(value[8] >> amount),
        (int8_t)(value[9] >> amount),
        (int8_t)(value[10] >> amount),
        (int8_t)(value[11] >> amount),
        (int8_t)(value[12] >> amount),
        (int8_t)(value[13] >> amount),
        (int8_t)(value[14] >> amount),
        (int8_t)(value[15] >> amount)
    };
}

static inline uint64x2_t vshrq_n_u64(uint64x2_t value, const int amount) {
    return (uint64x2_t){value[0] >> amount, value[1] >> amount};
}

static inline uint32x2_t vmovn_u64(uint64x2_t value) {
    return (uint32x2_t){(uint32_t)value[0], (uint32_t)value[1]};
}

static inline uint32x2_t vshrn_n_u64(uint64x2_t value, const int amount) {
    return (uint32x2_t){(uint32_t)(value[0] >> amount), (uint32_t)(value[1] >> amount)};
}

static inline uint32x2_t vdup_n_u32(uint32_t value) {
    return (uint32x2_t){value, value};
}

static inline uint32x4_t vdupq_n_u32(uint32_t value) {
    return (uint32x4_t){value, value, value, value};
}

static inline uint8x16_t vdupq_n_u8(uint8_t value) {
    return (uint8x16_t){
        value, value, value, value, value, value, value, value,
        value, value, value, value, value, value, value, value
    };
}

static inline uint64x2_t vdupq_n_u64(uint64_t value) {
    return (uint64x2_t){value, value};
}

static inline uint8x16_t vandq_u8(uint8x16_t lhs, uint8x16_t rhs) {
    return (uint8x16_t){
        (uint8_t)(lhs[0] & rhs[0]),
        (uint8_t)(lhs[1] & rhs[1]),
        (uint8_t)(lhs[2] & rhs[2]),
        (uint8_t)(lhs[3] & rhs[3]),
        (uint8_t)(lhs[4] & rhs[4]),
        (uint8_t)(lhs[5] & rhs[5]),
        (uint8_t)(lhs[6] & rhs[6]),
        (uint8_t)(lhs[7] & rhs[7]),
        (uint8_t)(lhs[8] & rhs[8]),
        (uint8_t)(lhs[9] & rhs[9]),
        (uint8_t)(lhs[10] & rhs[10]),
        (uint8_t)(lhs[11] & rhs[11]),
        (uint8_t)(lhs[12] & rhs[12]),
        (uint8_t)(lhs[13] & rhs[13]),
        (uint8_t)(lhs[14] & rhs[14]),
        (uint8_t)(lhs[15] & rhs[15])
    };
}

static inline uint8x16_t vorrq_u8(uint8x16_t lhs, uint8x16_t rhs) {
    return (uint8x16_t){
        (uint8_t)(lhs[0] | rhs[0]),
        (uint8_t)(lhs[1] | rhs[1]),
        (uint8_t)(lhs[2] | rhs[2]),
        (uint8_t)(lhs[3] | rhs[3]),
        (uint8_t)(lhs[4] | rhs[4]),
        (uint8_t)(lhs[5] | rhs[5]),
        (uint8_t)(lhs[6] | rhs[6]),
        (uint8_t)(lhs[7] | rhs[7]),
        (uint8_t)(lhs[8] | rhs[8]),
        (uint8_t)(lhs[9] | rhs[9]),
        (uint8_t)(lhs[10] | rhs[10]),
        (uint8_t)(lhs[11] | rhs[11]),
        (uint8_t)(lhs[12] | rhs[12]),
        (uint8_t)(lhs[13] | rhs[13]),
        (uint8_t)(lhs[14] | rhs[14]),
        (uint8_t)(lhs[15] | rhs[15])
    };
}

static inline uint32x4_t vorrq_u32(uint32x4_t lhs, uint32x4_t rhs) {
    return (uint32x4_t){
        lhs[0] | rhs[0],
        lhs[1] | rhs[1],
        lhs[2] | rhs[2],
        lhs[3] | rhs[3]
    };
}

static inline uint8x16_t vaddq_u8(uint8x16_t lhs, uint8x16_t rhs) {
    return (uint8x16_t){
        (uint8_t)(lhs[0] + rhs[0]),
        (uint8_t)(lhs[1] + rhs[1]),
        (uint8_t)(lhs[2] + rhs[2]),
        (uint8_t)(lhs[3] + rhs[3]),
        (uint8_t)(lhs[4] + rhs[4]),
        (uint8_t)(lhs[5] + rhs[5]),
        (uint8_t)(lhs[6] + rhs[6]),
        (uint8_t)(lhs[7] + rhs[7]),
        (uint8_t)(lhs[8] + rhs[8]),
        (uint8_t)(lhs[9] + rhs[9]),
        (uint8_t)(lhs[10] + rhs[10]),
        (uint8_t)(lhs[11] + rhs[11]),
        (uint8_t)(lhs[12] + rhs[12]),
        (uint8_t)(lhs[13] + rhs[13]),
        (uint8_t)(lhs[14] + rhs[14]),
        (uint8_t)(lhs[15] + rhs[15])
    };
}

static inline uint8x16_t vceqq_u8(uint8x16_t lhs, uint8x16_t rhs) {
    return (uint8x16_t){
        (uint8_t)(lhs[0] == rhs[0] ? 0xFFu : 0u),
        (uint8_t)(lhs[1] == rhs[1] ? 0xFFu : 0u),
        (uint8_t)(lhs[2] == rhs[2] ? 0xFFu : 0u),
        (uint8_t)(lhs[3] == rhs[3] ? 0xFFu : 0u),
        (uint8_t)(lhs[4] == rhs[4] ? 0xFFu : 0u),
        (uint8_t)(lhs[5] == rhs[5] ? 0xFFu : 0u),
        (uint8_t)(lhs[6] == rhs[6] ? 0xFFu : 0u),
        (uint8_t)(lhs[7] == rhs[7] ? 0xFFu : 0u),
        (uint8_t)(lhs[8] == rhs[8] ? 0xFFu : 0u),
        (uint8_t)(lhs[9] == rhs[9] ? 0xFFu : 0u),
        (uint8_t)(lhs[10] == rhs[10] ? 0xFFu : 0u),
        (uint8_t)(lhs[11] == rhs[11] ? 0xFFu : 0u),
        (uint8_t)(lhs[12] == rhs[12] ? 0xFFu : 0u),
        (uint8_t)(lhs[13] == rhs[13] ? 0xFFu : 0u),
        (uint8_t)(lhs[14] == rhs[14] ? 0xFFu : 0u),
        (uint8_t)(lhs[15] == rhs[15] ? 0xFFu : 0u)
    };
}

static inline uint32x4_t vceqq_u32(uint32x4_t lhs, uint32x4_t rhs) {
    return (uint32x4_t){
        lhs[0] == rhs[0] ? 0xFFFFFFFFu : 0u,
        lhs[1] == rhs[1] ? 0xFFFFFFFFu : 0u,
        lhs[2] == rhs[2] ? 0xFFFFFFFFu : 0u,
        lhs[3] == rhs[3] ? 0xFFFFFFFFu : 0u
    };
}

static inline uint8x16_t vcgtq_s8(int8x16_t lhs, int8x16_t rhs) {
    return (uint8x16_t){
        (uint8_t)(lhs[0] > rhs[0] ? 0xFFu : 0u),
        (uint8_t)(lhs[1] > rhs[1] ? 0xFFu : 0u),
        (uint8_t)(lhs[2] > rhs[2] ? 0xFFu : 0u),
        (uint8_t)(lhs[3] > rhs[3] ? 0xFFu : 0u),
        (uint8_t)(lhs[4] > rhs[4] ? 0xFFu : 0u),
        (uint8_t)(lhs[5] > rhs[5] ? 0xFFu : 0u),
        (uint8_t)(lhs[6] > rhs[6] ? 0xFFu : 0u),
        (uint8_t)(lhs[7] > rhs[7] ? 0xFFu : 0u),
        (uint8_t)(lhs[8] > rhs[8] ? 0xFFu : 0u),
        (uint8_t)(lhs[9] > rhs[9] ? 0xFFu : 0u),
        (uint8_t)(lhs[10] > rhs[10] ? 0xFFu : 0u),
        (uint8_t)(lhs[11] > rhs[11] ? 0xFFu : 0u),
        (uint8_t)(lhs[12] > rhs[12] ? 0xFFu : 0u),
        (uint8_t)(lhs[13] > rhs[13] ? 0xFFu : 0u),
        (uint8_t)(lhs[14] > rhs[14] ? 0xFFu : 0u),
        (uint8_t)(lhs[15] > rhs[15] ? 0xFFu : 0u)
    };
}

static inline uint8x16_t vminq_u8(uint8x16_t lhs, uint8x16_t rhs) {
    return (uint8x16_t){
        lhs[0] < rhs[0] ? lhs[0] : rhs[0],
        lhs[1] < rhs[1] ? lhs[1] : rhs[1],
        lhs[2] < rhs[2] ? lhs[2] : rhs[2],
        lhs[3] < rhs[3] ? lhs[3] : rhs[3],
        lhs[4] < rhs[4] ? lhs[4] : rhs[4],
        lhs[5] < rhs[5] ? lhs[5] : rhs[5],
        lhs[6] < rhs[6] ? lhs[6] : rhs[6],
        lhs[7] < rhs[7] ? lhs[7] : rhs[7],
        lhs[8] < rhs[8] ? lhs[8] : rhs[8],
        lhs[9] < rhs[9] ? lhs[9] : rhs[9],
        lhs[10] < rhs[10] ? lhs[10] : rhs[10],
        lhs[11] < rhs[11] ? lhs[11] : rhs[11],
        lhs[12] < rhs[12] ? lhs[12] : rhs[12],
        lhs[13] < rhs[13] ? lhs[13] : rhs[13],
        lhs[14] < rhs[14] ? lhs[14] : rhs[14],
        lhs[15] < rhs[15] ? lhs[15] : rhs[15]
    };
}

static inline uint8_t vminvq_u8(uint8x16_t value) {
    uint8_t result = value[0];
    for (int lane = 1; lane < 16; ++lane) {
        if (value[lane] < result) {
            result = value[lane];
        }
    }
    return result;
}

static inline uint8_t vmaxvq_u8(uint8x16_t value) {
    uint8_t result = value[0];
    for (int lane = 1; lane < 16; ++lane) {
        if (value[lane] > result) {
            result = value[lane];
        }
    }
    return result;
}

static inline uint16_t vaddvq_u16(uint16x8_t value) {
    return (uint16_t)(value[0] + value[1] + value[2] + value[3] +
                      value[4] + value[5] + value[6] + value[7]);
}

static inline uint8x16_t vzip1q_u8(uint8x16_t lhs, uint8x16_t rhs) {
    return (uint8x16_t){
        lhs[0], rhs[0], lhs[1], rhs[1], lhs[2], rhs[2], lhs[3], rhs[3],
        lhs[4], rhs[4], lhs[5], rhs[5], lhs[6], rhs[6], lhs[7], rhs[7]
    };
}

static inline uint8x16_t vzip2q_u8(uint8x16_t lhs, uint8x16_t rhs) {
    return (uint8x16_t){
        lhs[8], rhs[8], lhs[9], rhs[9], lhs[10], rhs[10], lhs[11], rhs[11],
        lhs[12], rhs[12], lhs[13], rhs[13], lhs[14], rhs[14], lhs[15], rhs[15]
    };
}

static inline uint8x16_t vuzp1q_u8(uint8x16_t lhs, uint8x16_t rhs) {
    return (uint8x16_t){
        lhs[0], lhs[2], lhs[4], lhs[6], lhs[8], lhs[10], lhs[12], lhs[14],
        rhs[0], rhs[2], rhs[4], rhs[6], rhs[8], rhs[10], rhs[12], rhs[14]
    };
}

static inline int8_t aburi_sat_sub_s8(int8_t lhs, int8_t rhs) {
    int value = (int)lhs - (int)rhs;
    if (value > 127) {
        value = 127;
    } else if (value < -128) {
        value = -128;
    }
    return (int8_t)value;
}

static inline int8x16_t vqsubq_s8(int8x16_t lhs, int8x16_t rhs) {
    return (int8x16_t){
        aburi_sat_sub_s8(lhs[0], rhs[0]),
        aburi_sat_sub_s8(lhs[1], rhs[1]),
        aburi_sat_sub_s8(lhs[2], rhs[2]),
        aburi_sat_sub_s8(lhs[3], rhs[3]),
        aburi_sat_sub_s8(lhs[4], rhs[4]),
        aburi_sat_sub_s8(lhs[5], rhs[5]),
        aburi_sat_sub_s8(lhs[6], rhs[6]),
        aburi_sat_sub_s8(lhs[7], rhs[7]),
        aburi_sat_sub_s8(lhs[8], rhs[8]),
        aburi_sat_sub_s8(lhs[9], rhs[9]),
        aburi_sat_sub_s8(lhs[10], rhs[10]),
        aburi_sat_sub_s8(lhs[11], rhs[11]),
        aburi_sat_sub_s8(lhs[12], rhs[12]),
        aburi_sat_sub_s8(lhs[13], rhs[13]),
        aburi_sat_sub_s8(lhs[14], rhs[14]),
        aburi_sat_sub_s8(lhs[15], rhs[15])
    };
}

static inline uint8_t aburi_popcount_u8(uint8_t value) {
    uint8_t count = 0;
    while (value != 0) {
        count = (uint8_t)(count + (value & 1u));
        value = (uint8_t)(value >> 1);
    }
    return count;
}

static inline uint8x8_t vcnt_u8(uint8x8_t value) {
    return (uint8x8_t){
        aburi_popcount_u8(value[0]),
        aburi_popcount_u8(value[1]),
        aburi_popcount_u8(value[2]),
        aburi_popcount_u8(value[3]),
        aburi_popcount_u8(value[4]),
        aburi_popcount_u8(value[5]),
        aburi_popcount_u8(value[6]),
        aburi_popcount_u8(value[7])
    };
}

static inline uint8x16_t vcntq_u8(uint8x16_t value) {
    return (uint8x16_t){
        aburi_popcount_u8(value[0]),
        aburi_popcount_u8(value[1]),
        aburi_popcount_u8(value[2]),
        aburi_popcount_u8(value[3]),
        aburi_popcount_u8(value[4]),
        aburi_popcount_u8(value[5]),
        aburi_popcount_u8(value[6]),
        aburi_popcount_u8(value[7]),
        aburi_popcount_u8(value[8]),
        aburi_popcount_u8(value[9]),
        aburi_popcount_u8(value[10]),
        aburi_popcount_u8(value[11]),
        aburi_popcount_u8(value[12]),
        aburi_popcount_u8(value[13]),
        aburi_popcount_u8(value[14]),
        aburi_popcount_u8(value[15])
    };
}

static inline uint8_t vaddv_u8(uint8x8_t value) {
    return (uint8_t)(value[0] + value[1] + value[2] + value[3] +
                     value[4] + value[5] + value[6] + value[7]);
}

static inline uint16x8_t vpaddlq_u8(uint8x16_t value) {
    return (uint16x8_t){
        (uint16_t)value[0] + (uint16_t)value[1],
        (uint16_t)value[2] + (uint16_t)value[3],
        (uint16_t)value[4] + (uint16_t)value[5],
        (uint16_t)value[6] + (uint16_t)value[7],
        (uint16_t)value[8] + (uint16_t)value[9],
        (uint16_t)value[10] + (uint16_t)value[11],
        (uint16_t)value[12] + (uint16_t)value[13],
        (uint16_t)value[14] + (uint16_t)value[15]
    };
}

static inline uint32x4_t vpaddlq_u16(uint16x8_t value) {
    return (uint32x4_t){
        (uint32_t)value[0] + (uint32_t)value[1],
        (uint32_t)value[2] + (uint32_t)value[3],
        (uint32_t)value[4] + (uint32_t)value[5],
        (uint32_t)value[6] + (uint32_t)value[7]
    };
}

static inline uint64x2_t vpadalq_u32(uint64x2_t acc, uint32x4_t value) {
    return (uint64x2_t){
        acc[0] + (uint64_t)value[0] + (uint64_t)value[1],
        acc[1] + (uint64_t)value[2] + (uint64_t)value[3]
    };
}

static inline uint64_t vaddvq_u64(uint64x2_t value) {
    return value[0] + value[1];
}

static inline uint64x2_t vmlal_u32(uint64x2_t acc, uint32x2_t lhs, uint32x2_t rhs) {
    return (uint64x2_t){
        acc[0] + (uint64_t)lhs[0] * (uint64_t)rhs[0],
        acc[1] + (uint64_t)lhs[1] * (uint64_t)rhs[1]
    };
}

static inline uint64x2_t vmlal_high_u32(uint64x2_t acc, uint32x4_t lhs, uint32x4_t rhs) {
    return (uint64x2_t){
        acc[0] + (uint64_t)lhs[2] * (uint64_t)rhs[2],
        acc[1] + (uint64_t)lhs[3] * (uint64_t)rhs[3]
    };
}

static inline uint32x4_t vmulq_u32(uint32x4_t lhs, uint32x4_t rhs) {
    return (uint32x4_t){
        lhs[0] * rhs[0],
        lhs[1] * rhs[1],
        lhs[2] * rhs[2],
        lhs[3] * rhs[3]
    };
}

static inline uint32x4x2_t vuzpq_u32(uint32x4_t lhs, uint32x4_t rhs) {
    uint32x4x2_t result;
    result.val[0] = (uint32x4_t){lhs[0], lhs[2], rhs[0], rhs[2]};
    result.val[1] = (uint32x4_t){lhs[1], lhs[3], rhs[1], rhs[3]};
    return result;
}

static inline uint32_t vmaxvq_u32(uint32x4_t value) {
    uint32_t result = value[0];
    if (value[1] > result) {
        result = value[1];
    }
    if (value[2] > result) {
        result = value[2];
    }
    if (value[3] > result) {
        result = value[3];
    }
    return result;
}

static inline uint8x16_t vqtbl1q_u8(uint8x16_t table, uint8x16_t index) {
    uint8x16_t result = (uint8x16_t){0};
    for (int lane = 0; lane < 16; ++lane) {
        uint8_t idx = index[lane];
        result[lane] = idx < 16 ? table[idx] : 0;
    }
    return result;
}

static inline uint8x16_t vaesdq_u8(uint8x16_t data, uint8x16_t key) {
    asm(".arch_extension aes\n\t"
        "aesd %0.16b, %1.16b" : "+w"(data) : "w"(key));
    return data;
}

static inline uint8x16_t vaeseq_u8(uint8x16_t data, uint8x16_t key) {
    asm(".arch_extension aes\n\t"
        "aese %0.16b, %1.16b" : "+w"(data) : "w"(key));
    return data;
}

static inline uint8x16_t vaesmcq_u8(uint8x16_t data) {
    asm(".arch_extension aes\n\t"
        "aesmc %0.16b, %1.16b" : "=w"(data) : "w"(data));
    return data;
}

static inline uint8x16_t vaesimcq_u8(uint8x16_t data) {
    asm(".arch_extension aes\n\t"
        "aesimc %0.16b, %1.16b" : "=w"(data) : "w"(data));
    return data;
}

static inline poly128_t vmull_p64(poly64_t lhs, poly64_t rhs) {
    poly128_t result;
    asm(".arch_extension aes\n\t"
        "pmull %0.1q, %1.1d, %2.1d" : "=w"(result) : "w"(lhs), "w"(rhs));
    return result;
}

#endif
