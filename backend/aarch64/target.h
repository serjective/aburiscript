#ifndef ABURI_BACKEND_AARCH64_TARGET_H
#define ABURI_BACKEND_AARCH64_TARGET_H

#include <cstdint>

#include "../common/regalloc.h"

namespace aburi::backend::aarch64 {

inline constexpr uint32_t X0 = 0;
inline constexpr uint32_t X1 = 1;
inline constexpr uint32_t X2 = 2;
inline constexpr uint32_t X8 = 8;
inline constexpr uint32_t X16 = 16;
inline constexpr uint32_t X17 = 17;
inline constexpr uint32_t X18 = 18;
inline constexpr uint32_t X19 = 19;
inline constexpr uint32_t X28 = 28;
inline constexpr uint32_t X29 = 29;
inline constexpr uint32_t X30 = 30;
inline constexpr uint32_t SP = 31;
inline constexpr uint32_t XZR = 32;
inline constexpr uint32_t V0 = 33;
inline constexpr uint32_t V7 = 40;
inline constexpr uint32_t V8 = 41;
inline constexpr uint32_t V15 = 48;
inline constexpr uint32_t V16 = 49;
inline constexpr uint32_t V28 = 61;
inline constexpr uint32_t V29 = 62;
inline constexpr uint32_t V30 = 63;
inline constexpr uint32_t V31 = 64;

inline constexpr uint32_t v(uint32_t n) { return V0 + n; }

inline bool is_fpr_index(uint32_t phys) { return phys >= V0 && phys <= V31; }

inline RegClass phys_reg_class(uint32_t phys) {
    return is_fpr_index(phys) ? RegClass::Fpr : RegClass::Gpr;
}

inline bool is_callee_saved_reg(uint32_t phys) {
    if (phys >= X19 && phys <= X28) {
        return true;
    }
    return phys >= V8 && phys <= V15;
}

const TargetRegInfo& reg_info();

} // namespace aburi::backend::aarch64

#endif // ABURI_BACKEND_AARCH64_TARGET_H
