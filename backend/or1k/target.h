#ifndef ABURI_BACKEND_OR1K_TARGET_H
#define ABURI_BACKEND_OR1K_TARGET_H

#include <cstdint>

#include "../common/regalloc.h"

namespace aburi::backend::or1k {

inline constexpr uint32_t R0 = 0;
inline constexpr uint32_t SP = 1;
inline constexpr uint32_t FP = 2;
inline constexpr uint32_t R3 = 3;
inline constexpr uint32_t R8 = 8;
inline constexpr uint32_t LR = 9;
inline constexpr uint32_t TLS = 10;
inline constexpr uint32_t RV = 11;
inline constexpr uint32_t R12 = 12;
inline constexpr uint32_t R13 = 13;
inline constexpr uint32_t R15 = 15;

inline bool is_fpr_index(uint32_t) { return false; }

inline RegClass phys_reg_class(uint32_t) { return RegClass::Gpr; }

inline bool is_callee_saved_reg(uint32_t phys) {
    return phys >= 14 && phys <= 30 && (phys & 1) == 0;
}

const TargetRegInfo& reg_info();

} // namespace aburi::backend::or1k

#endif // ABURI_BACKEND_OR1K_TARGET_H
