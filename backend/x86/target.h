#ifndef ABURI_BACKEND_X86_TARGET_H
#define ABURI_BACKEND_X86_TARGET_H

#include <cstdint>

#include "../../abi/target_info.h"
#include "../common/regalloc.h"

namespace aburi::backend::x86 {

enum class Mode : uint8_t {
    Long64,
    Legacy32,
    Real16,
};

inline bool is_legacy32(const TargetInfo& target) {
    return target.arch == TargetArch::X86;
}

inline constexpr uint32_t RAX = 0;
inline constexpr uint32_t RCX = 1;
inline constexpr uint32_t RDX = 2;
inline constexpr uint32_t RBX = 3;
inline constexpr uint32_t RSP = 4;
inline constexpr uint32_t RBP = 5;
inline constexpr uint32_t RSI = 6;
inline constexpr uint32_t RDI = 7;
inline constexpr uint32_t R8 = 8;
inline constexpr uint32_t R9 = 9;
inline constexpr uint32_t R10 = 10;
inline constexpr uint32_t R11 = 11;
inline constexpr uint32_t R12 = 12;
inline constexpr uint32_t R13 = 13;
inline constexpr uint32_t R14 = 14;
inline constexpr uint32_t R15 = 15;
inline constexpr uint32_t XMM0 = 16;
inline constexpr uint32_t XMM7 = 23;
inline constexpr uint32_t XMM8 = 24;
inline constexpr uint32_t XMM13 = 29;
inline constexpr uint32_t XMM15 = 31;

inline constexpr uint32_t xmm(uint32_t n) { return XMM0 + n; }

inline bool is_fpr_index(uint32_t phys) {
    return phys >= XMM0 && phys <= XMM15;
}

inline RegClass phys_reg_class(uint32_t phys) {
    return is_fpr_index(phys) ? RegClass::Fpr : RegClass::Gpr;
}

inline bool is_callee_saved_reg(uint32_t phys) {
    return phys == RBX || phys == RBP || (phys >= R12 && phys <= R15);
}

inline bool is_callee_saved_reg_32(uint32_t phys) {
    return phys == RBX || phys == RSI || phys == RDI;
}

const TargetRegInfo& reg_info();

const TargetRegInfo& reg_info_32();

} // namespace aburi::backend::x86

#endif // ABURI_BACKEND_X86_TARGET_H
