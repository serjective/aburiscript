#ifndef ABURI_BACKEND_X86_INSTS_H
#define ABURI_BACKEND_X86_INSTS_H

#include <cstdint>
#include <string>
#include <string_view>

#include "../common/mir_verifier.h"
#include "../common/regalloc.h"

namespace aburi::backend::x86 {

inline constexpr uint32_t X86_DEF0 = 1u << 0;
inline constexpr uint32_t X86_USE0 = 1u << 1;
inline constexpr uint32_t X86_CALL = 1u << 2;
inline constexpr uint32_t X86_TERM = 1u << 3;
inline constexpr uint32_t X86_LOAD = 1u << 4;
inline constexpr uint32_t X86_STORE = 1u << 5;
inline constexpr uint32_t X86_PSEUDO = 1u << 6;

enum class InstFormat : uint8_t {
    RR,
    RI,
    MovAbs,
    R1,
    Load,
    Store,
    FpuMem,
    MemRmw,
    RipR,
    SymImm,
    ShiftCl,
    Jmp,
    Jcc,
    JmpReg,
    CallSym,
    CallReg,
    Setcc,
    Cmov,
    DivR,
    NoOps,
    Ret,
    AsmText,
};

enum class X86Op : uint16_t {
#define ABURI_X86_INST(Name, mnemonic, format, widths, flags, encoding) Name,
#include "inst.def"
#undef ABURI_X86_INST
};

enum class Cond : uint8_t {
    E, Ne, L, Le, G, Ge, B, Be, A, Ae, S, Ns, P, Np,
};

std::string_view x86_mnemonic(X86Op op);
InstFormat x86_format(X86Op op);
std::string_view x86_widths(X86Op op);
uint32_t x86_flags(X86Op op);
std::string_view cond_name(Cond cond);

std::string att_reg_name(uint32_t phys, char width);

RegAllocOpcodeInfo x86_regalloc_info(uint16_t opcode);

MirOpcodeFacts x86_mir_facts(uint16_t opcode);
MirShape x86_mir_shape(uint16_t opcode);
const MirTargetInfo& x86_mir_target();

} // namespace aburi::backend::x86

#endif // ABURI_BACKEND_X86_INSTS_H
