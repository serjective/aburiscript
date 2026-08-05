#ifndef ABURI_BACKEND_AARCH64_INSTS_H
#define ABURI_BACKEND_AARCH64_INSTS_H

#include <cstdint>
#include <string>
#include <string_view>

#include "../common/mir_verifier.h"
#include "../common/regalloc.h"

namespace aburi::backend::aarch64 {

inline constexpr uint32_t A64_DEF0 = 1u << 0;
inline constexpr uint32_t A64_USE0 = 1u << 1;
inline constexpr uint32_t A64_CALL = 1u << 2;
inline constexpr uint32_t A64_TERM = 1u << 3;
inline constexpr uint32_t A64_LOAD = 1u << 4;
inline constexpr uint32_t A64_STORE = 1u << 5;
inline constexpr uint32_t A64_PSEUDO = 1u << 6;

enum class InstFormat : uint8_t {
    RR,
    RRR,
    RRRR,
    RIshift,
    RRI,
    Mem,
    PairPre,
    PairPost,
    PairOff,
    Adrp,
    AddSym,
    Branch,
    CondBranch,
    CallSym,
    CallReg,
    CmpRR,
    CmpRI,
    Cset,
    Csel,
    Ret,
    Brk,
    RRMem,
    LseRmw,
    VecCnt,
    Vec16Mov,
    VecAddv,
    Barrier,
    AsmText,
};

enum class A64Op : uint16_t {
#define ABURI_A64_INST(Name, mnemonic, format, widths, flags, encoding) Name,
#include "inst.def"
#undef ABURI_A64_INST
};

enum class Cond : uint8_t {
    Eq, Ne, Lt, Le, Gt, Ge, Lo, Ls, Hi, Hs, Mi, Pl, Vs, Vc,
};

std::string_view a64_mnemonic(A64Op op);
InstFormat a64_format(A64Op op);
std::string_view a64_widths(A64Op op);
uint32_t a64_flags(A64Op op);
std::string_view cond_name(Cond cond);

std::string a64_gpr_name(uint32_t phys, bool wide);

RegAllocOpcodeInfo a64_regalloc_info(uint16_t opcode);

MirOpcodeFacts a64_mir_facts(uint16_t opcode);
MirShape a64_mir_shape(uint16_t opcode);
const MirTargetInfo& a64_mir_target();

} // namespace aburi::backend::aarch64

#endif // ABURI_BACKEND_AARCH64_INSTS_H
