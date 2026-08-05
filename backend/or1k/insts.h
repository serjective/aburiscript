#ifndef ABURI_BACKEND_OR1K_INSTS_H
#define ABURI_BACKEND_OR1K_INSTS_H

#include <cstdint>
#include <string>
#include <string_view>

#include "../common/mir_verifier.h"
#include "../common/regalloc.h"

namespace aburi::backend::or1k {

inline constexpr uint32_t OR1K_DEF0 = 1u << 0;
inline constexpr uint32_t OR1K_USE0 = 1u << 1;
inline constexpr uint32_t OR1K_CALL = 1u << 2;
inline constexpr uint32_t OR1K_TERM = 1u << 3;
inline constexpr uint32_t OR1K_LOAD = 1u << 4;
inline constexpr uint32_t OR1K_STORE = 1u << 5;
inline constexpr uint32_t OR1K_PSEUDO = 1u << 6;

inline constexpr uint32_t OR1K_DELAY = 1u << 7;

enum class InstFormat : uint8_t {
    RR,
    RRR,
    RRI,
    RImm,
    RSymHi,
    RRSymLo,
    Mem,
    MemStore,
    Sf,
    SfI,
    Branch,
    CallSym,
    CallReg,
    JmpReg,
    Nop,
    SetBool,
    AsmText,
};

enum class Or1kOp : uint16_t {
#define ABURI_OR1K_INST(Name, mnemonic, format, widths, flags, encoding) Name,
#include "inst.def"
#undef ABURI_OR1K_INST
};

std::string_view or1k_mnemonic(Or1kOp op);
InstFormat or1k_format(Or1kOp op);
std::string_view or1k_widths(Or1kOp op);
uint32_t or1k_flags(Or1kOp op);

std::string or1k_gpr_name(uint32_t phys);

RegAllocOpcodeInfo or1k_regalloc_info(uint16_t opcode);

MirOpcodeFacts or1k_mir_facts(uint16_t opcode);
MirShape or1k_mir_shape(uint16_t opcode);
const MirTargetInfo& or1k_mir_target();

} // namespace aburi::backend::or1k

#endif // ABURI_BACKEND_OR1K_INSTS_H
