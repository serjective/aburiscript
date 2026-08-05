#ifndef ABURI_BACKEND_X86_ISA_H
#define ABURI_BACKEND_X86_ISA_H

#include <cstdint>
#include <span>
#include <string>
#include <string_view>
#include <vector>

#include "../common/mir.h"

namespace aburi::backend::x86 {

enum class OpndPat : uint8_t {
    None,
    Gpr8,
    Gpr16,
    Gpr32,
    Gpr64,
    Rm8,
    Rm16,
    Rm32,
    Rm64,
    Mem,
    Xmm,
    RmX,
    Imm8s,
    Imm8u,
    Imm16,
    Imm32,
    Imm64,
    ImmSym,
    ImmSym64,
    ImmOne,
    Acc8,
    Acc16,
    Acc32,
    Acc64,
    Cl,
    Rel,
    IndirRm,
    St0,
    StN,
    Cond,
};

enum class EncClass : uint8_t {
    Plain,
    Modrm,
    OpReg,
    Rel,
    FpuSt,
};

inline constexpr uint16_t RF_NONE = 0;

inline constexpr uint16_t RF_W = 1u << 0;

inline constexpr uint16_t RF_RELAX = 1u << 1;

inline constexpr uint16_t RF_COND = 1u << 2;

enum class IsaFixup : uint8_t {
    None,
    PcRel32,
    Abs32,
    Abs64,
};

struct AsmOperand {
    enum class Kind : uint8_t {
        Reg,
        Imm,
        Mem,
        Sym,
    };

    Kind kind = Kind::Imm;
    uint8_t reg = 0;
    char reg_class = 0;
    bool high_byte = false;

    int64_t imm = 0;
    bool has_base = false;
    bool has_index = false;
    bool rip = false;
    uint8_t base = 0;
    uint8_t index = 0;
    uint8_t scale = 1;
    uint8_t segment = 0;
    int64_t disp = 0;
    uint32_t sym = UINT32_MAX;
    int64_t addend = 0;
    SymFlavor flavor = SymFlavor::Plain;

    bool indirect = false;
    bool is_cond() const { return reg_class == 'c'; }
};

struct X86IsaRow {
    std::string_view mnemonic;
    EncClass enc = EncClass::Plain;
    uint8_t prefix = 0;
    uint32_t opcode = 0;
    OpndPat pats[3] = {OpndPat::None, OpndPat::None, OpndPat::None};
    uint16_t flags = RF_NONE;
    uint8_t aux = 0;
};

enum class X86Row : uint16_t {
#define ABURI_X86_ISA(name, mnemonic, enc, prefix, opcode, pats, flags, aux) \
    name,
#include "isa.def"
#undef ABURI_X86_ISA
};

struct IsaEncoded {
    bool ok = false;
    std::string error;
    uint8_t bytes[16] = {};
    uint8_t size = 0;

    IsaFixup fixup = IsaFixup::None;
    uint8_t fixup_offset = 0;
    uint8_t pcrel_extra = 0;
    uint32_t fixup_sym = UINT32_MAX;
    int64_t fixup_addend = 0;
    SymFlavor fixup_flavor = SymFlavor::Plain;

    bool is_branch = false;
    uint8_t branch_short_opcode = 0;
    uint8_t branch_near_size = 0;
};

IsaEncoded x86_encode_row(X86Row row, std::span<const AsmOperand> operands);

IsaEncoded x86_match_and_encode(std::string_view mnemonic,
                                std::span<const AsmOperand> operands,
                                uint8_t lock_prefix = 0);

bool x86_known_mnemonic(std::string_view mnemonic);

bool x86_split_condition(std::string_view mnemonic, std::string_view& stem,
                         uint8_t& cond);

bool x86_condition_value(std::string_view name, uint8_t& value);

void x86_append_nop_padding(std::vector<uint8_t>& out, uint64_t count);

} // namespace aburi::backend::x86

#endif // ABURI_BACKEND_X86_ISA_H
