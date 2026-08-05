#ifndef ABURI_BACKEND_AARCH64_ISA_H
#define ABURI_BACKEND_AARCH64_ISA_H

#include <cstdint>
#include <span>
#include <string>
#include <string_view>

#include "../common/mir.h"

namespace aburi::backend::aarch64 {

enum class OpndPat : uint8_t {
    None,
    GprW,
    GprX,
    GprWsp,
    GprXsp,
    FprS,
    FprD,
    FprQ,
    FprB,
    VecB8,
    VecB16,
    Imm,
    MovImm16,
    SymPage,
    SymPageOff,
    SymCall,
    Target,
    MemBase,
    MemBaseOff,
    MemPre,
    MemPost,
    Cond,
    BarrierOpt,
};

enum class EncClass : uint8_t {
    Fixed,
    RdRnRm,
    RdRn,
    RdRm16,
    RnOnly,
    RdRnRmRa,
    MovWide,
    MovSpAlias,
    MovRegAlias,
    MovImmAlias,
    AddSubImm,
    AddSymLo12,
    LogicalImm,
    LdSt,
    LdStPair,
    Adr,
    BranchImm26,
    BranchCond19,
    CompareBranch19,
    Brk,
    CmpReg,
    CmpImm,
    Cset,
    Csel,
    LdapStl,
    LseRmw,
    Cas,
    VecMov16,
};

inline constexpr uint16_t RF_NONE = 0;

inline constexpr uint16_t RF_NEEDS_SP = 1u << 0;

enum class IsaFixup : uint8_t {
    None,
    Branch26,
    Branch19,
    Page21,
    PageOff12,
};

struct AsmOperand {
    enum class Kind : uint8_t {
        Reg,
        Vec,
        Imm,
        Sym,
        Cond,
        Mem,
        Barrier,
    };
    enum class MemMode : uint8_t { BaseOnly, Offset, Pre, Post };

    Kind kind = Kind::Imm;
    uint8_t reg = 0;
    char reg_class = 0;
    bool is_sp = false;
    bool is_zr = false;
    uint8_t lanes = 0;
    int64_t imm = 0;
    uint8_t shift_hw = 0;
    uint32_t sym = UINT32_MAX;
    int64_t addend = 0;
    SymFlavor flavor = SymFlavor::Plain;
    uint8_t cond = 0;
    MemMode mem_mode = MemMode::BaseOnly;
    uint8_t base = 0;
    bool base_is_sp = false;
    bool offset_is_sym = false;
};

struct A64IsaRow {
    std::string_view mnemonic;
    EncClass enc = EncClass::Fixed;
    uint32_t base = 0;
    OpndPat pats[5] = {OpndPat::None, OpndPat::None, OpndPat::None,
                       OpndPat::None, OpndPat::None};
    uint16_t flags = RF_NONE;
    uint8_t aux = 0;
};

enum class A64Row : uint16_t {
#define ABURI_A64_ISA(name, mnemonic, enc, base, pats, flags, aux) name,
#include "isa.def"
#undef ABURI_A64_ISA
};

struct IsaEncoded {
    bool ok = false;
    std::string error;
    uint32_t word = 0;
    IsaFixup fixup = IsaFixup::None;
    uint32_t fixup_sym = UINT32_MAX;
    int64_t fixup_addend = 0;
    SymFlavor fixup_flavor = SymFlavor::Plain;
    uint8_t fixup_access_bytes = 0;
};

IsaEncoded a64_encode_row(A64Row row, std::span<const AsmOperand> operands);

IsaEncoded a64_match_and_encode(std::string_view mnemonic,
                                std::span<const AsmOperand> operands);

bool a64_known_mnemonic(std::string_view mnemonic);

bool a64_logical_imm(uint64_t value, bool is_64, uint32_t& n, uint32_t& immr,
                     uint32_t& imms);

} // namespace aburi::backend::aarch64

#endif // ABURI_BACKEND_AARCH64_ISA_H
