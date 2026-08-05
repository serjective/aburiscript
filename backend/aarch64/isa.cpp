#include "isa.h"

#include <algorithm>
#include <vector>

namespace aburi::backend::aarch64 {

namespace {

using enum OpndPat;

#define ABURI_A64_UNPACK(...) {__VA_ARGS__}
constexpr A64IsaRow kRows[] = {
#define ABURI_A64_ISA(name, mnemonic, enc, base, pats, flags, aux) \
    {mnemonic, EncClass::enc, base, ABURI_A64_UNPACK pats, flags, aux},
#include "isa.def"
#undef ABURI_A64_ISA
};
#undef ABURI_A64_UNPACK

constexpr size_t kRowCount = sizeof(kRows) / sizeof(kRows[0]);

struct MnemonicIndex {
    std::vector<uint16_t> rows;

    MnemonicIndex() {
        rows.resize(kRowCount);
        for (size_t i = 0; i < kRowCount; ++i) {
            rows[i] = static_cast<uint16_t>(i);
        }
        std::stable_sort(rows.begin(), rows.end(),
                         [](uint16_t a, uint16_t b) {
                             return kRows[a].mnemonic < kRows[b].mnemonic;
                         });
    }
};

const MnemonicIndex& mnemonic_index() {
    static const MnemonicIndex index;
    return index;
}

size_t pattern_arity(const A64IsaRow& row) {
    size_t count = 0;
    while (count < 5 && row.pats[count] != OpndPat::None) {
        ++count;
    }
    return count;
}

bool match_reg(const AsmOperand& operand, char reg_class, bool allow_sp) {
    if (operand.kind != AsmOperand::Kind::Reg ||
        operand.reg_class != reg_class) {
        return false;
    }
    return allow_sp ? !operand.is_zr : !operand.is_sp;
}

bool match_operand(OpndPat pattern, const AsmOperand& operand) {
    switch (pattern) {
        case OpndPat::None:
            return false;
        case OpndPat::GprW:
            return match_reg(operand, 'w', false);
        case OpndPat::GprX:
            return match_reg(operand, 'x', false);
        case OpndPat::GprWsp:
            return match_reg(operand, 'w', true);
        case OpndPat::GprXsp:
            return match_reg(operand, 'x', true);
        case OpndPat::FprS:
            return operand.kind == AsmOperand::Kind::Reg &&
                   operand.reg_class == 's';
        case OpndPat::FprD:
            return operand.kind == AsmOperand::Kind::Reg &&
                   operand.reg_class == 'd';
        case OpndPat::FprQ:
            return operand.kind == AsmOperand::Kind::Reg &&
                   operand.reg_class == 'q';
        case OpndPat::FprB:
            return operand.kind == AsmOperand::Kind::Reg &&
                   operand.reg_class == 'b';
        case OpndPat::VecB8:
            return operand.kind == AsmOperand::Kind::Vec &&
                   operand.lanes == 8;
        case OpndPat::VecB16:
            return operand.kind == AsmOperand::Kind::Vec &&
                   operand.lanes == 16;
        case OpndPat::Imm:
            return operand.kind == AsmOperand::Kind::Imm &&
                   operand.shift_hw == 0;
        case OpndPat::MovImm16:
            return operand.kind == AsmOperand::Kind::Imm;
        case OpndPat::SymPage:

            return operand.kind == AsmOperand::Kind::Sym &&
                   (operand.flavor == SymFlavor::Plain ||
                    operand.flavor == SymFlavor::Page ||
                    operand.flavor == SymFlavor::GotPage ||
                    operand.flavor == SymFlavor::TlvPage);
        case OpndPat::SymPageOff:
            return operand.kind == AsmOperand::Kind::Sym &&
                   (operand.flavor == SymFlavor::PageOff ||
                    operand.flavor == SymFlavor::GotPageOff ||
                    operand.flavor == SymFlavor::TlvPageOff);
        case OpndPat::SymCall:
        case OpndPat::Target:
            return operand.kind == AsmOperand::Kind::Sym &&
                   operand.flavor == SymFlavor::Plain;
        case OpndPat::MemBase:
            return operand.kind == AsmOperand::Kind::Mem &&
                   operand.mem_mode == AsmOperand::MemMode::BaseOnly;
        case OpndPat::MemBaseOff:
            return operand.kind == AsmOperand::Kind::Mem &&
                   (operand.mem_mode == AsmOperand::MemMode::BaseOnly ||
                    operand.mem_mode == AsmOperand::MemMode::Offset);
        case OpndPat::MemPre:
            return operand.kind == AsmOperand::Kind::Mem &&
                   operand.mem_mode == AsmOperand::MemMode::Pre;
        case OpndPat::MemPost:
            return operand.kind == AsmOperand::Kind::Mem &&
                   operand.mem_mode == AsmOperand::MemMode::Post;
        case OpndPat::Cond:
            return operand.kind == AsmOperand::Kind::Cond;
        case OpndPat::BarrierOpt:
            return operand.kind == AsmOperand::Kind::Barrier;
    }
    return false;
}

bool match_row(const A64IsaRow& row, std::span<const AsmOperand> operands) {
    if (pattern_arity(row) != operands.size()) {
        return false;
    }
    for (size_t i = 0; i < operands.size(); ++i) {
        if (!match_operand(row.pats[i], operands[i])) {
            return false;
        }
    }
    if (row.flags & RF_NEEDS_SP) {
        bool has_sp = false;
        for (const AsmOperand& operand : operands) {
            has_sp = has_sp || (operand.kind == AsmOperand::Kind::Reg &&
                                operand.is_sp);
        }
        if (!has_sp) {
            return false;
        }
    }
    return true;
}

void take_sym_fixup(IsaEncoded& out, IsaFixup kind,
                    const AsmOperand& operand) {
    out.fixup = kind;
    out.fixup_sym = operand.sym;
    out.fixup_addend = operand.addend;
    out.fixup_flavor = operand.flavor;
}

IsaEncoded encode_row(const A64IsaRow& row,
                      std::span<const AsmOperand> ops) {
    IsaEncoded out;
    auto word = [&](uint32_t value) {
        out.word = value;
        out.ok = true;
    };
    auto fail = [&](std::string message) {
        out.ok = false;
        out.error = std::string(row.mnemonic) + ": " + std::move(message);
    };
    auto reg = [&](size_t index) -> uint32_t { return ops[index].reg; };

    switch (row.enc) {
        case EncClass::Fixed:
            word(row.base);
            break;
        case EncClass::RdRnRm:
            word(row.base | (reg(2) << 16) | (reg(1) << 5) | reg(0));
            break;
        case EncClass::RdRn:
            word(row.base | (reg(1) << 5) | reg(0));
            break;
        case EncClass::RdRm16:
            word(row.base | (reg(1) << 16) | reg(0));
            break;
        case EncClass::RnOnly:
            word(row.base | (reg(0) << 5));
            break;
        case EncClass::RdRnRmRa:
            word(row.base | (reg(2) << 16) | (reg(3) << 10) |
                 (reg(1) << 5) | reg(0));
            break;
        case EncClass::MovWide: {
            int64_t value = ops[1].imm;
            if (value < 0 || value > 0xFFFF) {
                fail("move immediate out of range: " + std::to_string(value));
                break;
            }
            word(row.base | (static_cast<uint32_t>(ops[1].shift_hw) << 21) |
                 (static_cast<uint32_t>(value) << 5) | reg(0));
            break;
        }
        case EncClass::MovSpAlias:
            word(row.base | (reg(1) << 5) | reg(0));
            break;
        case EncClass::MovRegAlias:
            word(row.base | (reg(1) << 16) | reg(0));
            break;
        case EncClass::MovImmAlias: {
            bool is_64 = (row.base & 0x80000000u) != 0;
            uint64_t value = static_cast<uint64_t>(ops[1].imm);
            if (!is_64) {
                value &= 0xFFFFFFFFull;
            }
            uint32_t rd = reg(0);
            uint32_t shifts = is_64 ? 4 : 2;

            for (uint32_t shift = 0; shift < shifts; ++shift) {
                uint64_t field = 0xFFFFull << (16 * shift);
                if ((value & ~field) == 0) {
                    word((is_64 ? 0xD2800000u : 0x52800000u) | (shift << 21) |
                         (static_cast<uint32_t>(value >> (16 * shift)) << 5) |
                         rd);
                    return out;
                }
            }

            uint64_t inverted = is_64 ? ~value : (~value & 0xFFFFFFFFull);
            for (uint32_t shift = 0; shift < shifts; ++shift) {
                uint64_t field = 0xFFFFull << (16 * shift);
                if ((inverted & ~field) == 0) {
                    word((is_64 ? 0x92800000u : 0x12800000u) | (shift << 21) |
                         (static_cast<uint32_t>(inverted >> (16 * shift))
                          << 5) |
                         rd);
                    return out;
                }
            }
            uint32_t n = 0;
            uint32_t immr = 0;
            uint32_t imms = 0;
            if (a64_logical_imm(value, is_64, n, immr, imms)) {
                word((is_64 ? 0xB2000000u : 0x32000000u) | (n << 22) |
                     (immr << 16) | (imms << 10) | (31u << 5) | rd);
                return out;
            }
            fail("immediate " + std::to_string(ops[1].imm) +
                 " needs a multi-instruction move sequence");
            break;
        }
        case EncClass::AddSubImm: {
            int64_t value = ops[2].imm;
            if (value < 0 || value > 4095) {
                fail("immediate out of range: " + std::to_string(value));
                break;
            }
            word(row.base | (static_cast<uint32_t>(value) << 10) |
                 (reg(1) << 5) | reg(0));
            break;
        }
        case EncClass::AddSymLo12:
            word(row.base | (reg(1) << 5) | reg(0));
            take_sym_fixup(out, IsaFixup::PageOff12, ops[2]);
            break;
        case EncClass::LogicalImm: {
            uint32_t n = 0;
            uint32_t immr = 0;
            uint32_t imms = 0;
            bool is_64 = (row.base & 0x80000000u) != 0;
            if (!a64_logical_imm(static_cast<uint64_t>(ops[2].imm), is_64, n,
                                 immr, imms)) {
                fail("immediate is not a bitmask immediate: " +
                     std::to_string(ops[2].imm));
                break;
            }
            word(row.base | (n << 22) | (immr << 16) | (imms << 10) |
                 (reg(1) << 5) | reg(0));
            break;
        }
        case EncClass::LdSt: {
            const AsmOperand& mem = ops[1];
            uint32_t rt = reg(0);
            uint32_t rn = mem.base;
            if (mem.offset_is_sym) {
                word(row.base | (rn << 5) | rt);
                take_sym_fixup(out, IsaFixup::PageOff12, mem);
                out.fixup_access_bytes = row.aux;
                break;
            }
            int64_t offset = mem.imm;
            uint32_t scale = row.aux;
            if (offset >= 0 && offset % scale == 0 &&
                offset / scale <= 4095) {
                word(row.base |
                     (static_cast<uint32_t>(offset / scale) << 10) |
                     (rn << 5) | rt);
                break;
            }
            if (offset >= -256 && offset <= 255) {
                word((row.base - 0x01000000u) |
                     ((static_cast<uint32_t>(offset) & 0x1FF) << 12) |
                     (rn << 5) | rt);
                break;
            }
            fail("memory offset out of range: " + std::to_string(offset));
            break;
        }
        case EncClass::LdStPair: {
            const AsmOperand& mem = ops[2];
            int64_t offset = mem.offset_is_sym ? -1 : mem.imm;
            uint32_t scale = row.aux;
            if (mem.offset_is_sym || offset % scale != 0 ||
                offset / scale < -64 || offset / scale > 63) {
                fail("pair offset out of range");
                break;
            }
            word(row.base |
                 ((static_cast<uint32_t>(offset / scale) & 0x7F) << 15) |
                 (reg(1) << 10) | (mem.base << 5) | reg(0));
            break;
        }
        case EncClass::Adr:
            word(row.base | reg(0));
            take_sym_fixup(out, IsaFixup::Page21, ops[1]);
            break;
        case EncClass::BranchImm26:
            word(row.base);
            take_sym_fixup(out, IsaFixup::Branch26, ops[0]);
            break;
        case EncClass::BranchCond19:
            word(row.base | ops[0].cond);
            take_sym_fixup(out, IsaFixup::Branch19, ops[1]);
            break;
        case EncClass::CompareBranch19:
            word(row.base | reg(0));
            take_sym_fixup(out, IsaFixup::Branch19, ops[1]);
            break;
        case EncClass::Brk: {
            int64_t value = ops[0].imm;
            if (value < 0 || value > 0xFFFF) {
                fail("immediate out of range: " + std::to_string(value));
                break;
            }
            word(row.base | (static_cast<uint32_t>(value) << 5));
            break;
        }
        case EncClass::CmpReg:
            word(row.base | (reg(1) << 16) | (reg(0) << 5));
            break;
        case EncClass::CmpImm: {
            int64_t value = ops[1].imm;
            if (value < 0 || value > 4095) {
                fail("immediate out of range: " + std::to_string(value));
                break;
            }
            word(row.base | (static_cast<uint32_t>(value) << 10) |
                 (reg(0) << 5));
            break;
        }
        case EncClass::Cset:
            word(row.base |
                 ((static_cast<uint32_t>(ops[1].cond) ^ 1u) << 12) | reg(0));
            break;
        case EncClass::Csel:
            word(row.base | (reg(2) << 16) |
                 (static_cast<uint32_t>(ops[3].cond) << 12) |
                 (reg(1) << 5) | reg(0));
            break;
        case EncClass::LdapStl:
            word(row.base | (ops[1].base << 5) | reg(0));
            break;
        case EncClass::LseRmw:
        case EncClass::Cas:

            word(row.base | (reg(0) << 16) | (ops[2].base << 5) | reg(1));
            break;
        case EncClass::VecMov16:
            word(row.base | (reg(1) << 16) | (reg(1) << 5) | reg(0));
            break;
    }
    return out;
}

} // namespace

bool a64_logical_imm(uint64_t value, bool is_64, uint32_t& n, uint32_t& immr,
                     uint32_t& imms) {
    if (!is_64) {
        if ((value >> 32) != 0) {
            return false;
        }
        value |= value << 32;
    }
    if (value == 0 || ~value == 0) {
        return false;
    }
    uint32_t size = 64;
    while (size > 2) {
        uint32_t half = size / 2;
        uint64_t mask = (1ull << half) - 1;
        if ((value & mask) == ((value >> half) & mask)) {
            size = half;
        } else {
            break;
        }
    }
    uint64_t element_mask = size == 64 ? ~0ull : ((1ull << size) - 1);
    uint64_t element = value & element_mask;
    uint32_t ones = 0;
    for (uint32_t bit = 0; bit < size; ++bit) {
        ones += (element >> bit) & 1;
    }
    if (ones == 0 || ones == size) {
        return false;
    }
    uint64_t run = (ones == 64) ? ~0ull : ((1ull << ones) - 1);
    for (uint32_t rotation = 0; rotation < size; ++rotation) {
        uint64_t rotated =
            rotation == 0
                ? run
                : (((run >> rotation) | (run << (size - rotation))) &
                   element_mask);
        if (rotated == element) {
            immr = rotation;
            if (size == 64) {
                n = 1;
                imms = ones - 1;
            } else {
                n = 0;
                imms = ((0x3Fu & ~(2 * size - 1)) | (ones - 1)) & 0x3F;
            }
            return true;
        }
    }
    return false;
}

IsaEncoded a64_encode_row(A64Row row, std::span<const AsmOperand> operands) {
    return encode_row(kRows[static_cast<uint16_t>(row)], operands);
}

bool a64_known_mnemonic(std::string_view mnemonic) {
    const MnemonicIndex& index = mnemonic_index();
    auto it = std::lower_bound(
        index.rows.begin(), index.rows.end(), mnemonic,
        [](uint16_t row, std::string_view lookup) {
            return kRows[row].mnemonic < lookup;
        });
    return it != index.rows.end() && kRows[*it].mnemonic == mnemonic;
}

IsaEncoded a64_match_and_encode(std::string_view mnemonic,
                                std::span<const AsmOperand> operands) {
    const MnemonicIndex& index = mnemonic_index();
    auto it = std::lower_bound(
        index.rows.begin(), index.rows.end(), mnemonic,
        [](uint16_t row, std::string_view lookup) {
            return kRows[row].mnemonic < lookup;
        });
    if (it == index.rows.end() || kRows[*it].mnemonic != mnemonic) {
        IsaEncoded out;
        out.error = "unknown mnemonic '" + std::string(mnemonic) + "'";
        return out;
    }
    IsaEncoded last_failure;
    bool any_candidate = false;
    for (; it != index.rows.end() && kRows[*it].mnemonic == mnemonic; ++it) {
        const A64IsaRow& row = kRows[*it];
        if (!match_row(row, operands)) {
            continue;
        }
        any_candidate = true;
        IsaEncoded encoded = encode_row(row, operands);
        if (encoded.ok) {
            return encoded;
        }
        last_failure = encoded;
    }
    if (any_candidate) {
        return last_failure;
    }
    IsaEncoded out;
    out.error = "no matching operand form for '" + std::string(mnemonic) +
                "'";
    return out;
}

} // namespace aburi::backend::aarch64
