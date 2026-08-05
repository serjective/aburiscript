#include "isa.h"

#include <algorithm>

namespace aburi::backend::x86 {

namespace {

using enum OpndPat;

#define ABURI_X86_UNPACK(...) {__VA_ARGS__}
constexpr X86IsaRow kRows[] = {
#define ABURI_X86_ISA(name, mnemonic, enc, prefix, opcode, pats, flags, aux) \
    {mnemonic, EncClass::enc, prefix, opcode, ABURI_X86_UNPACK pats, flags,  \
     aux},
#include "isa.def"
#undef ABURI_X86_ISA
};
#undef ABURI_X86_UNPACK

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

struct CondSpelling {
    std::string_view name;
    uint8_t bits;
};

constexpr CondSpelling kConds[] = {
    {"nbe", 0x7}, {"nae", 0x2}, {"nge", 0xC}, {"nle", 0xF}, {"ae", 0x3},
    {"be", 0x6},  {"ge", 0xD},  {"le", 0xE},  {"na", 0x6},  {"nb", 0x3},
    {"nc", 0x3},  {"ne", 0x5},  {"ng", 0xE},  {"nl", 0xD},  {"no", 0x1},
    {"np", 0xB},  {"ns", 0x9},  {"nz", 0x5},  {"pe", 0xA},  {"po", 0xB},
    {"a", 0x7},   {"b", 0x2},   {"c", 0x2},   {"e", 0x4},   {"g", 0xF},
    {"l", 0xC},   {"o", 0x0},   {"p", 0xA},   {"s", 0x8},   {"z", 0x4},
};

size_t pattern_arity(const X86IsaRow& row) {
    size_t count = 0;
    while (count < 3 && row.pats[count] != OpndPat::None) {
        ++count;
    }
    return count;
}

bool fits_int8(int64_t value) { return value >= -128 && value <= 127; }
bool fits_byte(int64_t value) { return value >= -128 && value <= 255; }
bool fits_int16(int64_t value) { return value >= -32768 && value <= 65535; }
bool fits_int32(int64_t value) {
    return value >= -(int64_t(1) << 31) && value <= (int64_t(1) << 32) - 1;
}

bool match_gpr(const AsmOperand& operand, char width) {
    return operand.kind == AsmOperand::Kind::Reg && operand.reg_class == width;
}

uint8_t row_operand_width(const X86IsaRow& row) {
    for (OpndPat pattern : row.pats) {
        switch (pattern) {
            case Gpr8: case Rm8: case Acc8: case Cl: return 8;
            case Gpr16: case Rm16: case Acc16: return 16;
            case Gpr32: case Rm32: case Acc32: return 32;
            case Gpr64: case Rm64: case Acc64: case IndirRm: return 64;
            default: break;
        }
    }
    return 64;
}

int64_t narrow_to_width(int64_t value, uint8_t width) {
    if (width >= 64) {
        return value;
    }
    uint64_t mask = (uint64_t(1) << width) - 1;
    uint64_t bits = static_cast<uint64_t>(value) & mask;
    uint64_t sign = uint64_t(1) << (width - 1);
    return static_cast<int64_t>((bits ^ sign) - sign);
}

bool match_operand(OpndPat pattern, const AsmOperand& operand,
                   uint8_t width) {
    if (operand.indirect && pattern != IndirRm) {
        return false;
    }
    int64_t imm = operand.kind == AsmOperand::Kind::Imm
                      ? narrow_to_width(operand.imm, width)
                      : 0;
    switch (pattern) {
        case None:
            return false;
        case Gpr8: return match_gpr(operand, 'b');
        case Gpr16: return match_gpr(operand, 'w');
        case Gpr32: return match_gpr(operand, 'l');
        case Gpr64: return match_gpr(operand, 'q');
        case Rm8:
            return match_gpr(operand, 'b') ||
                   operand.kind == AsmOperand::Kind::Mem;
        case Rm16:
            return match_gpr(operand, 'w') ||
                   operand.kind == AsmOperand::Kind::Mem;
        case Rm32:
            return match_gpr(operand, 'l') ||
                   operand.kind == AsmOperand::Kind::Mem;
        case Rm64:
            return match_gpr(operand, 'q') ||
                   operand.kind == AsmOperand::Kind::Mem;
        case Mem:
            return operand.kind == AsmOperand::Kind::Mem;
        case Xmm:
            return match_gpr(operand, 'x');
        case RmX:
            return match_gpr(operand, 'x') ||
                   operand.kind == AsmOperand::Kind::Mem;
        case Imm8s:
            return operand.kind == AsmOperand::Kind::Imm && fits_int8(imm);
        case Imm8u:
            return operand.kind == AsmOperand::Kind::Imm && fits_byte(imm);
        case Imm16:
            return operand.kind == AsmOperand::Kind::Imm && fits_int16(imm);
        case Imm32:
            return operand.kind == AsmOperand::Kind::Imm && fits_int32(imm);
        case Imm64:
            return operand.kind == AsmOperand::Kind::Imm;
        case ImmSym:
        case ImmSym64:
            return operand.kind == AsmOperand::Kind::Sym;
        case ImmOne:
            return operand.kind == AsmOperand::Kind::Imm && imm == 1;
        case Acc8:
            return match_gpr(operand, 'b') && operand.reg == 0 &&
                   !operand.high_byte;
        case Acc16: return match_gpr(operand, 'w') && operand.reg == 0;
        case Acc32: return match_gpr(operand, 'l') && operand.reg == 0;
        case Acc64: return match_gpr(operand, 'q') && operand.reg == 0;
        case Cl:
            return match_gpr(operand, 'b') && operand.reg == 1 &&
                   !operand.high_byte;
        case Rel:
            return operand.kind == AsmOperand::Kind::Sym;
        case IndirRm:
            return operand.indirect &&
                   (match_gpr(operand, 'q') ||
                    operand.kind == AsmOperand::Kind::Mem);
        case St0:
            return match_gpr(operand, 't') && operand.reg == 0;
        case StN:
            return match_gpr(operand, 't');
        case Cond:
            return operand.is_cond();
    }
    return false;
}

bool pattern_is_rm(OpndPat pattern) {
    switch (pattern) {
        case Rm8:
        case Rm16:
        case Rm32:
        case Rm64:
        case Mem:
        case RmX:
        case IndirRm:
            return true;
        default:
            return false;
    }
}

bool pattern_is_reg_field(OpndPat pattern) {
    switch (pattern) {
        case Gpr8:
        case Gpr16:
        case Gpr32:
        case Gpr64:
        case Xmm:
            return true;
        default:
            return false;
    }
}

uint8_t pattern_imm_bytes(OpndPat pattern) {
    switch (pattern) {
        case Imm8s:
        case Imm8u:
            return 1;
        case Imm16:
            return 2;
        case Imm32:
        case ImmSym:
            return 4;
        case Imm64:
        case ImmSym64:
            return 8;
        default:
            return 0;
    }
}

bool pattern_is_imm(OpndPat pattern) {
    return pattern_imm_bytes(pattern) != 0 || pattern == ImmOne;
}

struct RmEncoding {
    uint8_t modrm = 0;
    bool has_sib = false;
    uint8_t sib = 0;
    uint8_t disp_bytes = 0;
    int64_t disp = 0;
    bool rex_x = false;
    bool rex_b = false;
    bool rip = false;
};

bool encode_rm(const AsmOperand& operand, uint8_t reg_field, RmEncoding& out,
               std::string& error) {
    if (operand.kind == AsmOperand::Kind::Reg) {
        out.modrm = static_cast<uint8_t>(0xC0 | ((reg_field & 7) << 3) |
                                         (operand.reg & 7));
        out.rex_b = operand.reg >= 8;
        return true;
    }
    if (operand.kind != AsmOperand::Kind::Mem) {
        error = "operand is not addressable";
        return false;
    }
    if (operand.rip) {
        out.modrm = static_cast<uint8_t>(((reg_field & 7) << 3) | 5);
        out.disp_bytes = 4;
        out.disp = operand.disp;
        out.rip = true;
        return true;
    }
    if (operand.has_index && operand.index == 4) {
        error = "%rsp cannot be an index register";
        return false;
    }
    bool need_sib = operand.has_index || !operand.has_base ||
                    (operand.base & 7) == 4;
    uint8_t mod = 0;
    if (!operand.has_base) {
        mod = 0;
        out.disp_bytes = 4;
    } else if (operand.disp == 0 && (operand.base & 7) != 5 &&
               operand.sym == UINT32_MAX) {
        mod = 0;
        out.disp_bytes = 0;
    } else if (fits_int8(operand.disp) && operand.sym == UINT32_MAX) {
        mod = 1;
        out.disp_bytes = 1;
    } else {
        mod = 2;
        out.disp_bytes = 4;
    }
    out.disp = operand.disp;
    if (need_sib) {
        uint8_t scale_bits = 0;
        switch (operand.scale) {
            case 1: scale_bits = 0; break;
            case 2: scale_bits = 1; break;
            case 4: scale_bits = 2; break;
            case 8: scale_bits = 3; break;
            default:
                error = "index scale must be 1, 2, 4, or 8";
                return false;
        }
        uint8_t index_field = operand.has_index ? (operand.index & 7) : 4;
        uint8_t base_field = operand.has_base ? (operand.base & 7) : 5;
        out.has_sib = true;
        out.sib = static_cast<uint8_t>((scale_bits << 6) | (index_field << 3) |
                                       base_field);
        out.modrm =
            static_cast<uint8_t>((mod << 6) | ((reg_field & 7) << 3) | 4);
        out.rex_x = operand.has_index && operand.index >= 8;
        out.rex_b = operand.has_base && operand.base >= 8;
        return true;
    }
    out.modrm = static_cast<uint8_t>((mod << 6) | ((reg_field & 7) << 3) |
                                     (operand.base & 7));
    out.rex_b = operand.base >= 8;
    return true;
}

bool forces_rex(const AsmOperand& operand) {
    return operand.kind == AsmOperand::Kind::Reg && operand.reg_class == 'b' &&
           !operand.high_byte && operand.reg >= 4 && operand.reg <= 7;
}

bool bars_rex(const AsmOperand& operand) {
    return operand.kind == AsmOperand::Kind::Reg && operand.high_byte;
}

struct Packer {
    IsaEncoded out;

    void byte(uint8_t value) { out.bytes[out.size++] = value; }
    void field(int64_t value, uint8_t width) {
        for (uint8_t i = 0; i < width; ++i) {
            byte(static_cast<uint8_t>(static_cast<uint64_t>(value) >>
                                      (8 * i)));
        }
    }
    void opcode_bytes(uint32_t opcode, uint8_t cond_add) {
        uint8_t length = opcode > 0xFFFFu ? 3 : opcode > 0xFFu ? 2 : 1;
        for (uint8_t i = length; i > 1; --i) {
            byte(static_cast<uint8_t>(opcode >> (8 * (i - 1))));
        }
        byte(static_cast<uint8_t>((opcode & 0xFF) + cond_add));
    }
    IsaEncoded fail(std::string message) {
        IsaEncoded failed;
        failed.ok = false;
        failed.error = std::move(message);
        return failed;
    }
};

} // namespace

IsaEncoded x86_encode_row(X86Row row_id,
                          std::span<const AsmOperand> operands) {
    const X86IsaRow& row = kRows[static_cast<size_t>(row_id)];
    Packer packer;
    size_t arity = pattern_arity(row);
    if (operands.size() != arity) {
        return packer.fail("wrong number of operands");
    }

    const AsmOperand* rm = nullptr;
    const AsmOperand* reg = nullptr;
    const AsmOperand* imm = nullptr;
    OpndPat imm_pattern = None;
    uint8_t cond_add = 0;
    for (size_t i = 0; i < arity; ++i) {
        OpndPat pattern = row.pats[i];
        if (pattern_is_rm(pattern)) {
            rm = &operands[i];
        } else if (pattern_is_reg_field(pattern)) {
            reg = &operands[i];
        } else if (pattern_is_imm(pattern)) {
            imm = &operands[i];
            imm_pattern = pattern;
        } else if (pattern == Cond) {
            cond_add = operands[i].reg;
        }
    }
    if ((row.flags & RF_COND) == 0) {
        cond_add = 0;
    }

    bool rex_w = (row.flags & RF_W) != 0;
    bool rex_r = false;
    bool force_rex = false;
    bool block_rex = false;
    for (const AsmOperand& operand : operands) {
        force_rex |= forces_rex(operand);
        block_rex |= bars_rex(operand);
    }

    RmEncoding addressing;
    bool has_modrm = false;
    uint8_t opcode_reg = 0;

    switch (row.enc) {
        case EncClass::Plain:
        case EncClass::Rel:
            break;
        case EncClass::Modrm: {
            if (rm == nullptr) {
                return packer.fail("row has no addressable operand");
            }
            uint8_t reg_field = reg != nullptr ? reg->reg : row.aux;
            std::string error;
            if (!encode_rm(*rm, reg_field, addressing, error)) {
                return packer.fail(std::move(error));
            }
            rex_r = reg != nullptr && reg->reg >= 8;
            has_modrm = true;
            break;
        }
        case EncClass::OpReg: {
            const AsmOperand* target = reg;
            if (target == nullptr) {

                for (const AsmOperand& operand : operands) {
                    if (operand.kind == AsmOperand::Kind::Reg) {
                        target = &operand;
                        break;
                    }
                }
            }
            if (target == nullptr) {
                return packer.fail("row has no register operand");
            }
            opcode_reg = static_cast<uint8_t>(target->reg & 7);
            addressing.rex_b = target->reg >= 8;
            break;
        }
        case EncClass::FpuSt: {
            const AsmOperand* target = nullptr;
            for (size_t i = 0; i < arity; ++i) {
                if (row.pats[i] == StN) {
                    target = &operands[i];
                    break;
                }
            }
            if (target == nullptr) {
                return packer.fail("row has no x87 stack operand");
            }
            if (target->reg > 7) {
                return packer.fail("x87 stack index is out of range");
            }
            opcode_reg = target->reg;
            break;
        }
    }

    bool rex_needed = rex_w || rex_r || addressing.rex_x || addressing.rex_b ||
                      force_rex;
    if (rex_needed && block_rex) {
        return packer.fail(
            "%ah/%ch/%dh/%bh cannot be used with a REX prefix");
    }

    if (rm != nullptr && rm->kind == AsmOperand::Kind::Mem &&
        rm->segment != 0) {
        packer.byte(rm->segment);
    }
    if (row.prefix != 0) {
        packer.byte(row.prefix);
    }
    if (rex_needed) {
        uint8_t rex = 0x40;
        if (rex_w) rex |= 0x08;
        if (rex_r) rex |= 0x04;
        if (addressing.rex_x) rex |= 0x02;
        if (addressing.rex_b) rex |= 0x01;
        packer.byte(rex);
    }

    packer.opcode_bytes(row.opcode, static_cast<uint8_t>(cond_add + opcode_reg));

    uint8_t imm_width = pattern_imm_bytes(imm_pattern);
    if (row.enc == EncClass::Rel) {
        packer.out.is_branch = true;
        packer.out.branch_short_opcode =
            (row.flags & RF_RELAX) != 0
                ? static_cast<uint8_t>(row.aux + cond_add)
                : 0;
        packer.out.fixup = IsaFixup::PcRel32;
        packer.out.fixup_offset = packer.out.size;
        const AsmOperand* target = &operands[arity - 1];
        packer.out.fixup_sym = target->sym;
        packer.out.fixup_addend = target->addend;
        packer.out.fixup_flavor = target->flavor;
        packer.field(0, 4);
        packer.out.branch_near_size = packer.out.size;
        packer.out.ok = true;
        return packer.out;
    }

    if (has_modrm) {
        packer.byte(addressing.modrm);
        if (addressing.has_sib) {
            packer.byte(addressing.sib);
        }
        if (addressing.disp_bytes != 0) {
            if (rm->sym != UINT32_MAX) {
                packer.out.fixup =
                    addressing.rip ? IsaFixup::PcRel32 : IsaFixup::Abs32;
                packer.out.fixup_offset = packer.out.size;
                packer.out.pcrel_extra = imm_width;
                packer.out.fixup_sym = rm->sym;
                packer.out.fixup_addend = rm->addend;
                packer.out.fixup_flavor = rm->flavor;

                packer.field(addressing.rip ? -static_cast<int64_t>(imm_width)
                                            : addressing.disp,
                             addressing.disp_bytes);
            } else {
                packer.field(addressing.disp, addressing.disp_bytes);
            }
        }
    }

    if (imm != nullptr && imm_width != 0) {
        if (imm->kind == AsmOperand::Kind::Sym) {
            packer.out.fixup =
                imm_width == 8 ? IsaFixup::Abs64 : IsaFixup::Abs32;
            packer.out.fixup_offset = packer.out.size;
            packer.out.fixup_sym = imm->sym;
            packer.out.fixup_addend = imm->addend;
            packer.out.fixup_flavor = imm->flavor;
            packer.field(0, imm_width);
        } else {
            packer.field(imm->imm, imm_width);
        }
    }

    packer.out.ok = true;
    return packer.out;
}

IsaEncoded x86_match_and_encode(std::string_view mnemonic,
                                std::span<const AsmOperand> operands,
                                uint8_t lock_prefix) {
    const MnemonicIndex& index = mnemonic_index();
    auto begin = std::lower_bound(
        index.rows.begin(), index.rows.end(), mnemonic,
        [](uint16_t row, std::string_view name) {
            return kRows[row].mnemonic < name;
        });
    IsaEncoded last_error;
    last_error.error = "no encoding matches the operands of '" +
                       std::string(mnemonic) + "'";
    bool saw_mnemonic = false;
    for (auto it = begin;
         it != index.rows.end() && kRows[*it].mnemonic == mnemonic; ++it) {
        const X86IsaRow& row = kRows[*it];
        saw_mnemonic = true;
        size_t arity = pattern_arity(row);
        if (arity != operands.size()) {
            continue;
        }
        bool matched = true;
        uint8_t width = row_operand_width(row);
        for (size_t i = 0; i < arity; ++i) {
            if (!match_operand(row.pats[i], operands[i], width)) {
                matched = false;
                break;
            }
        }
        if (!matched) {
            continue;
        }
        IsaEncoded encoded =
            x86_encode_row(static_cast<X86Row>(*it), operands);
        if (!encoded.ok) {
            last_error = encoded;
            continue;
        }
        if (lock_prefix != 0) {
            for (int i = encoded.size; i > 0; --i) {
                encoded.bytes[i] = encoded.bytes[i - 1];
            }
            encoded.bytes[0] = lock_prefix;
            ++encoded.size;
            if (encoded.fixup != IsaFixup::None) {
                ++encoded.fixup_offset;
            }
            if (encoded.is_branch) {
                ++encoded.branch_near_size;
            }
        }
        return encoded;
    }
    if (!saw_mnemonic) {
        last_error.error = "unknown instruction '" + std::string(mnemonic) +
                           "'";
    }
    last_error.ok = false;
    return last_error;
}

bool x86_known_mnemonic(std::string_view mnemonic) {
    const MnemonicIndex& index = mnemonic_index();
    auto it = std::lower_bound(index.rows.begin(), index.rows.end(), mnemonic,
                               [](uint16_t row, std::string_view name) {
                                   return kRows[row].mnemonic < name;
                               });
    return it != index.rows.end() && kRows[*it].mnemonic == mnemonic;
}

bool x86_condition_value(std::string_view name, uint8_t& value) {
    for (const CondSpelling& spelling : kConds) {
        if (spelling.name == name) {
            value = spelling.bits;
            return true;
        }
    }
    return false;
}

bool x86_split_condition(std::string_view mnemonic, std::string_view& stem,
                         uint8_t& cond) {
    static constexpr std::string_view kStems[] = {"cmov", "set", "j"};
    for (std::string_view candidate : kStems) {
        if (mnemonic.size() <= candidate.size() ||
            mnemonic.substr(0, candidate.size()) != candidate) {
            continue;
        }
        std::string_view rest = mnemonic.substr(candidate.size());
        if (x86_condition_value(rest, cond)) {
            stem = candidate;
            return true;
        }

        char last = rest.back();
        if ((last == 'b' || last == 'w' || last == 'l' || last == 'q') &&
            x86_condition_value(rest.substr(0, rest.size() - 1), cond)) {
            stem = candidate;
            return true;
        }
    }
    return false;
}

void x86_append_nop_padding(std::vector<uint8_t>& out, uint64_t count) {

    static constexpr uint8_t kNops[10][10] = {
        {0x90},
        {0x66, 0x90},
        {0x0F, 0x1F, 0x00},
        {0x0F, 0x1F, 0x40, 0x00},
        {0x0F, 0x1F, 0x44, 0x00, 0x00},
        {0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00},
        {0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00},
        {0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00},
        {0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00},
        {0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00},
    };
    constexpr uint64_t kMaxNop = 10;
    while (count > 0) {
        uint64_t length = count > kMaxNop ? kMaxNop : count;
        const uint8_t* nop = kNops[length - 1];
        out.insert(out.end(), nop, nop + length);
        count -= length;
    }
}

} // namespace aburi::backend::x86
