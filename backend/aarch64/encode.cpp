#include "encode.h"

#include <span>

#include "insts.h"
#include "isa.h"
#include "target.h"

namespace aburi::backend::aarch64 {

namespace {

enum class EncDispatch { match, none };

constexpr EncDispatch kDispatch[] = {
#define ABURI_A64_INST(name, mnemonic, format, widths, flags, enc) \
    EncDispatch::enc,
#include "inst.def"
#undef ABURI_A64_INST
};

uint32_t cond_bits(uint32_t aux) {
    switch (static_cast<Cond>(aux)) {
        case Cond::Eq: return 0x0;
        case Cond::Ne: return 0x1;
        case Cond::Hs: return 0x2;
        case Cond::Lo: return 0x3;
        case Cond::Mi: return 0x4;
        case Cond::Pl: return 0x5;
        case Cond::Vs: return 0x6;
        case Cond::Vc: return 0x7;
        case Cond::Hi: return 0x8;
        case Cond::Ls: return 0x9;
        case Cond::Ge: return 0xA;
        case Cond::Lt: return 0xB;
        case Cond::Gt: return 0xC;
        case Cond::Le: return 0xD;
    }
    return 0xE;
}

AsmOperand adapt_reg(const MOperand& operand, char width) {
    AsmOperand out;
    out.kind = AsmOperand::Kind::Reg;
    uint32_t phys = operand.reg.index();
    if (phys >= V0 && phys <= V31) {
        out.reg = static_cast<uint8_t>(phys - V0);
    } else if (phys == SP) {
        out.reg = 31;
        out.is_sp = true;
    } else if (phys == XZR) {
        out.reg = 31;
        out.is_zr = true;
    } else {
        out.reg = static_cast<uint8_t>(phys);
    }
    out.reg_class = width;
    return out;
}

AsmOperand adapt_vec(const MOperand& operand, uint8_t lanes) {
    AsmOperand out;
    out.kind = AsmOperand::Kind::Vec;
    out.reg = static_cast<uint8_t>(operand.reg.index() - V0);
    out.reg_class = 'v';
    out.lanes = lanes;
    return out;
}

AsmOperand adapt_imm(int64_t value) {
    AsmOperand out;
    out.kind = AsmOperand::Kind::Imm;
    out.imm = value;
    return out;
}

AsmOperand adapt_sym(const MInst& inst, size_t index) {
    const MOperand& operand = inst.operands[index];
    AsmOperand out;
    out.kind = AsmOperand::Kind::Sym;
    out.sym = static_cast<uint32_t>(index);
    out.flavor = operand.kind == MOperandKind::Symbol ? operand.flavor
                                                      : SymFlavor::Plain;
    return out;
}

AsmOperand adapt_cond(uint32_t aux) {
    AsmOperand out;
    out.kind = AsmOperand::Kind::Cond;
    out.cond = static_cast<uint8_t>(cond_bits(aux));
    return out;
}

AsmOperand adapt_mem(const MInst& inst, size_t base_index,
                     size_t offset_index, AsmOperand::MemMode mode) {
    const MOperand& base = inst.operands[base_index];
    AsmOperand out;
    out.kind = AsmOperand::Kind::Mem;
    uint32_t phys = base.reg.index();
    out.base = phys == SP ? 31 : static_cast<uint8_t>(phys);
    out.base_is_sp = phys == SP;
    out.mem_mode = mode;
    const MOperand& offset = inst.operands[offset_index];
    if (offset.kind == MOperandKind::Symbol) {
        out.offset_is_sym = true;
        out.sym = static_cast<uint32_t>(offset_index);
        out.flavor = offset.flavor;
        out.mem_mode = AsmOperand::MemMode::Offset;
    } else {
        out.imm = offset.imm;
        if (mode == AsmOperand::MemMode::Offset && offset.imm == 0) {
            out.mem_mode = AsmOperand::MemMode::BaseOnly;
        }
    }
    return out;
}

} // namespace

uint32_t patch_branch26(uint32_t word, int64_t byte_displacement) {
    uint32_t imm26 = static_cast<uint32_t>(byte_displacement / 4) & 0x03FFFFFF;
    return (word & 0xFC000000u) | imm26;
}

uint32_t patch_branch19(uint32_t word, int64_t byte_displacement) {
    uint32_t imm19 = static_cast<uint32_t>(byte_displacement / 4) & 0x0007FFFF;
    return (word & ~(0x0007FFFFu << 5)) | (imm19 << 5);
}

EncodedInst encode_a64(const MInst& inst) {
    EncodedInst out;
    A64Op op = static_cast<A64Op>(inst.opcode);
    if (kDispatch[static_cast<uint16_t>(op)] == EncDispatch::none) {
        if (op == A64Op::AsmBlock) {
            out.error = "inline assembly requires the assembler path "
                        "(--air-object=as)";
        } else {
            out.error = "frame pseudo-instruction reached the encoder";
        }
        return out;
    }

    std::string_view widths = a64_widths(op);
    size_t width_index = 0;
    auto next_width = [&]() -> char {
        return width_index < widths.size() ? widths[width_index++] : 'x';
    };

    AsmOperand operands[5];
    size_t count = 0;
    auto push = [&](AsmOperand operand) { operands[count++] = operand; };
    auto push_reg = [&](size_t index) {
        push(adapt_reg(inst.operands[index], next_width()));
    };

    switch (a64_format(op)) {
        case InstFormat::RR:
            push_reg(0);
            push_reg(1);
            break;
        case InstFormat::RRR:
            push_reg(0);
            push_reg(1);
            push_reg(2);
            break;
        case InstFormat::RRRR:
            push_reg(0);
            push_reg(1);
            push_reg(2);
            push_reg(3);
            break;
        case InstFormat::RIshift: {
            push_reg(0);
            AsmOperand imm = adapt_imm(inst.operands[1].imm);
            imm.shift_hw = static_cast<uint8_t>(inst.aux);
            push(imm);
            break;
        }
        case InstFormat::RRI:
            push_reg(0);
            push_reg(1);
            push(adapt_imm(inst.operands[2].imm));
            break;
        case InstFormat::Mem:
            push_reg(0);
            push(adapt_mem(inst, 1, 2, AsmOperand::MemMode::Offset));
            break;
        case InstFormat::PairPre:
            push_reg(0);
            push_reg(1);
            push(adapt_mem(inst, 2, 3, AsmOperand::MemMode::Pre));
            break;
        case InstFormat::PairPost:
            push_reg(0);
            push_reg(1);
            push(adapt_mem(inst, 2, 3, AsmOperand::MemMode::Post));
            break;
        case InstFormat::PairOff:
            push_reg(0);
            push_reg(1);
            push(adapt_mem(inst, 2, 3, AsmOperand::MemMode::Offset));
            break;
        case InstFormat::Adrp:
            push_reg(0);
            push(adapt_sym(inst, 1));
            break;
        case InstFormat::AddSym:
            push_reg(0);
            push_reg(1);
            push(adapt_sym(inst, 2));
            break;
        case InstFormat::Branch:
            push(adapt_sym(inst, 0));
            break;
        case InstFormat::CondBranch:
            push(adapt_cond(inst.aux));
            push(adapt_sym(inst, 0));
            break;
        case InstFormat::CallSym:
            push(adapt_sym(inst, 0));
            break;
        case InstFormat::CallReg:
            push_reg(0);
            break;
        case InstFormat::CmpRR:
            push_reg(0);
            push_reg(1);
            break;
        case InstFormat::CmpRI:
            push_reg(0);
            push(adapt_imm(inst.operands[1].imm));
            break;
        case InstFormat::Cset:
            push_reg(0);
            push(adapt_cond(inst.aux));
            break;
        case InstFormat::Csel:
            push_reg(0);
            push_reg(1);
            push_reg(2);
            push(adapt_cond(inst.aux));
            break;
        case InstFormat::Ret:
            break;
        case InstFormat::Brk:
            push(adapt_imm(inst.operands[0].imm));
            break;
        case InstFormat::RRMem:
            push_reg(0);
            push_reg(1);
            push(adapt_mem(inst, 2, 2, AsmOperand::MemMode::BaseOnly));
            break;
        case InstFormat::LseRmw:

            push(adapt_reg(inst.operands[1], widths[0]));
            push(adapt_reg(inst.operands[0], widths[0]));
            push(adapt_mem(inst, 2, 2, AsmOperand::MemMode::BaseOnly));
            break;
        case InstFormat::VecCnt:
            push(adapt_vec(inst.operands[0], 8));
            push(adapt_vec(inst.operands[1], 8));
            break;
        case InstFormat::Vec16Mov:
            push(adapt_vec(inst.operands[0], 16));
            push(adapt_vec(inst.operands[1], 16));
            break;
        case InstFormat::VecAddv: {
            AsmOperand dest = adapt_reg(inst.operands[0], 'b');
            dest.reg = static_cast<uint8_t>(
                inst.operands[0].reg.index() - V0);
            push(dest);
            push(adapt_vec(inst.operands[1], 8));
            break;
        }
        case InstFormat::Barrier: {
            AsmOperand barrier;
            barrier.kind = AsmOperand::Kind::Barrier;
            push(barrier);
            break;
        }
        case InstFormat::AsmText:
            break;
    }

    IsaEncoded encoded = a64_match_and_encode(
        a64_mnemonic(op), std::span<const AsmOperand>(operands, count));
    if (!encoded.ok) {
        out.error = std::move(encoded.error);
        return out;
    }
    out.ok = true;
    out.word = encoded.word;

    if (encoded.fixup != IsaFixup::None) {
        uint32_t index = encoded.fixup_sym;
        bool is_label = inst.operands[index].kind == MOperandKind::Label;
        switch (encoded.fixup) {
            case IsaFixup::Branch26:
                if (is_label) {
                    out.fixup = TextFixup::LabelBranch26;
                    out.fixup_label = inst.operands[index].label;
                } else {
                    out.fixup = TextFixup::SymBranch26;
                    out.fixup_operand = index;
                }
                break;
            case IsaFixup::Branch19:
                out.fixup = TextFixup::LabelBranch19;
                out.fixup_label = inst.operands[index].label;
                break;
            case IsaFixup::Page21:
                out.fixup = TextFixup::SymPage21;
                out.fixup_operand = index;
                break;
            case IsaFixup::PageOff12:
                out.fixup = TextFixup::SymPageOff12;
                out.fixup_operand = index;
                break;
            case IsaFixup::None:
                break;
        }
    }
    return out;
}

} // namespace aburi::backend::aarch64
