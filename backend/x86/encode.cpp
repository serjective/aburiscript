#include "encode.h"

#include <span>

#include "insts.h"
#include "isa.h"
#include "target.h"

namespace aburi::backend::x86 {

namespace {

enum class EncDispatch { match, none };

constexpr EncDispatch kDispatch[] = {
#define ABURI_X86_INST(name, mnemonic, format, widths, flags, enc) \
    EncDispatch::enc,
#include "inst.def"
#undef ABURI_X86_INST
};

uint8_t cond_bits(uint32_t aux) {
    switch (static_cast<Cond>(aux)) {
        case Cond::E: return 0x4;
        case Cond::Ne: return 0x5;
        case Cond::L: return 0xC;
        case Cond::Le: return 0xE;
        case Cond::G: return 0xF;
        case Cond::Ge: return 0xD;
        case Cond::B: return 0x2;
        case Cond::Be: return 0x6;
        case Cond::A: return 0x7;
        case Cond::Ae: return 0x3;
        case Cond::S: return 0x8;
        case Cond::Ns: return 0x9;
        case Cond::P: return 0xA;
        case Cond::Np: return 0xB;
    }
    return 0x4;
}

AsmOperand adapt_reg(const MOperand& operand, char width) {
    AsmOperand out;
    out.kind = AsmOperand::Kind::Reg;
    uint32_t phys = operand.reg.index();
    out.reg = static_cast<uint8_t>(phys >= XMM0 ? phys - XMM0 : phys);
    out.reg_class = phys >= XMM0 ? 'x' : width;
    return out;
}

AsmOperand adapt_imm(int64_t value) {
    AsmOperand out;
    out.kind = AsmOperand::Kind::Imm;
    out.imm = value;
    return out;
}

AsmOperand adapt_target(const MInst& inst, size_t index) {
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
    out.kind = AsmOperand::Kind::Reg;
    out.reg_class = 'c';
    out.reg = cond_bits(aux);
    return out;
}

AsmOperand adapt_mem(const MInst& inst, size_t base_index) {
    AsmOperand out;
    out.kind = AsmOperand::Kind::Mem;
    out.has_base = true;
    out.base = static_cast<uint8_t>(inst.operands[base_index].reg.index());
    out.disp = inst.operands[base_index + 1].imm;
    return out;
}

AsmOperand adapt_rip(const MInst& inst, size_t index) {
    const MOperand& operand = inst.operands[index];
    AsmOperand out;
    out.kind = AsmOperand::Kind::Mem;
    out.rip = true;
    out.sym = static_cast<uint32_t>(index);
    out.flavor = operand.flavor;
    return out;
}

AsmOperand cl_register() {
    AsmOperand out;
    out.kind = AsmOperand::Kind::Reg;
    out.reg = RCX;
    out.reg_class = 'b';
    return out;
}

AsmOperand st_register(uint8_t index) {
    AsmOperand out;
    out.kind = AsmOperand::Kind::Reg;
    out.reg = index;
    out.reg_class = 't';
    return out;
}

} // namespace

EncodedInst encode_x86(const MInst& inst) {
    EncodedInst out;
    X86Op op = static_cast<X86Op>(inst.opcode);
    if (kDispatch[static_cast<uint16_t>(op)] == EncDispatch::none) {
        switch (op) {
            case X86Op::AsmBlock:
                out.error = "inline assembly requires the assembler path "
                            "(--air-object=as)";
                break;
            case X86Op::MovAbsSym32:
            case X86Op::Adc32:
            case X86Op::Sbb32:
            case X86Op::SarI32:
                out.error =
                    "32-bit x86 requires the assembler path (--air-object=as)";
                break;
            default:
                out.error = "pseudo-instruction reached the encoder";
                break;
        }
        out.ok = false;
        return out;
    }

    std::string_view widths = x86_widths(op);
    auto width_of = [&](size_t index) -> char {
        return index < widths.size() ? widths[index] : 'q';
    };

    AsmOperand operands[3];
    size_t count = 0;
    auto push = [&](AsmOperand operand) { operands[count++] = operand; };
    auto push_reg = [&](size_t index) {
        push(adapt_reg(inst.operands[index], width_of(index)));
    };

    std::string_view mnemonic = x86_mnemonic(op);
    uint8_t lock_prefix = 0;
    if (mnemonic.rfind("lock ", 0) == 0) {
        lock_prefix = 0xF0;
        mnemonic = mnemonic.substr(5);
    }
    switch (op) {
        case X86Op::Fucomip:

            mnemonic = "fucomip";
            push(st_register(1));
            push(st_register(0));
            break;
        case X86Op::FpopSt0:
            mnemonic = "fstp";
            push(st_register(0));
            break;
        default:
            switch (x86_format(op)) {
                case InstFormat::RR:
                    push_reg(1);
                    push_reg(0);
                    break;
                case InstFormat::RI:
                case InstFormat::MovAbs:
                    push(adapt_imm(inst.operands[1].imm));
                    push_reg(0);
                    break;
                case InstFormat::R1:
                case InstFormat::DivR:
                    push_reg(0);
                    break;
                case InstFormat::Load:
                    push(adapt_mem(inst, 1));
                    push_reg(0);
                    break;
                case InstFormat::Store:
                case InstFormat::MemRmw:
                    push_reg(0);
                    push(adapt_mem(inst, 1));
                    break;
                case InstFormat::FpuMem:
                    push(adapt_mem(inst, 0));
                    break;
                case InstFormat::RipR:
                    push(adapt_rip(inst, 1));
                    push_reg(0);
                    break;
                case InstFormat::ShiftCl:
                    push(cl_register());
                    push_reg(0);
                    break;
                case InstFormat::Jmp:
                case InstFormat::CallSym:
                    push(adapt_target(inst, 0));
                    break;
                case InstFormat::Jcc:
                    push(adapt_cond(inst.aux));
                    push(adapt_target(inst, 0));
                    break;
                case InstFormat::JmpReg:
                case InstFormat::CallReg: {
                    AsmOperand target = adapt_reg(inst.operands[0], 'q');
                    target.indirect = true;
                    push(target);
                    break;
                }
                case InstFormat::Setcc:
                    push(adapt_cond(inst.aux));
                    push_reg(0);
                    break;
                case InstFormat::Cmov:
                    push(adapt_cond(inst.aux));
                    push_reg(1);
                    push_reg(0);
                    break;
                case InstFormat::SymImm:
                case InstFormat::NoOps:
                case InstFormat::Ret:
                case InstFormat::AsmText:
                    break;
            }
            break;
    }

    IsaEncoded encoded = x86_match_and_encode(
        mnemonic, std::span<const AsmOperand>(operands, count), lock_prefix);
    if (!encoded.ok) {
        out.ok = false;
        out.error = std::move(encoded.error);
        return out;
    }
    out.ok = true;
    out.size = encoded.size;
    for (uint8_t i = 0; i < encoded.size; ++i) {
        out.bytes[i] = encoded.bytes[i];
    }

    if (encoded.fixup != IsaFixup::None) {
        uint32_t index = encoded.fixup_sym;
        out.fixup_offset = encoded.fixup_offset;
        if (encoded.is_branch) {
            if (inst.operands[index].kind == MOperandKind::Label) {
                out.fixup = TextFixup::LabelRel32;
                out.fixup_label = inst.operands[index].label;
            } else {
                out.fixup = TextFixup::SymBranch32;
                out.fixup_operand = static_cast<uint8_t>(index);
            }
        } else if (encoded.fixup == IsaFixup::PcRel32) {
            out.fixup = TextFixup::SymRip32;
            out.fixup_operand = static_cast<uint8_t>(index);
        } else {
            out.ok = false;
            out.error = "absolute symbol operands are not supported by the "
                        "direct object writer";
        }
    }
    return out;
}

} // namespace aburi::backend::x86
