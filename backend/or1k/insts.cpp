#include "insts.h"

#include "target.h"

namespace aburi::backend::or1k {

namespace {

struct InstTraits {
    std::string_view mnemonic;
    InstFormat format;
    std::string_view widths;
    uint32_t flags;
};

constexpr InstTraits kTraits[] = {
#define ABURI_OR1K_INST(Name, mnemonic, format, widths, flags, encoding) \
    {mnemonic, InstFormat::format, widths, flags},
#include "inst.def"
#undef ABURI_OR1K_INST
};

} // namespace

std::string_view or1k_mnemonic(Or1kOp op) {
    return kTraits[static_cast<uint16_t>(op)].mnemonic;
}

InstFormat or1k_format(Or1kOp op) {
    return kTraits[static_cast<uint16_t>(op)].format;
}

std::string_view or1k_widths(Or1kOp op) {
    return kTraits[static_cast<uint16_t>(op)].widths;
}

uint32_t or1k_flags(Or1kOp op) {
    return kTraits[static_cast<uint16_t>(op)].flags;
}

std::string or1k_gpr_name(uint32_t phys) {
    return "r" + std::to_string(phys);
}

RegAllocOpcodeInfo or1k_regalloc_info(uint16_t opcode) {
    uint32_t flags = kTraits[opcode].flags;
    RegAllocOpcodeInfo info;
    info.defines_operand0 = (flags & OR1K_DEF0) != 0;
    info.reads_operand0 = (flags & OR1K_USE0) != 0;
    info.is_call = (flags & OR1K_CALL) != 0;
    return info;
}

MirOpcodeFacts or1k_mir_facts(uint16_t opcode) {
    Or1kOp op = static_cast<Or1kOp>(opcode);
    uint32_t flags = kTraits[opcode].flags;
    MirOpcodeFacts facts;
    facts.is_terminator = (flags & OR1K_TERM) != 0;
    facts.is_call = (flags & OR1K_CALL) != 0;
    facts.is_pseudo = (flags & OR1K_PSEUDO) != 0;
    facts.defines_operand0 = (flags & OR1K_DEF0) != 0;
    facts.reads_operand0 = (flags & OR1K_USE0) != 0;
    facts.is_conditional_branch = op == Or1kOp::Bf || op == Or1kOp::Bnf;

    facts.is_frame_pseudo =
        op == Or1kOp::FrameAddr || op == Or1kOp::EpilogueRet;
    facts.is_asm_block = op == Or1kOp::AsmBlock;
    facts.is_eh_label = op == Or1kOp::EhLabel;
    return facts;
}

namespace {

std::string_view or1k_mnemonic_u16(uint16_t opcode) {
    return or1k_mnemonic(static_cast<Or1kOp>(opcode));
}

} // namespace

MirShape or1k_mir_shape(uint16_t opcode) {

    switch (static_cast<Or1kOp>(opcode)) {
        case Or1kOp::FrameAddr:
            return mir_shape(2, 2, {MK_Reg, MK_Frame});
        case Or1kOp::EpilogueRet:
            return mir_shape(0, 0, {});
        default:
            break;
    }
    switch (or1k_format(static_cast<Or1kOp>(opcode))) {
        case InstFormat::RR:
        case InstFormat::Sf:
            return mir_shape(2, 2, {MK_Reg, MK_Reg});
        case InstFormat::RRR:
            return mir_shape(3, 3, {MK_Reg, MK_Reg, MK_Reg});
        case InstFormat::RRI:
            return mir_shape(3, 3, {MK_Reg, MK_Reg, MK_Imm});
        case InstFormat::RImm:
        case InstFormat::SfI:
            return mir_shape(2, 2, {MK_Reg, MK_Imm});
        case InstFormat::RSymHi:
            return mir_shape(2, 2, {MK_Reg, MK_Symbol});
        case InstFormat::RRSymLo:
            return mir_shape(3, 3, {MK_Reg, MK_Reg, MK_Symbol});
        case InstFormat::Mem:
        case InstFormat::MemStore:

            return mir_shape(3, 3, {MK_Reg, MK_Reg | MK_Frame, MK_Imm});
        case InstFormat::Branch:
            return mir_shape(1, 1, {MK_Label});
        case InstFormat::CallSym:
            return mir_shape(1, 1, {MK_Symbol});
        case InstFormat::CallReg:
        case InstFormat::JmpReg:
            return mir_shape(1, 1, {MK_Reg});
        case InstFormat::SetBool:
            return mir_shape(1, 1, {MK_Reg});
        case InstFormat::Nop:
        case InstFormat::AsmText:
            return mir_shape(0, 0, {});
    }
    return mir_shape(0, kMirUnbounded, {});
}

const MirTargetInfo& or1k_mir_target() {
    static const MirTargetInfo info = [] {
        MirTargetInfo target;
        target.mnemonic = or1k_mnemonic_u16;
        target.facts = or1k_mir_facts;
        target.shape = or1k_mir_shape;
        target.phys_reg_count = 32;
        return target;
    }();
    return info;
}

const TargetRegInfo& reg_info() {
    static const TargetRegInfo info = [] {
        TargetRegInfo regs;

        for (uint32_t r = 17; r <= 31; r += 2) {
            regs.gpr_order.push_back(r);
        }

        for (uint32_t r = R3; r <= R8; ++r) {
            regs.gpr_order.push_back(r);
        }
        regs.gpr_order.push_back(RV);
        regs.gpr_order.push_back(R12);

        for (uint32_t r = 14; r <= 30; r += 2) {
            regs.gpr_order.push_back(r);
        }
        regs.is_callee_saved = is_callee_saved_reg;
        regs.reg_class = phys_reg_class;

        for (uint32_t r = 19; r <= 29; r += 2) {
            regs.linear_gpr_caller.push_back(r);
        }
        regs.linear_gpr_caller.push_back(31);
        for (uint32_t r = 14; r <= 30; r += 2) {
            regs.linear_gpr_callee.push_back(r);
        }
        regs.linear_gpr_scratch = {R13, R15, 17};
        return regs;
    }();
    return info;
}

} // namespace aburi::backend::or1k
