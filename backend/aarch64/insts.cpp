#include "insts.h"

#include "target.h"

namespace aburi::backend::aarch64 {

namespace {

struct InstTraits {
    std::string_view mnemonic;
    InstFormat format;
    std::string_view widths;
    uint32_t flags;
};

constexpr InstTraits kTraits[] = {
#define ABURI_A64_INST(Name, mnemonic, format, widths, flags, encoding) \
    {mnemonic, InstFormat::format, widths, flags},
#include "inst.def"
#undef ABURI_A64_INST
};

constexpr std::string_view kCondNames[] = {
    "eq", "ne", "lt", "le", "gt", "ge", "lo", "ls", "hi", "hs", "mi", "pl",
    "vs", "vc",
};

} // namespace

std::string_view a64_mnemonic(A64Op op) {
    return kTraits[static_cast<uint16_t>(op)].mnemonic;
}

InstFormat a64_format(A64Op op) {
    return kTraits[static_cast<uint16_t>(op)].format;
}

std::string_view a64_widths(A64Op op) {
    return kTraits[static_cast<uint16_t>(op)].widths;
}

uint32_t a64_flags(A64Op op) {
    return kTraits[static_cast<uint16_t>(op)].flags;
}

std::string_view cond_name(Cond cond) {
    return kCondNames[static_cast<uint8_t>(cond)];
}

std::string a64_gpr_name(uint32_t phys, bool wide) {
    if (phys == SP) {
        return wide ? "sp" : "wsp";
    }
    return (wide ? "x" : "w") + std::to_string(phys);
}

RegAllocOpcodeInfo a64_regalloc_info(uint16_t opcode) {
    uint32_t flags = kTraits[opcode].flags;
    RegAllocOpcodeInfo info;
    info.defines_operand0 = (flags & A64_DEF0) != 0;
    info.reads_operand0 = (flags & A64_USE0) != 0;
    info.is_call = (flags & A64_CALL) != 0;
    return info;
}

MirOpcodeFacts a64_mir_facts(uint16_t opcode) {
    A64Op op = static_cast<A64Op>(opcode);
    uint32_t flags = kTraits[opcode].flags;
    MirOpcodeFacts facts;
    facts.is_terminator = (flags & A64_TERM) != 0;
    facts.is_call = (flags & A64_CALL) != 0;
    facts.is_pseudo = (flags & A64_PSEUDO) != 0;
    facts.defines_operand0 = (flags & A64_DEF0) != 0;
    facts.reads_operand0 = (flags & A64_USE0) != 0;
    facts.is_conditional_branch = op == A64Op::Bcc;

    facts.is_frame_pseudo = op == A64Op::FrameAddr ||
                            op == A64Op::EpilogueRet ||
                            op == A64Op::EpilogueTailBr;
    facts.is_asm_block = op == A64Op::AsmBlock;
    facts.is_eh_label = op == A64Op::EhLabel;
    return facts;
}

namespace {

std::string_view a64_mnemonic_u16(uint16_t opcode) {
    return a64_mnemonic(static_cast<A64Op>(opcode));
}

} // namespace

MirShape a64_mir_shape(uint16_t opcode) {

    switch (static_cast<A64Op>(opcode)) {
        case A64Op::FrameAddr:
            return mir_shape(2, 2, {MK_Reg, MK_Frame});
        default:
            break;
    }
    switch (a64_format(static_cast<A64Op>(opcode))) {
        case InstFormat::RR:
        case InstFormat::CmpRR:
            return mir_shape(2, 2, {MK_Reg, MK_Reg});
        case InstFormat::RRR:
        case InstFormat::Csel:
            return mir_shape(3, 3, {MK_Reg, MK_Reg, MK_Reg});
        case InstFormat::RRRR:
            return mir_shape(4, 4, {MK_Reg, MK_Reg, MK_Reg, MK_Reg});
        case InstFormat::RIshift:
        case InstFormat::CmpRI:
            return mir_shape(2, 2, {MK_Reg, MK_Imm});
        case InstFormat::RRI:
            return mir_shape(3, 3, {MK_Reg, MK_Reg, MK_Imm});
        case InstFormat::Mem:

            return mir_shape_class(
                mir_shape(3, 3, {MK_Reg, MK_Reg | MK_Frame, MK_Imm | MK_Symbol}),
                1, RegClass::Gpr);
        case InstFormat::PairPre:
        case InstFormat::PairPost:
        case InstFormat::PairOff:

            return mir_shape_class(mir_shape(4, 4, {MK_Reg, MK_Reg, MK_Reg, MK_Imm}), 2,
                              RegClass::Gpr);
        case InstFormat::Adrp:
            return mir_shape(2, 2, {MK_Reg, MK_Symbol});
        case InstFormat::AddSym:
            return mir_shape(3, 3, {MK_Reg, MK_Reg, MK_Symbol});
        case InstFormat::Branch:
        case InstFormat::CondBranch:
            return mir_shape(1, 1, {MK_Label});
        case InstFormat::CallSym:
            return mir_shape(1, 1, {MK_Symbol});
        case InstFormat::CallReg:
            return mir_shape_class(mir_shape(1, 1, {MK_Reg}), 0, RegClass::Gpr);
        case InstFormat::Cset:
            return mir_shape(1, 1, {MK_Reg});
        case InstFormat::Brk:
            return mir_shape(1, 1, {MK_Imm});
        case InstFormat::RRMem:
        case InstFormat::LseRmw:
            return mir_shape_class(
                mir_shape(3, 3, {MK_Reg, MK_Reg, MK_Reg | MK_Frame}), 2,
                RegClass::Gpr);
        case InstFormat::VecCnt:
        case InstFormat::Vec16Mov:
        case InstFormat::VecAddv:
            return mir_shape_class(
                mir_shape_class(mir_shape(2, 2, {MK_Reg, MK_Reg}), 0, RegClass::Fpr), 1,
                RegClass::Fpr);
        case InstFormat::Ret:
        case InstFormat::Barrier:
        case InstFormat::AsmText:
            return mir_shape(0, 0, {});
    }
    return mir_shape(0, kMirUnbounded, {});
}

const MirTargetInfo& a64_mir_target() {
    static const MirTargetInfo info = [] {
        MirTargetInfo target;
        target.mnemonic = a64_mnemonic_u16;
        target.facts = a64_mir_facts;
        target.shape = a64_mir_shape;
        target.phys_reg_count = V31 + 1;
        return target;
    }();
    return info;
}

const TargetRegInfo& reg_info() {
    static const TargetRegInfo info = [] {
        TargetRegInfo regs;
        for (uint32_t r = 9; r <= 15; ++r) {
            regs.gpr_order.push_back(r);
        }
        for (uint32_t r = 0; r <= 8; ++r) {
            regs.gpr_order.push_back(r);
        }
        for (uint32_t r = X19; r <= X28; ++r) {
            regs.gpr_order.push_back(r);
        }
        for (uint32_t r = V16; r <= V31; ++r) {
            regs.fpr_order.push_back(r);
        }
        for (uint32_t r = V0; r <= V7; ++r) {
            regs.fpr_order.push_back(r);
        }
        for (uint32_t r = V8; r <= V15; ++r) {
            regs.fpr_order.push_back(r);
        }
        regs.is_callee_saved = is_callee_saved_reg;
        regs.reg_class = phys_reg_class;

        for (uint32_t r = 9; r <= 13; ++r) {
            regs.linear_gpr_caller.push_back(r);
        }
        for (uint32_t r = X19; r <= X28; ++r) {
            regs.linear_gpr_callee.push_back(r);
        }
        for (uint32_t r = V16; r <= V28; ++r) {
            regs.linear_fpr_caller.push_back(r);
        }
        for (uint32_t r = V8; r <= V15; ++r) {
            regs.linear_fpr_callee.push_back(r);
        }
        regs.linear_gpr_scratch = {14, 15, X16, X17};
        regs.linear_fpr_scratch = {V29, V30, V31};
        return regs;
    }();
    return info;
}

} // namespace aburi::backend::aarch64
