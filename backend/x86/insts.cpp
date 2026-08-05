#include "insts.h"

#include "target.h"

namespace aburi::backend::x86 {

namespace {

struct InstTraits {
    std::string_view mnemonic;
    InstFormat format;
    std::string_view widths;
    uint32_t flags;
};

constexpr InstTraits kTraits[] = {
#define ABURI_X86_INST(Name, mnemonic, format, widths, flags, encoding) \
    {mnemonic, InstFormat::format, widths, flags},
#include "inst.def"
#undef ABURI_X86_INST
};

constexpr std::string_view kCondNames[] = {
    "e", "ne", "l", "le", "g", "ge", "b", "be", "a", "ae", "s", "ns", "p",
    "np",
};

} // namespace

std::string_view x86_mnemonic(X86Op op) {
    return kTraits[static_cast<uint16_t>(op)].mnemonic;
}

InstFormat x86_format(X86Op op) {
    return kTraits[static_cast<uint16_t>(op)].format;
}

std::string_view x86_widths(X86Op op) {
    return kTraits[static_cast<uint16_t>(op)].widths;
}

uint32_t x86_flags(X86Op op) {
    return kTraits[static_cast<uint16_t>(op)].flags;
}

std::string_view cond_name(Cond cond) {
    return kCondNames[static_cast<uint8_t>(cond)];
}

namespace {

constexpr const char* kGpr64[] = {
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi",
    "r8",  "r9",  "r10", "r11", "r12", "r13", "r14", "r15",
};
constexpr const char* kGpr32[] = {
    "eax", "ecx", "edx",  "ebx",  "esp",  "ebp",  "esi",  "edi",
    "r8d", "r9d", "r10d", "r11d", "r12d", "r13d", "r14d", "r15d",
};
constexpr const char* kGpr16[] = {
    "ax",  "cx",  "dx",   "bx",   "sp",   "bp",   "si",   "di",
    "r8w", "r9w", "r10w", "r11w", "r12w", "r13w", "r14w", "r15w",
};
constexpr const char* kGpr8[] = {
    "al",  "cl",  "dl",   "bl",   "spl",  "bpl",  "sil",  "dil",
    "r8b", "r9b", "r10b", "r11b", "r12b", "r13b", "r14b", "r15b",
};

} // namespace

std::string att_reg_name(uint32_t phys, char width) {
    if (phys >= XMM0 && phys <= XMM15) {
        return "%xmm" + std::to_string(phys - XMM0);
    }
    switch (width) {
        case 'l': return std::string("%") + kGpr32[phys];
        case 'w': return std::string("%") + kGpr16[phys];
        case 'b': return std::string("%") + kGpr8[phys];
        default: return std::string("%") + kGpr64[phys];
    }
}

RegAllocOpcodeInfo x86_regalloc_info(uint16_t opcode) {
    uint32_t flags = kTraits[opcode].flags;
    RegAllocOpcodeInfo info;
    info.defines_operand0 = (flags & X86_DEF0) != 0;
    info.reads_operand0 = (flags & X86_USE0) != 0;
    info.is_call = (flags & X86_CALL) != 0;
    return info;
}

MirOpcodeFacts x86_mir_facts(uint16_t opcode) {
    X86Op op = static_cast<X86Op>(opcode);
    uint32_t flags = kTraits[opcode].flags;
    MirOpcodeFacts facts;
    facts.is_terminator = (flags & X86_TERM) != 0;
    facts.is_call = (flags & X86_CALL) != 0;
    facts.is_pseudo = (flags & X86_PSEUDO) != 0;
    facts.defines_operand0 = (flags & X86_DEF0) != 0;
    facts.reads_operand0 = (flags & X86_USE0) != 0;
    facts.is_conditional_branch = op == X86Op::JccLbl;

    facts.is_frame_pseudo =
        op == X86Op::FrameAddr || op == X86Op::EpilogueRet;
    facts.is_asm_block = op == X86Op::AsmBlock;
    facts.is_eh_label = op == X86Op::EhLabel;
    return facts;
}

namespace {

std::string_view x86_mnemonic_u16(uint16_t opcode) {
    return x86_mnemonic(static_cast<X86Op>(opcode));
}

} // namespace

MirShape x86_mir_shape(uint16_t opcode) {

    if (static_cast<X86Op>(opcode) == X86Op::FrameAddr) {
        return mir_shape(2, 2, {MK_Reg, MK_Frame});
    }

    const uint8_t base = MK_Reg | MK_Frame;
    switch (x86_format(static_cast<X86Op>(opcode))) {
        case InstFormat::RR:
        case InstFormat::Cmov:
            return mir_shape(2, 2, {MK_Reg, MK_Reg});
        case InstFormat::RI:
        case InstFormat::MovAbs:
            return mir_shape(2, 2, {MK_Reg, MK_Imm});
        case InstFormat::R1:
            return mir_shape(1, kMirUnbounded, {MK_Reg});
        case InstFormat::Load:
        case InstFormat::Store:
            return mir_shape_class(mir_shape(3, 3, {MK_Reg, base, MK_Imm}), 1,
                                   RegClass::Gpr);
        case InstFormat::MemRmw:

            return mir_shape_class(
                mir_shape(3, kMirUnbounded, {MK_Reg, base, MK_Imm}), 1,
                RegClass::Gpr);
        case InstFormat::FpuMem:
            return mir_shape_class(mir_shape(2, 2, {base, MK_Imm}), 0,
                                   RegClass::Gpr);
        case InstFormat::RipR:
        case InstFormat::SymImm:
            return mir_shape(2, 2, {MK_Reg, MK_Symbol});
        case InstFormat::ShiftCl:

            return mir_shape(1, kMirUnbounded, {MK_Reg, MK_Reg});
        case InstFormat::Jmp:
        case InstFormat::Jcc:
            return mir_shape(1, 1, {MK_Label});
        case InstFormat::JmpReg:
        case InstFormat::CallReg:
            return mir_shape_class(mir_shape(1, 1, {MK_Reg}), 0, RegClass::Gpr);
        case InstFormat::CallSym:
            return mir_shape(1, 1, {MK_Symbol});
        case InstFormat::Setcc:
            return mir_shape_class(mir_shape(1, 1, {MK_Reg}), 0, RegClass::Gpr);
        case InstFormat::DivR:

            return mir_shape(1, kMirUnbounded, {MK_Reg, MK_Reg, MK_Reg});
        case InstFormat::NoOps:

            return mir_shape(0, kMirUnbounded, {});
        case InstFormat::Ret:
        case InstFormat::AsmText:
            return mir_shape(0, 0, {});
    }
    return mir_shape(0, kMirUnbounded, {});
}

const MirTargetInfo& x86_mir_target() {
    static const MirTargetInfo info = [] {
        MirTargetInfo target;
        target.mnemonic = x86_mnemonic_u16;
        target.facts = x86_mir_facts;
        target.shape = x86_mir_shape;
        target.phys_reg_count = XMM15 + 1;
        return target;
    }();
    return info;
}

const TargetRegInfo& reg_info_32() {
    static const TargetRegInfo info = [] {
        TargetRegInfo regs;

        regs.gpr_order = {RAX, RCX, RDX, RBX};
        for (uint32_t r = XMM0; r <= XMM7; ++r) {
            regs.fpr_order.push_back(r);
        }
        regs.is_callee_saved = is_callee_saved_reg_32;
        regs.reg_class = phys_reg_class;
        regs.linear_gpr_caller = {};
        regs.linear_gpr_callee = {RBX};
        for (uint32_t r = XMM0; r < xmm(5); ++r) {
            regs.linear_fpr_caller.push_back(r);
        }
        regs.linear_fpr_callee = {};
        regs.linear_gpr_scratch = {RAX, RCX, RDX};
        regs.linear_fpr_scratch = {xmm(5), xmm(6), xmm(7)};
        return regs;
    }();
    return info;
}

const TargetRegInfo& reg_info() {
    static const TargetRegInfo info = [] {
        TargetRegInfo regs;
        regs.gpr_order = {R10, R11, RBX, R12, R13, R14, R15,
                          RAX, RCX, RDX, RSI, RDI, R8, R9};
        for (uint32_t r = XMM8; r <= XMM15; ++r) {
            regs.fpr_order.push_back(r);
        }
        for (uint32_t r = XMM0; r <= XMM7; ++r) {
            regs.fpr_order.push_back(r);
        }
        regs.is_callee_saved = is_callee_saved_reg;
        regs.reg_class = phys_reg_class;

        regs.linear_gpr_caller = {};
        regs.linear_gpr_callee = {RBX, R12, R13, R14, R15};
        for (uint32_t r = XMM8; r < XMM13; ++r) {
            regs.linear_fpr_caller.push_back(r);
        }
        regs.linear_fpr_callee = {};
        regs.linear_gpr_scratch = {R10, R11};
        regs.linear_fpr_scratch = {xmm(13), xmm(14), xmm(15)};
        return regs;
    }();
    return info;
}

} // namespace aburi::backend::x86
