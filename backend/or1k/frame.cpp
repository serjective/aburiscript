#include "frame.h"

#include <algorithm>
#include <vector>

#include "insts.h"
#include "target.h"

namespace aburi::backend::or1k {

namespace {

uint64_t align_up(uint64_t value, uint64_t align) {
    return (value + align - 1) & ~(align - 1);
}

uint16_t op(Or1kOp o) { return static_cast<uint16_t>(o); }

MInst make_inst(Or1kOp o, std::vector<MOperand> operands, uint32_t aux = 0) {
    MInst inst;
    inst.opcode = op(o);
    inst.aux = aux;
    inst.operands = std::move(operands);
    return inst;
}

MOperand reg_op(uint32_t phys) { return MOperand::make_reg(MReg::phys(phys)); }

bool fits_simm16(int64_t v) { return v >= -32768 && v <= 32767; }

void emit_frame_addr(std::vector<MInst>& out, uint32_t dst, int64_t offset) {
    if (fits_simm16(offset)) {
        out.push_back(make_inst(Or1kOp::Addi,
                                {reg_op(dst), reg_op(SP),
                                 MOperand::make_imm(offset)}));
        return;
    }
    uint32_t value = static_cast<uint32_t>(offset);
    out.push_back(make_inst(Or1kOp::Movhi,
                            {reg_op(R13), MOperand::make_imm(value >> 16)}));
    out.push_back(make_inst(Or1kOp::Ori,
                            {reg_op(R13), reg_op(R13),
                             MOperand::make_imm(value & 0xffff)}));
    out.push_back(make_inst(Or1kOp::Add,
                            {reg_op(dst), reg_op(SP), reg_op(R13)}));
}

} // namespace

void lower_frame(MFunction& function) {

    bool non_leaf = false;
    for (const MBlock& block : function.blocks) {
        for (const MInst& inst : block.insts) {
            if ((or1k_flags(static_cast<Or1kOp>(inst.opcode)) & OR1K_CALL) != 0) {
                non_leaf = true;
            }
        }
    }
    bool needs_fp = function.named_stack_bytes > 0 ||
                    function.has_dynamic_stack ||
                    function.needs_frame_pointer;

    uint64_t outgoing = align_up(function.max_outgoing_bytes, 4);

    std::vector<uint32_t> csrs;
    for (uint32_t phys : function.used_csrs) {
        csrs.push_back(phys);
    }
    std::sort(csrs.begin(), csrs.end());

    std::vector<uint32_t> saves;
    if (non_leaf) {
        saves.push_back(LR);
    }
    if (needs_fp) {
        saves.push_back(FP);
    }
    for (uint32_t phys : csrs) {
        saves.push_back(phys);
    }

    std::vector<uint64_t> offsets(function.frame_objects.size(), 0);
    uint64_t running = outgoing;
    for (size_t i = 0; i < function.frame_objects.size(); ++i) {
        const FrameObject& object = function.frame_objects[i];
        running = align_up(running, std::max<uint32_t>(1, object.align));
        offsets[i] = running;
        running += std::max<uint64_t>(1, object.size);
    }
    uint64_t save_base = align_up(running, 4);
    uint64_t frame_size = align_up(save_base + 4 * saves.size(), 8);
    function.frame_size = static_cast<uint32_t>(frame_size);

    function.csr_cfa_offsets.clear();
    {
        uint64_t slot = save_base;
        for (uint32_t phys : saves) {
            function.csr_cfa_offsets.push_back(
                {phys, static_cast<int32_t>(static_cast<int64_t>(slot) -
                                            static_cast<int64_t>(frame_size))});
            slot += 4;
        }
    }

    for (MBlock& block : function.blocks) {
        std::vector<MInst> out;
        out.reserve(block.insts.size() + 8);
        for (MInst& inst : block.insts) {
            Or1kOp opcode = static_cast<Or1kOp>(inst.opcode);

            if (opcode == Or1kOp::FrameAddr) {
                uint64_t offset = offsets[inst.operands[1].frame_index] +
                                  static_cast<uint64_t>(inst.operands[1].imm);
                emit_frame_addr(out, inst.operands[0].reg.index(),
                                static_cast<int64_t>(offset));
                continue;
            }

            if (opcode == Or1kOp::EpilogueRet) {

                uint64_t slot = save_base;
                for (uint32_t phys : saves) {
                    out.push_back(make_inst(
                        Or1kOp::Lwz,
                        {reg_op(phys), reg_op(SP),
                         MOperand::make_imm(static_cast<int64_t>(slot))}));
                    slot += 4;
                }
                if (frame_size != 0) {
                    out.push_back(make_inst(
                        Or1kOp::Addi,
                        {reg_op(SP), reg_op(SP),
                         MOperand::make_imm(static_cast<int64_t>(frame_size))}));
                }
                out.push_back(make_inst(Or1kOp::Jr, {reg_op(LR)}));
                continue;
            }

            if (inst.operands.size() >= 3 &&
                inst.operands[1].kind == MOperandKind::FrameIndex) {
                uint64_t offset = offsets[inst.operands[1].frame_index] +
                                  static_cast<uint64_t>(inst.operands[1].imm) +
                                  static_cast<uint64_t>(inst.operands[2].imm);
                if (fits_simm16(static_cast<int64_t>(offset))) {
                    inst.operands[1] = reg_op(SP);
                    inst.operands[2] =
                        MOperand::make_imm(static_cast<int64_t>(offset));
                } else {

                    emit_frame_addr(out, R13, static_cast<int64_t>(offset));
                    inst.operands[1] = reg_op(R13);
                    inst.operands[2] = MOperand::make_imm(0);
                }
            }
            out.push_back(std::move(inst));
        }
        block.insts = std::move(out);
    }

    std::vector<MInst> prologue;
    if (frame_size != 0) {
        prologue.push_back(make_inst(
            Or1kOp::Addi,
            {reg_op(SP), reg_op(SP),
             MOperand::make_imm(-static_cast<int64_t>(frame_size))}));
    }
    if (needs_fp) {

        prologue.push_back(make_inst(
            Or1kOp::Addi,
            {reg_op(FP), reg_op(SP),
             MOperand::make_imm(static_cast<int64_t>(frame_size))}));
    }
    uint64_t slot = save_base;
    for (uint32_t phys : saves) {
        prologue.push_back(make_inst(
            Or1kOp::Sw,
            {reg_op(phys), reg_op(SP),
             MOperand::make_imm(static_cast<int64_t>(slot))}));
        slot += 4;
    }
    if (!function.blocks.empty()) {
        MBlock& entry = function.blocks.front();
        entry.insts.insert(entry.insts.begin(),
                           std::make_move_iterator(prologue.begin()),
                           std::make_move_iterator(prologue.end()));
    }
}

} // namespace aburi::backend::or1k
