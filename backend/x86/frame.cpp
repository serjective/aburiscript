#include "frame.h"

#include <algorithm>
#include <vector>

#include "insts.h"
#include "target.h"

namespace aburi::backend::x86 {

namespace {

uint64_t align_up(uint64_t value, uint64_t align) {
    return (value + align - 1) & ~(align - 1);
}

uint16_t op(X86Op o) { return static_cast<uint16_t>(o); }

MInst make_inst(X86Op o, std::vector<MOperand> operands, uint32_t aux = 0) {
    MInst inst;
    inst.opcode = op(o);
    inst.aux = aux;
    inst.operands = std::move(operands);
    return inst;
}

MOperand reg_op(uint32_t phys) { return MOperand::make_reg(MReg::phys(phys)); }

} // namespace

void lower_frame(MFunction& function) {
    bool dynamic = function.has_dynamic_stack;
    bool legacy32 = function.legacy32;

    uint64_t word = legacy32 ? 4 : 8;
    X86Op word_load = legacy32 ? X86Op::Load32 : X86Op::Load64;
    X86Op word_store = legacy32 ? X86Op::Store32 : X86Op::Store64;
    uint64_t outgoing = dynamic ? 0 : align_up(function.max_outgoing_bytes, 16);

    std::vector<uint32_t> csrs;
    for (uint32_t phys : function.used_csrs) {
        csrs.push_back(phys);
    }
    std::sort(csrs.begin(), csrs.end());
    uint64_t csr_size = align_up(word * csrs.size(), 16);
    uint64_t save_base = outgoing;

    std::vector<uint64_t> offsets(function.frame_objects.size(), 0);
    uint64_t running = outgoing + csr_size;
    for (size_t i = 0; i < function.frame_objects.size(); ++i) {
        const FrameObject& object = function.frame_objects[i];
        running = align_up(running, std::max<uint32_t>(1, object.align));
        offsets[i] = running;
        running += std::max<uint64_t>(1, object.size);
    }
    uint64_t frame_size = align_up(running, 16);

    int64_t cfa_from_rbp = static_cast<int64_t>(2 * word);
    function.csr_cfa_offsets.clear();
    {
        uint64_t slot = save_base;
        for (uint32_t phys : csrs) {
            function.csr_cfa_offsets.push_back(
                {phys, static_cast<int32_t>(static_cast<int64_t>(slot) -
                                            static_cast<int64_t>(frame_size) -
                                            cfa_from_rbp)});
            slot += word;
        }
    }

    for (MBlock& block : function.blocks) {
        std::vector<MInst> out;
        out.reserve(block.insts.size() + 8);
        for (MInst& inst : block.insts) {
            X86Op opcode = static_cast<X86Op>(inst.opcode);

            if (opcode == X86Op::FrameAddr) {
                uint64_t offset = offsets[inst.operands[1].frame_index] +
                                  static_cast<uint64_t>(inst.operands[1].imm);
                MOperand dst = inst.operands[0];
                if (dynamic) {

                    out.push_back(make_inst(
                        X86Op::LeaMem,
                        {dst, reg_op(RBP),
                         MOperand::make_imm(static_cast<int64_t>(offset) -
                                            static_cast<int64_t>(frame_size))}));
                } else {
                    out.push_back(make_inst(
                        X86Op::LeaMem,
                        {dst, reg_op(RSP),
                         MOperand::make_imm(static_cast<int64_t>(offset))}));
                }
                continue;
            }

            if (opcode == X86Op::EpilogueRet) {

                uint64_t slot = save_base;
                for (uint32_t phys : csrs) {
                    out.push_back(make_inst(
                        word_load,
                        {reg_op(phys), reg_op(RBP),
                         MOperand::make_imm(static_cast<int64_t>(slot) -
                                            static_cast<int64_t>(frame_size))}));
                    slot += word;
                }
                out.push_back(
                    make_inst(X86Op::MovRR64, {reg_op(RSP), reg_op(RBP)}));
                out.push_back(make_inst(X86Op::PopR, {reg_op(RBP)}));
                out.push_back(make_inst(X86Op::RetQ, {}));
                continue;
            }

            size_t base_index =
                x86_format(opcode) == InstFormat::FpuMem ? 0 : 1;
            if (inst.operands.size() >= base_index + 2 &&
                inst.operands[base_index].kind == MOperandKind::FrameIndex) {
                uint64_t offset =
                    offsets[inst.operands[base_index].frame_index] +
                    static_cast<uint64_t>(inst.operands[base_index].imm) +
                    static_cast<uint64_t>(inst.operands[base_index + 1].imm);
                if (dynamic) {
                    inst.operands[base_index] = reg_op(RBP);
                    inst.operands[base_index + 1] = MOperand::make_imm(
                        static_cast<int64_t>(offset) -
                        static_cast<int64_t>(frame_size));
                } else {
                    inst.operands[base_index] = reg_op(RSP);
                    inst.operands[base_index + 1] =
                        MOperand::make_imm(static_cast<int64_t>(offset));
                }
            }
            out.push_back(std::move(inst));
        }
        block.insts = std::move(out);
    }

    std::vector<MInst> prologue;
    prologue.push_back(make_inst(X86Op::PushR, {reg_op(RBP)}));
    prologue.push_back(make_inst(X86Op::MovRR64, {reg_op(RBP), reg_op(RSP)}));
    if (frame_size != 0) {
        prologue.push_back(make_inst(
            X86Op::SubI64,
            {reg_op(RSP),
             MOperand::make_imm(static_cast<int64_t>(frame_size))}));
    }
    uint64_t slot = save_base;
    for (uint32_t phys : csrs) {
        prologue.push_back(make_inst(
            word_store,
            {reg_op(phys), reg_op(RSP),
             MOperand::make_imm(static_cast<int64_t>(slot))}));
        slot += word;
    }
    if (!function.blocks.empty()) {
        MBlock& entry = function.blocks.front();
        entry.insts.insert(entry.insts.begin(),
                           std::make_move_iterator(prologue.begin()),
                           std::make_move_iterator(prologue.end()));
    }
}

} // namespace aburi::backend::x86
