#include "frame.h"

#include <algorithm>
#include <vector>

#include "insts.h"
#include "target.h"

namespace aburi::backend::aarch64 {

namespace {

uint64_t align_up(uint64_t value, uint64_t align) {
    return (value + align - 1) & ~(align - 1);
}

uint16_t op(A64Op o) { return static_cast<uint16_t>(o); }

uint32_t mem_access_size(A64Op o) {
    switch (o) {
        case A64Op::LdrQ:
        case A64Op::StrQ:
            return 16;
        case A64Op::LdrX:
        case A64Op::StrX:
        case A64Op::LdrD:
        case A64Op::StrD:
            return 8;
        case A64Op::LdrW:
        case A64Op::StrW:
        case A64Op::LdrS:
        case A64Op::StrS:
        case A64Op::Ldrsw:
            return 4;
        case A64Op::LdrhW:
        case A64Op::StrhW:
        case A64Op::LdrshW:
            return 2;
        default:
            return 1;
    }
}

bool bare_base_only(A64Op o) {
    switch (o) {
        case A64Op::LdarbW:
        case A64Op::LdarhW:
        case A64Op::LdarW:
        case A64Op::LdarX:
        case A64Op::StlrbW:
        case A64Op::StlrhW:
        case A64Op::StlrW:
        case A64Op::StlrX:
            return true;
        default:
            return false;
    }
}

MInst make_inst(A64Op o, std::vector<MOperand> operands, uint32_t aux = 0) {
    MInst inst;
    inst.opcode = op(o);
    inst.aux = aux;
    inst.operands = std::move(operands);
    return inst;
}

MOperand reg_op(uint32_t phys) { return MOperand::make_reg(MReg::phys(phys)); }

void emit_offset_into_x16(std::vector<MInst>& out, uint64_t offset) {
    bool started = false;
    for (int i = 0; i < 4; ++i) {
        uint64_t chunk = (offset >> (16 * i)) & 0xFFFF;
        if (!started) {
            if (chunk == 0 && offset != 0) {
                continue;
            }
            out.push_back(make_inst(
                A64Op::MovzX,
                {reg_op(X16), MOperand::make_imm(static_cast<int64_t>(chunk))},
                static_cast<uint32_t>(i)));
            started = true;
            continue;
        }
        if (chunk != 0) {
            out.push_back(make_inst(
                A64Op::MovkX,
                {reg_op(X16), MOperand::make_imm(static_cast<int64_t>(chunk))},
                static_cast<uint32_t>(i)));
        }
    }
    if (!started) {
        out.push_back(make_inst(A64Op::MovzX,
                                {reg_op(X16), MOperand::make_imm(0)}, 0));
    }
}

void emit_sp_adjust(std::vector<MInst>& out, bool subtract, uint64_t amount) {
    if (amount == 0) {
        return;
    }
    if (amount <= 4095) {
        out.push_back(make_inst(subtract ? A64Op::SubXri : A64Op::AddXri,
                                {reg_op(SP), reg_op(SP),
                                 MOperand::make_imm(static_cast<int64_t>(amount))}));
        return;
    }
    emit_offset_into_x16(out, amount);
    out.push_back(make_inst(subtract ? A64Op::SubX : A64Op::AddX,
                            {reg_op(SP), reg_op(SP), reg_op(X16)}));
}

} // namespace

void lower_frame(MFunction& function) {

    bool dynamic = function.has_dynamic_stack;
    uint64_t outgoing = dynamic ? 0 : align_up(function.max_outgoing_bytes, 16);

    std::vector<uint32_t> gpr_csrs;
    std::vector<uint32_t> fpr_csrs;
    for (uint32_t phys : function.used_csrs) {
        if (is_fpr_index(phys)) {
            fpr_csrs.push_back(phys);
        } else {
            gpr_csrs.push_back(phys);
        }
    }
    std::sort(gpr_csrs.begin(), gpr_csrs.end());
    std::sort(fpr_csrs.begin(), fpr_csrs.end());
    uint64_t csr_size =
        align_up(8 * (gpr_csrs.size() + fpr_csrs.size()), 16);
    uint64_t save_base = outgoing;

    bool save_pairs = save_base + csr_size <= 504;

    std::vector<uint64_t> offsets(function.frame_objects.size(), 0);
    uint64_t running = outgoing + csr_size;
    for (size_t i = 0; i < function.frame_objects.size(); ++i) {
        const FrameObject& object = function.frame_objects[i];
        running = align_up(running, std::max<uint32_t>(1, object.align));
        offsets[i] = running;
        running += std::max<uint64_t>(1, object.size);
    }
    uint64_t frame_size = align_up(running, 16);

    function.csr_cfa_offsets.clear();
    {
        uint64_t slot = save_base;
        for (uint32_t phys : gpr_csrs) {
            function.csr_cfa_offsets.push_back(
                {phys, static_cast<int32_t>(static_cast<int64_t>(slot) -
                                            static_cast<int64_t>(frame_size) -
                                            16)});
            slot += 8;
        }
        for (uint32_t phys : fpr_csrs) {
            function.csr_cfa_offsets.push_back(
                {phys, static_cast<int32_t>(static_cast<int64_t>(slot) -
                                            static_cast<int64_t>(frame_size) -
                                            16)});
            slot += 8;
        }
    }

    for (MBlock& block : function.blocks) {
        std::vector<MInst> out;
        out.reserve(block.insts.size() + 8);
        for (MInst& inst : block.insts) {
            A64Op opcode = static_cast<A64Op>(inst.opcode);

            if (opcode == A64Op::FrameAddr) {
                uint64_t offset = offsets[inst.operands[1].frame_index] +
                                  static_cast<uint64_t>(inst.operands[1].imm);
                MOperand dst = inst.operands[0];
                if (dynamic) {

                    uint64_t distance = frame_size - offset;
                    emit_offset_into_x16(out, distance);
                    out.push_back(
                        make_inst(A64Op::SubX, {dst, reg_op(X29), reg_op(X16)}));
                } else if (offset <= 4095) {
                    out.push_back(make_inst(
                        A64Op::AddXri,
                        {dst, reg_op(SP),
                         MOperand::make_imm(static_cast<int64_t>(offset))}));
                } else {
                    emit_offset_into_x16(out, offset);
                    out.push_back(
                        make_inst(A64Op::AddX, {dst, reg_op(SP), reg_op(X16)}));
                }
                continue;
            }

            if (opcode == A64Op::EpilogueRet ||
                opcode == A64Op::EpilogueTailBr) {

                if (dynamic) {

                    if (frame_size <= 4095) {
                        out.push_back(make_inst(
                            A64Op::SubXri,
                            {reg_op(SP), reg_op(X29),
                             MOperand::make_imm(static_cast<int64_t>(frame_size))}));
                    } else {
                        emit_offset_into_x16(out, frame_size);
                        out.push_back(make_inst(
                            A64Op::SubX,
                            {reg_op(SP), reg_op(X29), reg_op(X16)}));
                    }
                }
                uint64_t save = save_base;
                if (save_pairs) {
                    for (size_t i = 0; i + 1 < gpr_csrs.size(); i += 2, save += 16) {
                        out.push_back(make_inst(
                            A64Op::LdpXoff,
                            {reg_op(gpr_csrs[i]), reg_op(gpr_csrs[i + 1]), reg_op(SP),
                             MOperand::make_imm(static_cast<int64_t>(save))}));
                    }
                    if (gpr_csrs.size() % 2) {
                        out.push_back(make_inst(
                            A64Op::LdrX,
                            {reg_op(gpr_csrs.back()), reg_op(SP),
                             MOperand::make_imm(static_cast<int64_t>(save))}));
                        save += 8;
                    }
                    for (size_t i = 0; i + 1 < fpr_csrs.size(); i += 2, save += 16) {
                        out.push_back(make_inst(
                            A64Op::LdpDoff,
                            {reg_op(fpr_csrs[i]), reg_op(fpr_csrs[i + 1]), reg_op(SP),
                             MOperand::make_imm(static_cast<int64_t>(save))}));
                    }
                    if (fpr_csrs.size() % 2) {
                        out.push_back(make_inst(
                            A64Op::LdrD,
                            {reg_op(fpr_csrs.back()), reg_op(SP),
                             MOperand::make_imm(static_cast<int64_t>(save))}));
                    }
                } else {
                    for (uint32_t phys : gpr_csrs) {
                        out.push_back(make_inst(
                            A64Op::LdrX,
                            {reg_op(phys), reg_op(SP),
                             MOperand::make_imm(static_cast<int64_t>(save))}));
                        save += 8;
                    }
                    for (uint32_t phys : fpr_csrs) {
                        out.push_back(make_inst(
                            A64Op::LdrD,
                            {reg_op(phys), reg_op(SP),
                             MOperand::make_imm(static_cast<int64_t>(save))}));
                        save += 8;
                    }
                }
                emit_sp_adjust(out, false, frame_size);
                out.push_back(make_inst(
                    A64Op::LdpXpost,
                    {reg_op(X29), reg_op(X30), reg_op(SP), MOperand::make_imm(16)}));
                if (opcode == A64Op::EpilogueTailBr) {
                    out.push_back(make_inst(A64Op::BrReg, {reg_op(X17)}));
                } else {
                    out.push_back(make_inst(A64Op::Ret, {}));
                }
                continue;
            }

            InstFormat format = a64_format(opcode);
            if (format == InstFormat::Mem && !inst.operands.empty() &&
                inst.operands.size() >= 3 &&
                inst.operands[1].kind == MOperandKind::FrameIndex) {
                uint64_t offset = offsets[inst.operands[1].frame_index] +
                                  static_cast<uint64_t>(inst.operands[1].imm) +
                                  static_cast<uint64_t>(inst.operands[2].imm);
                uint32_t access = mem_access_size(opcode);
                bool encodable = !dynamic && !bare_base_only(opcode) &&
                    offset % access == 0 && offset / access <= 4095;
                if (encodable) {
                    inst.operands[1] = reg_op(SP);
                    inst.operands[2] = MOperand::make_imm(
                        static_cast<int64_t>(offset));
                } else if (dynamic) {
                    uint64_t distance = frame_size - offset;
                    emit_offset_into_x16(out, distance);
                    out.push_back(make_inst(A64Op::SubX, {reg_op(X16), reg_op(X29),
                                                          reg_op(X16)}));
                    inst.operands[1] = reg_op(X16);
                    inst.operands[2] = MOperand::make_imm(0);
                } else {
                    emit_offset_into_x16(out, offset);
                    out.push_back(make_inst(A64Op::AddX, {reg_op(X16), reg_op(SP),
                                                          reg_op(X16)}));
                    inst.operands[1] = reg_op(X16);
                    inst.operands[2] = MOperand::make_imm(0);
                }
            }

            if ((format == InstFormat::RRMem || format == InstFormat::LseRmw) &&
                inst.operands.size() >= 3 &&
                inst.operands[2].kind == MOperandKind::FrameIndex) {
                uint64_t offset = offsets[inst.operands[2].frame_index] +
                                  static_cast<uint64_t>(inst.operands[2].imm);
                if (dynamic) {
                    uint64_t distance = frame_size - offset;
                    emit_offset_into_x16(out, distance);
                    out.push_back(make_inst(A64Op::SubX, {reg_op(X16), reg_op(X29),
                                                          reg_op(X16)}));
                } else {
                    emit_offset_into_x16(out, offset);
                    out.push_back(make_inst(A64Op::AddX, {reg_op(X16), reg_op(SP),
                                                          reg_op(X16)}));
                }
                inst.operands[2] = reg_op(X16);
            }
            out.push_back(std::move(inst));
        }
        block.insts = std::move(out);
    }

    std::vector<MInst> prologue;
    prologue.push_back(make_inst(
        A64Op::StpXpre,
        {reg_op(X29), reg_op(X30), reg_op(SP), MOperand::make_imm(-16)}));
    prologue.push_back(make_inst(A64Op::MovX, {reg_op(X29), reg_op(SP)}));
    emit_sp_adjust(prologue, true, frame_size);
    uint64_t save = save_base;
    if (save_pairs) {
        for (size_t i = 0; i + 1 < gpr_csrs.size(); i += 2, save += 16) {
            prologue.push_back(make_inst(
                A64Op::StpXoff,
                {reg_op(gpr_csrs[i]), reg_op(gpr_csrs[i + 1]), reg_op(SP),
                 MOperand::make_imm(static_cast<int64_t>(save))}));
        }
        if (gpr_csrs.size() % 2) {
            prologue.push_back(make_inst(
                A64Op::StrX, {reg_op(gpr_csrs.back()), reg_op(SP),
                              MOperand::make_imm(static_cast<int64_t>(save))}));
            save += 8;
        }
        for (size_t i = 0; i + 1 < fpr_csrs.size(); i += 2, save += 16) {
            prologue.push_back(make_inst(
                A64Op::StpDoff,
                {reg_op(fpr_csrs[i]), reg_op(fpr_csrs[i + 1]), reg_op(SP),
                 MOperand::make_imm(static_cast<int64_t>(save))}));
        }
        if (fpr_csrs.size() % 2) {
            prologue.push_back(make_inst(
                A64Op::StrD, {reg_op(fpr_csrs.back()), reg_op(SP),
                              MOperand::make_imm(static_cast<int64_t>(save))}));
        }
    } else {
        for (uint32_t phys : gpr_csrs) {
            prologue.push_back(make_inst(
                A64Op::StrX, {reg_op(phys), reg_op(SP),
                              MOperand::make_imm(static_cast<int64_t>(save))}));
            save += 8;
        }
        for (uint32_t phys : fpr_csrs) {
            prologue.push_back(make_inst(
                A64Op::StrD, {reg_op(phys), reg_op(SP),
                              MOperand::make_imm(static_cast<int64_t>(save))}));
            save += 8;
        }
    }
    if (!function.blocks.empty()) {
        MBlock& entry = function.blocks.front();
        entry.insts.insert(entry.insts.begin(),
                           std::make_move_iterator(prologue.begin()),
                           std::make_move_iterator(prologue.end()));
    }
}

} // namespace aburi::backend::aarch64
