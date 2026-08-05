#include "regalloc.h"

#include <algorithm>
#include <cstddef>
#include <unordered_map>
#include <vector>

namespace aburi::backend {

namespace {

constexpr uint32_t kNoReg = ~0u;
constexpr uint32_t kNoPos = ~0u;

struct Interval {
    uint32_t vreg = 0;
    uint32_t start = kNoPos;
    uint32_t end = 0;
    bool crosses_call = false;
    uint32_t assigned = kNoReg;
    bool spilled = false;
};

struct Liveness {
    size_t words = 0;
    std::vector<uint64_t> use;
    std::vector<uint64_t> def;
    std::vector<uint64_t> live_in;
    std::vector<uint64_t> live_out;

    uint64_t* row(std::vector<uint64_t>& set, size_t block) {
        return set.data() + block * words;
    }
};

struct InstRegs {
    uint32_t def_vreg = kNoReg;
    bool def_also_read = false;
    std::vector<uint32_t> use_vregs;
};

InstRegs classify_inst(const MInst& inst, const RegAllocOpcodeInfo& info) {
    InstRegs regs;
    for (size_t i = 0; i < inst.operands.size(); ++i) {
        const MOperand& operand = inst.operands[i];
        if (operand.kind != MOperandKind::Reg || !operand.reg.is_virtual()) {
            continue;
        }
        uint32_t vreg = operand.reg.index();
        if (i == 0 && info.defines_operand0) {
            regs.def_vreg = vreg;
            regs.def_also_read = info.reads_operand0;
            continue;
        }
        regs.use_vregs.push_back(vreg);
    }
    return regs;
}

} // namespace

void LinearScanAllocator::run(MFunction& function, const TargetRegInfo& regs,
                              OpcodeInfoFn opcode_info) {
    const size_t vreg_count = function.vreg_classes.size();
    const size_t block_count = function.blocks.size();
    if (vreg_count == 0) {
        return;
    }

    std::vector<uint32_t> block_first(block_count, 0);
    std::vector<uint32_t> block_last(block_count, 0);
    uint32_t position = 0;
    for (size_t b = 0; b < block_count; ++b) {
        block_first[b] = position;
        position += static_cast<uint32_t>(function.blocks[b].insts.size());
        block_last[b] = position;
    }

    Liveness live;
    live.words = (vreg_count + 63) / 64;
    live.use.assign(block_count * live.words, 0);
    live.def.assign(block_count * live.words, 0);
    live.live_in.assign(block_count * live.words, 0);
    live.live_out.assign(block_count * live.words, 0);

    auto set_bit = [&](std::vector<uint64_t>& set, size_t block, uint32_t vreg) {
        set[block * live.words + vreg / 64] |= uint64_t{1} << (vreg % 64);
    };
    auto test_bit = [&](const std::vector<uint64_t>& set, size_t block,
                        uint32_t vreg) {
        return (set[block * live.words + vreg / 64] >> (vreg % 64)) & 1;
    };

    for (size_t b = 0; b < block_count; ++b) {
        for (const MInst& inst : function.blocks[b].insts) {
            InstRegs iregs = classify_inst(inst, opcode_info(inst.opcode));
            for (uint32_t vreg : iregs.use_vregs) {
                if (!test_bit(live.def, b, vreg)) {
                    set_bit(live.use, b, vreg);
                }
            }
            if (iregs.def_vreg != kNoReg) {
                if (iregs.def_also_read && !test_bit(live.def, b, iregs.def_vreg)) {
                    set_bit(live.use, b, iregs.def_vreg);
                }
                set_bit(live.def, b, iregs.def_vreg);
            }
        }
    }

    bool changed = true;
    while (changed) {
        changed = false;
        for (size_t bi = block_count; bi-- > 0;) {
            uint64_t* out_row = live.row(live.live_out, bi);
            for (uint32_t succ : function.blocks[bi].succs) {
                const uint64_t* succ_in = live.row(live.live_in, succ);
                for (size_t w = 0; w < live.words; ++w) {
                    uint64_t merged = out_row[w] | succ_in[w];
                    if (merged != out_row[w]) {
                        out_row[w] = merged;
                        changed = true;
                    }
                }
            }
            uint64_t* in_row = live.row(live.live_in, bi);
            const uint64_t* use_row = live.row(live.use, bi);
            const uint64_t* def_row = live.row(live.def, bi);
            for (size_t w = 0; w < live.words; ++w) {
                uint64_t computed = use_row[w] | (out_row[w] & ~def_row[w]);
                if (computed != in_row[w]) {
                    in_row[w] = computed;
                    changed = true;
                }
            }
        }
    }

    std::vector<Interval> intervals(vreg_count);
    for (uint32_t v = 0; v < vreg_count; ++v) {
        intervals[v].vreg = v;
    }
    auto extend = [&](uint32_t vreg, uint32_t from, uint32_t to) {
        Interval& interval = intervals[vreg];
        interval.start = std::min(interval.start, from);
        interval.end = std::max(interval.end, to);
    };

    std::vector<uint32_t> call_positions;
    for (size_t b = 0; b < block_count; ++b) {
        for (uint32_t v = 0; v < vreg_count; ++v) {
            if (test_bit(live.live_in, b, v)) {
                extend(v, block_first[b], block_first[b] + 1);
            }
            if (test_bit(live.live_out, b, v)) {
                extend(v, block_last[b] > 0 ? block_last[b] - 1 : 0,
                       block_last[b]);
            }
        }
        uint32_t index = block_first[b];
        for (const MInst& inst : function.blocks[b].insts) {
            RegAllocOpcodeInfo info = opcode_info(inst.opcode);
            InstRegs iregs = classify_inst(inst, info);
            for (uint32_t vreg : iregs.use_vregs) {
                extend(vreg, index, index + 1);
            }
            if (iregs.def_vreg != kNoReg) {
                extend(iregs.def_vreg, index, index + 1);
            }
            if (info.is_call) {
                call_positions.push_back(index);
            }
            ++index;
        }
    }
    std::sort(call_positions.begin(), call_positions.end());

    for (Interval& interval : intervals) {
        if (interval.start == kNoPos) {
            continue;
        }

        auto first_call = std::lower_bound(call_positions.begin(),
                                           call_positions.end(),
                                           interval.start);
        interval.crosses_call = first_call != call_positions.end() &&
                                *first_call + 1 < interval.end;
    }

    std::vector<uint32_t> order;
    order.reserve(vreg_count);
    for (uint32_t v = 0; v < vreg_count; ++v) {
        if (intervals[v].start != kNoPos) {
            order.push_back(v);
        }
    }
    std::sort(order.begin(), order.end(), [&](uint32_t a, uint32_t b) {
        if (intervals[a].start != intervals[b].start) {
            return intervals[a].start < intervals[b].start;
        }
        return a < b;
    });

    std::vector<uint32_t> active;
    std::unordered_map<uint32_t, uint32_t> reg_holder;

    auto note_used_csr = [&](uint32_t phys) {
        if (!regs.is_callee_saved(phys)) {
            return;
        }
        for (uint32_t used : function.used_csrs) {
            if (used == phys) {
                return;
            }
        }
        function.used_csrs.push_back(phys);
    };

    for (uint32_t v : order) {
        Interval& interval = intervals[v];

        for (size_t i = active.size(); i-- > 0;) {
            if (intervals[active[i]].end <= interval.start) {
                reg_holder.erase(intervals[active[i]].assigned);
                active.erase(active.begin() + static_cast<ptrdiff_t>(i));
            }
        }

        RegClass cls = function.vreg_classes[v];
        const std::vector<uint32_t>& caller_pool =
            cls == RegClass::Gpr ? regs.linear_gpr_caller
                                 : regs.linear_fpr_caller;

        static const std::vector<uint32_t> no_callee_pool;
        const std::vector<uint32_t>& callee_pool =
            cls == RegClass::Gpr ? regs.linear_gpr_callee
            : cls == RegClass::Fpr128 ? no_callee_pool
                                      : regs.linear_fpr_callee;

        auto try_pool = [&](const std::vector<uint32_t>& pool) -> uint32_t {
            for (uint32_t phys : pool) {
                if (!reg_holder.contains(phys)) {
                    return phys;
                }
            }
            return kNoReg;
        };

        uint32_t phys = kNoReg;
        if (interval.crosses_call) {
            phys = try_pool(callee_pool);
        } else {
            phys = try_pool(caller_pool);
            if (phys == kNoReg) {
                phys = try_pool(callee_pool);
            }
        }
        if (phys == kNoReg) {
            interval.spilled = true;
            continue;
        }
        interval.assigned = phys;
        reg_holder[phys] = v;
        active.push_back(v);
        note_used_csr(phys);
    }

    std::unordered_map<uint32_t, uint32_t> spill_slots;
    auto slot_for = [&](uint32_t vreg) {
        auto found = spill_slots.find(vreg);
        if (found != spill_slots.end()) {
            return found->second;
        }
        RegClass cls = function.vreg_classes[vreg];
        uint32_t bytes =
            cls == RegClass::Fpr128 ? 16
            : cls == RegClass::Fpr  ? 8
                                    : function.word_bytes;
        uint32_t slot = function.new_frame_object(bytes, bytes);
        spill_slots[vreg] = slot;
        return slot;
    };
    auto make_mem = [&](uint16_t opcode, uint32_t phys, uint32_t slot) {
        MInst inst;
        inst.opcode = opcode;
        inst.operands.push_back(MOperand::make_reg(MReg::phys(phys)));
        inst.operands.push_back(MOperand::make_frame(slot));
        inst.operands.push_back(MOperand::make_imm(0));
        return inst;
    };

    for (MBlock& block : function.blocks) {
        std::vector<MInst> out;
        out.reserve(block.insts.size());
        for (MInst& inst : block.insts) {
            RegAllocOpcodeInfo info = opcode_info(inst.opcode);

            std::unordered_map<uint32_t, uint32_t> inst_scratch;
            size_t next_gpr_scratch = 0;
            size_t next_fpr_scratch = 0;
            auto scratch_for = [&](uint32_t vreg) -> uint32_t {
                auto found = inst_scratch.find(vreg);
                if (found != inst_scratch.end()) {
                    return found->second;
                }
                RegClass cls = function.vreg_classes[vreg];
                const std::vector<uint32_t>& pool =
                    cls == RegClass::Gpr ? regs.linear_gpr_scratch
                                         : regs.linear_fpr_scratch;
                size_t& next = cls == RegClass::Gpr ? next_gpr_scratch
                                                    : next_fpr_scratch;
                uint32_t phys = pool[next < pool.size() ? next : pool.size() - 1];
                ++next;
                inst_scratch[vreg] = phys;
                return phys;
            };

            std::vector<MInst> reloads;
            std::vector<MInst> stores;
            for (size_t i = 0; i < inst.operands.size(); ++i) {
                MOperand& operand = inst.operands[i];
                if (operand.kind != MOperandKind::Reg ||
                    !operand.reg.is_virtual()) {
                    continue;
                }
                uint32_t vreg = operand.reg.index();
                const Interval& interval = intervals[vreg];
                bool is_def = i == 0 && info.defines_operand0;
                if (!interval.spilled) {
                    operand.reg = MReg::phys(interval.assigned);
                    continue;
                }
                uint32_t phys = scratch_for(vreg);
                uint32_t slot = slot_for(vreg);
                RegClass cls = function.vreg_classes[vreg];
                bool needs_reload = !is_def || info.reads_operand0;
                if (needs_reload) {
                    bool already = false;
                    for (const MInst& reload : reloads) {
                        if (reload.operands[0].reg.index() == phys) {
                            already = true;
                            break;
                        }
                    }
                    if (!already) {
                        reloads.push_back(
                            make_mem(regalloc_reload_opcode(cls), phys, slot));
                    }
                }
                if (is_def) {
                    stores.push_back(
                        make_mem(regalloc_spill_opcode(cls), phys, slot));
                }
                operand.reg = MReg::phys(phys);
            }

            for (MInst& reload : reloads) {
                out.push_back(std::move(reload));
            }
            out.push_back(std::move(inst));
            for (MInst& store : stores) {
                out.push_back(std::move(store));
            }
        }
        block.insts = std::move(out);
    }
}

} // namespace aburi::backend
