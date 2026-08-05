#include "regalloc.h"

#include <cstddef>
#include <unordered_map>
#include <vector>

namespace aburi::backend {

namespace {

struct SpillHooks {
    uint16_t store_gpr;
    uint16_t load_gpr;
    uint16_t store_fpr;
    uint16_t load_fpr;
    uint16_t store_fpr128;
    uint16_t load_fpr128;
};

} // namespace

static SpillHooks g_spill_hooks;

void set_fast_regalloc_spill_opcodes(uint16_t store_gpr, uint16_t load_gpr,
                                     uint16_t store_fpr, uint16_t load_fpr,
                                     uint16_t store_fpr128,
                                     uint16_t load_fpr128) {
    g_spill_hooks = {store_gpr, load_gpr, store_fpr, load_fpr, store_fpr128,
                     load_fpr128};
}

uint16_t regalloc_spill_opcode(RegClass cls) {
    switch (cls) {
        case RegClass::Gpr: return g_spill_hooks.store_gpr;
        case RegClass::Fpr: return g_spill_hooks.store_fpr;
        case RegClass::Fpr128: return g_spill_hooks.store_fpr128;
    }
    return g_spill_hooks.store_gpr;
}

uint16_t regalloc_reload_opcode(RegClass cls) {
    switch (cls) {
        case RegClass::Gpr: return g_spill_hooks.load_gpr;
        case RegClass::Fpr: return g_spill_hooks.load_fpr;
        case RegClass::Fpr128: return g_spill_hooks.load_fpr128;
    }
    return g_spill_hooks.load_gpr;
}

namespace {

struct AllocState {
    std::unordered_map<uint32_t, uint32_t> vreg_to_phys;
    std::unordered_map<uint32_t, uint32_t> phys_to_vreg;
    std::unordered_map<uint32_t, uint32_t> spill_slots;

    void assign(uint32_t vreg, uint32_t phys) {
        vreg_to_phys[vreg] = phys;
        phys_to_vreg[phys] = vreg;
    }
    void unassign(uint32_t vreg) {
        auto it = vreg_to_phys.find(vreg);
        if (it != vreg_to_phys.end()) {
            phys_to_vreg.erase(it->second);
            vreg_to_phys.erase(it);
        }
    }
};

uint32_t spill_slot_for(MFunction& function, AllocState& state, uint32_t vreg) {
    auto it = state.spill_slots.find(vreg);
    if (it != state.spill_slots.end()) {
        return it->second;
    }
    RegClass cls = function.vreg_classes[vreg];
    uint32_t bytes =
        cls == RegClass::Fpr128 ? 16
        : cls == RegClass::Fpr  ? 8
                                : function.word_bytes;
    uint32_t slot = function.new_frame_object(bytes, bytes);
    state.spill_slots[vreg] = slot;
    return slot;
}

MInst make_spill(MFunction& function, AllocState& state, uint32_t vreg,
                 uint32_t phys) {
    MInst store;
    store.opcode = regalloc_spill_opcode(function.vreg_classes[vreg]);
    store.operands.push_back(MOperand::make_reg(MReg::phys(phys)));
    store.operands.push_back(
        MOperand::make_frame(spill_slot_for(function, state, vreg)));
    store.operands.push_back(MOperand::make_imm(0));
    return store;
}

MInst make_reload(MFunction& function, AllocState& state, uint32_t vreg,
                  uint32_t phys) {
    MInst load;
    load.opcode = regalloc_reload_opcode(function.vreg_classes[vreg]);
    load.operands.push_back(MOperand::make_reg(MReg::phys(phys)));
    load.operands.push_back(
        MOperand::make_frame(spill_slot_for(function, state, vreg)));
    load.operands.push_back(MOperand::make_imm(0));
    return load;
}

void note_used_csr(MFunction& function, const TargetRegInfo& regs,
                   uint32_t phys) {
    if (!regs.is_callee_saved(phys)) {
        return;
    }
    for (uint32_t used : function.used_csrs) {
        if (used == phys) {
            return;
        }
    }
    function.used_csrs.push_back(phys);
}

} // namespace

void FastRegAllocator::run(MFunction& function, const TargetRegInfo& regs,
                           OpcodeInfoFn opcode_info) {
    for (MBlock& block : function.blocks) {
        AllocState state;

        std::unordered_map<uint32_t, size_t> last_use;
        for (size_t i = 0; i < block.insts.size(); ++i) {
            for (const MOperand& op : block.insts[i].operands) {
                if (op.kind == MOperandKind::Reg && op.reg.is_virtual()) {
                    last_use[op.reg.index()] = i;
                }
            }
        }

        std::vector<MInst> out;
        out.reserve(block.insts.size() + 8);

        auto evict_phys = [&](uint32_t phys) {
            auto it = state.phys_to_vreg.find(phys);
            if (it == state.phys_to_vreg.end()) {
                return;
            }
            uint32_t vreg = it->second;
            out.push_back(make_spill(function, state, vreg, phys));
            state.unassign(vreg);
        };

        for (size_t i = 0; i < block.insts.size(); ++i) {
            MInst inst = block.insts[i];
            RegAllocOpcodeInfo info = opcode_info(inst.opcode);

            bool op0_was_virtual = !inst.operands.empty() &&
                                   inst.operands[0].kind == MOperandKind::Reg &&
                                   inst.operands[0].reg.is_virtual();

            std::vector<uint32_t> pinned;
            auto is_pinned = [&](uint32_t phys) {
                for (uint32_t p : pinned) {
                    if (p == phys) {
                        return true;
                    }
                }
                return false;
            };
            for (const MOperand& op : inst.operands) {
                if (op.kind == MOperandKind::Reg && !op.reg.is_virtual()) {
                    pinned.push_back(op.reg.index());
                }
            }

            auto allocate = [&](uint32_t vreg) -> uint32_t {
                RegClass cls = function.vreg_classes[vreg];
                const std::vector<uint32_t>& order =
                    cls == RegClass::Gpr ? regs.gpr_order : regs.fpr_order;
                for (uint32_t phys : order) {
                    if (is_pinned(phys)) {
                        continue;
                    }

                    if (cls == RegClass::Fpr128 && regs.is_callee_saved &&
                        regs.is_callee_saved(phys)) {
                        continue;
                    }
                    if (!state.phys_to_vreg.contains(phys)) {
                        state.assign(vreg, phys);
                        note_used_csr(function, regs, phys);
                        pinned.push_back(phys);
                        return phys;
                    }
                }

                for (uint32_t phys : order) {
                    if (is_pinned(phys)) {
                        continue;
                    }
                    evict_phys(phys);
                    state.assign(vreg, phys);
                    note_used_csr(function, regs, phys);
                    pinned.push_back(phys);
                    return phys;
                }

                return 0;
            };

            for (size_t op_index = 0; op_index < inst.operands.size(); ++op_index) {
                MOperand& op = inst.operands[op_index];
                if (op.kind != MOperandKind::Reg || !op.reg.is_virtual()) {
                    continue;
                }
                bool write_only_def = op_index == 0 && info.defines_operand0 &&
                                      !info.reads_operand0;
                if (write_only_def) {
                    continue;
                }
                uint32_t vreg = op.reg.index();
                auto assigned = state.vreg_to_phys.find(vreg);
                uint32_t phys;
                if (assigned != state.vreg_to_phys.end()) {
                    phys = assigned->second;
                    pinned.push_back(phys);
                } else {
                    phys = allocate(vreg);
                    out.push_back(make_reload(function, state, vreg, phys));
                }
                op.reg = MReg::phys(phys);
            }

            if (info.is_call) {
                std::vector<uint32_t> clobbered;
                for (const auto& [phys, vreg] : state.phys_to_vreg) {
                    if (!regs.is_callee_saved(phys)) {
                        clobbered.push_back(phys);
                    }
                }
                for (uint32_t phys : clobbered) {
                    uint32_t vreg = state.phys_to_vreg[phys];
                    out.push_back(make_spill(function, state, vreg, phys));
                    state.unassign(vreg);
                }
            }

            if (info.defines_operand0 && !inst.operands.empty()) {
                MOperand& def = inst.operands[0];
                if (def.kind == MOperandKind::Reg) {
                    if (def.reg.is_virtual()) {
                        uint32_t vreg = def.reg.index();
                        uint32_t phys;
                        auto assigned = state.vreg_to_phys.find(vreg);
                        if (assigned != state.vreg_to_phys.end()) {
                            phys = assigned->second;
                        } else {
                            phys = allocate(vreg);
                        }
                        def.reg = MReg::phys(phys);
                    } else if (!op0_was_virtual) {

                        evict_phys(def.reg.index());
                    }
                }
            }

            out.push_back(std::move(inst));

            for (const MOperand& op : block.insts[i].operands) {
                if (op.kind != MOperandKind::Reg || !op.reg.is_virtual()) {
                    continue;
                }
                uint32_t vreg = op.reg.index();
                auto last = last_use.find(vreg);
                if (last != last_use.end() && last->second == i) {
                    state.unassign(vreg);
                }
            }
        }

        block.insts = std::move(out);
    }
}

} // namespace aburi::backend
