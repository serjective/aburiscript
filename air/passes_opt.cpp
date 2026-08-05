#include "passes.h"

#include "../numeric/floating_point.h"

#include <cassert>
#include <cstdint>
#include <optional>
#include <span>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace aburi::air {

namespace {

numeric::FloatFormat numeric_float_format(TypeId type) {
    if (type == types::F32) {
        return numeric::FloatFormat::IEEEBinary32;
    }
    if (type == types::F64) {
        return numeric::FloatFormat::IEEEBinary64;
    }
    if (type == types::F80) {
        return numeric::FloatFormat::X87Extended80;
    }
    if (type == types::F128) {
        return numeric::FloatFormat::IEEEBinary128;
    }
    return numeric::FloatFormat::Invalid;
}

numeric::FloatValue numeric_float_value(const ValueData& value) {
    return {numeric_float_format(value.type), value.payload, value.payload2};
}

ValueId intern_float_result(Function& func,
                            TypeId type,
                            const numeric::FloatResult& result) {
    if (!result) {
        return {};
    }
    return func.const_float_bits(type,
                                 result.value.low_bits,
                                 result.value.high_bits);
}

struct PredEdge {
    BlockId from;
    BlockCallId call;
    Opcode terminator;
};

struct CfgFacts {
    std::unordered_map<uint32_t, std::vector<PredEdge>> preds;
    std::unordered_set<uint32_t> protected_blocks;
    bool has_indirect_flow = false;
};

InstId terminator_of(const Function& func, BlockId block) {
    return func.block(block).last;
}

CfgFacts collect_cfg_facts(const Function& func) {
    CfgFacts facts;
    for (uint32_t v = 1; v <= func.value_count(); ++v) {
        const ValueData& value = func.value(ValueId{v});
        if (value.kind == ValueKind::LabelAddr) {
            facts.protected_blocks.insert(static_cast<uint32_t>(value.payload));
            facts.has_indirect_flow = true;
        }
    }
    std::vector<BlockCallId> succs;
    for (BlockId b = func.first_block(); b.is_valid(); b = func.block(b).next) {
        InstId term = terminator_of(func, b);
        if (!term.is_valid()) {
            continue;
        }
        const InstData& data = func.inst(term);
        if (data.op == Opcode::BrIndirect) {
            facts.has_indirect_flow = true;
        }
        func.successors(term, succs);
        for (BlockCallId call : succs) {
            BlockId target = func.block_call(call).target;
            facts.preds[target.index].push_back({b, call, data.op});
            if (data.op == Opcode::BrIndirect) {
                facts.protected_blocks.insert(target.index);
            }
        }
    }
    return facts;
}

bool block_is_empty(const Function& func, BlockId block) {
    const BlockData& data = func.block(block);
    return data.first.is_valid() && data.first == data.last;
}

void replace_terminator_with_jump(Function& func, BlockId block, BlockCallId call) {
    InstId term = terminator_of(func, block);
    SrcLoc loc = func.inst(term).loc;
    func.remove_inst(term);
    InstId jump = func.make_inst(Opcode::Jump, TypeId{}, {}, call.index, loc);
    func.append_inst(block, jump);
}

bool spans_equal(std::span<const ValueId> a, std::span<const ValueId> b) {
    if (a.size() != b.size()) {
        return false;
    }
    for (size_t i = 0; i < a.size(); ++i) {
        if (a[i] != b[i]) {
            return false;
        }
    }
    return true;
}

bool fold_branch(Function& func, BlockId block) {
    InstId term = terminator_of(func, block);
    const InstData& data = func.inst(term);
    if (data.op != Opcode::BrIf) {
        return false;
    }
    BlockCallId then_call{aux_low(data.aux)};
    BlockCallId else_call{aux_high(data.aux)};
    ValueId cond = func.operands(term)[0];
    const ValueData& cond_value = func.value(cond);
    if (cond_value.kind == ValueKind::ConstInt) {
        replace_terminator_with_jump(func, block,
                                     cond_value.payload != 0 ? then_call : else_call);
        return true;
    }
    if (func.block_call(then_call).target == func.block_call(else_call).target &&
        spans_equal(func.block_call_args(then_call),
                    func.block_call_args(else_call))) {
        replace_terminator_with_jump(func, block, then_call);
        return true;
    }
    return false;
}

bool fold_forwarding_block(Function& func, const CfgFacts& facts, BlockId block) {
    if (block == func.entry_block() || facts.protected_blocks.contains(block.index)) {
        return false;
    }
    if (!block_is_empty(func, block)) {
        return false;
    }
    InstId term = terminator_of(func, block);
    const InstData& data = func.inst(term);
    if (data.op != Opcode::Jump) {
        return false;
    }
    BlockCallId onward{aux_low(data.aux)};
    BlockId target = func.block_call(onward).target;
    if (target == block) {
        return false;
    }
    auto found = facts.preds.find(block.index);
    if (found == facts.preds.end() || found->second.empty()) {
        return false;
    }

    std::vector<ValueId> params(func.block_params(block).begin(),
                                func.block_params(block).end());
    std::vector<ValueId> onward_args(func.block_call_args(onward).begin(),
                                     func.block_call_args(onward).end());

    for (ValueId param : params) {
        uint32_t uses_in_onward = 0;
        for (ValueId arg : onward_args) {
            if (arg == param) {
                ++uses_in_onward;
            }
        }
        if (func.count_uses(param) != uses_in_onward) {
            return false;
        }
    }
    bool needs_translation = !params.empty();
    bool changed = false;
    for (const PredEdge& edge : found->second) {

        if (edge.terminator == Opcode::Switch &&
            (needs_translation || !onward_args.empty())) {
            continue;
        }
        std::span<const ValueId> incoming = func.block_call_args(edge.call);
        std::vector<ValueId> translated(onward_args.begin(), onward_args.end());
        if (needs_translation) {
            for (ValueId& arg : translated) {
                const ValueData& value = func.value(arg);
                if (value.kind == ValueKind::BlockParam &&
                    BlockId{static_cast<uint32_t>(value.payload)} == block) {
                    arg = incoming[value.payload2];
                }
            }
        }
        func.set_block_call_target(edge.call, target);
        func.set_block_call_args(edge.call, translated);
        changed = true;
    }
    return changed;
}

bool merge_into_predecessor(Function& func, const CfgFacts& facts, BlockId block) {
    if (block == func.entry_block() || facts.protected_blocks.contains(block.index)) {
        return false;
    }
    auto found = facts.preds.find(block.index);
    if (found == facts.preds.end() || found->second.size() != 1) {
        return false;
    }
    const PredEdge& edge = found->second[0];
    if (edge.terminator != Opcode::Jump || edge.from == block) {
        return false;
    }

    std::vector<ValueId> params(func.block_params(block).begin(),
                                func.block_params(block).end());
    std::vector<ValueId> args(func.block_call_args(edge.call).begin(),
                              func.block_call_args(edge.call).end());
    for (size_t i = 0; i < params.size(); ++i) {
        func.replace_all_uses(params[i], args[i]);
    }

    InstId pred_term = terminator_of(func, edge.from);
    func.remove_inst(pred_term);
    InstId next = func.block(block).first;
    while (next.is_valid()) {
        InstId moved = next;
        next = func.inst(moved).next;
        func.remove_inst(moved);
        func.append_inst(edge.from, moved);
    }
    func.remove_block(block);
    return true;
}

bool remove_unreachable_blocks(Function& func, const CfgFacts& facts) {
    std::unordered_set<uint32_t> reachable;
    std::vector<BlockId> worklist{func.entry_block()};
    for (uint32_t index : facts.protected_blocks) {
        worklist.push_back(BlockId{index});
    }
    std::vector<BlockCallId> succs;
    while (!worklist.empty()) {
        BlockId block = worklist.back();
        worklist.pop_back();
        if (!reachable.insert(block.index).second) {
            continue;
        }
        InstId term = terminator_of(func, block);
        if (!term.is_valid()) {
            continue;
        }
        func.successors(term, succs);
        for (BlockCallId call : succs) {
            worklist.push_back(func.block_call(call).target);
        }
    }

    bool changed = false;
    BlockId block = func.first_block();
    while (block.is_valid()) {
        BlockId next = func.block(block).next;
        if (!reachable.contains(block.index)) {
            func.remove_block(block);
            changed = true;
        }
        block = next;
    }
    return changed;
}

} // namespace

bool run_simplify_cfg(Function& func, Module& mod) {
    (void)mod;
    bool changed = false;
    bool round_changed = true;
    while (round_changed) {
        round_changed = false;
        CfgFacts facts = collect_cfg_facts(func);

        for (BlockId b = func.first_block(); b.is_valid(); b = func.block(b).next) {
            if (fold_branch(func, b)) {
                round_changed = true;
            }
        }
        if (round_changed) {
            changed = true;
            continue;
        }

        for (BlockId b = func.first_block(); b.is_valid(); b = func.block(b).next) {
            if (fold_forwarding_block(func, facts, b)) {
                round_changed = true;
                break;
            }
        }
        if (round_changed) {
            changed = true;
            continue;
        }

        for (BlockId b = func.first_block(); b.is_valid(); b = func.block(b).next) {
            if (merge_into_predecessor(func, facts, b)) {
                round_changed = true;
                break;
            }
        }
        if (round_changed) {
            changed = true;
            continue;
        }

        if (remove_unreachable_blocks(func, facts)) {
            changed = true;
            round_changed = true;
        }
    }
    return changed;
}

namespace {

struct SlotFacts {
    InstId alloc;
    ValueId pointer;
    TypeId type;
    bool promotable = true;
    std::vector<InstId> loads;
    std::vector<InstId> stores;
};

struct BlockAccess {
    std::vector<std::pair<InstId, ValueId>> loads;
    ValueId local_out;
};

class SlotPromoter {
public:
    SlotPromoter(Function& func, const SlotFacts& slot,
                 const CfgFacts& facts)
        : func_(func), slot_(slot), facts_(facts) {}

    void run() {
        collect_block_accesses();
        for (auto& [block_index, access] : accesses_) {
            for (auto& [load, local_value] : access.loads) {
                ValueId reaching = local_value.is_valid()
                    ? local_value
                    : value_in(BlockId{block_index});
                func_.replace_all_uses(func_.inst(load).result, reaching);
            }
        }
        for (InstId load : slot_.loads) {
            func_.remove_inst(load);
        }
        for (InstId store : slot_.stores) {
            func_.remove_inst(store);
        }
        func_.remove_inst(slot_.alloc);
        prune_trivial_params();
    }

private:
    void collect_block_accesses() {
        for (BlockId b = func_.first_block(); b.is_valid();
             b = func_.block(b).next) {
            ValueId running{};
            for (InstId i = func_.block(b).first; i.is_valid();
                 i = func_.inst(i).next) {
                const InstData& data = func_.inst(i);
                if (data.op == Opcode::Load &&
                    func_.operands(i)[0] == slot_.pointer) {
                    accesses_[b.index].loads.push_back({i, running});
                } else if (data.op == Opcode::Store &&
                           func_.operands(i)[1] == slot_.pointer) {
                    running = func_.operands(i)[0];
                    accesses_[b.index].local_out = running;
                }
            }
        }
    }

    ValueId value_in(BlockId block) {
        auto memo = in_.find(block.index);
        if (memo != in_.end()) {
            return memo->second;
        }
        if (block == func_.entry_block()) {
            ValueId undef = func_.undef(slot_.type);
            in_[block.index] = undef;
            return undef;
        }
        auto preds = facts_.preds.find(block.index);
        if (preds == facts_.preds.end() || preds->second.empty()) {
            ValueId undef = func_.undef(slot_.type);
            in_[block.index] = undef;
            return undef;
        }
        if (preds->second.size() == 1) {

            if (preds->second[0].from == block) {
                ValueId undef = func_.undef(slot_.type);
                in_[block.index] = undef;
                return undef;
            }
            ValueId value = value_out(preds->second[0].from);
            in_[block.index] = value;
            return value;
        }
        ValueId param = func_.append_block_param(block, slot_.type);
        in_[block.index] = param;
        inserted_params_.push_back({block, param});
        for (const PredEdge& edge : preds->second) {
            func_.append_block_call_arg(edge.call, value_out(edge.from));
        }
        return param;
    }

    ValueId value_out(BlockId block) {
        auto access = accesses_.find(block.index);
        if (access != accesses_.end() && access->second.local_out.is_valid()) {
            return access->second.local_out;
        }
        return value_in(block);
    }
    void prune_trivial_params() {
        bool changed = true;
        while (changed) {
            changed = false;
            for (auto& [block, param] : inserted_params_) {
                if (!param.is_valid()) {
                    continue;
                }
                auto preds = facts_.preds.find(block.index);
                assert(preds != facts_.preds.end());
                ValueId unique{};
                bool trivial = true;
                uint32_t index =
                    static_cast<uint32_t>(func_.value(param).payload2);
                for (const PredEdge& edge : preds->second) {
                    ValueId arg = func_.block_call_args(edge.call)[index];
                    if (arg == param) {
                        continue;
                    }
                    if (unique.is_valid() && arg != unique) {
                        trivial = false;
                        break;
                    }
                    unique = arg;
                }
                if (!trivial || !unique.is_valid()) {
                    continue;
                }
                func_.replace_all_uses(param, unique);
                for (const PredEdge& edge : preds->second) {
                    func_.remove_block_call_arg(edge.call, index);
                }
                func_.remove_block_param(block, index);
                param = ValueId{};
                changed = true;
            }
        }
    }

    Function& func_;
    const SlotFacts& slot_;
    const CfgFacts& facts_;
    std::unordered_map<uint32_t, BlockAccess> accesses_;
    std::unordered_map<uint32_t, ValueId> in_;
    std::vector<std::pair<BlockId, ValueId>> inserted_params_;
};

} // namespace

bool run_mem2reg(Function& func, Module& mod) {
    CfgFacts facts = collect_cfg_facts(func);

    if (facts.has_indirect_flow) {
        return false;
    }

    uint32_t ptr_bytes = static_cast<uint32_t>(mod.target().pointer_width / 8);

    std::vector<SlotFacts> slots;
    std::unordered_map<uint32_t, size_t> by_pointer;
    for (InstId i = func.block(func.entry_block()).first; i.is_valid();
         i = func.inst(i).next) {
        if (func.inst(i).op != Opcode::StackAlloc) {
            continue;
        }
        SlotFacts slot;
        slot.alloc = i;
        slot.pointer = func.inst(i).result;
        by_pointer[slot.pointer.index] = slots.size();
        slots.push_back(slot);
    }
    if (slots.empty()) {
        return false;
    }

    std::vector<BlockCallId> succs;
    for (BlockId b = func.first_block(); b.is_valid(); b = func.block(b).next) {
        for (InstId i = func.block(b).first; i.is_valid(); i = func.inst(i).next) {
            const InstData& data = func.inst(i);
            std::span<const ValueId> operands = func.operands(i);
            for (size_t index = 0; index < operands.size(); ++index) {
                auto found = by_pointer.find(operands[index].index);
                if (found == by_pointer.end()) {
                    continue;
                }
                SlotFacts& slot = slots[found->second];
                uint64_t slot_size = stack_alloc_size(func.inst(slot.alloc).aux);
                if (data.op == Opcode::Load && index == 0 &&
                    !(data.flags & INST_FLAG_VOLATILE)) {
                    TypeId type = data.type;
                    if (!mod.types().is_scalar(type) ||
                        mod.types().byte_size(type, ptr_bytes) != slot_size ||
                        (slot.type.is_valid() && slot.type != type)) {
                        slot.promotable = false;
                        continue;
                    }
                    slot.type = type;
                    slot.loads.push_back(i);
                } else if (data.op == Opcode::Store && index == 1 &&
                           !(data.flags & INST_FLAG_VOLATILE)) {
                    TypeId type = func.value_type(operands[0]);
                    if (!mod.types().is_scalar(type) ||
                        mod.types().byte_size(type, ptr_bytes) != slot_size ||
                        (slot.type.is_valid() && slot.type != type)) {
                        slot.promotable = false;
                        continue;
                    }
                    slot.type = type;
                    slot.stores.push_back(i);
                } else {
                    slot.promotable = false;
                }
            }
            func.successors(i, succs);
            for (BlockCallId call : succs) {
                for (ValueId arg : func.block_call_args(call)) {
                    auto found = by_pointer.find(arg.index);
                    if (found != by_pointer.end()) {
                        slots[found->second].promotable = false;
                    }
                }
            }
        }
    }

    bool changed = false;
    for (SlotFacts& slot : slots) {
        if (!slot.promotable || !slot.type.is_valid()) {
            continue;
        }

        SlotPromoter(func, slot, facts).run();
        changed = true;
    }
    return changed;
}

namespace {

struct ConstInt {
    uint64_t bits;
    uint16_t width;
};

uint64_t width_mask(uint16_t width) {
    return width >= 64 ? ~0ull : ((1ull << width) - 1);
}

int64_t sign_extend(uint64_t bits, uint16_t width) {
    if (width >= 64) {
        return static_cast<int64_t>(bits);
    }
    uint64_t sign = 1ull << (width - 1);
    return static_cast<int64_t>((bits ^ sign) - sign);
}

std::optional<ConstInt> const_int_of(const Function& func, const Module& mod,
                                     ValueId value) {
    const ValueData& data = func.value(value);
    if (data.kind != ValueKind::ConstInt || !mod.types().is_int(data.type)) {
        return std::nullopt;
    }
    uint16_t width = mod.types().int_width(data.type);
    if (width > 64) {
        return std::nullopt;
    }
    return ConstInt{data.payload & width_mask(width), width};
}

bool is_bool_valued(const Function& func, ValueId value, int depth = 0) {
    if (depth > 3) {
        return false;
    }
    const ValueData& data = func.value(value);
    if (data.kind == ValueKind::ConstInt) {
        return data.type == types::I8 && (data.payload == 0 || data.payload == 1);
    }
    if (data.kind != ValueKind::InstResult) {
        return false;
    }
    const InstData& inst = func.inst(func.def_inst(value));
    if (inst.op == Opcode::Icmp || inst.op == Opcode::Fcmp) {
        return true;
    }
    if (inst.op == Opcode::Select) {
        std::span<const ValueId> operands =
            func.operands(func.def_inst(value));
        return is_bool_valued(func, operands[1], depth + 1) &&
               is_bool_valued(func, operands[2], depth + 1);
    }
    return false;
}

std::optional<uint64_t> fold_int_binop(Opcode op, ConstInt lhs, ConstInt rhs) {
    uint16_t width = lhs.width;
    uint64_t mask = width_mask(width);
    int64_t slhs = sign_extend(lhs.bits, width);
    int64_t srhs = sign_extend(rhs.bits, width);
    switch (op) {
        case Opcode::Iadd: return (lhs.bits + rhs.bits) & mask;
        case Opcode::Isub: return (lhs.bits - rhs.bits) & mask;
        case Opcode::Imul: return (lhs.bits * rhs.bits) & mask;
        case Opcode::Iand: return lhs.bits & rhs.bits;
        case Opcode::Ior:  return lhs.bits | rhs.bits;
        case Opcode::Ixor: return lhs.bits ^ rhs.bits;
        case Opcode::Shl:
            if (rhs.bits >= width) return std::nullopt;
            return (lhs.bits << rhs.bits) & mask;
        case Opcode::Lshr:
            if (rhs.bits >= width) return std::nullopt;
            return lhs.bits >> rhs.bits;
        case Opcode::Ashr:
            if (rhs.bits >= width) return std::nullopt;
            return static_cast<uint64_t>(slhs >> rhs.bits) & mask;
        case Opcode::Udiv:
            if (rhs.bits == 0) return std::nullopt;
            return lhs.bits / rhs.bits;
        case Opcode::Urem:
            if (rhs.bits == 0) return std::nullopt;
            return lhs.bits % rhs.bits;
        case Opcode::Sdiv:
            if (srhs == 0 || (slhs == sign_extend(1ull << (width - 1), width) &&
                              srhs == -1)) {
                return std::nullopt;
            }
            return static_cast<uint64_t>(slhs / srhs) & mask;
        case Opcode::Srem:
            if (srhs == 0 || (slhs == sign_extend(1ull << (width - 1), width) &&
                              srhs == -1)) {
                return std::nullopt;
            }
            return static_cast<uint64_t>(slhs % srhs) & mask;
        default:
            return std::nullopt;
    }
}

bool fold_icmp(IntCond cond, ConstInt lhs, ConstInt rhs) {
    int64_t slhs = sign_extend(lhs.bits, lhs.width);
    int64_t srhs = sign_extend(rhs.bits, rhs.width);
    switch (cond) {
        case IntCond::Eq:  return lhs.bits == rhs.bits;
        case IntCond::Ne:  return lhs.bits != rhs.bits;
        case IntCond::Slt: return slhs < srhs;
        case IntCond::Sle: return slhs <= srhs;
        case IntCond::Sgt: return slhs > srhs;
        case IntCond::Sge: return slhs >= srhs;
        case IntCond::Ult: return lhs.bits < rhs.bits;
        case IntCond::Ule: return lhs.bits <= rhs.bits;
        case IntCond::Ugt: return lhs.bits > rhs.bits;
        case IntCond::Uge: return lhs.bits >= rhs.bits;
    }
    return false;
}

ValueId simplify_inst(Function& func, Module& mod, InstId inst_id) {
    const InstData& data = func.inst(inst_id);
    std::span<const ValueId> operands = func.operands(inst_id);
    const TypeTable& types = mod.types();

    switch (data.op) {
        case Opcode::Iadd: case Opcode::Isub: case Opcode::Imul:
        case Opcode::Iand: case Opcode::Ior:  case Opcode::Ixor:
        case Opcode::Shl:  case Opcode::Sdiv: case Opcode::Udiv:
        case Opcode::Srem: case Opcode::Urem: case Opcode::Ashr:
        case Opcode::Lshr: {
            auto lhs = const_int_of(func, mod, operands[0]);
            auto rhs = const_int_of(func, mod, operands[1]);
            if (lhs && rhs) {
                if (auto folded = fold_int_binop(data.op, *lhs, *rhs)) {
                    return func.const_int(data.type, *folded);
                }
            }

            bool commutative = data.op == Opcode::Iadd || data.op == Opcode::Imul ||
                               data.op == Opcode::Iand || data.op == Opcode::Ior ||
                               data.op == Opcode::Ixor;
            ValueId value = operands[0];
            std::optional<ConstInt> konst = rhs;
            bool konst_is_rhs = true;
            if (!konst && commutative && lhs) {
                konst = lhs;
                konst_is_rhs = false;
                value = operands[1];
            }
            if (konst) {
                uint64_t all = width_mask(konst->width);
                switch (data.op) {
                    case Opcode::Iadd: case Opcode::Ixor:
                    case Opcode::Ior:
                        if (konst->bits == 0) return value;
                        break;
                    case Opcode::Isub: case Opcode::Shl:
                    case Opcode::Lshr: case Opcode::Ashr:
                        if (konst->bits == 0 && konst_is_rhs) return value;
                        break;
                    case Opcode::Imul:
                        if (konst->bits == 1) return value;
                        if (konst->bits == 0) return func.const_int(data.type, 0);
                        break;
                    case Opcode::Iand:
                        if (konst->bits == all) return value;
                        if (konst->bits == 0) return func.const_int(data.type, 0);
                        break;
                    case Opcode::Udiv: case Opcode::Sdiv:
                        if (konst->bits == 1 && konst_is_rhs) return value;
                        break;
                    default:
                        break;
                }
            }
            if ((data.op == Opcode::Iand || data.op == Opcode::Ior) &&
                operands[0] == operands[1]) {
                return operands[0];
            }
            return ValueId{};
        }
        case Opcode::Icmp: {
            IntCond cond = static_cast<IntCond>(data.aux);
            auto lhs = const_int_of(func, mod, operands[0]);
            auto rhs = const_int_of(func, mod, operands[1]);
            if (lhs && rhs) {
                return func.const_int(types::I8, fold_icmp(cond, *lhs, *rhs) ? 1 : 0);
            }
            if (operands[0] == operands[1] && !types.is_float(func.value_type(operands[0]))) {
                bool result = cond == IntCond::Eq || cond == IntCond::Sle ||
                              cond == IntCond::Sge || cond == IntCond::Ule ||
                              cond == IntCond::Uge;
                bool decidable = result || cond == IntCond::Ne ||
                                 cond == IntCond::Slt || cond == IntCond::Sgt ||
                                 cond == IntCond::Ult || cond == IntCond::Ugt;
                if (decidable) {
                    return func.const_int(types::I8, result ? 1 : 0);
                }
            }

            if (cond == IntCond::Ne && rhs && rhs->bits == 0) {
                if (is_bool_valued(func, operands[0])) {
                    return operands[0];
                }
                const ValueData& lhs_value = func.value(operands[0]);
                if (lhs_value.kind == ValueKind::InstResult) {
                    InstId def = func.def_inst(operands[0]);
                    if (func.inst(def).op == Opcode::Zext &&
                        is_bool_valued(func, func.operands(def)[0])) {
                        return func.operands(def)[0];
                    }
                }
            }
            return ValueId{};
        }
        case Opcode::Trunc: case Opcode::Zext: case Opcode::Sext: {
            if (auto value = const_int_of(func, mod, operands[0])) {
                uint16_t to_width = types.int_width(data.type);
                if (to_width <= 64) {
                    uint64_t bits = value->bits;
                    if (data.op == Opcode::Sext) {
                        bits = static_cast<uint64_t>(sign_extend(bits, value->width));
                    }
                    return func.const_int(data.type, bits & width_mask(to_width));
                }
            }

            if (data.op == Opcode::Trunc) {
                const ValueData& source = func.value(operands[0]);
                if (source.kind == ValueKind::InstResult) {
                    InstId def = func.def_inst(operands[0]);
                    Opcode def_op = func.inst(def).op;
                    if ((def_op == Opcode::Zext || def_op == Opcode::Sext) &&
                        func.value_type(func.operands(def)[0]) == data.type) {
                        return func.operands(def)[0];
                    }
                }
            }
            return ValueId{};
        }
        case Opcode::Fpext: case Opcode::Fptrunc: {
            const ValueData& source = func.value(operands[0]);
            numeric::FloatFormat destination = numeric_float_format(data.type);
            if (source.kind == ValueKind::ConstFloat &&
                destination != numeric::FloatFormat::Invalid) {
                return intern_float_result(
                    func, data.type,
                    numeric::convert(numeric_float_value(source), destination));
            }
            return ValueId{};
        }
        case Opcode::Sitofp: case Opcode::Uitofp: {
            numeric::FloatFormat destination = numeric_float_format(data.type);
            if (destination != numeric::FloatFormat::Invalid) {
                auto value = const_int_of(func, mod, operands[0]);
                if (!value) {
                    return ValueId{};
                }
                return intern_float_result(
                    func, data.type,
                    numeric::from_integer(value->bits,
                                          value->width,
                                          data.op == Opcode::Sitofp,
                                          destination));
            }
            return ValueId{};
        }
        case Opcode::Bitcast:
            if (func.value_type(operands[0]) == data.type) {
                return operands[0];
            }
            return ValueId{};
        case Opcode::PtrAdd: {
            if (auto offset = const_int_of(func, mod, operands[1])) {
                if (offset->bits == 0) {
                    return operands[0];
                }
            }
            return ValueId{};
        }
        case Opcode::Select: {
            const ValueData& cond = func.value(operands[0]);
            if (cond.kind == ValueKind::ConstInt) {
                return cond.payload != 0 ? operands[1] : operands[2];
            }
            if (operands[1] == operands[2]) {
                return operands[1];
            }

            auto then_value = const_int_of(func, mod, operands[1]);
            auto else_value = const_int_of(func, mod, operands[2]);
            if (then_value && else_value && data.type == types::I8 &&
                then_value->bits == 1 && else_value->bits == 0 &&
                is_bool_valued(func, operands[0])) {
                return operands[0];
            }
            return ValueId{};
        }
        default:
            return ValueId{};
    }
}

} // namespace

bool run_instsimplify(Function& func, Module& mod) {
    bool changed = false;
    bool round_changed = true;
    while (round_changed) {
        round_changed = false;
        for (BlockId b = func.first_block(); b.is_valid(); b = func.block(b).next) {
            InstId i = func.block(b).first;
            while (i.is_valid()) {
                InstId next = func.inst(i).next;
                const InstData& data = func.inst(i);
                if (opcode_result_kind(data.op) == ResultKind::Value &&
                    !(data.flags & INST_FLAG_VOLATILE)) {
                    ValueId simplified = simplify_inst(func, mod, i);
                    if (simplified.is_valid() && simplified != data.result) {
                        func.replace_all_uses(data.result, simplified);
                        func.remove_inst(i);
                        changed = true;
                        round_changed = true;
                    }
                }
                i = next;
            }
        }
    }
    return changed;
}

PipelineResult run_o1_pipeline(Module& mod, PipelineOptions options) {
    static const FunctionPass kPasses[] = {
        {"simplify_cfg", run_simplify_cfg},
        {"mem2reg", run_mem2reg},
        {"instsimplify", run_instsimplify},
        {"dce", run_dce},
    };
    PipelineResult total;
    for (int round = 0; round < 3; ++round) {
        PipelineResult result = run_pipeline(mod, kPasses, options);
        total.changed |= result.changed;
        if (!result.verified) {
            total.verified = false;
            total.verify_error = std::move(result.verify_error);
            return total;
        }
        if (!result.changed) {
            break;
        }
    }
    return total;
}

} // namespace aburi::air
