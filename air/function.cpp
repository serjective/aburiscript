#include "function.h"

#include <cassert>

namespace aburi::air {

namespace {

uint64_t hash_combine(uint64_t seed, uint64_t value) {
    return seed ^ (value + UINT64_C(0x9e3779b97f4a7c15) + (seed << 12) + (seed >> 4));
}

uint64_t hash_constant(ValueKind kind, TypeId type, uint64_t payload, uint64_t payload2) {
    uint64_t h = hash_combine(0xC0u, static_cast<uint64_t>(kind));
    h = hash_combine(h, type.index);
    h = hash_combine(h, payload);
    h = hash_combine(h, payload2);
    return h;
}

} // namespace

Function::Function(std::string name, SigId sig, Linkage linkage)
    : name_(std::move(name)), sig_(sig), linkage_(linkage) {
    insts_.emplace_back();
    blocks_.emplace_back();
    values_.emplace_back();
    block_calls_.emplace_back();
}

BlockId Function::create_block(std::span<const TypeId> param_types) {
    BlockId id{static_cast<uint32_t>(blocks_.size())};
    BlockData data;
    data.param_begin = static_cast<uint32_t>(block_param_pool_.size());
    data.param_count = static_cast<uint32_t>(param_types.size());
    for (uint32_t i = 0; i < param_types.size(); ++i) {
        ValueId param = new_value(ValueKind::BlockParam, param_types[i], id.index, i);
        block_param_pool_.push_back(param);
    }
    if (last_block_.is_valid()) {
        data.prev = last_block_;
        blocks_[last_block_.index].next = id;
    } else {
        entry_block_ = id;
    }
    last_block_ = id;
    blocks_.push_back(data);
    return id;
}

const BlockData& Function::block(BlockId id) const {
    assert(is_valid(id));
    return blocks_[id.index];
}

std::span<const ValueId> Function::block_params(BlockId id) const {
    const BlockData& data = block(id);
    return {block_param_pool_.data() + data.param_begin, data.param_count};
}

ValueId Function::append_block_param(BlockId id, TypeId type) {
    assert(is_valid(id));
    BlockData& data = blocks_[id.index];
    ValueId param = new_value(ValueKind::BlockParam, type, id.index, data.param_count);
    if (data.param_begin + data.param_count == block_param_pool_.size()) {
        block_param_pool_.push_back(param);
    } else {

        uint32_t new_begin = static_cast<uint32_t>(block_param_pool_.size());
        for (uint32_t i = 0; i < data.param_count; ++i) {
            block_param_pool_.push_back(block_param_pool_[data.param_begin + i]);
        }
        block_param_pool_.push_back(param);
        data.param_begin = new_begin;
    }
    ++data.param_count;
    return param;
}

void Function::remove_block_param(BlockId id, uint32_t index) {
    assert(is_valid(id));
    BlockData& data = blocks_[id.index];
    assert(index < data.param_count);

    for (uint32_t i = index + 1; i < data.param_count; ++i) {
        ValueId moved = block_param_pool_[data.param_begin + i];
        block_param_pool_[data.param_begin + i - 1] = moved;
        values_[moved.index].payload2 = i - 1;
    }
    --data.param_count;
}

void Function::set_block_params(BlockId id, std::span<const TypeId> types) {
    assert(is_valid(id));
    BlockData& data = blocks_[id.index];

    uint32_t new_begin = static_cast<uint32_t>(block_param_pool_.size());
    for (uint32_t i = 0; i < types.size(); ++i) {
        block_param_pool_.push_back(
            new_value(ValueKind::BlockParam, types[i], id.index, i));
    }
    data.param_begin = new_begin;
    data.param_count = static_cast<uint32_t>(types.size());
}

void Function::retype_value(ValueId id, TypeId type) {
    assert(is_valid(id));
    ValueData& data = values_[id.index];
    assert((data.kind == ValueKind::BlockParam ||
            data.kind == ValueKind::InstResult) &&
           "constants are interned by type; replace them instead");
    data.type = type;
    if (data.kind == ValueKind::InstResult) {
        insts_[static_cast<uint32_t>(data.payload)].type = type;
    }
}

void Function::remove_block(BlockId id) {
    assert(is_valid(id));
    assert(id != entry_block_ && "the entry block cannot be removed");
    BlockData& data = blocks_[id.index];
    if (data.prev.is_valid()) {
        blocks_[data.prev.index].next = data.next;
    }
    if (data.next.is_valid()) {
        blocks_[data.next.index].prev = data.prev;
    } else {
        last_block_ = data.prev;
    }
    data.prev = BlockId{};
    data.next = BlockId{};
}

const ValueData& Function::value(ValueId id) const {
    assert(is_valid(id));
    return values_[id.index];
}

ValueId Function::const_int(TypeId type, uint64_t bits, uint64_t high_bits) {
    return intern_constant(ValueKind::ConstInt, type, bits, high_bits);
}

ValueId Function::const_float_bits(TypeId type, uint64_t bits, uint64_t high_bits) {
    return intern_constant(ValueKind::ConstFloat, type, bits, high_bits);
}

ValueId Function::const_null(TypeId ptr_type) {
    return intern_constant(ValueKind::ConstNull, ptr_type, 0, 0);
}

ValueId Function::undef(TypeId type) {
    return intern_constant(ValueKind::Undef, type, 0, 0);
}

ValueId Function::global_addr(GlobalId global, TypeId ptr_type) {
    return intern_constant(ValueKind::GlobalAddr, ptr_type, global.index, 0);
}

ValueId Function::func_addr(FuncId func, TypeId ptr_type) {
    return intern_constant(ValueKind::FuncAddr, ptr_type, func.index, 0);
}

ValueId Function::label_addr(BlockId block, TypeId ptr_type) {
    assert(is_valid(block));
    return intern_constant(ValueKind::LabelAddr, ptr_type, block.index, 0);
}

bool Function::is_constant(ValueId id) const {
    switch (value(id).kind) {
        case ValueKind::ConstInt:
        case ValueKind::ConstFloat:
        case ValueKind::ConstNull:
        case ValueKind::Undef:
        case ValueKind::GlobalAddr:
        case ValueKind::FuncAddr:
        case ValueKind::LabelAddr:
            return true;
        case ValueKind::InstResult:
        case ValueKind::BlockParam:
            return false;
    }
    return false;
}

InstId Function::def_inst(ValueId id) const {
    const ValueData& data = value(id);
    if (data.kind != ValueKind::InstResult) {
        return InstId{};
    }
    return InstId{static_cast<uint32_t>(data.payload)};
}

void Function::set_value_name(ValueId id, std::string_view name) {
    assert(is_valid(id));
    if (name.empty()) {
        value_names_.erase(id.index);
    } else {
        value_names_[id.index] = std::string(name);
    }
}

std::string_view Function::value_name(ValueId id) const {
    auto it = value_names_.find(id.index);
    if (it == value_names_.end()) {
        return {};
    }
    return it->second;
}

InstId Function::make_inst(Opcode op, TypeId result_type,
                           std::span<const ValueId> operands, uint64_t aux,
                           SrcLoc loc, uint16_t flags, uint64_t aux2) {
    int expected = opcode_operand_count(op);
    assert(expected < 0 || static_cast<uint32_t>(expected) == operands.size());
    (void)expected;

    InstId id{static_cast<uint32_t>(insts_.size())};
    InstData data;
    data.op = op;
    data.flags = flags;
    data.aux = aux;
    data.aux2 = aux2;
    data.loc = loc;
    data.op_begin = append_operands(operands);
    data.op_count = static_cast<uint32_t>(operands.size());

    ResultKind result_kind = opcode_result_kind(op);
    bool has_result = result_kind == ResultKind::Value ||
                      (result_kind == ResultKind::SigDependent && result_type.is_valid());
    if (has_result) {
        assert(result_type.is_valid());
        data.type = result_type;
        data.result = new_value(ValueKind::InstResult, result_type, id.index, 0);
    }
    insts_.push_back(data);
    return id;
}

void Function::append_inst(BlockId block_id, InstId inst_id) {
    assert(is_valid(block_id) && is_valid(inst_id));
    InstData& data = insts_[inst_id.index];
    assert(!data.block.is_valid() && "instruction already attached");
    BlockData& block_data = blocks_[block_id.index];
    data.block = block_id;
    data.prev = block_data.last;
    data.next = InstId{};
    if (block_data.last.is_valid()) {
        insts_[block_data.last.index].next = inst_id;
    } else {
        block_data.first = inst_id;
    }
    block_data.last = inst_id;
}

void Function::insert_before(InstId pos, InstId inst_id) {
    assert(is_valid(pos) && is_valid(inst_id));
    InstData& pos_data = insts_[pos.index];
    assert(pos_data.block.is_valid() && "insertion point not attached");
    InstData& data = insts_[inst_id.index];
    assert(!data.block.is_valid() && "instruction already attached");
    data.block = pos_data.block;
    data.prev = pos_data.prev;
    data.next = pos;
    if (pos_data.prev.is_valid()) {
        insts_[pos_data.prev.index].next = inst_id;
    } else {
        blocks_[pos_data.block.index].first = inst_id;
    }
    pos_data.prev = inst_id;
}

void Function::remove_inst(InstId inst_id) {
    assert(is_valid(inst_id));
    InstData& data = insts_[inst_id.index];
    assert(data.block.is_valid() && "instruction not attached");
    BlockData& block_data = blocks_[data.block.index];
    if (data.prev.is_valid()) {
        insts_[data.prev.index].next = data.next;
    } else {
        block_data.first = data.next;
    }
    if (data.next.is_valid()) {
        insts_[data.next.index].prev = data.prev;
    } else {
        block_data.last = data.prev;
    }
    data.block = BlockId{};
    data.prev = InstId{};
    data.next = InstId{};
}

const InstData& Function::inst(InstId id) const {
    assert(is_valid(id));
    return insts_[id.index];
}

InstData& Function::inst_mut(InstId id) {
    assert(is_valid(id));
    return insts_[id.index];
}

std::span<const ValueId> Function::operands(InstId id) const {
    const InstData& data = inst(id);
    return {operand_pool_.data() + data.op_begin, data.op_count};
}

void Function::set_operand(InstId id, uint32_t index, ValueId v) {
    const InstData& data = inst(id);
    assert(index < data.op_count);
    operand_pool_[data.op_begin + index] = v;
}

BlockCallId Function::make_block_call(BlockId target, std::span<const ValueId> args) {
    assert(is_valid(target));
    BlockCallId id{static_cast<uint32_t>(block_calls_.size())};
    BlockCall call;
    call.target = target;
    call.arg_begin = append_operands(args);
    call.arg_count = static_cast<uint32_t>(args.size());
    block_calls_.push_back(call);
    return id;
}

const BlockCall& Function::block_call(BlockCallId id) const {
    assert(is_valid(id));
    return block_calls_[id.index];
}

std::span<const ValueId> Function::block_call_args(BlockCallId id) const {
    const BlockCall& call = block_call(id);
    return {operand_pool_.data() + call.arg_begin, call.arg_count};
}

void Function::set_block_call_arg(BlockCallId id, uint32_t index, ValueId v) {
    const BlockCall& call = block_call(id);
    assert(index < call.arg_count);
    operand_pool_[call.arg_begin + index] = v;
}

void Function::append_block_call_arg(BlockCallId id, ValueId v) {
    assert(is_valid(id));
    BlockCall& call = block_calls_[id.index];
    if (call.arg_begin + call.arg_count == operand_pool_.size()) {
        operand_pool_.push_back(v);
    } else {

        uint32_t new_begin = static_cast<uint32_t>(operand_pool_.size());
        for (uint32_t i = 0; i < call.arg_count; ++i) {
            operand_pool_.push_back(operand_pool_[call.arg_begin + i]);
        }
        operand_pool_.push_back(v);
        call.arg_begin = new_begin;
    }
    ++call.arg_count;
}

void Function::remove_block_call_arg(BlockCallId id, uint32_t index) {
    assert(is_valid(id));
    BlockCall& call = block_calls_[id.index];
    assert(index < call.arg_count);
    for (uint32_t i = index + 1; i < call.arg_count; ++i) {
        operand_pool_[call.arg_begin + i - 1] = operand_pool_[call.arg_begin + i];
    }
    --call.arg_count;
}

void Function::set_block_call_args(BlockCallId id, std::span<const ValueId> args) {
    assert(is_valid(id));
    BlockCall& call = block_calls_[id.index];
    if (args.size() == call.arg_count) {
        for (uint32_t i = 0; i < call.arg_count; ++i) {
            operand_pool_[call.arg_begin + i] = args[i];
        }
        return;
    }
    call.arg_begin = append_operands(args);
    call.arg_count = static_cast<uint32_t>(args.size());
}

void Function::set_block_call_target(BlockCallId id, BlockId target) {
    assert(is_valid(id));
    assert(is_valid(target));
    block_calls_[id.index].target = target;
}

uint32_t Function::make_jump_table(std::span<const SwitchCase> cases) {
    uint32_t index = static_cast<uint32_t>(jump_tables_.size());
    jump_tables_.emplace_back(cases.begin(), cases.end());
    return index;
}

std::span<const SwitchCase> Function::jump_table(uint32_t index) const {
    assert(index < jump_tables_.size());
    return jump_tables_[index];
}

uint32_t Function::make_block_call_list(std::span<const BlockCallId> calls) {
    uint32_t index = static_cast<uint32_t>(block_call_lists_.size());
    block_call_lists_.emplace_back(calls.begin(), calls.end());
    return index;
}

std::span<const BlockCallId> Function::block_call_list(uint32_t index) const {
    assert(index < block_call_lists_.size());
    return block_call_lists_[index];
}

void Function::successors(InstId id, std::vector<BlockCallId>& out) const {
    out.clear();
    const InstData& data = inst(id);
    switch (data.op) {
        case Opcode::Jump:
            out.push_back(BlockCallId{aux_low(data.aux)});
            break;
        case Opcode::BrIf:
            out.push_back(BlockCallId{aux_low(data.aux)});
            out.push_back(BlockCallId{aux_high(data.aux)});
            break;
        case Opcode::Switch: {
            out.push_back(BlockCallId{aux_low(data.aux)});
            for (const SwitchCase& c : jump_table(aux_high(data.aux))) {
                out.push_back(c.target);
            }
            break;
        }
        case Opcode::BrIndirect: {
            for (BlockCallId call : block_call_list(aux_low(data.aux))) {
                out.push_back(call);
            }
            break;
        }
        case Opcode::AsmGoto: {

            for (BlockCallId call :
                 block_call_list(static_cast<uint32_t>(data.aux2))) {
                out.push_back(call);
            }
            break;
        }
        case Opcode::Invoke:
        case Opcode::InvokeIndirect:
            out.push_back(BlockCallId{aux_low(data.aux2)});
            out.push_back(BlockCallId{aux_high(data.aux2)});
            break;
        default:
            break;
    }
}

void Function::replace_all_uses(ValueId old_value, ValueId new_value) {
    assert(is_valid(old_value) && is_valid(new_value));
    for (ValueId& slot : operand_pool_) {
        if (slot == old_value) {
            slot = new_value;
        }
    }
}

uint32_t Function::count_uses(ValueId id) const {

    uint32_t uses = 0;
    std::vector<BlockCallId> succs;
    for (BlockId b = entry_block_; b.is_valid(); b = blocks_[b.index].next) {
        for (InstId i = blocks_[b.index].first; i.is_valid(); i = insts_[i.index].next) {
            for (ValueId operand : operands(i)) {
                if (operand == id) {
                    ++uses;
                }
            }
            successors(i, succs);
            for (BlockCallId call : succs) {
                for (ValueId arg : block_call_args(call)) {
                    if (arg == id) {
                        ++uses;
                    }
                }
            }
        }
    }
    return uses;
}

ValueId Function::new_value(ValueKind kind, TypeId type, uint64_t payload,
                            uint64_t payload2) {
    ValueId id{static_cast<uint32_t>(values_.size())};
    ValueData data;
    data.kind = kind;
    data.type = type;
    data.payload = payload;
    data.payload2 = payload2;
    values_.push_back(data);
    return id;
}

ValueId Function::intern_constant(ValueKind kind, TypeId type, uint64_t payload,
                                  uint64_t payload2) {
    assert(type.is_valid());
    uint64_t h = hash_constant(kind, type, payload, payload2);
    auto range = constant_lookup_.equal_range(h);
    for (auto it = range.first; it != range.second; ++it) {
        const ValueData& cand = values_[it->second];
        if (cand.kind == kind && cand.type == type && cand.payload == payload &&
            cand.payload2 == payload2) {
            return ValueId{it->second};
        }
    }
    ValueId id = new_value(kind, type, payload, payload2);
    constant_lookup_.emplace(h, id.index);
    return id;
}

uint32_t Function::append_operands(std::span<const ValueId> operands) {
    uint32_t begin = static_cast<uint32_t>(operand_pool_.size());
    operand_pool_.insert(operand_pool_.end(), operands.begin(), operands.end());
    return begin;
}

} // namespace aburi::air
