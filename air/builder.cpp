#include "builder.h"

#include <cassert>
#include <vector>

namespace aburi::air {

namespace {

uint8_t align_log2_of(uint32_t align_bytes) {
    assert(align_bytes != 0 && (align_bytes & (align_bytes - 1)) == 0 &&
           "alignment must be a power of two");
    uint8_t log2 = 0;
    while ((1u << log2) < align_bytes) {
        ++log2;
    }
    return log2;
}

} // namespace

ValueId Builder::stack_alloc(uint64_t size_bytes, uint32_t align_bytes) {
    InstId inst = emit(Opcode::StackAlloc, types::PTR, {},
                       pack_stack_alloc_aux(size_bytes, align_log2_of(align_bytes)));
    return result_of(inst);
}

ValueId Builder::stack_alloc_dyn(ValueId size_bytes, uint32_t align_bytes) {
    ValueId ops[] = {size_bytes};
    InstId inst = emit(Opcode::StackAllocDyn, types::PTR, ops,
                       align_log2_of(align_bytes));
    return result_of(inst);
}

ValueId Builder::stack_save() {
    return result_of(emit(Opcode::StackSave, types::PTR, {}));
}

void Builder::stack_restore(ValueId saved) {
    ValueId ops[] = {saved};
    emit(Opcode::StackRestore, TypeId{}, ops);
}

ValueId Builder::load(TypeId type, ValueId ptr, uint32_t align_bytes,
                      bool is_volatile) {
    ValueId ops[] = {ptr};
    InstId inst = emit(Opcode::Load, type, ops, align_log2_of(align_bytes),
                       is_volatile ? INST_FLAG_VOLATILE : 0);
    return result_of(inst);
}

void Builder::store(ValueId value, ValueId ptr, uint32_t align_bytes,
                    bool is_volatile) {
    ValueId ops[] = {value, ptr};
    emit(Opcode::Store, TypeId{}, ops, align_log2_of(align_bytes),
         is_volatile ? INST_FLAG_VOLATILE : 0);
}

void Builder::memcpy_(ValueId dst, ValueId src, ValueId size_bytes) {
    ValueId ops[] = {dst, src, size_bytes};
    emit(Opcode::Memcpy, TypeId{}, ops);
}

void Builder::memmove_(ValueId dst, ValueId src, ValueId size_bytes) {
    ValueId ops[] = {dst, src, size_bytes};
    emit(Opcode::Memmove, TypeId{}, ops);
}

void Builder::memset_(ValueId dst, ValueId byte, ValueId size_bytes) {
    ValueId ops[] = {dst, byte, size_bytes};
    emit(Opcode::Memset, TypeId{}, ops);
}

ValueId Builder::atomic_load(TypeId type, ValueId ptr, uint32_t align_bytes,
                             MemOrder order) {
    ValueId ops[] = {ptr};
    InstId inst = emit(Opcode::AtomicLoad, type, ops,
                       pack_atomic_access_aux(order, align_log2_of(align_bytes)));
    return result_of(inst);
}

void Builder::atomic_store(ValueId value, ValueId ptr, uint32_t align_bytes,
                           MemOrder order) {
    ValueId ops[] = {value, ptr};
    emit(Opcode::AtomicStore, TypeId{}, ops,
         pack_atomic_access_aux(order, align_log2_of(align_bytes)));
}

ValueId Builder::atomic_rmw(RmwOp op, ValueId ptr, ValueId value, MemOrder order) {
    ValueId ops[] = {ptr, value};
    InstId inst = emit(Opcode::AtomicRmw, func_.value_type(value), ops,
                       pack_rmw_aux(op, order));
    return result_of(inst);
}

ValueId Builder::atomic_cas(ValueId ptr, ValueId expected, ValueId desired,
                            MemOrder success, MemOrder failure) {
    ValueId ops[] = {ptr, expected, desired};
    InstId inst = emit(Opcode::AtomicCas, func_.value_type(desired), ops,
                       pack_cas_aux(success, failure));
    return result_of(inst);
}

void Builder::fence(MemOrder order) {
    emit(Opcode::Fence, TypeId{}, {}, static_cast<uint64_t>(order));
}

ValueId Builder::fneg(ValueId a) {
    ValueId ops[] = {a};
    InstId inst = emit(Opcode::Fneg, func_.value_type(a), ops);
    return result_of(inst);
}

ValueId Builder::icmp(IntCond cond, ValueId a, ValueId b) {
    ValueId ops[] = {a, b};
    InstId inst = emit(Opcode::Icmp, types::I8, ops, static_cast<uint64_t>(cond));
    return result_of(inst);
}

ValueId Builder::fcmp(FloatCond cond, ValueId a, ValueId b) {
    ValueId ops[] = {a, b};
    InstId inst = emit(Opcode::Fcmp, types::I8, ops, static_cast<uint64_t>(cond));
    return result_of(inst);
}

ValueId Builder::cast(Opcode op, TypeId to, ValueId v) {
    assert(opcode_is_cast(op));
    ValueId ops[] = {v};
    return result_of(emit(op, to, ops));
}

ValueId Builder::ptr_add(ValueId ptr, ValueId byte_offset) {
    ValueId ops[] = {ptr, byte_offset};
    return result_of(emit(Opcode::PtrAdd, func_.value_type(ptr), ops));
}

ValueId Builder::select(ValueId cond, ValueId a, ValueId b) {
    ValueId ops[] = {cond, a, b};
    return result_of(emit(Opcode::Select, func_.value_type(a), ops));
}

void Builder::va_start_(ValueId va_list_ptr) {
    ValueId ops[] = {va_list_ptr};
    emit(Opcode::VaStart, TypeId{}, ops);
}

void Builder::inline_asm(uint32_t payload_index, std::span<const ValueId> inputs) {
    emit(Opcode::InlineAsm, TypeId{}, inputs, payload_index);
}

void Builder::trap() { emit(Opcode::Trap, TypeId{}, {}); }

ValueId Builder::frame_addr() {
    return result_of(emit(Opcode::FrameAddr, types::PTR, {}));
}

ValueId Builder::return_addr() {
    return result_of(emit(Opcode::ReturnAddr, types::PTR, {}));
}

ValueId Builder::call(FuncId callee, std::span<const ValueId> args) {
    const SigData& sig = module_.types().signature(module_.function(callee).sig());
    TypeId result_type =
        sig.ret_class == RetClass::Scalar ? sig.ret_type : TypeId{};
    InstId inst = emit(Opcode::Call, result_type, args, callee.index);
    return result_of(inst);
}

ValueId Builder::call_indirect(SigId sig_id, ValueId callee,
                               std::span<const ValueId> args) {
    const SigData& sig = module_.types().signature(sig_id);
    TypeId result_type =
        sig.ret_class == RetClass::Scalar ? sig.ret_type : TypeId{};
    std::vector<ValueId> ops;
    ops.reserve(args.size() + 1);
    ops.push_back(callee);
    ops.insert(ops.end(), args.begin(), args.end());
    InstId inst = emit(Opcode::CallIndirect, result_type, ops, sig_id.index);
    return result_of(inst);
}

void Builder::tail_call_indirect(SigId sig_id, ValueId callee,
                                 std::span<const ValueId> args) {
    std::vector<ValueId> ops;
    ops.reserve(args.size() + 1);
    ops.push_back(callee);
    ops.insert(ops.end(), args.begin(), args.end());
    emit(Opcode::TailCallIndirect, TypeId{}, ops, sig_id.index);
}

ValueId Builder::eh_alloc_exception(uint64_t size_bytes) {
    return result_of(emit(Opcode::EhAllocException, types::PTR, {}, size_bytes));
}

ValueId Builder::eh_landing_pad(uint32_t payload_index) {
    return result_of(emit(Opcode::EhLandingPad, types::PTR, {}, payload_index));
}

ValueId Builder::eh_selector(ValueId exception_ptr) {
    ValueId ops[] = {exception_ptr};
    return result_of(emit(Opcode::EhSelector, types::I32, ops));
}

ValueId Builder::eh_typeid_for(ValueId typeinfo) {
    ValueId ops[] = {typeinfo};
    return result_of(emit(Opcode::EhTypeId, types::I32, ops));
}

ValueId Builder::catch_begin(ValueId exception_ptr) {
    ValueId ops[] = {exception_ptr};
    return result_of(emit(Opcode::CatchBegin, types::PTR, ops));
}

void Builder::catch_end() {
    emit(Opcode::CatchEnd, TypeId{}, {});
}

void Builder::jump(BlockId target, std::span<const ValueId> args) {
    BlockCallId call = func_.make_block_call(target, args);
    emit(Opcode::Jump, TypeId{}, {}, pack_pair_aux(call.index, 0));
}

void Builder::br_if(ValueId cond, BlockId then_target,
                    std::span<const ValueId> then_args, BlockId else_target,
                    std::span<const ValueId> else_args) {
    BlockCallId then_call = func_.make_block_call(then_target, then_args);
    BlockCallId else_call = func_.make_block_call(else_target, else_args);
    ValueId ops[] = {cond};
    emit(Opcode::BrIf, TypeId{}, ops, pack_pair_aux(then_call.index, else_call.index));
}

void Builder::switch_(ValueId v, BlockId default_target,
                      std::span<const std::pair<uint64_t, BlockId>> cases) {
    BlockCallId default_call = func_.make_block_call(default_target, {});
    std::vector<SwitchCase> entries;
    entries.reserve(cases.size());
    for (const auto& [value, target] : cases) {
        entries.push_back({value, func_.make_block_call(target, {})});
    }
    switch_raw(v, default_call, entries);
}

void Builder::switch_raw(ValueId v, BlockCallId default_call,
                         std::span<const SwitchCase> cases) {
    ValueId ops[] = {v};
    uint32_t table = func_.make_jump_table(cases);
    emit(Opcode::Switch, TypeId{}, ops, pack_pair_aux(default_call.index, table));
}

void Builder::br_indirect(ValueId target_ptr,
                          std::span<const BlockId> plausible_targets) {
    std::vector<BlockCallId> calls;
    calls.reserve(plausible_targets.size());
    for (BlockId target : plausible_targets) {
        calls.push_back(func_.make_block_call(target, {}));
    }
    uint32_t list = func_.make_block_call_list(calls);
    ValueId ops[] = {target_ptr};
    emit(Opcode::BrIndirect, TypeId{}, ops, pack_pair_aux(list, 0));
}

void Builder::asm_goto(uint32_t payload_index,
                       std::span<const ValueId> inputs,
                       BlockId fallthrough,
                       std::span<const BlockId> targets) {
    std::vector<BlockCallId> calls;
    calls.reserve(targets.size() + 1);
    calls.push_back(func_.make_block_call(fallthrough, {}));
    for (BlockId target : targets) {
        calls.push_back(func_.make_block_call(target, {}));
    }
    uint32_t list = func_.make_block_call_list(calls);
    emit(Opcode::AsmGoto, TypeId{}, inputs, payload_index, 0, list);
}

void Builder::ret(ValueId v) {
    ValueId ops[] = {v};
    emit(Opcode::Ret, TypeId{}, ops);
}

void Builder::throw_(ValueId exception, ValueId typeinfo, ValueId destructor) {
    std::vector<ValueId> ops;
    ops.reserve(destructor.is_valid() ? 3 : 2);
    ops.push_back(exception);
    ops.push_back(typeinfo);
    if (destructor.is_valid()) {
        ops.push_back(destructor);
    }
    emit(Opcode::Throw, TypeId{}, ops);
}

void Builder::rethrow() {
    emit(Opcode::Rethrow, TypeId{}, {});
}

void Builder::resume(ValueId exception, ValueId selector) {
    ValueId ops[] = {exception, selector};
    emit(Opcode::Resume, TypeId{}, ops);
}

ValueId Builder::invoke(FuncId callee, std::span<const ValueId> args,
                        BlockId normal_target,
                        std::span<const ValueId> normal_args,
                        BlockId unwind_target,
                        std::span<const ValueId> unwind_args) {
    const SigData& sig = module_.types().signature(module_.function(callee).sig());
    TypeId result_type =
        sig.ret_class == RetClass::Scalar ? sig.ret_type : TypeId{};
    BlockCallId normal = func_.make_block_call(normal_target, normal_args);
    BlockCallId unwind = func_.make_block_call(unwind_target, unwind_args);
    InstId inst = emit(Opcode::Invoke, result_type, args, callee.index, 0,
                       pack_pair_aux(normal.index, unwind.index));
    return result_of(inst);
}

ValueId Builder::invoke_indirect(SigId sig_id, ValueId callee,
                                 std::span<const ValueId> args,
                                 BlockId normal_target,
                                 std::span<const ValueId> normal_args,
                                 BlockId unwind_target,
                                 std::span<const ValueId> unwind_args) {
    const SigData& sig = module_.types().signature(sig_id);
    TypeId result_type =
        sig.ret_class == RetClass::Scalar ? sig.ret_type : TypeId{};
    std::vector<ValueId> ops;
    ops.reserve(args.size() + 1);
    ops.push_back(callee);
    ops.insert(ops.end(), args.begin(), args.end());
    BlockCallId normal = func_.make_block_call(normal_target, normal_args);
    BlockCallId unwind = func_.make_block_call(unwind_target, unwind_args);
    InstId inst = emit(Opcode::InvokeIndirect, result_type, ops, sig_id.index, 0,
                       pack_pair_aux(normal.index, unwind.index));
    return result_of(inst);
}

InstId Builder::emit(Opcode op, TypeId result_type, std::span<const ValueId> operands,
                     uint64_t aux, uint16_t flags, uint64_t aux2) {
    assert(block_.is_valid() && "builder has no insertion point");
    InstId inst =
        func_.make_inst(op, result_type, operands, aux, loc_, flags, aux2);
    if (before_.is_valid()) {
        func_.insert_before(before_, inst);
    } else {
        func_.append_inst(block_, inst);
    }
    return inst;
}

ValueId Builder::binary(Opcode op, ValueId a, ValueId b) {
    ValueId ops[] = {a, b};
    return result_of(emit(op, func_.value_type(a), ops));
}

ValueId Builder::unary_same_type(Opcode op, ValueId a) {
    ValueId ops[] = {a};
    return result_of(emit(op, func_.value_type(a), ops));
}

} // namespace aburi::air
