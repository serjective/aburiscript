#ifndef ABURI_AIR_BUILDER_H
#define ABURI_AIR_BUILDER_H

#include "function.h"
#include "module.h"

#include <cstdint>
#include <span>
#include <utility>

namespace aburi::air {

class Builder {
public:
    Builder(Module& module, Function& func) : module_(module), func_(func) {}

    Module& module() { return module_; }
    Function& func() { return func_; }

    BlockId create_block(std::span<const TypeId> param_types = {}) {
        return func_.create_block(param_types);
    }
    void set_insertion_point(BlockId block) {
        block_ = block;
        before_ = InstId{};
    }
    void set_insertion_before(InstId inst) {
        block_ = func_.inst(inst).block;
        before_ = inst;
    }
    BlockId insertion_block() const { return block_; }

    void set_loc(SrcLoc loc) { loc_ = loc; }
    SrcLoc loc() const { return loc_; }
    ValueId const_int(TypeId type, uint64_t bits, uint64_t high_bits = 0) {
        const TypeTable& types = module_.types();
        if (types.is_valid(type) && types.is_int(type)) {
            const uint16_t width = types.int_width(type);
            if (width < 64) {
                bits &= width == 0 ? 0 : (uint64_t{1} << width) - 1;
                high_bits = 0;
            } else if (width == 64) {
                high_bits = 0;
            } else if (width < 128) {
                high_bits &= (uint64_t{1} << (width - 64)) - 1;
            }
        }
        return func_.const_int(type, bits, high_bits);
    }
    ValueId const_bool(bool v) { return const_int(types::I8, v ? 1 : 0); }
    ValueId const_i32(int32_t v) {
        return const_int(types::I32, static_cast<uint32_t>(v));
    }
    ValueId const_i64(int64_t v) {
        return const_int(types::I64, static_cast<uint64_t>(v));
    }
    ValueId const_float_bits(TypeId type,
                             uint64_t bits,
                             uint64_t high_bits = 0) {
        return func_.const_float_bits(type, bits, high_bits);
    }
    ValueId const_null(uint32_t address_space = 0) {
        return func_.const_null(module_.types().get_ptr(address_space));
    }
    ValueId undef(TypeId type) { return func_.undef(type); }
    ValueId global_addr(GlobalId global) {
        return func_.global_addr(global, types::PTR);
    }
    ValueId func_addr(FuncId callee) { return func_.func_addr(callee, types::PTR); }
    ValueId label_addr(BlockId target) { return func_.label_addr(target, types::PTR); }

    ValueId stack_alloc(uint64_t size_bytes, uint32_t align_bytes);
    ValueId stack_alloc_dyn(ValueId size_bytes, uint32_t align_bytes);
    ValueId stack_save();
    void stack_restore(ValueId saved);
    ValueId load(TypeId type, ValueId ptr, uint32_t align_bytes,
                 bool is_volatile = false);
    void store(ValueId value, ValueId ptr, uint32_t align_bytes,
               bool is_volatile = false);
    void memcpy_(ValueId dst, ValueId src, ValueId size_bytes);
    void memmove_(ValueId dst, ValueId src, ValueId size_bytes);
    void memset_(ValueId dst, ValueId byte, ValueId size_bytes);

    ValueId atomic_load(TypeId type, ValueId ptr, uint32_t align_bytes,
                        MemOrder order);
    void atomic_store(ValueId value, ValueId ptr, uint32_t align_bytes,
                      MemOrder order);
    ValueId atomic_rmw(RmwOp op, ValueId ptr, ValueId value, MemOrder order);
    ValueId atomic_cas(ValueId ptr, ValueId expected, ValueId desired,
                       MemOrder success, MemOrder failure);
    void fence(MemOrder order);
    ValueId iadd(ValueId a, ValueId b) { return binary(Opcode::Iadd, a, b); }
    ValueId isub(ValueId a, ValueId b) { return binary(Opcode::Isub, a, b); }
    ValueId imul(ValueId a, ValueId b) { return binary(Opcode::Imul, a, b); }
    ValueId iand(ValueId a, ValueId b) { return binary(Opcode::Iand, a, b); }
    ValueId ior(ValueId a, ValueId b) { return binary(Opcode::Ior, a, b); }
    ValueId ixor(ValueId a, ValueId b) { return binary(Opcode::Ixor, a, b); }
    ValueId shl(ValueId a, ValueId b) { return binary(Opcode::Shl, a, b); }
    ValueId sdiv(ValueId a, ValueId b) { return binary(Opcode::Sdiv, a, b); }
    ValueId udiv(ValueId a, ValueId b) { return binary(Opcode::Udiv, a, b); }
    ValueId srem(ValueId a, ValueId b) { return binary(Opcode::Srem, a, b); }
    ValueId urem(ValueId a, ValueId b) { return binary(Opcode::Urem, a, b); }
    ValueId ashr(ValueId a, ValueId b) { return binary(Opcode::Ashr, a, b); }
    ValueId lshr(ValueId a, ValueId b) { return binary(Opcode::Lshr, a, b); }
    ValueId fadd(ValueId a, ValueId b) { return binary(Opcode::Fadd, a, b); }
    ValueId fsub(ValueId a, ValueId b) { return binary(Opcode::Fsub, a, b); }
    ValueId fmul(ValueId a, ValueId b) { return binary(Opcode::Fmul, a, b); }
    ValueId fdiv(ValueId a, ValueId b) { return binary(Opcode::Fdiv, a, b); }
    ValueId frem(ValueId a, ValueId b) { return binary(Opcode::Frem, a, b); }
    ValueId fneg(ValueId a);

    ValueId bswap(ValueId a) { return unary_same_type(Opcode::Bswap, a); }
    ValueId clz(ValueId a) { return unary_same_type(Opcode::Clz, a); }
    ValueId ctz(ValueId a) { return unary_same_type(Opcode::Ctz, a); }
    ValueId popcnt(ValueId a) { return unary_same_type(Opcode::Popcnt, a); }

    ValueId icmp(IntCond cond, ValueId a, ValueId b);
    ValueId fcmp(FloatCond cond, ValueId a, ValueId b);
    ValueId cast(Opcode op, TypeId to, ValueId v);
    ValueId trunc(TypeId to, ValueId v) { return cast(Opcode::Trunc, to, v); }
    ValueId zext(TypeId to, ValueId v) { return cast(Opcode::Zext, to, v); }
    ValueId sext(TypeId to, ValueId v) { return cast(Opcode::Sext, to, v); }
    ValueId fptrunc(TypeId to, ValueId v) { return cast(Opcode::Fptrunc, to, v); }
    ValueId fpext(TypeId to, ValueId v) { return cast(Opcode::Fpext, to, v); }
    ValueId fptosi(TypeId to, ValueId v) { return cast(Opcode::Fptosi, to, v); }
    ValueId fptoui(TypeId to, ValueId v) { return cast(Opcode::Fptoui, to, v); }
    ValueId sitofp(TypeId to, ValueId v) { return cast(Opcode::Sitofp, to, v); }
    ValueId uitofp(TypeId to, ValueId v) { return cast(Opcode::Uitofp, to, v); }
    ValueId ptrtoint(TypeId to, ValueId v) { return cast(Opcode::Ptrtoint, to, v); }
    ValueId inttoptr(TypeId to, ValueId v) { return cast(Opcode::Inttoptr, to, v); }
    ValueId bitcast(TypeId to, ValueId v) { return cast(Opcode::Bitcast, to, v); }

    TypeId size_int_type() const {
        return module_.target().pointer_width == 64 ? types::I64 : types::I32;
    }
    ValueId const_usize(int64_t v) {
        return const_int(size_int_type(), static_cast<uint64_t>(v));
    }
    ValueId ptr_add(ValueId ptr, ValueId byte_offset);
    ValueId ptr_add(ValueId ptr, int64_t byte_offset) {
        return ptr_add(ptr, const_usize(byte_offset));
    }

    ValueId select(ValueId cond, ValueId a, ValueId b);

    void va_start_(ValueId va_list_ptr);
    void inline_asm(uint32_t payload_index, std::span<const ValueId> inputs);
    void trap();
    ValueId frame_addr();
    ValueId return_addr();

    // ---- calls ----
    // The operand list must match the signature's ABI shape: the Sret-role
    // argument in position 0 for IndirectSret callees, and one trailing
    // destination pointer for IntPair/Hfa callees. The result is valid only
    // for Scalar returns.
    ValueId call(FuncId callee, std::span<const ValueId> args);
    ValueId call_indirect(SigId sig, ValueId callee, std::span<const ValueId> args);
    void tail_call_indirect(SigId sig, ValueId callee,
                            std::span<const ValueId> args);
    ValueId eh_alloc_exception(uint64_t size_bytes);
    ValueId eh_landing_pad(uint32_t payload_index);
    ValueId eh_selector(ValueId exception_ptr);
    ValueId eh_typeid_for(ValueId typeinfo);
    ValueId catch_begin(ValueId exception_ptr);
    void catch_end();

    void jump(BlockId target, std::span<const ValueId> args = {});
    void br_if(ValueId cond, BlockId then_target, std::span<const ValueId> then_args,
               BlockId else_target, std::span<const ValueId> else_args);
    void br_if(ValueId cond, BlockId then_target, BlockId else_target) {
        br_if(cond, then_target, {}, else_target, {});
    }
    void switch_(ValueId v, BlockId default_target,
                 std::span<const std::pair<uint64_t, BlockId>> cases);
    void switch_raw(ValueId v, BlockCallId default_call,
                    std::span<const SwitchCase> cases);
    void br_indirect(ValueId target_ptr, std::span<const BlockId> plausible_targets);
    void asm_goto(uint32_t payload_index, std::span<const ValueId> inputs,
                  BlockId fallthrough, std::span<const BlockId> targets);
    void ret() { emit(Opcode::Ret, TypeId{}, {}); }
    void ret(ValueId v);
    void unreachable_() { emit(Opcode::Unreachable, TypeId{}, {}); }
    void throw_(ValueId exception, ValueId typeinfo, ValueId destructor = {});
    void rethrow();
    void resume(ValueId exception, ValueId selector);
    ValueId invoke(FuncId callee, std::span<const ValueId> args,
                   BlockId normal_target, std::span<const ValueId> normal_args,
                   BlockId unwind_target, std::span<const ValueId> unwind_args);
    ValueId invoke_indirect(SigId sig, ValueId callee, std::span<const ValueId> args,
                            BlockId normal_target,
                            std::span<const ValueId> normal_args,
                            BlockId unwind_target,
                            std::span<const ValueId> unwind_args);
    InstId emit(Opcode op, TypeId result_type, std::span<const ValueId> operands,
                uint64_t aux = 0, uint16_t flags = 0, uint64_t aux2 = 0);

private:
    ValueId binary(Opcode op, ValueId a, ValueId b);
    ValueId unary_same_type(Opcode op, ValueId a);
    ValueId result_of(InstId inst) { return func_.inst(inst).result; }

    Module& module_;
    Function& func_;
    BlockId block_;
    InstId before_;
    SrcLoc loc_;
};

} // namespace aburi::air

#endif // ABURI_AIR_BUILDER_H
