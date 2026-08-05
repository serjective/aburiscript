#include "legalize_internal.h"

#include "builder.h"

#include <unordered_map>
#include <vector>

namespace aburi::air::legalize_detail {

namespace {

struct Halves {
    ValueId lo, hi;
};

class I64Stage {
public:
    I64Stage(Module& mod, StageState& state) : mod_(mod), state_(state) {}

    void run() {
        uint32_t function_count = mod_.function_count();
        for (uint32_t index = 1; index <= function_count; ++index) {
            old_sig_.emplace(index, mod_.function(FuncId{index}).sig().index);
        }
        for (uint32_t index = 1; index <= function_count; ++index) {
            Function& func = mod_.function(FuncId{index});
            SigId mapped = map_sig(func.sig());
            if (!state_.ok) {
                return;
            }
            if (mapped != func.sig()) {
                func.set_sig(mapped);
                state_.changed = true;
            }
        }
        for (uint32_t index = 1; index <= function_count; ++index) {
            Function& func = mod_.function(FuncId{index});
            if (!func.is_declaration()) {
                run_on_function(func, SigId{old_sig_.at(index)});
                if (!state_.ok) {
                    return;
                }
            }
        }
    }

private:
    bool big_endian() const {
        return state_.config.endianness == EndiannessKind::Big;
    }
    ValueId first_half(Halves h) const { return big_endian() ? h.hi : h.lo; }
    ValueId second_half(Halves h) const { return big_endian() ? h.lo : h.hi; }
    int64_t lo_byte_offset() const { return big_endian() ? 4 : 0; }
    int64_t hi_byte_offset() const { return big_endian() ? 0 : 4; }

    bool is_i64(TypeId type) const { return type == types::I64; }
    bool is_i128(TypeId type) const { return type == types::I128; }

    SigId map_sig(SigId sig) {
        auto found = sig_map_.find(sig.index);
        if (found != sig_map_.end()) {
            return SigId{found->second};
        }
        const SigData& data = mod_.types().signature(sig);
        SigData out;
        out.is_variadic = data.is_variadic;
        out.ret_sse_mask = data.ret_sse_mask;
        bool changed = false;
        switch (data.ret_class) {
            case RetClass::Scalar:
                if (is_i64(data.ret_type)) {
                    out.ret_class = RetClass::IntPair;
                    out.ret_type = types::I32;
                    out.ret_count = 2;
                    changed = true;
                } else if (is_i128(data.ret_type)) {
                    state_.fail("i128 returns are not supported on a "
                                "4-byte-word target");
                    return sig;
                } else {
                    out.ret_class = data.ret_class;
                    out.ret_type = data.ret_type;
                    out.ret_count = data.ret_count;
                }
                break;
            case RetClass::IntPair:
                if (is_i64(data.ret_type)) {
                    state_.fail("a 16-byte register-pair return is not "
                                "representable on a 4-byte-word target");
                    return sig;
                }
                [[fallthrough]];
            case RetClass::Void:
            case RetClass::Hfa:
            case RetClass::IndirectSret:
                out.ret_class = data.ret_class;
                out.ret_type = data.ret_type;
                out.ret_count = data.ret_count;
                break;
        }
        uint32_t fixed_bump = 0;
        for (uint32_t index = 0; index < data.params.size(); ++index) {
            const SigParam& param = data.params[index];
            if (is_i128(param.type)) {
                state_.fail("i128 parameters are not supported on a "
                            "4-byte-word target");
                return sig;
            }
            if (is_i64(param.type) && param.role == ParamRole::Normal) {
                SigParam first{types::I32, ParamRole::Normal};
                first.coerce_group = 2;
                out.params.push_back(first);
                out.params.push_back({types::I32, ParamRole::Normal});
                if (index < data.fixed_param_count) {
                    ++fixed_bump;
                }
                changed = true;
            } else {
                out.params.push_back(param);
            }
        }
        out.fixed_param_count = data.fixed_param_count + fixed_bump;
        SigId mapped = changed ? mod_.types().get_signature(out) : sig;
        sig_map_.emplace(sig.index, mapped.index);
        return mapped;
    }

    SigData pair_binary_sig() const {
        SigData sig;
        sig.ret_class = RetClass::IntPair;
        sig.ret_type = types::I32;
        sig.ret_count = 2;
        SigParam group{types::I32, ParamRole::Normal};
        group.coerce_group = 2;
        sig.params = {group, {types::I32}, group, {types::I32}};
        return sig;
    }

    SigData shift_sig() const {
        SigData sig;
        sig.ret_class = RetClass::IntPair;
        sig.ret_type = types::I32;
        sig.ret_count = 2;
        SigParam group{types::I32, ParamRole::Normal};
        group.coerce_group = 2;
        sig.params = {group, {types::I32}, {types::I32}};
        return sig;
    }

    SigData pair_to_float_sig(TypeId float_type) const {
        SigData sig;
        sig.ret_class = RetClass::Scalar;
        sig.ret_type = float_type;
        sig.ret_count = 1;
        SigParam group{types::I32, ParamRole::Normal};
        group.coerce_group = 2;
        sig.params = {group, {types::I32}};
        return sig;
    }

    SigData float_to_pair_sig(TypeId float_type) const {
        SigData sig;
        sig.ret_class = RetClass::IntPair;
        sig.ret_type = types::I32;
        sig.ret_count = 2;
        sig.params = {{float_type}};
        return sig;
    }

    FuncId helper(LibcallId id, const SigData& sig) {
        return find_or_declare(mod_, libcall_name(state_.config, id), sig);
    }

    Halves halves(Function& func, ValueId value) {
        auto found = pairs_.find(value.index);
        if (found != pairs_.end()) {
            return found->second;
        }

        ValueData data = func.value(value);
        Halves result;
        if (data.kind == ValueKind::ConstInt) {
            result = {func.const_int(types::I32, data.payload & 0xffffffffu),
                      func.const_int(types::I32, data.payload >> 32)};
        } else {

            result = {func.undef(types::I32), func.undef(types::I32)};
        }
        pairs_.emplace(value.index, result);
        return result;
    }
    void emit_pair_call(Function& func, Builder& b, FuncId callee,
                        std::vector<ValueId> args, ValueId result_of) {
        ValueId staging = b.stack_alloc(8, 4);
        args.push_back(staging);
        b.call(callee, args);
        ValueId lo = b.load(types::I32, b.ptr_add(staging, lo_byte_offset()), 4);
        ValueId hi = b.load(types::I32, b.ptr_add(staging, hi_byte_offset()), 4);
        pairs_[result_of.index] = {lo, hi};
    }

    void run_on_function(Function& func, SigId old_sig) {
        pairs_.clear();
        split_block_params(func);
        if (!state_.ok) {
            return;
        }
        bool ret_pairified =
            mod_.types().signature(old_sig).ret_class == RetClass::Scalar &&
            is_i64(mod_.types().signature(old_sig).ret_type);
        Builder b(mod_, func);
        std::vector<BlockId> order = walk_order(func);
        for (BlockId block : order) {
            for (InstId inst = func.block(block).first; inst.is_valid();) {
                InstId next = func.inst(inst).next;
                rewrite_inst(func, b, inst, ret_pairified);
                if (!state_.ok) {
                    return;
                }
                inst = next;
            }
        }
    }
    void split_block_params(Function& func) {
        for (BlockId block = func.first_block(); block.is_valid();
             block = func.block(block).next) {
            auto params = func.block_params(block);
            bool any_i64 = false;
            for (ValueId param : params) {
                TypeId type = func.value_type(param);
                if (is_i128(type)) {
                    state_.fail("i128 block parameters are not supported on "
                                "a 4-byte-word target");
                    return;
                }
                any_i64 |= is_i64(type);
            }
            if (!any_i64) {
                continue;
            }
            std::vector<ValueId> old_params(params.begin(), params.end());
            std::vector<TypeId> new_types;
            for (ValueId param : old_params) {
                if (is_i64(func.value_type(param))) {
                    new_types.push_back(types::I32);
                    new_types.push_back(types::I32);
                } else {
                    new_types.push_back(func.value_type(param));
                }
            }
            func.set_block_params(block, new_types);
            auto new_params = func.block_params(block);
            size_t cursor = 0;
            for (ValueId old_param : old_params) {
                if (is_i64(func.value_type(old_param))) {
                    ValueId first = new_params[cursor++];
                    ValueId second = new_params[cursor++];
                    pairs_[old_param.index] = big_endian()
                        ? Halves{second, first}
                        : Halves{first, second};
                } else {
                    func.replace_all_uses(old_param, new_params[cursor++]);
                }
            }
            state_.changed = true;
        }
    }

    std::vector<BlockId> walk_order(Function& func) {
        std::vector<BlockId> post;
        std::vector<char> seen(func.block_count() + 1, 0);
        std::vector<std::pair<BlockId, size_t>> stack;
        std::vector<BlockCallId> calls;
        auto targets_of = [&](BlockId block) {
            std::vector<BlockId> out;
            InstId last = func.block(block).last;
            if (last.is_valid()) {
                calls.clear();
                func.successors(last, calls);
                for (BlockCallId call : calls) {
                    out.push_back(func.block_call(call).target);
                }
            }
            return out;
        };
        std::vector<std::vector<BlockId>> succ_stack;
        stack.push_back({func.entry_block(), 0});
        succ_stack.push_back(targets_of(func.entry_block()));
        seen[func.entry_block().index] = 1;
        while (!stack.empty()) {
            size_t top = stack.size() - 1;
            if (stack[top].second < succ_stack[top].size()) {

                BlockId next = succ_stack[top][stack[top].second++];
                if (next.index >= seen.size()) {
                    seen.resize(next.index + 1, 0);
                }
                if (!seen[next.index]) {
                    seen[next.index] = 1;
                    stack.push_back({next, 0});
                    succ_stack.push_back(targets_of(next));
                }
            } else {
                post.push_back(stack[top].first);
                stack.pop_back();
                succ_stack.pop_back();
            }
        }
        std::vector<BlockId> order(post.rbegin(), post.rend());
        for (BlockId block = func.first_block(); block.is_valid();
             block = func.block(block).next) {
            if (block.index >= seen.size() || !seen[block.index]) {
                order.push_back(block);
            }
        }
        return order;
    }
    void rewrite_edge_args(Function& func, BlockCallId call) {
        auto args = func.block_call_args(call);
        bool any = false;
        for (ValueId arg : args) {
            any |= is_i64(func.value_type(arg));
        }
        if (!any) {
            return;
        }
        std::vector<ValueId> old_args(args.begin(), args.end());
        std::vector<ValueId> new_args;
        for (ValueId arg : old_args) {
            if (is_i64(func.value_type(arg))) {
                Halves h = halves(func, arg);
                new_args.push_back(first_half(h));
                new_args.push_back(second_half(h));
            } else {
                new_args.push_back(arg);
            }
        }
        func.set_block_call_args(call, new_args);
        state_.changed = true;
    }

    void rewrite_terminator_edges(Function& func, InstId inst) {
        std::vector<BlockCallId> calls;
        func.successors(inst, calls);
        for (BlockCallId call : calls) {
            rewrite_edge_args(func, call);
        }
    }

    void rewrite_inst(Function& func, Builder& b, InstId inst,
                      bool ret_pairified) {

        InstData data = func.inst(inst);
        auto ops_span = func.operands(inst);
        std::vector<ValueId> ops(ops_span.begin(), ops_span.end());

        if (is_i128(data.type)) {
            state_.fail("i128 operations are not supported on a 4-byte-word "
                        "target");
            return;
        }

        auto opcode_traits_is_terminator = [&]() {
            switch (data.op) {
                case Opcode::Jump:
                case Opcode::BrIf:
                case Opcode::Switch:
                case Opcode::BrIndirect:
                case Opcode::Invoke:
                case Opcode::InvokeIndirect:
                    return true;
                default:
                    return false;
            }
        };
        if (opcode_traits_is_terminator()) {
            rewrite_terminator_edges(func, inst);
        }

        switch (data.op) {
            case Opcode::Load: {
                if (!is_i64(data.type)) {
                    return;
                }
                b.set_insertion_before(inst);
                b.set_loc(data.loc);
                uint32_t align = 1u << static_cast<uint8_t>(data.aux);
                uint32_t part_align = align < 4 ? align : 4;
                bool is_volatile = (data.flags & INST_FLAG_VOLATILE) != 0;
                ValueId base = ops[0];
                ValueId at0 =
                    b.load(types::I32, base, part_align, is_volatile);
                ValueId at4 = b.load(types::I32, b.ptr_add(base, 4),
                                     part_align, is_volatile);
                pairs_[data.result.index] = big_endian() ? Halves{at4, at0}
                                                         : Halves{at0, at4};
                func.remove_inst(inst);
                state_.changed = true;
                return;
            }
            case Opcode::Store: {
                if (!is_i64(func.value_type(ops[0]))) {
                    return;
                }
                b.set_insertion_before(inst);
                b.set_loc(data.loc);
                uint32_t align = 1u << static_cast<uint8_t>(data.aux);
                uint32_t part_align = align < 4 ? align : 4;
                bool is_volatile = (data.flags & INST_FLAG_VOLATILE) != 0;
                Halves h = halves(func, ops[0]);
                ValueId base = ops[1];
                b.store(first_half(h), base, part_align, is_volatile);
                b.store(second_half(h), b.ptr_add(base, 4), part_align,
                        is_volatile);
                func.remove_inst(inst);
                state_.changed = true;
                return;
            }
            case Opcode::Iadd:
            case Opcode::Isub: {
                if (!is_i64(data.type)) {
                    return;
                }
                if (state_.config.i64.add_sub != LegalizeAction::Expand) {
                    state_.fail("LegalizeAction::Keep for i64 add/sub is not "
                                "implemented yet (arrives with armv7)");
                    return;
                }
                b.set_insertion_before(inst);
                b.set_loc(data.loc);
                Halves a = halves(func, ops[0]);
                Halves c = halves(func, ops[1]);
                Halves out;
                if (data.op == Opcode::Iadd) {
                    out.lo = b.iadd(a.lo, c.lo);
                    ValueId carry =
                        b.zext(types::I32, b.icmp(IntCond::Ult, out.lo, a.lo));
                    out.hi = b.iadd(b.iadd(a.hi, c.hi), carry);
                } else {
                    ValueId borrow =
                        b.zext(types::I32, b.icmp(IntCond::Ult, a.lo, c.lo));
                    out.lo = b.isub(a.lo, c.lo);
                    out.hi = b.isub(b.isub(a.hi, c.hi), borrow);
                }
                pairs_[data.result.index] = out;
                func.remove_inst(inst);
                state_.changed = true;
                return;
            }
            case Opcode::Iand:
            case Opcode::Ior:
            case Opcode::Ixor: {
                if (!is_i64(data.type)) {
                    return;
                }
                b.set_insertion_before(inst);
                b.set_loc(data.loc);
                Halves a = halves(func, ops[0]);
                Halves c = halves(func, ops[1]);
                Halves out;
                if (data.op == Opcode::Iand) {
                    out = {b.iand(a.lo, c.lo), b.iand(a.hi, c.hi)};
                } else if (data.op == Opcode::Ior) {
                    out = {b.ior(a.lo, c.lo), b.ior(a.hi, c.hi)};
                } else {
                    out = {b.ixor(a.lo, c.lo), b.ixor(a.hi, c.hi)};
                }
                pairs_[data.result.index] = out;
                func.remove_inst(inst);
                state_.changed = true;
                return;
            }
            case Opcode::Imul:
            case Opcode::Sdiv:
            case Opcode::Udiv:
            case Opcode::Srem:
            case Opcode::Urem: {
                if (!is_i64(data.type)) {
                    return;
                }
                LegalizeAction action = data.op == Opcode::Imul
                    ? state_.config.i64.mul
                    : state_.config.i64.div_rem;
                if (action != LegalizeAction::Libcall) {
                    state_.fail("i64 mul/div/rem require "
                                "LegalizeAction::Libcall");
                    return;
                }
                LibcallId id = data.op == Opcode::Imul   ? LibcallId::MulDI3
                    : data.op == Opcode::Sdiv            ? LibcallId::DivDI3
                    : data.op == Opcode::Udiv            ? LibcallId::UDivDI3
                    : data.op == Opcode::Srem            ? LibcallId::ModDI3
                                                         : LibcallId::UModDI3;
                b.set_insertion_before(inst);
                b.set_loc(data.loc);
                Halves a = halves(func, ops[0]);
                Halves c = halves(func, ops[1]);
                emit_pair_call(func, b, helper(id, pair_binary_sig()),
                               {first_half(a), second_half(a), first_half(c),
                                second_half(c)},
                               data.result);
                func.remove_inst(inst);
                state_.changed = true;
                return;
            }
            case Opcode::Shl:
            case Opcode::Lshr:
            case Opcode::Ashr: {
                if (!is_i64(data.type)) {
                    return;
                }
                rewrite_shift(func, b, inst, data, ops);
                return;
            }
            case Opcode::Icmp: {
                if (!is_i64(func.value_type(ops[0]))) {
                    return;
                }
                rewrite_icmp(func, b, inst, data, ops);
                return;
            }
            case Opcode::Select: {
                if (!is_i64(data.type)) {
                    return;
                }
                b.set_insertion_before(inst);
                b.set_loc(data.loc);
                Halves a = halves(func, ops[1]);
                Halves c = halves(func, ops[2]);
                pairs_[data.result.index] = {b.select(ops[0], a.lo, c.lo),
                                             b.select(ops[0], a.hi, c.hi)};
                func.remove_inst(inst);
                state_.changed = true;
                return;
            }
            case Opcode::Trunc: {
                TypeId src_type = func.value_type(ops[0]);
                if (!is_i64(src_type)) {
                    return;
                }
                b.set_insertion_before(inst);
                b.set_loc(data.loc);
                Halves h = halves(func, ops[0]);
                ValueId result = data.type == types::I32
                    ? h.lo
                    : b.trunc(data.type, h.lo);
                func.replace_all_uses(data.result, result);
                func.remove_inst(inst);
                state_.changed = true;
                return;
            }
            case Opcode::Zext:
            case Opcode::Sext: {
                if (!is_i64(data.type)) {
                    return;
                }
                b.set_insertion_before(inst);
                b.set_loc(data.loc);
                TypeId src_type = func.value_type(ops[0]);
                bool is_signed = data.op == Opcode::Sext;
                ValueId lo = src_type == types::I32
                    ? ops[0]
                    : (is_signed ? b.sext(types::I32, ops[0])
                                 : b.zext(types::I32, ops[0]));
                ValueId hi = is_signed
                    ? b.ashr(lo, func.const_int(types::I32, 31))
                    : func.const_int(types::I32, 0);
                pairs_[data.result.index] = {lo, hi};
                func.remove_inst(inst);
                state_.changed = true;
                return;
            }
            case Opcode::Bswap:
            case Opcode::Clz:
            case Opcode::Ctz:
            case Opcode::Popcnt: {
                if (!is_i64(data.type)) {
                    return;
                }
                if (state_.config.i64.bit_manip != LegalizeAction::Expand) {
                    state_.fail("only LegalizeAction::Expand is implemented "
                                "for i64 bit manipulation");
                    return;
                }
                b.set_insertion_before(inst);
                b.set_loc(data.loc);
                Halves h = halves(func, ops[0]);
                ValueId zero = func.const_int(types::I32, 0);
                ValueId thirtytwo = func.const_int(types::I32, 32);
                Halves out;
                if (data.op == Opcode::Bswap) {
                    out = {b.bswap(h.hi), b.bswap(h.lo)};
                } else if (data.op == Opcode::Clz) {
                    ValueId hi_zero = b.icmp(IntCond::Eq, h.hi, zero);
                    out.lo = b.select(hi_zero, b.iadd(b.clz(h.lo), thirtytwo),
                                      b.clz(h.hi));
                    out.hi = zero;
                } else if (data.op == Opcode::Ctz) {
                    ValueId lo_zero = b.icmp(IntCond::Eq, h.lo, zero);
                    out.lo = b.select(lo_zero, b.iadd(b.ctz(h.hi), thirtytwo),
                                      b.ctz(h.lo));
                    out.hi = zero;
                } else {
                    out.lo = b.iadd(b.popcnt(h.lo), b.popcnt(h.hi));
                    out.hi = zero;
                }
                pairs_[data.result.index] = out;
                func.remove_inst(inst);
                state_.changed = true;
                return;
            }
            case Opcode::Ptrtoint: {
                if (!is_i64(data.type)) {
                    return;
                }
                b.set_insertion_before(inst);
                b.set_loc(data.loc);
                pairs_[data.result.index] = {
                    b.ptrtoint(types::I32, ops[0]),
                    func.const_int(types::I32, 0)};
                func.remove_inst(inst);
                state_.changed = true;
                return;
            }
            case Opcode::Inttoptr: {
                if (!is_i64(func.value_type(ops[0]))) {
                    return;
                }
                b.set_insertion_before(inst);
                b.set_loc(data.loc);
                Halves h = halves(func, ops[0]);
                ValueId result = b.inttoptr(data.type, h.lo);
                func.replace_all_uses(data.result, result);
                func.remove_inst(inst);
                state_.changed = true;
                return;
            }
            case Opcode::Bitcast: {
                if (is_i64(data.type) || is_i64(func.value_type(ops[0]))) {
                    state_.fail("i64 bitcasts are not supported on a "
                                "4-byte-word target yet (hard-float armv7 "
                                "item)");
                }
                return;
            }
            case Opcode::Sitofp:
            case Opcode::Uitofp: {
                if (!is_i64(func.value_type(ops[0]))) {
                    return;
                }
                bool is_signed = data.op == Opcode::Sitofp;
                bool to_f32 =
                    mod_.types().type(data.type).float_kind == FloatKind::F32;
                if (!mod_.types().is_float(data.type) ||
                    (mod_.types().type(data.type).float_kind != FloatKind::F32 &&
                     mod_.types().type(data.type).float_kind != FloatKind::F64)) {
                    state_.fail("i64 to non-f32/f64 conversion is not "
                                "supported on a 4-byte-word target");
                    return;
                }
                LibcallId id = to_f32
                    ? (is_signed ? LibcallId::FloatDISF : LibcallId::FloatUnDISF)
                    : (is_signed ? LibcallId::FloatDIDF : LibcallId::FloatUnDIDF);
                b.set_insertion_before(inst);
                b.set_loc(data.loc);
                Halves h = halves(func, ops[0]);
                const ValueId args[] = {first_half(h), second_half(h)};
                ValueId result =
                    b.call(helper(id, pair_to_float_sig(data.type)), args);
                func.replace_all_uses(data.result, result);
                func.remove_inst(inst);
                state_.changed = true;
                return;
            }
            case Opcode::Fptosi:
            case Opcode::Fptoui: {
                if (!is_i64(data.type)) {
                    return;
                }
                TypeId src_type = func.value_type(ops[0]);
                bool is_signed = data.op == Opcode::Fptosi;
                if (!mod_.types().is_float(src_type) ||
                    (mod_.types().type(src_type).float_kind != FloatKind::F32 &&
                     mod_.types().type(src_type).float_kind != FloatKind::F64)) {
                    state_.fail("non-f32/f64 to i64 conversion is not "
                                "supported on a 4-byte-word target");
                    return;
                }
                bool from_f32 =
                    mod_.types().type(src_type).float_kind == FloatKind::F32;
                LibcallId id = from_f32
                    ? (is_signed ? LibcallId::FixSFDI : LibcallId::FixUnsSFDI)
                    : (is_signed ? LibcallId::FixDFDI : LibcallId::FixUnsDFDI);
                b.set_insertion_before(inst);
                b.set_loc(data.loc);
                emit_pair_call(func, b, helper(id, float_to_pair_sig(src_type)),
                               {ops[0]}, data.result);
                func.remove_inst(inst);
                state_.changed = true;
                return;
            }
            case Opcode::Call:
            case Opcode::CallIndirect:
                rewrite_call(func, b, inst, data, ops);
                return;
            case Opcode::Invoke:
            case Opcode::InvokeIndirect:
                rewrite_invoke(func, b, inst, data, ops);
                return;
            case Opcode::Ret: {
                if (!ret_pairified) {
                    return;
                }
                b.set_insertion_before(inst);
                b.set_loc(data.loc);
                Halves h = halves(func, ops[0]);
                ValueId staging = b.stack_alloc(8, 4);
                b.store(first_half(h), staging, 4);
                b.store(second_half(h), b.ptr_add(staging, 4), 4);
                const ValueId ret_ops[] = {staging};
                InstId new_ret =
                    func.make_inst(Opcode::Ret, TypeId{}, ret_ops, 0, data.loc);
                func.insert_before(inst, new_ret);
                func.remove_inst(inst);
                state_.changed = true;
                return;
            }
            case Opcode::Switch: {
                if (!is_i64(func.value_type(ops[0]))) {
                    return;
                }
                rewrite_switch(func, b, inst, data, ops);
                return;
            }
            case Opcode::AtomicLoad:
            case Opcode::AtomicStore:
            case Opcode::AtomicRmw:
            case Opcode::AtomicCas: {
                bool touches_i64 = is_i64(data.type);
                for (ValueId op : ops) {
                    touches_i64 |= is_i64(func.value_type(op));
                }
                if (touches_i64) {
                    state_.fail("64-bit atomics are not supported on this "
                                "target yet");
                }
                return;
            }
            case Opcode::InlineAsm:
            case Opcode::AsmGoto: {

                const AsmPayload& payload =
                    mod_.asm_payload(static_cast<uint32_t>(data.aux));
                for (size_t i = 0; i < ops.size(); ++i) {
                    if (!is_i64(func.value_type(ops[i]))) {
                        continue;
                    }
                    bool memory = i < payload.constraints.size() &&
                                  payload.constraints[i].find('m') !=
                                      std::string::npos;
                    if (!memory) {
                        state_.fail("i64 inline-asm operands are not "
                                    "supported on a 4-byte-word target");
                        return;
                    }
                }
                return;
            }
            case Opcode::Memcpy:
            case Opcode::Memmove:
            case Opcode::Memset:
            case Opcode::StackAllocDyn: {
                for (ValueId op : ops) {
                    if (is_i64(func.value_type(op))) {
                        state_.fail("i64-sized memory operations are not "
                                    "supported on a 4-byte-word target (use "
                                    "the pointer-sized integer)");
                        return;
                    }
                }
                return;
            }
            default:
                return;
        }
    }

    void rewrite_shift(Function& func, Builder& b, InstId inst,
                       const InstData& data, const std::vector<ValueId>& ops) {
        b.set_insertion_before(inst);
        b.set_loc(data.loc);
        Halves a = halves(func, ops[0]);

        ValueData amount = func.value(ops[1]);
        if (amount.kind == ValueKind::ConstInt) {
            uint64_t c = amount.payload & 63;
            Halves out = expand_constant_shift(func, b, data.op, a,
                                               static_cast<uint32_t>(c));
            pairs_[data.result.index] = out;
            func.remove_inst(inst);
            state_.changed = true;
            return;
        }
        if (state_.config.i64.shifts != LegalizeAction::Libcall) {
            state_.fail("dynamic i64 shifts require "
                        "LegalizeAction::Libcall");
            return;
        }
        LibcallId id = data.op == Opcode::Shl ? LibcallId::AshlDI3
            : data.op == Opcode::Lshr         ? LibcallId::LshrDI3
                                              : LibcallId::AshrDI3;
        Halves amt = halves(func, ops[1]);
        emit_pair_call(func, b, helper(id, shift_sig()),
                       {first_half(a), second_half(a), amt.lo}, data.result);
        func.remove_inst(inst);
        state_.changed = true;
    }

    Halves expand_constant_shift(Function& func, Builder& b, Opcode op,
                                 Halves a, uint32_t c) {
        if (c == 0) {
            return a;
        }
        ValueId zero = func.const_int(types::I32, 0);
        ValueId amt = func.const_int(types::I32, c % 32);
        ValueId inv = func.const_int(types::I32, 32 - (c % 32));
        ValueId big = func.const_int(types::I32, c - 32);
        ValueId sign_amt = func.const_int(types::I32, 31);
        if (op == Opcode::Shl) {
            if (c < 32) {
                return {b.shl(a.lo, amt),
                        b.ior(b.shl(a.hi, amt), b.lshr(a.lo, inv))};
            }
            if (c == 32) {
                return {zero, a.lo};
            }
            return {zero, b.shl(a.lo, big)};
        }
        if (op == Opcode::Lshr) {
            if (c < 32) {
                return {b.ior(b.lshr(a.lo, amt), b.shl(a.hi, inv)),
                        b.lshr(a.hi, amt)};
            }
            if (c == 32) {
                return {a.hi, zero};
            }
            return {b.lshr(a.hi, big), zero};
        }

        if (c < 32) {
            return {b.ior(b.lshr(a.lo, amt), b.shl(a.hi, inv)),
                    b.ashr(a.hi, amt)};
        }
        if (c == 32) {
            return {a.hi, b.ashr(a.hi, sign_amt)};
        }
        return {b.ashr(a.hi, big), b.ashr(a.hi, sign_amt)};
    }

    void rewrite_icmp(Function& func, Builder& b, InstId inst,
                      const InstData& data, const std::vector<ValueId>& ops) {
        b.set_insertion_before(inst);
        b.set_loc(data.loc);
        Halves a = halves(func, ops[0]);
        Halves c = halves(func, ops[1]);
        auto cond = static_cast<IntCond>(data.aux);
        ValueId result;
        if (cond == IntCond::Eq || cond == IntCond::Ne) {
            ValueId mixed =
                b.ior(b.ixor(a.lo, c.lo), b.ixor(a.hi, c.hi));
            result = b.icmp(cond, mixed, func.const_int(types::I32, 0));
        } else {
            IntCond hi_cond = cond;
            IntCond lo_cond;
            switch (cond) {
                case IntCond::Slt: lo_cond = IntCond::Ult; break;
                case IntCond::Sle: hi_cond = IntCond::Slt;
                                   lo_cond = IntCond::Ule; break;
                case IntCond::Sgt: lo_cond = IntCond::Ugt; break;
                case IntCond::Sge: hi_cond = IntCond::Sgt;
                                   lo_cond = IntCond::Uge; break;
                case IntCond::Ult: lo_cond = IntCond::Ult; break;
                case IntCond::Ule: hi_cond = IntCond::Ult;
                                   lo_cond = IntCond::Ule; break;
                case IntCond::Ugt: lo_cond = IntCond::Ugt; break;
                case IntCond::Uge: hi_cond = IntCond::Ugt;
                                   lo_cond = IntCond::Uge; break;
                default: lo_cond = IntCond::Ult; break;
            }
            ValueId hi_cmp = b.icmp(hi_cond, a.hi, c.hi);
            ValueId hi_eq = b.icmp(IntCond::Eq, a.hi, c.hi);
            ValueId lo_cmp = b.icmp(lo_cond, a.lo, c.lo);
            result = b.select(hi_eq, lo_cmp, hi_cmp);
        }
        func.replace_all_uses(data.result, result);
        func.remove_inst(inst);
        state_.changed = true;
    }

    void rewrite_call(Function& func, Builder& b, InstId inst,
                      const InstData& data, const std::vector<ValueId>& ops) {
        bool direct = data.op == Opcode::Call;
        SigId old_callee_sig;
        if (direct) {
            auto found = old_sig_.find(static_cast<uint32_t>(data.aux));
            old_callee_sig = found != old_sig_.end()
                ? SigId{found->second}
                : mod_.function(FuncId{static_cast<uint32_t>(data.aux)}).sig();
        } else {
            old_callee_sig = SigId{static_cast<uint32_t>(data.aux)};
        }
        const SigData& old_sig = mod_.types().signature(old_callee_sig);
        bool pairify_ret = old_sig.ret_class == RetClass::Scalar &&
                           is_i64(old_sig.ret_type);
        bool any_i64_arg = false;
        for (ValueId op : ops) {
            any_i64_arg |= is_i64(func.value_type(op));
        }
        SigId new_site_sig =
            direct ? SigId{} : map_sig(old_callee_sig);
        if (!state_.ok) {
            return;
        }
        bool aux_changes = !direct && new_site_sig != old_callee_sig;
        if (!pairify_ret && !any_i64_arg && !aux_changes) {
            return;
        }
        b.set_insertion_before(inst);
        b.set_loc(data.loc);
        std::vector<ValueId> new_ops;
        for (ValueId op : ops) {
            if (is_i64(func.value_type(op))) {
                Halves h = halves(func, op);
                new_ops.push_back(first_half(h));
                new_ops.push_back(second_half(h));
            } else {
                new_ops.push_back(op);
            }
        }
        ValueId staging;
        if (pairify_ret) {
            staging = b.stack_alloc(8, 4);
            new_ops.push_back(staging);
        }
        uint64_t aux = direct ? data.aux : new_site_sig.index;
        InstId new_call = func.make_inst(
            data.op, pairify_ret ? TypeId{} : data.type, new_ops, aux,
            data.loc, data.flags, data.aux2);
        func.insert_before(inst, new_call);
        if (pairify_ret) {
            ValueId lo =
                b.load(types::I32, b.ptr_add(staging, lo_byte_offset()), 4);
            ValueId hi =
                b.load(types::I32, b.ptr_add(staging, hi_byte_offset()), 4);
            pairs_[data.result.index] = {lo, hi};
        } else if (data.result.is_valid()) {
            func.replace_all_uses(data.result, func.inst(new_call).result);
        }
        func.remove_inst(inst);
        state_.changed = true;
    }

    void rewrite_invoke(Function& func, Builder& b, InstId inst,
                        const InstData& data,
                        const std::vector<ValueId>& ops) {
        bool direct = data.op == Opcode::Invoke;
        SigId old_callee_sig;
        if (direct) {
            auto found = old_sig_.find(static_cast<uint32_t>(data.aux));
            old_callee_sig = found != old_sig_.end()
                ? SigId{found->second}
                : mod_.function(FuncId{static_cast<uint32_t>(data.aux)}).sig();
        } else {
            old_callee_sig = SigId{static_cast<uint32_t>(data.aux)};
        }
        const SigData& old_sig = mod_.types().signature(old_callee_sig);
        if (old_sig.ret_class == RetClass::Scalar && is_i64(old_sig.ret_type)) {
            state_.fail("i64-returning invokes require exception-aware "
                        "pair-result lowering");
            return;
        }
        bool any_i64_arg = false;
        for (ValueId op : ops) {
            any_i64_arg |= is_i64(func.value_type(op));
        }
        SigId new_site_sig = direct ? SigId{} : map_sig(old_callee_sig);
        if (!state_.ok) {
            return;
        }
        bool aux_changes = !direct && new_site_sig != old_callee_sig;
        if (!any_i64_arg && !aux_changes) {
            return;
        }
        std::vector<ValueId> new_ops;
        for (ValueId op : ops) {
            if (is_i64(func.value_type(op))) {
                b.set_insertion_before(inst);
                b.set_loc(data.loc);
                Halves h = halves(func, op);
                new_ops.push_back(first_half(h));
                new_ops.push_back(second_half(h));
            } else {
                new_ops.push_back(op);
            }
        }
        uint64_t aux = direct ? data.aux : new_site_sig.index;
        InstId new_invoke = func.make_inst(data.op, data.type, new_ops, aux,
                                           data.loc, data.flags, data.aux2);
        func.insert_before(inst, new_invoke);
        if (data.result.is_valid()) {
            func.replace_all_uses(data.result, func.inst(new_invoke).result);
        }
        func.remove_inst(inst);
        state_.changed = true;
    }

    void rewrite_switch(Function& func, Builder& b, InstId inst,
                        const InstData& data, const std::vector<ValueId>& ops) {

        BlockCallId default_call{aux_low(data.aux)};
        std::vector<SwitchCase> cases;
        {
            auto table = func.jump_table(aux_high(data.aux));
            cases.assign(table.begin(), table.end());
        }
        b.set_insertion_before(inst);
        b.set_loc(data.loc);
        Halves v = halves(func, ops[0]);
        if (cases.empty()) {
            InstId jump = func.make_inst(Opcode::Jump, TypeId{}, {},
                                         default_call.index, data.loc);
            func.insert_before(inst, jump);
            func.remove_inst(inst);
            state_.changed = true;
            return;
        }
        for (size_t index = 0; index < cases.size(); ++index) {
            ValueId case_lo = func.const_int(
                types::I32, cases[index].value & 0xffffffffu);
            ValueId case_hi =
                func.const_int(types::I32, cases[index].value >> 32);
            ValueId matches = b.iand(b.icmp(IntCond::Eq, v.lo, case_lo),
                                     b.icmp(IntCond::Eq, v.hi, case_hi));
            bool last = index + 1 == cases.size();
            BlockCallId else_call;
            BlockId next_block;
            if (last) {
                else_call = default_call;
            } else {
                next_block = func.create_block({});
                else_call = func.make_block_call(next_block, {});
            }
            const ValueId cond_ops[] = {matches};
            InstId branch = func.make_inst(
                Opcode::BrIf, TypeId{}, cond_ops,
                pack_pair_aux(cases[index].target.index, else_call.index),
                data.loc);
            if (index == 0) {
                func.insert_before(inst, branch);
            } else {
                func.append_inst(b.insertion_block(), branch);
            }
            if (!last) {
                b.set_insertion_point(next_block);
            }
        }
        func.remove_inst(inst);
        state_.changed = true;
    }

    Module& mod_;
    StageState& state_;
    std::unordered_map<uint32_t, uint32_t> sig_map_;
    std::unordered_map<uint32_t, uint32_t> old_sig_;
    std::unordered_map<uint32_t, Halves> pairs_;
};

} // namespace

void run_i64_stage(Module& mod, StageState& state) {
    I64Stage(mod, state).run();
}

} // namespace aburi::air::legalize_detail
