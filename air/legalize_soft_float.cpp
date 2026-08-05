#include "legalize_internal.h"

#include "builder.h"

#include <unordered_map>
#include <vector>

namespace aburi::air::legalize_detail {

namespace {

class SoftFloatStage {
public:
    SoftFloatStage(Module& mod, StageState& state)
        : mod_(mod), state_(state) {}

    void run() {
        uint32_t function_count = mod_.function_count();
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
                run_on_function(func);
                if (!state_.ok) {
                    return;
                }
            }
        }
    }

private:
    bool softened(TypeId type) const {
        const TypeTable& types = mod_.types();
        if (!types.is_valid(type) || !types.is_float(type)) {
            return false;
        }
        FloatKind kind = types.type(type).float_kind;
        return (kind == FloatKind::F32 && state_.config.floats.soften_f32) ||
               (kind == FloatKind::F64 && state_.config.floats.soften_f64);
    }

    TypeId carrier(TypeId type) const {
        return mod_.types().type(type).float_kind == FloatKind::F32
            ? types::I32
            : types::I64;
    }

    SigId map_sig(SigId sig) {
        auto found = sig_map_.find(sig.index);
        if (found != sig_map_.end()) {
            return SigId{found->second};
        }
        const SigData& data = mod_.types().signature(sig);
        SigData out = data;
        bool changed = false;
        switch (data.ret_class) {
            case RetClass::Scalar:
                if (softened(data.ret_type)) {
                    out.ret_type = carrier(data.ret_type);
                    changed = true;
                }
                break;
            case RetClass::Hfa:
                if (softened(data.ret_type)) {
                    state_.fail("soft-float cannot legalize an HFA float "
                                "return (no float registers exist)");
                }
                break;
            case RetClass::Void:
            case RetClass::IntPair:
            case RetClass::IndirectSret:
                break;
        }
        for (SigParam& param : out.params) {
            if (softened(param.type)) {
                param.type = carrier(param.type);
                changed = true;
            }
        }
        SigId mapped = changed ? mod_.types().get_signature(out) : sig;
        sig_map_.emplace(sig.index, mapped.index);
        return mapped;
    }

    FuncId helper_binary(LibcallId id, TypeId carrier_type) {
        SigData sig;
        sig.ret_class = RetClass::Scalar;
        sig.ret_type = carrier_type;
        sig.ret_count = 1;
        sig.params = {{carrier_type}, {carrier_type}};
        return find_or_declare(mod_, libcall_name(state_.config, id), sig);
    }

    FuncId helper_compare(LibcallId id, TypeId carrier_type) {
        SigData sig;
        sig.ret_class = RetClass::Scalar;
        sig.ret_type = types::I32;
        sig.ret_count = 1;
        sig.params = {{carrier_type}, {carrier_type}};
        return find_or_declare(mod_, libcall_name(state_.config, id), sig);
    }

    FuncId helper_unary(LibcallId id, TypeId from, TypeId to) {
        SigData sig;
        sig.ret_class = RetClass::Scalar;
        sig.ret_type = to;
        sig.ret_count = 1;
        sig.params = {{from}};
        return find_or_declare(mod_, libcall_name(state_.config, id), sig);
    }

    void run_on_function(Function& func) {
        erase_value_types(func);
        Builder b(mod_, func);
        for (BlockId block = func.first_block(); block.is_valid();
             block = func.block(block).next) {
            for (InstId inst = func.block(block).first; inst.is_valid();) {
                InstId next = func.inst(inst).next;
                rewrite_inst(func, b, inst);
                if (!state_.ok) {
                    return;
                }
                inst = next;
            }
        }
    }

    void erase_value_types(Function& func) {
        uint32_t value_count = func.value_count();
        for (uint32_t index = 1; index <= value_count; ++index) {
            ValueId id{index};

            ValueData data = func.value(id);
            if (!softened(data.type)) {
                continue;
            }
            state_.changed = true;
            switch (data.kind) {
                case ValueKind::BlockParam:
                case ValueKind::InstResult:
                    func.retype_value(id, carrier(data.type));
                    break;
                case ValueKind::ConstFloat:

                    func.replace_all_uses(
                        id, func.const_int(carrier(data.type), data.payload));
                    break;
                case ValueKind::Undef:
                    func.replace_all_uses(id, func.undef(carrier(data.type)));
                    break;
                default:
                    state_.fail("unexpected float-typed constant kind under "
                                "soft-float legalization");
                    return;
            }
        }
    }

    LibcallId pick32_64(TypeId carrier_type, LibcallId for32, LibcallId for64) {
        return carrier_type == types::I32 ? for32 : for64;
    }

    void rewrite_inst(Function& func, Builder& b, InstId inst) {

        InstData data = func.inst(inst);

        switch (data.op) {
            case Opcode::Fadd:
            case Opcode::Fsub:
            case Opcode::Fmul:
            case Opcode::Fdiv:
            case Opcode::Frem: {
                if (!mod_.types().is_int(data.type)) {
                    return;
                }
                TypeId carrier_type = data.type;
                LibcallId id =
                    data.op == Opcode::Fadd
                        ? pick32_64(carrier_type, LibcallId::AddSF3,
                                    LibcallId::AddDF3)
                    : data.op == Opcode::Fsub
                        ? pick32_64(carrier_type, LibcallId::SubSF3,
                                    LibcallId::SubDF3)
                    : data.op == Opcode::Fmul
                        ? pick32_64(carrier_type, LibcallId::MulSF3,
                                    LibcallId::MulDF3)
                    : data.op == Opcode::Fdiv
                        ? pick32_64(carrier_type, LibcallId::DivSF3,
                                    LibcallId::DivDF3)
                        : pick32_64(carrier_type, LibcallId::FmodF,
                                    LibcallId::Fmod);
                b.set_insertion_before(inst);
                b.set_loc(data.loc);
                auto ops = func.operands(inst);
                const ValueId args[] = {ops[0], ops[1]};
                ValueId result =
                    b.call(helper_binary(id, carrier_type), args);
                func.replace_all_uses(data.result, result);
                func.remove_inst(inst);
                state_.changed = true;
                return;
            }
            case Opcode::Fneg: {
                if (!mod_.types().is_int(data.type)) {
                    return;
                }
                b.set_insertion_before(inst);
                b.set_loc(data.loc);
                ValueId sign = data.type == types::I32
                    ? func.const_int(types::I32, 0x80000000u)
                    : func.const_int(types::I64, uint64_t{1} << 63);
                ValueId result = b.ixor(func.operands(inst)[0], sign);
                func.replace_all_uses(data.result, result);
                func.remove_inst(inst);
                state_.changed = true;
                return;
            }
            case Opcode::Fcmp: {
                auto ops = func.operands(inst);
                TypeId operand_type = func.value_type(ops[0]);
                if (!mod_.types().is_int(operand_type)) {
                    return;
                }
                rewrite_fcmp(func, b, inst, operand_type);
                return;
            }
            case Opcode::Fptrunc:
            case Opcode::Fpext: {
                auto ops = func.operands(inst);
                bool src_soft = mod_.types().is_int(func.value_type(ops[0]));
                bool dst_soft = mod_.types().is_int(data.type);
                if (!src_soft && !dst_soft) {
                    return;
                }
                if (src_soft != dst_soft) {
                    state_.fail("mixed hard/soft float conversion is not "
                                "supported (soften both widths)");
                    return;
                }
                LibcallId id = data.op == Opcode::Fptrunc
                    ? LibcallId::TruncDFSF2
                    : LibcallId::ExtendSFDF2;
                TypeId from = data.op == Opcode::Fptrunc ? types::I64
                                                         : types::I32;
                TypeId to = data.op == Opcode::Fptrunc ? types::I32
                                                       : types::I64;
                b.set_insertion_before(inst);
                b.set_loc(data.loc);
                const ValueId args[] = {ops[0]};
                ValueId result = b.call(helper_unary(id, from, to), args);
                func.replace_all_uses(data.result, result);
                func.remove_inst(inst);
                state_.changed = true;
                return;
            }
            case Opcode::Sitofp:
            case Opcode::Uitofp: {
                if (!mod_.types().is_int(data.type)) {
                    return;
                }
                bool is_signed = data.op == Opcode::Sitofp;
                b.set_insertion_before(inst);
                b.set_loc(data.loc);
                ValueId src = func.operands(inst)[0];
                uint16_t width = mod_.types().int_width(func.value_type(src));
                LibcallId id;
                TypeId from;
                if (width <= 32) {
                    if (width < 32) {
                        src = is_signed ? b.sext(types::I32, src)
                                        : b.zext(types::I32, src);
                    }
                    from = types::I32;
                    id = data.type == types::I32
                        ? (is_signed ? LibcallId::FloatSISF
                                     : LibcallId::FloatUnSISF)
                        : (is_signed ? LibcallId::FloatSIDF
                                     : LibcallId::FloatUnSIDF);
                } else if (width == 64) {
                    from = types::I64;
                    id = data.type == types::I32
                        ? (is_signed ? LibcallId::FloatDISF
                                     : LibcallId::FloatUnDISF)
                        : (is_signed ? LibcallId::FloatDIDF
                                     : LibcallId::FloatUnDIDF);
                } else {
                    state_.fail("int-to-float conversion source wider than 64 "
                                "bits is not supported");
                    return;
                }
                const ValueId args[] = {src};
                ValueId result =
                    b.call(helper_unary(id, from, data.type), args);
                func.replace_all_uses(data.result, result);
                func.remove_inst(inst);
                state_.changed = true;
                return;
            }
            case Opcode::Fptosi:
            case Opcode::Fptoui: {
                auto ops = func.operands(inst);
                TypeId src_type = func.value_type(ops[0]);
                if (!mod_.types().is_int(src_type)) {
                    return;
                }
                bool is_signed = data.op == Opcode::Fptosi;
                uint16_t dst_width = mod_.types().int_width(data.type);
                b.set_insertion_before(inst);
                b.set_loc(data.loc);
                LibcallId id;
                TypeId to;
                if (dst_width <= 32) {
                    to = types::I32;
                    id = src_type == types::I32
                        ? (is_signed ? LibcallId::FixSFSI
                                     : LibcallId::FixUnsSFSI)
                        : (is_signed ? LibcallId::FixDFSI
                                     : LibcallId::FixUnsDFSI);
                } else if (dst_width == 64) {
                    to = types::I64;
                    id = src_type == types::I32
                        ? (is_signed ? LibcallId::FixSFDI
                                     : LibcallId::FixUnsSFDI)
                        : (is_signed ? LibcallId::FixDFDI
                                     : LibcallId::FixUnsDFDI);
                } else {
                    state_.fail("float-to-int conversion destination wider "
                                "than 64 bits is not supported");
                    return;
                }
                const ValueId args[] = {ops[0]};
                ValueId result = b.call(helper_unary(id, src_type, to), args);
                if (dst_width < 32) {
                    result = b.trunc(data.type, result);
                }
                func.replace_all_uses(data.result, result);
                func.remove_inst(inst);
                state_.changed = true;
                return;
            }
            case Opcode::Bitcast: {

                auto ops = func.operands(inst);
                if (data.type == func.value_type(ops[0]) &&
                    mod_.types().is_int(data.type)) {
                    func.replace_all_uses(data.result, ops[0]);
                    func.remove_inst(inst);
                    state_.changed = true;
                }
                return;
            }
            case Opcode::CallIndirect:
            case Opcode::InvokeIndirect: {
                SigId site_sig{static_cast<uint32_t>(data.aux)};
                SigId mapped = map_sig(site_sig);
                if (mapped != site_sig) {
                    func.inst_mut(inst).aux = mapped.index;
                    state_.changed = true;
                }
                return;
            }
            default:
                return;
        }
    }

    void rewrite_fcmp(Function& func, Builder& b, InstId inst,
                      TypeId carrier_type) {
        InstData data = func.inst(inst);
        auto cond = static_cast<FloatCond>(data.aux);
        auto ops = func.operands(inst);
        const ValueId args[] = {ops[0], ops[1]};
        b.set_insertion_before(inst);
        b.set_loc(data.loc);
        ValueId zero = func.const_int(types::I32, 0);
        bool is32 = carrier_type == types::I32;
        auto call2 = [&](LibcallId sf, LibcallId df) {
            return b.call(helper_compare(is32 ? sf : df, carrier_type), args);
        };

        ValueId result;
        switch (cond) {
            case FloatCond::Oeq:
                result = b.icmp(IntCond::Eq,
                                call2(LibcallId::EqSF2, LibcallId::EqDF2), zero);
                break;
            case FloatCond::Une:
                result = b.icmp(IntCond::Ne,
                                call2(LibcallId::NeSF2, LibcallId::NeDF2), zero);
                break;
            case FloatCond::Olt:
                result = b.icmp(IntCond::Slt,
                                call2(LibcallId::LtSF2, LibcallId::LtDF2), zero);
                break;
            case FloatCond::Ole:
                result = b.icmp(IntCond::Sle,
                                call2(LibcallId::LeSF2, LibcallId::LeDF2), zero);
                break;
            case FloatCond::Ogt:
                result = b.icmp(IntCond::Sgt,
                                call2(LibcallId::GtSF2, LibcallId::GtDF2), zero);
                break;
            case FloatCond::Oge:
                result = b.icmp(IntCond::Sge,
                                call2(LibcallId::GeSF2, LibcallId::GeDF2), zero);
                break;
            case FloatCond::Ult:
                result = b.icmp(IntCond::Slt,
                                call2(LibcallId::GeSF2, LibcallId::GeDF2), zero);
                break;
            case FloatCond::Ule:
                result = b.icmp(IntCond::Sle,
                                call2(LibcallId::GtSF2, LibcallId::GtDF2), zero);
                break;
            case FloatCond::Ugt:
                result = b.icmp(IntCond::Sgt,
                                call2(LibcallId::LeSF2, LibcallId::LeDF2), zero);
                break;
            case FloatCond::Uge:
                result = b.icmp(IntCond::Sge,
                                call2(LibcallId::LtSF2, LibcallId::LtDF2), zero);
                break;
            case FloatCond::Ord:
                result = b.icmp(
                    IntCond::Eq,
                    call2(LibcallId::UnordSF2, LibcallId::UnordDF2), zero);
                break;
            case FloatCond::Uno:
                result = b.icmp(
                    IntCond::Ne,
                    call2(LibcallId::UnordSF2, LibcallId::UnordDF2), zero);
                break;
            case FloatCond::One:
                result = b.iand(
                    b.icmp(IntCond::Ne,
                           call2(LibcallId::NeSF2, LibcallId::NeDF2), zero),
                    b.icmp(IntCond::Eq,
                           call2(LibcallId::UnordSF2, LibcallId::UnordDF2),
                           zero));
                break;
            case FloatCond::Ueq:
                result = b.ior(
                    b.icmp(IntCond::Eq,
                           call2(LibcallId::EqSF2, LibcallId::EqDF2), zero),
                    b.icmp(IntCond::Ne,
                           call2(LibcallId::UnordSF2, LibcallId::UnordDF2),
                           zero));
                break;
        }
        func.replace_all_uses(data.result, result);
        func.remove_inst(inst);
        state_.changed = true;
    }

    Module& mod_;
    StageState& state_;
    std::unordered_map<uint32_t, uint32_t> sig_map_;
};

} // namespace

void run_soft_float_stage(Module& mod, StageState& state) {
    SoftFloatStage(mod, state).run();
}

} // namespace aburi::air::legalize_detail
