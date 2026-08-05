#include "isel.h"

#include <cctype>
#include <cstdint>
#include <cstdlib>
#include <set>
#include <span>
#include <string>
#include <unordered_map>
#include <vector>

#include "../common/eh_metadata.h"
#include "../common/inline_asm.h"
#include "../common/symbols.h"
#include "insts.h"
#include "target.h"

namespace aburi::backend::or1k {

namespace {

bool fits_simm16(int64_t v) { return v >= -32768 && v <= 32767; }
bool fits_uimm16(uint64_t v) { return v <= 0xffff; }

class ISel {
public:
    ISel(const air::Module& mod, const air::Function& func,
         uint32_t function_index, MFunction& out,
         std::vector<Diagnostic>& diagnostics)
        : mod_(mod), func_(func), out_(out), diagnostics_(diagnostics) {
        out_.name = target_symbol_name(mod.target(), func.name(),
                                       func.attrs().no_prefix);
        out_.attrs = func.attrs();
        out_.attrs.no_prefix = true;
        out_.linkage = func.linkage();
        out_.index = function_index;
        out_.word_bytes = 4;
    }

    bool run();

private:
    void error(const std::string& message, SrcLoc loc = {}) {
        Diagnostic diag;
        diag.level = DiagnosticLevel::Error;
        diag.message = "air backend: " + message;
        diag.location = loc.isInvalid() ? func_.loc() : loc;
        diagnostics_.push_back(std::move(diag));
        failed_ = true;
    }
    void unsupported(const std::string& what, SrcLoc loc = {}) {
        error("not supported by the or1k backend yet: " + what, loc);
    }
    uint16_t int_width(air::TypeId type) const {
        const air::TypeData& data = mod_.types().type(type);
        if (data.kind == air::TypeKind::Ptr) {
            return 32;
        }
        return data.int_width;
    }
    bool check_scalar(air::TypeId type, SrcLoc loc) {
        const air::TypeData& data = mod_.types().type(type);
        if (data.kind == air::TypeKind::Ptr) {
            return true;
        }
        if (data.kind == air::TypeKind::Int) {
            if (data.int_width > 32) {
                unsupported("integer wider than 32 bits reached the selector "
                            "(legalization gap)", loc);
                return false;
            }
            return true;
        }
        if (data.kind == air::TypeKind::Float) {
            unsupported("floating-point value reached the selector "
                        "(soft-float legalization gap)", loc);
            return false;
        }
        unsupported("non-scalar value", loc);
        return false;
    }

    MBlock& cur() { return out_.blocks[cur_block_]; }
    MOperand vr(uint32_t vreg) { return MOperand::make_reg(MReg::vreg(vreg)); }
    MOperand pr(uint32_t phys) { return MOperand::make_reg(MReg::phys(phys)); }
    uint32_t new_gpr() { return out_.new_vreg(RegClass::Gpr); }

    void emit(Or1kOp o, std::vector<MOperand> operands, uint32_t aux = 0) {
        MInst inst;
        inst.opcode = static_cast<uint16_t>(o);
        inst.aux = aux;
        inst.operands = std::move(operands);
        cur().insts.push_back(std::move(inst));
    }
    uint32_t materialize_int(uint64_t bits) {
        uint32_t value = static_cast<uint32_t>(bits);
        uint32_t vreg = new_gpr();
        int32_t sval = static_cast<int32_t>(value);
        if (fits_simm16(sval)) {
            emit(Or1kOp::Addi, {vr(vreg), pr(R0), MOperand::make_imm(sval)});
            return vreg;
        }
        if ((value & 0xffff) == 0) {
            emit(Or1kOp::Movhi,
                 {vr(vreg), MOperand::make_imm(value >> 16)});
            return vreg;
        }

        emit(Or1kOp::Movhi, {vr(vreg), MOperand::make_imm(value >> 16)});
        uint32_t full = new_gpr();
        emit(Or1kOp::Ori,
             {vr(full), vr(vreg), MOperand::make_imm(value & 0xffff)});
        return full;
    }
    uint32_t materialize_symbol(const std::string& symbol, int64_t addend) {
        uint32_t hi = new_gpr();
        emit(Or1kOp::MovhiHi,
             {vr(hi), MOperand::make_symbol(symbol, SymFlavor::Plain, addend)});
        uint32_t full = new_gpr();
        emit(Or1kOp::OriLo,
             {vr(full), vr(hi),
              MOperand::make_symbol(symbol, SymFlavor::Plain, addend)});
        return full;
    }

    Or1kOp load_op_for(air::TypeId type, bool is_signed) {
        const air::TypeData& data = mod_.types().type(type);
        if (data.kind == air::TypeKind::Ptr) {
            return Or1kOp::Lwz;
        }
        switch (data.int_width) {
            case 8: return is_signed ? Or1kOp::Lbs : Or1kOp::Lbz;
            case 16: return is_signed ? Or1kOp::Lhs : Or1kOp::Lhz;
            default: return Or1kOp::Lwz;
        }
    }
    Or1kOp store_op_for(air::TypeId type) {
        const air::TypeData& data = mod_.types().type(type);
        if (data.kind == air::TypeKind::Ptr) {
            return Or1kOp::Sw;
        }
        switch (data.int_width) {
            case 8: return Or1kOp::Sb;
            case 16: return Or1kOp::Sh;
            default: return Or1kOp::Sw;
        }
    }

    struct Slot {
        uint32_t frame_index;
        air::TypeId type;
    };

    uint32_t use_reg(air::ValueId v, SrcLoc loc) {
        auto cached = block_values_.find(v.index);
        if (cached != block_values_.end()) {
            return cached->second;
        }
        auto frame = frame_addrs_.find(v.index);
        if (frame != frame_addrs_.end()) {
            uint32_t addr = new_gpr();
            emit(Or1kOp::FrameAddr,
                 {vr(addr), MOperand::make_frame(frame->second)});
            block_values_[v.index] = addr;
            return addr;
        }
        const air::ValueData& data = func_.value(v);
        uint32_t vreg = 0;
        switch (data.kind) {
            case air::ValueKind::InstResult:
            case air::ValueKind::BlockParam: {
                auto slot = slots_.find(v.index);
                if (slot == slots_.end()) {
                    error("value used before definition in the fast tier", loc);
                    return new_gpr();
                }
                vreg = new_gpr();
                bool is_signed = false;
                emit(load_op_for(slot->second.type, is_signed),
                     {vr(vreg), MOperand::make_frame(slot->second.frame_index),
                      MOperand::make_imm(0)});
                break;
            }
            case air::ValueKind::ConstInt:
                vreg = materialize_int(data.payload);
                break;
            case air::ValueKind::ConstNull:
            case air::ValueKind::Undef:
                vreg = materialize_int(0);
                break;
            case air::ValueKind::GlobalAddr: {
                const air::GlobalData& g =
                    mod_.global(air::GlobalId{static_cast<uint32_t>(data.payload)});
                if (g.is_thread_local) {
                    unsupported("thread_local address lowering", loc);
                    vreg = new_gpr();
                    break;
                }
                vreg = materialize_symbol(g.name, 0);
                break;
            }
            case air::ValueKind::FuncAddr: {
                const air::Function& f =
                    mod_.function(air::FuncId{static_cast<uint32_t>(data.payload)});
                vreg = materialize_symbol(
                    target_symbol_name(mod_.target(), f.name(),
                                       f.attrs().no_prefix),
                    0);
                break;
            }
            case air::ValueKind::LabelAddr: {

                uint32_t air_block = static_cast<uint32_t>(data.payload);
                auto it = block_map_.find(air_block);
                if (it == block_map_.end()) {
                    unsupported("label address for an unknown block", loc);
                    vreg = new_gpr();
                    break;
                }
                out_.blocks[it->second].address_taken = true;
                std::string sym = ".LBB" + std::to_string(out_.index) + "_" +
                                  std::to_string(it->second);
                uint32_t hi = new_gpr();
                emit(Or1kOp::MovhiHi,
                     {vr(hi), MOperand::make_symbol(sym, SymFlavor::Plain)});
                vreg = new_gpr();
                emit(Or1kOp::OriLo,
                     {vr(vreg), vr(hi),
                      MOperand::make_symbol(sym, SymFlavor::Plain)});
                break;
            }
            default:
                unsupported("value kind in the selector", loc);
                vreg = new_gpr();
                break;
        }
        block_values_[v.index] = vreg;
        return vreg;
    }

    void define(air::ValueId result, uint32_t vreg) {
        block_values_[result.index] = vreg;
        auto slot = slots_.find(result.index);
        if (slot != slots_.end()) {
            emit(store_op_for(slot->second.type),
                 {vr(vreg), MOperand::make_frame(slot->second.frame_index),
                  MOperand::make_imm(0)});
        }
    }

    struct MemRef {
        uint32_t base;
        int64_t disp;
    };
    MemRef address_of(air::ValueId ptr, SrcLoc loc) {

        const air::ValueData& data = func_.value(ptr);
        if (data.kind == air::ValueKind::InstResult &&
            !slots_.count(ptr.index)) {
            air::InstId def{static_cast<uint32_t>(data.payload)};
            const air::InstData& inst = func_.inst(def);
            if (inst.op == air::Opcode::PtrAdd) {
                auto ops = func_.operands(def);
                const air::ValueData& off = func_.value(ops[1]);
                if (off.kind == air::ValueKind::ConstInt &&
                    fits_simm16(static_cast<int32_t>(off.payload))) {
                    return {use_reg(ops[0], loc),
                            static_cast<int32_t>(off.payload)};
                }
            }
        }
        return {use_reg(ptr, loc), 0};
    }
    Or1kOp emit_compare(air::IntCond cond, air::ValueId a, air::ValueId b,
                        SrcLoc loc) {
        uint32_t ra = use_reg(a, loc);
        uint32_t rb = use_reg(b, loc);
        Or1kOp sf;
        switch (cond) {
            case air::IntCond::Eq: sf = Or1kOp::Sfeq; break;
            case air::IntCond::Ne: sf = Or1kOp::Sfne; break;
            case air::IntCond::Slt: sf = Or1kOp::Sflts; break;
            case air::IntCond::Sle: sf = Or1kOp::Sfles; break;
            case air::IntCond::Sgt: sf = Or1kOp::Sfgts; break;
            case air::IntCond::Sge: sf = Or1kOp::Sfges; break;
            case air::IntCond::Ult: sf = Or1kOp::Sfltu; break;
            case air::IntCond::Ule: sf = Or1kOp::Sfleu; break;
            case air::IntCond::Ugt: sf = Or1kOp::Sfgtu; break;
            case air::IntCond::Uge: sf = Or1kOp::Sfgeu; break;
            default: sf = Or1kOp::Sfeq; break;
        }
        emit(sf, {vr(ra), vr(rb)});
        return Or1kOp::Bf;
    }

    void select_inst(air::InstId inst_id);
    void select_terminator(air::InstId inst_id);
    void lower_asm(const air::InstData& inst, air::InstId inst_id);
    void select_call(air::InstId inst_id);
    void select_invoke(air::InstId inst_id);
    void emit_parameter_arrival();
    void emit_edge_stores(air::BlockCallId call, SrcLoc loc);
    void branch_to(air::BlockCallId call, SrcLoc loc, bool with_terminator);
    void emit_eh_label(uint32_t label) {
        emit(Or1kOp::EhLabel, {}, label);
    }
    void call_runtime(const char* name, uint32_t arg_vreg) {
        emit(Or1kOp::Mov, {pr(R3), vr(arg_vreg)});
        emit(Or1kOp::Jal, {MOperand::make_symbol(name, SymFlavor::Plain)});
    }

    const air::Module& mod_;
    const air::Function& func_;
    MFunction& out_;
    std::vector<Diagnostic>& diagnostics_;
    bool failed_ = false;
    EhMetadataBuilder eh_{mod_, func_, out_, diagnostics_, failed_};
    uint32_t cur_block_ = 0;

    std::unordered_map<uint32_t, uint32_t> block_map_;
    std::unordered_map<uint32_t, Slot> slots_;
    std::unordered_map<uint32_t, uint32_t> frame_addrs_;
    std::unordered_map<uint32_t, uint32_t> block_values_;
};

void ISel::emit_edge_stores(air::BlockCallId call, SrcLoc loc) {
    const air::BlockCall& edge = func_.block_call(call);
    auto args = func_.block_call_args(call);
    auto params = func_.block_params(edge.target);
    for (size_t i = 0; i < args.size() && i < params.size(); ++i) {
        auto slot = slots_.find(params[i].index);
        if (slot == slots_.end()) {
            continue;
        }
        uint32_t vreg = use_reg(args[i], loc);
        emit(store_op_for(slot->second.type),
             {vr(vreg), MOperand::make_frame(slot->second.frame_index),
              MOperand::make_imm(0)});
    }
}

void ISel::branch_to(air::BlockCallId call, SrcLoc loc, bool with_terminator) {
    emit_edge_stores(call, loc);
    if (with_terminator) {
        const air::BlockCall& edge = func_.block_call(call);
        emit(Or1kOp::J,
             {MOperand::make_label(block_map_[edge.target.index])});
    }
}

void ISel::select_inst(air::InstId inst_id) {
    const air::InstData& inst = func_.inst(inst_id);
    SrcLoc loc = inst.loc;
    auto ops = func_.operands(inst_id);

    switch (inst.op) {
        case air::Opcode::StackAlloc:

            return;
        case air::Opcode::Iadd:
        case air::Opcode::Isub:
        case air::Opcode::Iand:
        case air::Opcode::Ior:
        case air::Opcode::Ixor:
        case air::Opcode::Imul:
        case air::Opcode::Sdiv:
        case air::Opcode::Udiv: {
            if (!check_scalar(inst.type, loc)) return;
            uint32_t a = use_reg(ops[0], loc);
            uint32_t b = use_reg(ops[1], loc);
            uint32_t d = new_gpr();
            Or1kOp o;
            switch (inst.op) {
                case air::Opcode::Iadd: o = Or1kOp::Add; break;
                case air::Opcode::Isub: o = Or1kOp::Sub; break;
                case air::Opcode::Iand: o = Or1kOp::And; break;
                case air::Opcode::Ior:  o = Or1kOp::Or; break;
                case air::Opcode::Ixor: o = Or1kOp::Xor; break;
                case air::Opcode::Imul: o = Or1kOp::Mul; break;
                case air::Opcode::Sdiv: o = Or1kOp::Div; break;
                default:                o = Or1kOp::Divu; break;
            }
            emit(o, {vr(d), vr(a), vr(b)});
            define(inst.result, d);
            return;
        }
        case air::Opcode::Srem:
        case air::Opcode::Urem: {
            if (!check_scalar(inst.type, loc)) return;

            uint32_t a = use_reg(ops[0], loc);
            uint32_t b = use_reg(ops[1], loc);
            uint32_t q = new_gpr();
            emit(inst.op == air::Opcode::Srem ? Or1kOp::Div : Or1kOp::Divu,
                 {vr(q), vr(a), vr(b)});
            uint32_t m = new_gpr();
            emit(Or1kOp::Mul, {vr(m), vr(q), vr(b)});
            uint32_t d = new_gpr();
            emit(Or1kOp::Sub, {vr(d), vr(a), vr(m)});
            define(inst.result, d);
            return;
        }
        case air::Opcode::Shl:
        case air::Opcode::Lshr:
        case air::Opcode::Ashr: {
            if (!check_scalar(inst.type, loc)) return;
            uint32_t a = use_reg(ops[0], loc);
            const air::ValueData& amt = func_.value(ops[1]);
            uint32_t d = new_gpr();
            Or1kOp reg_op = inst.op == air::Opcode::Shl  ? Or1kOp::Sll
                          : inst.op == air::Opcode::Lshr ? Or1kOp::Srl
                                                         : Or1kOp::Sra;
            Or1kOp imm_op = inst.op == air::Opcode::Shl  ? Or1kOp::Slli
                          : inst.op == air::Opcode::Lshr ? Or1kOp::Srli
                                                         : Or1kOp::Srai;
            if (amt.kind == air::ValueKind::ConstInt) {
                emit(imm_op, {vr(d), vr(a),
                              MOperand::make_imm(amt.payload & 31)});
            } else {
                uint32_t b = use_reg(ops[1], loc);
                emit(reg_op, {vr(d), vr(a), vr(b)});
            }
            define(inst.result, d);
            return;
        }
        case air::Opcode::Load: {
            if (!check_scalar(inst.type, loc)) return;
            MemRef m = address_of(ops[0], loc);
            uint32_t d = new_gpr();
            emit(load_op_for(inst.type, /*is_signed=*/false),
                 {vr(d), vr(m.base), MOperand::make_imm(m.disp)});
            define(inst.result, d);
            return;
        }
        case air::Opcode::Store: {
            uint32_t val = use_reg(ops[0], loc);
            MemRef m = address_of(ops[1], loc);
            emit(store_op_for(func_.value_type(ops[0])),
                 {vr(val), vr(m.base), MOperand::make_imm(m.disp)});
            return;
        }
        case air::Opcode::Trunc: {
            if (!check_scalar(inst.type, loc)) return;
            uint32_t src = use_reg(ops[0], loc);
            uint16_t w = int_width(inst.type);
            uint32_t d = new_gpr();
            if (w >= 32) {
                emit(Or1kOp::Mov, {vr(d), vr(src)});
            } else {
                emit(Or1kOp::Andi,
                     {vr(d), vr(src),
                      MOperand::make_imm((uint64_t{1} << w) - 1)});
            }
            define(inst.result, d);
            return;
        }
        case air::Opcode::Zext: {
            if (!check_scalar(inst.type, loc)) return;
            uint32_t src = use_reg(ops[0], loc);
            uint16_t sw = int_width(func_.value_type(ops[0]));
            uint32_t d = new_gpr();
            if (sw >= 32) {
                emit(Or1kOp::Mov, {vr(d), vr(src)});
            } else {
                emit(Or1kOp::Andi,
                     {vr(d), vr(src),
                      MOperand::make_imm((uint64_t{1} << sw) - 1)});
            }
            define(inst.result, d);
            return;
        }
        case air::Opcode::Sext: {
            if (!check_scalar(inst.type, loc)) return;
            uint32_t src = use_reg(ops[0], loc);
            uint16_t sw = int_width(func_.value_type(ops[0]));
            uint32_t d = new_gpr();
            if (sw >= 32) {
                emit(Or1kOp::Mov, {vr(d), vr(src)});
            } else {

                uint32_t shift = 32 - sw;
                uint32_t up = new_gpr();
                emit(Or1kOp::Slli, {vr(up), vr(src), MOperand::make_imm(shift)});
                emit(Or1kOp::Srai, {vr(d), vr(up), MOperand::make_imm(shift)});
            }
            define(inst.result, d);
            return;
        }
        case air::Opcode::Bitcast:
        case air::Opcode::Ptrtoint:
        case air::Opcode::Inttoptr: {
            if (!check_scalar(inst.type, loc)) return;
            uint32_t src = use_reg(ops[0], loc);
            uint32_t d = new_gpr();
            emit(Or1kOp::Mov, {vr(d), vr(src)});
            define(inst.result, d);
            return;
        }
        case air::Opcode::Bswap: {
            if (!check_scalar(inst.type, loc)) return;

            if (int_width(inst.type) <= 16) {
                uint32_t x = use_reg(ops[0], loc);
                uint32_t lo = new_gpr();
                emit(Or1kOp::Andi, {vr(lo), vr(x), MOperand::make_imm(0xff)});
                uint32_t lo_sh = new_gpr();
                emit(Or1kOp::Slli, {vr(lo_sh), vr(lo), MOperand::make_imm(8)});
                uint32_t hi = new_gpr();
                emit(Or1kOp::Srli, {vr(hi), vr(x), MOperand::make_imm(8)});
                uint32_t hi_m = new_gpr();
                emit(Or1kOp::Andi, {vr(hi_m), vr(hi), MOperand::make_imm(0xff)});
                uint32_t d = new_gpr();
                emit(Or1kOp::Or, {vr(d), vr(lo_sh), vr(hi_m)});
                define(inst.result, d);
                return;
            }
            call_runtime("__bswapsi2", use_reg(ops[0], loc));
            uint32_t d = new_gpr();
            emit(Or1kOp::Mov, {vr(d), pr(RV)});
            define(inst.result, d);
            return;
        }
        case air::Opcode::Clz:
        case air::Opcode::Ctz:
        case air::Opcode::Popcnt: {

            if (!check_scalar(inst.type, loc)) return;
            const char* name = inst.op == air::Opcode::Clz ? "__clzsi2"
                             : inst.op == air::Opcode::Ctz ? "__ctzsi2"
                                                           : "__popcountsi2";
            call_runtime(name, use_reg(ops[0], loc));
            uint32_t d = new_gpr();
            emit(Or1kOp::Mov, {vr(d), pr(RV)});
            define(inst.result, d);
            return;
        }
        case air::Opcode::PtrAdd: {

            uint32_t base = use_reg(ops[0], loc);
            const air::ValueData& off = func_.value(ops[1]);
            uint32_t d = new_gpr();
            if (off.kind == air::ValueKind::ConstInt &&
                fits_simm16(static_cast<int32_t>(off.payload))) {
                emit(Or1kOp::Addi,
                     {vr(d), vr(base),
                      MOperand::make_imm(static_cast<int32_t>(off.payload))});
            } else {
                uint32_t o = use_reg(ops[1], loc);
                emit(Or1kOp::Add, {vr(d), vr(base), vr(o)});
            }
            define(inst.result, d);
            return;
        }
        case air::Opcode::Icmp: {

            auto cond = static_cast<air::IntCond>(inst.aux);
            Or1kOp taken = emit_compare(cond, ops[0], ops[1], loc);
            uint32_t d = new_gpr();
            emit(Or1kOp::SetBool, {vr(d)},
                 taken == Or1kOp::Bf ? 0u : 1u);
            define(inst.result, d);
            return;
        }
        case air::Opcode::Select: {
            if (!check_scalar(inst.type, loc)) return;

            uint32_t c = use_reg(ops[0], loc);
            uint32_t bit = new_gpr();
            emit(Or1kOp::Andi, {vr(bit), vr(c), MOperand::make_imm(1)});
            uint32_t mask = new_gpr();
            emit(Or1kOp::Sub, {vr(mask), pr(R0), vr(bit)});
            uint32_t a = use_reg(ops[1], loc);
            uint32_t b = use_reg(ops[2], loc);
            uint32_t ax = new_gpr();
            emit(Or1kOp::And, {vr(ax), vr(a), vr(mask)});
            uint32_t notmask = new_gpr();
            emit(Or1kOp::Xori, {vr(notmask), vr(mask), MOperand::make_imm(-1)});
            uint32_t bx = new_gpr();
            emit(Or1kOp::And, {vr(bx), vr(b), vr(notmask)});
            uint32_t d = new_gpr();
            emit(Or1kOp::Or, {vr(d), vr(ax), vr(bx)});
            define(inst.result, d);
            return;
        }
        case air::Opcode::VaStart: {

            out_.needs_frame_pointer = true;
            uint32_t list_ptr = use_reg(ops[0], loc);
            uint32_t addr = new_gpr();
            emit(Or1kOp::Addi,
                 {vr(addr), pr(FP),
                  MOperand::make_imm(static_cast<int64_t>(
                      out_.named_stack_bytes))});
            emit(Or1kOp::Sw, {vr(addr), vr(list_ptr), MOperand::make_imm(0)});
            return;
        }
        case air::Opcode::Memcpy:
        case air::Opcode::Memmove:
        case air::Opcode::Memset: {

            const char* name = inst.op == air::Opcode::Memcpy   ? "memcpy"
                             : inst.op == air::Opcode::Memmove   ? "memmove"
                                                                 : "memset";
            uint32_t a0 = use_reg(ops[0], loc);
            uint32_t a1 = use_reg(ops[1], loc);
            uint32_t a2 = use_reg(ops[2], loc);
            emit(Or1kOp::Mov, {pr(R3), vr(a0)});
            emit(Or1kOp::Mov, {pr(R3 + 1), vr(a1)});
            emit(Or1kOp::Mov, {pr(R3 + 2), vr(a2)});
            emit(Or1kOp::Jal,
                 {MOperand::make_symbol(name, SymFlavor::Plain)});
            return;
        }
        case air::Opcode::Call:
        case air::Opcode::CallIndirect:
            select_call(inst_id);
            return;
        case air::Opcode::EhAllocException: {
            uint32_t size = materialize_int(inst.aux);
            emit(Or1kOp::Mov, {pr(R3), vr(size)});
            emit(Or1kOp::Jal, {MOperand::make_symbol(
                                  "__cxa_allocate_exception", SymFlavor::Plain)});
            uint32_t d = new_gpr();
            emit(Or1kOp::Mov, {vr(d), pr(RV)});
            define(inst.result, d);
            return;
        }
        case air::Opcode::EhLandingPad: {

            uint32_t d = new_gpr();
            emit(Or1kOp::Mov, {vr(d), pr(25)});
            define(inst.result, d);
            return;
        }
        case air::Opcode::EhSelector: {

            uint32_t d = new_gpr();
            emit(Or1kOp::Mov, {vr(d), pr(27)});
            define(inst.result, d);
            return;
        }
        case air::Opcode::EhTypeId: {
            uint32_t filter = eh_.typeinfo_filter_for_value(ops[0], loc);
            define(inst.result, materialize_int(filter));
            return;
        }
        case air::Opcode::CatchBegin: {
            call_runtime("__cxa_begin_catch", use_reg(ops[0], loc));
            uint32_t d = new_gpr();
            emit(Or1kOp::Mov, {vr(d), pr(RV)});
            define(inst.result, d);
            return;
        }
        case air::Opcode::CatchEnd:
            emit(Or1kOp::Jal, {MOperand::make_symbol("__cxa_end_catch",
                                                     SymFlavor::Plain)});
            return;
        case air::Opcode::InlineAsm:
            lower_asm(inst, inst_id);
            return;
        default:
            unsupported(std::string("opcode ") +
                            std::string(air::opcode_mnemonic(inst.op)),
                        loc);
            return;
    }
}

void ISel::lower_asm(const air::InstData& inst, air::InstId inst_id) {
    SrcLoc loc = inst.loc;
    std::span<const air::ValueId> ops = func_.operands(inst_id);
    const air::AsmPayload& payload =
        mod_.asm_payload(static_cast<uint32_t>(inst.aux));
    size_t n = payload.constraints.size();
    if (ops.size() != n || payload.operand_types.size() != n) {
        error("inline asm operand metadata is inconsistent", loc);
        return;
    }

    struct OpInfo {
        AsmOperandRole role = AsmOperandRole::Input;
        AsmOperandKind kind = AsmOperandKind::Register;
        uint32_t phys = 0;
        bool has_phys = false;
        air::TypeId type;
    };
    std::vector<OpInfo> info(n);
    std::set<uint32_t> claimed;

    for (const std::string& clobber : payload.clobbers) {
        if (clobber == "memory" || clobber == "cc") {
            continue;
        }
        if (clobber.size() < 2 || clobber[0] != 'r') {
            continue;
        }
        bool digits = true;
        for (size_t i = 1; i < clobber.size(); ++i) {
            digits = digits &&
                     std::isdigit(static_cast<unsigned char>(clobber[i]));
        }
        if (!digits) {
            continue;
        }
        uint32_t reg = static_cast<uint32_t>(std::atoi(clobber.c_str() + 1));
        if (reg > 31) {
            continue;
        }
        if (is_callee_saved_reg(reg) || reg == 0 || reg == 1 || reg == 2) {
            unsupported("clobbering register '" + clobber + "' in inline asm",
                        loc);
            return;
        }
        claimed.insert(reg);
    }

    for (size_t i = 0; i < n; ++i) {
        AsmConstraint c = parse_asm_constraint(payload.constraints[i]);
        if (!c.ok) {
            unsupported(c.error, loc);
            return;
        }
        info[i].role = c.role;
        info[i].type = payload.operand_types[i];
        info[i].kind = c.kind;
        if (c.kind == AsmOperandKind::Immediate) {
            continue;
        }
        if (c.kind != AsmOperandKind::Register || c.letter != 'r') {
            unsupported("this asm operand constraint on or1k", loc);
            return;
        }
        if (mod_.types().is_float(info[i].type)) {
            unsupported("floating-point inline asm operands on or1k", loc);
            return;
        }
    }

    static const uint32_t kPool[] = {R3, 4, 5, 6, 7, R8};
    size_t next = 0;
    for (size_t i = 0; i < n; ++i) {
        if (info[i].kind != AsmOperandKind::Register) {
            continue;
        }
        bool assigned = false;
        while (next < std::size(kPool)) {
            uint32_t candidate = kPool[next++];
            if (claimed.insert(candidate).second) {
                info[i].phys = candidate;
                info[i].has_phys = true;
                assigned = true;
                break;
            }
        }
        if (!assigned) {
            unsupported("inline asm needs more registers than the backend "
                        "allocates for it", loc);
            return;
        }
    }

    std::vector<uint32_t> src(n, 0);
    std::vector<int64_t> imm(n, 0);
    for (size_t i = 0; i < n; ++i) {
        if (info[i].kind == AsmOperandKind::Immediate) {
            const air::ValueData& data = func_.value(ops[i]);
            if (data.kind != air::ValueKind::ConstInt) {
                error("asm operand for an 'i' constraint is not a "
                      "compile-time constant", loc);
                return;
            }
            imm[i] = static_cast<int64_t>(data.payload);
            continue;
        }
        src[i] = use_reg(ops[i], loc);
    }

    for (size_t i = 0; i < n; ++i) {
        if (!info[i].has_phys) {
            continue;
        }
        if (info[i].role == AsmOperandRole::ReadWriteOutput) {
            emit(load_op_for(info[i].type, /*is_signed=*/false),
                 {pr(info[i].phys), vr(src[i]), MOperand::make_imm(0)});
        } else if (info[i].role == AsmOperandRole::Input) {
            emit(Or1kOp::Mov, {pr(info[i].phys), vr(src[i])});
        }
    }

    const std::string& tmpl = payload.text;
    std::string resolved;
    bool template_error = false;
    for (size_t i = 0; i < tmpl.size() && !template_error; ++i) {
        if (tmpl[i] != '%') {
            resolved += tmpl[i];
            continue;
        }
        if (i + 1 >= tmpl.size()) {
            template_error = true;
            break;
        }
        if (tmpl[i + 1] == '%') {
            resolved += '%';
            ++i;
            continue;
        }
        size_t j = i + 1;
        if (!std::isdigit(static_cast<unsigned char>(tmpl[j]))) {
            template_error = true;
            break;
        }
        size_t number = 0;
        while (j < tmpl.size() &&
               std::isdigit(static_cast<unsigned char>(tmpl[j]))) {
            number = number * 10 + static_cast<size_t>(tmpl[j] - '0');
            ++j;
        }
        if (number >= n) {
            template_error = true;
            break;
        }
        if (info[number].kind == AsmOperandKind::Immediate) {
            resolved += std::to_string(imm[number]);
        } else {
            resolved += or1k_gpr_name(info[number].phys);
        }
        i = j - 1;
    }
    if (template_error) {
        unsupported("this inline asm template operand form", loc);
        return;
    }

    out_.asm_texts.push_back("\t" + resolved + "\n");
    emit(Or1kOp::AsmBlock, {},
         static_cast<uint32_t>(out_.asm_texts.size()) - 1);

    std::vector<uint32_t> captured(n, 0);
    for (size_t i = 0; i < n; ++i) {
        if (info[i].has_phys && info[i].role != AsmOperandRole::Input) {
            captured[i] = new_gpr();
            emit(Or1kOp::Mov, {vr(captured[i]), pr(info[i].phys)});
        }
    }
    for (size_t i = 0; i < n; ++i) {
        if (info[i].has_phys && info[i].role != AsmOperandRole::Input) {
            emit(store_op_for(info[i].type),
                 {vr(captured[i]), vr(src[i]), MOperand::make_imm(0)});
        }
    }
}

void ISel::select_terminator(air::InstId inst_id) {
    const air::InstData& inst = func_.inst(inst_id);
    SrcLoc loc = inst.loc;
    auto ops = func_.operands(inst_id);
    switch (inst.op) {
        case air::Opcode::Ret: {
            const air::SigData& sig = mod_.types().signature(func_.sig());
            if (sig.ret_class == air::RetClass::Scalar && !ops.empty()) {
                uint32_t v = use_reg(ops[0], loc);
                emit(Or1kOp::Mov, {pr(RV), vr(v)});
            } else if (sig.ret_class == air::RetClass::IntPair && !ops.empty()) {

                uint32_t ptr = use_reg(ops[0], loc);
                emit(Or1kOp::Lwz, {pr(RV), vr(ptr), MOperand::make_imm(0)});
                emit(Or1kOp::Lwz, {pr(R12), vr(ptr), MOperand::make_imm(4)});
            }
            emit(Or1kOp::EpilogueRet, {});
            return;
        }
        case air::Opcode::Jump: {
            air::BlockCallId call{air::aux_low(inst.aux)};
            branch_to(call, loc, /*with_terminator=*/true);
            return;
        }
        case air::Opcode::BrIf: {
            air::BlockCallId then_call{air::aux_low(inst.aux)};
            air::BlockCallId else_call{air::aux_high(inst.aux)};

            const air::ValueData& cond = func_.value(ops[0]);
            Or1kOp taken = Or1kOp::Bf;
            bool fused = false;
            if (cond.kind == air::ValueKind::InstResult &&
                !block_values_.count(ops[0].index)) {
                air::InstId def{static_cast<uint32_t>(cond.payload)};
                const air::InstData& cmp = func_.inst(def);
                if (cmp.op == air::Opcode::Icmp) {
                    auto cops = func_.operands(def);
                    taken = emit_compare(static_cast<air::IntCond>(cmp.aux),
                                         cops[0], cops[1], loc);
                    fused = true;
                }
            }
            if (!fused) {
                uint32_t c = use_reg(ops[0], loc);
                emit(Or1kOp::Sfnei, {vr(c), MOperand::make_imm(0)});
                taken = Or1kOp::Bf;
            }

            const air::BlockCall& then_edge = func_.block_call(then_call);

            emit_edge_stores(then_call, loc);
            emit(taken,
                 {MOperand::make_label(block_map_[then_edge.target.index])});
            branch_to(else_call, loc, /*with_terminator=*/true);
            return;
        }
        case air::Opcode::Switch: {
            air::BlockCallId default_call{air::aux_low(inst.aux)};
            uint32_t table_idx = air::aux_high(inst.aux);
            std::vector<air::SwitchCase> cases;
            {
                auto table = func_.jump_table(table_idx);
                cases.assign(table.begin(), table.end());
            }
            uint32_t v = use_reg(ops[0], loc);

            std::vector<uint32_t> landings;
            landings.reserve(cases.size());
            for (const air::SwitchCase& c : cases) {
                uint32_t landing = static_cast<uint32_t>(out_.blocks.size());
                out_.blocks.push_back({});
                landings.push_back(landing);
                int64_t val = static_cast<int64_t>(c.value);
                if (fits_simm16(val)) {
                    emit(Or1kOp::Sfeqi, {vr(v), MOperand::make_imm(val)});
                } else {
                    uint32_t cv = materialize_int(c.value);
                    emit(Or1kOp::Sfeq, {vr(v), vr(cv)});
                }
                emit(Or1kOp::Bf, {MOperand::make_label(landing)});
            }

            branch_to(default_call, loc, /*with_terminator=*/true);

            uint32_t switch_block = cur_block_;
            for (size_t i = 0; i < cases.size(); ++i) {
                cur_block_ = landings[i];
                block_values_.clear();
                const air::BlockCall& edge = func_.block_call(cases[i].target);
                branch_to(cases[i].target, loc, /*with_terminator=*/false);
                emit(Or1kOp::J,
                     {MOperand::make_label(block_map_[edge.target.index])});
            }
            cur_block_ = switch_block;
            return;
        }

        case air::Opcode::Throw: {
            uint32_t exception = use_reg(ops[0], loc);
            uint32_t typeinfo = use_reg(ops[1], loc);
            uint32_t destructor = ops.size() > 2 ? use_reg(ops[2], loc)
                                                 : materialize_int(0);
            emit(Or1kOp::Mov, {pr(R3), vr(exception)});
            emit(Or1kOp::Mov, {pr(R3 + 1), vr(typeinfo)});
            emit(Or1kOp::Mov, {pr(R3 + 2), vr(destructor)});
            emit(Or1kOp::Jal,
                 {MOperand::make_symbol("__cxa_throw", SymFlavor::Plain)});
            emit(Or1kOp::EpilogueRet, {});
            return;
        }
        case air::Opcode::Rethrow:
            emit(Or1kOp::Jal,
                 {MOperand::make_symbol("__cxa_rethrow", SymFlavor::Plain)});
            emit(Or1kOp::EpilogueRet, {});
            return;
        case air::Opcode::Resume: {
            uint32_t exception = use_reg(ops[0], loc);
            emit(Or1kOp::Mov, {pr(R3), vr(exception)});
            emit(Or1kOp::Jal,
                 {MOperand::make_symbol("_Unwind_Resume", SymFlavor::Plain)});
            emit(Or1kOp::EpilogueRet, {});
            return;
        }
        case air::Opcode::Invoke:
        case air::Opcode::InvokeIndirect:
            select_invoke(inst_id);
            return;
        case air::Opcode::BrIndirect: {

            uint32_t target = use_reg(ops[0], loc);
            emit(Or1kOp::Jr, {vr(target)});
            return;
        }
        case air::Opcode::Unreachable:
            emit(Or1kOp::EpilogueRet, {});
            return;
        default:
            unsupported(std::string("terminator ") +
                            std::string(air::opcode_mnemonic(inst.op)),
                        loc);
            return;
    }
}

void ISel::select_call(air::InstId inst_id) {
    const air::InstData& inst = func_.inst(inst_id);
    SrcLoc loc = inst.loc;
    auto ops = func_.operands(inst_id);
    bool indirect = inst.op == air::Opcode::CallIndirect ||
                    inst.op == air::Opcode::InvokeIndirect;

    air::SigId sig_id =
        indirect ? air::SigId{static_cast<uint32_t>(inst.aux)}
                 : mod_.function(air::FuncId{static_cast<uint32_t>(inst.aux)})
                       .sig();
    const air::SigData& sig = mod_.types().signature(sig_id);

    size_t first_arg = indirect ? 1 : 0;
    uint32_t callee_reg = 0;
    if (indirect) {
        callee_reg = use_reg(ops[0], loc);
    }

    bool pair_return = sig.ret_class == air::RetClass::IntPair;
    size_t arg_end = ops.size();
    uint32_t dest_ptr = 0;
    bool has_dest = false;
    if (pair_return && arg_end > first_arg) {
        dest_ptr = use_reg(ops[arg_end - 1], loc);
        has_dest = true;
        --arg_end;
    }

    std::vector<std::pair<uint32_t, uint32_t>> reg_moves;
    uint32_t next_reg = R3;
    uint32_t stack_off = 0;
    for (size_t i = first_arg; i < arg_end; ++i) {
        size_t arg_index = i - first_arg;
        bool is_fixed =
            !sig.is_variadic || arg_index < sig.fixed_param_count;
        uint32_t vreg = use_reg(ops[i], loc);
        if (is_fixed && next_reg <= R8) {
            reg_moves.emplace_back(next_reg++, vreg);
        } else {
            emit(Or1kOp::Sw,
                 {vr(vreg), pr(SP), MOperand::make_imm(stack_off)});
            stack_off += 4;
        }
    }
    if (stack_off > out_.max_outgoing_bytes) {
        out_.max_outgoing_bytes = stack_off;
    }

    for (auto [phys, vreg] : reg_moves) {
        emit(Or1kOp::Mov, {pr(phys), vr(vreg)});
    }

    if (indirect) {
        emit(Or1kOp::Jalr, {vr(callee_reg)});
    } else {
        const air::Function& callee =
            mod_.function(air::FuncId{static_cast<uint32_t>(inst.aux)});
        emit(Or1kOp::Jal,
             {MOperand::make_symbol(
                 target_symbol_name(mod_.target(), callee.name(),
                                    callee.attrs().no_prefix),
                 SymFlavor::Plain)});
    }

    if (sig.ret_class == air::RetClass::Scalar && inst.result.is_valid()) {
        uint32_t d = new_gpr();
        emit(Or1kOp::Mov, {vr(d), pr(RV)});
        define(inst.result, d);
    } else if (pair_return && has_dest) {

        uint32_t hi = new_gpr();
        emit(Or1kOp::Mov, {vr(hi), pr(RV)});
        uint32_t lo = new_gpr();
        emit(Or1kOp::Mov, {vr(lo), pr(R12)});
        emit(Or1kOp::Sw, {vr(hi), vr(dest_ptr), MOperand::make_imm(0)});
        emit(Or1kOp::Sw, {vr(lo), vr(dest_ptr), MOperand::make_imm(4)});
    }
}

void ISel::select_invoke(air::InstId inst_id) {
    const air::InstData& inst = func_.inst(inst_id);
    SrcLoc loc = inst.loc;
    air::BlockCallId unwind{air::aux_high(inst.aux2)};
    uint32_t landing_pad =
        block_map_.at(func_.block_call(unwind).target.index);
    uint32_t begin_label = out_.new_eh_label();
    uint32_t end_label = out_.new_eh_label();
    out_.eh_call_sites.push_back(
        MEhCallSite{begin_label, end_label, landing_pad,
                     eh_.action_for_block(landing_pad)});

    emit_eh_label(begin_label);
    select_call(inst_id);
    emit_eh_label(end_label);
    if (failed_) {
        return;
    }
    air::BlockCallId normal{air::aux_low(inst.aux2)};
    emit_edge_stores(normal, loc);
    uint32_t target = block_map_.at(func_.block_call(normal).target.index);
    emit(Or1kOp::J, {MOperand::make_label(target)});
}

void ISel::emit_parameter_arrival() {
    const air::SigData& sig = mod_.types().signature(func_.sig());
    auto params = func_.block_params(func_.entry_block());
    uint32_t next_reg = R3;
    int64_t stack_off = 0;
    for (size_t i = 0; i < params.size() && i < sig.params.size(); ++i) {
        auto slot = slots_.find(params[i].index);
        air::TypeId type = func_.value_type(params[i]);
        if (next_reg <= R8) {
            if (slot != slots_.end()) {
                emit(store_op_for(type),
                     {pr(next_reg),
                      MOperand::make_frame(slot->second.frame_index),
                      MOperand::make_imm(0)});
            }
            ++next_reg;
        } else {

            uint32_t tmp = new_gpr();
            emit(Or1kOp::Lwz, {vr(tmp), pr(FP), MOperand::make_imm(stack_off)});
            if (slot != slots_.end()) {
                emit(store_op_for(type),
                     {vr(tmp),
                      MOperand::make_frame(slot->second.frame_index),
                      MOperand::make_imm(0)});
            }
            stack_off += 4;
        }
    }
    out_.named_stack_bytes = static_cast<uint32_t>(stack_off);
}

bool ISel::run() {
    std::vector<air::BlockId> layout;
    for (air::BlockId block = func_.first_block(); block.is_valid();
         block = func_.block(block).next) {
        layout.push_back(block);
    }
    out_.blocks.resize(layout.size());
    for (size_t i = 0; i < layout.size(); ++i) {
        block_map_[layout[i].index] = static_cast<uint32_t>(i);
    }
    eh_.build(layout, block_map_);

    auto def_block_of = [&](air::ValueId v) -> uint32_t {
        const air::ValueData& data = func_.value(v);
        if (data.kind == air::ValueKind::InstResult) {
            return func_.inst(air::InstId{static_cast<uint32_t>(data.payload)})
                .block.index;
        }
        if (data.kind == air::ValueKind::BlockParam) {
            return static_cast<uint32_t>(data.payload);
        }
        return 0;
    };
    auto note_slot = [&](air::ValueId v) {
        if (slots_.count(v.index)) {
            return;
        }
        air::TypeId type = func_.value_type(v);
        slots_[v.index] = Slot{out_.new_frame_object(4, 4), type};
    };

    for (air::BlockId block_id : layout) {
        for (air::ValueId param : func_.block_params(block_id)) {
            note_slot(param);
        }
        const air::BlockData& block = func_.block(block_id);
        for (air::InstId inst_id = block.first; inst_id.is_valid();
             inst_id = func_.inst(inst_id).next) {
            const air::InstData& inst = func_.inst(inst_id);
            if (inst.op == air::Opcode::StackAlloc) {
                uint64_t size = air::stack_alloc_size(inst.aux);
                uint32_t align = 1u << air::stack_alloc_align_log2(inst.aux);
                frame_addrs_[inst.result.index] =
                    out_.new_frame_object(size ? size : 1, align);
            }
            if (inst.op == air::Opcode::StackAllocDyn ||
                inst.op == air::Opcode::StackSave ||
                inst.op == air::Opcode::StackRestore) {
                out_.has_dynamic_stack = true;
            }
            auto note_use = [&](air::ValueId used) {
                const air::ValueData& data = func_.value(used);
                if (data.kind != air::ValueKind::InstResult &&
                    data.kind != air::ValueKind::BlockParam) {
                    return;
                }
                if (frame_addrs_.count(used.index)) {
                    return;
                }
                if (def_block_of(used) != block_id.index) {
                    note_slot(used);
                }
            };
            for (air::ValueId used : func_.operands(inst_id)) {
                note_use(used);
            }
            std::vector<air::BlockCallId> edges;
            func_.successors(inst_id, edges);
            for (air::BlockCallId edge : edges) {
                for (air::ValueId used : func_.block_call_args(edge)) {
                    note_use(used);
                }
            }
        }
    }

    for (air::BlockId block_id : layout) {
        cur_block_ = block_map_[block_id.index];
        block_values_.clear();

        if (block_id == func_.entry_block()) {
            emit_parameter_arrival();
        }
        const air::BlockData& block = func_.block(block_id);
        for (air::InstId inst_id = block.first; inst_id.is_valid();
             inst_id = func_.inst(inst_id).next) {
            const air::InstData& inst = func_.inst(inst_id);
            bool is_term = inst.op == air::Opcode::Jump ||
                           inst.op == air::Opcode::BrIf ||
                           inst.op == air::Opcode::Switch ||
                           inst.op == air::Opcode::BrIndirect ||
                           inst.op == air::Opcode::Ret ||
                           inst.op == air::Opcode::Unreachable ||
                           inst.op == air::Opcode::Throw ||
                           inst.op == air::Opcode::Rethrow ||
                           inst.op == air::Opcode::Resume ||
                           inst.op == air::Opcode::Invoke ||
                           inst.op == air::Opcode::InvokeIndirect;
            if (is_term) {
                select_terminator(inst_id);
            } else {
                select_inst(inst_id);
            }
            if (failed_) {
                return false;
            }
        }
    }
    return !failed_;
}

} // namespace

bool select_function(const air::Module& module, const air::Function& function,
                     uint32_t function_index, MFunction& out,
                     std::vector<Diagnostic>& diagnostics, int opt_level) {
    (void)opt_level;
    ISel isel(module, function, function_index, out, diagnostics);
    return isel.run();
}

} // namespace aburi::backend::or1k
