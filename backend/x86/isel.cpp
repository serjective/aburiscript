#include "isel.h"

#include <algorithm>
#include <cctype>
#include <iterator>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

#include "insts.h"
#include "target.h"
#include "../common/eh_metadata.h"
#include "../common/inline_asm.h"
#include "../common/symbols.h"

namespace aburi::backend::x86 {

namespace {

uint16_t op(X86Op o) { return static_cast<uint16_t>(o); }

std::string sym_name(const TargetInfo& target, const std::string& name,
                     bool no_prefix) {
    return target_symbol_name(target, name, no_prefix);
}

constexpr uint32_t kGprArgs[6] = {RDI, RSI, RDX, RCX, R8, R9};

class ISel {
public:
    ISel(const air::Module& mod, const air::Function& func,
         uint32_t function_index, MFunction& out,
         std::vector<Diagnostic>& diagnostics, int opt_level)
        : mod_(mod), func_(func), out_(out), diagnostics_(diagnostics),
          opt_(opt_level >= 1) {
        out_.name = sym_name(mod.target(), func.name(), func.attrs().no_prefix);
        out_.attrs = func.attrs();
        out_.attrs.no_prefix = true;
        out_.linkage = func.linkage();
        out_.index = function_index;
        out_.legacy32 = is_legacy32(mod.target());
        legacy32_ = out_.legacy32;
        out_.word_bytes = legacy32_ ? 4 : 8;
        real_mode_ = mod.target().real_mode_16;
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
        error("not supported by the x86-64 backend yet: " + what, loc);
    }

    bool is_fp_type(air::TypeId type) const { return mod_.types().is_float(type); }
    bool is_f128(air::TypeId type) const {
        const air::TypeData& data = mod_.types().type(type);
        return data.kind == air::TypeKind::Float &&
               data.float_kind == air::FloatKind::F128;
    }
    bool is_f80(air::TypeId type) const {
        const air::TypeData& data = mod_.types().type(type);
        return data.kind == air::TypeKind::Float &&
               data.float_kind == air::FloatKind::F80;
    }
    bool is_wide(air::TypeId type) const {
        const air::TypeData& data = mod_.types().type(type);
        if (data.kind == air::TypeKind::Ptr) {
            return !legacy32_;
        }
        if (data.kind == air::TypeKind::Int) {
            return data.int_width > 32;
        }
        if (data.kind == air::TypeKind::Float) {
            return data.float_kind == air::FloatKind::F64;
        }
        return false;
    }
    uint16_t int_width(air::TypeId type) const {
        return mod_.types().type(type).int_width;
    }
    uint64_t scalar_size(air::TypeId type) const {
        const air::TypeData& data = mod_.types().type(type);
        if (data.kind == air::TypeKind::Ptr) {
            return legacy32_ ? 4 : 8;
        }
        if (data.kind == air::TypeKind::Int) {
            return std::max<uint64_t>(1, data.int_width / 8);
        }
        if (data.kind == air::TypeKind::Float) {
            switch (data.float_kind) {
                case air::FloatKind::F32: return 4;
                case air::FloatKind::F64: return 8;
                case air::FloatKind::F128: return 16;
                case air::FloatKind::F80: return 16;
            }
        }
        return 8;
    }
    bool check_scalar(air::TypeId type, SrcLoc loc) {
        const air::TypeData& data = mod_.types().type(type);
        if (data.kind == air::TypeKind::Int && data.int_width == 128) {
            unsupported("128-bit integers", loc);
            return false;
        }

        if (legacy32_ && data.kind == air::TypeKind::Int &&
            data.int_width == 64) {
            unsupported("64-bit integers in 32-bit mode", loc);
            return false;
        }
        if (is_f128(type)) {
            unsupported("IEEE-quad long double", loc);
            return false;
        }

        if (real_mode_ && is_fp_type(type)) {
            unsupported("floating point in 16-bit real mode", loc);
            return false;
        }
        return true;
    }
    MBlock& cur() { return out_.blocks[cur_block_]; }
    void emit(X86Op o, std::vector<MOperand> operands, uint32_t aux = 0) {
        MInst inst;
        inst.opcode = op(o);
        inst.aux = aux;
        inst.operands = std::move(operands);
        cur().insts.push_back(std::move(inst));
    }
    void emit_eh_label(uint32_t label) { emit(X86Op::EhLabel, {}, label); }
    uint32_t new_gpr() { return out_.new_vreg(RegClass::Gpr); }
    uint32_t new_fpr() { return out_.new_vreg(RegClass::Fpr); }
    uint32_t new_reg_for(air::TypeId type) {
        if (is_f128(type) || is_f80(type)) {
            return out_.new_vreg(RegClass::Fpr128);
        }
        return is_fp_type(type) ? new_fpr() : new_gpr();
    }
    static MOperand vr(uint32_t vreg) { return MOperand::make_reg(MReg::vreg(vreg)); }
    static MOperand pr(uint32_t phys) { return MOperand::make_reg(MReg::phys(phys)); }

    struct Slot {
        uint32_t frame_index = 0;
        air::TypeId type;
    };

    bool has_frame_addr(air::ValueId v) const {
        return frame_addrs_.contains(v.index);
    }
    uint32_t use_reg(air::ValueId v, SrcLoc loc);
    MOperand mem_base(air::ValueId v, SrcLoc loc);
    void define(air::ValueId result, uint32_t vreg, SrcLoc loc);

    uint32_t materialize_int(uint64_t bits, bool wide);
    uint32_t materialize_symbol_addr(const std::string& symbol, bool direct);
    uint32_t materialize_tls_addr(const std::string& symbol, SrcLoc loc);
    uint32_t materialize_fp_bits(uint64_t bits, bool wide);
    uint32_t materialize_f80_bits(uint64_t lo, uint64_t hi);

    X86Op load_op_for(air::TypeId type) const;
    X86Op store_op_for(air::TypeId type) const;
    void emit_move(uint32_t dest_vreg_or_phys, bool dest_phys, uint32_t src,
                   air::TypeId type);
    uint32_t two_address_result(uint32_t lhs, bool wide, bool fp);
    uint32_t setcc_result(Cond cond);
    uint32_t f80_spill(uint32_t vreg);
    void f80_fld(uint32_t slot);
    uint32_t f80_pop_result();
    void fp_push_st0(uint32_t xmm, air::TypeId type);
    uint32_t fp_pop_st0(air::TypeId type);

    void store_to_slot(uint32_t vreg, const Slot& slot);
    void emit_edge_stores(air::BlockCallId call, SrcLoc loc);
    uint32_t edge_target(air::BlockCallId call, SrcLoc loc);

    uint32_t canonical_vreg(air::ValueId v);
    void emit_copy(uint32_t dest_vreg, uint32_t src_vreg);
    void emit_parallel_copies(air::BlockCallId call, SrcLoc loc);
    void record_successors();
    void start_dead_block() {
        out_.blocks.emplace_back();
        cur_block_ = static_cast<uint32_t>(out_.blocks.size()) - 1;
        block_values_.clear();
    }
    bool legacy_i64(air::TypeId type) const {

        if (!legacy32_ || !mod_.types().is_valid(type)) {
            return false;
        }
        const air::TypeData& d = mod_.types().type(type);
        return d.kind == air::TypeKind::Int && d.int_width == 64;
    }
    struct I64Halves {
        uint32_t lo = 0;
        uint32_t hi = 0;
    };
    uint32_t i64_frame(air::ValueId v, SrcLoc loc);
    I64Halves i64_load(air::ValueId v, SrcLoc loc);
    void i64_store(air::ValueId result, I64Halves halves, SrcLoc loc);
    bool needs_i64_lowering(const air::InstData& inst, air::InstId id) const;
    void lower_i64_inst(air::InstId inst_id);
    void i64_helper_call(const char* name, air::ValueId a, air::ValueId b,
                         air::ValueId result, bool shift_count, SrcLoc loc);
    bool legacy_f80(air::TypeId type) const {
        return legacy32_ && mod_.types().is_valid(type) && is_f80(type);
    }
    uint32_t f80_frame(air::ValueId v, SrcLoc loc);
    void f80_push(air::ValueId v, SrcLoc loc);
    void f80_pop(air::ValueId result, SrcLoc loc);
    bool needs_f80_lowering(const air::InstData& inst, air::InstId id) const;
    void lower_f80_inst(air::InstId inst_id);

    void lower_inst(air::InstId inst_id);
    void lower_asm(const air::InstData& inst, air::InstId inst_id);
    void lower_call(const air::InstData& inst, air::InstId inst_id);
    void lower_call_cdecl(const air::InstData& inst, air::InstId inst_id);
    void lower_ret(const air::InstData& inst, air::InstId inst_id);
    void lower_icmp(const air::InstData& inst, air::InstId inst_id);
    void lower_fcmp(const air::InstData& inst, air::InstId inst_id);
    void mask_subword(air::TypeId type, uint32_t& vreg);
    void emit_truth_test(air::ValueId cond, SrcLoc loc);

    const air::Module& mod_;
    const air::Function& func_;
    MFunction& out_;
    std::vector<Diagnostic>& diagnostics_;
    bool failed_ = false;
    EhMetadataBuilder eh_{mod_, func_, out_, diagnostics_, failed_};

    std::unordered_map<uint32_t, uint32_t> block_map_;
    std::unordered_map<uint32_t, Slot> slots_;
    std::unordered_map<uint32_t, uint32_t> frame_addrs_;
    std::unordered_map<uint32_t, uint32_t> block_values_;
    std::unordered_map<uint32_t, uint32_t> value_vregs_;

    const bool opt_ = false;
    bool legacy32_ = false;
    bool real_mode_ = false;
    air::ValueId sret_param_{};
    bool has_sret_param_ = false;
    uint32_t named_gprs_ = 0;
    uint32_t named_fprs_ = 0;
    int32_t reg_save_frame_ = -1;
    uint32_t cur_block_ = 0;
};

X86Op ISel::load_op_for(air::TypeId type) const {
    const air::TypeData& data = mod_.types().type(type);
    if (data.kind == air::TypeKind::Ptr) {
        return legacy32_ ? X86Op::Load32 : X86Op::Load64;
    }
    if (data.kind == air::TypeKind::Float) {
        switch (data.float_kind) {
            case air::FloatKind::F32: return X86Op::LoadSS;
            case air::FloatKind::F64: return X86Op::LoadSD;
            case air::FloatKind::F128: return X86Op::LoadX128;
            case air::FloatKind::F80: return X86Op::LoadX128;
        }
    }
    switch (data.int_width) {
        case 8: return X86Op::Load8Z;
        case 16: return X86Op::Load16Z;
        case 32: return X86Op::Load32;
        default: return X86Op::Load64;
    }
}

X86Op ISel::store_op_for(air::TypeId type) const {
    const air::TypeData& data = mod_.types().type(type);
    if (data.kind == air::TypeKind::Ptr) {
        return legacy32_ ? X86Op::Store32 : X86Op::Store64;
    }
    if (data.kind == air::TypeKind::Float) {
        switch (data.float_kind) {
            case air::FloatKind::F32: return X86Op::StoreSS;
            case air::FloatKind::F64: return X86Op::StoreSD;
            case air::FloatKind::F128: return X86Op::StoreX128;
            case air::FloatKind::F80: return X86Op::StoreX128;
        }
    }
    switch (data.int_width) {
        case 8: return X86Op::Store8;
        case 16: return X86Op::Store16;
        case 32: return X86Op::Store32;
        default: return X86Op::Store64;
    }
}

uint32_t ISel::materialize_int(uint64_t bits, bool wide) {
    uint32_t vreg = new_gpr();
    if (!wide || bits <= 0xFFFFFFFFull) {

        emit(X86Op::MovRI32,
             {vr(vreg),
              MOperand::make_imm(static_cast<int64_t>(bits & 0xFFFFFFFFull))});
        return vreg;
    }
    int64_t value = static_cast<int64_t>(bits);
    if (value == static_cast<int32_t>(value)) {
        emit(X86Op::MovRI64, {vr(vreg), MOperand::make_imm(value)});
        return vreg;
    }
    emit(X86Op::MovAbs64, {vr(vreg), MOperand::make_imm(value)});
    return vreg;
}

uint32_t ISel::materialize_symbol_addr(const std::string& symbol, bool direct) {
    uint32_t vreg = new_gpr();
    if (legacy32_) {

        emit(X86Op::MovAbsSym32,
             {vr(vreg), MOperand::make_symbol(symbol, SymFlavor::Plain)});
        return vreg;
    }
    if (direct) {
        emit(X86Op::LeaRip,
             {vr(vreg), MOperand::make_symbol(symbol, SymFlavor::Plain)});
    } else {
        emit(X86Op::LoadRip64,
             {vr(vreg), MOperand::make_symbol(symbol, SymFlavor::GotPcRel)});
    }
    return vreg;
}

uint32_t ISel::materialize_tls_addr(const std::string& symbol, SrcLoc loc) {
    if (legacy32_ || mod_.target().os != TargetOS::MACOS) {
        error("thread_local address lowering is not supported for this x86 "
              "object format yet",
              loc);
        return new_gpr();
    }

    uint32_t descriptor = new_gpr();
    emit(X86Op::LoadRip64,
         {vr(descriptor),
          MOperand::make_symbol(symbol, SymFlavor::TlvPcRel)});
    uint32_t resolver = new_gpr();
    emit(X86Op::Load64,
         {vr(resolver), vr(descriptor), MOperand::make_imm(0)});
    emit(X86Op::MovRR64, {pr(RDI), vr(descriptor)});
    emit(X86Op::MovRR64, {pr(R11), vr(resolver)});
    emit(X86Op::CallR, {pr(R11)});
    uint32_t result = new_gpr();
    emit(X86Op::MovRR64, {vr(result), pr(RAX)});
    return result;
}

uint32_t ISel::materialize_fp_bits(uint64_t bits, bool wide) {
    if (legacy32_ && wide) {

        uint32_t slot = out_.new_frame_object(8, 8);
        uint32_t lo = materialize_int(bits & 0xFFFFFFFFull, false);
        emit(X86Op::Store32,
             {vr(lo), MOperand::make_frame(slot), MOperand::make_imm(0)});
        uint32_t hi = materialize_int((bits >> 32) & 0xFFFFFFFFull, false);
        emit(X86Op::Store32,
             {vr(hi), MOperand::make_frame(slot), MOperand::make_imm(4)});
        uint32_t vreg = new_fpr();
        emit(X86Op::LoadSD,
             {vr(vreg), MOperand::make_frame(slot), MOperand::make_imm(0)});
        return vreg;
    }
    uint32_t gpr = materialize_int(bits, wide);
    uint32_t vreg = new_fpr();
    emit(wide ? X86Op::MovqGX : X86Op::MovdGX, {vr(vreg), vr(gpr)});
    return vreg;
}

uint32_t ISel::materialize_f80_bits(uint64_t lo, uint64_t hi) {
    uint32_t slot = out_.new_frame_object(16, 16);
    uint32_t low = materialize_int(lo, true);
    emit(X86Op::Store64,
         {vr(low), MOperand::make_frame(slot), MOperand::make_imm(0)});
    uint32_t high = materialize_int(hi, true);
    emit(X86Op::Store64,
         {vr(high), MOperand::make_frame(slot), MOperand::make_imm(8)});
    uint32_t vreg = out_.new_vreg(RegClass::Fpr128);
    emit(X86Op::LoadX128,
         {vr(vreg), MOperand::make_frame(slot), MOperand::make_imm(0)});
    return vreg;
}

void ISel::emit_move(uint32_t dest, bool dest_phys, uint32_t src,
                     air::TypeId type) {
    MOperand dst = dest_phys ? pr(dest) : vr(dest);
    if (is_fp_type(type)) {
        emit(X86Op::MovapsRR, {dst, vr(src)});
    } else {
        emit(is_wide(type) ? X86Op::MovRR64 : X86Op::MovRR32, {dst, vr(src)});
    }
}

uint32_t ISel::two_address_result(uint32_t lhs, bool wide, bool fp) {
    uint32_t result = fp ? new_fpr() : new_gpr();
    if (fp) {
        emit(X86Op::MovapsRR, {vr(result), vr(lhs)});
    } else {
        emit(wide ? X86Op::MovRR64 : X86Op::MovRR32, {vr(result), vr(lhs)});
    }
    return result;
}

uint32_t ISel::setcc_result(Cond cond) {
    uint32_t flag = new_gpr();
    emit(X86Op::SetccR, {vr(flag)}, static_cast<uint32_t>(cond));
    uint32_t result = new_gpr();
    emit(X86Op::Movzbl, {vr(result), vr(flag)});
    return result;
}

uint32_t ISel::f80_spill(uint32_t vreg) {
    uint32_t slot = out_.new_frame_object(16, 16);
    emit(X86Op::StoreX128,
         {vr(vreg), MOperand::make_frame(slot), MOperand::make_imm(0)});
    return slot;
}

void ISel::f80_fld(uint32_t slot) {
    emit(X86Op::Fld80, {MOperand::make_frame(slot), MOperand::make_imm(0)});
}

uint32_t ISel::f80_pop_result() {
    uint32_t slot = out_.new_frame_object(16, 16);
    emit(X86Op::Fstp80, {MOperand::make_frame(slot), MOperand::make_imm(0)});
    uint32_t result = out_.new_vreg(RegClass::Fpr128);
    emit(X86Op::LoadX128,
         {vr(result), MOperand::make_frame(slot), MOperand::make_imm(0)});
    return result;
}

void ISel::fp_push_st0(uint32_t xmm, air::TypeId type) {
    bool wide = is_wide(type);
    uint32_t slot = out_.new_frame_object(8, 8);
    emit(wide ? X86Op::StoreSD : X86Op::StoreSS,
         {vr(xmm), MOperand::make_frame(slot), MOperand::make_imm(0)});
    emit(wide ? X86Op::FldM64 : X86Op::FldM32,
         {MOperand::make_frame(slot), MOperand::make_imm(0)});
}

uint32_t ISel::fp_pop_st0(air::TypeId type) {
    bool wide = is_wide(type);
    uint32_t slot = out_.new_frame_object(8, 8);
    emit(wide ? X86Op::FstpM64 : X86Op::FstpM32,
         {MOperand::make_frame(slot), MOperand::make_imm(0)});
    uint32_t result = new_fpr();
    emit(wide ? X86Op::LoadSD : X86Op::LoadSS,
         {vr(result), MOperand::make_frame(slot), MOperand::make_imm(0)});
    return result;
}

uint32_t ISel::canonical_vreg(air::ValueId v) {
    auto found = value_vregs_.find(v.index);
    if (found != value_vregs_.end()) {
        return found->second;
    }
    air::TypeId type = func_.value_type(v);
    uint32_t vreg = new_reg_for(type);
    value_vregs_[v.index] = vreg;
    return vreg;
}

void ISel::emit_copy(uint32_t dest_vreg, uint32_t src_vreg) {
    RegClass cls = out_.vreg_classes[dest_vreg];
    if (cls == RegClass::Gpr) {
        emit(X86Op::MovRR64, {vr(dest_vreg), vr(src_vreg)});
        return;
    }
    emit(X86Op::MovapsRR, {vr(dest_vreg), vr(src_vreg)});
}

uint32_t ISel::use_reg(air::ValueId v, SrcLoc loc) {
    auto cached = block_values_.find(v.index);
    if (cached != block_values_.end()) {
        return cached->second;
    }

    auto frame = frame_addrs_.find(v.index);
    if (frame != frame_addrs_.end()) {
        uint32_t addr = new_gpr();
        emit(X86Op::FrameAddr, {vr(addr), MOperand::make_frame(frame->second)});
        block_values_[v.index] = addr;
        return addr;
    }

    const air::ValueData& data = func_.value(v);
    if (!check_scalar(data.type, loc)) {
        return new_gpr();
    }

    if (opt_ && (data.kind == air::ValueKind::InstResult ||
                 data.kind == air::ValueKind::BlockParam)) {
        return canonical_vreg(v);
    }

    uint32_t vreg = 0;
    switch (data.kind) {
        case air::ValueKind::InstResult:
        case air::ValueKind::BlockParam: {
            auto slot = slots_.find(v.index);
            if (slot == slots_.end()) {
                error("value used before definition in the fast tier", loc);
                return new_gpr();
            }
            vreg = new_reg_for(data.type);
            MInst load;
            load.opcode = op(load_op_for(data.type));
            load.operands.push_back(vr(vreg));
            load.operands.push_back(MOperand::make_frame(slot->second.frame_index));
            load.operands.push_back(MOperand::make_imm(0));
            cur().insts.push_back(std::move(load));
            break;
        }
        case air::ValueKind::ConstInt:
            vreg = materialize_int(data.payload, is_wide(data.type));
            break;
        case air::ValueKind::ConstNull:
        case air::ValueKind::Undef:
            if (is_f80(data.type)) {
                vreg = materialize_f80_bits(0, 0);
            } else if (is_fp_type(data.type)) {
                vreg = materialize_fp_bits(0, is_wide(data.type));
            } else {
                vreg = materialize_int(0, is_wide(data.type));
            }
            break;
        case air::ValueKind::ConstFloat:
            if (is_f80(data.type)) {
                vreg = materialize_f80_bits(data.payload, data.payload2);
            } else {
                vreg = materialize_fp_bits(data.payload, is_wide(data.type));
            }
            break;
        case air::ValueKind::GlobalAddr: {
            const air::GlobalData& global =
                mod_.global(air::GlobalId{static_cast<uint32_t>(data.payload)});
            if (global.is_thread_local) {
                vreg = materialize_tls_addr(
                    sym_name(mod_.target(), global.name,
                             global.attrs.no_prefix),
                    loc);
                break;
            }
            bool local = global.linkage == air::Linkage::Internal ||
                         global.attrs.hidden;
            vreg = materialize_symbol_addr(
                sym_name(mod_.target(), global.name, global.attrs.no_prefix), local);
            break;
        }
        case air::ValueKind::FuncAddr: {
            const air::Function& target =
                mod_.function(air::FuncId{static_cast<uint32_t>(data.payload)});
            bool local = !target.is_declaration() &&
                         (target.linkage() == air::Linkage::Internal ||
                          target.attrs().hidden);
            vreg = materialize_symbol_addr(
                sym_name(mod_.target(), target.name(), target.attrs().no_prefix), local);
            break;
        }
        case air::ValueKind::LabelAddr: {
            auto found = block_map_.find(static_cast<uint32_t>(data.payload));
            if (found == block_map_.end()) {
                error("label address of an unmapped block", loc);
                return new_gpr();
            }
            out_.blocks[found->second].address_taken = true;
            vreg = materialize_symbol_addr(
                "l_air_lbl_" + std::to_string(out_.index) + "_" +
                    std::to_string(found->second),
                /*direct=*/true);
            break;
        }
    }

    block_values_[v.index] = vreg;
    return vreg;
}

MOperand ISel::mem_base(air::ValueId v, SrcLoc loc) {
    auto frame = frame_addrs_.find(v.index);
    if (frame != frame_addrs_.end()) {
        return MOperand::make_frame(frame->second);
    }
    return vr(use_reg(v, loc));
}

void ISel::define(air::ValueId result, uint32_t vreg, SrcLoc loc) {
    if (opt_) {
        auto bound = value_vregs_.find(result.index);
        if (bound == value_vregs_.end()) {
            value_vregs_[result.index] = vreg;
        } else if (bound->second != vreg) {
            emit_copy(bound->second, vreg);
        }
        return;
    }
    block_values_[result.index] = vreg;
    auto slot = slots_.find(result.index);
    if (slot != slots_.end()) {
        store_to_slot(vreg, slot->second);
    }
    (void)loc;
}

void ISel::store_to_slot(uint32_t vreg, const Slot& slot) {
    MInst store;
    store.opcode = op(store_op_for(slot.type));
    store.operands.push_back(vr(vreg));
    store.operands.push_back(MOperand::make_frame(slot.frame_index));
    store.operands.push_back(MOperand::make_imm(0));
    cur().insts.push_back(std::move(store));
}

void ISel::emit_edge_stores(air::BlockCallId call, SrcLoc loc) {
    const air::BlockCall& edge = func_.block_call(call);
    std::span<const air::ValueId> args = func_.block_call_args(call);
    std::span<const air::ValueId> params = func_.block_params(edge.target);
    for (size_t i = 0; i < args.size() && i < params.size(); ++i) {
        auto slot = slots_.find(params[i].index);
        if (slot == slots_.end()) {
            continue;
        }
        if (legacy_i64(func_.value_type(params[i]))) {

            I64Halves v = i64_load(args[i], loc);
            uint32_t fi = slot->second.frame_index;
            emit(X86Op::Store32,
                 {vr(v.lo), MOperand::make_frame(fi), MOperand::make_imm(0)});
            emit(X86Op::Store32,
                 {vr(v.hi), MOperand::make_frame(fi), MOperand::make_imm(4)});
            continue;
        }
        if (legacy_f80(func_.value_type(params[i]))) {

            f80_push(args[i], loc);
            emit(X86Op::Fstp80,
                 {MOperand::make_frame(slot->second.frame_index),
                  MOperand::make_imm(0)});
            continue;
        }
        uint32_t vreg = use_reg(args[i], loc);
        store_to_slot(vreg, slot->second);
    }
}

void ISel::emit_parallel_copies(air::BlockCallId call, SrcLoc loc) {
    const air::BlockCall& edge = func_.block_call(call);
    std::span<const air::ValueId> args = func_.block_call_args(call);
    std::span<const air::ValueId> params = func_.block_params(edge.target);

    struct Copy {
        uint32_t dest;
        uint32_t src;
    };
    std::vector<Copy> pending;
    for (size_t i = 0; i < args.size() && i < params.size(); ++i) {
        uint32_t dest = canonical_vreg(params[i]);
        uint32_t src = use_reg(args[i], loc);
        if (dest != src) {
            pending.push_back({dest, src});
        }
    }

    while (!pending.empty()) {
        bool progressed = false;
        for (size_t i = 0; i < pending.size(); ++i) {
            bool dest_is_pending_source = false;
            for (const Copy& other : pending) {
                if (other.src == pending[i].dest) {
                    dest_is_pending_source = true;
                    break;
                }
            }
            if (dest_is_pending_source) {
                continue;
            }
            emit_copy(pending[i].dest, pending[i].src);
            pending.erase(pending.begin() + static_cast<ptrdiff_t>(i));
            progressed = true;
            break;
        }
        if (progressed) {
            continue;
        }
        uint32_t saved_dest = pending.front().dest;
        RegClass cls = out_.vreg_classes[saved_dest];
        uint32_t temp = out_.new_vreg(cls);
        emit_copy(temp, saved_dest);
        for (Copy& copy : pending) {
            if (copy.src == saved_dest) {
                copy.src = temp;
            }
        }
    }
}

uint32_t ISel::edge_target(air::BlockCallId call, SrcLoc loc) {
    const air::BlockCall& edge = func_.block_call(call);
    uint32_t target = block_map_.at(edge.target.index);
    if (func_.block_call_args(call).empty()) {
        return target;
    }

    uint32_t saved = cur_block_;
    std::unordered_map<uint32_t, uint32_t> saved_values;
    saved_values.swap(block_values_);
    out_.blocks.emplace_back();
    uint32_t edge_block = static_cast<uint32_t>(out_.blocks.size()) - 1;
    cur_block_ = edge_block;
    if (opt_) {
        emit_parallel_copies(call, loc);
    } else {
        emit_edge_stores(call, loc);
    }
    emit(X86Op::JmpLbl, {MOperand::make_label(target)});
    cur_block_ = saved;
    saved_values.swap(block_values_);
    return edge_block;
}

void ISel::mask_subword(air::TypeId type, uint32_t& vreg) {
    uint16_t width = int_width(type);
    if (width != 8 && width != 16) {
        return;
    }
    uint32_t masked = new_gpr();
    emit(width == 8 ? X86Op::Movzbl : X86Op::Movzwl, {vr(masked), vr(vreg)});
    vreg = masked;
}

void ISel::emit_truth_test(air::ValueId cond, SrcLoc loc) {
    uint32_t vreg = use_reg(cond, loc);
    emit(X86Op::Test32, {vr(vreg), vr(vreg)});
}

void ISel::lower_icmp(const air::InstData& inst, air::InstId inst_id) {
    std::span<const air::ValueId> ops = func_.operands(inst_id);
    air::TypeId operand_type = func_.value_type(ops[0]);
    uint32_t lhs = use_reg(ops[0], inst.loc);
    uint32_t rhs = use_reg(ops[1], inst.loc);
    bool wide = is_wide(operand_type);
    emit(wide ? X86Op::Cmp64 : X86Op::Cmp32, {vr(lhs), vr(rhs)});

    static constexpr Cond kMap[] = {
        Cond::E, Cond::Ne, Cond::L, Cond::Le, Cond::G, Cond::Ge,
        Cond::B, Cond::Be, Cond::A, Cond::Ae,
    };
    uint32_t result = setcc_result(kMap[inst.aux & 0xFF]);
    define(inst.result, result, inst.loc);
}

void ISel::lower_fcmp(const air::InstData& inst, air::InstId inst_id) {
    std::span<const air::ValueId> ops = func_.operands(inst_id);
    air::TypeId operand_type = func_.value_type(ops[0]);
    if (is_f128(operand_type)) {
        unsupported("IEEE-quad long double comparison", inst.loc);
        return;
    }
    bool f80 = is_f80(operand_type);

    bool f80_mem = f80 && legacy32_;
    uint32_t lhs = f80_mem ? 0 : use_reg(ops[0], inst.loc);
    uint32_t rhs = f80_mem ? 0 : use_reg(ops[1], inst.loc);
    bool wide = is_wide(operand_type);
    X86Op cmp = wide ? X86Op::Ucomisd : X86Op::Ucomiss;

    auto compare = [&](bool swap) {
        if (f80) {
            if (f80_mem) {
                f80_push(swap ? ops[0] : ops[1], inst.loc);
                f80_push(swap ? ops[1] : ops[0], inst.loc);
            } else {
                uint32_t first = swap ? lhs : rhs;
                uint32_t second = swap ? rhs : lhs;
                f80_fld(f80_spill(first));
                f80_fld(f80_spill(second));
            }
            emit(X86Op::Fucomip, {});
            emit(X86Op::FpopSt0, {});
            return;
        }
        if (swap) {
            emit(cmp, {vr(rhs), vr(lhs)});
        } else {
            emit(cmp, {vr(lhs), vr(rhs)});
        }
    };
    auto single = [&](Cond cond, bool swap) {
        compare(swap);
        define(inst.result, setcc_result(cond), inst.loc);
    };
    auto pair = [&](Cond a, Cond b, bool combine_and) {
        compare(false);
        uint32_t first = setcc_result(a);
        uint32_t second = setcc_result(b);
        uint32_t result = new_gpr();
        emit(X86Op::MovRR32, {vr(result), vr(first)});
        emit(combine_and ? X86Op::And32 : X86Op::Or32,
             {vr(result), vr(second)});
        define(inst.result, result, inst.loc);
    };

    switch (static_cast<air::FloatCond>(inst.aux & 0xFF)) {
        case air::FloatCond::Oeq: pair(Cond::Np, Cond::E, true); break;
        case air::FloatCond::One: pair(Cond::Np, Cond::Ne, true); break;
        case air::FloatCond::Ogt: single(Cond::A, false); break;
        case air::FloatCond::Oge: single(Cond::Ae, false); break;
        case air::FloatCond::Olt: single(Cond::A, true); break;
        case air::FloatCond::Ole: single(Cond::Ae, true); break;
        case air::FloatCond::Ord: single(Cond::Np, false); break;
        case air::FloatCond::Uno: single(Cond::P, false); break;
        case air::FloatCond::Ueq: single(Cond::E, false); break;
        case air::FloatCond::Une: pair(Cond::P, Cond::Ne, false); break;
        case air::FloatCond::Ugt: single(Cond::B, true); break;
        case air::FloatCond::Uge: single(Cond::Be, true); break;
        case air::FloatCond::Ult: single(Cond::B, false); break;
        case air::FloatCond::Ule: single(Cond::Be, false); break;
    }
}

namespace {

int clobber_reg_index(const std::string& name) {
    static const std::unordered_map<std::string, int> kNames = {
        {"rax", RAX}, {"eax", RAX}, {"ax", RAX}, {"al", RAX}, {"ah", RAX},
        {"rbx", RBX}, {"ebx", RBX}, {"bx", RBX}, {"bl", RBX}, {"bh", RBX},
        {"rcx", RCX}, {"ecx", RCX}, {"cx", RCX}, {"cl", RCX}, {"ch", RCX},
        {"rdx", RDX}, {"edx", RDX}, {"dx", RDX}, {"dl", RDX}, {"dh", RDX},
        {"rsi", RSI}, {"esi", RSI}, {"si", RSI}, {"sil", RSI},
        {"rdi", RDI}, {"edi", RDI}, {"di", RDI}, {"dil", RDI},
        {"rbp", RBP}, {"rsp", RSP},
        {"r8", R8}, {"r9", R9}, {"r10", R10}, {"r11", R11},
        {"r12", R12}, {"r13", R13}, {"r14", R14}, {"r15", R15},
    };
    auto found = kNames.find(name);
    return found == kNames.end() ? -1 : found->second;
}

char asm_width_char(uint64_t size) {
    return size == 1 ? 'b' : size == 2 ? 'w' : size == 4 ? 'l' : 'q';
}

} // namespace

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
        bool is_memory = false;
        int tied_to = -1;
        air::TypeId type;
    };
    std::vector<OpInfo> info(n);
    std::set<uint32_t> claimed;
    std::set<uint32_t> claimed_out;
    std::set<uint32_t> claimed_in;
    std::set<uint32_t> save_set;

    auto callee_saved = [&](uint32_t phys) {
        return legacy32_ ? is_callee_saved_reg_32(phys)
                         : is_callee_saved_reg(phys);
    };
    auto claim_touch = [&](uint32_t phys, const std::string& what) -> bool {
        if (phys == RSP) {
            error("inline asm cannot write the stack pointer (" + what + ")",
                  loc);
            return false;
        }
        if (phys == RBP) {
            error("inline asm cannot write the frame pointer (" + what + ")",
                  loc);
            return false;
        }
        if (callee_saved(phys)) {
            save_set.insert(phys);
        }
        claimed.insert(phys);
        return true;
    };

    for (const std::string& clobber : payload.clobbers) {
        if (clobber == "memory" || clobber == "cc") {
            continue;
        }
        int reg = clobber_reg_index(clobber);
        if (reg < 0) {
            continue;

        }
        if (!claim_touch(static_cast<uint32_t>(reg),
                         "clobber '" + clobber + "'")) {
            return;
        }
    }

    auto letter_reg = [](char letter) -> int {
        switch (letter) {
            case 'a': return RAX;
            case 'b': return RBX;
            case 'c': return RCX;
            case 'd': return RDX;
            case 'S': return RSI;
            case 'D': return RDI;
            default: return -1;
        }
    };

    const std::vector<std::string>& bindings = payload.register_bindings;
    if (!bindings.empty() && bindings.size() != n) {
        error("inline asm register-binding metadata is inconsistent", loc);
        return;
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
        int reg = -1;
        switch (c.kind) {
            case AsmOperandKind::Immediate:
                continue;
            case AsmOperandKind::Memory:
                info[i].is_memory = true;
                break;
            case AsmOperandKind::Tied:
                if (c.tied_output < 0 ||
                    static_cast<size_t>(c.tied_output) >= n) {
                    error("asm matching constraint references a nonexistent "
                          "operand", loc);
                    return;
                }
                info[i].tied_to = c.tied_output;
                continue;
            case AsmOperandKind::Register:
                if (c.letter != 'r') {
                    reg = letter_reg(c.letter);
                    if (reg < 0) {
                        unsupported("the '" + std::string(1, c.letter) +
                                    "' register constraint in inline asm",
                                    loc);
                        return;
                    }
                }
                break;
            default:
                unsupported("this asm operand constraint", loc);
                return;
        }
        if (!bindings.empty() && !bindings[i].empty()) {
            int bound = clobber_reg_index(bindings[i]);
            if (bound < 0) {
                error("unknown register '" + bindings[i] +
                      "' in an asm operand binding", loc);
                return;
            }
            reg = bound;
        }
        if (reg < 0) {
            continue;
        }

        bool is_out = c.role != AsmOperandRole::Input;
        bool is_in = c.role != AsmOperandRole::Output;
        bool conflict =
            (is_out && !claimed_out.insert(static_cast<uint32_t>(reg)).second) ||
            (is_in && !claimed_in.insert(static_cast<uint32_t>(reg)).second);
        if (conflict) {
            unsupported("conflicting asm register constraint '" +
                        payload.constraints[i] + "'", loc);
            return;
        }
        if (!claim_touch(static_cast<uint32_t>(reg),
                         "constraint '" + payload.constraints[i] + "'")) {
            return;
        }
        info[i].phys = static_cast<uint32_t>(reg);
        info[i].has_phys = true;
    }

    static const uint32_t kPool64[] = {RSI, RDI, R8, R9, RAX, RCX, RDX};
    static const uint32_t kPool32[] = {RAX, RCX, RDX, RSI, RDI, RBX};
    const uint32_t* pool = legacy32_ ? kPool32 : kPool64;
    size_t pool_size = legacy32_ ? std::size(kPool32) : std::size(kPool64);
    size_t next_generic = 0;
    for (size_t i = 0; i < n; ++i) {
        bool needs_register = info[i].kind == AsmOperandKind::Register ||
                              info[i].is_memory;
        if (!needs_register || info[i].has_phys) {
            continue;
        }
        bool found = false;
        while (next_generic < pool_size) {
            uint32_t candidate = pool[next_generic++];
            if (claimed.count(candidate) != 0) {
                continue;
            }
            if (!claim_touch(candidate, "operand " + std::to_string(i))) {
                return;
            }
            info[i].phys = candidate;
            info[i].has_phys = true;
            found = true;
            break;
        }
        if (!found) {
            unsupported("inline asm needs more general registers than the "
                        "backend allocates for it", loc);
            return;
        }
    }

    for (size_t i = 0; i < n; ++i) {
        if (info[i].tied_to < 0) {
            continue;
        }
        const OpInfo& target = info[static_cast<size_t>(info[i].tied_to)];
        if (!target.has_phys || target.is_memory) {
            error("asm matching constraint ties to an operand with no "
                  "register", loc);
            return;
        }
        info[i].phys = target.phys;
        info[i].has_phys = true;
    }

    std::vector<uint32_t> src(n, 0);
    std::vector<int64_t> imm(n, 0);
    for (size_t i = 0; i < n; ++i) {
        if (info[i].kind == AsmOperandKind::Immediate) {
            const air::ValueData& data = func_.value(ops[i]);
            if (data.kind != air::ValueKind::ConstInt) {
                error("asm immediate operand is not a constant", loc);
                return;
            }
            imm[i] = static_cast<int64_t>(data.payload);
            continue;
        }

        src[i] = use_reg(ops[i], loc);
    }

    struct SavedReg {
        uint32_t phys = 0;
        uint32_t slot = 0;
    };
    uint32_t word_bytes = legacy32_ ? 4u : 8u;
    X86Op save_store = legacy32_ ? X86Op::Store32 : X86Op::Store64;
    X86Op save_load = legacy32_ ? X86Op::Load32 : X86Op::Load64;
    std::vector<SavedReg> saved;
    saved.reserve(save_set.size());
    for (uint32_t phys : save_set) {
        SavedReg entry;
        entry.phys = phys;
        entry.slot = out_.new_frame_object(word_bytes, word_bytes);
        emit(save_store,
             {pr(phys), MOperand::make_frame(entry.slot),
              MOperand::make_imm(0)});
        saved.push_back(entry);
    }

    for (size_t i = 0; i < n; ++i) {
        if (!info[i].has_phys) {
            continue;
        }
        uint64_t size = scalar_size(info[i].type);
        if (info[i].is_memory) {

            emit(legacy32_ ? X86Op::MovRR32 : X86Op::MovRR64,
                 {pr(info[i].phys), vr(src[i])});
            continue;
        }
        if (info[i].role == AsmOperandRole::ReadWriteOutput) {
            X86Op load = size == 1 ? X86Op::Load8Z
                         : size == 2 ? X86Op::Load16Z
                         : size == 4 ? X86Op::Load32
                                     : X86Op::Load64;
            emit(load, {pr(info[i].phys), vr(src[i]), MOperand::make_imm(0)});
        } else if (info[i].role == AsmOperandRole::Input) {
            emit(size == 8 ? X86Op::MovRR64 : X86Op::MovRR32,
                 {pr(info[i].phys), vr(src[i])});
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
        char next = tmpl[i + 1];
        if (next == '%') {
            resolved += '%';
            ++i;
            continue;
        }
        char forced = 0;
        bool high_byte = false;
        size_t j = i + 1;
        if (next == 'b' || next == 'w' || next == 'k' || next == 'q') {
            forced = next == 'k' ? 'l' : next;
            ++j;
        } else if (next == 'h') {

            high_byte = true;
            ++j;
        }
        if (j >= tmpl.size() || !std::isdigit(static_cast<unsigned char>(tmpl[j]))) {
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
            resolved += '$';
            resolved += std::to_string(imm[number]);
        } else if (info[number].is_memory) {
            resolved += '(';
            resolved += att_reg_name(info[number].phys,
                                     legacy32_ ? 'l' : 'q');
            resolved += ')';
        } else if (high_byte) {
            uint32_t phys = info[number].phys;
            if (phys != RAX && phys != RBX && phys != RCX && phys != RDX) {
                template_error = true;
                break;
            }
            static const char* kHigh[] = {"%ah", "%ch", "%dh", "%bh"};
            resolved += kHigh[phys];
        } else {
            char width =
                forced ? forced : asm_width_char(scalar_size(info[number].type));
            resolved += att_reg_name(info[number].phys, width);
        }
        i = j - 1;
    }
    if (template_error) {
        unsupported("this inline asm template operand form", loc);
        return;
    }

    out_.asm_texts.push_back("\t" + resolved + "\n");
    emit(X86Op::AsmBlock, {},
         static_cast<uint32_t>(out_.asm_texts.size()) - 1);

    std::vector<uint32_t> captured(n, 0);
    auto is_captured_output = [&](size_t i) {
        return info[i].has_phys && !info[i].is_memory && info[i].tied_to < 0 &&
               info[i].role != AsmOperandRole::Input;
    };
    for (size_t i = 0; i < n; ++i) {
        if (!is_captured_output(i)) {
            continue;
        }
        captured[i] = new_gpr();
        uint64_t size = scalar_size(info[i].type);
        emit(size == 8 ? X86Op::MovRR64 : X86Op::MovRR32,
             {vr(captured[i]), pr(info[i].phys)});
    }
    for (size_t i = 0; i < n; ++i) {
        if (!is_captured_output(i)) {
            continue;
        }
        uint64_t size = scalar_size(info[i].type);
        X86Op store = size == 1 ? X86Op::Store8
                      : size == 2 ? X86Op::Store16
                      : size == 4 ? X86Op::Store32
                                  : X86Op::Store64;
        emit(store, {vr(captured[i]), vr(src[i]), MOperand::make_imm(0)});
    }

    for (const SavedReg& entry : saved) {
        emit(save_load,
             {pr(entry.phys), MOperand::make_frame(entry.slot),
              MOperand::make_imm(0)});
    }
}

void ISel::lower_call(const air::InstData& inst, air::InstId inst_id) {
    if (legacy32_) {
        lower_call_cdecl(inst, inst_id);
        return;
    }
    std::span<const air::ValueId> ops = func_.operands(inst_id);
    bool indirect = inst.op == air::Opcode::CallIndirect ||
                    inst.op == air::Opcode::InvokeIndirect;

    air::SigId sig_id;
    std::string callee_symbol;
    air::ValueId callee_value;
    if (indirect) {
        sig_id = air::SigId{static_cast<uint32_t>(inst.aux)};
        callee_value = ops[0];
        ops = ops.subspan(1);
    } else {
        const air::Function& callee =
            mod_.function(air::FuncId{static_cast<uint32_t>(inst.aux)});
        sig_id = callee.sig();
        callee_symbol = sym_name(mod_.target(), callee.name(), callee.attrs().no_prefix);
    }
    const air::SigData& sig = mod_.types().signature(sig_id);

    bool pair_ret = sig.ret_class == air::RetClass::IntPair;
    bool hfa_ret = sig.ret_class == air::RetClass::Hfa;
    air::ValueId ret_dest{};
    if (pair_ret || hfa_ret) {
        if (ops.empty()) {
            error("multi-register return call is missing its destination",
                  inst.loc);
            return;
        }
        ret_dest = ops.back();
        ops = ops.first(ops.size() - 1);
    }
    if (hfa_ret && (is_f128(sig.ret_type) || sig.ret_count > 2)) {

        unsupported("this floating-point aggregate return", inst.loc);
        return;
    }

    std::vector<uint32_t> arg_vregs;
    std::vector<air::TypeId> arg_types;
    arg_vregs.reserve(ops.size());
    for (air::ValueId arg : ops) {
        arg_vregs.push_back(use_reg(arg, inst.loc));
        arg_types.push_back(func_.value_type(arg));
    }
    uint32_t callee_vreg = 0;
    if (indirect) {
        callee_vreg = use_reg(callee_value, inst.loc);
    }

    struct RegMove {
        uint32_t phys;
        uint32_t vreg;
        air::TypeId type;
    };

    auto byval_param = [&](size_t i) -> const air::SigParam* {
        if (i < sig.params.size() &&
            sig.params[i].role == air::ParamRole::StackByval) {
            return &sig.params[i];
        }
        return nullptr;
    };

    uint64_t dynamic_outgoing = 0;
    if (out_.has_dynamic_stack) {
        uint32_t plan_gpr = 0;
        uint32_t plan_fpr = 0;
        uint64_t planned = 0;
        for (size_t i = 0; i < arg_vregs.size();) {
            uint8_t group =
                i < sig.params.size() ? sig.params[i].coerce_group : 0;
            if (group > 1 && i + group <= arg_vregs.size()) {
                unsigned need_int = 0;
                unsigned need_sse = 0;
                for (size_t j = i; j < i + group; ++j) {
                    if (is_fp_type(arg_types[j])) {
                        ++need_sse;
                    } else {
                        ++need_int;
                    }
                }
                if (plan_gpr + need_int <= 6 && plan_fpr + need_sse <= 8) {
                    plan_gpr += need_int;
                    plan_fpr += need_sse;
                } else {
                    planned = (planned + 7) & ~uint64_t{7};
                    planned += 8ull * group;
                }
                i += group;
                continue;
            }
            if (const air::SigParam* byval = byval_param(i)) {
                uint64_t align = std::max<uint64_t>(8, byval->byval_align);
                planned = (planned + align - 1) & ~(align - 1);
                planned += (byval->byval_size + 7) & ~uint64_t{7};
                ++i;
                continue;
            }
            if (is_f80(arg_types[i])) {
                planned = (planned + 15) & ~uint64_t{15};
                planned += 16;
                ++i;
                continue;
            }
            bool fp = is_fp_type(arg_types[i]);
            bool to_stack = fp ? plan_fpr >= 8 : plan_gpr >= 6;
            if (fp && !to_stack) {
                ++plan_fpr;
            } else if (!fp && !to_stack) {
                ++plan_gpr;
            }
            if (to_stack) {
                uint64_t slot = std::max<uint64_t>(8, scalar_size(arg_types[i]));
                planned = (planned + slot - 1) & ~(slot - 1);
                planned += slot;
            }
            ++i;
        }
        dynamic_outgoing = (planned + 15) & ~uint64_t{15};
        if (dynamic_outgoing > 0) {
            emit(X86Op::SubI64,
                 {pr(RSP),
                  MOperand::make_imm(static_cast<int64_t>(dynamic_outgoing))});
        }
    }

    std::vector<RegMove> reg_moves;
    uint32_t next_gpr = 0;
    uint32_t next_fpr = 0;
    uint64_t stack_off = 0;
    for (size_t i = 0; i < arg_vregs.size();) {
        air::TypeId type = arg_types[i];

        uint8_t group = i < sig.params.size() ? sig.params[i].coerce_group : 0;
        if (group > 1 && i + group <= arg_vregs.size()) {
            unsigned need_int = 0;
            unsigned need_sse = 0;
            for (size_t j = i; j < i + group; ++j) {
                if (is_fp_type(arg_types[j])) {
                    ++need_sse;
                } else {
                    ++need_int;
                }
            }
            bool fits = next_gpr + need_int <= 6 && next_fpr + need_sse <= 8;
            for (size_t j = i; j < i + group; ++j) {
                bool fp = is_fp_type(arg_types[j]);
                if (fits) {
                    uint32_t phys = fp ? xmm(next_fpr++) : kGprArgs[next_gpr++];
                    reg_moves.push_back({phys, arg_vregs[j], arg_types[j]});
                } else {
                    stack_off = (stack_off + 7) & ~uint64_t{7};
                    emit(store_op_for(arg_types[j]),
                         {vr(arg_vregs[j]), pr(RSP),
                          MOperand::make_imm(static_cast<int64_t>(stack_off))});
                    stack_off += 8;
                }
            }
            i += group;
            continue;
        }
        if (is_f80(type)) {

            stack_off = (stack_off + 15) & ~uint64_t{15};
            emit(X86Op::StoreX128,
                 {vr(arg_vregs[i]), pr(RSP),
                  MOperand::make_imm(static_cast<int64_t>(stack_off))});
            stack_off += 16;
            ++i;
            continue;
        }
        if (const air::SigParam* byval = byval_param(i)) {

            uint64_t align = std::max<uint64_t>(8, byval->byval_align);
            stack_off = (stack_off + align - 1) & ~(align - 1);
            uint32_t dest = new_gpr();
            emit(X86Op::LeaMem,
                 {vr(dest), pr(RSP),
                  MOperand::make_imm(static_cast<int64_t>(stack_off))});
            uint32_t size = materialize_int(byval->byval_size, true);
            emit(X86Op::MovRR64, {pr(RDI), vr(dest)});
            emit(X86Op::MovRR64, {pr(RSI), vr(arg_vregs[i])});
            emit(X86Op::MovRR64, {pr(RDX), vr(size)});
            emit(X86Op::CallS,
                 {MOperand::make_symbol(sym_name(mod_.target(), "memcpy", false),
                                        SymFlavor::Plain)});
            stack_off += (byval->byval_size + 7) & ~uint64_t{7};
            ++i;
            continue;
        }
        bool fp = is_fp_type(type);
        uint32_t phys = 0;
        bool to_stack = false;
        if (fp) {
            if (next_fpr >= 8) {
                to_stack = true;
            } else {
                phys = xmm(next_fpr++);
            }
        } else {
            if (next_gpr >= 6) {
                to_stack = true;
            } else {
                phys = kGprArgs[next_gpr++];
            }
        }
        if (!to_stack) {
            reg_moves.push_back({phys, arg_vregs[i], type});
            ++i;
            continue;
        }
        uint64_t slot_size = std::max<uint64_t>(8, scalar_size(type));
        stack_off = (stack_off + slot_size - 1) & ~(slot_size - 1);
        emit(store_op_for(type),
             {vr(arg_vregs[i]), pr(RSP),
              MOperand::make_imm(static_cast<int64_t>(stack_off))});
        stack_off += slot_size;
        ++i;
    }
    uint64_t outgoing = (stack_off + 15) & ~uint64_t{15};
    if (!out_.has_dynamic_stack) {
        out_.max_outgoing_bytes =
            std::max<uint32_t>(out_.max_outgoing_bytes,
                               static_cast<uint32_t>(outgoing));
    }

    for (const RegMove& move : reg_moves) {
        emit_move(move.phys, /*dest_phys=*/true, move.vreg, move.type);
    }

    if (indirect) {
        emit(X86Op::MovRR64, {pr(R11), vr(callee_vreg)});
    }
    if (sig.is_variadic) {
        emit(X86Op::MovRI32,
             {pr(RAX), MOperand::make_imm(static_cast<int64_t>(next_fpr))});
    }
    if (indirect) {
        emit(X86Op::CallR, {pr(R11)});
    } else {
        emit(X86Op::CallS,
             {MOperand::make_symbol(callee_symbol, SymFlavor::Plain)});
    }
    if (dynamic_outgoing > 0) {
        emit(X86Op::AddI64,
             {pr(RSP),
              MOperand::make_imm(static_cast<int64_t>(dynamic_outgoing))});
    }

    if (sig.ret_class == air::RetClass::Scalar && inst.result.is_valid()) {
        if (is_f80(sig.ret_type)) {

            define(inst.result, f80_pop_result(), inst.loc);
        } else {
            uint32_t result = new_reg_for(sig.ret_type);
            if (is_fp_type(sig.ret_type)) {
                emit(X86Op::MovapsRR, {vr(result), pr(XMM0)});
            } else {
                emit(is_wide(sig.ret_type) ? X86Op::MovRR64 : X86Op::MovRR32,
                     {vr(result), pr(RAX)});
            }
            define(inst.result, result, inst.loc);
        }
    } else if (pair_ret) {

        struct Lane {
            uint32_t vreg;
            bool sse;
        };
        Lane lanes[2];
        uint32_t next_int = 0;
        uint32_t next_sse = 0;
        for (int lane = 0; lane < 2; ++lane) {
            bool sse = (sig.ret_sse_mask >> lane) & 1;
            if (sse) {
                lanes[lane] = {new_fpr(), true};
                emit(X86Op::MovapsRR, {vr(lanes[lane].vreg), pr(xmm(next_sse++))});
            } else {
                lanes[lane] = {new_gpr(), false};
                emit(X86Op::MovRR64,
                     {vr(lanes[lane].vreg), pr(next_int++ == 0 ? RAX : RDX)});
            }
        }
        uint32_t dest = use_reg(ret_dest, inst.loc);
        for (int lane = 0; lane < 2; ++lane) {
            emit(lanes[lane].sse ? X86Op::StoreSD : X86Op::Store64,
                 {vr(lanes[lane].vreg), vr(dest),
                  MOperand::make_imm(8 * lane)});
        }
    } else if (hfa_ret) {
        bool wide = is_wide(sig.ret_type);
        int64_t element_size = wide ? 8 : 4;
        std::vector<uint32_t> lanes;
        for (uint8_t lane = 0; lane < sig.ret_count; ++lane) {
            uint32_t copy = new_fpr();
            emit(X86Op::MovapsRR, {vr(copy), pr(xmm(lane))});
            lanes.push_back(copy);
        }
        uint32_t dest = use_reg(ret_dest, inst.loc);
        for (uint8_t lane = 0; lane < sig.ret_count; ++lane) {
            emit(wide ? X86Op::StoreSD : X86Op::StoreSS,
                 {vr(lanes[lane]), vr(dest),
                  MOperand::make_imm(lane * element_size)});
        }
    }

}

void ISel::lower_call_cdecl(const air::InstData& inst, air::InstId inst_id) {
    SrcLoc loc = inst.loc;
    std::span<const air::ValueId> ops = func_.operands(inst_id);
    bool indirect = inst.op == air::Opcode::CallIndirect ||
                    inst.op == air::Opcode::InvokeIndirect;

    air::SigId sig_id;
    std::string callee_symbol;
    air::ValueId callee_value;
    if (indirect) {
        sig_id = air::SigId{static_cast<uint32_t>(inst.aux)};
        callee_value = ops[0];
        ops = ops.subspan(1);
    } else {
        const air::Function& callee =
            mod_.function(air::FuncId{static_cast<uint32_t>(inst.aux)});
        sig_id = callee.sig();
        callee_symbol =
            sym_name(mod_.target(), callee.name(), callee.attrs().no_prefix);
    }
    const air::SigData& sig = mod_.types().signature(sig_id);

    // Void, Scalar, and IndirectSret returns are supported; the SysV register
    // return classes (IntPair/Hfa) never arise under the i386 convention.
    if (sig.ret_class != air::RetClass::Void &&
        sig.ret_class != air::RetClass::Scalar &&
        sig.ret_class != air::RetClass::IndirectSret) {
        unsupported("this return kind in 32-bit mode", loc);
        return;
    }
    if (sig.ret_class == air::RetClass::Scalar && is_f128(sig.ret_type)) {
        unsupported("IEEE-quad long double return in 32-bit mode", loc);
        return;
    }
    if (out_.has_dynamic_stack) {
        unsupported("calls from dynamic-stack frames in 32-bit mode", loc);
        return;
    }

    struct CdeclArg {
        enum Kind { Scalar, Wide, Byval, F80 } kind = Scalar;
        uint32_t lo = 0;
        uint32_t hi = 0;
        air::ValueId f80_src;
        air::TypeId type;
        uint32_t byval_size = 0;
    };
    std::vector<CdeclArg> args;
    for (size_t i = 0; i < ops.size(); ++i) {
        air::ValueId arg = ops[i];
        air::ParamRole role =
            i < sig.params.size() ? sig.params[i].role : air::ParamRole::Normal;
        CdeclArg entry;
        entry.type = func_.value_type(arg);
        if (role == air::ParamRole::StackByval) {
            entry.kind = CdeclArg::Byval;
            entry.lo = use_reg(arg, loc);
            entry.byval_size = std::max<uint32_t>(1, sig.params[i].byval_size);
        } else if (legacy_i64(entry.type)) {
            I64Halves h = i64_load(arg, loc);
            entry.kind = CdeclArg::Wide;
            entry.lo = h.lo;
            entry.hi = h.hi;
        } else if (legacy_f80(entry.type)) {

            entry.kind = CdeclArg::F80;
            entry.f80_src = arg;
        } else {
            if (!check_scalar(entry.type, loc)) {
                return;
            }
            if (is_f128(entry.type)) {
                unsupported("IEEE-quad long double call arguments in 32-bit "
                            "mode",
                            loc);
                return;
            }

            entry.lo = use_reg(arg, loc);
        }
        args.push_back(entry);
    }
    uint32_t callee_vreg = indirect ? use_reg(callee_value, loc) : 0;

    uint64_t stack_off = 0;
    for (const CdeclArg& arg : args) {
        stack_off = (stack_off + 3) & ~uint64_t{3};
        if (arg.kind == CdeclArg::Wide) {
            emit(X86Op::Store32,
                 {vr(arg.lo), pr(RSP),
                  MOperand::make_imm(static_cast<int64_t>(stack_off))});
            emit(X86Op::Store32,
                 {vr(arg.hi), pr(RSP),
                  MOperand::make_imm(static_cast<int64_t>(stack_off + 4))});
            stack_off += 8;
        } else if (arg.kind == CdeclArg::Byval) {

            uint32_t scratch = new_gpr();
            uint32_t k = 0;
            for (; k + 4 <= arg.byval_size; k += 4) {
                emit(X86Op::Load32, {vr(scratch), vr(arg.lo),
                                     MOperand::make_imm(static_cast<int64_t>(k))});
                emit(X86Op::Store32,
                     {vr(scratch), pr(RSP),
                      MOperand::make_imm(static_cast<int64_t>(stack_off + k))});
            }
            if (k + 2 <= arg.byval_size) {
                emit(X86Op::Load16Z, {vr(scratch), vr(arg.lo),
                                      MOperand::make_imm(static_cast<int64_t>(k))});
                emit(X86Op::Store16,
                     {vr(scratch), pr(RSP),
                      MOperand::make_imm(static_cast<int64_t>(stack_off + k))});
                k += 2;
            }
            if (k < arg.byval_size) {
                emit(X86Op::Load8Z, {vr(scratch), vr(arg.lo),
                                     MOperand::make_imm(static_cast<int64_t>(k))});
                emit(X86Op::Store8,
                     {vr(scratch), pr(RSP),
                      MOperand::make_imm(static_cast<int64_t>(stack_off + k))});
            }
            stack_off += (arg.byval_size + 3) & ~uint32_t{3};
        } else if (arg.kind == CdeclArg::F80) {

            f80_push(arg.f80_src, loc);
            emit(X86Op::Fstp80,
                 {pr(RSP), MOperand::make_imm(static_cast<int64_t>(stack_off))});
            stack_off += 12;
        } else {
            emit(store_op_for(arg.type),
                 {vr(arg.lo), pr(RSP),
                  MOperand::make_imm(static_cast<int64_t>(stack_off))});
            stack_off += std::max<uint64_t>(4, scalar_size(arg.type));
        }
    }
    out_.max_outgoing_bytes = std::max<uint32_t>(
        out_.max_outgoing_bytes,
        static_cast<uint32_t>((stack_off + 15) & ~uint64_t{15}));

    if (indirect) {
        emit(X86Op::CallR, {vr(callee_vreg)});
    } else {
        emit(X86Op::CallS,
             {MOperand::make_symbol(callee_symbol, SymFlavor::Plain)});
    }

    if (sig.ret_class == air::RetClass::IndirectSret) {

        emit(X86Op::SubI32, {pr(RSP), MOperand::make_imm(4)});
    }

    if (sig.ret_class == air::RetClass::Scalar && inst.result.is_valid()) {
        if (legacy_i64(sig.ret_type)) {

            I64Halves r;
            r.lo = new_gpr();
            emit(X86Op::MovRR32, {vr(r.lo), pr(RAX)});
            r.hi = new_gpr();
            emit(X86Op::MovRR32, {vr(r.hi), pr(RDX)});
            i64_store(inst.result, r, loc);
        } else if (legacy_f80(sig.ret_type)) {

            f80_pop(inst.result, loc);
        } else if (is_fp_type(sig.ret_type)) {

            define(inst.result, fp_pop_st0(sig.ret_type), loc);
        } else {
            uint32_t result = new_gpr();
            emit(X86Op::MovRR32, {vr(result), pr(RAX)});
            define(inst.result, result, loc);
        }
    }
}

void ISel::lower_ret(const air::InstData& inst, air::InstId inst_id) {
    const air::SigData& sig = mod_.types().signature(func_.sig());
    std::span<const air::ValueId> ops = func_.operands(inst_id);
    switch (sig.ret_class) {
        case air::RetClass::Void:
            break;
        case air::RetClass::Scalar: {
            if (legacy32_ && is_f128(sig.ret_type)) {
                unsupported("IEEE-quad long double return in 32-bit mode",
                            inst.loc);
                return;
            }
            if (legacy_f80(sig.ret_type)) {

                f80_push(ops[0], inst.loc);
                break;
            }
            if (legacy_i64(sig.ret_type)) {

                I64Halves v = i64_load(ops[0], inst.loc);
                emit(X86Op::MovRR32, {pr(RAX), vr(v.lo)});
                emit(X86Op::MovRR32, {pr(RDX), vr(v.hi)});
                break;
            }
            uint32_t value = use_reg(ops[0], inst.loc);
            if (is_f80(sig.ret_type)) {

                f80_fld(f80_spill(value));
            } else if (is_fp_type(sig.ret_type)) {
                if (legacy32_) {

                    fp_push_st0(value, sig.ret_type);
                } else {
                    emit(X86Op::MovapsRR, {pr(XMM0), vr(value)});
                }
            } else {
                emit(is_wide(sig.ret_type) ? X86Op::MovRR64 : X86Op::MovRR32,
                     {pr(RAX), vr(value)});
            }
            break;
        }
        case air::RetClass::IntPair: {
            uint32_t buffer = use_reg(ops[0], inst.loc);
            emit(X86Op::MovRR64, {pr(R11), vr(buffer)});
            uint32_t next_int = 0;
            uint32_t next_sse = 0;
            for (int lane = 0; lane < 2; ++lane) {
                bool sse = (sig.ret_sse_mask >> lane) & 1;
                if (sse) {
                    emit(X86Op::LoadSD, {pr(xmm(next_sse++)), pr(R11),
                                         MOperand::make_imm(8 * lane)});
                } else {
                    emit(X86Op::Load64,
                         {pr(next_int++ == 0 ? RAX : RDX), pr(R11),
                          MOperand::make_imm(8 * lane)});
                }
            }
            break;
        }
        case air::RetClass::Hfa: {
            if (is_f128(sig.ret_type) || sig.ret_count > 2) {
                unsupported("this floating-point aggregate return", inst.loc);
                return;
            }
            uint32_t buffer = use_reg(ops[0], inst.loc);
            emit(X86Op::MovRR64, {pr(R11), vr(buffer)});
            bool wide = is_wide(sig.ret_type);
            int64_t element_size = wide ? 8 : 4;
            for (uint8_t lane = 0; lane < sig.ret_count; ++lane) {
                emit(wide ? X86Op::LoadSD : X86Op::LoadSS,
                     {pr(xmm(lane)), pr(R11),
                      MOperand::make_imm(lane * element_size)});
            }
            break;
        }
        case air::RetClass::IndirectSret: {

            if (has_sret_param_) {
                uint32_t pointer = use_reg(sret_param_, inst.loc);
                emit(legacy32_ ? X86Op::MovRR32 : X86Op::MovRR64,
                     {pr(RAX), vr(pointer)});
            }
            break;
        }
    }
    emit(X86Op::EpilogueRet, {});
}

uint32_t ISel::i64_frame(air::ValueId v, SrcLoc loc) {
    auto slot = slots_.find(v.index);
    if (slot == slots_.end()) {
        error("64-bit value has no frame slot in the fast tier", loc);
        return out_.new_frame_object(8, 8);
    }
    return slot->second.frame_index;
}

ISel::I64Halves ISel::i64_load(air::ValueId v, SrcLoc loc) {
    const air::ValueData& data = func_.value(v);
    I64Halves h;
    h.lo = new_gpr();
    h.hi = new_gpr();
    switch (data.kind) {
        case air::ValueKind::ConstInt: {
            uint64_t bits = data.payload;
            emit(X86Op::MovRI32,
                 {vr(h.lo),
                  MOperand::make_imm(static_cast<int64_t>(bits & 0xFFFFFFFFull))});
            emit(X86Op::MovRI32,
                 {vr(h.hi), MOperand::make_imm(
                                static_cast<int64_t>((bits >> 32) & 0xFFFFFFFFull))});
            break;
        }
        case air::ValueKind::ConstNull:
        case air::ValueKind::Undef:
            emit(X86Op::MovRI32, {vr(h.lo), MOperand::make_imm(0)});
            emit(X86Op::MovRI32, {vr(h.hi), MOperand::make_imm(0)});
            break;
        default: {
            uint32_t fi = i64_frame(v, loc);
            emit(X86Op::Load32,
                 {vr(h.lo), MOperand::make_frame(fi), MOperand::make_imm(0)});
            emit(X86Op::Load32,
                 {vr(h.hi), MOperand::make_frame(fi), MOperand::make_imm(4)});
            break;
        }
    }
    return h;
}

void ISel::i64_store(air::ValueId result, I64Halves h, SrcLoc loc) {
    uint32_t fi = i64_frame(result, loc);
    emit(X86Op::Store32,
         {vr(h.lo), MOperand::make_frame(fi), MOperand::make_imm(0)});
    emit(X86Op::Store32,
         {vr(h.hi), MOperand::make_frame(fi), MOperand::make_imm(4)});
}

void ISel::i64_helper_call(const char* name, air::ValueId a, air::ValueId b,
                           air::ValueId result, bool shift_count, SrcLoc loc) {
    if (out_.has_dynamic_stack) {
        unsupported("64-bit arithmetic in dynamic-stack frames in 32-bit mode",
                    loc);
        return;
    }

    I64Halves la = i64_load(a, loc);
    I64Halves lb = i64_load(b, loc);
    emit(X86Op::Store32, {vr(la.lo), pr(RSP), MOperand::make_imm(0)});
    emit(X86Op::Store32, {vr(la.hi), pr(RSP), MOperand::make_imm(4)});
    emit(X86Op::Store32, {vr(lb.lo), pr(RSP), MOperand::make_imm(8)});
    uint64_t total = 12;
    if (!shift_count) {
        emit(X86Op::Store32, {vr(lb.hi), pr(RSP), MOperand::make_imm(12)});
        total = 16;
    }
    out_.max_outgoing_bytes = std::max<uint32_t>(
        out_.max_outgoing_bytes, static_cast<uint32_t>((total + 15) & ~uint64_t{15}));
    emit(X86Op::CallS,
         {MOperand::make_symbol(sym_name(mod_.target(), name, false),
                                SymFlavor::Plain)});

    I64Halves r;
    r.lo = new_gpr();
    emit(X86Op::MovRR32, {vr(r.lo), pr(RAX)});
    r.hi = new_gpr();
    emit(X86Op::MovRR32, {vr(r.hi), pr(RDX)});
    i64_store(result, r, loc);
}

bool ISel::needs_i64_lowering(const air::InstData& inst,
                              air::InstId id) const {
    if (!legacy32_) {
        return false;
    }
    switch (inst.op) {
        case air::Opcode::Load:
        case air::Opcode::Store:
        case air::Opcode::Iadd:
        case air::Opcode::Isub:
        case air::Opcode::Imul:
        case air::Opcode::Iand:
        case air::Opcode::Ior:
        case air::Opcode::Ixor:
        case air::Opcode::Shl:
        case air::Opcode::Lshr:
        case air::Opcode::Ashr:
        case air::Opcode::Sdiv:
        case air::Opcode::Udiv:
        case air::Opcode::Srem:
        case air::Opcode::Urem:
        case air::Opcode::Icmp:
        case air::Opcode::Trunc:
        case air::Opcode::Zext:
        case air::Opcode::Sext:
        case air::Opcode::Select:
        case air::Opcode::Ptrtoint:
        case air::Opcode::Inttoptr:
        case air::Opcode::Bitcast:
        case air::Opcode::Bswap:
        case air::Opcode::Clz:
        case air::Opcode::Ctz:
        case air::Opcode::Popcnt:
        case air::Opcode::Fptosi:
        case air::Opcode::Fptoui:
        case air::Opcode::Sitofp:
        case air::Opcode::Uitofp:
            break;
        default:
            return false;
    }
    if (legacy_i64(inst.type)) {
        return true;
    }
    for (air::ValueId op : func_.operands(id)) {
        if (legacy_i64(func_.value_type(op))) {
            return true;
        }
    }
    return false;
}

void ISel::lower_i64_inst(air::InstId inst_id) {
    const air::InstData& inst = func_.inst(inst_id);
    std::span<const air::ValueId> ops = func_.operands(inst_id);
    SrcLoc loc = inst.loc;

    auto add_sub = [&](X86Op low, X86Op high) {
        I64Halves a = i64_load(ops[0], loc);
        I64Halves b = i64_load(ops[1], loc);
        emit(low, {vr(a.lo), vr(b.lo)});
        emit(high, {vr(a.hi), vr(b.hi)});
        i64_store(inst.result, a, loc);
    };

    auto bitwise = [&](X86Op op) {
        I64Halves a = i64_load(ops[0], loc);
        I64Halves b = i64_load(ops[1], loc);
        emit(op, {vr(a.lo), vr(b.lo)});
        emit(op, {vr(a.hi), vr(b.hi)});
        i64_store(inst.result, a, loc);
    };

    switch (inst.op) {
        case air::Opcode::Load: {
            MOperand base = mem_base(ops[0], loc);
            I64Halves h;
            h.lo = new_gpr();
            h.hi = new_gpr();
            emit(X86Op::Load32, {vr(h.lo), base, MOperand::make_imm(0)});
            emit(X86Op::Load32, {vr(h.hi), base, MOperand::make_imm(4)});
            i64_store(inst.result, h, loc);
            return;
        }
        case air::Opcode::Store: {
            I64Halves v = i64_load(ops[0], loc);
            MOperand base = mem_base(ops[1], loc);
            emit(X86Op::Store32, {vr(v.lo), base, MOperand::make_imm(0)});
            emit(X86Op::Store32, {vr(v.hi), base, MOperand::make_imm(4)});
            return;
        }
        case air::Opcode::Iadd: add_sub(X86Op::Add32, X86Op::Adc32); return;
        case air::Opcode::Isub: add_sub(X86Op::Sub32, X86Op::Sbb32); return;
        case air::Opcode::Iand: bitwise(X86Op::And32); return;
        case air::Opcode::Ior: bitwise(X86Op::Or32); return;
        case air::Opcode::Ixor: bitwise(X86Op::Xor32); return;
        case air::Opcode::Imul:
            i64_helper_call("__muldi3", ops[0], ops[1], inst.result, false, loc);
            return;
        case air::Opcode::Sdiv:
            i64_helper_call("__divdi3", ops[0], ops[1], inst.result, false, loc);
            return;
        case air::Opcode::Udiv:
            i64_helper_call("__udivdi3", ops[0], ops[1], inst.result, false, loc);
            return;
        case air::Opcode::Srem:
            i64_helper_call("__moddi3", ops[0], ops[1], inst.result, false, loc);
            return;
        case air::Opcode::Urem:
            i64_helper_call("__umoddi3", ops[0], ops[1], inst.result, false, loc);
            return;
        case air::Opcode::Shl:
            i64_helper_call("__ashldi3", ops[0], ops[1], inst.result, true, loc);
            return;
        case air::Opcode::Lshr:
            i64_helper_call("__lshrdi3", ops[0], ops[1], inst.result, true, loc);
            return;
        case air::Opcode::Ashr:
            i64_helper_call("__ashrdi3", ops[0], ops[1], inst.result, true, loc);
            return;
        case air::Opcode::Icmp: {
            uint8_t cond = inst.aux & 0xFF;
            if (cond <= 1) {

                I64Halves a = i64_load(ops[0], loc);
                I64Halves b = i64_load(ops[1], loc);
                emit(X86Op::Xor32, {vr(a.lo), vr(b.lo)});
                emit(X86Op::Xor32, {vr(a.hi), vr(b.hi)});
                emit(X86Op::Or32, {vr(a.lo), vr(a.hi)});
                uint32_t result = setcc_result(cond == 0 ? Cond::E : Cond::Ne);
                define(inst.result, result, loc);
                return;
            }

            bool swap = false;
            Cond cc = Cond::L;
            switch (cond) {
                case 2: swap = false; cc = Cond::L; break;
                case 3: swap = true;  cc = Cond::Ge; break;
                case 4: swap = true;  cc = Cond::L; break;
                case 5: swap = false; cc = Cond::Ge; break;
                case 6: swap = false; cc = Cond::B; break;
                case 7: swap = true;  cc = Cond::Ae; break;
                case 8: swap = true;  cc = Cond::B; break;
                case 9: swap = false; cc = Cond::Ae; break;
                default: unsupported("this 64-bit comparison", loc); return;
            }
            air::ValueId x = swap ? ops[1] : ops[0];
            air::ValueId y = swap ? ops[0] : ops[1];
            I64Halves lx = i64_load(x, loc);
            I64Halves ly = i64_load(y, loc);
            emit(X86Op::Sub32, {vr(lx.lo), vr(ly.lo)});
            emit(X86Op::Sbb32, {vr(lx.hi), vr(ly.hi)});
            uint32_t result = setcc_result(cc);
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::Trunc: {
            I64Halves v = i64_load(ops[0], loc);
            uint16_t width = int_width(inst.type);
            uint32_t result;
            if (width == 8) {
                result = new_gpr();
                emit(X86Op::Movzbl, {vr(result), vr(v.lo)});
            } else if (width == 16) {
                result = new_gpr();
                emit(X86Op::Movzwl, {vr(result), vr(v.lo)});
            } else {
                result = v.lo;
            }
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::Zext:
        case air::Opcode::Ptrtoint: {

            uint32_t src = use_reg(ops[0], loc);
            uint16_t from = inst.op == air::Opcode::Ptrtoint
                                ? 32
                                : int_width(func_.value_type(ops[0]));
            I64Halves h;
            h.lo = new_gpr();
            h.hi = new_gpr();
            if (from == 8) {
                emit(X86Op::Movzbl, {vr(h.lo), vr(src)});
            } else if (from == 16) {
                emit(X86Op::Movzwl, {vr(h.lo), vr(src)});
            } else {
                emit(X86Op::MovRR32, {vr(h.lo), vr(src)});
            }
            emit(X86Op::MovRI32, {vr(h.hi), MOperand::make_imm(0)});
            i64_store(inst.result, h, loc);
            return;
        }
        case air::Opcode::Sext: {
            uint32_t src = use_reg(ops[0], loc);
            uint16_t from = int_width(func_.value_type(ops[0]));
            I64Halves h;
            h.lo = new_gpr();
            h.hi = new_gpr();
            if (from == 8) {
                emit(X86Op::Movsbl, {vr(h.lo), vr(src)});
            } else if (from == 16) {
                emit(X86Op::Movswl, {vr(h.lo), vr(src)});
            } else {
                emit(X86Op::MovRR32, {vr(h.lo), vr(src)});
            }
            emit(X86Op::MovRR32, {vr(h.hi), vr(h.lo)});
            emit(X86Op::SarI32, {vr(h.hi), MOperand::make_imm(31)});
            i64_store(inst.result, h, loc);
            return;
        }
        case air::Opcode::Inttoptr: {

            I64Halves v = i64_load(ops[0], loc);
            define(inst.result, v.lo, loc);
            return;
        }
        case air::Opcode::Select: {
            I64Halves la = i64_load(ops[1], loc);
            I64Halves lb = i64_load(ops[2], loc);
            uint32_t rlo = new_gpr();
            uint32_t rhi = new_gpr();
            emit(X86Op::MovRR32, {vr(rlo), vr(la.lo)});
            emit(X86Op::MovRR32, {vr(rhi), vr(la.hi)});
            emit_truth_test(ops[0], loc);
            emit(X86Op::Cmov32, {vr(rlo), vr(lb.lo)},
                 static_cast<uint32_t>(Cond::E));
            emit(X86Op::Cmov32, {vr(rhi), vr(lb.hi)},
                 static_cast<uint32_t>(Cond::E));
            i64_store(inst.result, {rlo, rhi}, loc);
            return;
        }
        case air::Opcode::Sitofp:
        case air::Opcode::Uitofp: {

            if (is_f80(inst.type) || is_f128(inst.type)) {
                unsupported("64-bit integer to long double in 32-bit mode", loc);
                return;
            }
            if (out_.has_dynamic_stack) {
                unsupported("64-bit conversions in dynamic-stack frames in "
                            "32-bit mode",
                            loc);
                return;
            }
            bool is_signed = inst.op == air::Opcode::Sitofp;
            bool to_double = is_wide(inst.type);
            const char* name =
                is_signed ? (to_double ? "__floatdidf" : "__floatdisf")
                          : (to_double ? "__floatundidf" : "__floatundisf");
            I64Halves v = i64_load(ops[0], loc);
            emit(X86Op::Store32, {vr(v.lo), pr(RSP), MOperand::make_imm(0)});
            emit(X86Op::Store32, {vr(v.hi), pr(RSP), MOperand::make_imm(4)});
            out_.max_outgoing_bytes =
                std::max<uint32_t>(out_.max_outgoing_bytes, 16);
            emit(X86Op::CallS,
                 {MOperand::make_symbol(sym_name(mod_.target(), name, false),
                                        SymFlavor::Plain)});
            define(inst.result, fp_pop_st0(inst.type), loc);
            return;
        }
        case air::Opcode::Fptosi:
        case air::Opcode::Fptoui: {

            air::TypeId src_type = func_.value_type(ops[0]);
            if (is_f80(src_type) || is_f128(src_type)) {
                unsupported("long double to 64-bit integer in 32-bit mode", loc);
                return;
            }
            if (out_.has_dynamic_stack) {
                unsupported("64-bit conversions in dynamic-stack frames in "
                            "32-bit mode",
                            loc);
                return;
            }
            bool is_signed = inst.op == air::Opcode::Fptosi;
            bool from_double = is_wide(src_type);
            const char* name =
                is_signed ? (from_double ? "__fixdfdi" : "__fixsfdi")
                          : (from_double ? "__fixunsdfdi" : "__fixunssfdi");
            uint32_t src = use_reg(ops[0], loc);
            emit(from_double ? X86Op::StoreSD : X86Op::StoreSS,
                 {vr(src), pr(RSP), MOperand::make_imm(0)});
            out_.max_outgoing_bytes =
                std::max<uint32_t>(out_.max_outgoing_bytes, 16);
            emit(X86Op::CallS,
                 {MOperand::make_symbol(sym_name(mod_.target(), name, false),
                                        SymFlavor::Plain)});
            I64Halves r;
            r.lo = new_gpr();
            emit(X86Op::MovRR32, {vr(r.lo), pr(RAX)});
            r.hi = new_gpr();
            emit(X86Op::MovRR32, {vr(r.hi), pr(RDX)});
            i64_store(inst.result, r, loc);
            return;
        }
        default:
            unsupported("this 64-bit operation in 32-bit mode", loc);
            return;
    }
}

uint32_t ISel::f80_frame(air::ValueId v, SrcLoc loc) {
    auto slot = slots_.find(v.index);
    if (slot == slots_.end()) {
        error("long double value has no frame slot in the fast tier", loc);
        return out_.new_frame_object(12, 4);
    }
    return slot->second.frame_index;
}

void ISel::f80_push(air::ValueId v, SrcLoc loc) {
    const air::ValueData& data = func_.value(v);
    if (data.kind == air::ValueKind::ConstFloat ||
        data.kind == air::ValueKind::ConstNull ||
        data.kind == air::ValueKind::Undef) {

        uint64_t lo = data.kind == air::ValueKind::ConstFloat ? data.payload : 0;
        uint64_t hi = data.kind == air::ValueKind::ConstFloat ? data.payload2 : 0;
        uint32_t slot = out_.new_frame_object(12, 4);
        uint32_t r0 = materialize_int(lo & 0xFFFFFFFFull, false);
        emit(X86Op::Store32,
             {vr(r0), MOperand::make_frame(slot), MOperand::make_imm(0)});
        uint32_t r1 = materialize_int((lo >> 32) & 0xFFFFFFFFull, false);
        emit(X86Op::Store32,
             {vr(r1), MOperand::make_frame(slot), MOperand::make_imm(4)});
        uint32_t r2 = materialize_int(hi & 0xFFFFull, false);
        emit(X86Op::Store16,
             {vr(r2), MOperand::make_frame(slot), MOperand::make_imm(8)});
        emit(X86Op::Fld80,
             {MOperand::make_frame(slot), MOperand::make_imm(0)});
        return;
    }
    uint32_t fi = f80_frame(v, loc);
    emit(X86Op::Fld80, {MOperand::make_frame(fi), MOperand::make_imm(0)});
}

void ISel::f80_pop(air::ValueId result, SrcLoc loc) {
    uint32_t fi = f80_frame(result, loc);
    emit(X86Op::Fstp80, {MOperand::make_frame(fi), MOperand::make_imm(0)});
}

bool ISel::needs_f80_lowering(const air::InstData& inst, air::InstId id) const {
    if (!legacy32_) {
        return false;
    }
    switch (inst.op) {
        case air::Opcode::Load:
        case air::Opcode::Store:
        case air::Opcode::Fadd:
        case air::Opcode::Fsub:
        case air::Opcode::Fmul:
        case air::Opcode::Fdiv:
        case air::Opcode::Fneg:
        case air::Opcode::Fpext:
        case air::Opcode::Fptrunc:
        case air::Opcode::Fptosi:
        case air::Opcode::Fptoui:
        case air::Opcode::Sitofp:
        case air::Opcode::Uitofp:
        case air::Opcode::Select:
            break;
        default:
            return false;
    }
    if (legacy_f80(inst.type)) {
        return true;
    }
    for (air::ValueId op : func_.operands(id)) {
        if (legacy_f80(func_.value_type(op))) {
            return true;
        }
    }
    return false;
}

void ISel::lower_f80_inst(air::InstId inst_id) {
    const air::InstData& inst = func_.inst(inst_id);
    std::span<const air::ValueId> ops = func_.operands(inst_id);
    SrcLoc loc = inst.loc;

    switch (inst.op) {
        case air::Opcode::Fadd:
        case air::Opcode::Fsub:
        case air::Opcode::Fmul:
        case air::Opcode::Fdiv: {

            f80_push(ops[0], loc);
            f80_push(ops[1], loc);
            X86Op fpu = inst.op == air::Opcode::Fadd   ? X86Op::Faddp
                        : inst.op == air::Opcode::Fsub ? X86Op::Fsubp
                        : inst.op == air::Opcode::Fmul ? X86Op::Fmulp
                                                       : X86Op::Fdivp;
            emit(fpu, {});
            f80_pop(inst.result, loc);
            return;
        }
        case air::Opcode::Fneg:
            f80_push(ops[0], loc);
            emit(X86Op::Fchs, {});
            f80_pop(inst.result, loc);
            return;
        case air::Opcode::Load: {
            MOperand base = mem_base(ops[0], loc);
            emit(X86Op::Fld80, {base, MOperand::make_imm(0)});
            f80_pop(inst.result, loc);
            return;
        }
        case air::Opcode::Store: {
            f80_push(ops[0], loc);
            MOperand base = mem_base(ops[1], loc);
            emit(X86Op::Fstp80, {base, MOperand::make_imm(0)});
            return;
        }
        case air::Opcode::Fpext: {

            air::TypeId src_type = func_.value_type(ops[0]);
            bool from_wide = is_wide(src_type);
            uint32_t src = use_reg(ops[0], loc);
            uint32_t slot = out_.new_frame_object(8, 8);
            emit(from_wide ? X86Op::StoreSD : X86Op::StoreSS,
                 {vr(src), MOperand::make_frame(slot), MOperand::make_imm(0)});
            emit(from_wide ? X86Op::FldM64 : X86Op::FldM32,
                 {MOperand::make_frame(slot), MOperand::make_imm(0)});
            f80_pop(inst.result, loc);
            return;
        }
        case air::Opcode::Fptrunc: {

            bool to_wide = is_wide(inst.type);
            f80_push(ops[0], loc);
            uint32_t slot = out_.new_frame_object(8, 8);
            emit(to_wide ? X86Op::FstpM64 : X86Op::FstpM32,
                 {MOperand::make_frame(slot), MOperand::make_imm(0)});
            uint32_t result = new_fpr();
            emit(to_wide ? X86Op::LoadSD : X86Op::LoadSS,
                 {vr(result), MOperand::make_frame(slot), MOperand::make_imm(0)});
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::Sitofp:
        case air::Opcode::Uitofp: {

            air::TypeId src_type = func_.value_type(ops[0]);
            bool is_signed = inst.op == air::Opcode::Sitofp;
            uint32_t slot = out_.new_frame_object(8, 8);
            bool from_i64 = legacy_i64(src_type);
            if (from_i64) {
                I64Halves v = i64_load(ops[0], loc);
                emit(X86Op::Store32,
                     {vr(v.lo), MOperand::make_frame(slot), MOperand::make_imm(0)});
                emit(X86Op::Store32,
                     {vr(v.hi), MOperand::make_frame(slot), MOperand::make_imm(4)});
                emit(X86Op::FildM64,
                     {MOperand::make_frame(slot), MOperand::make_imm(0)});
                if (!is_signed) {

                    uint32_t two64 = out_.new_frame_object(12, 4);
                    uint32_t zero = out_.new_frame_object(12, 4);

                    uint32_t m0 = materialize_int(0, false);
                    uint32_t m1 = materialize_int(0x80000000u, false);
                    uint32_t e = materialize_int(0x403Fu, false);
                    emit(X86Op::Store32, {vr(m0), MOperand::make_frame(two64),
                                          MOperand::make_imm(0)});
                    emit(X86Op::Store32, {vr(m1), MOperand::make_frame(two64),
                                          MOperand::make_imm(4)});
                    emit(X86Op::Store16, {vr(e), MOperand::make_frame(two64),
                                          MOperand::make_imm(8)});
                    uint32_t z = materialize_int(0, false);
                    emit(X86Op::Store32, {vr(z), MOperand::make_frame(zero),
                                          MOperand::make_imm(0)});
                    emit(X86Op::Store32, {vr(z), MOperand::make_frame(zero),
                                          MOperand::make_imm(4)});
                    emit(X86Op::Store16, {vr(z), MOperand::make_frame(zero),
                                          MOperand::make_imm(8)});
                    uint32_t two64_addr = new_gpr();
                    emit(X86Op::FrameAddr,
                         {vr(two64_addr), MOperand::make_frame(two64)});
                    uint32_t zero_addr = new_gpr();
                    emit(X86Op::FrameAddr,
                         {vr(zero_addr), MOperand::make_frame(zero)});
                    uint32_t chosen = two_address_result(zero_addr, false, false);

                    uint32_t hi = new_gpr();
                    emit(X86Op::Load32, {vr(hi), MOperand::make_frame(slot),
                                         MOperand::make_imm(4)});
                    emit(X86Op::Test32, {vr(hi), vr(hi)});
                    emit(X86Op::Cmov32, {vr(chosen), vr(two64_addr)},
                         static_cast<uint32_t>(Cond::S));
                    emit(X86Op::Fld80, {vr(chosen), MOperand::make_imm(0)});
                    emit(X86Op::Faddp, {});
                }
                f80_pop(inst.result, loc);
                return;
            }

            uint32_t src = use_reg(ops[0], loc);
            uint16_t from = int_width(src_type);
            if (is_signed) {
                if (from == 8) {
                    uint32_t ext = new_gpr();
                    emit(X86Op::Movsbl, {vr(ext), vr(src)});
                    src = ext;
                } else if (from == 16) {
                    uint32_t ext = new_gpr();
                    emit(X86Op::Movswl, {vr(ext), vr(src)});
                    src = ext;
                }
                emit(X86Op::Store32,
                     {vr(src), MOperand::make_frame(slot), MOperand::make_imm(0)});
                emit(X86Op::FildM32,
                     {MOperand::make_frame(slot), MOperand::make_imm(0)});
            } else {

                if (from == 8) {
                    uint32_t ext = new_gpr();
                    emit(X86Op::Movzbl, {vr(ext), vr(src)});
                    src = ext;
                } else if (from == 16) {
                    uint32_t ext = new_gpr();
                    emit(X86Op::Movzwl, {vr(ext), vr(src)});
                    src = ext;
                }
                uint32_t z = materialize_int(0, false);
                emit(X86Op::Store32,
                     {vr(src), MOperand::make_frame(slot), MOperand::make_imm(0)});
                emit(X86Op::Store32,
                     {vr(z), MOperand::make_frame(slot), MOperand::make_imm(4)});
                emit(X86Op::FildM64,
                     {MOperand::make_frame(slot), MOperand::make_imm(0)});
            }
            f80_pop(inst.result, loc);
            return;
        }
        case air::Opcode::Fptosi:
        case air::Opcode::Fptoui: {

            f80_push(ops[0], loc);
            uint32_t slot = out_.new_frame_object(8, 8);
            emit(X86Op::FisttpM64,
                 {MOperand::make_frame(slot), MOperand::make_imm(0)});
            if (legacy_i64(inst.type)) {
                I64Halves r;
                r.lo = new_gpr();
                emit(X86Op::Load32, {vr(r.lo), MOperand::make_frame(slot),
                                     MOperand::make_imm(0)});
                r.hi = new_gpr();
                emit(X86Op::Load32, {vr(r.hi), MOperand::make_frame(slot),
                                     MOperand::make_imm(4)});
                i64_store(inst.result, r, loc);
            } else {
                uint32_t result = new_gpr();
                emit(X86Op::Load32, {vr(result), MOperand::make_frame(slot),
                                     MOperand::make_imm(0)});
                mask_subword(inst.type, result);
                define(inst.result, result, loc);
            }
            return;
        }
        case air::Opcode::Select: {

            uint32_t lhs_addr = new_gpr();
            emit(X86Op::FrameAddr,
                 {vr(lhs_addr), MOperand::make_frame(f80_frame(ops[1], loc))});
            uint32_t rhs_addr = new_gpr();
            emit(X86Op::FrameAddr,
                 {vr(rhs_addr), MOperand::make_frame(f80_frame(ops[2], loc))});
            uint32_t chosen = two_address_result(lhs_addr, false, false);
            emit_truth_test(ops[0], loc);
            emit(X86Op::Cmov32, {vr(chosen), vr(rhs_addr)},
                 static_cast<uint32_t>(Cond::E));
            emit(X86Op::Fld80, {vr(chosen), MOperand::make_imm(0)});
            f80_pop(inst.result, loc);
            return;
        }
        default:
            unsupported("this long double operation in 32-bit mode", loc);
            return;
    }
}

void ISel::lower_inst(air::InstId inst_id) {
    const air::InstData& inst = func_.inst(inst_id);

    if (needs_f80_lowering(inst, inst_id)) {
        lower_f80_inst(inst_id);
        return;
    }
    if (needs_i64_lowering(inst, inst_id)) {
        lower_i64_inst(inst_id);
        return;
    }
    std::span<const air::ValueId> ops = func_.operands(inst_id);
    SrcLoc loc = inst.loc;

    auto binary_int = [&](X86Op op32, X86Op op64, bool remask) {
        uint32_t lhs = use_reg(ops[0], loc);
        uint32_t rhs = use_reg(ops[1], loc);
        bool wide = is_wide(inst.type);
        uint32_t result = two_address_result(lhs, wide, /*fp=*/false);
        emit(wide ? op64 : op32, {vr(result), vr(rhs)});
        if (remask) {
            mask_subword(inst.type, result);
        }
        define(inst.result, result, loc);
    };
    auto binary_fp = [&](X86Op op_ss, X86Op op_sd) {
        uint32_t lhs = use_reg(ops[0], loc);
        uint32_t rhs = use_reg(ops[1], loc);
        bool wide = is_wide(inst.type);
        uint32_t result = two_address_result(lhs, wide, /*fp=*/true);
        emit(wide ? op_sd : op_ss, {vr(result), vr(rhs)});
        define(inst.result, result, loc);
    };
    auto shift = [&](X86Op op32, X86Op op64, bool remask) {
        uint32_t lhs = use_reg(ops[0], loc);
        uint32_t amount = use_reg(ops[1], loc);
        bool wide = is_wide(inst.type);
        uint32_t result = two_address_result(lhs, wide, /*fp=*/false);
        emit(X86Op::MovRR32, {pr(RCX), vr(amount)});
        emit(wide ? op64 : op32, {vr(result), pr(RCX)});
        if (remask) {
            mask_subword(inst.type, result);
        }
        define(inst.result, result, loc);
    };
    auto divide = [&](bool is_signed, bool want_remainder) {
        uint32_t lhs = use_reg(ops[0], loc);
        uint32_t rhs = use_reg(ops[1], loc);
        bool wide = is_wide(inst.type);
        emit(wide ? X86Op::MovRR64 : X86Op::MovRR32, {pr(RAX), vr(lhs)});
        if (is_signed) {
            emit(wide ? X86Op::Cqo : X86Op::Cdq, {pr(RDX), pr(RAX)});
        } else {
            emit(X86Op::MovRI32, {pr(RDX), MOperand::make_imm(0)});
        }
        X86Op div = wide ? (is_signed ? X86Op::Idiv64 : X86Op::Udiv64)
                         : (is_signed ? X86Op::Idiv32 : X86Op::Udiv32);
        emit(div, {vr(rhs), pr(RAX), pr(RDX)});
        uint32_t result = new_gpr();
        emit(wide ? X86Op::MovRR64 : X86Op::MovRR32,
             {vr(result), pr(want_remainder ? RDX : RAX)});
        define(inst.result, result, loc);
    };

    switch (inst.op) {
        case air::Opcode::StackAlloc:

            return;
        case air::Opcode::Load: {
            if (!check_scalar(inst.type, loc)) {
                return;
            }
            uint32_t result = new_reg_for(inst.type);
            MInst load;
            load.opcode = op(load_op_for(inst.type));
            load.operands.push_back(vr(result));
            load.operands.push_back(mem_base(ops[0], loc));
            load.operands.push_back(MOperand::make_imm(0));
            cur().insts.push_back(std::move(load));
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::Store: {
            air::TypeId value_type = func_.value_type(ops[0]);
            if (!check_scalar(value_type, loc)) {
                return;
            }
            uint32_t value = use_reg(ops[0], loc);
            MInst store;
            store.opcode = op(store_op_for(value_type));
            store.operands.push_back(vr(value));
            store.operands.push_back(mem_base(ops[1], loc));
            store.operands.push_back(MOperand::make_imm(0));
            cur().insts.push_back(std::move(store));
            return;
        }
        case air::Opcode::Memcpy:
        case air::Opcode::Memmove:
        case air::Opcode::Memset: {
            uint32_t dst = use_reg(ops[0], loc);
            uint32_t src = use_reg(ops[1], loc);
            uint32_t size = use_reg(ops[2], loc);
            const char* callee = inst.op == air::Opcode::Memcpy ? "memcpy"
                                 : inst.op == air::Opcode::Memmove ? "memmove"
                                                                   : "memset";
            if (legacy32_) {

                emit(X86Op::Store32, {vr(dst), pr(RSP), MOperand::make_imm(0)});
                emit(X86Op::Store32, {vr(src), pr(RSP), MOperand::make_imm(4)});
                emit(X86Op::Store32, {vr(size), pr(RSP), MOperand::make_imm(8)});
                out_.max_outgoing_bytes =
                    std::max<uint32_t>(out_.max_outgoing_bytes, 16);
                emit(X86Op::CallS,
                     {MOperand::make_symbol(sym_name(mod_.target(), callee, false),
                                            SymFlavor::Plain)});
                return;
            }
            emit(X86Op::MovRR64, {pr(RDI), vr(dst)});
            emit(inst.op == air::Opcode::Memset ? X86Op::MovRR32
                                                : X86Op::MovRR64,
                 {pr(RSI), vr(src)});
            emit(X86Op::MovRR64, {pr(RDX), vr(size)});
            emit(X86Op::CallS,
                 {MOperand::make_symbol(sym_name(mod_.target(), callee, false),
                                        SymFlavor::Plain)});
            return;
        }

        case air::Opcode::Iadd: binary_int(X86Op::Add32, X86Op::Add64, true); return;
        case air::Opcode::Isub: binary_int(X86Op::Sub32, X86Op::Sub64, true); return;
        case air::Opcode::Imul: binary_int(X86Op::Imul32, X86Op::Imul64, true); return;
        case air::Opcode::Iand: binary_int(X86Op::And32, X86Op::And64, false); return;
        case air::Opcode::Ior: binary_int(X86Op::Or32, X86Op::Or64, false); return;
        case air::Opcode::Ixor: binary_int(X86Op::Xor32, X86Op::Xor64, false); return;
        case air::Opcode::Shl: shift(X86Op::ShlCl32, X86Op::ShlCl64, true); return;
        case air::Opcode::Lshr: shift(X86Op::ShrCl32, X86Op::ShrCl64, false); return;
        case air::Opcode::Ashr: shift(X86Op::SarCl32, X86Op::SarCl64, false); return;
        case air::Opcode::Sdiv: divide(true, false); return;
        case air::Opcode::Udiv: divide(false, false); return;
        case air::Opcode::Srem: divide(true, true); return;
        case air::Opcode::Urem: divide(false, true); return;

        case air::Opcode::Fadd:
        case air::Opcode::Fsub:
        case air::Opcode::Fmul:
        case air::Opcode::Fdiv: {
            if (!check_scalar(inst.type, loc)) {
                return;
            }
            if (is_f80(inst.type)) {
                uint32_t lhs = use_reg(ops[0], loc);
                uint32_t rhs = use_reg(ops[1], loc);
                uint32_t lhs_slot = f80_spill(lhs);
                uint32_t rhs_slot = f80_spill(rhs);
                f80_fld(lhs_slot);
                f80_fld(rhs_slot);
                X86Op fpu = inst.op == air::Opcode::Fadd   ? X86Op::Faddp
                            : inst.op == air::Opcode::Fsub ? X86Op::Fsubp
                            : inst.op == air::Opcode::Fmul ? X86Op::Fmulp
                                                           : X86Op::Fdivp;
                emit(fpu, {});
                define(inst.result, f80_pop_result(), loc);
                return;
            }
            switch (inst.op) {
                case air::Opcode::Fadd: binary_fp(X86Op::AddSS, X86Op::AddSD); break;
                case air::Opcode::Fsub: binary_fp(X86Op::SubSS, X86Op::SubSD); break;
                case air::Opcode::Fmul: binary_fp(X86Op::MulSS, X86Op::MulSD); break;
                default: binary_fp(X86Op::DivSS, X86Op::DivSD); break;
            }
            return;
        }
        case air::Opcode::Fneg: {
            if (!check_scalar(inst.type, loc)) {
                return;
            }
            if (is_f80(inst.type)) {
                uint32_t src = use_reg(ops[0], loc);
                f80_fld(f80_spill(src));
                emit(X86Op::Fchs, {});
                define(inst.result, f80_pop_result(), loc);
                return;
            }

            bool wide = is_wide(inst.type);
            uint32_t mask = materialize_fp_bits(
                wide ? 0x8000000000000000ull : 0x80000000ull, wide);
            uint32_t src = use_reg(ops[0], loc);
            uint32_t result = two_address_result(src, wide, /*fp=*/true);
            emit(X86Op::XorpsRR, {vr(result), vr(mask)});
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::Frem:
            unsupported("floating-point remainder", loc);
            return;

        case air::Opcode::Icmp: lower_icmp(inst, inst_id); return;
        case air::Opcode::Fcmp: lower_fcmp(inst, inst_id); return;

        case air::Opcode::Trunc: {
            uint32_t src = use_reg(ops[0], loc);
            uint16_t width = int_width(inst.type);
            uint32_t result = new_gpr();
            if (width == 8) {
                emit(X86Op::Movzbl, {vr(result), vr(src)});
            } else if (width == 16) {
                emit(X86Op::Movzwl, {vr(result), vr(src)});
            } else {
                emit(X86Op::MovRR32, {vr(result), vr(src)});
            }
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::Zext: {
            uint32_t src = use_reg(ops[0], loc);
            uint16_t from = int_width(func_.value_type(ops[0]));
            uint32_t result = new_gpr();
            if (from == 8) {
                emit(X86Op::Movzbl, {vr(result), vr(src)});
            } else if (from == 16) {
                emit(X86Op::Movzwl, {vr(result), vr(src)});
            } else {
                emit(X86Op::MovRR32, {vr(result), vr(src)});
            }
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::Sext: {
            uint32_t src = use_reg(ops[0], loc);
            uint16_t from = int_width(func_.value_type(ops[0]));
            bool wide = is_wide(inst.type);
            uint32_t result = new_gpr();
            if (from == 8) {
                emit(wide ? X86Op::Movsbq : X86Op::Movsbl, {vr(result), vr(src)});
            } else if (from == 16) {
                emit(wide ? X86Op::Movswq : X86Op::Movswl, {vr(result), vr(src)});
            } else if (from == 32 && wide) {
                emit(X86Op::Movslq, {vr(result), vr(src)});
            } else {
                emit(X86Op::MovRR32, {vr(result), vr(src)});
            }
            if (!wide) {
                mask_subword(inst.type, result);
            }
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::Fptrunc: {
            air::TypeId src_type = func_.value_type(ops[0]);
            if (!check_scalar(src_type, loc)) {
                return;
            }
            uint32_t src = use_reg(ops[0], loc);
            if (is_f80(src_type)) {
                bool to_wide = is_wide(inst.type);
                f80_fld(f80_spill(src));
                uint32_t slot = out_.new_frame_object(8, 8);
                emit(to_wide ? X86Op::FstpM64 : X86Op::FstpM32,
                     {MOperand::make_frame(slot), MOperand::make_imm(0)});
                uint32_t result = new_fpr();
                emit(to_wide ? X86Op::LoadSD : X86Op::LoadSS,
                     {vr(result), MOperand::make_frame(slot),
                      MOperand::make_imm(0)});
                define(inst.result, result, loc);
                return;
            }
            uint32_t result = new_fpr();
            emit(X86Op::CvtSD2SS, {vr(result), vr(src)});
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::Fpext: {
            if (!check_scalar(inst.type, loc)) {
                return;
            }
            uint32_t src = use_reg(ops[0], loc);
            if (is_f80(inst.type)) {
                bool from_wide = is_wide(func_.value_type(ops[0]));
                uint32_t slot = out_.new_frame_object(8, 8);
                emit(from_wide ? X86Op::StoreSD : X86Op::StoreSS,
                     {vr(src), MOperand::make_frame(slot),
                      MOperand::make_imm(0)});
                emit(from_wide ? X86Op::FldM64 : X86Op::FldM32,
                     {MOperand::make_frame(slot), MOperand::make_imm(0)});
                define(inst.result, f80_pop_result(), loc);
                return;
            }
            uint32_t result = new_fpr();
            emit(X86Op::CvtSS2SD, {vr(result), vr(src)});
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::Fptosi:
        case air::Opcode::Fptoui: {
            air::TypeId src_type = func_.value_type(ops[0]);
            if (!check_scalar(src_type, loc)) {
                return;
            }
            if (is_f80(src_type)) {

                uint32_t src = use_reg(ops[0], loc);
                f80_fld(f80_spill(src));
                uint32_t slot = out_.new_frame_object(8, 8);
                emit(X86Op::FisttpM64,
                     {MOperand::make_frame(slot), MOperand::make_imm(0)});
                uint32_t value = new_gpr();
                emit(X86Op::Load64,
                     {vr(value), MOperand::make_frame(slot),
                      MOperand::make_imm(0)});
                bool dst_wide = is_wide(inst.type);
                uint32_t result = value;
                if (!dst_wide) {
                    result = new_gpr();
                    emit(X86Op::MovRR32, {vr(result), vr(value)});
                    mask_subword(inst.type, result);
                }
                define(inst.result, result, loc);
                return;
            }
            bool src_wide = is_wide(src_type);
            bool dst_wide = is_wide(inst.type);
            uint32_t src = use_reg(ops[0], loc);
            if (legacy32_ && inst.op == air::Opcode::Fptoui) {

                if (out_.has_dynamic_stack) {
                    unsupported("floating-point conversions in dynamic-stack "
                                "frames in 32-bit mode",
                                loc);
                    return;
                }
                const char* name = src_wide ? "__fixunsdfsi" : "__fixunssfsi";
                emit(src_wide ? X86Op::StoreSD : X86Op::StoreSS,
                     {vr(src), pr(RSP), MOperand::make_imm(0)});
                out_.max_outgoing_bytes =
                    std::max<uint32_t>(out_.max_outgoing_bytes, 16);
                emit(X86Op::CallS,
                     {MOperand::make_symbol(sym_name(mod_.target(), name, false),
                                            SymFlavor::Plain)});
                uint32_t result = new_gpr();
                emit(X86Op::MovRR32, {vr(result), pr(RAX)});
                mask_subword(inst.type, result);
                define(inst.result, result, loc);
                return;
            }
            if (inst.op == air::Opcode::Fptosi || !dst_wide) {

                bool cvt_wide = inst.op == air::Opcode::Fptoui || dst_wide;
                X86Op cvt = src_wide
                    ? (cvt_wide ? X86Op::Cvttsd2si64 : X86Op::Cvttsd2si32)
                    : (cvt_wide ? X86Op::Cvttss2si64 : X86Op::Cvttss2si32);
                uint32_t value = new_gpr();
                emit(cvt, {vr(value), vr(src)});
                uint32_t result = value;
                if (cvt_wide && !dst_wide) {
                    result = new_gpr();
                    emit(X86Op::MovRR32, {vr(result), vr(value)});
                }
                if (!dst_wide) {
                    mask_subword(inst.type, result);
                }
                define(inst.result, result, loc);
                return;
            }

            uint64_t threshold_bits =
                src_wide ? 0x43E0000000000000ull : 0x5F000000ull;
            uint32_t threshold = materialize_fp_bits(threshold_bits, src_wide);
            uint32_t shifted = two_address_result(src, src_wide, /*fp=*/true);
            emit(src_wide ? X86Op::SubSD : X86Op::SubSS,
                 {vr(shifted), vr(threshold)});
            uint32_t high = new_gpr();
            emit(src_wide ? X86Op::Cvttsd2si64 : X86Op::Cvttss2si64,
                 {vr(high), vr(shifted)});
            uint32_t sign_bit = new_gpr();
            emit(X86Op::MovAbs64,
                 {vr(sign_bit),
                  MOperand::make_imm(static_cast<int64_t>(0x8000000000000000ull))});
            uint32_t folded = new_gpr();
            emit(X86Op::MovRR64, {vr(folded), vr(high)});
            emit(X86Op::Xor64, {vr(folded), vr(sign_bit)});
            uint32_t low = new_gpr();
            emit(src_wide ? X86Op::Cvttsd2si64 : X86Op::Cvttss2si64,
                 {vr(low), vr(src)});
            uint32_t result = new_gpr();
            emit(X86Op::MovRR64, {vr(result), vr(low)});
            emit(src_wide ? X86Op::Ucomisd : X86Op::Ucomiss,
                 {vr(src), vr(threshold)});
            emit(X86Op::Cmov64, {vr(result), vr(folded)},
                 static_cast<uint32_t>(Cond::Ae));
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::Sitofp:
        case air::Opcode::Uitofp: {
            if (!check_scalar(inst.type, loc)) {
                return;
            }
            air::TypeId src_type = func_.value_type(ops[0]);
            uint32_t src = use_reg(ops[0], loc);
            bool is_signed = inst.op == air::Opcode::Sitofp;
            uint16_t from = int_width(src_type);
            bool dst_wide = is_wide(inst.type);
            if (is_f80(inst.type)) {
                if (is_signed && (from == 8 || from == 16)) {
                    uint32_t extended = new_gpr();
                    emit(from == 8 ? X86Op::Movsbl : X86Op::Movswl,
                         {vr(extended), vr(src)});
                    src = extended;
                    from = 32;
                }
                uint32_t slot = out_.new_frame_object(8, 8);
                if (is_signed && from <= 32) {
                    emit(X86Op::Store32,
                         {vr(src), MOperand::make_frame(slot),
                          MOperand::make_imm(0)});
                    emit(X86Op::FildM32,
                         {MOperand::make_frame(slot), MOperand::make_imm(0)});
                } else {

                    emit(X86Op::Store64,
                         {vr(src), MOperand::make_frame(slot),
                          MOperand::make_imm(0)});
                    emit(X86Op::FildM64,
                         {MOperand::make_frame(slot), MOperand::make_imm(0)});
                    if (!is_signed && from > 32) {

                        uint32_t table = out_.new_frame_object(16, 8);
                        uint32_t zero = materialize_int(0, true);
                        emit(X86Op::Store64,
                             {vr(zero), MOperand::make_frame(table),
                              MOperand::make_imm(0)});
                        uint32_t two64 =
                            materialize_int(0x43F0000000000000ull, true);
                        emit(X86Op::Store64,
                             {vr(two64), MOperand::make_frame(table),
                              MOperand::make_imm(8)});
                        uint32_t index =
                            two_address_result(src, /*wide=*/true, false);
                        emit(X86Op::ShrI64,
                             {vr(index), MOperand::make_imm(63)});
                        emit(X86Op::ShlI64,
                             {vr(index), MOperand::make_imm(3)});
                        uint32_t addr = new_gpr();
                        emit(X86Op::FrameAddr,
                             {vr(addr), MOperand::make_frame(table)});
                        emit(X86Op::Add64, {vr(addr), vr(index)});
                        emit(X86Op::FaddM64,
                             {vr(addr), MOperand::make_imm(0)});
                    }
                }
                define(inst.result, f80_pop_result(), loc);
                return;
            }
            if (from == 8 || from == 16) {

                if (is_signed) {
                    uint32_t extended = new_gpr();
                    emit(from == 8 ? X86Op::Movsbl : X86Op::Movswl,
                         {vr(extended), vr(src)});
                    src = extended;
                }
                from = 32;
                if (is_signed) {

                    uint32_t result = new_fpr();
                    emit(dst_wide ? X86Op::Cvtsi2sd32 : X86Op::Cvtsi2ss32,
                         {vr(result), vr(src)});
                    define(inst.result, result, loc);
                    return;
                }

                uint32_t result = new_fpr();
                emit(dst_wide ? X86Op::Cvtsi2sd32 : X86Op::Cvtsi2ss32,
                     {vr(result), vr(src)});
                define(inst.result, result, loc);
                return;
            }
            if (from <= 32) {
                uint32_t result = new_fpr();
                if (is_signed) {
                    emit(dst_wide ? X86Op::Cvtsi2sd32 : X86Op::Cvtsi2ss32,
                         {vr(result), vr(src)});
                } else {

                    emit(dst_wide ? X86Op::Cvtsi2sd64 : X86Op::Cvtsi2ss64,
                         {vr(result), vr(src)});
                }
                define(inst.result, result, loc);
                return;
            }
            if (is_signed) {
                uint32_t result = new_fpr();
                emit(dst_wide ? X86Op::Cvtsi2sd64 : X86Op::Cvtsi2ss64,
                     {vr(result), vr(src)});
                define(inst.result, result, loc);
                return;
            }

            X86Op cvt = dst_wide ? X86Op::Cvtsi2sd64 : X86Op::Cvtsi2ss64;
            X86Op add = dst_wide ? X86Op::AddSD : X86Op::AddSS;
            uint32_t direct = new_fpr();
            emit(cvt, {vr(direct), vr(src)});
            uint32_t halved = two_address_result(src, /*wide=*/true, false);
            emit(X86Op::ShrI64, {vr(halved), MOperand::make_imm(1)});
            uint32_t sticky = two_address_result(src, /*wide=*/true, false);
            emit(X86Op::AndI64, {vr(sticky), MOperand::make_imm(1)});
            emit(X86Op::Or64, {vr(halved), vr(sticky)});
            uint32_t doubled = new_fpr();
            emit(cvt, {vr(doubled), vr(halved)});
            emit(add, {vr(doubled), vr(doubled)});

            X86Op fp_to_g = dst_wide ? X86Op::MovqXG : X86Op::MovdXG;
            X86Op g_to_fp = dst_wide ? X86Op::MovqGX : X86Op::MovdGX;
            X86Op cmov = dst_wide ? X86Op::Cmov64 : X86Op::Cmov32;
            uint32_t direct_bits = new_gpr();
            emit(fp_to_g, {vr(direct_bits), vr(direct)});
            uint32_t doubled_bits = new_gpr();
            emit(fp_to_g, {vr(doubled_bits), vr(doubled)});
            uint32_t chosen = new_gpr();
            emit(dst_wide ? X86Op::MovRR64 : X86Op::MovRR32,
                 {vr(chosen), vr(direct_bits)});
            emit(X86Op::Test64, {vr(src), vr(src)});
            emit(cmov, {vr(chosen), vr(doubled_bits)},
                 static_cast<uint32_t>(Cond::S));
            uint32_t result = new_fpr();
            emit(g_to_fp, {vr(result), vr(chosen)});
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::Ptrtoint:
        case air::Opcode::Inttoptr: {
            uint32_t src = use_reg(ops[0], loc);
            uint32_t result = new_gpr();
            emit(is_wide(inst.type) ? X86Op::MovRR64 : X86Op::MovRR32,
                 {vr(result), vr(src)});
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::Bitcast: {
            air::TypeId src_type = func_.value_type(ops[0]);
            bool src_fp = is_fp_type(src_type);
            bool dst_fp = is_fp_type(inst.type);
            uint32_t src = use_reg(ops[0], loc);
            uint32_t result = dst_fp ? new_fpr() : new_gpr();
            if (src_fp && !dst_fp) {
                emit(is_wide(src_type) ? X86Op::MovqXG : X86Op::MovdXG,
                     {vr(result), vr(src)});
            } else if (!src_fp && dst_fp) {
                emit(is_wide(inst.type) ? X86Op::MovqGX : X86Op::MovdGX,
                     {vr(result), vr(src)});
            } else if (src_fp && dst_fp) {
                emit(X86Op::MovapsRR, {vr(result), vr(src)});
            } else {
                emit(is_wide(inst.type) ? X86Op::MovRR64 : X86Op::MovRR32,
                     {vr(result), vr(src)});
            }
            define(inst.result, result, loc);
            return;
        }

        case air::Opcode::PtrAdd: {
            uint32_t base = use_reg(ops[0], loc);
            uint32_t offset = use_reg(ops[1], loc);
            uint32_t result = two_address_result(base, /*wide=*/true, false);
            emit(X86Op::Add64, {vr(result), vr(offset)});
            define(inst.result, result, loc);
            return;
        }

        case air::Opcode::Select: {
            air::TypeId type = inst.type;
            if (!check_scalar(type, loc)) {
                return;
            }
            uint32_t lhs = use_reg(ops[1], loc);
            uint32_t rhs = use_reg(ops[2], loc);
            bool fp = is_fp_type(type);
            bool wide = is_wide(type);
            if (is_f80(type)) {

                uint32_t lhs_slot = f80_spill(lhs);
                uint32_t rhs_slot = f80_spill(rhs);
                uint32_t lhs_addr = new_gpr();
                emit(X86Op::FrameAddr,
                     {vr(lhs_addr), MOperand::make_frame(lhs_slot)});
                uint32_t rhs_addr = new_gpr();
                emit(X86Op::FrameAddr,
                     {vr(rhs_addr), MOperand::make_frame(rhs_slot)});
                uint32_t chosen = two_address_result(lhs_addr, true, false);
                emit_truth_test(ops[0], loc);
                emit(X86Op::Cmov64, {vr(chosen), vr(rhs_addr)},
                     static_cast<uint32_t>(Cond::E));
                uint32_t result = out_.new_vreg(RegClass::Fpr128);
                emit(X86Op::LoadX128,
                     {vr(result), vr(chosen), MOperand::make_imm(0)});
                define(inst.result, result, loc);
                return;
            }
            if (!fp) {
                uint32_t result = new_gpr();
                emit(wide ? X86Op::MovRR64 : X86Op::MovRR32,
                     {vr(result), vr(lhs)});
                emit_truth_test(ops[0], loc);
                emit(wide ? X86Op::Cmov64 : X86Op::Cmov32,
                     {vr(result), vr(rhs)}, static_cast<uint32_t>(Cond::E));
                define(inst.result, result, loc);
                return;
            }
            if (fp && legacy32_ && wide) {

                uint32_t lhs_slot = out_.new_frame_object(8, 8);
                emit(X86Op::StoreSD,
                     {vr(lhs), MOperand::make_frame(lhs_slot),
                      MOperand::make_imm(0)});
                uint32_t rhs_slot = out_.new_frame_object(8, 8);
                emit(X86Op::StoreSD,
                     {vr(rhs), MOperand::make_frame(rhs_slot),
                      MOperand::make_imm(0)});
                uint32_t lhs_addr = new_gpr();
                emit(X86Op::FrameAddr,
                     {vr(lhs_addr), MOperand::make_frame(lhs_slot)});
                uint32_t rhs_addr = new_gpr();
                emit(X86Op::FrameAddr,
                     {vr(rhs_addr), MOperand::make_frame(rhs_slot)});
                uint32_t chosen = two_address_result(lhs_addr, false, false);
                emit_truth_test(ops[0], loc);
                emit(X86Op::Cmov32, {vr(chosen), vr(rhs_addr)},
                     static_cast<uint32_t>(Cond::E));
                uint32_t result = new_fpr();
                emit(X86Op::LoadSD,
                     {vr(result), vr(chosen), MOperand::make_imm(0)});
                define(inst.result, result, loc);
                return;
            }

            X86Op fp_to_g = wide ? X86Op::MovqXG : X86Op::MovdXG;
            X86Op g_to_fp = wide ? X86Op::MovqGX : X86Op::MovdGX;
            uint32_t lhs_bits = new_gpr();
            emit(fp_to_g, {vr(lhs_bits), vr(lhs)});
            uint32_t rhs_bits = new_gpr();
            emit(fp_to_g, {vr(rhs_bits), vr(rhs)});
            uint32_t chosen = new_gpr();
            emit(wide ? X86Op::MovRR64 : X86Op::MovRR32,
                 {vr(chosen), vr(lhs_bits)});
            emit_truth_test(ops[0], loc);
            emit(wide ? X86Op::Cmov64 : X86Op::Cmov32,
                 {vr(chosen), vr(rhs_bits)}, static_cast<uint32_t>(Cond::E));
            uint32_t result = new_fpr();
            emit(g_to_fp, {vr(result), vr(chosen)});
            define(inst.result, result, loc);
            return;
        }

        case air::Opcode::Call:
        case air::Opcode::CallIndirect:
            lower_call(inst, inst_id);
            return;
        case air::Opcode::Invoke:
        case air::Opcode::InvokeIndirect:
            {
                air::BlockCallId unwind{air::aux_high(inst.aux2)};
                uint32_t landing_pad =
                    block_map_.at(func_.block_call(unwind).target.index);
                uint32_t begin_label = out_.new_eh_label();
                uint32_t end_label = out_.new_eh_label();
                out_.eh_call_sites.push_back(
                    MEhCallSite{begin_label, end_label, landing_pad,
                                eh_.action_for_block(landing_pad)});
                emit_eh_label(begin_label);
                lower_call(inst, inst_id);
                emit_eh_label(end_label);
            }
            if (failed_) {
                return;
            }
            {
                air::BlockCallId normal{air::aux_low(inst.aux2)};
                if (opt_) {
                    emit_parallel_copies(normal, loc);
                } else {
                    emit_edge_stores(normal, loc);
                }
                uint32_t target =
                    block_map_.at(func_.block_call(normal).target.index);
                emit(X86Op::JmpLbl, {MOperand::make_label(target)});
            }
            return;
        case air::Opcode::EhAllocException: {
            uint32_t size = materialize_int(inst.aux, true);
            emit(X86Op::MovRR64, {pr(RDI), vr(size)});
            emit(X86Op::CallS,
                 {MOperand::make_symbol(sym_name(mod_.target(), "__cxa_allocate_exception", false),
                                        SymFlavor::Plain)});
            uint32_t result = new_gpr();
            emit(X86Op::MovRR64, {vr(result), pr(RAX)});
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::EhLandingPad: {

            uint32_t result = new_gpr();
            emit(X86Op::MovRR64, {vr(result), pr(RAX)});
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::EhSelector: {

            uint32_t result = new_gpr();
            emit(X86Op::MovRR32, {vr(result), pr(RDX)});
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::EhTypeId: {
            uint32_t filter = eh_.typeinfo_filter_for_value(ops[0], loc);
            uint32_t result = materialize_int(filter, false);
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::CatchBegin: {
            uint32_t exception = use_reg(ops[0], loc);
            emit(X86Op::MovRR64, {pr(RDI), vr(exception)});
            emit(X86Op::CallS,
                 {MOperand::make_symbol(sym_name(mod_.target(), "__cxa_begin_catch", false),
                                        SymFlavor::Plain)});
            uint32_t result = new_gpr();
            emit(X86Op::MovRR64, {vr(result), pr(RAX)});
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::CatchEnd:
            emit(X86Op::CallS,
                 {MOperand::make_symbol(sym_name(mod_.target(), "__cxa_end_catch", false),
                                        SymFlavor::Plain)});
            return;
        case air::Opcode::Throw: {
            uint32_t exception = use_reg(ops[0], loc);
            uint32_t typeinfo = use_reg(ops[1], loc);
            uint32_t destructor = ops.size() > 2 ? use_reg(ops[2], loc)
                                                 : materialize_int(0, true);
            emit(X86Op::MovRR64, {pr(RDI), vr(exception)});
            emit(X86Op::MovRR64, {pr(RSI), vr(typeinfo)});
            emit(X86Op::MovRR64, {pr(RDX), vr(destructor)});
            emit(X86Op::CallS,
                 {MOperand::make_symbol(sym_name(mod_.target(), "__cxa_throw", false), SymFlavor::Plain)});
            emit(X86Op::Ud2, {});
            return;
        }
        case air::Opcode::Rethrow:
            emit(X86Op::CallS,
                 {MOperand::make_symbol(sym_name(mod_.target(), "__cxa_rethrow", false), SymFlavor::Plain)});
            emit(X86Op::Ud2, {});
            return;
        case air::Opcode::Resume: {
            uint32_t exception = use_reg(ops[0], loc);
            emit(X86Op::MovRR64, {pr(RDI), vr(exception)});
            emit(X86Op::CallS,
                 {MOperand::make_symbol(sym_name(mod_.target(), "_Unwind_Resume", false), SymFlavor::Plain)});
            emit(X86Op::Ud2, {});
            return;
        }

        case air::Opcode::Trap:
            emit(X86Op::Ud2, {});

            start_dead_block();
            return;

        case air::Opcode::Unreachable:
            emit(X86Op::Ud2, {});
            return;

        case air::Opcode::Jump: {
            air::BlockCallId call{air::aux_low(inst.aux)};
            if (opt_) {
                emit_parallel_copies(call, loc);
            } else {
                emit_edge_stores(call, loc);
            }
            uint32_t target = block_map_.at(func_.block_call(call).target.index);
            emit(X86Op::JmpLbl, {MOperand::make_label(target)});
            return;
        }
        case air::Opcode::BrIf: {
            air::BlockCallId then_call{air::aux_low(inst.aux)};
            air::BlockCallId else_call{air::aux_high(inst.aux)};
            emit_truth_test(ops[0], loc);
            uint32_t then_target = edge_target(then_call, loc);
            uint32_t else_target = edge_target(else_call, loc);
            emit(X86Op::JccLbl, {MOperand::make_label(then_target)},
                 static_cast<uint32_t>(Cond::Ne));
            emit(X86Op::JmpLbl, {MOperand::make_label(else_target)});
            return;
        }
        case air::Opcode::Switch: {
            air::BlockCallId default_call{air::aux_low(inst.aux)};
            uint32_t table_index = air::aux_high(inst.aux);
            std::span<const air::SwitchCase> cases = func_.jump_table(table_index);
            air::TypeId value_type = func_.value_type(ops[0]);
            bool wide = is_wide(value_type);
            uint32_t value = use_reg(ops[0], loc);
            for (const air::SwitchCase& switch_case : cases) {
                uint64_t case_bits = wide ? switch_case.value
                                          : (switch_case.value & 0xFFFFFFFFull);
                int64_t signed_bits = static_cast<int64_t>(case_bits);
                if (!wide) {
                    emit(X86Op::CmpI32,
                         {vr(value), MOperand::make_imm(signed_bits)});
                } else if (signed_bits == static_cast<int32_t>(signed_bits)) {
                    emit(X86Op::CmpI64,
                         {vr(value), MOperand::make_imm(signed_bits)});
                } else {
                    uint32_t imm = materialize_int(case_bits, wide);
                    emit(X86Op::Cmp64, {vr(value), vr(imm)});
                }
                uint32_t target = edge_target(switch_case.target, loc);
                emit(X86Op::JccLbl, {MOperand::make_label(target)},
                     static_cast<uint32_t>(Cond::E));
            }
            uint32_t default_target = edge_target(default_call, loc);
            emit(X86Op::JmpLbl, {MOperand::make_label(default_target)});
            return;
        }
        case air::Opcode::Ret:
            lower_ret(inst, inst_id);
            return;

        case air::Opcode::StackAllocDyn: {
            uint32_t size = use_reg(ops[0], loc);
            uint32_t aligned = two_address_result(size, /*wide=*/true, false);
            emit(X86Op::AddI64, {vr(aligned), MOperand::make_imm(15)});
            emit(X86Op::AndI64, {vr(aligned), MOperand::make_imm(-16)});
            uint32_t new_sp = new_gpr();
            emit(X86Op::MovRR64, {vr(new_sp), pr(RSP)});
            emit(X86Op::Sub64, {vr(new_sp), vr(aligned)});
            emit(X86Op::MovRR64, {pr(RSP), vr(new_sp)});
            define(inst.result, new_sp, loc);
            return;
        }
        case air::Opcode::StackSave: {
            uint32_t saved = new_gpr();
            emit(X86Op::MovRR64, {vr(saved), pr(RSP)});
            define(inst.result, saved, loc);
            return;
        }
        case air::Opcode::StackRestore: {
            uint32_t saved = use_reg(ops[0], loc);
            emit(X86Op::MovRR64, {pr(RSP), vr(saved)});
            return;
        }
        case air::Opcode::AtomicLoad: {
            if (is_fp_type(inst.type)) {
                unsupported("atomic floating-point access", loc);
                return;
            }

            uint32_t result = new_gpr();
            MInst load;
            load.opcode = op(load_op_for(inst.type));
            load.operands.push_back(vr(result));
            load.operands.push_back(mem_base(ops[0], loc));
            load.operands.push_back(MOperand::make_imm(0));
            cur().insts.push_back(std::move(load));
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::AtomicStore: {
            air::TypeId value_type = func_.value_type(ops[0]);
            if (is_fp_type(value_type)) {
                unsupported("atomic floating-point access", loc);
                return;
            }
            uint32_t value = use_reg(ops[0], loc);
            air::MemOrder order = static_cast<air::MemOrder>(inst.aux & 0xFF);
            uint64_t size = scalar_size(value_type);
            if (order == air::MemOrder::SeqCst) {

                uint32_t scratch = new_gpr();
                emit(size == 8 ? X86Op::MovRR64 : X86Op::MovRR32,
                     {vr(scratch), vr(value)});
                X86Op xchg = size == 1 ? X86Op::Xchg8
                             : size == 2 ? X86Op::Xchg16
                             : size == 4 ? X86Op::Xchg32
                                         : X86Op::Xchg64;
                MInst inst_x;
                inst_x.opcode = op(xchg);
                inst_x.operands.push_back(vr(scratch));
                inst_x.operands.push_back(mem_base(ops[1], loc));
                inst_x.operands.push_back(MOperand::make_imm(0));
                cur().insts.push_back(std::move(inst_x));
                return;
            }
            MInst store;
            store.opcode = op(store_op_for(value_type));
            store.operands.push_back(vr(value));
            store.operands.push_back(mem_base(ops[1], loc));
            store.operands.push_back(MOperand::make_imm(0));
            cur().insts.push_back(std::move(store));
            return;
        }
        case air::Opcode::AtomicRmw: {
            air::RmwOp rmw = air::rmw_op(inst.aux);
            air::TypeId value_type = inst.type;
            if (is_fp_type(value_type)) {
                unsupported("atomic floating-point access", loc);
                return;
            }
            uint64_t size = scalar_size(value_type);
            uint32_t size_index = size == 1 ? 0 : size == 2 ? 1 : size == 4 ? 2 : 3;
            if (rmw == air::RmwOp::And || rmw == air::RmwOp::Or ||
                rmw == air::RmwOp::Xor) {

                uint32_t value = use_reg(ops[1], loc);
                MOperand base = mem_base(ops[0], loc);
                if (base.kind == MOperandKind::FrameIndex) {
                    emit(X86Op::FrameAddr, {pr(R11), base});
                } else {
                    emit(X86Op::MovRR64, {pr(R11), base});
                }
                bool wide_op = size == 8;
                emit(wide_op ? X86Op::MovRR64 : X86Op::MovRR32,
                     {pr(RCX), vr(value)});
                static constexpr X86Op kLoad[4] = {X86Op::Load8Z, X86Op::Load16Z,
                                                   X86Op::Load32, X86Op::Load64};
                emit(kLoad[size_index], {pr(RAX), pr(R11), MOperand::make_imm(0)});

                out_.blocks.emplace_back();
                uint32_t retry = static_cast<uint32_t>(out_.blocks.size()) - 1;
                emit(X86Op::JmpLbl, {MOperand::make_label(retry)});
                cur_block_ = retry;
                emit(wide_op ? X86Op::MovRR64 : X86Op::MovRR32,
                     {pr(RDX), pr(RAX)});
                X86Op logic = rmw == air::RmwOp::And
                    ? (wide_op ? X86Op::And64 : X86Op::And32)
                    : rmw == air::RmwOp::Or
                        ? (wide_op ? X86Op::Or64 : X86Op::Or32)
                        : (wide_op ? X86Op::Xor64 : X86Op::Xor32);
                emit(logic, {pr(RDX), pr(RCX)});
                static constexpr X86Op kCas[4] = {
                    X86Op::LockCmpxchg8, X86Op::LockCmpxchg16,
                    X86Op::LockCmpxchg32, X86Op::LockCmpxchg64};
                MInst cas_inst;
                cas_inst.opcode = op(kCas[size_index]);
                cas_inst.operands.push_back(pr(RDX));
                cas_inst.operands.push_back(pr(R11));
                cas_inst.operands.push_back(MOperand::make_imm(0));
                cas_inst.operands.push_back(pr(RAX));
                cur().insts.push_back(std::move(cas_inst));
                emit(X86Op::JccLbl, {MOperand::make_label(retry)},
                     static_cast<uint32_t>(Cond::Ne));

                out_.blocks.emplace_back();
                uint32_t cont = static_cast<uint32_t>(out_.blocks.size()) - 1;

                emit(X86Op::JmpLbl, {MOperand::make_label(cont)});
                out_.blocks[retry].succs.push_back(cont);
                cur_block_ = cont;

                block_values_.clear();
                uint32_t result = new_gpr();
                emit(wide_op ? X86Op::MovRR64 : X86Op::MovRR32,
                     {vr(result), pr(RAX)});
                define(inst.result, result, loc);
                return;
            }
            if (rmw != air::RmwOp::Xchg && rmw != air::RmwOp::Add &&
                rmw != air::RmwOp::Sub) {
                unsupported("this atomic read-modify-write operation", loc);
                return;
            }
            uint32_t value = use_reg(ops[1], loc);
            uint32_t exchanged = new_gpr();
            emit(size == 8 ? X86Op::MovRR64 : X86Op::MovRR32,
                 {vr(exchanged), vr(value)});
            if (rmw == air::RmwOp::Sub) {
                emit(size == 8 ? X86Op::Neg64 : X86Op::Neg32, {vr(exchanged)});
            }
            static constexpr X86Op kXchg[4] = {X86Op::Xchg8, X86Op::Xchg16,
                                               X86Op::Xchg32, X86Op::Xchg64};
            static constexpr X86Op kXadd[4] = {
                X86Op::LockXadd8, X86Op::LockXadd16, X86Op::LockXadd32,
                X86Op::LockXadd64};
            X86Op rmw_op = rmw == air::RmwOp::Xchg ? kXchg[size_index]
                                                   : kXadd[size_index];
            MInst rmw_inst;
            rmw_inst.opcode = op(rmw_op);
            rmw_inst.operands.push_back(vr(exchanged));
            rmw_inst.operands.push_back(mem_base(ops[0], loc));
            rmw_inst.operands.push_back(MOperand::make_imm(0));
            cur().insts.push_back(std::move(rmw_inst));
            uint32_t result = exchanged;
            if (size < 4) {

                mask_subword(value_type, result);
            }
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::AtomicCas: {
            air::TypeId value_type = inst.type;
            if (is_fp_type(value_type)) {
                unsupported("atomic floating-point access", loc);
                return;
            }
            uint64_t size = scalar_size(value_type);
            uint32_t expected = use_reg(ops[1], loc);
            uint32_t desired = use_reg(ops[2], loc);
            emit(size == 8 ? X86Op::MovRR64 : X86Op::MovRR32,
                 {pr(RAX), vr(expected)});
            X86Op cas = size == 1 ? X86Op::LockCmpxchg8
                        : size == 2 ? X86Op::LockCmpxchg16
                        : size == 4 ? X86Op::LockCmpxchg32
                                    : X86Op::LockCmpxchg64;
            MInst cas_inst;
            cas_inst.opcode = op(cas);
            cas_inst.operands.push_back(vr(desired));
            cas_inst.operands.push_back(mem_base(ops[0], loc));
            cas_inst.operands.push_back(MOperand::make_imm(0));
            cas_inst.operands.push_back(pr(RAX));
            cur().insts.push_back(std::move(cas_inst));
            uint32_t result = new_gpr();
            emit(size == 8 ? X86Op::MovRR64 : X86Op::MovRR32,
                 {vr(result), pr(RAX)});
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::Fence:
            emit(X86Op::Mfence, {});
            return;
        case air::Opcode::Bswap: {
            uint16_t width = int_width(inst.type);
            uint32_t value = use_reg(ops[0], loc);
            if (width == 16) {
                uint32_t result = two_address_result(value, false, false);
                emit(X86Op::Rol16I, {vr(result), MOperand::make_imm(8)});
                define(inst.result, result, loc);
                return;
            }
            if (width != 32 && width != 64) {
                unsupported("bswap width", loc);
                return;
            }
            uint32_t result = two_address_result(value, width == 64, false);
            emit(width == 64 ? X86Op::Bswap64 : X86Op::Bswap32, {vr(result)});
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::Clz:
        case air::Opcode::Ctz: {
            uint16_t width = int_width(inst.type);
            if (width != 32 && width != 64) {
                unsupported("count-leading/trailing width", loc);
                return;
            }
            bool wide = width == 64;
            uint32_t value = use_reg(ops[0], loc);
            bool leading = inst.op == air::Opcode::Clz;
            uint32_t scanned = new_gpr();
            emit(leading ? (wide ? X86Op::Bsr64 : X86Op::Bsr32)
                         : (wide ? X86Op::Bsf64 : X86Op::Bsf32),
                 {vr(scanned), vr(value)});
            uint32_t result = new_gpr();
            if (leading) {

                emit(X86Op::MovRI32,
                     {vr(result), MOperand::make_imm(wide ? 127 : 63)});
                emit(wide ? X86Op::Cmov64 : X86Op::Cmov32,
                     {vr(result), vr(scanned)}, static_cast<uint32_t>(Cond::Ne));
                emit(wide ? X86Op::XorI64 : X86Op::XorI32,
                     {vr(result), MOperand::make_imm(wide ? 63 : 31)});
            } else {
                emit(X86Op::MovRI32,
                     {vr(result), MOperand::make_imm(wide ? 64 : 32)});
                emit(wide ? X86Op::Cmov64 : X86Op::Cmov32,
                     {vr(result), vr(scanned)}, static_cast<uint32_t>(Cond::Ne));
            }
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::Popcnt: {
            uint16_t width = int_width(inst.type);
            if (width != 32 && width != 64) {
                unsupported("population-count width", loc);
                return;
            }
            uint32_t value = use_reg(ops[0], loc);
            uint32_t result = new_gpr();
            emit(width == 64 ? X86Op::Popcnt64 : X86Op::Popcnt32,
                 {vr(result), vr(value)});
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::VaStart: {
            if (legacy32_) {

                uint32_t list = use_reg(ops[0], loc);
                uint32_t addr = new_gpr();
                emit(X86Op::LeaMem,
                     {vr(addr), pr(RBP),
                      MOperand::make_imm(static_cast<int64_t>(
                          8 + out_.named_stack_bytes))});
                emit(X86Op::Store32,
                     {vr(addr), vr(list), MOperand::make_imm(0)});
                return;
            }
            if (reg_save_frame_ < 0) {
                unsupported("va_start outside a variadic function", loc);
                return;
            }
            uint32_t list = use_reg(ops[0], loc);

            uint32_t gp = materialize_int(8u * named_gprs_, false);
            emit(X86Op::Store32, {vr(gp), vr(list), MOperand::make_imm(0)});
            uint32_t fp = materialize_int(48u + 16u * named_fprs_, false);
            emit(X86Op::Store32, {vr(fp), vr(list), MOperand::make_imm(4)});

            uint32_t overflow = new_gpr();
            emit(X86Op::LeaMem,
                 {vr(overflow), pr(RBP),
                  MOperand::make_imm(static_cast<int64_t>(
                      16 + out_.named_stack_bytes))});
            emit(X86Op::Store64,
                 {vr(overflow), vr(list), MOperand::make_imm(8)});
            uint32_t save = new_gpr();
            emit(X86Op::FrameAddr,
                 {vr(save), MOperand::make_frame(
                                static_cast<uint32_t>(reg_save_frame_))});
            emit(X86Op::Store64, {vr(save), vr(list), MOperand::make_imm(16)});
            return;
        }
        case air::Opcode::InlineAsm:
            lower_asm(inst, inst_id);
            return;
        case air::Opcode::BrIndirect: {
            uint32_t target = use_reg(ops[0], loc);
            if (opt_) {
                std::vector<air::BlockCallId> edges;
                func_.successors(inst_id, edges);
                for (air::BlockCallId edge : edges) {
                    out_.blocks[cur_block_].succs.push_back(
                        block_map_.at(func_.block_call(edge).target.index));
                }
            }
            emit(X86Op::JmpR, {vr(target)});
            return;
        }
        case air::Opcode::FrameAddr:
        case air::Opcode::ReturnAddr:
            unsupported("__builtin_frame_address/__builtin_return_address", loc);
            return;
    }
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
        if (slots_.contains(v.index)) {
            return;
        }
        air::TypeId type = func_.value_type(v);
        uint32_t bytes = is_f128(type) || is_f80(type) ? 16 : 8;
        uint32_t align = bytes;
        if (legacy32_ && is_f80(type)) {

            bytes = 12;
            align = 4;
        }
        slots_[v.index] = Slot{out_.new_frame_object(bytes, align), type};
    };

    for (air::BlockId block_id : layout) {
        if (!opt_) {
            for (air::ValueId param : func_.block_params(block_id)) {
                note_slot(param);
            }
        }
        const air::BlockData& block = func_.block(block_id);

        bool splits_block = false;
        if (!opt_) {
            for (air::InstId inst_id = block.first; inst_id.is_valid();
                 inst_id = func_.inst(inst_id).next) {
                const air::InstData& inst = func_.inst(inst_id);
                if (inst.op == air::Opcode::AtomicRmw) {
                    air::RmwOp rmw = air::rmw_op(inst.aux);
                    if (rmw == air::RmwOp::And || rmw == air::RmwOp::Or ||
                        rmw == air::RmwOp::Xor) {
                        splits_block = true;
                        break;
                    }
                }
            }
        }
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
            if (opt_) {
                continue;
            }

            if (legacy32_ && inst.result.is_valid() &&
                (legacy_i64(func_.value_type(inst.result)) ||
                 legacy_f80(func_.value_type(inst.result)))) {
                note_slot(inst.result);
            }
            auto note_use = [&](air::ValueId used, bool force_slot) {
                const air::ValueData& data = func_.value(used);
                if (data.kind != air::ValueKind::InstResult &&
                    data.kind != air::ValueKind::BlockParam) {
                    return;
                }
                if (frame_addrs_.contains(used.index)) {
                    return;
                }
                if (force_slot || legacy_i64(data.type) ||
                    legacy_f80(data.type) ||
                    def_block_of(used) != block_id.index) {
                    note_slot(used);
                }
            };
            for (air::ValueId used : func_.operands(inst_id)) {
                note_use(used, splits_block);
            }
            std::vector<air::BlockCallId> edges;
            func_.successors(inst_id, edges);
            for (air::BlockCallId edge : edges) {
                for (air::ValueId used : func_.block_call_args(edge)) {
                    note_use(used, true);
                }
            }
        }
    }

    const air::SigData& sig = mod_.types().signature(func_.sig());
    std::span<const air::ValueId> entry_params =
        func_.block_params(func_.entry_block());
    cur_block_ = 0;

    if (legacy32_ && sig.ret_class == air::RetClass::IndirectSret) {
        out_.callee_pop_bytes = 4;
    }

    for (size_t i = 0; i < sig.params.size() && i < entry_params.size(); ++i) {
        if (sig.params[i].role == air::ParamRole::Sret) {
            sret_param_ = entry_params[i];
            has_sret_param_ = true;
            if (!opt_) {
                note_slot(entry_params[i]);
            }
            break;
        }
    }

    if (legacy32_) {
        // The i386 cdecl ABI must align every stack argument to four bytes; i64
        // occupies adjacent slots rather than receiving eight-byte alignment.
        uint64_t off = 0;
        for (size_t i = 0; i < entry_params.size(); ++i) {
            air::TypeId type = sig.params[i].type;
            air::ParamRole role = sig.params[i].role;

            if (role == air::ParamRole::StackByval) {
                off = (off + 3) & ~uint64_t{3};
                int64_t disp = static_cast<int64_t>(8 + off);
                off += (sig.params[i].byval_size + 3) & ~uint64_t{3};
                auto slot = slots_.find(entry_params[i].index);
                if (slot == slots_.end()) {
                    continue;
                }
                emit(X86Op::LeaMem,
                     {pr(RAX), pr(RBP), MOperand::make_imm(disp)});
                emit(X86Op::Store32,
                     {pr(RAX), MOperand::make_frame(slot->second.frame_index),
                      MOperand::make_imm(0)});
                continue;
            }

            if (role != air::ParamRole::Normal &&
                role != air::ParamRole::Sret) {
                unsupported("this parameter kind in 32-bit mode", func_.loc());
                return false;
            }
            if (is_f128(type)) {
                unsupported("this parameter kind in 32-bit mode", func_.loc());
                return false;
            }
            uint64_t size = role == air::ParamRole::Sret ? 4
                            : is_f80(type)
                                ? 12
                                : std::max<uint64_t>(4, scalar_size(type));
            off = (off + 3) & ~uint64_t{3};
            int64_t disp = static_cast<int64_t>(8 + off);
            off += size;
            auto slot = slots_.find(entry_params[i].index);
            if (slot == slots_.end()) {
                continue;
            }
            uint32_t fi = slot->second.frame_index;
            if (role == air::ParamRole::Sret) {
                emit(X86Op::Load32,
                     {pr(RAX), pr(RBP), MOperand::make_imm(disp)});
                emit(X86Op::Store32,
                     {pr(RAX), MOperand::make_frame(fi), MOperand::make_imm(0)});
                continue;
            }
            if (is_f80(type)) {

                emit(X86Op::Fld80,
                     {pr(RBP), MOperand::make_imm(disp)});
                emit(X86Op::Fstp80,
                     {MOperand::make_frame(fi), MOperand::make_imm(0)});
                continue;
            }
            if (legacy_i64(type)) {

                emit(X86Op::Load32,
                     {pr(RAX), pr(RBP), MOperand::make_imm(disp)});
                emit(X86Op::Store32,
                     {pr(RAX), MOperand::make_frame(fi), MOperand::make_imm(0)});
                emit(X86Op::Load32,
                     {pr(RAX), pr(RBP), MOperand::make_imm(disp + 4)});
                emit(X86Op::Store32,
                     {pr(RAX), MOperand::make_frame(fi), MOperand::make_imm(4)});
                continue;
            }
            if (is_fp_type(type)) {

                uint32_t staged = new_fpr();
                emit(load_op_for(type),
                     {vr(staged), pr(RBP), MOperand::make_imm(disp)});
                emit(store_op_for(type),
                     {vr(staged), MOperand::make_frame(fi), MOperand::make_imm(0)});
                continue;
            }
            MInst load;
            load.opcode = op(load_op_for(type));
            load.operands = {pr(RAX), pr(RBP), MOperand::make_imm(disp)};
            cur().insts.push_back(std::move(load));
            MInst store;
            store.opcode = op(store_op_for(type));
            store.operands = {pr(RAX), MOperand::make_frame(fi),
                              MOperand::make_imm(0)};
            cur().insts.push_back(std::move(store));
        }
        out_.named_stack_bytes = static_cast<uint32_t>((off + 3) & ~uint64_t{3});
    } else {
    uint32_t next_gpr = 0;
    uint32_t next_fpr = 0;
    uint64_t incoming_stack = 0;
    for (size_t i = 0; i < entry_params.size(); ++i) {
        air::TypeId type = sig.params[i].type;
        auto slot = slots_.find(entry_params[i].index);
        if (sig.params[i].role == air::ParamRole::StackByval) {

            uint64_t align = std::max<uint64_t>(8, sig.params[i].byval_align);
            incoming_stack = (incoming_stack + align - 1) & ~(align - 1);
            int64_t displacement = static_cast<int64_t>(16 + incoming_stack);
            incoming_stack += (sig.params[i].byval_size + 7) & ~uint64_t{7};
            if (opt_) {
                uint32_t dest = canonical_vreg(entry_params[i]);
                emit(X86Op::LeaMem,
                     {vr(dest), pr(RBP), MOperand::make_imm(displacement)});
                continue;
            }
            if (slot == slots_.end()) {
                continue;
            }
            emit(X86Op::LeaMem,
                 {pr(R11), pr(RBP), MOperand::make_imm(displacement)});
            MInst store;
            store.opcode = op(X86Op::Store64);
            store.operands.push_back(pr(R11));
            store.operands.push_back(
                MOperand::make_frame(slot->second.frame_index));
            store.operands.push_back(MOperand::make_imm(0));
            cur().insts.push_back(std::move(store));
            continue;
        }

        auto park = [&](size_t index, bool from_stack, uint32_t incoming,
                        int64_t stack_disp) {
            air::TypeId param_type = sig.params[index].type;
            bool param_fp = is_fp_type(param_type);
            auto param_slot = slots_.find(entry_params[index].index);
            if (opt_) {
                uint32_t dest = canonical_vreg(entry_params[index]);
                if (from_stack) {
                    MInst load;
                    load.opcode = op(load_op_for(param_type));
                    load.operands.push_back(vr(dest));
                    load.operands.push_back(pr(RBP));
                    load.operands.push_back(MOperand::make_imm(stack_disp));
                    cur().insts.push_back(std::move(load));
                    return;
                }
                if (param_fp) {
                    emit(X86Op::MovapsRR, {vr(dest), pr(incoming)});
                } else {
                    emit(is_wide(param_type) ? X86Op::MovRR64 : X86Op::MovRR32,
                         {vr(dest), pr(incoming)});
                }
                return;
            }
            if (param_slot == slots_.end()) {
                return;
            }
            if (from_stack) {
                uint32_t scratch = param_fp ? XMM15 : R11;
                MInst load;
                load.opcode = op(load_op_for(param_type));
                load.operands.push_back(pr(scratch));
                load.operands.push_back(pr(RBP));
                load.operands.push_back(MOperand::make_imm(stack_disp));
                cur().insts.push_back(std::move(load));
                incoming = scratch;
            }
            MInst store;
            store.opcode = op(store_op_for(param_type));
            store.operands.push_back(pr(incoming));
            store.operands.push_back(
                MOperand::make_frame(param_slot->second.frame_index));
            store.operands.push_back(MOperand::make_imm(0));
            cur().insts.push_back(std::move(store));
        };

        uint8_t group = sig.params[i].coerce_group;
        if (group > 1 && i + group <= entry_params.size()) {
            unsigned need_int = 0;
            unsigned need_sse = 0;
            for (size_t j = i; j < i + group; ++j) {
                if (is_fp_type(sig.params[j].type)) {
                    ++need_sse;
                } else {
                    ++need_int;
                }
            }
            bool fits = next_gpr + need_int <= 6 && next_fpr + need_sse <= 8;
            if (fits) {
                for (size_t j = i; j < i + group; ++j) {
                    bool param_fp = is_fp_type(sig.params[j].type);
                    uint32_t incoming =
                        param_fp ? xmm(next_fpr++) : kGprArgs[next_gpr++];
                    park(j, /*from_stack=*/false, incoming, 0);
                }
            } else {
                incoming_stack = (incoming_stack + 7) & ~uint64_t{7};
                for (size_t j = i; j < i + group; ++j) {
                    park(j, /*from_stack=*/true, 0,
                         static_cast<int64_t>(16 + incoming_stack));
                    incoming_stack += 8;
                }
            }
            i += group - 1;
            continue;
        }

        bool fp = is_fp_type(type);
        uint64_t size = std::max<uint64_t>(8, scalar_size(type));
        bool on_stack = false;
        uint32_t incoming = 0;
        if (is_f80(type)) {
            on_stack = true;
        } else if (fp) {
            if (next_fpr >= 8) {
                on_stack = true;
            } else {
                incoming = xmm(next_fpr++);
            }
        } else {
            if (next_gpr >= 6) {
                on_stack = true;
            } else {
                incoming = kGprArgs[next_gpr++];
            }
        }
        int64_t stack_disp = 0;
        if (on_stack) {
            incoming_stack = (incoming_stack + size - 1) & ~(size - 1);
            stack_disp = static_cast<int64_t>(16 + incoming_stack);
            incoming_stack += size;
        }
        park(i, on_stack, incoming, stack_disp);
    }
    out_.named_stack_bytes =
        static_cast<uint32_t>((incoming_stack + 7) & ~uint64_t{7});
    named_gprs_ = next_gpr;
    named_fprs_ = next_fpr;

    if (sig.is_variadic) {

        reg_save_frame_ =
            static_cast<int32_t>(out_.new_frame_object(176, 16));
        for (uint32_t reg = named_gprs_; reg < 6; ++reg) {
            MInst store;
            store.opcode = op(X86Op::Store64);
            store.operands.push_back(pr(kGprArgs[reg]));
            store.operands.push_back(MOperand::make_frame(
                static_cast<uint32_t>(reg_save_frame_)));
            store.operands.push_back(
                MOperand::make_imm(static_cast<int64_t>(8u * reg)));
            cur().insts.push_back(std::move(store));
        }
        for (uint32_t reg = named_fprs_; reg < 8; ++reg) {
            MInst store;
            store.opcode = op(X86Op::StoreX128);
            store.operands.push_back(pr(xmm(reg)));
            store.operands.push_back(MOperand::make_frame(
                static_cast<uint32_t>(reg_save_frame_)));
            store.operands.push_back(
                MOperand::make_imm(static_cast<int64_t>(48u + 16u * reg)));
            cur().insts.push_back(std::move(store));
        }
    }
    }

    for (size_t i = 0; i < layout.size(); ++i) {
        cur_block_ = static_cast<uint32_t>(i);
        block_values_.clear();
        const air::BlockData& block = func_.block(layout[i]);
        for (air::InstId inst_id = block.first; inst_id.is_valid();
             inst_id = func_.inst(inst_id).next) {
            lower_inst(inst_id);
            if (failed_) {
                return false;
            }
        }
    }
    if (opt_) {
        record_successors();
    }
    return !failed_;
}

void ISel::record_successors() {
    for (MBlock& block : out_.blocks) {
        for (const MInst& inst : block.insts) {
            for (const MOperand& operand : inst.operands) {
                if (operand.kind == MOperandKind::Label) {
                    block.succs.push_back(operand.label);
                }
            }
        }
        std::sort(block.succs.begin(), block.succs.end());
        block.succs.erase(std::unique(block.succs.begin(), block.succs.end()),
                          block.succs.end());
    }
}

} // namespace

bool select_function(const air::Module& module, const air::Function& function,
                     uint32_t function_index, MFunction& out,
                     std::vector<Diagnostic>& diagnostics, int opt_level) {
    ISel isel(module, function, function_index, out, diagnostics, opt_level);
    return isel.run();
}

} // namespace aburi::backend::x86
