#include "isel.h"

#include "../common/emitter.h"

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

namespace aburi::backend::aarch64 {

namespace {

uint16_t op(A64Op o) { return static_cast<uint16_t>(o); }

std::string sym_name(const TargetInfo& target, const std::string& name,
                     bool no_prefix) {
    return target_symbol_name(target, name, no_prefix);
}

class ISel {
public:
    ISel(const air::Module& mod, const air::Function& func,
         uint32_t function_index, MFunction& out,
         std::vector<Diagnostic>& diagnostics, int opt_level)
        : mod_(mod), func_(func), out_(out), diagnostics_(diagnostics),
          opt_(opt_level >= 1),
          standard_aapcs_(mod.target().os == TargetOS::LINUX) {
        out_.name = sym_name(mod.target(), func.name(), func.attrs().no_prefix);
        out_.attrs = func.attrs();
        out_.attrs.no_prefix = true;
        out_.linkage = func.linkage();
        out_.index = function_index;
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
        error("not supported by the fast tier yet: " + what, loc);
    }
    bool is_fp_type(air::TypeId type) const { return mod_.types().is_float(type); }
    bool is_f128(air::TypeId type) const {
        const air::TypeData& data = mod_.types().type(type);
        return data.kind == air::TypeKind::Float &&
               data.float_kind == air::FloatKind::F128;
    }
    bool is_wide(air::TypeId type) const {
        const air::TypeData& data = mod_.types().type(type);
        if (data.kind == air::TypeKind::Ptr) {
            return true;
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
            return 8;
        }
        if (data.kind == air::TypeKind::Int) {
            return std::max<uint64_t>(1, data.int_width / 8);
        }
        if (data.kind == air::TypeKind::Float) {
            switch (data.float_kind) {
                case air::FloatKind::F32: return 4;
                case air::FloatKind::F64: return 8;
                case air::FloatKind::F128: return 16;
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
        return true;
    }

    MBlock& cur() { return out_.blocks[cur_block_]; }
    void emit(A64Op o, std::vector<MOperand> operands, uint32_t aux = 0) {
        MInst inst;
        inst.opcode = op(o);
        inst.aux = aux;
        inst.operands = std::move(operands);
        cur().insts.push_back(std::move(inst));
    }
    void emit_eh_label(uint32_t label) { emit(A64Op::EhLabel, {}, label); }
    uint32_t new_gpr() { return out_.new_vreg(RegClass::Gpr); }
    uint32_t new_fpr() { return out_.new_vreg(RegClass::Fpr); }
    uint32_t new_fpr128() { return out_.new_vreg(RegClass::Fpr128); }
    uint32_t new_reg_for(air::TypeId type) {
        if (is_f128(type)) {
            return new_fpr128();
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
    uint32_t f128_libcall(const char* name,
                          std::initializer_list<std::pair<uint32_t, char>> args,
                          char result_kind);

    A64Op load_op_for(air::TypeId type) const;
    A64Op store_op_for(air::TypeId type) const;
    A64Op asm_move_op(air::TypeId type, bool in_fpr, bool to_phys) const {
        bool wide = is_wide(type);
        if (!in_fpr) {
            return wide ? A64Op::MovX : A64Op::MovW;
        }
        if (is_fp_type(type)) {
            return wide ? A64Op::FmovD : A64Op::FmovS;
        }
        if (to_phys) {
            return wide ? A64Op::FmovDX : A64Op::FmovSW;
        }
        return wide ? A64Op::FmovXD : A64Op::FmovWS;
    }

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

    void lower_inst(air::InstId inst_id);
    void lower_asm(const air::InstData& inst, air::InstId inst_id,
                   const std::vector<std::string>& labels = {});
    void lower_call(const air::InstData& inst, air::InstId inst_id);
    void lower_ret(const air::InstData& inst, air::InstId inst_id);
    void lower_tail_call(const air::InstData& inst, air::InstId inst_id);
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
    const bool standard_aapcs_ = false;
    uint32_t named_gprs_ = 0;
    uint32_t named_fprs_ = 0;
    int32_t gr_save_frame_ = -1;
    int32_t vr_save_frame_ = -1;
    uint32_t cur_block_ = 0;
};

uint32_t ISel::f128_libcall(
    const char* name,
    std::initializer_list<std::pair<uint32_t, char>> args,
    char result_kind) {
    uint32_t next_q = 0;
    uint32_t next_x = 0;
    for (const auto& [vreg, kind] : args) {
        switch (kind) {
            case 'q':
                emit(A64Op::MovV16b, {pr(v(next_q++)), vr(vreg)});
                break;
            case 'd':
                emit(A64Op::FmovD, {pr(v(next_q++)), vr(vreg)});
                break;
            case 's':
                emit(A64Op::FmovS, {pr(v(next_q++)), vr(vreg)});
                break;
            case 'x':
                emit(A64Op::MovX, {pr(next_x++), vr(vreg)});
                break;
            default:
                emit(A64Op::MovW, {pr(next_x++), vr(vreg)});
                break;
        }
    }
    emit(A64Op::Bl,
         {MOperand::make_symbol(sym_name(mod_.target(), name, false),
                                SymFlavor::Plain)});
    uint32_t result;
    switch (result_kind) {
        case 'q':
            result = new_fpr128();
            emit(A64Op::MovV16b, {vr(result), pr(V0)});
            break;
        case 'd':
            result = new_fpr();
            emit(A64Op::FmovD, {vr(result), pr(V0)});
            break;
        case 's':
            result = new_fpr();
            emit(A64Op::FmovS, {vr(result), pr(V0)});
            break;
        case 'x':
            result = new_gpr();
            emit(A64Op::MovX, {vr(result), pr(X0)});
            break;
        default:
            result = new_gpr();
            emit(A64Op::MovW, {vr(result), pr(X0)});
            break;
    }
    return result;
}

A64Op ISel::load_op_for(air::TypeId type) const {
    const air::TypeData& data = mod_.types().type(type);
    if (data.kind == air::TypeKind::Ptr) {
        return A64Op::LdrX;
    }
    if (data.kind == air::TypeKind::Float) {
        switch (data.float_kind) {
            case air::FloatKind::F32: return A64Op::LdrS;
            case air::FloatKind::F64: return A64Op::LdrD;
            case air::FloatKind::F128: return A64Op::LdrQ;
        }
    }
    switch (data.int_width) {
        case 8: return A64Op::LdrbW;
        case 16: return A64Op::LdrhW;
        case 32: return A64Op::LdrW;
        default: return A64Op::LdrX;
    }
}

A64Op ISel::store_op_for(air::TypeId type) const {
    const air::TypeData& data = mod_.types().type(type);
    if (data.kind == air::TypeKind::Ptr) {
        return A64Op::StrX;
    }
    if (data.kind == air::TypeKind::Float) {
        switch (data.float_kind) {
            case air::FloatKind::F32: return A64Op::StrS;
            case air::FloatKind::F64: return A64Op::StrD;
            case air::FloatKind::F128: return A64Op::StrQ;
        }
    }
    switch (data.int_width) {
        case 8: return A64Op::StrbW;
        case 16: return A64Op::StrhW;
        case 32: return A64Op::StrW;
        default: return A64Op::StrX;
    }
}

uint32_t ISel::materialize_int(uint64_t bits, bool wide) {
    uint32_t vreg = new_gpr();
    uint64_t value = wide ? bits : (bits & 0xFFFFFFFFull);
    int chunks = wide ? 4 : 2;
    A64Op movz = wide ? A64Op::MovzX : A64Op::MovzW;
    A64Op movn = wide ? A64Op::MovnX : A64Op::MovnW;
    A64Op movk = wide ? A64Op::MovkX : A64Op::MovkW;

    int nonzero = 0;
    int nonones = 0;
    for (int i = 0; i < chunks; ++i) {
        uint64_t chunk = (value >> (16 * i)) & 0xFFFF;
        if (chunk != 0) {
            ++nonzero;
        }
        if (chunk != 0xFFFF) {
            ++nonones;
        }
    }

    if (nonzero == 0) {
        emit(movz, {vr(vreg), MOperand::make_imm(0)}, 0);
        return vreg;
    }

    bool use_movn = nonones < nonzero;
    bool started = false;
    for (int i = 0; i < chunks; ++i) {
        uint64_t chunk = (value >> (16 * i)) & 0xFFFF;
        if (!started) {
            if (use_movn) {
                if (chunk == 0xFFFF && nonones > 0) {
                    continue;
                }
                emit(movn, {vr(vreg), MOperand::make_imm(
                                          static_cast<int64_t>(~chunk & 0xFFFF))},
                     static_cast<uint32_t>(i));
                started = true;
            } else {
                if (chunk == 0) {
                    continue;
                }
                emit(movz, {vr(vreg), MOperand::make_imm(static_cast<int64_t>(chunk))},
                     static_cast<uint32_t>(i));
                started = true;
            }
            continue;
        }
        bool needs = use_movn ? chunk != 0xFFFF : chunk != 0;
        if (needs) {
            emit(movk, {vr(vreg), MOperand::make_imm(static_cast<int64_t>(chunk))},
                 static_cast<uint32_t>(i));
        }
    }
    return vreg;
}

uint32_t ISel::materialize_symbol_addr(const std::string& symbol, bool direct) {
    uint32_t vreg = new_gpr();
    if (direct) {
        emit(A64Op::Adrp,
             {vr(vreg), MOperand::make_symbol(symbol, SymFlavor::Page)});
        emit(A64Op::AddXsym,
             {vr(vreg), vr(vreg), MOperand::make_symbol(symbol, SymFlavor::PageOff)});
    } else {
        emit(A64Op::Adrp,
             {vr(vreg), MOperand::make_symbol(symbol, SymFlavor::GotPage)});
        MInst load;
        load.opcode = op(A64Op::LdrX);
        load.operands.push_back(vr(vreg));
        load.operands.push_back(vr(vreg));
        load.operands.push_back(
            MOperand::make_symbol(symbol, SymFlavor::GotPageOff));
        cur().insts.push_back(std::move(load));
    }
    return vreg;
}

uint32_t ISel::materialize_tls_addr(const std::string& symbol, SrcLoc loc) {
    if (mod_.target().os != TargetOS::MACOS) {
        error("thread_local address lowering is not supported for this "
              "AArch64 object format yet",
              loc);
        return new_gpr();
    }

    uint32_t descriptor = new_gpr();
    emit(A64Op::Adrp,
         {vr(descriptor),
          MOperand::make_symbol(symbol, SymFlavor::TlvPage)});
    emit(A64Op::LdrX,
         {vr(descriptor), vr(descriptor),
          MOperand::make_symbol(symbol, SymFlavor::TlvPageOff)});
    uint32_t resolver = new_gpr();
    emit(A64Op::LdrX,
         {vr(resolver), vr(descriptor), MOperand::make_imm(0)});
    emit(A64Op::MovX, {pr(X0), vr(descriptor)});
    emit(A64Op::MovX, {pr(X17), vr(resolver)});
    emit(A64Op::Blr, {pr(X17)});
    uint32_t result = new_gpr();
    emit(A64Op::MovX, {vr(result), pr(X0)});
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
    if (cls == RegClass::Fpr128) {
        emit(A64Op::MovV16b, {vr(dest_vreg), vr(src_vreg)});
        return;
    }
    emit(cls == RegClass::Fpr ? A64Op::FmovD : A64Op::MovX,
         {vr(dest_vreg), vr(src_vreg)});
}

uint32_t ISel::use_reg(air::ValueId v, SrcLoc loc) {
    auto cached = block_values_.find(v.index);
    if (cached != block_values_.end()) {
        return cached->second;
    }

    auto frame = frame_addrs_.find(v.index);
    if (frame != frame_addrs_.end()) {
        uint32_t addr = new_gpr();
        emit(A64Op::FrameAddr, {vr(addr), MOperand::make_frame(frame->second)});
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
            if (is_fp_type(data.type)) {
                uint32_t zero = materialize_int(0, false);
                vreg = new_fpr();
                emit(is_wide(data.type) ? A64Op::FmovDX : A64Op::FmovSW,
                     {vr(vreg), vr(zero)});
            } else {
                vreg = materialize_int(0, is_wide(data.type));
            }
            break;
        case air::ValueKind::ConstFloat: {
            if (is_f128(data.type)) {

                uint32_t slot = out_.new_frame_object(16, 16);
                uint32_t low = materialize_int(data.payload, true);
                uint32_t high = materialize_int(data.payload2, true);
                MInst store_low;
                store_low.opcode = op(A64Op::StrX);
                store_low.operands = {vr(low), MOperand::make_frame(slot),
                                      MOperand::make_imm(0)};
                cur().insts.push_back(std::move(store_low));
                MInst store_high;
                store_high.opcode = op(A64Op::StrX);
                store_high.operands = {vr(high), MOperand::make_frame(slot),
                                       MOperand::make_imm(8)};
                cur().insts.push_back(std::move(store_high));
                vreg = new_fpr128();
                MInst load;
                load.opcode = op(A64Op::LdrQ);
                load.operands = {vr(vreg), MOperand::make_frame(slot),
                                 MOperand::make_imm(0)};
                cur().insts.push_back(std::move(load));
                break;
            }
            bool wide = is_wide(data.type);
            uint32_t gpr = materialize_int(data.payload, wide);
            vreg = new_fpr();
            emit(wide ? A64Op::FmovDX : A64Op::FmovSW, {vr(vreg), vr(gpr)});
            break;
        }
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
        uint32_t vreg = use_reg(args[i], loc);
        auto slot = slots_.find(params[i].index);
        if (slot != slots_.end()) {
            store_to_slot(vreg, slot->second);
        }
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
    emit(A64Op::B, {MOperand::make_label(target)});
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
    emit(A64Op::AndWri,
         {vr(masked), vr(vreg), MOperand::make_imm(width == 8 ? 0xFF : 0xFFFF)});
    vreg = masked;
}

void ISel::emit_truth_test(air::ValueId cond, SrcLoc loc) {
    uint32_t vreg = use_reg(cond, loc);
    emit(A64Op::CmpWri, {vr(vreg), MOperand::make_imm(0)});
}

void ISel::lower_icmp(const air::InstData& inst, air::InstId inst_id) {
    std::span<const air::ValueId> ops = func_.operands(inst_id);
    air::TypeId operand_type = func_.value_type(ops[0]);
    uint32_t lhs = use_reg(ops[0], inst.loc);
    uint32_t rhs = use_reg(ops[1], inst.loc);
    bool wide = is_wide(operand_type);
    emit(wide ? A64Op::CmpX : A64Op::CmpW, {vr(lhs), vr(rhs)});

    static constexpr Cond kMap[] = {
        Cond::Eq, Cond::Ne, Cond::Lt, Cond::Le, Cond::Gt, Cond::Ge,
        Cond::Lo, Cond::Ls, Cond::Hi, Cond::Hs,
    };
    Cond cond = kMap[inst.aux & 0xFF];
    uint32_t result = new_gpr();
    emit(A64Op::CsetW, {vr(result)}, static_cast<uint32_t>(cond));
    define(inst.result, result, inst.loc);
}

void ISel::lower_fcmp(const air::InstData& inst, air::InstId inst_id) {
    std::span<const air::ValueId> ops = func_.operands(inst_id);
    air::TypeId operand_type = func_.value_type(ops[0]);
    uint32_t lhs = use_reg(ops[0], inst.loc);
    uint32_t rhs = use_reg(ops[1], inst.loc);
    if (is_f128(operand_type)) {

        const char* fn = nullptr;
        Cond cond = Cond::Eq;
        switch (static_cast<air::FloatCond>(inst.aux & 0xFF)) {
            case air::FloatCond::Oeq: fn = "__eqtf2"; cond = Cond::Eq; break;
            case air::FloatCond::Une: fn = "__netf2"; cond = Cond::Ne; break;
            case air::FloatCond::Olt: fn = "__lttf2"; cond = Cond::Lt; break;
            case air::FloatCond::Ole: fn = "__letf2"; cond = Cond::Le; break;
            case air::FloatCond::Ogt: fn = "__gttf2"; cond = Cond::Gt; break;
            case air::FloatCond::Oge: fn = "__getf2"; cond = Cond::Ge; break;
            default:
                break;
        }
        if (!fn) {
            unsupported("this long double comparison", inst.loc);
            return;
        }
        uint32_t verdict =
            f128_libcall(fn, {{lhs, 'q'}, {rhs, 'q'}}, 'w');
        emit(A64Op::CmpWri, {vr(verdict), MOperand::make_imm(0)});
        uint32_t result = new_gpr();
        emit(A64Op::CsetW, {vr(result)}, static_cast<uint32_t>(cond));
        define(inst.result, result, inst.loc);
        return;
    }
    bool wide = is_wide(operand_type);
    emit(wide ? A64Op::FcmpD : A64Op::FcmpS, {vr(lhs), vr(rhs)});

    air::FloatCond fc = static_cast<air::FloatCond>(inst.aux & 0xFF);
    auto single = [&](Cond cond) {
        uint32_t result = new_gpr();
        emit(A64Op::CsetW, {vr(result)}, static_cast<uint32_t>(cond));
        define(inst.result, result, inst.loc);
    };
    auto pair_or = [&](Cond a, Cond b) {
        uint32_t first = new_gpr();
        uint32_t second = new_gpr();
        uint32_t result = new_gpr();
        emit(A64Op::CsetW, {vr(first)}, static_cast<uint32_t>(a));
        emit(A64Op::CsetW, {vr(second)}, static_cast<uint32_t>(b));
        emit(A64Op::OrrW, {vr(result), vr(first), vr(second)});
        define(inst.result, result, inst.loc);
    };
    switch (fc) {
        case air::FloatCond::Oeq: single(Cond::Eq); break;
        case air::FloatCond::Ogt: single(Cond::Gt); break;
        case air::FloatCond::Oge: single(Cond::Ge); break;
        case air::FloatCond::Olt: single(Cond::Mi); break;
        case air::FloatCond::Ole: single(Cond::Ls); break;
        case air::FloatCond::Ord: single(Cond::Vc); break;
        case air::FloatCond::Uno: single(Cond::Vs); break;
        case air::FloatCond::Ugt: single(Cond::Hi); break;
        case air::FloatCond::Uge: single(Cond::Pl); break;
        case air::FloatCond::Ult: single(Cond::Lt); break;
        case air::FloatCond::Ule: single(Cond::Le); break;
        case air::FloatCond::Une: single(Cond::Ne); break;
        case air::FloatCond::One: pair_or(Cond::Mi, Cond::Gt); break;
        case air::FloatCond::Ueq: pair_or(Cond::Eq, Cond::Vs); break;
    }
}

namespace {

int a64_named_reg_index(const std::string& name) {
    if (name == "sp" || name == "wsp") {
        return static_cast<int>(SP);
    }
    if (name == "fp") {
        return static_cast<int>(X29);
    }
    if (name == "lr") {
        return static_cast<int>(X30);
    }
    if (name.size() < 2) {
        return -1;
    }
    for (size_t i = 1; i < name.size(); ++i) {
        if (!std::isdigit(static_cast<unsigned char>(name[i]))) {
            return -1;
        }
    }
    int number = std::atoi(name.c_str() + 1);
    switch (name[0]) {
        case 'x': case 'w': case 'r':
            return (number >= 0 && number <= 30) ? number : -1;
        case 'v': case 'q': case 'd': case 's': case 'h': case 'b':
            return (number >= 0 && number <= 31)
                       ? static_cast<int>(v(static_cast<uint32_t>(number)))
                       : -1;
        default:
            return -1;
    }
}

std::string a64_asm_reg_name(uint32_t phys, bool wide, char view) {
    if (is_fpr_index(phys)) {
        char kind = view != 0 ? view : (wide ? 'd' : 's');
        return std::string(1, kind) + std::to_string(phys - V0);
    }
    return a64_gpr_name(phys, view != 0 ? view == 'x' : wide);
}

} // namespace

void ISel::lower_asm(const air::InstData& inst, air::InstId inst_id,
                     const std::vector<std::string>& labels) {
    SrcLoc loc = inst.loc;
    std::span<const air::ValueId> ops = func_.operands(inst_id);
    const air::AsmPayload& payload =
        mod_.asm_payload(static_cast<uint32_t>(inst.aux));
    size_t n = payload.constraints.size();
    if (ops.size() != n || payload.operand_types.size() != n) {
        error("inline asm operand metadata is inconsistent", loc);
        return;
    }
    const std::vector<std::string>& bindings = payload.register_bindings;
    if (!bindings.empty() && bindings.size() != n) {
        error("inline asm register-binding metadata is inconsistent", loc);
        return;
    }

    struct OpInfo {
        AsmOperandRole role = AsmOperandRole::Input;
        AsmOperandKind kind = AsmOperandKind::Register;
        uint32_t phys = 0;
        bool has_phys = false;
        bool is_fp = false;
        bool is_memory = false;
        int tied_to = -1;
        air::TypeId type;
    };
    std::vector<OpInfo> info(n);
    std::set<uint32_t> reserved;
    std::set<uint32_t> claimed_out;
    std::set<uint32_t> claimed_in;
    std::set<uint32_t> save_set;

    auto claim_touch = [&](uint32_t phys, const std::string& what) -> bool {
        if (phys == SP) {
            error("inline asm cannot write the stack pointer (" + what + ")",
                  loc);
            return false;
        }
        if (phys == X29) {
            error("inline asm cannot write the frame pointer (" + what + ")",
                  loc);
            return false;
        }
        if (is_callee_saved_reg(phys) || phys == X30) {
            save_set.insert(phys);
        }
        reserved.insert(phys);
        return true;
    };

    for (const std::string& clobber : payload.clobbers) {
        if (clobber == "memory" || clobber == "cc") {
            continue;
        }
        int reg = a64_named_reg_index(clobber);
        if (reg < 0) {

            continue;
        }
        if (!claim_touch(static_cast<uint32_t>(reg),
                         "clobber '" + clobber + "'")) {
            return;
        }
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
        switch (c.kind) {
            case AsmOperandKind::Immediate:
                break;
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
                break;
            case AsmOperandKind::Register:
                if (c.letter == 'w' || c.letter == 'x') {
                    info[i].is_fp = true;
                } else if (c.letter != 'r') {
                    unsupported("the '" + std::string(1, c.letter) +
                                "' register constraint on AArch64", loc);
                    return;
                } else if (is_fp_type(info[i].type)) {
                    unsupported("a floating-point asm operand with the 'r' "
                                "constraint on AArch64", loc);
                    return;
                }
                break;
            default:
                unsupported("this asm operand constraint on AArch64", loc);
                return;
        }

        bool needs_register = info[i].kind == AsmOperandKind::Register ||
                              info[i].is_memory;
        const std::string& binding = bindings.empty() ? std::string() : bindings[i];
        if (binding.empty() || !needs_register) {
            continue;
        }
        int reg = a64_named_reg_index(binding);
        if (reg < 0) {
            error("unknown register '" + binding + "' in an asm operand "
                  "binding", loc);
            return;
        }
        uint32_t phys = static_cast<uint32_t>(reg);
        if (!claim_touch(phys, "binding '" + binding + "'")) {
            return;
        }

        std::set<uint32_t>& role_claims =
            info[i].role == AsmOperandRole::Input ? claimed_in : claimed_out;
        if (!role_claims.insert(phys).second) {
            error("two asm operands are bound to register '" + binding + "'",
                  loc);
            return;
        }
        info[i].phys = phys;
        info[i].has_phys = true;
        info[i].is_fp = is_fpr_index(phys);
    }

    static const uint32_t kGprPool[] = {0, 1, 2, 3, 4, 5, 6, 7};
    static const uint32_t kFprPool[] = {v(0), v(1), v(2), v(3),
                                        v(4), v(5), v(6), v(7)};
    size_t next_gpr = 0;
    size_t next_fpr = 0;
    for (size_t i = 0; i < n; ++i) {
        if (info[i].has_phys || info[i].kind == AsmOperandKind::Immediate ||
            info[i].kind == AsmOperandKind::Tied) {
            continue;
        }

        bool want_fp = info[i].is_fp && !info[i].is_memory;
        const uint32_t* pool = want_fp ? kFprPool : kGprPool;
        size_t pool_size = want_fp ? std::size(kFprPool) : std::size(kGprPool);
        size_t& cursor = want_fp ? next_fpr : next_gpr;
        bool assigned = false;
        while (cursor < pool_size) {
            uint32_t candidate = pool[cursor++];
            if (reserved.count(candidate) != 0) {
                continue;
            }
            reserved.insert(candidate);
            info[i].phys = candidate;
            info[i].has_phys = true;
            info[i].is_fp = want_fp;
            assigned = true;
            break;
        }
        if (!assigned) {
            unsupported("inline asm needs more registers than the backend "
                        "allocates for it", loc);
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
        info[i].is_fp = target.is_fp;
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

    struct SavedReg {
        uint32_t phys = 0;
        uint32_t slot = 0;
    };
    std::vector<SavedReg> saved;
    saved.reserve(save_set.size());
    for (uint32_t phys : save_set) {
        SavedReg entry;
        entry.phys = phys;
        entry.slot = out_.new_frame_object(8, 8);
        MInst store;
        store.opcode = op(is_fpr_index(phys) ? A64Op::StrD : A64Op::StrX);
        store.operands = {pr(phys), MOperand::make_frame(entry.slot),
                          MOperand::make_imm(0)};
        cur().insts.push_back(std::move(store));
        saved.push_back(entry);
    }

    for (size_t i = 0; i < n; ++i) {
        if (!info[i].has_phys) {
            continue;
        }
        if (info[i].is_memory) {

            emit(A64Op::MovX, {pr(info[i].phys), vr(src[i])});
            continue;
        }
        if (info[i].role == AsmOperandRole::ReadWriteOutput) {
            MInst load;
            load.opcode = op(load_op_for(info[i].type));
            load.operands.push_back(pr(info[i].phys));
            load.operands.push_back(vr(src[i]));
            load.operands.push_back(MOperand::make_imm(0));
            cur().insts.push_back(std::move(load));
        } else if (info[i].role == AsmOperandRole::Input) {
            emit(asm_move_op(info[i].type, info[i].is_fp,
                             /*to_phys=*/true),
                 {pr(info[i].phys), vr(src[i])});
        }
    }

    const std::string& tmpl = payload.text;
    std::string resolved;
    std::string template_error;
    for (size_t i = 0; i < tmpl.size() && template_error.empty(); ++i) {
        if (tmpl[i] != '%') {
            resolved += tmpl[i];
            continue;
        }
        if (i + 1 >= tmpl.size()) {
            template_error = "a trailing '%'";
            break;
        }
        char modifier = tmpl[i + 1];
        if (modifier == '%') {
            resolved += '%';
            ++i;
            continue;
        }
        size_t j = i + 1;
        char view = 0;
        bool bare_constant = false;
        bool label_reference = false;
        if (!std::isdigit(static_cast<unsigned char>(modifier))) {
            switch (modifier) {
                case 'x': case 'w':
                case 's': case 'd': case 'q': case 'h': case 'b':
                    view = modifier;
                    break;
                case 'c':
                    bare_constant = true;
                    break;
                case 'l':
                    label_reference = true;
                    break;
                case 'H':
                    template_error =
                        "'%H' (it needs a 128-bit operand pair, which AIR "
                        "does not carry)";
                    break;
                case 'a':
                    template_error =
                        "'%a' (use a memory constraint for an address "
                        "operand)";
                    break;
                default:
                    template_error =
                        "the '%" + std::string(1, modifier) + "' modifier";
                    break;
            }
            if (!template_error.empty()) {
                break;
            }
            ++j;
        }
        if (j >= tmpl.size() ||
            !std::isdigit(static_cast<unsigned char>(tmpl[j]))) {
            template_error = "an operand reference with no number";
            break;
        }
        size_t number = 0;
        while (j < tmpl.size() &&
               std::isdigit(static_cast<unsigned char>(tmpl[j]))) {
            number = number * 10 + static_cast<size_t>(tmpl[j] - '0');
            ++j;
        }
        if (label_reference) {

            size_t label_index = number >= n ? number - n : number;
            if (label_index >= labels.size()) {
                template_error = "a reference to label " +
                                 std::to_string(number) +
                                 ", which does not exist";
                break;
            }
            resolved += labels[label_index];
            i = j - 1;
            continue;
        }
        if (number >= n) {
            template_error = "a reference to operand " +
                             std::to_string(number) + ", which does not exist";
            break;
        }
        const OpInfo& target = info[number];
        if (target.kind == AsmOperandKind::Immediate) {
            if (!bare_constant) {
                resolved += '#';
            }
            resolved += std::to_string(imm[number]);
        } else if (target.is_memory) {
            resolved += '[';
            resolved += a64_gpr_name(target.phys, true);
            resolved += ']';
        } else if (bare_constant) {
            template_error = "'%c' on a register operand";
            break;
        } else if (view != 0 && (view == 'x' || view == 'w') != !target.is_fp) {
            template_error = target.is_fp
                ? "a general-register view of a floating-point operand"
                : "a floating-point view of a general-register operand";
            break;
        } else {
            resolved += a64_asm_reg_name(target.phys, is_wide(target.type),
                                         view);
        }
        i = j - 1;
    }
    if (!template_error.empty()) {
        unsupported("this inline asm template form: " + template_error, loc);
        return;
    }

    out_.asm_texts.push_back("\t" + resolved + "\n");
    emit(A64Op::AsmBlock, {},
         static_cast<uint32_t>(out_.asm_texts.size()) - 1);

    std::vector<uint32_t> captured(n, 0);
    auto is_captured_output = [&](size_t i) {
        return info[i].has_phys && !info[i].is_memory &&
               info[i].tied_to < 0 &&
               info[i].role != AsmOperandRole::Input;
    };
    for (size_t i = 0; i < n; ++i) {
        if (!is_captured_output(i)) {
            continue;
        }
        captured[i] = is_fp_type(info[i].type) ? new_fpr() : new_gpr();
        emit(asm_move_op(info[i].type, info[i].is_fp, /*to_phys=*/false),
             {vr(captured[i]), pr(info[i].phys)});
    }
    for (size_t i = 0; i < n; ++i) {
        if (!is_captured_output(i)) {
            continue;
        }
        MInst store;
        store.opcode = op(store_op_for(info[i].type));
        store.operands.push_back(vr(captured[i]));
        store.operands.push_back(vr(src[i]));
        store.operands.push_back(MOperand::make_imm(0));
        cur().insts.push_back(std::move(store));
    }

    for (const SavedReg& entry : saved) {
        MInst load;
        load.opcode = op(is_fpr_index(entry.phys) ? A64Op::LdrD : A64Op::LdrX);
        load.operands = {pr(entry.phys), MOperand::make_frame(entry.slot),
                         MOperand::make_imm(0)};
        cur().insts.push_back(std::move(load));
    }
}

void ISel::lower_call(const air::InstData& inst, air::InstId inst_id) {
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
        bool fp;
        bool wide;
        bool f128;
    };

    uint64_t dynamic_outgoing = 0;
    if (out_.has_dynamic_stack) {
        uint32_t plan_gpr = 0;
        uint32_t plan_fpr = 0;
        uint64_t planned = 0;
        for (size_t i = 0; i < arg_vregs.size(); ++i) {
            air::TypeId type = arg_types[i];
            bool named = i < sig.params.size();
            bool variadic_slot =
                sig.is_variadic && !named && !standard_aapcs_;
            bool fp = is_fp_type(type);
            bool to_stack = false;
            if (named && sig.params[i].role == air::ParamRole::Sret) {

            } else if (variadic_slot) {
                to_stack = true;
            } else if (fp) {
                if (plan_fpr >= 8) { to_stack = true; } else { ++plan_fpr; }
            } else {
                if (plan_gpr >= 8) { to_stack = true; } else { ++plan_gpr; }
            }
            if (to_stack) {
                uint64_t slot_size = (variadic_slot || standard_aapcs_)
                    ? std::max<uint64_t>(8, scalar_size(type))
                    : scalar_size(type);
                planned = (planned + slot_size - 1) & ~(slot_size - 1);
                planned += slot_size;
            }
        }
        dynamic_outgoing = (planned + 15) & ~uint64_t{15};
        if (dynamic_outgoing > 4095) {
            unsupported("outgoing stack arguments this large in a "
                        "dynamic-stack function", inst.loc);
            return;
        }
        if (dynamic_outgoing > 0) {
            emit(A64Op::SubXri,
                 {pr(SP), pr(SP),
                  MOperand::make_imm(static_cast<int64_t>(dynamic_outgoing))});
        }
    }

    std::vector<RegMove> reg_moves;
    uint32_t next_gpr = 0;
    uint32_t next_fpr = 0;
    uint64_t stack_off = 0;
    for (size_t i = 0; i < arg_vregs.size(); ++i) {
        air::TypeId type = arg_types[i];
        bool named = i < sig.params.size();
        bool variadic_slot = sig.is_variadic && !named && !standard_aapcs_;
        bool fp = is_fp_type(type);
        uint64_t size = scalar_size(type);
        uint32_t phys = 0;
        bool to_stack = false;
        if (named && sig.params[i].role == air::ParamRole::Sret) {
            phys = X8;
        } else if (variadic_slot) {
            to_stack = true;
        } else if (fp) {
            if (next_fpr >= 8) {
                to_stack = true;
            } else {
                phys = v(next_fpr++);
            }
        } else {
            if (next_gpr >= 8) {
                to_stack = true;
            } else {
                phys = next_gpr++;
            }
        }
        if (!to_stack) {
            reg_moves.push_back(
                {phys, arg_vregs[i], fp, is_wide(type), is_f128(type)});
            continue;
        }

        uint64_t slot_size = (variadic_slot || standard_aapcs_)
            ? std::max<uint64_t>(8, size)
            : size;
        stack_off = (stack_off + slot_size - 1) & ~(slot_size - 1);
        A64Op store_op;
        if (variadic_slot) {

            store_op = fp ? (is_wide(type) ? A64Op::StrD : A64Op::StrS)
                          : A64Op::StrX;
        } else {
            store_op = store_op_for(type);
        }
        emit(store_op, {vr(arg_vregs[i]), pr(SP),
                        MOperand::make_imm(static_cast<int64_t>(stack_off))});
        stack_off += slot_size;
    }
    uint64_t outgoing = (stack_off + 15) & ~uint64_t{15};
    if (!out_.has_dynamic_stack) {
        out_.max_outgoing_bytes =
            std::max<uint32_t>(out_.max_outgoing_bytes,
                               static_cast<uint32_t>(outgoing));
    }

    for (const RegMove& move : reg_moves) {
        if (move.f128) {
            emit(A64Op::MovV16b, {pr(move.phys), vr(move.vreg)});
        } else if (move.fp) {
            emit(move.wide ? A64Op::FmovD : A64Op::FmovS,
                 {pr(move.phys), vr(move.vreg)});
        } else {
            emit(move.wide ? A64Op::MovX : A64Op::MovW,
                 {pr(move.phys), vr(move.vreg)});
        }
    }

    if (indirect) {
        emit(A64Op::MovX, {pr(X17), vr(callee_vreg)});
        emit(A64Op::Blr, {pr(X17)});
    } else {
        emit(A64Op::Bl, {MOperand::make_symbol(callee_symbol, SymFlavor::Plain)});
    }
    if (dynamic_outgoing > 0) {
        emit(A64Op::AddXri,
             {pr(SP), pr(SP),
              MOperand::make_imm(static_cast<int64_t>(dynamic_outgoing))});
    }

    if (sig.ret_class == air::RetClass::Scalar && inst.result.is_valid()) {
        bool fp = is_fp_type(sig.ret_type);
        uint32_t result = new_reg_for(sig.ret_type);
        if (is_f128(sig.ret_type)) {
            emit(A64Op::MovV16b, {vr(result), pr(V0)});
        } else if (fp) {
            emit(is_wide(sig.ret_type) ? A64Op::FmovD : A64Op::FmovS,
                 {vr(result), pr(V0)});
        } else {
            emit(is_wide(sig.ret_type) ? A64Op::MovX : A64Op::MovW,
                 {vr(result), pr(X0)});
        }
        define(inst.result, result, inst.loc);
    } else if (pair_ret) {

        uint32_t low = new_gpr();
        uint32_t high = new_gpr();
        emit(A64Op::MovX, {vr(low), pr(X0)});
        emit(A64Op::MovX, {vr(high), pr(X1)});
        uint32_t dest = use_reg(ret_dest, inst.loc);
        emit(A64Op::StrX, {vr(low), vr(dest), MOperand::make_imm(0)});
        emit(A64Op::StrX, {vr(high), vr(dest), MOperand::make_imm(8)});
    } else if (hfa_ret) {
        bool f128 = is_f128(sig.ret_type);
        bool wide = is_wide(sig.ret_type);
        int64_t element_size = f128 ? 16 : wide ? 8 : 4;
        A64Op move_op = f128 ? A64Op::MovV16b
                       : wide ? A64Op::FmovD
                              : A64Op::FmovS;
        A64Op store_op = f128 ? A64Op::StrQ
                        : wide ? A64Op::StrD
                               : A64Op::StrS;
        std::vector<uint32_t> lanes;
        for (uint8_t lane = 0; lane < sig.ret_count; ++lane) {
            uint32_t copy = f128 ? new_fpr128() : new_fpr();
            emit(move_op, {vr(copy), pr(v(lane))});
            lanes.push_back(copy);
        }
        uint32_t dest = use_reg(ret_dest, inst.loc);
        for (uint8_t lane = 0; lane < sig.ret_count; ++lane) {
            emit(store_op,
                 {vr(lanes[lane]), vr(dest),
                  MOperand::make_imm(lane * element_size)});
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
            uint32_t value = use_reg(ops[0], inst.loc);
            if (is_f128(sig.ret_type)) {
                emit(A64Op::MovV16b, {pr(V0), vr(value)});
            } else if (is_fp_type(sig.ret_type)) {
                emit(is_wide(sig.ret_type) ? A64Op::FmovD : A64Op::FmovS,
                     {pr(V0), vr(value)});
            } else {
                emit(is_wide(sig.ret_type) ? A64Op::MovX : A64Op::MovW,
                     {pr(X0), vr(value)});
            }
            break;
        }
        case air::RetClass::IntPair: {
            uint32_t buffer = use_reg(ops[0], inst.loc);
            emit(A64Op::MovX, {pr(X16), vr(buffer)});
            emit(A64Op::LdrX, {pr(X0), pr(X16), MOperand::make_imm(0)});
            emit(A64Op::LdrX, {pr(X1), pr(X16), MOperand::make_imm(8)});
            break;
        }
        case air::RetClass::Hfa: {
            uint32_t buffer = use_reg(ops[0], inst.loc);
            emit(A64Op::MovX, {pr(X16), vr(buffer)});
            bool f128 = is_f128(sig.ret_type);
            bool wide = is_wide(sig.ret_type);
            int64_t element_size = f128 ? 16 : wide ? 8 : 4;
            A64Op load_op = f128 ? A64Op::LdrQ
                           : wide ? A64Op::LdrD
                                  : A64Op::LdrS;
            for (uint8_t lane = 0; lane < sig.ret_count; ++lane) {
                emit(load_op,
                     {pr(v(lane)), pr(X16),
                      MOperand::make_imm(lane * element_size)});
            }
            break;
        }
        case air::RetClass::IndirectSret:

            break;
    }
    emit(A64Op::EpilogueRet, {});
}

void ISel::lower_tail_call(const air::InstData& inst, air::InstId inst_id) {

    std::span<const air::ValueId> ops = func_.operands(inst_id);
    air::SigId sig_id{static_cast<uint32_t>(inst.aux)};
    const air::SigData& sig = mod_.types().signature(sig_id);
    air::ValueId callee_value = ops[0];
    std::span<const air::ValueId> args = ops.subspan(1);
    if (sig.is_variadic || args.size() > 8) {
        unsupported("this tail-call argument shape", inst.loc);
        return;
    }
    std::vector<uint32_t> arg_vregs;
    arg_vregs.reserve(args.size());
    for (size_t i = 0; i < args.size(); ++i) {
        if (is_fp_type(func_.value_type(args[i])) ||
            (i < sig.params.size() &&
             sig.params[i].role != air::ParamRole::Normal)) {
            unsupported("this tail-call argument shape", inst.loc);
            return;
        }
        arg_vregs.push_back(use_reg(args[i], inst.loc));
    }
    uint32_t callee_vreg = use_reg(callee_value, inst.loc);
    for (size_t i = 0; i < arg_vregs.size(); ++i) {
        bool wide = is_wide(func_.value_type(args[i]));
        emit(wide ? A64Op::MovX : A64Op::MovW,
             {pr(static_cast<uint32_t>(i)), vr(arg_vregs[i])});
    }
    emit(A64Op::MovX, {pr(X17), vr(callee_vreg)});
    emit(A64Op::EpilogueTailBr, {});
}

void ISel::lower_inst(air::InstId inst_id) {
    const air::InstData& inst = func_.inst(inst_id);
    std::span<const air::ValueId> ops = func_.operands(inst_id);
    SrcLoc loc = inst.loc;

    auto binary_int = [&](A64Op w, A64Op x, bool remask) {
        uint32_t lhs = use_reg(ops[0], loc);
        uint32_t rhs = use_reg(ops[1], loc);
        uint32_t result = new_gpr();
        emit(is_wide(inst.type) ? x : w, {vr(result), vr(lhs), vr(rhs)});
        if (remask) {
            mask_subword(inst.type, result);
        }
        define(inst.result, result, loc);
    };
    auto binary_fp = [&](A64Op s, A64Op d) {
        uint32_t lhs = use_reg(ops[0], loc);
        uint32_t rhs = use_reg(ops[1], loc);
        uint32_t result = new_fpr();
        emit(is_wide(inst.type) ? d : s, {vr(result), vr(lhs), vr(rhs)});
        define(inst.result, result, loc);
    };
    auto unary_rr = [&](A64Op o, bool fp_result) {
        uint32_t src = use_reg(ops[0], loc);
        uint32_t result = fp_result ? new_fpr() : new_gpr();
        emit(o, {vr(result), vr(src)});
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
            emit(A64Op::MovX, {pr(X0), vr(dst)});
            if (inst.op == air::Opcode::Memset) {
                emit(A64Op::MovW, {pr(X1), vr(src)});
            } else {
                emit(A64Op::MovX, {pr(X1), vr(src)});
            }
            emit(A64Op::MovX, {pr(X2), vr(size)});
            const char* callee = inst.op == air::Opcode::Memcpy ? "memcpy"
                                 : inst.op == air::Opcode::Memmove ? "memmove"
                                                                   : "memset";
            emit(A64Op::Bl,
                 {MOperand::make_symbol(sym_name(mod_.target(), callee, false),
                                        SymFlavor::Plain)});
            return;
        }

        case air::Opcode::Iadd: binary_int(A64Op::AddW, A64Op::AddX, true); return;
        case air::Opcode::Isub: binary_int(A64Op::SubW, A64Op::SubX, true); return;
        case air::Opcode::Imul: binary_int(A64Op::MulW, A64Op::MulX, true); return;
        case air::Opcode::Iand: binary_int(A64Op::AndW, A64Op::AndX, false); return;
        case air::Opcode::Ior: binary_int(A64Op::OrrW, A64Op::OrrX, false); return;
        case air::Opcode::Ixor: binary_int(A64Op::EorW, A64Op::EorX, false); return;
        case air::Opcode::Shl: binary_int(A64Op::LslW, A64Op::LslX, true); return;
        case air::Opcode::Sdiv: binary_int(A64Op::SdivW, A64Op::SdivX, false); return;
        case air::Opcode::Udiv: binary_int(A64Op::UdivW, A64Op::UdivX, false); return;
        case air::Opcode::Ashr: binary_int(A64Op::AsrW, A64Op::AsrX, false); return;
        case air::Opcode::Lshr: binary_int(A64Op::LsrW, A64Op::LsrX, false); return;
        case air::Opcode::Srem:
        case air::Opcode::Urem: {
            uint32_t lhs = use_reg(ops[0], loc);
            uint32_t rhs = use_reg(ops[1], loc);
            uint32_t quotient = new_gpr();
            uint32_t result = new_gpr();
            bool wide = is_wide(inst.type);
            bool is_signed = inst.op == air::Opcode::Srem;
            emit(wide ? (is_signed ? A64Op::SdivX : A64Op::UdivX)
                      : (is_signed ? A64Op::SdivW : A64Op::UdivW),
                 {vr(quotient), vr(lhs), vr(rhs)});
            emit(wide ? A64Op::MsubX : A64Op::MsubW,
                 {vr(result), vr(quotient), vr(rhs), vr(lhs)});
            define(inst.result, result, loc);
            return;
        }

        case air::Opcode::Fadd:
        case air::Opcode::Fsub:
        case air::Opcode::Fmul:
        case air::Opcode::Fdiv: {
            if (is_f128(inst.type)) {
                const char* fn = inst.op == air::Opcode::Fadd   ? "__addtf3"
                                 : inst.op == air::Opcode::Fsub ? "__subtf3"
                                 : inst.op == air::Opcode::Fmul ? "__multf3"
                                                                : "__divtf3";
                uint32_t lhs = use_reg(ops[0], loc);
                uint32_t rhs = use_reg(ops[1], loc);
                define(inst.result,
                       f128_libcall(fn, {{lhs, 'q'}, {rhs, 'q'}}, 'q'), loc);
                return;
            }
            switch (inst.op) {
                case air::Opcode::Fadd: binary_fp(A64Op::FaddS, A64Op::FaddD); break;
                case air::Opcode::Fsub: binary_fp(A64Op::FsubS, A64Op::FsubD); break;
                case air::Opcode::Fmul: binary_fp(A64Op::FmulS, A64Op::FmulD); break;
                default: binary_fp(A64Op::FdivS, A64Op::FdivD); break;
            }
            return;
        }
        case air::Opcode::Fneg:
            if (is_f128(inst.type)) {

                uint32_t src = use_reg(ops[0], loc);
                uint32_t slot = out_.new_frame_object(16, 16);
                MInst store;
                store.opcode = op(A64Op::StrQ);
                store.operands = {vr(src), MOperand::make_frame(slot),
                                  MOperand::make_imm(0)};
                cur().insts.push_back(std::move(store));
                uint32_t high = new_gpr();
                MInst load_high;
                load_high.opcode = op(A64Op::LdrX);
                load_high.operands = {vr(high), MOperand::make_frame(slot),
                                      MOperand::make_imm(8)};
                cur().insts.push_back(std::move(load_high));
                uint32_t mask = materialize_int(0x8000000000000000ull, true);
                uint32_t flipped = new_gpr();
                emit(A64Op::EorX, {vr(flipped), vr(high), vr(mask)});
                MInst store_high;
                store_high.opcode = op(A64Op::StrX);
                store_high.operands = {vr(flipped), MOperand::make_frame(slot),
                                       MOperand::make_imm(8)};
                cur().insts.push_back(std::move(store_high));
                uint32_t result = new_fpr128();
                MInst load;
                load.opcode = op(A64Op::LdrQ);
                load.operands = {vr(result), MOperand::make_frame(slot),
                                 MOperand::make_imm(0)};
                cur().insts.push_back(std::move(load));
                define(inst.result, result, loc);
                return;
            }
            unary_rr(is_wide(inst.type) ? A64Op::FnegD : A64Op::FnegS, true);
            return;
        case air::Opcode::Frem:
            unsupported("floating-point remainder", loc);
            return;

        case air::Opcode::Icmp: lower_icmp(inst, inst_id); return;
        case air::Opcode::Fcmp: lower_fcmp(inst, inst_id); return;

        case air::Opcode::Trunc: {
            uint32_t src = use_reg(ops[0], loc);
            uint16_t width = int_width(inst.type);
            uint32_t result = new_gpr();
            if (width == 8 || width == 16) {
                emit(A64Op::AndWri, {vr(result), vr(src),
                                     MOperand::make_imm(width == 8 ? 0xFF : 0xFFFF)});
            } else {

                emit(A64Op::MovW, {vr(result), vr(src)});
            }
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::Zext: {
            uint32_t src = use_reg(ops[0], loc);
            uint16_t from = int_width(func_.value_type(ops[0]));
            uint32_t result = new_gpr();
            if (from == 8) {
                emit(A64Op::UxtbW, {vr(result), vr(src)});
            } else if (from == 16) {
                emit(A64Op::UxthW, {vr(result), vr(src)});
            } else {
                emit(A64Op::MovW, {vr(result), vr(src)});
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
                emit(wide ? A64Op::SxtbX : A64Op::SxtbW, {vr(result), vr(src)});
            } else if (from == 16) {
                emit(wide ? A64Op::SxthX : A64Op::SxthW, {vr(result), vr(src)});
            } else if (from == 32 && wide) {
                emit(A64Op::Sxtw, {vr(result), vr(src)});
            } else {
                emit(A64Op::MovW, {vr(result), vr(src)});
            }
            if (!wide) {
                mask_subword(inst.type, result);
            }
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::Fptrunc: {
            air::TypeId src_type = func_.value_type(ops[0]);
            if (is_f128(src_type)) {
                bool to_double = is_wide(inst.type);
                uint32_t src = use_reg(ops[0], loc);
                define(inst.result,
                       f128_libcall(to_double ? "__trunctfdf2" : "__trunctfsf2",
                                    {{src, 'q'}}, to_double ? 'd' : 's'),
                       loc);
                return;
            }
            unary_rr(A64Op::FcvtSD, true);
            return;
        }
        case air::Opcode::Fpext: {
            if (is_f128(inst.type)) {
                air::TypeId src_type = func_.value_type(ops[0]);
                bool from_double = is_wide(src_type);
                uint32_t src = use_reg(ops[0], loc);
                define(inst.result,
                       f128_libcall(from_double ? "__extenddftf2"
                                                : "__extendsftf2",
                                    {{src, from_double ? 'd' : 's'}}, 'q'),
                       loc);
                return;
            }
            unary_rr(A64Op::FcvtDS, true);
            return;
        }
        case air::Opcode::Fptosi:
        case air::Opcode::Fptoui: {
            if (is_f128(func_.value_type(ops[0]))) {
                bool dst_wide128 = is_wide(inst.type);
                bool signed128 = inst.op == air::Opcode::Fptosi;
                const char* fn = dst_wide128
                    ? (signed128 ? "__fixtfdi" : "__fixunstfdi")
                    : (signed128 ? "__fixtfsi" : "__fixunstfsi");
                uint32_t src = use_reg(ops[0], loc);
                uint32_t result = f128_libcall(fn, {{src, 'q'}},
                                               dst_wide128 ? 'x' : 'w');
                if (!dst_wide128) {
                    mask_subword(inst.type, result);
                }
                define(inst.result, result, loc);
                return;
            }
            bool src_wide = is_wide(func_.value_type(ops[0]));
            bool dst_wide = is_wide(inst.type);
            bool s = inst.op == air::Opcode::Fptosi;
            A64Op cvt;
            if (dst_wide) {
                cvt = src_wide ? (s ? A64Op::FcvtzsXD : A64Op::FcvtzuXD)
                               : (s ? A64Op::FcvtzsXS : A64Op::FcvtzuXS);
            } else {
                cvt = src_wide ? (s ? A64Op::FcvtzsWD : A64Op::FcvtzuWD)
                               : (s ? A64Op::FcvtzsWS : A64Op::FcvtzuWS);
            }
            uint32_t src = use_reg(ops[0], loc);
            uint32_t result = new_gpr();
            emit(cvt, {vr(result), vr(src)});
            if (!dst_wide) {
                mask_subword(inst.type, result);
            }
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::Sitofp:
        case air::Opcode::Uitofp: {
            air::TypeId src_type = func_.value_type(ops[0]);
            uint32_t src = use_reg(ops[0], loc);
            bool s = inst.op == air::Opcode::Sitofp;
            uint16_t from = int_width(src_type);
            if (is_f128(inst.type)) {
                if (from == 8 || from == 16) {
                    uint32_t extended = new_gpr();
                    if (s) {
                        emit(from == 8 ? A64Op::SxtbW : A64Op::SxthW,
                             {vr(extended), vr(src)});
                    } else {
                        emit(from == 8 ? A64Op::UxtbW : A64Op::UxthW,
                             {vr(extended), vr(src)});
                    }
                    src = extended;
                }
                bool src_wide128 = from > 32;
                const char* fn = src_wide128
                    ? (s ? "__floatditf" : "__floatunditf")
                    : (s ? "__floatsitf" : "__floatunsitf");
                define(inst.result,
                       f128_libcall(fn, {{src, src_wide128 ? 'x' : 'w'}}, 'q'),
                       loc);
                return;
            }
            if (from == 8 || from == 16) {
                uint32_t extended = new_gpr();
                if (s) {
                    emit(from == 8 ? A64Op::SxtbW : A64Op::SxthW,
                         {vr(extended), vr(src)});
                } else {
                    emit(from == 8 ? A64Op::UxtbW : A64Op::UxthW,
                         {vr(extended), vr(src)});
                }
                src = extended;
            }
            bool src_wide = from > 32;
            bool dst_wide = is_wide(inst.type);
            A64Op cvt;
            if (dst_wide) {
                cvt = src_wide ? (s ? A64Op::ScvtfDX : A64Op::UcvtfDX)
                               : (s ? A64Op::ScvtfDW : A64Op::UcvtfDW);
            } else {
                cvt = src_wide ? (s ? A64Op::ScvtfSX : A64Op::UcvtfSX)
                               : (s ? A64Op::ScvtfSW : A64Op::UcvtfSW);
            }
            uint32_t result = new_fpr();
            emit(cvt, {vr(result), vr(src)});
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::Ptrtoint:
        case air::Opcode::Inttoptr: {
            uint32_t src = use_reg(ops[0], loc);
            uint32_t result = new_gpr();
            bool dst_wide = is_wide(inst.type);
            emit(dst_wide ? A64Op::MovX : A64Op::MovW, {vr(result), vr(src)});
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
                emit(is_wide(src_type) ? A64Op::FmovXD : A64Op::FmovWS,
                     {vr(result), vr(src)});
            } else if (!src_fp && dst_fp) {
                emit(is_wide(inst.type) ? A64Op::FmovDX : A64Op::FmovSW,
                     {vr(result), vr(src)});
            } else if (src_fp && dst_fp) {
                emit(is_wide(inst.type) ? A64Op::FmovD : A64Op::FmovS,
                     {vr(result), vr(src)});
            } else {
                emit(is_wide(inst.type) ? A64Op::MovX : A64Op::MovW,
                     {vr(result), vr(src)});
            }
            define(inst.result, result, loc);
            return;
        }

        case air::Opcode::PtrAdd: {
            uint32_t base = use_reg(ops[0], loc);
            uint32_t offset = use_reg(ops[1], loc);
            uint32_t result = new_gpr();
            emit(A64Op::AddX, {vr(result), vr(base), vr(offset)});
            define(inst.result, result, loc);
            return;
        }

        case air::Opcode::Select: {
            emit_truth_test(ops[0], loc);
            air::TypeId type = inst.type;
            bool fp = is_fp_type(type);
            uint32_t lhs = use_reg(ops[1], loc);
            uint32_t rhs = use_reg(ops[2], loc);
            uint32_t result = fp ? new_fpr() : new_gpr();
            A64Op sel = fp ? (is_wide(type) ? A64Op::FcselD : A64Op::FcselS)
                           : (is_wide(type) ? A64Op::CselX : A64Op::CselW);
            emit(sel, {vr(result), vr(lhs), vr(rhs)},
                 static_cast<uint32_t>(Cond::Ne));
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
                emit(A64Op::B, {MOperand::make_label(target)});
            }
            return;
        case air::Opcode::EhAllocException: {
            uint32_t size = materialize_int(inst.aux, true);
            emit(A64Op::MovX, {pr(X0), vr(size)});
            emit(A64Op::Bl,
                 {MOperand::make_symbol(sym_name(mod_.target(), "__cxa_allocate_exception", false),
                                        SymFlavor::Plain)});
            uint32_t result = new_gpr();
            emit(A64Op::MovX, {vr(result), pr(X0)});
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::EhLandingPad: {
            uint32_t result = new_gpr();
            emit(A64Op::MovX, {vr(result), pr(X0)});
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::EhSelector: {
            uint32_t result = new_gpr();
            emit(A64Op::MovW, {vr(result), pr(X1)});
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
            emit(A64Op::MovX, {pr(X0), vr(exception)});
            emit(A64Op::Bl,
                 {MOperand::make_symbol(sym_name(mod_.target(), "__cxa_begin_catch", false),
                                        SymFlavor::Plain)});
            uint32_t result = new_gpr();
            emit(A64Op::MovX, {vr(result), pr(X0)});
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::CatchEnd:
            emit(A64Op::Bl,
                 {MOperand::make_symbol(sym_name(mod_.target(), "__cxa_end_catch", false),
                                        SymFlavor::Plain)});
            return;
        case air::Opcode::Throw: {
            uint32_t exception = use_reg(ops[0], loc);
            uint32_t typeinfo = use_reg(ops[1], loc);
            uint32_t destructor = ops.size() > 2 ? use_reg(ops[2], loc)
                                                 : materialize_int(0, true);
            emit(A64Op::MovX, {pr(X0), vr(exception)});
            emit(A64Op::MovX, {pr(X1), vr(typeinfo)});
            emit(A64Op::MovX, {pr(X2), vr(destructor)});
            emit(A64Op::Bl,
                 {MOperand::make_symbol(sym_name(mod_.target(), "__cxa_throw", false), SymFlavor::Plain)});
            emit(A64Op::Brk, {MOperand::make_imm(1)});
            return;
        }
        case air::Opcode::Rethrow:
            emit(A64Op::Bl,
                 {MOperand::make_symbol(sym_name(mod_.target(), "__cxa_rethrow", false), SymFlavor::Plain)});
            emit(A64Op::Brk, {MOperand::make_imm(1)});
            return;
        case air::Opcode::Resume: {
            uint32_t exception = use_reg(ops[0], loc);
            emit(A64Op::MovX, {pr(X0), vr(exception)});
            emit(A64Op::Bl,
                 {MOperand::make_symbol(sym_name(mod_.target(), "_Unwind_Resume", false), SymFlavor::Plain)});
            emit(A64Op::Brk, {MOperand::make_imm(1)});
            return;
        }

        case air::Opcode::Trap:
            emit(A64Op::Brk, {MOperand::make_imm(1)});

            start_dead_block();
            return;

        case air::Opcode::Unreachable:
            emit(A64Op::Brk, {MOperand::make_imm(1)});
            return;

        case air::Opcode::Jump: {
            air::BlockCallId call{air::aux_low(inst.aux)};
            if (opt_) {
                emit_parallel_copies(call, loc);
            } else {
                emit_edge_stores(call, loc);
            }
            uint32_t target = block_map_.at(func_.block_call(call).target.index);
            emit(A64Op::B, {MOperand::make_label(target)});
            return;
        }
        case air::Opcode::BrIf: {
            air::BlockCallId then_call{air::aux_low(inst.aux)};
            air::BlockCallId else_call{air::aux_high(inst.aux)};
            emit_truth_test(ops[0], loc);
            uint32_t then_target = edge_target(then_call, loc);
            uint32_t else_target = edge_target(else_call, loc);
            emit(A64Op::Bcc, {MOperand::make_label(then_target)},
                 static_cast<uint32_t>(Cond::Ne));
            emit(A64Op::B, {MOperand::make_label(else_target)});
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
                if (case_bits <= 4095) {
                    emit(wide ? A64Op::CmpXri : A64Op::CmpWri,
                         {vr(value), MOperand::make_imm(
                                         static_cast<int64_t>(case_bits))});
                } else {
                    uint32_t imm = materialize_int(case_bits, wide);
                    emit(wide ? A64Op::CmpX : A64Op::CmpW, {vr(value), vr(imm)});
                }
                uint32_t target = edge_target(switch_case.target, loc);
                emit(A64Op::Bcc, {MOperand::make_label(target)},
                     static_cast<uint32_t>(Cond::Eq));
            }
            uint32_t default_target = edge_target(default_call, loc);
            emit(A64Op::B, {MOperand::make_label(default_target)});
            return;
        }
        case air::Opcode::Ret:
            lower_ret(inst, inst_id);
            return;
        case air::Opcode::TailCallIndirect:
            lower_tail_call(inst, inst_id);
            return;

        case air::Opcode::StackAllocDyn: {
            uint32_t size = use_reg(ops[0], loc);
            uint32_t rounded = new_gpr();
            emit(A64Op::AddXri,
                 {vr(rounded), vr(size), MOperand::make_imm(15)});
            uint32_t mask = materialize_int(~uint64_t{15}, true);
            uint32_t aligned = new_gpr();
            emit(A64Op::AndX, {vr(aligned), vr(rounded), vr(mask)});
            uint32_t old_sp = new_gpr();
            emit(A64Op::MovX, {vr(old_sp), pr(SP)});
            uint32_t new_sp = new_gpr();
            emit(A64Op::SubX, {vr(new_sp), vr(old_sp), vr(aligned)});
            emit(A64Op::MovX, {pr(SP), vr(new_sp)});
            define(inst.result, new_sp, loc);
            return;
        }
        case air::Opcode::StackSave: {
            uint32_t saved = new_gpr();
            emit(A64Op::MovX, {vr(saved), pr(SP)});
            define(inst.result, saved, loc);
            return;
        }
        case air::Opcode::StackRestore: {
            uint32_t saved = use_reg(ops[0], loc);
            emit(A64Op::MovX, {pr(SP), vr(saved)});
            return;
        }
        case air::Opcode::AtomicLoad: {
            if (is_fp_type(inst.type)) {
                unsupported("atomic floating-point access", loc);
                return;
            }
            uint32_t result = new_gpr();
            uint64_t size = scalar_size(inst.type);
            A64Op load_op = size == 1 ? A64Op::LdarbW
                            : size == 2 ? A64Op::LdarhW
                            : size == 4 ? A64Op::LdarW
                                        : A64Op::LdarX;
            MInst load;
            load.opcode = op(load_op);
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
            uint64_t size = scalar_size(value_type);
            A64Op store_op = size == 1 ? A64Op::StlrbW
                             : size == 2 ? A64Op::StlrhW
                             : size == 4 ? A64Op::StlrW
                                         : A64Op::StlrX;
            MInst store;
            store.opcode = op(store_op);
            store.operands.push_back(vr(value));
            store.operands.push_back(mem_base(ops[1], loc));
            store.operands.push_back(MOperand::make_imm(0));
            cur().insts.push_back(std::move(store));
            return;
        }
        case air::Opcode::AtomicRmw: {
            air::RmwOp rmw = air::rmw_op(inst.aux);
            if (rmw == air::RmwOp::Nand) {
                unsupported("atomic nand (no LSE encoding)", loc);
                return;
            }
            air::TypeId value_type = inst.type;
            if (is_fp_type(value_type)) {
                unsupported("atomic floating-point access", loc);
                return;
            }
            uint64_t size = scalar_size(value_type);
            uint32_t size_index = size == 1 ? 0 : size == 2 ? 1 : size == 4 ? 2 : 3;
            uint32_t value = use_reg(ops[1], loc);

            if (rmw == air::RmwOp::Sub || rmw == air::RmwOp::And) {
                uint32_t adjusted = new_gpr();
                bool wide = size == 8;
                A64Op fix = rmw == air::RmwOp::Sub
                    ? (wide ? A64Op::NegX : A64Op::NegW)
                    : (wide ? A64Op::MvnX : A64Op::MvnW);
                emit(fix, {vr(adjusted), vr(value)});
                value = adjusted;
            }
            static constexpr A64Op kAdd[4] = {A64Op::LdaddalbW, A64Op::LdaddalhW,
                                              A64Op::LdaddalW, A64Op::LdaddalX};
            static constexpr A64Op kClr[4] = {A64Op::LdclralbW, A64Op::LdclralhW,
                                              A64Op::LdclralW, A64Op::LdclralX};
            static constexpr A64Op kSet[4] = {A64Op::LdsetalbW, A64Op::LdsetalhW,
                                              A64Op::LdsetalW, A64Op::LdsetalX};
            static constexpr A64Op kEor[4] = {A64Op::LdeoralbW, A64Op::LdeoralhW,
                                              A64Op::LdeoralW, A64Op::LdeoralX};
            static constexpr A64Op kSwp[4] = {A64Op::SwpalbW, A64Op::SwpalhW,
                                              A64Op::SwpalW, A64Op::SwpalX};
            A64Op lse = A64Op::SwpalW;
            switch (rmw) {
                case air::RmwOp::Xchg: lse = kSwp[size_index]; break;
                case air::RmwOp::Add:
                case air::RmwOp::Sub: lse = kAdd[size_index]; break;
                case air::RmwOp::And: lse = kClr[size_index]; break;
                case air::RmwOp::Or: lse = kSet[size_index]; break;
                case air::RmwOp::Xor: lse = kEor[size_index]; break;
                default:
                    unsupported("atomic read-modify-write operation", loc);
                    return;
            }
            uint32_t old_value = new_gpr();
            MInst rmw_inst;
            rmw_inst.opcode = op(lse);
            rmw_inst.operands.push_back(vr(old_value));
            rmw_inst.operands.push_back(vr(value));
            rmw_inst.operands.push_back(mem_base(ops[0], loc));
            cur().insts.push_back(std::move(rmw_inst));
            define(inst.result, old_value, loc);
            return;
        }
        case air::Opcode::AtomicCas: {
            air::TypeId value_type = inst.type;
            if (is_fp_type(value_type)) {
                unsupported("atomic floating-point access", loc);
                return;
            }
            uint64_t size = scalar_size(value_type);
            A64Op cas = size == 1 ? A64Op::CasalbW
                        : size == 2 ? A64Op::CasalhW
                        : size == 4 ? A64Op::CasalW
                                    : A64Op::CasalX;
            uint32_t expected = use_reg(ops[1], loc);
            uint32_t desired = use_reg(ops[2], loc);

            uint32_t old_value = new_gpr();
            emit(size == 8 ? A64Op::MovX : A64Op::MovW,
                 {vr(old_value), vr(expected)});
            MInst cas_inst;
            cas_inst.opcode = op(cas);
            cas_inst.operands.push_back(vr(old_value));
            cas_inst.operands.push_back(vr(desired));
            cas_inst.operands.push_back(mem_base(ops[0], loc));
            cur().insts.push_back(std::move(cas_inst));
            define(inst.result, old_value, loc);
            return;
        }
        case air::Opcode::Fence:
            emit(A64Op::DmbIsh, {});
            return;
        case air::Opcode::Bswap: {
            uint16_t width = int_width(inst.type);
            uint32_t value = use_reg(ops[0], loc);
            uint32_t result = new_gpr();
            if (width == 16) {
                emit(A64Op::Rev16W, {vr(result), vr(value)});
                mask_subword(inst.type, result);
            } else if (width == 32) {
                emit(A64Op::RevW, {vr(result), vr(value)});
            } else if (width == 64) {
                emit(A64Op::RevX, {vr(result), vr(value)});
            } else {
                unsupported("bswap width", loc);
                return;
            }
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
            if (inst.op == air::Opcode::Ctz) {
                uint32_t reversed = new_gpr();
                emit(wide ? A64Op::RbitX : A64Op::RbitW,
                     {vr(reversed), vr(value)});
                value = reversed;
            }
            uint32_t result = new_gpr();
            emit(wide ? A64Op::ClzX : A64Op::ClzW, {vr(result), vr(value)});
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::Popcnt: {
            uint16_t width = int_width(inst.type);
            if (width != 32 && width != 64) {
                unsupported("population-count width", loc);
                return;
            }
            bool wide = width == 64;
            uint32_t value = use_reg(ops[0], loc);
            uint32_t lane = new_fpr();
            emit(wide ? A64Op::FmovDX : A64Op::FmovSW, {vr(lane), vr(value)});
            uint32_t counted = new_fpr();
            emit(A64Op::CntV8b, {vr(counted), vr(lane)});
            uint32_t summed = new_fpr();
            emit(A64Op::AddvB8, {vr(summed), vr(counted)});
            uint32_t result = new_gpr();
            emit(A64Op::FmovWS, {vr(result), vr(summed)});
            define(inst.result, result, loc);
            return;
        }
        case air::Opcode::VaStart: {
            uint32_t list = use_reg(ops[0], loc);
            if (!standard_aapcs_) {

                emit(A64Op::AddXri,
                     {pr(X16), pr(X29),
                      MOperand::make_imm(static_cast<int64_t>(
                          16 + out_.named_stack_bytes))});
                emit(A64Op::StrX, {pr(X16), vr(list), MOperand::make_imm(0)});
                return;
            }

            uint32_t stack_top = new_gpr();
            emit(A64Op::AddXri,
                 {vr(stack_top), pr(X29),
                  MOperand::make_imm(static_cast<int64_t>(
                      16 + out_.named_stack_bytes))});
            emit(A64Op::StrX, {vr(stack_top), vr(list), MOperand::make_imm(0)});

            const int64_t gr_bytes = (8 - static_cast<int64_t>(named_gprs_)) * 8;
            if (gr_save_frame_ >= 0 && gr_bytes > 0) {
                uint32_t gr_base = new_gpr();
                emit(A64Op::FrameAddr,
                     {vr(gr_base), MOperand::make_frame(
                                       static_cast<uint32_t>(gr_save_frame_))});
                uint32_t gr_top = new_gpr();
                emit(A64Op::AddXri, {vr(gr_top), vr(gr_base),
                                     MOperand::make_imm(gr_bytes)});
                emit(A64Op::StrX, {vr(gr_top), vr(list), MOperand::make_imm(8)});
                uint32_t gr_offs = materialize_int(
                    static_cast<uint32_t>(-gr_bytes), false);
                emit(A64Op::StrW,
                     {vr(gr_offs), vr(list), MOperand::make_imm(24)});
            } else {
                emit(A64Op::StrX, {pr(XZR), vr(list), MOperand::make_imm(8)});
                emit(A64Op::StrW, {pr(XZR), vr(list), MOperand::make_imm(24)});
            }

            const int64_t vr_bytes =
                (8 - static_cast<int64_t>(named_fprs_)) * 16;
            if (vr_save_frame_ >= 0 && vr_bytes > 0) {
                uint32_t vr_base = new_gpr();
                emit(A64Op::FrameAddr,
                     {vr(vr_base), MOperand::make_frame(
                                       static_cast<uint32_t>(vr_save_frame_))});
                uint32_t vr_top = new_gpr();
                emit(A64Op::AddXri, {vr(vr_top), vr(vr_base),
                                     MOperand::make_imm(vr_bytes)});
                emit(A64Op::StrX,
                     {vr(vr_top), vr(list), MOperand::make_imm(16)});
                uint32_t vr_offs = materialize_int(
                    static_cast<uint32_t>(-vr_bytes), false);
                emit(A64Op::StrW,
                     {vr(vr_offs), vr(list), MOperand::make_imm(28)});
            } else {
                emit(A64Op::StrX, {pr(XZR), vr(list), MOperand::make_imm(16)});
                emit(A64Op::StrW, {pr(XZR), vr(list), MOperand::make_imm(28)});
            }
            return;
        }
        case air::Opcode::InlineAsm:
            lower_asm(inst, inst_id);
            return;
        case air::Opcode::AsmGoto: {

            std::vector<air::BlockCallId> edges;
            func_.successors(inst_id, edges);
            if (edges.empty()) {
                error("asm goto has no fallthrough edge", loc);
                return;
            }

            const char* label_prefix =
                object_format_for(mod_.target()) == ObjectFormat::Elf
                    ? ".LBB" : "LBB";
            std::vector<std::string> labels;
            labels.reserve(edges.size() - 1);
            for (size_t e = 1; e < edges.size(); ++e) {
                uint32_t mblock =
                    block_map_.at(func_.block_call(edges[e]).target.index);
                labels.push_back(label_prefix + std::to_string(out_.index) +
                                 "_" + std::to_string(mblock));
            }

            lower_asm(inst, inst_id, labels);
            if (opt_) {
                for (air::BlockCallId edge : edges) {
                    out_.blocks[cur_block_].succs.push_back(
                        block_map_.at(func_.block_call(edge).target.index));
                }
            }
            emit(A64Op::B,
                 {MOperand::make_label(
                     block_map_.at(func_.block_call(edges[0]).target.index))});
            return;
        }
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
            emit(A64Op::BrReg, {vr(target)});
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
        uint32_t bytes = is_f128(type) ? 16 : 8;
        slots_[v.index] = Slot{out_.new_frame_object(bytes, bytes), type};
    };

    for (air::BlockId block_id : layout) {
        if (!opt_) {
            for (air::ValueId param : func_.block_params(block_id)) {
                note_slot(param);
            }
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
            if (opt_) {
                continue;
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
                if (force_slot || def_block_of(used) != block_id.index) {
                    note_slot(used);
                }
            };
            for (air::ValueId used : func_.operands(inst_id)) {
                note_use(used, false);
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
    uint32_t next_gpr = 0;
    uint32_t next_fpr = 0;
    uint64_t incoming_stack = 0;
    for (size_t i = 0; i < entry_params.size(); ++i) {
        air::TypeId type = sig.params[i].type;
        auto slot = slots_.find(entry_params[i].index);
        bool fp = is_fp_type(type);
        uint64_t size = scalar_size(type);
        bool on_stack = false;
        uint32_t incoming = 0;
        if (sig.params[i].role == air::ParamRole::Sret) {
            incoming = X8;
        } else if (fp) {
            if (next_fpr >= 8) {
                on_stack = true;
            } else {
                incoming = v(next_fpr++);
            }
        } else {
            if (next_gpr >= 8) {
                on_stack = true;
            } else {
                incoming = next_gpr++;
            }
        }
        if (on_stack) {

            if (standard_aapcs_) {
                uint64_t slot = std::max<uint64_t>(8, size);
                incoming_stack = (incoming_stack + slot - 1) & ~(slot - 1);
                size = slot;
            } else {
                incoming_stack = (incoming_stack + size - 1) & ~(size - 1);
            }
        }
        if (opt_) {

            uint32_t dest = canonical_vreg(entry_params[i]);
            if (on_stack) {
                MInst load;
                load.opcode = op(load_op_for(type));
                load.operands.push_back(vr(dest));
                load.operands.push_back(pr(X29));
                load.operands.push_back(MOperand::make_imm(
                    static_cast<int64_t>(16 + incoming_stack)));
                cur().insts.push_back(std::move(load));
                incoming_stack += size;
                continue;
            }
            if (is_f128(type)) {
                emit(A64Op::MovV16b, {vr(dest), pr(incoming)});
            } else if (fp) {
                emit(is_wide(type) ? A64Op::FmovD : A64Op::FmovS,
                     {vr(dest), pr(incoming)});
            } else {
                emit(is_wide(type) ? A64Op::MovX : A64Op::MovW,
                     {vr(dest), pr(incoming)});
            }
            continue;
        }
        if (slot == slots_.end()) {
            if (on_stack) {
                incoming_stack += size;
            }
            continue;
        }
        if (on_stack) {
            uint32_t scratch = fp ? V31 : X16;
            MInst load;
            load.opcode = op(load_op_for(type));
            load.operands.push_back(pr(scratch));
            load.operands.push_back(pr(X29));
            load.operands.push_back(MOperand::make_imm(
                static_cast<int64_t>(16 + incoming_stack)));
            cur().insts.push_back(std::move(load));
            incoming = scratch;
            incoming_stack += size;
        }
        MInst store;
        store.opcode = op(store_op_for(type));
        store.operands.push_back(pr(incoming));
        store.operands.push_back(MOperand::make_frame(slot->second.frame_index));
        store.operands.push_back(MOperand::make_imm(0));
        cur().insts.push_back(std::move(store));
    }
    out_.named_stack_bytes =
        static_cast<uint32_t>((incoming_stack + 7) & ~uint64_t{7});
    named_gprs_ = next_gpr;
    named_fprs_ = next_fpr;

    if (standard_aapcs_ && sig.is_variadic) {

        if (named_gprs_ < 8) {
            gr_save_frame_ = static_cast<int32_t>(
                out_.new_frame_object((8 - named_gprs_) * 8u, 8));
            for (uint32_t reg = named_gprs_; reg < 8; ++reg) {
                MInst store;
                store.opcode = op(A64Op::StrX);
                store.operands.push_back(pr(reg));
                store.operands.push_back(MOperand::make_frame(
                    static_cast<uint32_t>(gr_save_frame_)));
                store.operands.push_back(MOperand::make_imm(
                    static_cast<int64_t>((reg - named_gprs_) * 8u)));
                cur().insts.push_back(std::move(store));
            }
        }
        if (named_fprs_ < 8) {
            vr_save_frame_ = static_cast<int32_t>(
                out_.new_frame_object((8 - named_fprs_) * 16u, 16));
            for (uint32_t reg = named_fprs_; reg < 8; ++reg) {
                MInst store;
                store.opcode = op(A64Op::StrQ);
                store.operands.push_back(pr(v(reg)));
                store.operands.push_back(MOperand::make_frame(
                    static_cast<uint32_t>(vr_save_frame_)));
                store.operands.push_back(MOperand::make_imm(
                    static_cast<int64_t>((reg - named_fprs_) * 16u)));
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

} // namespace aburi::backend::aarch64
