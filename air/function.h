#ifndef ABURI_AIR_FUNCTION_H
#define ABURI_AIR_FUNCTION_H

#include "insts.h"
#include "ids.h"
#include "types.h"
#include "../source_mgnt.h"

#include <cstdint>
#include <span>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

namespace aburi::air {

enum class ValueKind : uint8_t {
    InstResult,
    BlockParam,
    ConstInt,
    ConstFloat,
    ConstNull,
    Undef,
    GlobalAddr,
    FuncAddr,
    LabelAddr,
};

struct ValueData {
    ValueKind kind = ValueKind::Undef;
    TypeId type;
    uint64_t payload = 0;
    uint64_t payload2 = 0;
};

struct InstData {
    Opcode op = Opcode::Unreachable;
    uint16_t flags = 0;
    TypeId type;
    uint32_t op_begin = 0;
    uint32_t op_count = 0;
    uint64_t aux = 0;
    uint64_t aux2 = 0;
    ValueId result;
    BlockId block;
    InstId prev, next;
    SrcLoc loc;
};

struct BlockData {
    InstId first, last;
    uint32_t param_begin = 0;
    uint32_t param_count = 0;
    BlockId prev, next;
};

struct BlockCall {
    BlockId target;
    uint32_t arg_begin = 0;
    uint32_t arg_count = 0;
};

struct SwitchCase {
    uint64_t value = 0;
    BlockCallId target;
};

enum class Linkage : uint8_t {
    External,
    Internal,
    LinkOnceODR,
    Weak,
    Common,
};

enum class SymbolVisibility : uint8_t {
    Default,
    Hidden,
    Protected
};

struct SymbolAttrs {
    SymbolVisibility visibility = SymbolVisibility::Default;
    bool hidden = false;
    bool no_prefix = false;
    std::string comdat_key;
};

inline uint64_t pack_stack_alloc_aux(uint64_t size_bytes, uint8_t align_log2) {
    return (static_cast<uint64_t>(align_log2) << 56) | (size_bytes & ((1ull << 56) - 1));
}
inline uint64_t stack_alloc_size(uint64_t aux) { return aux & ((1ull << 56) - 1); }
inline uint8_t stack_alloc_align_log2(uint64_t aux) { return static_cast<uint8_t>(aux >> 56); }

inline uint64_t pack_pair_aux(uint32_t low, uint32_t high) {
    return static_cast<uint64_t>(low) | (static_cast<uint64_t>(high) << 32);
}
inline uint32_t aux_low(uint64_t aux) { return static_cast<uint32_t>(aux); }
inline uint32_t aux_high(uint64_t aux) { return static_cast<uint32_t>(aux >> 32); }

class Function {
public:
    Function(std::string name, SigId sig, Linkage linkage = Linkage::External);

    const std::string& name() const { return name_; }
    SigId sig() const { return sig_; }
    void set_sig(SigId sig) { sig_ = sig; }
    Linkage linkage() const { return linkage_; }
    void set_linkage(Linkage linkage) { linkage_ = linkage; }
    SymbolAttrs& attrs() { return attrs_; }
    const SymbolAttrs& attrs() const { return attrs_; }
    bool is_declaration() const { return !entry_block_.is_valid(); }
    SrcLoc loc() const { return loc_; }
    void set_loc(SrcLoc loc) { loc_ = loc; }

    BlockId create_block(std::span<const TypeId> param_types);
    BlockId entry_block() const { return entry_block_; }
    BlockId first_block() const { return entry_block_; }
    const BlockData& block(BlockId id) const;
    std::span<const ValueId> block_params(BlockId id) const;
    ValueId append_block_param(BlockId id, TypeId type);
    void remove_block_param(BlockId id, uint32_t index);
    void set_block_params(BlockId id, std::span<const TypeId> types);
    void remove_block(BlockId id);
    uint32_t block_count() const { return static_cast<uint32_t>(blocks_.size()) - 1; }
    bool is_valid(BlockId id) const { return id.index > 0 && id.index < blocks_.size(); }
    const ValueData& value(ValueId id) const;
    TypeId value_type(ValueId id) const { return value(id).type; }
    uint32_t value_count() const { return static_cast<uint32_t>(values_.size()) - 1; }
    bool is_valid(ValueId id) const { return id.index > 0 && id.index < values_.size(); }
    ValueId const_int(TypeId type, uint64_t bits, uint64_t high_bits = 0);
    ValueId const_float_bits(TypeId type, uint64_t bits, uint64_t high_bits = 0);
    ValueId const_null(TypeId ptr_type);
    ValueId undef(TypeId type);
    ValueId global_addr(GlobalId global, TypeId ptr_type);
    ValueId func_addr(FuncId func, TypeId ptr_type);
    ValueId label_addr(BlockId block, TypeId ptr_type);

    bool is_constant(ValueId id) const;
    InstId def_inst(ValueId id) const;
    void retype_value(ValueId id, TypeId type);

    void set_value_name(ValueId id, std::string_view name);
    std::string_view value_name(ValueId id) const;
    InstId make_inst(Opcode op, TypeId result_type, std::span<const ValueId> operands,
                     uint64_t aux = 0, SrcLoc loc = {}, uint16_t flags = 0,
                     uint64_t aux2 = 0);
    void append_inst(BlockId block, InstId inst);
    void insert_before(InstId pos, InstId inst);
    void remove_inst(InstId inst);

    const InstData& inst(InstId id) const;
    InstData& inst_mut(InstId id);
    std::span<const ValueId> operands(InstId id) const;
    void set_operand(InstId id, uint32_t index, ValueId v);
    uint32_t inst_count() const { return static_cast<uint32_t>(insts_.size()) - 1; }
    bool is_valid(InstId id) const { return id.index > 0 && id.index < insts_.size(); }

    BlockCallId make_block_call(BlockId target, std::span<const ValueId> args);
    const BlockCall& block_call(BlockCallId id) const;
    std::span<const ValueId> block_call_args(BlockCallId id) const;
    void set_block_call_arg(BlockCallId id, uint32_t index, ValueId v);
    void append_block_call_arg(BlockCallId id, ValueId v);
    void remove_block_call_arg(BlockCallId id, uint32_t index);
    void set_block_call_args(BlockCallId id, std::span<const ValueId> args);
    void set_block_call_target(BlockCallId id, BlockId target);
    bool is_valid(BlockCallId id) const {
        return id.index > 0 && id.index < block_calls_.size();
    }

    uint32_t make_jump_table(std::span<const SwitchCase> cases);
    std::span<const SwitchCase> jump_table(uint32_t index) const;
    uint32_t jump_table_count() const { return static_cast<uint32_t>(jump_tables_.size()); }

    uint32_t make_block_call_list(std::span<const BlockCallId> calls);
    std::span<const BlockCallId> block_call_list(uint32_t index) const;
    uint32_t block_call_list_count() const {
        return static_cast<uint32_t>(block_call_lists_.size());
    }

    void successors(InstId id, std::vector<BlockCallId>& out) const;
    void replace_all_uses(ValueId old_value, ValueId new_value);
    uint32_t count_uses(ValueId id) const;

private:
    ValueId new_value(ValueKind kind, TypeId type, uint64_t payload, uint64_t payload2);
    ValueId intern_constant(ValueKind kind, TypeId type, uint64_t payload,
                            uint64_t payload2);
    uint32_t append_operands(std::span<const ValueId> operands);

    std::string name_;
    SigId sig_;
    Linkage linkage_ = Linkage::External;
    SymbolAttrs attrs_;
    SrcLoc loc_;
    BlockId entry_block_;
    BlockId last_block_;

    std::vector<InstData> insts_;
    std::vector<BlockData> blocks_;
    std::vector<ValueData> values_;
    std::vector<BlockCall> block_calls_;
    std::vector<ValueId> operand_pool_;
    std::vector<ValueId> block_param_pool_;
    std::vector<std::vector<SwitchCase>> jump_tables_;
    std::vector<std::vector<BlockCallId>> block_call_lists_;
    std::unordered_multimap<uint64_t, uint32_t> constant_lookup_;
    std::unordered_map<uint32_t, std::string> value_names_;
};

} // namespace aburi::air

#endif // ABURI_AIR_FUNCTION_H
