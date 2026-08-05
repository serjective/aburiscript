#ifndef ABURI_BACKEND_COMMON_MIR_H
#define ABURI_BACKEND_COMMON_MIR_H

#include <cstdint>
#include <string>
#include <vector>

#include "../../air/function.h"

namespace aburi::backend {

struct MReg {
    static constexpr uint32_t kVirtualBit = 0x80000000u;

    uint32_t value = 0;

    static MReg phys(uint32_t index) { return MReg{index}; }
    static MReg vreg(uint32_t index) { return MReg{index | kVirtualBit}; }

    bool is_virtual() const { return (value & kVirtualBit) != 0; }
    uint32_t index() const { return value & ~kVirtualBit; }

    bool operator==(const MReg& other) const { return value == other.value; }
    bool operator!=(const MReg& other) const { return value != other.value; }
};

enum class RegClass : uint8_t {
    Gpr,
    Fpr,
    Fpr128,
};

enum class MOperandKind : uint8_t {
    Reg,
    Imm,
    FrameIndex,
    Symbol,
    Label,
};

enum class SymFlavor : uint8_t {
    Plain,
    Page,
    PageOff,
    GotPage,
    GotPageOff,
    GotPcRel,
    TlvPage,
    TlvPageOff,
    TlvPcRel,
};

struct MOperand {
    MOperandKind kind = MOperandKind::Imm;
    MReg reg{};
    int64_t imm = 0;
    uint32_t frame_index = 0;
    std::string symbol;
    SymFlavor flavor = SymFlavor::Plain;
    int64_t addend = 0;
    uint32_t label = 0;

    static MOperand make_reg(MReg reg) {
        MOperand op;
        op.kind = MOperandKind::Reg;
        op.reg = reg;
        return op;
    }
    static MOperand make_imm(int64_t value) {
        MOperand op;
        op.kind = MOperandKind::Imm;
        op.imm = value;
        return op;
    }
    static MOperand make_frame(uint32_t index, int64_t displacement = 0) {
        MOperand op;
        op.kind = MOperandKind::FrameIndex;
        op.frame_index = index;
        op.imm = displacement;
        return op;
    }
    static MOperand make_symbol(std::string name, SymFlavor flavor,
                                int64_t addend = 0) {
        MOperand op;
        op.kind = MOperandKind::Symbol;
        op.symbol = std::move(name);
        op.flavor = flavor;
        op.addend = addend;
        return op;
    }
    static MOperand make_label(uint32_t block_index) {
        MOperand op;
        op.kind = MOperandKind::Label;
        op.label = block_index;
        return op;
    }
};

struct MInst {
    uint16_t opcode = 0;
    uint32_t aux = 0;
    std::vector<MOperand> operands;
};

struct MBlock {
    std::vector<MInst> insts;
    bool address_taken = false;
    std::vector<uint32_t> succs;
};

struct MEhCallSite {
    uint32_t begin_label = 0;
    uint32_t end_label = 0;
    uint32_t landing_pad_block = 0;
    uint32_t action_label = 0;
};

struct MEhAction {
    uint32_t label = 0;
    int32_t filter = 0;
    uint32_t next_label = 0;
};

struct MEhTypeInfo {
    uint32_t filter = 0;
    std::string symbol;
};

struct FrameObject {
    uint64_t size = 0;
    uint32_t align = 1;
};

struct MFunction {
    std::string name;
    air::Linkage linkage = air::Linkage::External;
    air::SymbolAttrs attrs;
    uint32_t index = 0;

    std::vector<MBlock> blocks;
    std::vector<FrameObject> frame_objects;
    std::vector<RegClass> vreg_classes;

    std::vector<uint32_t> used_csrs;
    std::vector<std::pair<uint32_t, int32_t>> csr_cfa_offsets;

    uint32_t max_outgoing_bytes = 0;
    uint32_t named_stack_bytes = 0;
    bool has_dynamic_stack = false;
    bool needs_frame_pointer = false;
    uint32_t frame_size = 0;
    uint8_t word_bytes = 8;
    bool legacy32 = false;
    uint32_t callee_pop_bytes = 0;
    uint32_t next_eh_label = 0;
    std::vector<MEhCallSite> eh_call_sites;
    std::vector<MEhAction> eh_actions;
    std::vector<MEhTypeInfo> eh_typeinfos;
    std::vector<std::string> asm_texts;

    uint32_t new_vreg(RegClass cls) {
        vreg_classes.push_back(cls);
        return static_cast<uint32_t>(vreg_classes.size()) - 1;
    }
    uint32_t new_frame_object(uint64_t size, uint32_t align) {
        frame_objects.push_back({size, align});
        return static_cast<uint32_t>(frame_objects.size()) - 1;
    }
    uint32_t new_eh_label() { return ++next_eh_label; }
};

} // namespace aburi::backend

#endif // ABURI_BACKEND_COMMON_MIR_H
