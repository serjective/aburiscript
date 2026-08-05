#ifndef ABURI_BACKEND_COMMON_REGALLOC_H
#define ABURI_BACKEND_COMMON_REGALLOC_H

#include <cstdint>
#include <vector>

#include "mir.h"

namespace aburi::backend {

struct TargetRegInfo {
    std::vector<uint32_t> gpr_order;
    std::vector<uint32_t> fpr_order;
    bool (*is_callee_saved)(uint32_t phys) = nullptr;
    RegClass (*reg_class)(uint32_t phys) = nullptr;

    std::vector<uint32_t> linear_gpr_caller;
    std::vector<uint32_t> linear_gpr_callee;
    std::vector<uint32_t> linear_fpr_caller;
    std::vector<uint32_t> linear_fpr_callee;
    std::vector<uint32_t> linear_gpr_scratch;
    std::vector<uint32_t> linear_fpr_scratch;
};

struct RegAllocOpcodeInfo {
    bool defines_operand0 = false;
    bool reads_operand0 = false;
    bool is_call = false;
};

using OpcodeInfoFn = RegAllocOpcodeInfo (*)(uint16_t opcode);

struct RegAllocator {
    virtual ~RegAllocator() = default;
    virtual void run(MFunction& function, const TargetRegInfo& regs,
                     OpcodeInfoFn opcode_info) = 0;
};

struct FastRegAllocator final : RegAllocator {
    void run(MFunction& function, const TargetRegInfo& regs,
             OpcodeInfoFn opcode_info) override;
};

struct LinearScanAllocator final : RegAllocator {
    void run(MFunction& function, const TargetRegInfo& regs,
             OpcodeInfoFn opcode_info) override;
};

void set_fast_regalloc_spill_opcodes(uint16_t store_gpr, uint16_t load_gpr,
                                     uint16_t store_fpr, uint16_t load_fpr,
                                     uint16_t store_fpr128,
                                     uint16_t load_fpr128);

uint16_t regalloc_spill_opcode(RegClass cls);
uint16_t regalloc_reload_opcode(RegClass cls);

} // namespace aburi::backend

#endif // ABURI_BACKEND_COMMON_REGALLOC_H
