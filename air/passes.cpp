#include "passes.h"

#include "verifier.h"

#include <unordered_map>
#include <vector>

namespace aburi::air {

PipelineResult run_pipeline(Module& mod, std::span<const FunctionPass> passes,
                            PipelineOptions options) {
    PipelineResult result;
    for (const FunctionPass& pass : passes) {
        for (uint32_t i = 1; i <= mod.function_count(); ++i) {
            Function& func = mod.function(FuncId{i});
            if (func.is_declaration()) {
                continue;
            }
            bool changed = pass.run(func, mod);
            result.changed |= changed;
            if (changed && options.verify_each) {
                VerifyResult verify;
                verify_function(mod, func, verify);
                if (!verify.ok()) {
                    result.verified = false;
                    result.verify_error = std::string("after pass '") + pass.name +
                                          "': " + verify.to_string();
                    return result;
                }
            }
        }
    }
    return result;
}

namespace {

bool is_removable(const InstData& data) {
    if (opcode_result_kind(data.op) != ResultKind::Value) {
        return false;
    }
    if (opcode_has_side_effects(data.op)) {
        return false;
    }
    if (data.flags & INST_FLAG_VOLATILE) {
        return false;
    }
    return true;
}

} // namespace

bool run_dce(Function& func, Module& mod) {
    (void)mod;
    bool changed = false;
    bool round_changed = true;
    std::vector<BlockCallId> succs;
    while (round_changed) {
        round_changed = false;

        std::unordered_map<uint32_t, uint32_t> uses;
        for (BlockId b = func.first_block(); b.is_valid(); b = func.block(b).next) {
            for (InstId i = func.block(b).first; i.is_valid();
                 i = func.inst(i).next) {
                for (ValueId op : func.operands(i)) {
                    ++uses[op.index];
                }
                func.successors(i, succs);
                for (BlockCallId call : succs) {
                    for (ValueId arg : func.block_call_args(call)) {
                        ++uses[arg.index];
                    }
                }
            }
        }

        for (BlockId b = func.first_block(); b.is_valid(); b = func.block(b).next) {
            InstId i = func.block(b).first;
            while (i.is_valid()) {
                InstId next = func.inst(i).next;
                const InstData& data = func.inst(i);
                if (is_removable(data) && uses[data.result.index] == 0) {
                    func.remove_inst(i);
                    changed = true;
                    round_changed = true;
                }
                i = next;
            }
        }
    }
    return changed;
}

} // namespace aburi::air
