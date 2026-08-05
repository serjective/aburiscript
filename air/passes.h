#ifndef ABURI_AIR_PASSES_H
#define ABURI_AIR_PASSES_H

#include "module.h"

#include <span>
#include <string>

namespace aburi::air {

struct FunctionPass {
    const char* name;
    bool (*run)(Function& func, Module& mod);
};

struct PipelineOptions {
    bool verify_each = true;
};

struct PipelineResult {
    bool changed = false;
    bool verified = true;
    std::string verify_error;
};

PipelineResult run_pipeline(Module& mod, std::span<const FunctionPass> passes,
                            PipelineOptions options = {});

bool run_dce(Function& func, Module& mod);

bool run_simplify_cfg(Function& func, Module& mod);

bool run_mem2reg(Function& func, Module& mod);

bool run_instsimplify(Function& func, Module& mod);

PipelineResult run_o1_pipeline(Module& mod, PipelineOptions options = {});

} // namespace aburi::air

#endif // ABURI_AIR_PASSES_H
