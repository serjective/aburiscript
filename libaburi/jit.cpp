#include "frontend.h"

#include "../cir2llvm/cir2llvm.h"

namespace aburi::frontend {

JitRunResult run_jit(FrontendInvocation invocation) {
    JitRunResult result;
    std::string module_name = invocation.filename;
    bool cxx_mangling = invocation.lang_options.is_cxx_mode();
    result.frontend = run_frontend(std::move(invocation));
    if (!result.frontend.ok()) {
        return result;
    }

    cir2llvm::JitOptions jit_options;
    jit_options.target = result.frontend.cir.target_info_ptr();
    jit_options.module_name = std::move(module_name);
    jit_options.cxx_mangling = cxx_mangling;
    cir2llvm::JitResult jit_result =
        cir2llvm::run_jit(result.frontend.cir, std::move(jit_options));
    for (const Diagnostic& diag : jit_result.diagnostics) {
        result.diagnostics.push_back(
            format_diagnostic(result.frontend.source_manager, diag));
    }
    result.exit_code = jit_result.ok() ? jit_result.exit_code : -1;
    result.run_completed = jit_result.ok();
    return result;
}

} // namespace aburi::frontend
