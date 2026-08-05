#include "library.h"

#include "frontend.h"

int compile_run_program(std::string prg, LangOptions lang_opts) {
    aburi::frontend::FrontendInvocation invocation;
    invocation.filename = lang_opts.is_cxx_mode() ? "main.cpp" : "main.c";
    invocation.source = std::move(prg);
    invocation.lang_options = std::move(lang_opts);

    aburi::frontend::JitRunResult result =
        aburi::frontend::run_jit(std::move(invocation));
    if (!result.ok()) {
        return -1;
    }
    return result.exit_code;
}
