#include "library.h"

#include <iostream>
#include <filesystem>

#include "preprocessor.h"
#include "abi/target_info.h"

int compile_run_program(std::string prg, LangOptions lang_opts) {
    auto target = TargetInfo::create_host();

    const std::string input_name = lang_opts.is_cxx_mode() ? "main.cpp" : "main.c";
    PreProcess pp = PreProcess(input_name, prg, target, lang_opts);
    std::error_code ec;
    auto builtin_headers =
        std::filesystem::path(__FILE__).parent_path().parent_path() / "builtin_headers";
    if (std::filesystem::exists(builtin_headers, ec) &&
        std::filesystem::is_directory(builtin_headers, ec)) {
        pp.sm->source_look_paths.push_back(builtin_headers.string());
    }
    auto tokens = pp.tokenize();
    auto parse = Parser(tokens, pp.sm, target);
    parse.lang_opts = lang_opts;
    if (parse.ast_ctx && parse.ast_ctx->abi_policy) {
        DriverAbiOptions effective_abi_options;
        if (lang_opts.is_cxx_mode() &&
            parse.ast_ctx->abi_policy->cxx_abi == CxxAbiKind::Itanium) {
            effective_abi_options.cxx_abi = CxxAbiKind::Itanium;
        }
        apply_driver_abi_overrides(*parse.ast_ctx->abi_policy, effective_abi_options);
    }
    auto tree = parse.parse();

    if (!tree) {
        // Errors were already flushed by parse()
        return -1;
    }

    auto cvt2llvm = ASTToLLVM();
    cvt2llvm.sm = pp.sm;
    cvt2llvm.ast_ctx = parse.ast_ctx;
    cvt2llvm.lang_opts = lang_opts;
    cvt2llvm.convert_translation_unit(tree.get());

    //std::cout << "== LLVM IR == " << std::endl;
    // cvt2llvm.dump();
    return cvt2llvm.run();
}
