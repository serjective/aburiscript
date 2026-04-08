#include "library.h"

#include <iostream>
#include <filesystem>

#include "preprocessor.h"
#include "abi/target_info.h"
#include "toolchain_profile.h"

int compile_run_program(std::string prg, LangOptions lang_opts) {
    auto target = TargetInfo::create_host();
    if (target->triple.empty()) {
        target->triple = default_target_triple();
    }

    const std::string input_name = lang_opts.is_cxx_mode() ? "main.cpp" : "main.c";
    PreProcess pp = PreProcess(input_name, prg, target, lang_opts);
    std::error_code ec;
    auto builtin_headers =
        std::filesystem::path(__FILE__).parent_path().parent_path() / "builtin_headers";
    if (std::filesystem::exists(builtin_headers, ec) &&
        std::filesystem::is_directory(builtin_headers, ec)) {
        pp.sm->source_look_paths.push_back(builtin_headers.string());
    }
    auto cxx_stdlib_paths = discover_cxx_stdlib_include_paths(
        nullptr,
        target->triple,
        lang_opts.is_cxx_mode(),
        StdLibKind::Auto);
    pp.sm->cxx_stdlib_lookup_active = lang_opts.is_cxx_mode();
    pp.sm->requested_cxx_stdlib = stdlib_kind_name(StdLibKind::Auto);
    pp.sm->resolved_cxx_stdlib = stdlib_kind_name(cxx_stdlib_paths.resolved);
    pp.sm->attempted_cxx_stdlib_paths = cxx_stdlib_paths.attempted_paths;
    for (const auto& path : cxx_stdlib_paths.include_paths) {
        pp.sm->source_look_paths.push_back(path);
    }
    if (target->os == TargetOS::MACOS) {
        for (const auto& path : discover_macos_sdk_include_paths(nullptr)) {
            pp.sm->source_look_paths.push_back(path);
        }
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
