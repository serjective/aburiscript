#include <cstdlib>
#include "frontend.h"

#include <sstream>
#include <stdexcept>

#include "../cirpasses/coro_split.h"
#include "../cirpasses/objc_lower.h"
#include "../collect/collect.h"
#include "../perf_stats.h"
#include "../preprocessor.h"

namespace aburi::frontend {
namespace {

bool diagnostic_is_error(const Diagnostic& diag) {
    return diag.level == DiagnosticLevel::Error;
}

void apply_header_search(PreProcess& pp,
                         const HeaderSearchResult& search,
                         bool cxx_mode) {
    pp.sm->quote_look_paths.insert(pp.sm->quote_look_paths.end(),
        search.quote_include_paths.begin(), search.quote_include_paths.end());
    pp.sm->source_look_paths.insert(pp.sm->source_look_paths.end(),
        search.include_paths.begin(), search.include_paths.end());
    pp.sm->cxx_stdlib_lookup_active = cxx_mode;
    pp.sm->requested_cxx_stdlib = stdlib_kind_name(search.cxx_stdlib.requested);
    pp.sm->resolved_cxx_stdlib = stdlib_kind_name(search.cxx_stdlib.resolved);
    pp.sm->attempted_cxx_stdlib_paths = search.cxx_stdlib.attempted_paths;
}

void append_manual_header_paths(PreProcess& pp,
                                const FrontendInvocation& invocation) {
    pp.sm->source_look_paths.insert(pp.sm->source_look_paths.end(),
        invocation.include_paths.begin(), invocation.include_paths.end());
    pp.sm->source_look_paths.insert(pp.sm->source_look_paths.end(),
        invocation.system_include_paths.begin(), invocation.system_include_paths.end());
    pp.sm->quote_look_paths.insert(pp.sm->quote_look_paths.end(),
        invocation.quote_include_paths.begin(), invocation.quote_include_paths.end());
}

void apply_driver_header_search(PreProcess& pp,
                                const FrontendInvocation& invocation,
                                const TargetInfo& target) {
    HeaderSearchOptions header_options;
    header_options.argv0 = invocation.argv0_for_header_discovery;
    header_options.target_triple = target.triple;
    header_options.cxx_mode = invocation.lang_options.is_cxx_mode();
    header_options.requested_stdlib = invocation.requested_stdlib;
    header_options.adinkra_root = invocation.adinkra_root;
    header_options.include_paths = invocation.include_paths;
    header_options.system_include_paths = invocation.system_include_paths;
    header_options.quote_include_paths = invocation.quote_include_paths;
    header_options.sysroots = invocation.sysroots;
    header_options.discover_platform_paths = !invocation.nostdinc;
    header_options.discover_cxx_stdlib_paths = !invocation.nostdincxx;

    apply_header_search(pp,
        build_header_search_paths(header_options),
        invocation.lang_options.is_cxx_mode());
}

PreProcess make_preprocessor(FrontendInvocation& invocation,
                             std::shared_ptr<TargetInfo> target) {
    PreProcess pp(invocation.filename,
        std::move(invocation.source),
        target,
        invocation.lang_options);
    pp.set_perf_profiler(active_perf_profiler());
    pp.sm->inhibit_warnings = invocation.inhibit_warnings;
    pp.builtin_headers_enabled = !invocation.nostdinc;
    if (invocation.use_driver_header_search) {
        apply_driver_header_search(pp, invocation, *target);
    } else {
        append_manual_header_paths(pp, invocation);
    }
    pp.sm->framework_look_paths.insert(pp.sm->framework_look_paths.end(),
        invocation.framework_include_paths.begin(),
        invocation.framework_include_paths.end());
    pp.sm->framework_look_paths.insert(pp.sm->framework_look_paths.end(),
        invocation.system_framework_include_paths.begin(),
        invocation.system_framework_include_paths.end());

    for (const auto& [name, value] : invocation.defines) {
        pp.define_object_macro(name, value);
    }
    for (const std::string& name : invocation.undefines) {
        pp.undef_macro(name);
    }

    for (auto it = invocation.pre_includes.rbegin();
         it != invocation.pre_includes.rend(); ++it) {
        pp.push_pre_include(*it);
    }
    return pp;
}

} // namespace

std::shared_ptr<TargetInfo> resolve_target(const FrontendInvocation& invocation) {
    if (invocation.target) {
        return invocation.target;
    }
    if (!invocation.target_triple.empty()) {
        return TargetInfo::create_for_triple(invocation.target_triple);
    }
    return TargetInfo::create_host();
}

std::string format_diagnostic(const std::shared_ptr<SourceManager>& sm,
                              const Diagnostic& diag) {
    if (sm) {
        return sm->formatDiagnostic(diag.level, diag.message, diag.location);
    }
    return diag.message;
}

bool FrontendResult::has_parse_errors() const {
    for (const Diagnostic& diag : parse_result.diagnostics) {
        if (diagnostic_is_error(diag)) {
            return true;
        }
    }
    return false;
}

bool FrontendResult::ok() const {
    return exception_text.empty() &&
           !has_parse_errors() &&
           tree_verified &&
           cir_verified &&
           !cir.has_errors();
}

std::string FrontendResult::failure_summary() const {
    std::ostringstream out;
    if (!exception_text.empty()) {
        out << "exception: " << exception_text << '\n';
    }
    for (const std::string& diagnostic : diagnostics) {
        out << diagnostic << '\n';
    }
    if (!tree_verified && !tree_verify_output.empty()) {
        out << tree_verify_output;
    }
    if (!cir_verified && !cir_verify_output.empty()) {
        out << cir_verify_output;
    }
    if (cir.has_errors()) {
        out << cir_dump();
    }
    return out.str();
}

std::string FrontendResult::cir_dump() const {
    PerfScopedTimer timer(active_perf_profiler(), PerfPhase::CirDump);
    std::ostringstream out;
    cir.dump(out);
    return out.str();
}

bool JitRunResult::ok() const {
    return frontend.ok() && run_completed;
}

std::string JitRunResult::failure_summary() const {
    std::ostringstream out;
    std::string frontend_summary = frontend.failure_summary();
    if (!frontend_summary.empty()) {
        out << frontend_summary;
        if (frontend_summary.back() != '\n') {
            out << '\n';
        }
    }
    for (const std::string& diagnostic : diagnostics) {
        out << diagnostic << '\n';
    }
    if (!run_completed) {
        out << "run_jit did not complete\n";
    } else {
        out << "run_jit exit code: " << exit_code << '\n';
    }
    return out.str();
}

FrontendResult run_frontend(FrontendInvocation invocation) {
    FrontendResult result;
    try {
        std::shared_ptr<TargetInfo> target = resolve_target(invocation);
        PreProcess pp = make_preprocessor(invocation, target);

        result.source_manager = pp.sm;
        result.tokens = pp.tokenize();

        collect::Session collect_session(invocation.lang_options, target);

        if (std::getenv("ABURI_TXN_INTEGRITY") != nullptr) {
            collect_session.file().set_transaction_integrity_checks(true);
        }
        collect_session.set_source_manager(pp.sm);
        collect_session.set_module_loader(invocation.module_loader);
        syntax::Parser parser(result.tokens,
            invocation.lang_options,
            pp.sm,
            collect_session);
        {
            PerfScopedTimer timer(active_perf_profiler(),
                                  PerfPhase::ParseCollect);
            result.parse_result = parser.parse_translation_unit();
        }
        for (const Diagnostic& diag : result.parse_result.diagnostics) {
            if (invocation.inhibit_warnings &&
                diag.level == DiagnosticLevel::Warning) {
                continue;
            }
            result.diagnostics.push_back(format_diagnostic(pp.sm, diag));
        }

        {
            PerfScopedTimer timer(active_perf_profiler(), PerfPhase::Verify);
            std::ostringstream tree_errors;
            result.tree_verified = result.parse_result.tree.verify(&tree_errors);
            result.tree_verify_output = tree_errors.str();
        }

        if (invocation.export_template_state) {
            result.template_state = collect_session.export_template_state();
        }
        {
            PerfScopedTimer timer(active_perf_profiler(),
                                  PerfPhase::CollectFinish);
            result.cir = collect_session.finish_file();
        }

        if (!result.cir.coroutine_facts().empty()) {
            (void)cirpasses::split_coroutines(result.cir);
        }

        if (invocation.lang_options.is_objc()) {
            (void)cirpasses::lower_objc(
                result.cir, invocation.lang_options.is_objc_arc());
        }

        for (const auto& [error_loc, error_message] : result.cir.errors()) {
            Diagnostic diag{DiagnosticLevel::Error, error_message, error_loc};
            result.diagnostics.push_back(format_diagnostic(pp.sm, diag));
        }
        for (const auto& [warning_loc, warning_message] : result.cir.warnings()) {
            if (invocation.inhibit_warnings) {
                break;
            }
            Diagnostic diag{DiagnosticLevel::Warning, warning_message, warning_loc};
            result.diagnostics.push_back(format_diagnostic(pp.sm, diag));
        }
        for (const auto& [note_loc, note_message] : result.cir.notes()) {
            Diagnostic diag{DiagnosticLevel::Note, note_message, note_loc};
            result.diagnostics.push_back(format_diagnostic(pp.sm, diag));
        }
        {
            PerfScopedTimer timer(active_perf_profiler(), PerfPhase::Verify);
            std::ostringstream cir_errors;
            result.cir_verified = result.cir.verify(&cir_errors);
            result.cir_verify_output = cir_errors.str();
        }

    } catch (const std::exception& ex) {
        result.exception_text = ex.what();
    }
    return result;
}

std::shared_ptr<SourceManager> run_preprocessor(FrontendInvocation invocation,
                                                PreprocessOutputMode mode,
                                                std::ostream& out) {
    std::shared_ptr<TargetInfo> target = resolve_target(invocation);
    PreProcess pp = make_preprocessor(invocation, target);
    if (mode == PreprocessOutputMode::MacroDefinitions) {
        (void)pp.tokenize();
        pp.emit_macro_definitions(out);
        return pp.sm;
    }
    pp.emit_preprocessed_text(out,
        mode != PreprocessOutputMode::TextNoLineMarkers);
    return pp.sm;
}

} // namespace aburi::frontend
