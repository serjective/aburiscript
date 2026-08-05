#ifndef ABURI_LIBABURI_FRONTEND_H
#define ABURI_LIBABURI_FRONTEND_H

#include <iosfwd>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "../abi/target_info.h"
#include "../cir/file.h"
#include "../diagnostics.h"
#include "../lang_options.h"
#include "../lexer.h"
#include "../parser/parser.h"
#include "../source_mgnt.h"
#include "../toolchain_profile.h"

namespace aburi::modules {
class ModuleLoader;
}

namespace aburi::frontend {

struct FrontendInvocation {
    std::string filename = "test.c";
    std::string source;
    LangOptions lang_options;
    std::shared_ptr<TargetInfo> target;
    std::string target_triple;
    std::vector<std::string> include_paths;
    std::vector<std::string> system_include_paths;
    std::vector<std::string> quote_include_paths;
    std::vector<std::string> framework_include_paths;
    std::vector<std::string> system_framework_include_paths;
    std::vector<std::string> sysroots;
    std::vector<std::string> pre_includes;
    std::vector<std::pair<std::string, std::string>> defines;
    std::vector<std::string> undefines;
    StdLibKind requested_stdlib = StdLibKind::Auto;
    std::string adinkra_root;
    std::string argv0_for_header_discovery;
    bool use_driver_header_search = true;
    bool nostdinc = false;
    bool nostdincxx = false;
    bool inhibit_warnings = false;
    aburi::modules::ModuleLoader* module_loader = nullptr;
    bool export_template_state = false;
};

struct FrontendResult {
    std::shared_ptr<SourceManager> source_manager;
    std::vector<Token> tokens;
    syntax::ParseResult parse_result;
    cir::File cir;
    std::shared_ptr<void> template_state;
    std::vector<std::string> diagnostics;
    std::string exception_text;
    std::string tree_verify_output;
    std::string cir_verify_output;
    bool tree_verified = false;
    bool cir_verified = false;

    bool has_parse_errors() const;
    bool ok() const;
    std::string failure_summary() const;
    std::string cir_dump() const;
};

enum class PreprocessOutputMode {
    Text,
    TextNoLineMarkers,
    MacroDefinitions,
};

struct JitRunResult {
    FrontendResult frontend;
    std::vector<std::string> diagnostics;
    int exit_code = -1;
    bool run_completed = false;

    bool ok() const;
    std::string failure_summary() const;
};

std::shared_ptr<TargetInfo> resolve_target(const FrontendInvocation& invocation);
std::string format_diagnostic(const std::shared_ptr<SourceManager>& sm,
                              const Diagnostic& diag);

FrontendResult run_frontend(FrontendInvocation invocation);

std::shared_ptr<SourceManager> run_preprocessor(FrontendInvocation invocation,
                                                PreprocessOutputMode mode,
                                                std::ostream& out);
JitRunResult run_jit(FrontendInvocation invocation);

} // namespace aburi::frontend

#endif // ABURI_LIBABURI_FRONTEND_H
