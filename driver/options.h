#ifndef ABURI_DRIVER_OPTIONS_H
#define ABURI_DRIVER_OPTIONS_H

#include <iosfwd>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "../lang_options.h"
#include "../perf_stats.h"
#include "../toolchain_profile.h"

namespace aburi::driver {

inline constexpr const char* kAburiProductName = "aburi";
inline constexpr const char* kAburiVersionString = "0.1";

inline constexpr int kGccPersonaMajor = 10;
inline constexpr int kGccPersonaMinor = 2;
inline constexpr int kGccPersonaPatch = 0;
inline constexpr const char* kGccPersonaBrand = "Ghanaian C/C++ compiler :)";

enum class DriverPersona {
    Native,
    ClangCompat,
    GccCompat,
};

enum class EarlyDriverQuery {
    None,
    Version,
    VerboseVersion,
    DumpMachine,
    DumpVersion,
    DumpFullVersion,
    PrintFileName,
};

struct DepfileOptions {
    bool enabled = false;
    bool include_system_headers = false;
    bool phony_targets = false;
    std::string output_path;
    std::vector<std::string> targets;
    bool generate_only = false;
};

struct DriverOptions {
    std::vector<std::string> input_files;
    std::vector<std::string> include_paths;
    std::vector<std::string> system_include_paths;
    std::vector<std::string> quote_include_paths;
    std::vector<std::string> framework_include_paths;
    std::vector<std::string> system_framework_include_paths;
    std::vector<std::string> sysroots;
    std::vector<std::string> pre_includes;
    std::vector<std::string> linker_flags;
    std::string ld_path;
    std::vector<std::pair<std::string, std::string>> defines;
    std::vector<std::string> undefines;
    std::string output_path;
    std::string target_triple;
    std::string cross_cc;
    StdLibKind requested_stdlib = StdLibKind::Auto;
    AdinkraRuntimeKind adinkra_runtime = AdinkraRuntimeKind::Static;
    std::string adinkra_root;
    std::string adinkra_library;
    LangOptions lang_opts;
    bool preprocess_only = false;
    bool dump_macros = false;
    bool preprocess_no_linemarkers = false;
    bool nostdinc = false;
    bool nostdincxx = false;
    bool nostdlib = false;
    bool nostdlibxx = false;
    bool inhibit_warnings = false;
    bool keep_comments = false;
    std::vector<std::string> assembler_flags;
    bool assembler_language = false;
    bool assembler_with_cpp = false;
    bool objc_passthrough = true;
    DepfileOptions depfile;
    bool precompile_only = false;
    std::vector<std::pair<std::string, std::string>> module_files;
    std::vector<std::string> prebuilt_module_paths;
    bool module_output = false;
    bool syntax_only = false;
    bool dump_syntax = false;
    bool dump_cir = false;
    std::string dump_cir_example;
    bool dump_air = false;
    bool verify_mir = false;
    std::string backend = "llvm";
    std::string air_object = "as";
    bool integrated_as = false;
    int opt_level = 0;
    bool pic = true;
    bool fcommon = false;
    bool freestanding = false;
    std::vector<int> reserved_aarch64_gprs;
    bool short_wchar = false;
    bool general_regs_only = false;
    bool aarch64_aes = false;
    bool aarch64_sha2 = false;
    bool branch_target_enforcement = false;
    bool sign_return_address = false;
    bool keep_frame_pointer = false;
    bool emit_llvm = false;
    bool emit_assembly = false;
    bool compile_only = false;
    bool jit = false;
    bool ignore_unknown_options = false;
    bool show_help = false;
    DriverPersona persona = DriverPersona::Native;
    EarlyDriverQuery early_query = EarlyDriverQuery::None;
    std::string print_file_name;
    std::optional<PerfDetail> perf_detail;
    std::string perf_json_path;
};

bool parse_driver_options(int argc, char** argv, DriverOptions& opts);
void print_driver_help(std::ostream& out);

} // namespace aburi::driver

#endif // ABURI_DRIVER_OPTIONS_H
