#include <iostream>
#include <vector>
#include <string>
#include <filesystem>
#include <algorithm>
#include <unordered_set>
#include <cctype>
#include <cstdlib>
#include <fstream>
#include <optional>
#include "preprocessor.h"
#include "parser/parser.h"
#include "ast/ast_memory_report.h"
#include "ast2llvm/ast2llvm.h"
#include "abi/abi_policy.h"
#include "abi/darwin_blocks.h"
#include "abi/target_info.h"
#include "target_feature_gate.h"
#include "toolchain_profile.h"
#include <llvm/Config/llvm-config.h>
#include <llvm/ADT/SmallString.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/Program.h>

namespace cl = llvm::cl;

static cl::OptionCategory AburiCategory("Aburiscript Options");

static cl::list<std::string> InputFilenames(cl::Positional, cl::desc("<input files>"), cl::ZeroOrMore, cl::cat(AburiCategory));
static cl::opt<std::string> OutputFilename("o", cl::desc("Output filename"), cl::value_desc("filename"), cl::cat(AburiCategory));
static cl::opt<bool> CompileOnly("c", cl::desc("Compile only; do not link"), cl::cat(AburiCategory));
static cl::opt<bool> PreprocessOnly("E", cl::desc("Preprocess only; print post-preprocessed output"), cl::cat(AburiCategory));
static cl::opt<bool> FSyntaxOnly("fsyntax-only",
    cl::desc("Run preprocessing, parsing, and semantic analysis only"),
    cl::init(false), cl::cat(AburiCategory));
static cl::opt<bool> DumpMacroDefinitions("dM",
    cl::desc("With -E, emit macro definitions instead of preprocessed text"),
    cl::init(false), cl::cat(AburiCategory));
static cl::opt<bool> GenerateDependenciesM("M",
    cl::desc("Generate header dependency rules via system compiler passthrough"),
    cl::init(false), cl::cat(AburiCategory));
static cl::opt<bool> GenerateDependenciesMM("MM",
    cl::desc("Generate user-header dependency rules via system compiler passthrough"),
    cl::init(false), cl::cat(AburiCategory));
static cl::opt<bool> EmitAssembly("S", cl::desc("Emit assembly"), cl::cat(AburiCategory));
static cl::opt<bool> EmitLLVM("emit-llvm", cl::desc("Emit LLVM IR"), cl::cat(AburiCategory));
static cl::opt<bool> EmitDebugInfo("g", cl::desc("Emit debug information"), cl::cat(AburiCategory));
static cl::opt<bool> AstMemoryReport("ast-memory-report",
    cl::desc("Print AST memory usage report after parsing"),
    cl::init(false), cl::cat(AburiCategory));
static cl::opt<std::string> OptLevel("O", cl::desc("Optimization level"), cl::Prefix, cl::init("0"), cl::cat(AburiCategory));
static cl::opt<bool> Verbose("v", cl::desc("Verbose output"), cl::cat(AburiCategory));
static cl::list<std::string> IncludePaths("I", cl::desc("Add include search path"), cl::ZeroOrMore,
    cl::value_desc("dir"), cl::Prefix, cl::cat(AburiCategory));
static cl::list<std::string> SystemIncludePaths("isystem",
    cl::desc("Add system include search path"), cl::ZeroOrMore,
    cl::value_desc("dir"), cl::Prefix, cl::cat(AburiCategory));
static cl::list<std::string> QuoteIncludePaths("iquote",
    cl::desc("Add quote-only include search path"), cl::ZeroOrMore,
    cl::value_desc("dir"), cl::Prefix, cl::cat(AburiCategory));
static cl::opt<std::string> TargetTriple("target", cl::desc("Target triple"),
    cl::value_desc("triple"), cl::init(""), cl::cat(AburiCategory));
static cl::opt<std::string> StdOption("std", cl::desc("Language standard (e.g. c89, gnu89, c99, c11, gnu11)"),
    cl::value_desc("standard"), cl::init(""), cl::cat(AburiCategory));
static cl::opt<std::string> StdLibOption("stdlib",
    cl::desc("C++ standard library family (auto|libc++|libstdc++)"),
    cl::value_desc("library"), cl::init("auto"), cl::cat(AburiCategory));
static cl::opt<std::string> LanguageOption("x",
    cl::desc("Treat input files as having this language (c|c++)"),
    cl::value_desc("language"), cl::init(""), cl::cat(AburiCategory));
static cl::opt<bool> FPermissive("fpermissive", cl::desc("Enable permissive mode (implicit function declarations, etc.)"),
    cl::init(false), cl::cat(AburiCategory));
static cl::opt<bool> FExceptions("fexceptions",
    cl::desc("Enable support for exception handling"),
    cl::init(false), cl::cat(AburiCategory));
static cl::opt<bool> FNoExceptions("fno-exceptions",
    cl::desc("Disable support for exception handling"),
    cl::init(false), cl::cat(AburiCategory));
static cl::opt<bool> FBlocks("fblocks",
    cl::desc("Enable Darwin Blocks language support on supported targets"),
    cl::init(false), cl::cat(AburiCategory));
static cl::opt<bool> FNoBlocks("fno-blocks",
    cl::desc("Disable Darwin Blocks language support"),
    cl::init(false), cl::cat(AburiCategory));
static cl::opt<bool> DisableSourcePassthrough("no-source-passthrough",
    cl::desc("Disable system compiler passthrough for non-C source kinds"),
    cl::init(false), cl::cat(AburiCategory));
static cl::opt<std::string> DriverPersonaOption("driver-persona",
    cl::desc("Driver persona for build-system compatibility (native|clang)"),
    cl::value_desc("native|clang"), cl::init(""), cl::cat(AburiCategory));
static cl::opt<std::string> DriverMode("driver-mode",
    cl::desc("Driver mode: strict (default) or compat"),
    cl::value_desc("strict|compat"), cl::init("strict"), cl::cat(AburiCategory));
static cl::opt<std::string> FCxxAbi("fc++-abi",
    cl::desc("C++ ABI to use (itanium|microsoft)"),
    cl::value_desc("abi"), cl::init(""), cl::cat(AburiCategory));
static cl::opt<bool> MMsBitfields("mms-bitfields",
    cl::desc("Use Microsoft-compatible bitfield layout"),
    cl::init(false), cl::cat(AburiCategory));
static cl::opt<bool> MNoMsBitfields("mno-ms-bitfields",
    cl::desc("Disable Microsoft-compatible bitfield layout"),
    cl::init(false), cl::cat(AburiCategory));
static cl::opt<std::string> FAbiVersion("fabi-version",
    cl::desc("Set the C++ ABI compatibility version"),
    cl::value_desc("version"), cl::init(""), cl::cat(AburiCategory));
static cl::opt<std::string> FExceptionRuntime("fexception-runtime",
    cl::desc("Exception runtime profile (llvm|gcc|custom)"),
    cl::value_desc("runtime"), cl::init(""), cl::cat(AburiCategory));

struct CmdMacroOp {
    bool is_define;
    std::string name;
    std::string value;
};

struct MacroParseResult {
    std::vector<CmdMacroOp> ops;
    std::vector<std::string> args;
    std::vector<std::string> linker_flags; // -l, -L flags to forward to linker
    bool ignore_unknown_options = false;
    bool compat_mode = false;
};

struct DriverAbiParseResult {
    DriverAbiOptions options;
    std::optional<std::string> error;
};

enum class DriverPersona {
    Native,
    ClangCompat
};

enum class EarlyDriverQuery {
    None,
    Version,
    VerboseVersion,
    DumpMachine,
    DumpVersion
};

struct DriverPersonaParseResult {
    DriverPersona persona = DriverPersona::Native;
    std::optional<std::string> error;
};

static DriverPersona driver_persona_from_invocation_name(std::string_view argv0);

static constexpr const char* kAburiDisplayVersion = "0.1.0-dev";
static constexpr const char* kAburiNumericVersion = "0.1.0";

static bool starts_with(const std::string& value, const std::string& prefix) {
    return value.rfind(prefix, 0) == 0;
}

static std::optional<std::string> normalize_debug_option_for_driver(const std::string& arg) {
    if (arg == "-g") {
        return arg;
    }
    if (arg == "-g0") {
        return std::string();
    }
    if (arg == "-g1" || arg == "-g2" || arg == "-g3" ||
        starts_with(arg, "-ggdb") ||
        starts_with(arg, "-gdwarf") ||
        starts_with(arg, "-gline-tables-only") ||
        starts_with(arg, "-gsplit-dwarf") ||
        starts_with(arg, "-gmodules") ||
        starts_with(arg, "-gfull") ||
        starts_with(arg, "-gcolumn-info") ||
        starts_with(arg, "-gpubnames")) {
        return std::string("-g");
    }
    return std::nullopt;
}

static bool is_ignored_driver_arg(std::string_view arg) {
    return arg.empty();
}

static std::optional<bool> parse_exceptions_toggle_from_argv(int argc, char** argv) {
    std::optional<bool> enabled;
    for (int i = 1; i < argc; ++i) {
        const std::string arg = argv[i];
        if (is_ignored_driver_arg(arg)) continue;
        if (arg == "-fexceptions" || arg == "--fexceptions") {
            enabled = true;
            continue;
        }
        if (arg == "-fno-exceptions" || arg == "--fno-exceptions") {
            enabled = false;
            continue;
        }
    }
    return enabled;
}

static std::optional<bool> parse_blocks_toggle_from_argv(int argc, char** argv) {
    std::optional<bool> enabled;
    for (int i = 1; i < argc; ++i) {
        const std::string arg = argv[i];
        if (is_ignored_driver_arg(arg)) continue;
        if (arg == "-fblocks" || arg == "--fblocks") {
            enabled = true;
            continue;
        }
        if (arg == "-fno-blocks" || arg == "--fno-blocks") {
            enabled = false;
            continue;
        }
    }
    return enabled;
}

static DriverAbiParseResult parse_driver_abi_options_from_argv(int argc, char** argv) {
    DriverAbiParseResult result;
    for (int i = 1; i < argc; ++i) {
        const std::string arg = argv[i];
        if (is_ignored_driver_arg(arg)) continue;

        if (arg == "-mms-bitfields") {
            result.options.bitfield_abi = BitfieldABI::MSVC;
            continue;
        }
        if (arg == "-mno-ms-bitfields") {
            result.options.bitfield_abi = BitfieldABI::ITANIUM;
            continue;
        }

        std::optional<std::string> cxx_abi_raw;
        if (starts_with(arg, "-fc++-abi=")) {
            cxx_abi_raw = arg.substr(std::string("-fc++-abi=").size());
        } else if (starts_with(arg, "--fc++-abi=")) {
            cxx_abi_raw = arg.substr(std::string("--fc++-abi=").size());
        } else if (arg == "-fc++-abi") {
            if (i + 1 >= argc) {
                result.error = "missing argument to '-fc++-abi'";
                return result;
            }
            cxx_abi_raw = std::string(argv[++i]);
        } else if (arg == "--fc++-abi") {
            if (i + 1 >= argc) {
                result.error = "missing argument to '--fc++-abi'";
                return result;
            }
            cxx_abi_raw = std::string(argv[++i]);
        }
        if (cxx_abi_raw.has_value()) {
            auto parsed = parse_cxx_abi_kind(*cxx_abi_raw);
            if (!parsed.has_value()) {
                result.error = "invalid value for '-fc++-abi': '" + *cxx_abi_raw +
                               "' (expected: itanium|microsoft)";
                return result;
            }
            result.options.cxx_abi = *parsed;
            if (*parsed == CxxAbiKind::Microsoft) {
                result.error = "'-fc++-abi=microsoft' is not implemented yet";
                return result;
            }
            continue;
        }

        std::optional<std::string> abi_version_raw;
        if (starts_with(arg, "-fabi-version=")) {
            abi_version_raw = arg.substr(std::string("-fabi-version=").size());
        } else if (starts_with(arg, "--fabi-version=")) {
            abi_version_raw = arg.substr(std::string("--fabi-version=").size());
        } else if (arg == "-fabi-version") {
            if (i + 1 >= argc) {
                result.error = "missing argument to '-fabi-version'";
                return result;
            }
            abi_version_raw = std::string(argv[++i]);
        } else if (arg == "--fabi-version") {
            if (i + 1 >= argc) {
                result.error = "missing argument to '--fabi-version'";
                return result;
            }
            abi_version_raw = std::string(argv[++i]);
        }
        if (abi_version_raw.has_value()) {
            auto parsed = parse_non_negative_int(*abi_version_raw);
            if (!parsed.has_value()) {
                result.error = "invalid value for '-fabi-version': '" + *abi_version_raw + "'";
                return result;
            }
            if (*parsed != 0) {
                result.error = "'-fabi-version' values other than 0 are not implemented yet";
                return result;
            }
            result.options.cxx_abi_version = *parsed;
            continue;
        }

        std::optional<std::string> eh_runtime_raw;
        if (starts_with(arg, "-fexception-runtime=")) {
            eh_runtime_raw = arg.substr(std::string("-fexception-runtime=").size());
        } else if (starts_with(arg, "--fexception-runtime=")) {
            eh_runtime_raw = arg.substr(std::string("--fexception-runtime=").size());
        } else if (arg == "-fexception-runtime") {
            if (i + 1 >= argc) {
                result.error = "missing argument to '-fexception-runtime'";
                return result;
            }
            eh_runtime_raw = std::string(argv[++i]);
        } else if (arg == "--fexception-runtime") {
            if (i + 1 >= argc) {
                result.error = "missing argument to '--fexception-runtime'";
                return result;
            }
            eh_runtime_raw = std::string(argv[++i]);
        }
        if (eh_runtime_raw.has_value()) {
            auto parsed = parse_eh_runtime_kind(*eh_runtime_raw);
            if (!parsed.has_value()) {
                result.error = "invalid value for '-fexception-runtime': '" + *eh_runtime_raw +
                               "' (expected: llvm|gcc|custom)";
                return result;
            }
            result.options.eh_runtime = *parsed;
            continue;
        }
    }
    return result;
}

static bool compat_mode_requested_from_argv(int argc, char** argv) {
    bool compat_from_persona = false;
    if (argc > 0 && argv[0]) {
        compat_from_persona = driver_persona_from_invocation_name(argv[0]) == DriverPersona::ClangCompat;
    }
    std::optional<bool> explicit_driver_mode;
    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (is_ignored_driver_arg(arg)) continue;
        if (arg == "--driver-mode" && i + 1 < argc) {
            explicit_driver_mode = (std::string(argv[i + 1]) == "compat");
            ++i;
            continue;
        }
        if (starts_with(arg, "--driver-mode=")) {
            explicit_driver_mode =
                (arg.substr(std::string("--driver-mode=").size()) == "compat");
            continue;
        }
        if (arg == "--driver-persona" && i + 1 < argc) {
            compat_from_persona = (std::string(argv[i + 1]) == "clang" ||
                                   std::string(argv[i + 1]) == "clang-compat");
            ++i;
            continue;
        }
        if (starts_with(arg, "--driver-persona=")) {
            auto value = arg.substr(std::string("--driver-persona=").size());
            compat_from_persona = (value == "clang" || value == "clang-compat");
        }
    }
    if (explicit_driver_mode.has_value()) {
        return *explicit_driver_mode;
    }
    return compat_from_persona;
}

static bool explicit_compat_mode_requested_from_argv(int argc, char** argv) {
    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (is_ignored_driver_arg(arg)) continue;
        if (arg == "--driver-mode" && i + 1 < argc) {
            return std::string(argv[i + 1]) == "compat";
        }
        if (starts_with(arg, "--driver-mode=")) {
            return arg.substr(std::string("--driver-mode=").size()) == "compat";
        }
    }
    return false;
}

static std::string to_lower_ascii(std::string value) {
    std::transform(value.begin(), value.end(), value.begin(),
        [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
    return value;
}

static std::string input_extension(const std::filesystem::path& input_path) {
    return to_lower_ascii(input_path.extension().string());
}

static std::optional<DriverPersona> parse_driver_persona_value(std::string_view value) {
    if (value == "native" || value == "aburi") {
        return DriverPersona::Native;
    }
    if (value == "clang" || value == "clang-compat") {
        return DriverPersona::ClangCompat;
    }
    return std::nullopt;
}

static DriverPersona driver_persona_from_invocation_name(std::string_view argv0) {
    std::filesystem::path invocation_path(argv0);
    std::string basename = to_lower_ascii(invocation_path.filename().string());
    if (basename == "aburi-clang" || basename == "clang" || basename == "clang++") {
        return DriverPersona::ClangCompat;
    }
    return DriverPersona::Native;
}

static DriverPersonaParseResult parse_driver_persona_from_argv(int argc, char** argv) {
    DriverPersonaParseResult result;
    if (argc > 0 && argv[0]) {
        result.persona = driver_persona_from_invocation_name(argv[0]);
    }
    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (is_ignored_driver_arg(arg)) continue;
        std::optional<std::string> persona_raw;
        if (arg == "--driver-persona") {
            if (i + 1 >= argc) {
                result.error = "missing argument to '--driver-persona'";
                return result;
            }
            persona_raw = std::string(argv[++i]);
        } else if (starts_with(arg, "--driver-persona=")) {
            persona_raw = arg.substr(std::string("--driver-persona=").size());
        }
        if (!persona_raw.has_value()) {
            continue;
        }
        auto parsed = parse_driver_persona_value(*persona_raw);
        if (!parsed.has_value()) {
            result.error = "invalid value for '--driver-persona': '" + *persona_raw +
                           "' (expected: native|clang)";
            return result;
        }
        result.persona = *parsed;
    }
    return result;
}

static std::optional<std::string> parse_target_triple_from_argv(int argc, char** argv) {
    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (is_ignored_driver_arg(arg)) continue;
        if (arg == "-target" || arg == "--target") {
            if (i + 1 < argc) {
                return std::string(argv[++i]);
            }
            return std::nullopt;
        }
        if (starts_with(arg, "-target=")) {
            return arg.substr(std::string("-target=").size());
        }
        if (starts_with(arg, "--target=")) {
            return arg.substr(std::string("--target=").size());
        }
    }
    return std::nullopt;
}

static EarlyDriverQuery detect_early_driver_query(int argc, char** argv) {
    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (is_ignored_driver_arg(arg)) continue;
        if (arg == "--version") {
            return EarlyDriverQuery::Version;
        }
        if (arg == "-dumpmachine") {
            return EarlyDriverQuery::DumpMachine;
        }
        if (arg == "-dumpversion") {
            return EarlyDriverQuery::DumpVersion;
        }
    }

    bool saw_v = false;
    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (is_ignored_driver_arg(arg)) continue;
        if (arg == "-v") {
            saw_v = true;
            continue;
        }
        if (arg == "--ignore-unknown-options") {
            continue;
        }
        if (arg == "-fblocks" || arg == "--fblocks" ||
            arg == "-fno-blocks" || arg == "--fno-blocks") {
            continue;
        }
        if (arg == "--driver-persona" || arg == "--driver-mode" ||
            arg == "--target" || arg == "-target") {
            if (i + 1 < argc) {
                ++i;
            }
            continue;
        }
        if (starts_with(arg, "--driver-persona=") ||
            starts_with(arg, "--driver-mode=") ||
            starts_with(arg, "--target=") ||
            starts_with(arg, "-target=")) {
            continue;
        }
        return EarlyDriverQuery::None;
    }
    return saw_v ? EarlyDriverQuery::VerboseVersion : EarlyDriverQuery::None;
}

static std::string resolve_installed_dir(const char* argv0) {
    if (argv0 == nullptr || *argv0 == '\0') {
        return ".";
    }
    std::error_code ec;
    auto absolute_path = std::filesystem::absolute(std::filesystem::path(argv0), ec);
    if (ec) {
        absolute_path = std::filesystem::path(argv0);
    }
    auto resolved = std::filesystem::weakly_canonical(absolute_path, ec);
    auto final_path = ec ? absolute_path : resolved;
    auto parent = final_path.parent_path();
    if (parent.empty()) {
        return ".";
    }
    return parent.string();
}

static void print_driver_banner(std::ostream& os,
                                DriverPersona persona,
                                const std::string& target_triple,
                                const std::string& installed_dir) {
    if (persona == DriverPersona::ClangCompat) {
        os << "clang version " << LLVM_VERSION_STRING
           << " (Aburiscript " << kAburiDisplayVersion << ")\n";
        os << "Target: " << target_triple << "\n";
        os << "Thread model: posix\n";
        os << "InstalledDir: " << installed_dir << "\n";
        return;
    }

    os << "Aburiscript version " << kAburiDisplayVersion << "\n";
    os << "LLVM backend version " << LLVM_VERSION_STRING << "\n";
    os << "Target: " << target_triple << "\n";
    os << "InstalledDir: " << installed_dir << "\n";
}

static int handle_early_driver_query(EarlyDriverQuery query,
                                     DriverPersona persona,
                                     const std::string& target_triple,
                                     const char* argv0) {
    switch (query) {
        case EarlyDriverQuery::Version:
        case EarlyDriverQuery::VerboseVersion:
            print_driver_banner(std::cout, persona, target_triple, resolve_installed_dir(argv0));
            return 0;
        case EarlyDriverQuery::DumpMachine:
            std::cout << target_triple << "\n";
            return 0;
        case EarlyDriverQuery::DumpVersion:
            if (persona == DriverPersona::ClangCompat) {
                std::cout << LLVM_VERSION_STRING << "\n";
            } else {
                std::cout << kAburiNumericVersion << "\n";
            }
            return 0;
        case EarlyDriverQuery::None:
            break;
    }
    return -1;
}

static bool is_linker_input_extension(const std::string& ext) {
    return ext == ".o" || ext == ".a" || ext == ".so" ||
           ext == ".dylib" || ext == ".tbd" || ext == ".lo";
}

static bool is_passthrough_source_extension(const std::string& ext) {
    return ext == ".s" || ext == ".asm" || ext == ".m" ||
           ext == ".mm" || ext == ".cu";
}
static bool is_cpp_source_extension(const std::string& ext) {
    return ext == ".cc" || ext == ".cpp" || ext == ".cxx" ||
           ext == ".c++" || ext == ".cp";
}
static bool is_linker_flag(const std::string& arg) {
    if (arg.rfind("-l", 0) == 0 || arg.rfind("-L", 0) == 0 ||
        arg.rfind("-Wl,", 0) == 0 || arg == "-shared" ||
        arg == "-pie" || arg == "-no-pie" || arg == "-nostdlib" ||
        arg == "-nodefaultlibs" || arg == "-nostartfiles" ||
        arg == "-rdynamic" || arg == "-s" || arg == "-static-libgcc" ||
        arg == "-flat_namespace" || arg == "-two_levelnamespaces" ||
        arg == "-dynamic" || arg == "-dylib" || arg == "-dynamiclib" ||
        arg == "-bundle" ||
        arg == "-r" || arg == "-undefined" || arg == "-dead_strip" ||
        arg == "-no_deduplicate" || arg == "-export_dynamic") {
        return true;
    }
    return false;
}

static bool is_linker_flag_with_value(const std::string& arg) {
    return arg == "-framework" || arg == "-rpath" || arg == "-soname" ||
           arg == "-Map" || arg == "-install_name" ||
           arg == "-compatibility_version" || arg == "-current_version" ||
           arg == "-bundle_loader" ||
           arg == "-exported_symbols_list" ||
           arg == "-undefined" || arg == "-Xlinker";
}

static bool is_dual_use_flag(const std::string& arg) {
    return arg == "-pthread" || starts_with(arg, "-fopenmp") ||
           starts_with(arg, "-fuse-ld=") || starts_with(arg, "-stdlib=") ||
           starts_with(arg, "--sysroot=");
}

static bool is_dual_use_flag_with_value(const std::string& arg) {
    return arg == "-arch" || arg == "-isysroot" || arg == "--sysroot";
}

static bool is_compat_compile_flag(const std::string& arg) {
    if (arg == "-fpermissive" || arg == "-fno-permissive") {
        return false;
    }
    if (arg == "-pipe" || arg == "-M" || arg == "-MM" || arg == "-MD" || arg == "-MMD" || arg == "-MP" || arg == "-MG") {
        return true;
    }
    return starts_with(arg, "-W") || starts_with(arg, "-f") || starts_with(arg, "-m");
}

static bool is_compat_compile_flag_with_value(const std::string& arg) {
    return arg == "-isystem" || arg == "-iquote" || arg == "-idirafter" ||
           arg == "-include" || arg == "-imacros" ||
           arg == "-Xpreprocessor" || arg == "-Xassembler" ||
           arg == "-MF" || arg == "-MT" || arg == "-MQ" ||
           arg == "-march" || arg == "-mcpu" || arg == "-mtune" ||
           arg == "-mabi" || arg == "-mfpu" || arg == "-mfloat-abi" ||
           arg == "--param" || arg == "-param" || arg == "-Xclang";
}

static bool is_passthrough_driver_only_option(const std::string& arg) {
    return arg == "--ignore-unknown-options" || arg == "-c" || arg == "-S" || arg == "-E" ||
           arg == "--emit-llvm" || arg == "-emit-llvm" ||
           arg == "-x" ||
           arg == "--driver-persona" || starts_with(arg, "--driver-persona=") ||
           arg == "--driver-mode" || starts_with(arg, "--driver-mode=") ||
           arg == "-fc++-abi" || starts_with(arg, "-fc++-abi=") ||
           arg == "--fc++-abi" || starts_with(arg, "--fc++-abi=") ||
           arg == "-fabi-version" || starts_with(arg, "-fabi-version=") ||
           arg == "--fabi-version" || starts_with(arg, "--fabi-version=") ||
           arg == "-fexception-runtime" || starts_with(arg, "-fexception-runtime=") ||
           arg == "--fexception-runtime" || starts_with(arg, "--fexception-runtime=") ||
           arg == "-mms-bitfields" || arg == "-mno-ms-bitfields" ||
           arg == "-v" || arg == "--no-source-passthrough" ||
           arg == "-no-source-passthrough";
}

static bool passthrough_option_takes_value(const std::string& arg) {
    return arg == "-I" || arg == "-D" || arg == "-U" || arg == "-F" ||
           arg == "-framework" ||
           arg == "-isystem" || arg == "-isysroot" || arg == "-iquote" ||
           arg == "-idirafter" || arg == "-include" || arg == "-imacros" ||
           arg == "-target" || arg == "--target" || arg == "-arch" ||
           arg == "-x" || arg == "-Xpreprocessor" || arg == "-Xassembler" ||
           arg == "-MF" || arg == "-MT" || arg == "-MQ" || arg == "-std" ||
           arg == "-mabi" || arg == "-march" || arg == "-mcpu" ||
           arg == "-mtune" || arg == "-mfpu" || arg == "-mfloat-abi" ||
           arg == "-fc++-abi" || arg == "-fabi-version" ||
           arg == "-fexception-runtime" || arg == "--fexception-runtime" ||
           arg == "--param" || arg == "-param";
}

static bool is_darwin_unsupported_linker_passthrough(const std::string& arg) {
#ifdef __APPLE__
    auto starts_with_flag = [](const std::string& s, const std::string& prefix) {
        return s.rfind(prefix, 0) == 0;
    };
    if (starts_with_flag(arg, "-Wl,")) {
        std::string payload = arg.substr(4);
        if (payload == "--as-needed" || payload == "-z" ||
            starts_with_flag(payload, "-z,") ||
            starts_with_flag(payload, "-rpath-link")) {
            return true;
        }
    }
    if (arg == "--as-needed" || arg == "-z" || starts_with_flag(arg, "-rpath-link")) {
        return true;
    }
#endif
    return false;
}

static std::vector<std::string> collect_passthrough_compile_flags(int argc, char** argv, bool compat_mode,
                                                                  const TargetFeatureGate& feature_gate) {
    std::vector<std::string> result;
    result.reserve(static_cast<size_t>(argc));

    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (is_ignored_driver_arg(arg)) continue;

        if (arg[0] != '-') {
            continue;
        }

        if (is_passthrough_driver_only_option(arg)) {
            if ((arg == "--driver-persona" || arg == "--driver-mode" ||
                 arg == "-fc++-abi" || arg == "--fc++-abi" ||
                 arg == "-fabi-version" || arg == "--fabi-version" ||
                 arg == "-fexception-runtime" || arg == "--fexception-runtime" ||
                 arg == "-x") &&
                i + 1 < argc) {
                ++i;
            }
            continue;
        }

        if (arg == "-o") {
            if (i + 1 < argc) ++i;
            continue;
        }

        if (compat_mode) {
            bool consume_next_arg = false;
            std::optional<std::string_view> next_arg;
            if (i + 1 < argc) {
                next_arg = argv[i + 1];
            }
            if (feature_gate.should_strip_compat_flag(arg, next_arg, consume_next_arg)) {
                if (consume_next_arg && i + 1 < argc) {
                    ++i;
                }
                continue;
            }
        }

        if (is_linker_flag_with_value(arg)) {
            if (i + 1 < argc) ++i;
            continue;
        }
        if (is_linker_flag(arg)) {
            continue;
        }

        if (passthrough_option_takes_value(arg)) {
            result.push_back(arg);
            if (i + 1 < argc) result.push_back(argv[++i]);
            continue;
        }

        result.push_back(arg);
    }

    return result;
}

static bool try_add_include_path(const std::filesystem::path& path,
    std::vector<std::string>& paths,
    std::unordered_set<std::string>& seen) {
    if (path.empty()) {
        return false;
    }
    std::error_code ec;
    if (!std::filesystem::exists(path, ec)) {
        return false;
    }
    auto norm = std::filesystem::weakly_canonical(path, ec);
    std::string norm_str = ec ? path.lexically_normal().string() : norm.string();
    if (!seen.insert(norm_str).second) {
        return false;
    }
    paths.push_back(norm_str);
    return true;
}

static void add_sdk_include_from_root(const std::filesystem::path& sdk_root,
    std::vector<std::string>& paths,
    std::unordered_set<std::string>& seen) {
    auto add_subframework_roots = [&](const std::filesystem::path& frameworks_root) {
        std::error_code ec;
        if (!std::filesystem::exists(frameworks_root, ec) ||
            !std::filesystem::is_directory(frameworks_root, ec)) {
            return;
        }
        for (const auto& entry : std::filesystem::directory_iterator(frameworks_root, ec)) {
            if (ec) break;
            if (!entry.is_directory(ec)) continue;
            auto framework_path = entry.path();
            if (framework_path.extension() != ".framework") continue;
            (void)try_add_include_path(framework_path / "Frameworks", paths, seen);
        }
    };

    if (sdk_root.empty()) {
        return;
    }
    std::filesystem::path include_path = sdk_root / "usr" / "include";
    (void)try_add_include_path(include_path, paths, seen);
    // Apple SDK framework-style headers (e.g. <CoreFoundation/CoreFoundation.h>)
    // are resolved from framework roots rather than usr/include.
    std::filesystem::path frameworks_root = sdk_root / "System" / "Library" / "Frameworks";
    std::filesystem::path private_frameworks_root = sdk_root / "System" / "Library" / "PrivateFrameworks";
    (void)try_add_include_path(frameworks_root, paths, seen);
    (void)try_add_include_path(private_frameworks_root, paths, seen);
    add_subframework_roots(frameworks_root);
    add_subframework_roots(private_frameworks_root);
}

static void add_sdk_from_dir(const std::filesystem::path& sdk_dir,
    std::vector<std::string>& paths,
    std::unordered_set<std::string>& seen) {
    std::error_code ec;
    if (!std::filesystem::exists(sdk_dir, ec) || !std::filesystem::is_directory(sdk_dir, ec)) {
        return;
    }
    std::filesystem::path default_sdk = sdk_dir / "MacOSX.sdk";
    if (std::filesystem::exists(default_sdk, ec)) {
        add_sdk_include_from_root(default_sdk, paths, seen);
        return;
    }
    std::vector<std::filesystem::path> candidates;
    for (const auto& entry : std::filesystem::directory_iterator(sdk_dir, ec)) {
        if (ec) break;
        if (!entry.is_directory(ec)) continue;
        auto p = entry.path();
        auto name = p.filename().string();
        if (name.rfind("MacOSX", 0) == 0 && p.extension() == ".sdk") {
            candidates.push_back(p);
        }
    }
    if (candidates.empty()) {
        return;
    }
    std::sort(candidates.begin(), candidates.end());
    add_sdk_include_from_root(candidates.back(), paths, seen);
}

static void discover_clang_resource_includes(std::vector<std::string>& paths,
    std::unordered_set<std::string>& seen) {
    // Clang resource headers (stdatomic.h, etc.) live in the Clang resource dir.
    // Search common locations for the newest version.
    const std::filesystem::path bases[] = {
        "/Library/Developer/CommandLineTools/usr/lib/clang",
        "/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/lib/clang",
    };
    for (const auto& base : bases) {
        std::error_code ec;
        if (!std::filesystem::exists(base, ec) || !std::filesystem::is_directory(base, ec)) continue;
        std::vector<std::filesystem::path> versions;
        for (const auto& entry : std::filesystem::directory_iterator(base, ec)) {
            if (ec) break;
            if (!entry.is_directory(ec)) continue;
            auto inc = entry.path() / "include";
            if (std::filesystem::exists(inc, ec)) {
                versions.push_back(inc);
            }
        }
        if (!versions.empty()) {
            std::sort(versions.begin(), versions.end());
            try_add_include_path(versions.back(), paths, seen);
            return;
        }
    }
}

static void discover_aburi_builtin_includes(const char* argv0,
                                           std::vector<std::string>& paths,
                                           std::unordered_set<std::string>& seen) {
    std::filesystem::path installed_dir(resolve_installed_dir(argv0));
    const std::filesystem::path candidates[] = {
        installed_dir / "builtin_headers",
        installed_dir.parent_path() / "builtin_headers",
    };
    for (const auto& candidate : candidates) {
        std::error_code ec;
        if (!std::filesystem::exists(candidate, ec) ||
            !std::filesystem::is_directory(candidate, ec)) {
            continue;
        }
        try_add_include_path(candidate, paths, seen);
        return;
    }
}

static std::vector<std::string> discover_driver_macos_sdk_include_paths(const char* argv0) {
    std::vector<std::string> paths;
    std::unordered_set<std::string> seen;

    discover_aburi_builtin_includes(argv0, paths, seen);

    if (const char* sdkroot = std::getenv("SDKROOT")) {
        add_sdk_include_from_root(std::filesystem::path(sdkroot), paths, seen);
    }

    add_sdk_from_dir("/Library/Developer/CommandLineTools/SDKs", paths, seen);
    add_sdk_from_dir("/Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs",
        paths, seen);

    // Add Clang resource headers (stdatomic.h, stdarg.h, etc.)
    discover_clang_resource_includes(paths, seen);

    return paths;
}

static MacroParseResult collect_macro_ops_and_strip_args(int argc, char** argv, bool compat_mode) {
    MacroParseResult result;
    result.compat_mode = compat_mode;
    if (compat_mode) {
        result.ignore_unknown_options = true;
    }
    result.args.reserve(static_cast<size_t>(argc));
    if (argc > 0) {
        result.args.emplace_back(argv[0]);
    }
    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (is_ignored_driver_arg(arg)) continue;
        if (arg == "-") {
            result.args.push_back("/dev/stdin");
            continue;
        }
        if (arg == "-D" || arg == "-U") {
            if (i + 1 >= argc) {
                continue;
            }
            std::string spec = argv[i + 1];
            if (!spec.empty() && spec[0] == '-') {
                continue;
            }
            ++i;
            if (arg == "-D") {
                auto eq = spec.find('=');
                if (eq == std::string::npos) {
                    result.ops.push_back({true, spec, "1"});
                } else {
                    result.ops.push_back({true, spec.substr(0, eq), spec.substr(eq + 1)});
                }
            } else {
                result.ops.push_back({false, spec, ""});
            }
            continue;
        }
        if (arg.rfind("-D", 0) == 0 && arg.size() > 2) {
            std::string spec = arg.substr(2);
            auto eq = spec.find('=');
            if (eq == std::string::npos) {
                result.ops.push_back({true, spec, "1"});
            } else {
                result.ops.push_back({true, spec.substr(0, eq), spec.substr(eq + 1)});
            }
            continue;
        }
        if (arg.rfind("-U", 0) == 0 && arg.size() > 2) {
            std::string spec = arg.substr(2);
            result.ops.push_back({false, spec, ""});
            continue;
        }
        if (arg == "--ignore-unknown-options") {
            result.ignore_unknown_options = true;
            continue;
        }
        if (result.compat_mode) {
            if (is_linker_flag_with_value(arg)) {
                result.linker_flags.push_back(arg);
                if (i + 1 < argc) {
                    result.linker_flags.push_back(argv[++i]);
                }
                continue;
            }
            if (is_linker_flag(arg)) {
                result.linker_flags.push_back(arg);
                continue;
            }
            if (is_dual_use_flag_with_value(arg)) {
                result.linker_flags.push_back(arg);
                if (i + 1 < argc) {
                    result.linker_flags.push_back(argv[++i]);
                }
                continue;
            }
            if (is_dual_use_flag(arg)) {
                result.linker_flags.push_back(arg);
                continue;
            }
        }
        // Bare -O (no level) means -O1
        if (arg == "-O") {
            result.args.push_back("-O1");
            continue;
        }
        // Collect linker flags to forward to the linker
        if (arg.rfind("-l", 0) == 0 || arg.rfind("-L", 0) == 0) {
            result.linker_flags.push_back(arg);
            continue;
        }
        // -Wl,... is an explicit linker pass-through
        if (arg.rfind("-Wl,", 0) == 0) {
            result.linker_flags.push_back(arg);
            continue;
        }
        // macOS/ld64 linker flags
        if (arg == "-flat_namespace" || arg == "-two_levelnamespaces" ||
            arg == "-dynamic" || arg == "-dylib" || arg == "-dynamiclib" ||
            arg == "-bundle" || arg == "-r" ||
            arg == "-undefined" || arg == "-dead_strip" ||
            arg == "-no_deduplicate" || arg == "-export_dynamic") {
            result.linker_flags.push_back(arg);
            // Some of these take a following argument
            if ((arg == "-undefined") && i + 1 < argc) {
                result.linker_flags.push_back(argv[++i]);
            }
            continue;
        }
        // -framework Name (macOS)
        if (arg == "-framework" && i + 1 < argc) {
            result.linker_flags.push_back(arg);
            result.linker_flags.push_back(argv[++i]);
            continue;
        }
        // -rpath, -soname, -Map (linker flags with a following argument)
        if ((arg == "-rpath" || arg == "-soname" || arg == "-Map" ||
             arg == "-install_name" || arg == "-compatibility_version" ||
             arg == "-bundle_loader" || arg == "-exported_symbols_list" ||
             arg == "-current_version") && i + 1 < argc) {
            result.linker_flags.push_back(arg);
            result.linker_flags.push_back(argv[++i]);
            continue;
        }
        // -shared (create shared library)
        if (arg == "-shared" || arg == "-pie" || arg == "-no-pie" ||
            arg == "-nostdlib" || arg == "-nodefaultlibs" || arg == "-nostartfiles" ||
            arg == "-rdynamic" || arg == "-s" || arg == "-static-libgcc") {
            result.linker_flags.push_back(arg);
            continue;
        }
        result.args.push_back(std::move(arg));
    }
#ifdef __APPLE__
    if (!result.compat_mode) {
        std::vector<std::string> filtered_linker_flags;
        filtered_linker_flags.reserve(result.linker_flags.size());
        for (auto& flag : result.linker_flags) {
            if (is_darwin_unsupported_linker_passthrough(flag)) {
                continue;
            }
            filtered_linker_flags.push_back(std::move(flag));
        }
        result.linker_flags = std::move(filtered_linker_flags);
    }
#endif
    return result;
}

static std::vector<std::string> filter_unknown_options(const std::vector<std::string>& args) {
    auto registered = cl::getRegisteredOptions();
    std::vector<std::string> filtered;
    bool past_double_dash = false;

    for (size_t i = 0; i < args.size(); ++i) {
        const auto& arg = args[i];

        if (i == 0 || past_double_dash) {
            if (i == 0 || !arg.empty()) {
                filtered.push_back(arg);
            }
            continue;
        }

        if (arg == "--") {
            past_double_dash = true;
            filtered.push_back(arg);
            continue;
        }

        if (arg.empty()) {
            continue;
        }
        if (arg[0] != '-') {
            filtered.push_back(arg);
            continue;
        }
        if (auto normalized_debug = normalize_debug_option_for_driver(arg)) {
            if (!normalized_debug->empty()) {
                filtered.push_back(*normalized_debug);
            }
            continue;
        }

        std::string opt_name;
        bool is_long = (arg.size() > 1 && arg[1] == '-');
        if (is_long) {
            auto eq = arg.find('=', 2);
            opt_name = arg.substr(2, eq == std::string::npos ? std::string::npos : eq - 2);
        } else {
            // Try full option name first (e.g. -std=gnu89 -> "std")
            auto eq = arg.find('=', 1);
            opt_name = arg.substr(1, eq == std::string::npos ? std::string::npos : eq - 1);
        }

        auto it = registered.find(opt_name);
        // For short options, fall back to single-char prefix (e.g. -I/path -> "I")
        if (it == registered.end() && !is_long && opt_name.size() > 1) {
            auto short_it = registered.find(arg.substr(1, 1));
            if (short_it != registered.end()) {
                auto* short_opt = short_it->second;
                if (short_opt &&
                    short_opt->getFormattingFlag() == cl::Prefix) {
                    it = short_it;
                }
            }
        }
        if (it == registered.end() && !is_long) {
            const std::string body = arg.substr(1);
            size_t best_match_len = 0;
            for (const auto& entry : registered) {
                llvm::StringRef candidate_name = entry.getKey();
                auto* candidate_opt = entry.getValue();
                if (!candidate_opt ||
                    candidate_opt->getFormattingFlag() != cl::Prefix) {
                    continue;
                }
                if (candidate_name.empty() || body.rfind(candidate_name.str(), 0) != 0) {
                    continue;
                }
                if (candidate_name.size() > best_match_len) {
                    best_match_len = candidate_name.size();
                    it = registered.find(candidate_name.str());
                }
            }
        }
        if (it != registered.end()) {
            filtered.push_back(arg);
            auto* opt = it->second;
            bool value_in_next_arg = false;
            if (opt->getValueExpectedFlag() == cl::ValueRequired) {
                bool has_eq = (arg.find('=') != std::string::npos);
                bool is_prefix = (opt->getFormattingFlag() == cl::Prefix);
                bool short_with_extra = (!is_long && arg.size() > 2);
                if (!has_eq && !is_prefix && !short_with_extra) {
                    value_in_next_arg = true;
                }
            }
            if (value_in_next_arg && i + 1 < args.size()) {
                filtered.push_back(args[++i]);
            }
        } else {
            // Unknown compatibility options that consume a separate argument need
            // to skip that value too, so it is not mistaken as an input file.
            bool has_inline_value = (arg.find('=') != std::string::npos);
            if (!has_inline_value &&
                (is_linker_flag_with_value(arg) ||
                 is_dual_use_flag_with_value(arg) ||
                 is_compat_compile_flag_with_value(arg) ||
                 passthrough_option_takes_value(arg))) {
                if (i + 1 < args.size()) ++i;
            }
        }
        // else: unknown option, silently skip
    }

    return filtered;
}

static std::optional<std::string> detect_incompatible_target_feature_flag(
    int argc,
    char** argv,
    const TargetFeatureGate& feature_gate,
    std::string_view target_triple) {
    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (arg.empty() || arg[0] != '-') {
            continue;
        }

        bool consume_next_arg = false;
        std::optional<std::string_view> next_arg;
        if (i + 1 < argc) {
            next_arg = argv[i + 1];
        }

        if (!feature_gate.should_strip_compat_flag(arg, next_arg, consume_next_arg)) {
            continue;
        }

        std::string message =
            "unsupported target feature option '" + arg +
            "' for target '" + std::string(target_triple) + "'";
        if (consume_next_arg && next_arg.has_value()) {
            message += " (value '" + std::string(*next_arg) + "')";
        }
        return message;
    }
    return std::nullopt;
}

void run_command(const std::string& cmd, const std::vector<std::string>& args) {
    if (Verbose) {
        std::cout << cmd;
        for (const auto& arg : args) std::cout << " " << arg;
        std::cout << std::endl;
    }
    
    std::vector<llvm::StringRef> argRefs;
    argRefs.push_back(cmd);
    for (const auto& arg : args) argRefs.push_back(arg);

    std::string errMsg;
    int result = llvm::sys::ExecuteAndWait(cmd, llvm::ArrayRef<llvm::StringRef>(argRefs), std::nullopt, {}, 0, 0, &errMsg);
    if (result != 0) {
        if (!errMsg.empty()) std::cerr << "Error: " << errMsg << std::endl;
        exit(result);
    }
}

static std::optional<std::string> resolve_program_candidate(
    const std::vector<std::string>& candidates) {
    for (const auto& candidate : candidates) {
        if (candidate.empty()) {
            continue;
        }
        std::filesystem::path path_candidate(candidate);
        if (path_candidate.is_absolute()) {
            if (std::filesystem::exists(path_candidate)) {
                return path_candidate.string();
            }
            continue;
        }
        auto found = llvm::sys::findProgramByName(candidate);
        if (found) {
            return *found;
        }
    }
    return std::nullopt;
}

static bool linker_disables_default_runtime(const std::vector<std::string>& linker_flags) {
    for (const auto& flag : linker_flags) {
        if (flag == "-nostdlib" || flag == "-nodefaultlibs" || flag == "-nostartfiles") {
            return true;
        }
    }
    return false;
}

int main(int argc, char** argv) {
    try {
        auto persona_parse = parse_driver_persona_from_argv(argc, argv);
        if (persona_parse.error.has_value()) {
            std::cerr << "Error: " << *persona_parse.error << std::endl;
            return 1;
        }
        DriverPersona driver_persona = persona_parse.persona;
        std::string early_target_triple =
            parse_target_triple_from_argv(argc, argv).value_or(default_target_triple());
        auto early_query = detect_early_driver_query(argc, argv);
        if (early_query != EarlyDriverQuery::None) {
            return handle_early_driver_query(early_query, driver_persona,
                                             early_target_triple,
                                             argc > 0 ? argv[0] : nullptr);
        }
        bool compat_mode_requested = compat_mode_requested_from_argv(argc, argv);
        bool explicit_compat_mode_requested = explicit_compat_mode_requested_from_argv(argc, argv);
        auto driver_exceptions_enabled = parse_exceptions_toggle_from_argv(argc, argv);
        auto driver_blocks_enabled = parse_blocks_toggle_from_argv(argc, argv);
        auto abi_parse = parse_driver_abi_options_from_argv(argc, argv);
        if (abi_parse.error.has_value()) {
            std::cerr << "Error: " << *abi_parse.error << std::endl;
            return 1;
        }
        DriverAbiOptions driver_abi_options = abi_parse.options;
        auto feature_gate = TargetFeatureGate::from_driver_args(argc, argv, default_target_triple());
        if (!explicit_compat_mode_requested) {
            if (auto incompatible_target_flag = detect_incompatible_target_feature_flag(
                    argc,
                    argv,
                    feature_gate,
                    early_target_triple)) {
                std::cerr << "Error: " << *incompatible_target_flag << std::endl;
                return 1;
            }
        }
        auto passthrough_compile_flags = collect_passthrough_compile_flags(argc, argv, compat_mode_requested, feature_gate);
        auto macro_parse = collect_macro_ops_and_strip_args(argc, argv, compat_mode_requested);
        auto macro_ops = std::move(macro_parse.ops);
        auto linker_flags = std::move(macro_parse.linker_flags);
        std::vector<const char*> arg_ptrs;
        arg_ptrs.reserve(macro_parse.args.size());
        for (const auto& arg : macro_parse.args) {
            if (arg.empty()) continue;
            arg_ptrs.push_back(arg.c_str());
        }
        if (macro_parse.ignore_unknown_options) {
            macro_parse.args = filter_unknown_options(macro_parse.args);
            arg_ptrs.clear();
            for (const auto& arg : macro_parse.args) {
                if (arg.empty()) continue;
                arg_ptrs.push_back(arg.c_str());
            }
        }
        int parsed_argc = static_cast<int>(arg_ptrs.size());
        cl::HideUnrelatedOptions(AburiCategory);
        cl::ParseCommandLineOptions(parsed_argc, arg_ptrs.data(), "Aburiscript compiler\n");
        if (DriverMode != "strict" && DriverMode != "compat") {
            std::cerr << "Error: --driver-mode must be 'strict' or 'compat'" << std::endl;
            return 1;
        }
        if (!FCxxAbi.empty()) {
            auto parsed = parse_cxx_abi_kind(FCxxAbi);
            if (!parsed.has_value()) {
                std::cerr << "Error: invalid value for '-fc++-abi': '" << FCxxAbi
                          << "' (expected: itanium|microsoft)" << std::endl;
                return 1;
            }
            driver_abi_options.cxx_abi = *parsed;
            if (*parsed == CxxAbiKind::Microsoft) {
                std::cerr << "Error: '-fc++-abi=microsoft' is not implemented yet" << std::endl;
                return 1;
            }
        }
        if (!FAbiVersion.empty()) {
            auto parsed = parse_non_negative_int(FAbiVersion);
            if (!parsed.has_value()) {
                std::cerr << "Error: invalid value for '-fabi-version': '" << FAbiVersion << "'" << std::endl;
                return 1;
            }
            if (*parsed != 0) {
                std::cerr << "Error: '-fabi-version' values other than 0 are not implemented yet" << std::endl;
                return 1;
            }
            driver_abi_options.cxx_abi_version = *parsed;
        }
        if (!FExceptionRuntime.empty()) {
            auto parsed = parse_eh_runtime_kind(FExceptionRuntime);
            if (!parsed.has_value()) {
                std::cerr << "Error: invalid value for '-fexception-runtime': '"
                          << FExceptionRuntime
                          << "' (expected: llvm|gcc|custom)" << std::endl;
                return 1;
            }
            driver_abi_options.eh_runtime = *parsed;
        }
        if (MMsBitfields) {
            driver_abi_options.bitfield_abi = BitfieldABI::MSVC;
        }
        if (MNoMsBitfields) {
            driver_abi_options.bitfield_abi = BitfieldABI::ITANIUM;
        }
        auto parsed_stdlib = parse_stdlib_kind(StdLibOption);
        if (!parsed_stdlib.has_value()) {
            std::cerr << "Error: invalid value for '-stdlib': '" << StdLibOption
                      << "' (expected: auto|libc++|libstdc++)" << std::endl;
            return 1;
        }
        StdLibKind requested_stdlib = *parsed_stdlib;
        std::optional<LanguageMode> forced_language_mode;
        if (!LanguageOption.empty()) {
            LangOptions probe;
            if (!probe.set_language_from_x(LanguageOption)) {
                std::cerr << "Error: invalid value for '-x': '" << LanguageOption
                          << "' (expected: c|c++)" << std::endl;
                return 1;
            }
            forced_language_mode = probe.language_mode;
        }
        std::string target_triple =
            parse_target_triple_from_argv(argc, argv).value_or(default_target_triple());
        auto target_info = TargetInfo::create_host();
        target_info->triple = target_triple;
        if (FBlocks && FNoBlocks) {
            std::cerr << "Error: cannot combine '-fblocks' with '-fno-blocks'" << std::endl;
            return 1;
        }
        if (FBlocks && !darwin_blocks::target_supports_darwin_blocks(*target_info)) {
            std::cerr << "Error: '-fblocks' is only supported on Darwin targets" << std::endl;
            return 1;
        }
        if (InputFilenames.empty()) {
            std::vector<std::string> probe_args = passthrough_compile_flags;
            probe_args.insert(probe_args.end(), linker_flags.begin(), linker_flags.end());
            if (!probe_args.empty()) {
                std::string probe_driver =
                    (forced_language_mode.has_value() &&
                     *forced_language_mode == LanguageMode::CXX)
                    ? "/usr/bin/c++"
                    : "/usr/bin/cc";
                run_command(probe_driver, probe_args);
                return 0;
            }
            std::cerr << "Error: no input files" << std::endl;
            return 1;
        }
        if (FSyntaxOnly && (PreprocessOnly || EmitAssembly || EmitLLVM)) {
            std::cerr << "Error: cannot combine '-fsyntax-only' with '-E', '-S', or '--emit-llvm'" << std::endl;
            return 1;
        }
        if (PreprocessOnly && !OutputFilename.empty() && InputFilenames.size() != 1) {
            std::cerr << "Error: cannot use -o with -E when compiling multiple input files" << std::endl;
            return 1;
        }
        if (DumpMacroDefinitions && !PreprocessOnly) {
            std::cerr << "Error: -dM requires -E" << std::endl;
            return 1;
        }
        if (GenerateDependenciesM || GenerateDependenciesMM) {
            std::string dep_driver =
                (forced_language_mode.has_value() &&
                 *forced_language_mode == LanguageMode::CXX)
                ? "/usr/bin/c++"
                : "/usr/bin/cc";
            std::vector<std::string> dep_args = passthrough_compile_flags;
            dep_args.insert(dep_args.end(), InputFilenames.begin(), InputFilenames.end());
            run_command(dep_driver, dep_args);
            return 0;
        }
        std::vector<std::string> objectFiles;
        std::vector<std::string> tempFiles;
        bool link_as_cxx = false;
        std::optional<std::filesystem::path> temp_object_dir;
        size_t temp_object_counter = 0;

        // Separate source files from object/library files that should be
        // passed directly to the linker (e.g. .o, .a, .so, .dylib).
        std::vector<std::string> linkerInputFiles;

        for (const auto& inputFilename : InputFilenames) {
            std::filesystem::path inputPath(inputFilename);
            if (!std::filesystem::exists(inputPath)) {
                std::cerr << "Error: file not found: " << inputFilename << std::endl;
                return 1;
            }

            auto ext = input_extension(inputPath);
            if (is_linker_input_extension(ext)) {
                // Not a source file — forward to linker
                linkerInputFiles.push_back(inputFilename);
                continue;
            }

            bool has_forced_language =
                forced_language_mode.has_value() &&
                *forced_language_mode != LanguageMode::Auto;
            bool frontend_source =
                has_forced_language || ext == ".c" || is_cpp_source_extension(ext);

            if (!frontend_source) {
                if (!is_passthrough_source_extension(ext)) {
                    std::cerr << "Error: unsupported source file kind for " << inputFilename
                              << " (extension '" << ext << "')" << std::endl;
                    return 1;
                }
                if (ext == ".mm") {
                    link_as_cxx = true;
                }
                if (DisableSourcePassthrough) {
                    std::cerr << "Error: source passthrough is disabled, cannot compile "
                              << inputFilename << " (extension '" << ext << "')" << std::endl;
                    return 1;
                }
                if (PreprocessOnly) {
                    std::vector<std::string> ccArgs = passthrough_compile_flags;
                    ccArgs.push_back("-E");
                    ccArgs.push_back(inputFilename);
                    if (!OutputFilename.empty() && InputFilenames.size() == 1) {
                        ccArgs.push_back("-o");
                        ccArgs.push_back(OutputFilename);
                    }
                    run_command("/usr/bin/cc", ccArgs);
                    continue;
                }
                if (FSyntaxOnly) {
                    std::vector<std::string> ccArgs = passthrough_compile_flags;
                    ccArgs.push_back("-fsyntax-only");
                    ccArgs.push_back(inputFilename);
                    run_command("/usr/bin/cc", ccArgs);
                    continue;
                }
                if (EmitLLVM) {
                    std::cerr << "Error: --emit-llvm is not supported for passthrough source kind '"
                              << ext << "' in " << inputFilename << std::endl;
                    return 1;
                }

                std::vector<std::string> ccArgs = passthrough_compile_flags;

                if (EmitAssembly) {
                    std::string asmOut;
                    if (!OutputFilename.empty() && InputFilenames.size() == 1) {
                        asmOut = OutputFilename;
                    } else {
                        asmOut = inputPath.stem().string() + ".s";
                    }
                    ccArgs.push_back("-S");
                    ccArgs.push_back(inputFilename);
                    ccArgs.push_back("-o");
                    ccArgs.push_back(asmOut);
                    run_command("/usr/bin/cc", ccArgs);
                    continue;
                }

                std::string objOut;
                if (CompileOnly && !OutputFilename.empty() && InputFilenames.size() == 1) {
                    objOut = OutputFilename;
                } else {
                    objOut = inputPath.stem().string() + ".o";
                }
                ccArgs.push_back("-c");
                ccArgs.push_back(inputFilename);
                ccArgs.push_back("-o");
                ccArgs.push_back(objOut);
                run_command("/usr/bin/cc", ccArgs);
                objectFiles.push_back(objOut);
                if (!CompileOnly) {
                    tempFiles.push_back(objOut);
                }
                continue;
            }

            LangOptions lang_opts;
            if (!StdOption.empty()) {
                lang_opts.set_standard(StdOption);
            }
            if (has_forced_language) {
                lang_opts.language_mode = *forced_language_mode;
            } else if (is_cpp_source_extension(ext)) {
                lang_opts.language_mode = LanguageMode::CXX;
            } else if (ext == ".c") {
                lang_opts.language_mode = LanguageMode::C;
            }
            if (lang_opts.is_cxx_mode()) {
                link_as_cxx = true;
            }
            if (FPermissive) {
                lang_opts.implicit_function_declarations = true;
                lang_opts.implicit_int = true;
            }
            if (driver_exceptions_enabled.has_value()) {
                lang_opts.exceptions_enabled = *driver_exceptions_enabled;
            }
            if (driver_blocks_enabled.has_value()) {
                lang_opts.blocks_mode = *driver_blocks_enabled
                    ? BlocksMode::Enabled
                    : BlocksMode::Disabled;
            }

            // 1. Preprocess
            std::ifstream t(inputFilename);
            std::string content((std::istreambuf_iterator<char>(t)), std::istreambuf_iterator<char>());
            PreProcess pp(inputFilename, content, target_info, lang_opts);
            auto main_file = pp.sm->getFileWithId(pp.current_file_id);
            if (main_file) {
                main_file->directory = inputPath.parent_path().string();
            }
            auto cxx_stdlib_paths = discover_cxx_stdlib_include_paths(
                argc > 0 ? argv[0] : nullptr,
                target_triple,
                lang_opts.is_cxx_mode(),
                requested_stdlib);
            pp.sm->cxx_stdlib_lookup_active = lang_opts.is_cxx_mode();
            pp.sm->requested_cxx_stdlib = stdlib_kind_name(requested_stdlib);
            pp.sm->resolved_cxx_stdlib = stdlib_kind_name(cxx_stdlib_paths.resolved);
            pp.sm->attempted_cxx_stdlib_paths = cxx_stdlib_paths.attempted_paths;
            std::vector<std::string> include_paths;
            std::unordered_set<std::string> seen_paths;
            for (const auto& path : IncludePaths) {
                try_add_include_path(path, include_paths, seen_paths);
            }
            for (const auto& path : SystemIncludePaths) {
                try_add_include_path(path, include_paths, seen_paths);
            }
            for (const auto& path : cxx_stdlib_paths.include_paths) {
                try_add_include_path(path, include_paths, seen_paths);
            }
            std::vector<std::string> quote_include_paths;
            std::unordered_set<std::string> seen_quote_paths;
            for (const auto& path : QuoteIncludePaths) {
                try_add_include_path(path, quote_include_paths, seen_quote_paths);
            }
            if (target_info->os == TargetOS::MACOS) {
                auto sdk_paths =
                    discover_driver_macos_sdk_include_paths(argc > 0 ? argv[0] : nullptr);
                for (const auto& path : sdk_paths) {
                    try_add_include_path(path, include_paths, seen_paths);
                }
            }
            for (const auto& path : quote_include_paths) {
                pp.sm->quote_look_paths.push_back(path);
            }
            for (const auto& path : include_paths) {
                pp.sm->source_look_paths.push_back(path);
            }
            for (const auto& op : macro_ops) {
                if (op.is_define) {
                    pp.define_object_macro(op.name, op.value);
                } else {
                    pp.undef_macro(op.name);
                }
            }
            if (PreprocessOnly) {
                if (!OutputFilename.empty() && InputFilenames.size() == 1) {
                    std::ofstream out(OutputFilename);
                    if (!out.is_open()) {
                        std::cerr << "Error: unable to open output file: " << OutputFilename << std::endl;
                        return 1;
                    }
                    if (DumpMacroDefinitions) {
                        pp.emit_macro_definitions(out);
                    } else {
                        pp.emit_preprocessed_text(out);
                    }
                } else {
                    if (DumpMacroDefinitions) {
                        pp.emit_macro_definitions(std::cout);
                    } else {
                        pp.emit_preprocessed_text(std::cout);
                    }
                }
                continue;
            }
            auto tokens = pp.tokenize();

            // 2. Parse
            Parser parser(tokens, pp.sm, target_info);
            parser.lang_opts = lang_opts;
            if (parser.ast_ctx && parser.ast_ctx->abi_policy) {
                DriverAbiOptions effective_abi_options = driver_abi_options;
                if (lang_opts.is_cxx_mode() &&
                    !effective_abi_options.cxx_abi.has_value() &&
                    parser.ast_ctx->abi_policy->cxx_abi == CxxAbiKind::Itanium) {
                    effective_abi_options.cxx_abi = CxxAbiKind::Itanium;
                }
                apply_driver_abi_overrides(*parser.ast_ctx->abi_policy, effective_abi_options);
            }
            auto ast = parser.parse();
            if (!ast) {
                std::cerr << "Error: parsing failed for " << inputFilename << std::endl;
                return 1;
            }
            if (AstMemoryReport) {
                print_ast_memory_report(std::cout, ast.get(), *parser.ast_ctx);
            }
            if (FSyntaxOnly) {
                continue;
            }

            // 3. CodeGen (Parser::parse() already performs semantic analysis)
            ASTToLLVM codegen;
            codegen.optimization_level = OptLevel;
            codegen.emit_debug_info = EmitDebugInfo;
            codegen.sm = pp.sm;
            codegen.ast_ctx = parser.ast_ctx;
            codegen.lang_opts = lang_opts;
            codegen.convert_translation_unit(ast.get());
            codegen.optimize();

            bool producedOutput = false;

            if (EmitLLVM) {
                std::string out;
                // Avoid collision if both EmitLLVM and EmitAssembly are used and -o is set
                // Prioritize -o for Assembly if both are present (arbitrary choice, but distinct)
                // Or prioritize -o for LLVM if only LLVM is present.
                if (EmitAssembly && !OutputFilename.empty()) {
                    out = inputPath.stem().string() + ".ll";
                } else {
                    out = OutputFilename.empty() ? inputPath.stem().string() + ".ll" : OutputFilename;
                }

                std::error_code ec;
                llvm::raw_fd_ostream dest(out, ec, llvm::sys::fs::OF_None);
                codegen.module->print(dest, nullptr);
                producedOutput = true;
            }

            if (EmitAssembly) {
                std::string out = OutputFilename.empty() ? inputPath.stem().string() + ".s" : OutputFilename;
                codegen.emit(out, llvm::CodeGenFileType::AssemblyFile);
                producedOutput = true;
            }
            // If we generated LLVM IR or Assembly, we stop here for this file.
            // This prevents -c from forcing object code generation that might overwrite the previous output
            // if -o was used, and generally treats -emit-llvm/-S as terminal stages.
            if (producedOutput) continue;

            // Default to object file if we need to link or if -c is specified
            std::string objOut;
            if (CompileOnly && !OutputFilename.empty() && InputFilenames.size() == 1) {
                objOut = OutputFilename;
            } else if (!CompileOnly) {
                if (!temp_object_dir.has_value()) {
                    llvm::SmallString<256> temp_dir_storage;
                    std::error_code temp_dir_ec =
                        llvm::sys::fs::createUniqueDirectory(
                            "aburi-link-%%%%%%",
                            temp_dir_storage);
                    if (temp_dir_ec) {
                        std::cerr << "Error: unable to create temporary link object directory: "
                                  << temp_dir_ec.message() << std::endl;
                        return 1;
                    }
                    temp_object_dir =
                        std::filesystem::path(std::string(temp_dir_storage.str()));
                }
                std::string stem = inputPath.stem().string();
                if (stem.empty()) {
                    stem = "input";
                }
                std::filesystem::path temp_obj_path =
                    *temp_object_dir /
                    (stem + "." + std::to_string(temp_object_counter++) + ".o");
                objOut = temp_obj_path.string();
            } else {
                objOut = inputPath.stem().string() + ".o";
            }

            codegen.emit(objOut, llvm::CodeGenFileType::ObjectFile);
            objectFiles.push_back(objOut);
            if (!CompileOnly) {
                tempFiles.push_back(objOut);
            }
        }

        if (!CompileOnly && !EmitAssembly && !EmitLLVM && !PreprocessOnly && !FSyntaxOnly) {
            // Linking stage
            std::string exeOut = OutputFilename.empty() ? "a.out" : std::string(OutputFilename);
            std::vector<std::string> linkerArgs;
            for (const auto& obj : objectFiles) linkerArgs.push_back(obj);
            for (const auto& obj : linkerInputFiles) linkerArgs.push_back(obj);

            std::string linker_driver = "/usr/bin/cc";
            if (link_as_cxx) {
                linker_driver = "/usr/bin/c++";
            }

            EhRuntimeKind eh_runtime =
                driver_abi_options.eh_runtime.value_or(EhRuntimeKind::LLVM);
            if (link_as_cxx) {
                EhRuntimeLinkProfile runtime_link_profile =
                    eh_runtime_link_profile_for_kind(eh_runtime, target_info->os);
                auto resolved_driver =
                    resolve_program_candidate(runtime_link_profile.cxx_linker_candidates);
                if (resolved_driver.has_value()) {
                    linker_driver = *resolved_driver;
                } else if (runtime_link_profile.require_runtime_specific_driver) {
                    std::cerr << "Error: exception runtime profile requested a runtime-specific C++ linker driver, "
                              << "but none of the configured candidates are available:";
                    for (const auto& candidate : runtime_link_profile.cxx_linker_candidates) {
                        std::cerr << " " << candidate;
                    }
                    std::cerr << std::endl;
                    return 1;
                }

                if (!linker_disables_default_runtime(linker_flags)) {
                    for (const auto& runtime_arg : runtime_link_profile.runtime_link_args) {
                        linkerArgs.push_back(runtime_arg);
                    }
                }
            }

            for (const auto& flag : linker_flags) linkerArgs.push_back(flag);
            linkerArgs.push_back("-o");
            linkerArgs.push_back(exeOut);

            run_command(linker_driver, linkerArgs);

            // Clean up temp object files
            for (const auto& temp : tempFiles) {
                std::filesystem::remove(temp);
            }
            if (temp_object_dir.has_value()) {
                std::error_code cleanup_ec;
                std::filesystem::remove_all(*temp_object_dir, cleanup_ec);
            }
        }

        return 0;
    } catch (const std::runtime_error& err) {
        std::string msg = err.what();
        if (!msg.empty()) {
            std::cerr << msg;
            if (msg.back() != '\n') {
                std::cerr << "\n";
            }
        }
        return 1;
    }
}
