#include "options.h"

#include <cstdlib>
#include <filesystem>
#include <iostream>
#include <optional>
#include <string>
#include <string_view>

#include <llvm/Support/CommandLine.h>

namespace aburi::driver {
namespace {

namespace cl = llvm::cl;

cl::OptionCategory AburiCategory("Aburi Options");

cl::list<std::string> InputFilenames(
    cl::Positional,
    cl::desc("<input files>"),
    cl::ZeroOrMore,
    cl::cat(AburiCategory));
cl::opt<std::string> OutputFilename(
    "o",
    cl::desc("Output filename"),
    cl::value_desc("filename"),
    cl::Prefix,
    cl::cat(AburiCategory));
cl::opt<bool> CompileOnly(
    "c",
    cl::desc("Lower CIR to a target object file"),
    cl::cat(AburiCategory));
cl::opt<bool> PreprocessOnly(
    "E",
    cl::desc("Run the preprocessor"),
    cl::cat(AburiCategory));
cl::opt<bool> DumpMacroDefinitions(
    "dM",
    cl::desc("With -E, emit macro definitions instead of preprocessed text"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> PreprocessNoLineMarkers(
    "P",
    cl::desc("With -E, omit line markers from preprocessed output"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> KeepComments(
    "C",
    cl::desc("With -E, keep comments (honored on passthrough paths)"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> KeepCommentsMacro(
    "CC",
    cl::desc("With -E, keep comments including in macros"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> FSyntaxOnly(
    "fsyntax-only",
    cl::desc("Parse and verify without lowering"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> Precompile(
    "precompile",
    cl::desc("Compile a module interface unit to a .abmi artifact"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::list<std::string> ModuleFiles(
    "fmodule-file",
    cl::desc("Use a prebuilt module artifact (NAME=path)"),
    cl::ZeroOrMore,
    cl::value_desc("NAME=path"),
    cl::cat(AburiCategory));
cl::list<std::string> PrebuiltModulePaths(
    "fprebuilt-module-path",
    cl::desc("Directory searched for <module>.abmi artifacts"),
    cl::ZeroOrMore,
    cl::value_desc("dir"),
    cl::cat(AburiCategory));
cl::opt<bool> ModuleOutput(
    "fmodule-output",
    cl::desc("Also write a .abmi artifact when compiling a module interface"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> FBlocks(
    "fblocks",
    cl::desc("Enable the Apple Blocks language extension"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> FNoBlocks(
    "fno-blocks",
    cl::desc("Disable the Apple Blocks language extension"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> FReflection(
    "freflection",
    cl::desc("Enable C++26 reflection (P2996) in pre-C++26 C++ modes"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> FNoReflection(
    "fno-reflection",
    cl::desc("Disable C++26 reflection (P2996)"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> FNoTemplatePatternClone(
    "fno-template-pattern-clone",
    cl::desc("Instantiate templates by token replay instead of pattern-CIR "
             "cloning (differential testing/triage)"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> FCoroPreSplit(
    "fcoro-pre-split",
    cl::desc("Emit coroutine marker CIR before the coroutine-splitting pass; "
             "backends cannot lower unsplit coroutine markers"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> FTemplateFallbackNotes(
    "ftemplate-fallback-notes",
    cl::desc("Emit a note whenever a template instantiation falls back to "
             "token replay"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> DumpSyntax(
    "dump-syntax",
    cl::desc("Dump the arena syntax tree"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> DumpCIR(
    "dump-cir",
    cl::desc("Dump the collected CIR"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<std::string> DumpCIRExample(
    "dump-cir-example",
    cl::desc("Dump a self-contained CIR example"),
    cl::value_desc("name"),
    cl::init(""),
    cl::cat(AburiCategory));
cl::opt<bool> DumpAIR(
    "dump-air",
    cl::desc("Dump the lowered AIR (Aburi IR)"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> VerifyMir(
    "verify-mir",
    cl::desc("Verify machine IR after selection, allocation and frame lowering"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<std::string> Backend(
    "backend",
    cl::desc("Code generation backend (llvm|air)"),
    cl::value_desc("name"),
    cl::init("llvm"),
    cl::cat(AburiCategory));
cl::opt<std::string> AirObject(
    "air-object",
    cl::desc("Object emission for the air backend (as|direct|system-as)"),
    cl::value_desc("mode"),
    cl::init("as"),
    cl::cat(AburiCategory));
cl::opt<bool> IntegratedAs(
    "fintegrated-as",
    cl::desc("Assemble in-process on supported targets"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> NoIntegratedAs(
    "fno-integrated-as",
    cl::desc("Assemble through the external toolchain"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> EmitLLVM(
    "emit-llvm",
    cl::desc("Lower CIR to LLVM IR"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> EmitAssembly(
    "S",
    cl::desc("Lower CIR to target assembly"),
    cl::cat(AburiCategory));
cl::opt<bool> Jit(
    "jit",
    cl::desc("Lower CIR and run main with LLVM ORC JIT"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<std::string> TimeReport(
    "time-report",
    cl::desc("Print a compile-time report to stderr (summary|headers|full)"),
    cl::value_desc("detail"),
    cl::ValueOptional,
    cl::init(""),
    cl::cat(AburiCategory));
cl::opt<std::string> PerfJson(
    "perf-json",
    cl::desc("Write the compile-time report as JSON"),
    cl::value_desc("path"),
    cl::init(""),
    cl::cat(AburiCategory));
cl::opt<bool> IgnoreUnknownOptions(
    "ignore-unknown-options",
    cl::desc("Ignore unsupported driver options"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> DepGenerateAll(
    "M",
    cl::desc("Emit make dependencies (all headers) instead of compiling"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> DepGenerateUser(
    "MM",
    cl::desc("Emit make dependencies (user headers) instead of compiling"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> DepWriteUser(
    "MMD",
    cl::desc("Write a make dependency file listing user headers"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> DepWriteAll(
    "MD",
    cl::desc("Write a make dependency file listing all headers"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> DepPhonyTargets(
    "MP",
    cl::desc("Add a phony target for each dependency"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<std::string> DepOutputFile(
    "MF",
    cl::desc("Dependency file path"),
    cl::value_desc("file"),
    cl::init(""),

    cl::Prefix,
    cl::cat(AburiCategory));
cl::list<std::string> DepTargets(
    "MT",
    cl::desc("Dependency rule target name"),
    cl::ZeroOrMore,
    cl::value_desc("target"),
    cl::Prefix,
    cl::cat(AburiCategory));
cl::list<std::string> DepQuotedTargets(
    "MQ",
    cl::desc("Dependency rule target name (make-escaped)"),
    cl::ZeroOrMore,
    cl::value_desc("target"),
    cl::Prefix,
    cl::cat(AburiCategory));
cl::opt<bool> NoStdInc(
    "nostdinc",
    cl::desc("Do not search standard or builtin include directories"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> NoStdIncXX(
    "nostdinc++",
    cl::desc("Do not search C++ standard library include directories"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> InhibitWarnings(
    "w",
    cl::desc("Suppress all warnings"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::list<std::string> PreIncludeFiles(
    "include",
    cl::desc("Include file before the main source"),
    cl::ZeroOrMore,
    cl::value_desc("file"),
    cl::cat(AburiCategory));
cl::list<std::string> IncludePaths(
    "I",
    cl::desc("Add include search path"),
    cl::ZeroOrMore,
    cl::value_desc("dir"),
    cl::Prefix,
    cl::cat(AburiCategory));
cl::list<std::string> SystemIncludePaths(
    "isystem",
    cl::desc("Add system include search path"),
    cl::ZeroOrMore,
    cl::value_desc("dir"),
    cl::Prefix,
    cl::cat(AburiCategory));
cl::list<std::string> QuoteIncludePaths(
    "iquote",
    cl::desc("Add quote-only include search path"),
    cl::ZeroOrMore,
    cl::value_desc("dir"),
    cl::Prefix,
    cl::cat(AburiCategory));
cl::list<std::string> ISysrootPaths(
    "isysroot",
    cl::desc("Add Darwin SDK/sysroot include root"),
    cl::ZeroOrMore,
    cl::value_desc("dir"),
    cl::Prefix,
    cl::cat(AburiCategory));
cl::list<std::string> SysrootPaths(
    "sysroot",
    cl::desc("Add target sysroot"),
    cl::ZeroOrMore,
    cl::value_desc("dir"),
    cl::cat(AburiCategory));
cl::list<std::string> Defines(
    "D",
    cl::desc("Define a macro"),
    cl::ZeroOrMore,
    cl::value_desc("NAME[=VALUE]"),
    cl::Prefix,
    cl::cat(AburiCategory));
cl::list<std::string> Undefines(
    "U",
    cl::desc("Undefine a macro"),
    cl::ZeroOrMore,
    cl::value_desc("NAME"),
    cl::Prefix,
    cl::cat(AburiCategory));
cl::opt<std::string> StdOption(
    "std",
    cl::desc("Choose a C/C++ standard"),
    cl::value_desc("standard"),
    cl::init(""),
    cl::cat(AburiCategory));
cl::opt<std::string> StdLibOption(
    "stdlib",
    cl::desc("Choose C++ standard library (auto|adinkra|libc++|libstdc++)"),
    cl::value_desc("library"),
    cl::init("auto"),
    cl::cat(AburiCategory));
cl::opt<std::string> AdinkraRuntimeOption(
    "adinkra-runtime",
    cl::desc("Choose the Adinkra runtime form (static|shared)"),
    cl::value_desc("static|shared"),
    cl::init("static"),
    cl::cat(AburiCategory));
cl::opt<std::string> AdinkraRootOption(
    "adinkra-root",
    cl::desc("Directory holding the Adinkra headers and runtime"),
    cl::value_desc("dir"),
    cl::init(""),
    cl::cat(AburiCategory));
cl::opt<std::string> AdinkraLibraryOption(
    "adinkra-lib",
    cl::desc("Path to the Adinkra runtime library to link"),
    cl::value_desc("path"),
    cl::init(""),
    cl::cat(AburiCategory));
cl::opt<std::string> LanguageOption(
    "x",
    cl::desc("Treat input files as this language"),
    cl::value_desc("language"),
    cl::init(""),

    cl::Prefix,
    cl::cat(AburiCategory));
cl::opt<std::string> TargetTriple(
    "target",
    cl::desc("Target triple"),
    cl::value_desc("triple"),
    cl::init(""),
    cl::cat(AburiCategory));
cl::opt<std::string> DriverPersonaOption(
    "driver-persona",
    cl::desc("Driver identity for build-system probes (native|clang|gcc)"),
    cl::value_desc("native|clang|gcc"),
    cl::init(""),
    cl::cat(AburiCategory));
cl::opt<std::string> CrossCc(
    "cross-cc",
    cl::desc("Cross compiler driver used to assemble and link for "
             "non-native targets (default: $ABURI_CROSS_CC, then Homebrew "
             "clang)"),
    cl::value_desc("path"),
    cl::init(""),
    cl::cat(AburiCategory));
cl::list<std::string> LinkLibraries(
    "l",
    cl::desc("Link against library"),
    cl::ZeroOrMore,
    cl::value_desc("library"),
    cl::Prefix,
    cl::cat(AburiCategory));
cl::list<std::string> LibraryPaths(
    "L",
    cl::desc("Add linker library search path"),
    cl::ZeroOrMore,
    cl::value_desc("dir"),
    cl::Prefix,
    cl::cat(AburiCategory));

cl::opt<std::string> LdPathOption(
    "ld-path",
    cl::desc("Path to the linker executable to drive"),
    cl::value_desc("file"),
    cl::init(""),
    cl::cat(AburiCategory));
cl::list<std::string> Frameworks(
    "framework",
    cl::desc("Link against Darwin framework"),
    cl::ZeroOrMore,
    cl::value_desc("name"),
    cl::cat(AburiCategory));
cl::list<std::string> FrameworkSearchPaths(
    "F",
    cl::desc("Add framework header search path"),
    cl::ZeroOrMore,
    cl::value_desc("dir"),
    cl::Prefix,
    cl::cat(AburiCategory));
cl::list<std::string> SystemFrameworkSearchPaths(
    "iframework",
    cl::desc("Add system framework header search path"),
    cl::ZeroOrMore,
    cl::value_desc("dir"),
    cl::cat(AburiCategory));
cl::opt<bool> ObjCPassthrough(
    "fobjc-passthrough",
    cl::desc("Force Objective-C[++] inputs through the system compiler "
             "(default for file-extension language detection)"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> ObjCNative(
    "fobjc-native",
    cl::desc("Compile Objective-C[++] inputs with the aburi frontend"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> ObjCArc(
    "fobjc-arc",
    cl::desc("Compile Objective-C with automatic reference counting"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::opt<bool> NoObjCArc(
    "fno-objc-arc",
    cl::desc("Compile Objective-C with manual retain/release (default)"),
    cl::init(false),
    cl::cat(AburiCategory));
cl::list<std::string> Rpaths(
    "rpath",
    cl::desc("Add runtime library search path"),
    cl::ZeroOrMore,
    cl::value_desc("path"),
    cl::cat(AburiCategory));
cl::list<std::string> XlinkerArgs(
    "Xlinker",
    cl::desc("Pass one argument to the linker"),
    cl::ZeroOrMore,
    cl::value_desc("arg"),
    cl::cat(AburiCategory));
cl::list<std::string> UndefinedPolicies(
    "undefined",
    cl::desc("Darwin undefined-symbol policy"),
    cl::ZeroOrMore,
    cl::value_desc("policy"),
    cl::cat(AburiCategory));
cl::list<std::string> InstallNames(
    "install_name",
    cl::desc("Darwin dynamic-library install name"),
    cl::ZeroOrMore,
    cl::value_desc("name"),
    cl::cat(AburiCategory));
cl::list<std::string> CompatibilityVersions(
    "compatibility_version",
    cl::desc("Darwin dynamic-library compatibility version"),
    cl::ZeroOrMore,
    cl::value_desc("version"),
    cl::cat(AburiCategory));
cl::list<std::string> CurrentVersions(
    "current_version",
    cl::desc("Darwin dynamic-library current version"),
    cl::ZeroOrMore,
    cl::value_desc("version"),
    cl::cat(AburiCategory));
cl::list<std::string> BundleLoaders(
    "bundle_loader",
    cl::desc("Darwin bundle loader"),
    cl::ZeroOrMore,
    cl::value_desc("path"),
    cl::cat(AburiCategory));
cl::list<std::string> ExportedSymbolsLists(
    "exported_symbols_list",
    cl::desc("Darwin exported-symbols list"),
    cl::ZeroOrMore,
    cl::value_desc("path"),
    cl::cat(AburiCategory));
cl::list<std::string> UnknownOptions(
    cl::Sink,
    cl::ZeroOrMore,
    cl::Hidden);

std::pair<std::string, std::string> split_define(std::string value) {
    size_t eq = value.find('=');
    if (eq == std::string::npos) {
        return {std::move(value), "1"};
    }
    std::string name = value.substr(0, eq);
    std::string replacement = value.substr(eq + 1);
    if (replacement.empty()) {
        replacement = "1";
    }
    return {std::move(name), std::move(replacement)};
}

bool starts_with(std::string_view value, std::string_view prefix) {
    return value.size() >= prefix.size() &&
           value.substr(0, prefix.size()) == prefix;
}

std::string strip_optional_equals(std::string value) {
    if (!value.empty() && value.front() == '=') {
        value.erase(value.begin());
    }
    return value;
}

bool should_ignore_unknown(const DriverOptions& opts, std::string_view arg) {
    return opts.ignore_unknown_options ||
           starts_with(arg, "-W") ||
           starts_with(arg, "-f") ||
           starts_with(arg, "-m") ||

           arg == "-pipe" ||

           starts_with(arg, "-g");
}

std::string make_quote_target(std::string_view target) {
    std::string quoted;
    quoted.reserve(target.size());
    for (char c : target) {
        if (c == '$') {
            quoted += "$$";
        } else {
            quoted.push_back(c);
        }
    }
    return quoted;
}

bool apply_preprocessor_args(DriverOptions& opts, std::string_view arg) {
    std::vector<std::string> parts;
    size_t start = std::string_view("-Wp,").size();
    while (start <= arg.size()) {
        size_t comma = arg.find(',', start);
        if (comma == std::string_view::npos) {
            parts.emplace_back(arg.substr(start));
            break;
        }
        parts.emplace_back(arg.substr(start, comma - start));
        start = comma + 1;
    }
    for (size_t i = 0; i < parts.size(); ++i) {
        const std::string& part = parts[i];
        auto take_value = [&]() -> std::optional<std::string> {
            if (i + 1 < parts.size()) {
                return parts[++i];
            }
            return std::nullopt;
        };
        if (part == "-MD" || part == "-MMD") {
            opts.depfile.enabled = true;
            opts.depfile.include_system_headers = (part == "-MD");
            if (i + 1 < parts.size() && !parts[i + 1].empty() &&
                parts[i + 1][0] != '-') {
                opts.depfile.output_path = parts[++i];
            }
            continue;
        }
        if (part == "-MF") {
            if (auto value = take_value()) {
                opts.depfile.output_path = *value;
                continue;
            }
        } else if (part == "-MT") {
            if (auto value = take_value()) {
                opts.depfile.targets.push_back(*value);
                continue;
            }
        } else if (part == "-MQ") {
            if (auto value = take_value()) {
                opts.depfile.targets.push_back(make_quote_target(*value));
                continue;
            }
        } else if (part == "-MP") {
            opts.depfile.phony_targets = true;
            continue;
        } else if (part == "-undef" || part.empty()) {

            continue;
        } else if (part == "-w") {
            opts.inhibit_warnings = true;
            continue;
        }
        std::cerr << "aburi: error: unsupported preprocessor argument '"
                  << part << "' in '" << arg << "'\n";
        return false;
    }
    return true;
}

bool is_linker_flag(std::string_view arg) {
    return starts_with(arg, "-l") ||
           starts_with(arg, "-L") ||
           starts_with(arg, "-Wl,") ||
           arg == "-shared" ||
           arg == "-pie" ||
           arg == "-no-pie" ||
           arg == "-nostdlib" ||
           arg == "-nostdlib++" ||
           arg == "-nodefaultlibs" ||
           arg == "-nostartfiles" ||
           arg == "-rdynamic" ||
           arg == "-s" ||
           arg == "-flat_namespace" ||
           arg == "-two_levelnamespaces" ||
           arg == "-dynamic" ||
           arg == "-dylib" ||
           arg == "-dynamiclib" ||
           arg == "-bundle" ||
           arg == "-r" ||
           arg == "-dead_strip" ||
           arg == "-no_deduplicate" ||
           arg == "-export_dynamic";
}

void append_joined_linker_flags(std::vector<std::string>& flags,
                                const cl::list<std::string>& values,
                                std::string_view prefix) {
    for (const std::string& value : values) {
        std::string normalized = strip_optional_equals(value);
        if (!normalized.empty()) {
            flags.push_back(std::string(prefix) + normalized);
        }
    }
}

void append_paired_linker_flags(std::vector<std::string>& flags,
                                const cl::list<std::string>& values,
                                std::string_view option) {
    for (const std::string& value : values) {
        flags.push_back(std::string(option));
        flags.push_back(strip_optional_equals(value));
    }
}

std::optional<DriverPersona> parse_driver_persona_value(std::string_view value) {
    if (value == "native" || value == "aburi") {
        return DriverPersona::Native;
    }
    if (value == "clang" || value == "clang-compat") {
        return DriverPersona::ClangCompat;
    }
    if (value == "gcc" || value == "gcc-compat") {
        return DriverPersona::GccCompat;
    }
    return std::nullopt;
}

std::string lower_ascii(std::string value) {
    for (char& c : value) {
        if (c >= 'A' && c <= 'Z') {
            c = static_cast<char>(c - 'A' + 'a');
        }
    }
    return value;
}

DriverPersona persona_from_invocation_name(const char* argv0) {
    if (argv0 == nullptr || *argv0 == '\0') {
        return DriverPersona::Native;
    }
    const std::string basename =
        lower_ascii(std::filesystem::path(argv0).filename().string());
    if (basename == "aburi-clang" || basename == "clang" ||
        basename == "clang++") {
        return DriverPersona::ClangCompat;
    }
    if (basename == "aburi-gcc" || basename == "aburi-g++" ||
        basename == "gcc" || basename == "g++") {
        return DriverPersona::GccCompat;
    }
    return DriverPersona::Native;
}

bool scan_persona_and_triple(int argc, char** argv, DriverOptions& opts) {
    opts.persona = persona_from_invocation_name(argc > 0 ? argv[0] : nullptr);
    for (int i = 1; i < argc; ++i) {
        std::string_view arg = argv[i] != nullptr ? argv[i] : "";
        std::optional<std::string_view> persona_value;
        if (arg == "--driver-persona" || arg == "-driver-persona") {
            if (i + 1 >= argc || argv[i + 1] == nullptr) {
                std::cerr << "aburi: error: missing value for '--driver-persona'\n";
                return false;
            }
            persona_value = argv[++i];
        } else if (starts_with(arg, "--driver-persona=")) {
            persona_value = arg.substr(std::string_view("--driver-persona=").size());
        } else if (starts_with(arg, "-driver-persona=")) {
            persona_value = arg.substr(std::string_view("-driver-persona=").size());
        }
        if (persona_value.has_value()) {
            auto parsed = parse_driver_persona_value(*persona_value);
            if (!parsed.has_value()) {
                std::cerr << "aburi: error: invalid value for '--driver-persona': '"
                          << *persona_value << "' (expected: native|clang|gcc)\n";
                return false;
            }
            opts.persona = *parsed;
            continue;
        }
        if ((arg == "--target" || arg == "-target") && i + 1 < argc &&
            argv[i + 1] != nullptr) {
            opts.target_triple = argv[++i];
        } else if (starts_with(arg, "--target=")) {
            opts.target_triple = arg.substr(std::string_view("--target=").size());
        } else if (starts_with(arg, "-target=")) {
            opts.target_triple = arg.substr(std::string_view("-target=").size());
        }
    }
    return true;
}

bool early_query_skippable_arg(std::string_view arg, int& i, int argc, char** argv) {
    if (arg.empty() || arg == "--ignore-unknown-options") {
        return true;
    }
    if (arg == "--driver-persona" || arg == "-driver-persona" ||
        arg == "--target" || arg == "-target") {
        if (i + 1 < argc && argv[i + 1] != nullptr) {
            ++i;
        }
        return true;
    }
    return starts_with(arg, "--driver-persona=") ||
           starts_with(arg, "-driver-persona=") ||
           starts_with(arg, "--target=") ||
           starts_with(arg, "-target=");
}

EarlyDriverQuery detect_early_driver_query(int argc, char** argv,
                                           DriverOptions& opts) {
    for (int i = 1; i < argc; ++i) {
        std::string_view arg = argv[i] != nullptr ? argv[i] : "";
        if (arg == "--version") {
            return EarlyDriverQuery::Version;
        }
        if (arg == "-dumpmachine") {
            return EarlyDriverQuery::DumpMachine;
        }
        if (arg == "-dumpversion") {
            return EarlyDriverQuery::DumpVersion;
        }

        if (arg == "-dumpfullversion" &&
            opts.persona == DriverPersona::GccCompat) {
            return EarlyDriverQuery::DumpFullVersion;
        }
        if (starts_with(arg, "-print-file-name=") ||
            starts_with(arg, "--print-file-name=")) {
            opts.print_file_name = std::string(
                arg.substr(arg.find('=') + 1));
            return EarlyDriverQuery::PrintFileName;
        }
    }

    bool saw_v = false;
    for (int i = 1; i < argc; ++i) {
        std::string_view arg = argv[i] != nullptr ? argv[i] : "";
        if (arg == "-v") {
            saw_v = true;
            continue;
        }
        if (early_query_skippable_arg(arg, i, argc, argv)) {
            continue;
        }
        return EarlyDriverQuery::None;
    }
    return saw_v ? EarlyDriverQuery::VerboseVersion : EarlyDriverQuery::None;
}

bool scan_early_option(int argc, char** argv, DriverOptions& opts) {
    for (int i = 1; i < argc; ++i) {
        std::string_view arg = argv[i] != nullptr ? argv[i] : "";
        if (arg == "--help" || arg == "-h") {
            opts.show_help = true;
            return true;
        }
    }
    opts.early_query = detect_early_driver_query(argc, argv, opts);
    return opts.early_query != EarlyDriverQuery::None;
}

} // namespace

bool parse_driver_options(int argc, char** argv, DriverOptions& opts) {
    if (!scan_persona_and_triple(argc, argv, opts)) {
        return false;
    }
    if (scan_early_option(argc, argv, opts)) {
        return true;
    }

    std::vector<char*> filtered_argv;
    filtered_argv.reserve(static_cast<size_t>(argc));
    for (int i = 0; i < argc; ++i) {
        if (i == 0 || (argv[i] != nullptr && argv[i][0] != '\0')) {
            filtered_argv.push_back(argv[i]);
        }
    }

    cl::HideUnrelatedOptions(AburiCategory);
    if (!cl::ParseCommandLineOptions(static_cast<int>(filtered_argv.size()),
                                     filtered_argv.data(),
                                     "Aburi frontend\n")) {
        return false;
    }

    opts.input_files.assign(InputFilenames.begin(), InputFilenames.end());
    opts.output_path = OutputFilename;
    opts.ld_path = LdPathOption;
    opts.compile_only = CompileOnly;
    opts.preprocess_only = PreprocessOnly;
    opts.dump_macros = DumpMacroDefinitions;
    opts.preprocess_no_linemarkers = PreprocessNoLineMarkers;
    opts.keep_comments = KeepComments || KeepCommentsMacro;
    opts.syntax_only = FSyntaxOnly;
    opts.lang_opts.syntax_only = FSyntaxOnly;
    opts.precompile_only = Precompile;
    for (const std::string& entry : ModuleFiles) {
        size_t equals = entry.find('=');
        if (equals == std::string::npos || equals == 0 ||
            equals + 1 == entry.size()) {
            std::cerr << "aburi: error: -fmodule-file expects NAME=path, got '"
                      << entry << "'\n";
            return false;
        }
        opts.module_files.emplace_back(entry.substr(0, equals),
                                       entry.substr(equals + 1));
    }
    opts.prebuilt_module_paths.assign(PrebuiltModulePaths.begin(),
                                      PrebuiltModulePaths.end());
    opts.module_output = ModuleOutput;
    if (FNoBlocks) {
        opts.lang_opts.blocks_mode = BlocksMode::Disabled;
    } else if (FBlocks) {
        opts.lang_opts.blocks_mode = BlocksMode::Enabled;
    }
    opts.lang_opts.template_pattern_cloning = !FNoTemplatePatternClone;
    opts.lang_opts.template_fallback_notes = FTemplateFallbackNotes;
    opts.dump_syntax = DumpSyntax;
    opts.dump_cir = DumpCIR;
    opts.dump_cir_example = DumpCIRExample;
    opts.dump_air = DumpAIR;
    opts.verify_mir = VerifyMir;
    opts.backend = Backend;
    opts.integrated_as = IntegratedAs && !NoIntegratedAs;
    opts.air_object = AirObject;
    opts.emit_llvm = EmitLLVM;
    opts.emit_assembly = EmitAssembly;
    opts.jit = Jit;
    opts.ignore_unknown_options = IgnoreUnknownOptions;
    opts.target_triple = TargetTriple;
    opts.cross_cc = CrossCc;

    if (target_os_from_triple(opts.target_triple) == TargetOS::NETBSD) {
        opts.pic = false;
    }

    if (TimeReport.getNumOccurrences() > 0) {
        std::string detail = strip_optional_equals(TimeReport);
        if (detail.empty()) {
            opts.perf_detail = PerfDetail::Summary;
        } else {
            auto parsed = parse_perf_detail(detail);
            if (!parsed.has_value()) {
                std::cerr << "aburi: error: invalid value for '--time-report': '"
                          << detail << "' (expected: summary|headers|full)\n";
                return false;
            }
            opts.perf_detail = *parsed;
        }
    }
    opts.perf_json_path = PerfJson;

    if (!opts.perf_json_path.empty() && !opts.perf_detail.has_value()) {
        opts.perf_detail = PerfDetail::Summary;
    }

    for (const std::string& path : IncludePaths) {
        opts.include_paths.push_back(strip_optional_equals(path));
    }
    for (const std::string& path : SystemIncludePaths) {
        opts.system_include_paths.push_back(strip_optional_equals(path));
    }
    for (const std::string& path : QuoteIncludePaths) {
        opts.quote_include_paths.push_back(strip_optional_equals(path));
    }
    opts.nostdinc = NoStdInc;
    opts.nostdincxx = NoStdIncXX;
    opts.inhibit_warnings = opts.inhibit_warnings || InhibitWarnings;
    if (DepWriteUser || DepWriteAll) {
        opts.depfile.enabled = true;
        opts.depfile.include_system_headers = DepWriteAll;
    }

    if (DepGenerateAll || DepGenerateUser) {
        opts.depfile.enabled = true;
        opts.depfile.generate_only = true;
        opts.depfile.include_system_headers = DepGenerateAll;
        opts.preprocess_only = true;
    }
    if (DepPhonyTargets) {
        opts.depfile.phony_targets = true;
    }
    if (!DepOutputFile.empty()) {
        opts.depfile.output_path = strip_optional_equals(DepOutputFile);
    }
    for (const std::string& target : DepTargets) {
        opts.depfile.targets.push_back(target);
    }
    for (const std::string& target : DepQuotedTargets) {
        opts.depfile.targets.push_back(make_quote_target(target));
    }
    for (const std::string& path : PreIncludeFiles) {
        opts.pre_includes.push_back(strip_optional_equals(path));
    }
    for (const std::string& path : ISysrootPaths) {
        opts.sysroots.push_back(strip_optional_equals(path));
    }
    for (const std::string& path : FrameworkSearchPaths) {
        opts.framework_include_paths.push_back(strip_optional_equals(path));
    }
    for (const std::string& path : SystemFrameworkSearchPaths) {
        opts.system_framework_include_paths.push_back(strip_optional_equals(path));
    }
    for (const std::string& path : SysrootPaths) {
        opts.sysroots.push_back(strip_optional_equals(path));
    }
    for (const std::string& define : Defines) {
        opts.defines.push_back(split_define(strip_optional_equals(define)));
    }
    for (const std::string& undefine : Undefines) {
        opts.undefines.push_back(strip_optional_equals(undefine));
    }
    append_joined_linker_flags(opts.linker_flags, LinkLibraries, "-l");
    append_joined_linker_flags(opts.linker_flags, LibraryPaths, "-L");
    append_paired_linker_flags(opts.linker_flags, Frameworks, "-framework");
    append_paired_linker_flags(opts.linker_flags, Rpaths, "-rpath");
    append_paired_linker_flags(opts.linker_flags, XlinkerArgs, "-Xlinker");
    append_paired_linker_flags(opts.linker_flags, UndefinedPolicies, "-undefined");
    append_paired_linker_flags(opts.linker_flags, InstallNames, "-install_name");
    append_paired_linker_flags(opts.linker_flags,
        CompatibilityVersions,
        "-compatibility_version");
    append_paired_linker_flags(opts.linker_flags, CurrentVersions, "-current_version");
    append_paired_linker_flags(opts.linker_flags, BundleLoaders, "-bundle_loader");
    append_paired_linker_flags(opts.linker_flags,
        ExportedSymbolsLists,
        "-exported_symbols_list");

    // ABURI_STDLIB supplies the default for a whole build; an explicit
    // '-stdlib' on the command line always wins. The option's cl::init value
    // makes the occurrence count the only way to tell the two apart.
    std::string stdlib_text = StdLibOption;
    bool stdlib_from_environment = false;
    if (StdLibOption.getNumOccurrences() == 0) {
        if (const char* env = std::getenv("ABURI_STDLIB")) {
            if (*env != '\0') {
                stdlib_text = env;
                stdlib_from_environment = true;
            }
        }
    }
    auto parsed_stdlib = parse_stdlib_kind(stdlib_text);
    if (!parsed_stdlib.has_value()) {
        std::cerr << "aburi: error: invalid value for '"
                  << (stdlib_from_environment ? "ABURI_STDLIB" : "-stdlib")
                  << "': '" << stdlib_text
                  << "' (expected: auto|adinkra|libc++|libstdc++)\n";
        return false;
    }
    opts.requested_stdlib = *parsed_stdlib;

    auto parsed_adinkra_runtime = parse_adinkra_runtime_kind(AdinkraRuntimeOption);
    if (!parsed_adinkra_runtime.has_value()) {
        std::cerr << "aburi: error: invalid value for '-adinkra-runtime': '"
                  << AdinkraRuntimeOption
                  << "' (expected: static|shared)\n";
        return false;
    }
    opts.adinkra_runtime = *parsed_adinkra_runtime;
    opts.adinkra_root = AdinkraRootOption;
    opts.adinkra_library = AdinkraLibraryOption;

    if (!StdOption.empty() && !opts.lang_opts.set_standard(StdOption)) {
        std::cerr << "aburi: error: unsupported standard '" << StdOption << "'\n";
        return false;
    }
    if (LanguageOption == "assembler" ||
        LanguageOption == "assembler-with-cpp") {

        opts.assembler_language = true;
        opts.assembler_with_cpp = LanguageOption == "assembler-with-cpp";
    } else if (!LanguageOption.empty() &&
               !opts.lang_opts.set_language_from_x(LanguageOption)) {
        std::cerr << "aburi: error: unsupported language '" << LanguageOption << "'\n";
        return false;
    }
    const bool explicit_objc_language = opts.lang_opts.is_objc();
    opts.objc_passthrough = ObjCPassthrough ||
                            (!ObjCNative && !explicit_objc_language);
    opts.lang_opts.objc_arc = ObjCArc && !NoObjCArc;

    if (FNoReflection) {
        opts.lang_opts.enable_cpp_reflection = false;
    } else if (FReflection) {
        if (!opts.lang_opts.is_cxx_mode() &&
            opts.lang_opts.language_mode != LanguageMode::Auto) {
            std::cerr << "aburi: error: '-freflection' requires a C++ mode\n";
            return false;
        }
        opts.lang_opts.enable_cpp_reflection = true;
    }
    if (FCoroPreSplit) {
        opts.lang_opts.enable_coroutine_pre_split_cir = true;
    }

    for (const std::string& unknown : UnknownOptions) {

        if (opts.persona == DriverPersona::GccCompat &&
            (unknown == "-cpp" || unknown == "-v")) {
            continue;
        }
        if (is_linker_flag(unknown)) {
            // These stay in linker_flags so the host link driver still sees
            // them; the flags also record that the user is supplying the C++
            // standard library, which suppresses the automatic Adinkra link.
            if (unknown == "-nostdlib++") {
                opts.nostdlibxx = true;
            } else if (unknown == "-nostdlib") {
                opts.nostdlib = true;
            }
            opts.linker_flags.push_back(unknown);
            continue;
        }

        if (starts_with(unknown, "-Wa,")) {
            opts.assembler_flags.push_back(unknown);
            continue;
        }

        if (starts_with(unknown, "-Wp,")) {
            if (!apply_preprocessor_args(opts, unknown)) {
                return false;
            }
            continue;
        }

        if (starts_with(unknown, "-fbackend=")) {
            opts.backend = unknown.substr(std::string_view("-fbackend=").size());
            continue;
        }

        if (unknown == "-O" || unknown == "-O1") {
            opts.opt_level = 1;
            opts.lang_opts.optimization_level = 1;
            opts.lang_opts.optimize_for_size = false;
            continue;
        }
        if (unknown == "-O0") {
            opts.opt_level = 0;
            opts.lang_opts.optimization_level = 0;
            opts.lang_opts.optimize_for_size = false;
            continue;
        }
        if (unknown == "-O2") {
            opts.opt_level = 2;
            opts.lang_opts.optimization_level = 2;
            opts.lang_opts.optimize_for_size = false;
            continue;
        }
        if (unknown == "-O3" || unknown == "-Ofast") {
            opts.opt_level = 3;
            opts.lang_opts.optimization_level = 3;
            opts.lang_opts.optimize_for_size = false;
            continue;
        }
        if (unknown == "-Os" || unknown == "-Oz") {
            opts.opt_level = 2;
            opts.lang_opts.optimization_level = 2;
            opts.lang_opts.optimize_for_size = true;
            continue;
        }

        if (unknown == "-Og") {
            opts.lang_opts.optimization_level = 1;
            opts.lang_opts.optimize_for_size = false;
            opts.opt_level = 1;
            continue;
        }

        if (unknown == "-fno-pie" || unknown == "-fno-PIE" ||
            unknown == "-fno-pic" || unknown == "-fno-PIC" ||
            unknown == "-fno-pic=1" || unknown == "-fno-pic=2") {
            opts.pic = false;
            continue;
        }
        if (unknown == "-fpie" || unknown == "-fPIE" ||
            unknown == "-fpic" || unknown == "-fPIC" ||
            unknown == "-fpie=1" || unknown == "-fpie=2" ||
            unknown == "-fpic=1" || unknown == "-fpic=2") {
            opts.pic = true;
            continue;
        }

        if (unknown == "-static") {
            opts.pic = false;
            opts.linker_flags.push_back("-static");
            continue;
        }

        if (unknown == "-fshort-wchar") {
            opts.short_wchar = true;
            continue;
        }
        if (unknown == "-fno-short-wchar") {
            opts.short_wchar = false;
            continue;
        }

        if (unknown == "-mgeneral-regs-only") {
            opts.general_regs_only = true;
            continue;
        }

        if (starts_with(unknown, "-mcpu=") || starts_with(unknown, "-march=")) {
            if (unknown.find("+crypto") != std::string::npos ||
                unknown.find("+aes") != std::string::npos) {
                opts.aarch64_aes = true;
            }
            if (unknown.find("+crypto") != std::string::npos ||
                unknown.find("+sha2") != std::string::npos) {
                opts.aarch64_sha2 = true;
            }

            if (unknown.find("+nofp") != std::string::npos ||
                unknown.find("+nosimd") != std::string::npos ||
                unknown.find("+noneon") != std::string::npos) {
                opts.general_regs_only = true;
            }
            continue;
        }

        if (starts_with(unknown, "-mbranch-protection=")) {
            std::string spec =
                unknown.substr(std::string_view("-mbranch-protection=").size());
            bool standard = spec == "standard";
            opts.branch_target_enforcement =
                standard || spec.find("bti") != std::string::npos;
            opts.sign_return_address =
                standard || spec.find("pac-ret") != std::string::npos;
            continue;
        }

        if (unknown == "-fno-omit-frame-pointer") {
            opts.keep_frame_pointer = true;
            continue;
        }
        if (unknown == "-fomit-frame-pointer") {
            opts.keep_frame_pointer = false;
            continue;
        }

        if (unknown == "-ftrivial-auto-var-init=zero" ||
            unknown == "-ftrivial-auto-var-init=pattern") {
            opts.lang_opts.trivial_auto_var_init_zero = true;
            continue;
        }
        if (unknown == "-ftrivial-auto-var-init=uninitialized") {
            opts.lang_opts.trivial_auto_var_init_zero = false;
            continue;
        }

        if (starts_with(unknown, "-B") && unknown.size() > 2) {
            opts.linker_flags.push_back(unknown);
            continue;
        }

        if (unknown == "-fcommon") {
            opts.fcommon = true;
            continue;
        }
        if (unknown == "-fno-common") {
            opts.fcommon = false;
            continue;
        }

        if (unknown == "-ffreestanding" || unknown == "-fno-builtin") {
            opts.freestanding = true;
            continue;
        }
        if (unknown == "-fbuiltin" || unknown == "-fhosted") {
            opts.freestanding = false;
            continue;
        }

        if (starts_with(unknown, "-ffixed-x")) {
            std::string_view digits =
                std::string_view(unknown).substr(
                    std::string_view("-ffixed-x").size());
            if (!digits.empty() &&
                digits.find_first_not_of("0123456789") == std::string_view::npos) {
                int reg = std::stoi(std::string(digits));
                if (reg >= 0 && reg <= 30) {
                    opts.reserved_aarch64_gprs.push_back(reg);
                }
            }
            continue;
        }
        if (!should_ignore_unknown(opts, unknown)) {
            std::cerr << "aburi: error: unsupported option '" << unknown << "'\n";
            return false;
        }
    }

    if (opts.backend != "llvm" && opts.backend != "air") {
        std::cerr << "aburi: error: invalid value for '--backend': '"
                  << opts.backend << "' (expected: llvm|air)\n";
        return false;
    }
    if (opts.air_object != "as" && opts.air_object != "direct" &&
        opts.air_object != "system-as") {
        std::cerr << "aburi: error: invalid value for '--air-object': '"
                  << opts.air_object << "' (expected: as|direct|system-as)\n";
        return false;
    }

    return true;
}

void print_driver_help(std::ostream& out) {
    out << "usage: aburi [options] file...\n"
        << "  default            lower supported sources and link an executable\n"
        << "  -E                 run the preprocessor\n"
        << "  -dM                with -E, dump macro definitions\n"
        << "  -P                 with -E, omit line markers\n"
        << "  -fsyntax-only      parse and verify without lowering\n"
        << "  --dump-syntax      dump the arena syntax tree\n"
        << "  --dump-cir         dump the collected CIR\n"
        << "  --dump-cir-example NAME\n"
        << "                     dump a self-contained CIR example\n"
        << "  --dump-air         dump the lowered AIR (Aburi IR)\n"
        << "  --verify-mir       verify machine IR at each air backend stage\n"
        << "  --backend=NAME     choose the code generation backend (llvm|air)\n"
        << "  -O0..-O3, -Os      optimization level (air backend pass pipeline)\n"
        << "  --emit-llvm        lower CIR to LLVM IR\n"
        << "  -S                 lower CIR to target assembly\n"
        << "  -c                 lower CIR to a target object file\n"
        << "  --jit              lower CIR and run main with LLVM ORC JIT\n"
        << "  --time-report[=D]  print a compile-time report (summary|headers|full)\n"
        << "  --perf-json PATH   write the compile-time report as JSON\n"
        << "  -fno-template-pattern-clone\n"
        << "                     instantiate templates by token replay only\n"
        << "  -ftemplate-fallback-notes\n"
        << "                     note each template token-replay fallback\n"
        << "  -include FILE      include FILE before the main source\n"
        << "  -nostdinc          skip standard/builtin include directories\n"
        << "  -nostdinc++        skip C++ standard-library include directories\n"
        << "  -nostdlib++        skip the C++ standard library during linking\n"
        << "  -I DIR             add an include path\n"
        << "  -isystem DIR       add a system include path\n"
        << "  -iquote DIR        add a quote-only include path\n"
        << "  -isysroot DIR      add a Darwin SDK/sysroot include root\n"
        << "  --sysroot DIR      add a target sysroot\n"
        << "  --cross-cc PATH    cross compiler driver for non-native targets\n"
        << "  --driver-persona=P identity for probes (native|clang|gcc);\n"
        << "                     also selected by aburi-clang/aburi-gcc names\n"
        << "  -dumpmachine       print the target triple and exit\n"
        << "  -dumpversion       print the compiler version and exit\n"
        << "  -dumpfullversion   print the full GCC-persona version and exit\n"
        << "  -stdlib=LIB        choose C++ standard library "
           "(auto|adinkra|libc++|libstdc++)\n"
        << "                     the default also comes from $ABURI_STDLIB\n"
        << "  --adinkra-runtime=K link the static or shared Adinkra runtime\n"
        << "                     (static|shared)\n"
        << "  --adinkra-root DIR Adinkra headers and runtime location\n"
        << "                     (also $ABURI_ADINKRA_ROOT)\n"
        << "  --adinkra-lib PATH Adinkra runtime library to link\n"
        << "  -DNAME[=VALUE]     define a macro\n"
        << "  -UNAME             undefine a macro\n"
        << "  -std=STD           choose a C/C++ standard\n";
}

} // namespace aburi::driver
