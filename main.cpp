#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <sstream>
#include <string>
#include <string_view>
#include <vector>

#include <llvm/ADT/SmallString.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/Program.h>

#include "air/passes.h"
#include "air/print.h"
#include "air/verifier.h"
#include "assembler/assembler.h"
#include "backend/backend.h"
#include "cir/examples.h"
#include "cir2air/cir2air.h"
#include "cir2llvm/cir2llvm.h"
#include "driver/options.h"
#include "libaburi/frontend.h"
#include "libaburi/modules/scan.h"
#include "libaburi/modules/session.h"
#include "libaburi/serialize/bmi.h"
#include "perf_stats.h"
#include "source_mgnt.h"

namespace {

using aburi::driver::DriverOptions;

bool is_stdin_input(const std::string& path) {
    return path == "-";
}

std::string read_file(const std::string& path) {
    if (is_stdin_input(path)) {
        std::ostringstream ss;
        ss << std::cin.rdbuf();
        return ss.str();
    }
    std::ifstream in(path, std::ios::binary);
    if (!in) {
        throw std::runtime_error("could not open input file '" + path + "'");
    }
    std::ostringstream ss;
    ss << in.rdbuf();
    return ss.str();
}

bool has_cpp_extension(const std::string& path) {
    auto ends_with = [&](std::string_view suffix) {
        return path.size() >= suffix.size() &&
               path.compare(path.size() - suffix.size(), suffix.size(), suffix) == 0;
    };
    return ends_with(".cc") || ends_with(".cpp") || ends_with(".cxx") ||
           ends_with(".c++") || ends_with(".C") || ends_with(".hpp") ||
           ends_with(".cppm") || ends_with(".ixx") || ends_with(".mpp");
}

bool has_cpp_module_extension(const std::string& path) {
    auto ends_with = [&](std::string_view suffix) {
        return path.size() >= suffix.size() &&
               path.compare(path.size() - suffix.size(), suffix.size(), suffix) == 0;
    };
    return ends_with(".cppm") || ends_with(".ixx") || ends_with(".mpp");
}

bool has_objc_extension(const std::string& path) {
    auto ends_with = [&](std::string_view suffix) {
        return path.size() >= suffix.size() &&
               path.compare(path.size() - suffix.size(), suffix.size(), suffix) == 0;
    };
    return ends_with(".m") || ends_with(".mm") || ends_with(".M");
}

LangOptions options_for_file(LangOptions opts, const std::string& path) {
    if (opts.language_mode == LanguageMode::Auto) {
        auto ends_with = [&](std::string_view suffix) {
            return path.size() >= suffix.size() &&
                   path.compare(path.size() - suffix.size(), suffix.size(), suffix) == 0;
        };
        if (has_objc_extension(path)) {

            opts.language_mode = ends_with(".m") ? LanguageMode::C
                                                 : LanguageMode::CXX;
            opts.objc = true;
        } else {
            opts.language_mode = has_cpp_extension(path) ? LanguageMode::CXX
                                                         : LanguageMode::C;
        }
    }

    if (opts.standard.empty() && opts.language_mode == LanguageMode::CXX &&
        has_cpp_module_extension(path)) {
        opts.set_standard("c++20");
    }
    return opts;
}

std::string to_lower_ascii(std::string value) {
    for (char& c : value) {
        if (c >= 'A' && c <= 'Z') {
            c = static_cast<char>(c - 'A' + 'a');
        }
    }
    return value;
}

std::string input_extension(const std::filesystem::path& input_path) {
    return to_lower_ascii(input_path.extension().string());
}

bool is_cpp_source_extension(const std::string& ext) {
    return ext == ".cc" || ext == ".cpp" || ext == ".cxx" ||
           ext == ".c++" || ext == ".cp" || ext == ".cppm" ||
           ext == ".ixx" || ext == ".mpp";
}

bool is_linker_input_extension(const std::string& ext) {
    return ext == ".o" || ext == ".a" || ext == ".so" ||
           ext == ".dylib" || ext == ".tbd" || ext == ".lo";
}

bool is_passthrough_source_extension(const DriverOptions& opts, const std::string& ext) {
    if (ext == ".m" || ext == ".mm" || opts.lang_opts.is_objc()) {

        return opts.objc_passthrough;
    }
    return ext == ".s" || ext == ".asm" || ext == ".cu";
}

bool is_frontend_source(const DriverOptions& opts, const std::filesystem::path& path) {
    if (opts.assembler_language) {
        return false;
    }

    const std::string ext = input_extension(path);
    if (is_passthrough_source_extension(opts, ext) ||
        is_linker_input_extension(ext)) {
        return false;
    }

    if (opts.preprocess_only) {
        return true;
    }
    if (opts.lang_opts.language_mode != LanguageMode::Auto) {
        return true;
    }

    if (is_stdin_input(path.string())) {
        return true;
    }
    return ext == ".c" || is_cpp_source_extension(ext) ||
           ext == ".m" || ext == ".mm" ||
           path.extension().string() == ".C";
}

bool file_selects_cxx_linker(const DriverOptions& opts, const std::filesystem::path& path) {
    LangOptions lang_opts = options_for_file(opts.lang_opts, path.string());
    if (lang_opts.is_cxx_mode()) {
        return true;
    }
    const std::string ext = input_extension(path);
    return ext == ".mm" || ext == ".cu";
}

std::ostream& open_output_if_requested(const DriverOptions& opts,
                                       std::ofstream& owned,
                                       bool multi_input) {
    if (opts.output_path.empty()) {
        return std::cout;
    }
    if (multi_input) {
        throw std::runtime_error("-o cannot be used with multiple inputs in this driver");
    }
    owned.open(opts.output_path, std::ios::binary);
    if (!owned) {
        throw std::runtime_error("could not open output file '" + opts.output_path + "'");
    }
    return owned;
}

int output_mode_count(const DriverOptions& opts) {
    int count = 0;
    if (opts.emit_llvm) ++count;
    if (opts.emit_assembly) ++count;
    if (opts.compile_only) ++count;
    if (opts.jit) ++count;
    return count;
}

bool needs_text_output_stream(const DriverOptions& opts) {
    return opts.preprocess_only || opts.dump_syntax || opts.dump_cir ||
           opts.dump_air || opts.emit_llvm;
}

std::string derived_target_output_path(const DriverOptions& opts,
                                       const std::string& input_path,
                                       std::string_view extension) {
    if (!opts.output_path.empty()) {
        return opts.output_path;
    }
    std::filesystem::path path(input_path);
    std::string stem = path.stem().string();
    if (stem.empty()) {
        stem = "a";
    }
    return stem + std::string(extension);
}

std::string depfile_escape(const std::string& path) {
    std::string escaped;
    escaped.reserve(path.size());
    for (char c : path) {
        if (c == ' ') {
            escaped += "\\ ";
        } else if (c == '#') {
            escaped += "\\#";
        } else if (c == '$') {
            escaped += "$$";
        } else {
            escaped.push_back(c);
        }
    }
    return escaped;
}

std::string default_depfile_target(const DriverOptions& opts,
                                   const std::string& input_path) {
    if (!opts.output_path.empty()) {
        return opts.output_path;
    }

    std::filesystem::path path(input_path);
    std::string stem = path.stem().string();
    if (stem.empty()) {
        stem = "a";
    }
    return stem + ".o";
}

std::string default_depfile_path(const DriverOptions& opts,
                                 const std::string& input_path) {
    std::filesystem::path base(opts.output_path.empty() ? input_path
                                                        : opts.output_path);
    std::string stem = base.stem().string();
    if (stem.empty()) {
        stem = "a";
    }
    std::filesystem::path dir = base.parent_path();
    return (dir / (stem + ".d")).string();
}

bool write_depfile(const DriverOptions& opts,
                   const std::string& input_path,
                   const SourceManager& sm) {

    const bool to_stdout =
        opts.depfile.generate_only && opts.depfile.output_path.empty();
    const std::string depfile_path = opts.depfile.output_path.empty()
        ? default_depfile_path(opts, input_path)
        : opts.depfile.output_path;

    std::vector<std::string> deps;
    deps.push_back(input_path == "-" ? "<stdin>" : input_path);
    for (const auto& file : sm.files) {
        if (file == nullptr || file->resolved_path.empty()) {
            continue;
        }
        if (file->is_system_header && !opts.depfile.include_system_headers) {
            continue;
        }
        if (file->resolved_path == deps.front()) {
            continue;
        }
        deps.push_back(file->resolved_path);
    }

    std::ofstream owned;
    if (!to_stdout) {
        owned.open(depfile_path, std::ios::binary);
        if (!owned) {
            std::cerr << "aburi: error: cannot write dependency file '"
                      << depfile_path << "'\n";
            return false;
        }
    }
    std::ostream& out = to_stdout ? std::cout : owned;

    std::string target_list;
    if (opts.depfile.targets.empty()) {
        target_list = depfile_escape(default_depfile_target(opts, input_path));
    } else {
        for (size_t i = 0; i < opts.depfile.targets.size(); ++i) {
            if (i != 0) {
                target_list += ' ';
            }

            target_list += opts.depfile.targets[i];
        }
    }

    out << target_list << ':';
    for (const std::string& dep : deps) {
        out << " \\\n  " << depfile_escape(dep);
    }
    out << '\n';
    if (opts.depfile.phony_targets) {

        for (size_t i = 1; i < deps.size(); ++i) {
            out << '\n' << depfile_escape(deps[i]) << ":\n";
        }
    }
    return out.good();
}

bool is_final_link_mode(const DriverOptions& opts) {
    return !opts.preprocess_only &&
           !opts.precompile_only &&
           !opts.syntax_only &&
           !opts.dump_syntax &&
           !opts.dump_cir &&
           !opts.dump_air &&
           !opts.emit_llvm &&
           !opts.emit_assembly &&
           !opts.compile_only &&
           !opts.jit;
}

struct LinkState {
    std::vector<std::string> object_files;
    std::vector<std::string> linker_input_files;
    std::optional<std::filesystem::path> temp_object_dir;
    size_t temp_object_counter = 0;
    bool link_as_cxx = false;
    bool link_objc_runtime = false;
};

std::filesystem::path ensure_temp_object_dir(LinkState& state) {
    if (state.temp_object_dir.has_value()) {
        return *state.temp_object_dir;
    }

    llvm::SmallString<256> temp_dir_storage;
    std::error_code ec =
        llvm::sys::fs::createUniqueDirectory("aburi-link-%%%%%%", temp_dir_storage);
    if (ec) {
        throw std::runtime_error(
            "unable to create temporary link object directory: " + ec.message());
    }
    state.temp_object_dir = std::filesystem::path(std::string(temp_dir_storage.str()));
    return *state.temp_object_dir;
}

std::string temporary_object_path(LinkState& state, const std::filesystem::path& input_path) {
    std::string stem = input_path.stem().string();
    if (stem.empty()) {
        stem = "input";
    }
    std::filesystem::path temp_path =
        ensure_temp_object_dir(state) /
        (stem + "." + std::to_string(state.temp_object_counter++) + ".o");
    return temp_path.string();
}

void cleanup_temp_objects(LinkState& state) {
    if (!state.temp_object_dir.has_value()) {
        return;
    }
    std::error_code ec;
    std::filesystem::remove_all(*state.temp_object_dir, ec);
}

int run_command(const std::string& command, const std::vector<std::string>& args) {
    std::vector<llvm::StringRef> arg_refs;
    arg_refs.push_back(command);
    for (const std::string& arg : args) {
        arg_refs.push_back(arg);
    }

    std::string error_message;
    int result = llvm::sys::ExecuteAndWait(command,
        llvm::ArrayRef<llvm::StringRef>(arg_refs),
        std::nullopt,
        {},
        0,
        0,
        &error_message);
    if (result != 0 && !error_message.empty()) {
        std::cerr << "aburi: error: " << error_message << '\n';
    }
    return result;
}

bool target_is_linux(const DriverOptions& opts) {
    return !opts.target_triple.empty() &&
           target_os_from_triple(opts.target_triple) == TargetOS::LINUX;
}

bool target_is_cross_elf(const DriverOptions& opts) {
    if (opts.target_triple.empty()) {
        return false;
    }
    TargetOS os = target_os_from_triple(opts.target_triple);
    return os == TargetOS::LINUX || os == TargetOS::FREEBSD ||
           os == TargetOS::NETBSD;
}

std::shared_ptr<TargetInfo> effective_target_info(const DriverOptions& opts) {
    std::shared_ptr<TargetInfo> info;
    if (!opts.target_triple.empty()) {
        info = TargetInfo::create_for_triple(opts.target_triple);
    }
    if (!info) {
        info = TargetInfo::create_host();
    }

    if (info && opts.short_wchar) {
        info->wchar_width = 16;
    }
    return info;
}

bool integrated_assembler_supports(
    const std::shared_ptr<TargetInfo>& target) {
    if (!target || target->os != TargetOS::MACOS) {
        return false;
    }
    return target->arch == TargetArch::AARCH64 ||
           target->arch == TargetArch::X86_64;
}

std::string codegen_feature_string(const DriverOptions& opts) {
    std::shared_ptr<TargetInfo> target = effective_target_info(opts);
    bool aarch64 = target && target->arch == TargetArch::AARCH64;
    std::vector<std::string> features;
    if (opts.general_regs_only && aarch64) {
        features.insert(features.end(),
                        {"+v8a", "-fp-armv8", "-neon", "-sve"});
    } else if (aarch64 && (opts.aarch64_aes || opts.aarch64_sha2)) {

        features.push_back("+v8a");
        if (opts.aarch64_aes) {
            features.push_back("+aes");
        }
        if (opts.aarch64_sha2) {
            features.push_back("+sha2");
        }
    }

    if (aarch64) {
        for (int reg : opts.reserved_aarch64_gprs) {
            features.push_back("+reserve-x" + std::to_string(reg));
        }
    }
    std::string joined;
    for (const std::string& feature : features) {
        if (!joined.empty()) {
            joined += ",";
        }
        joined += feature;
    }
    return joined;
}

std::string resolve_installed_dir(const char* argv0) {
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

std::string clang_persona_version(const TargetInfo& target) {
    return std::to_string(target.clang_major) + "." +
           std::to_string(target.clang_minor) + "." +
           std::to_string(target.clang_patch);
}

std::string gcc_persona_version() {
    return std::to_string(aburi::driver::kGccPersonaMajor) + "." +
           std::to_string(aburi::driver::kGccPersonaMinor) + "." +
           std::to_string(aburi::driver::kGccPersonaPatch);
}

void print_gcc_version_banner(std::ostream& os) {
    os << "gcc (" << aburi::driver::kGccPersonaBrand << ") "
       << gcc_persona_version()
       << " (" << aburi::driver::kAburiProductName << ' '
       << aburi::driver::kAburiVersionString
       << "; compatible with GCC from the Free Software Foundation)\n";
}

void print_gcc_verbose_banner(std::ostream& os,
                              const DriverOptions& opts) {
    std::shared_ptr<TargetInfo> target = effective_target_info(opts);
    const std::string triple = target ? target->triple : opts.target_triple;
    os << "Using built-in specs.\n";
    os << "Target: " << triple << '\n';
    os << "Thread model: posix\n";

    os << "gcc version " << gcc_persona_version()
       << " (" << aburi::driver::kGccPersonaBrand
       << "; " << aburi::driver::kAburiProductName << ' '
       << aburi::driver::kAburiVersionString
       << "; compatible with GCC from the Free Software Foundation)\n";
}

void print_version_banner(std::ostream& os,
                          const DriverOptions& opts,
                          const char* argv0) {
    std::shared_ptr<TargetInfo> target = effective_target_info(opts);
    const std::string triple =
        target ? target->triple : opts.target_triple;
    if (opts.persona == aburi::driver::DriverPersona::ClangCompat) {

        os << "clang version "
           << (target ? clang_persona_version(*target) : "0.0.0")
           << " (" << aburi::driver::kAburiProductName << ' '
           << aburi::driver::kAburiVersionString << ")\n";
        os << "Target: " << triple << '\n';
        os << "Thread model: posix\n";
        os << "InstalledDir: " << resolve_installed_dir(argv0) << '\n';
        return;
    }
    if (opts.persona == aburi::driver::DriverPersona::GccCompat) {
        print_gcc_version_banner(os);
        return;
    }
    os << aburi::driver::kAburiProductName << " compiler "
       << aburi::driver::kAburiVersionString << '\n';
    os << "Target: " << triple << '\n';
    os << "InstalledDir: " << resolve_installed_dir(argv0) << '\n';
}

int handle_early_driver_query(const DriverOptions& opts, const char* argv0) {
    using aburi::driver::EarlyDriverQuery;
    switch (opts.early_query) {
        case EarlyDriverQuery::Version:
            print_version_banner(std::cout, opts, argv0);
            return 0;
        case EarlyDriverQuery::VerboseVersion:
            if (opts.persona == aburi::driver::DriverPersona::GccCompat) {
                print_gcc_verbose_banner(std::cerr, opts);
            } else {
                print_version_banner(std::cout, opts, argv0);
            }
            return 0;
        case EarlyDriverQuery::DumpMachine: {
            std::shared_ptr<TargetInfo> target = effective_target_info(opts);
            std::cout << (target ? target->triple : opts.target_triple) << '\n';
            return 0;
        }
        case EarlyDriverQuery::PrintFileName:

            std::cout << opts.print_file_name << '\n';
            return 0;
        case EarlyDriverQuery::DumpVersion: {
            if (opts.persona == aburi::driver::DriverPersona::ClangCompat) {
                std::shared_ptr<TargetInfo> target = effective_target_info(opts);
                std::cout << (target ? clang_persona_version(*target) : "0.0.0")
                          << '\n';
            } else if (opts.persona ==
                       aburi::driver::DriverPersona::GccCompat) {
                std::cout << aburi::driver::kGccPersonaMajor << '\n';
            } else {
                std::cout << aburi::driver::kAburiVersionString << '\n';
            }
            return 0;
        }
        case EarlyDriverQuery::DumpFullVersion:
            std::cout << gcc_persona_version() << '\n';
            return 0;
        case EarlyDriverQuery::None:
            break;
    }
    return -1;
}

bool target_is_x86_32(const DriverOptions& opts) {
    const std::string& t = opts.target_triple;
    return (t.find("i386") != std::string::npos ||
            t.find("i486") != std::string::npos ||
            t.find("i586") != std::string::npos ||
            t.find("i686") != std::string::npos);
}

bool target_is_or1k(const DriverOptions& opts) {
    const std::string& t = opts.target_triple;
    return t.find("or1k") != std::string::npos ||
           t.find("openrisc") != std::string::npos;
}

std::string primary_target_sysroot(const DriverOptions& opts) {
    if (!opts.sysroots.empty()) {
        return opts.sysroots.front();
    }
    if (const char* env = std::getenv("ABURI_LINUX_SYSROOT")) {
        return env;
    }
    return {};
}

std::string cross_compiler_path(const DriverOptions& opts, bool as_cxx) {
    std::string base = opts.cross_cc;
    if (base.empty()) {
        if (const char* env = std::getenv("ABURI_CROSS_CC")) {
            base = env;
        }
    }
    if (base.empty()) {
        base = "/opt/homebrew/opt/llvm/bin/clang";
    }
    if (as_cxx) {
        if (base.size() >= 5 && base.rfind("clang") == base.size() - 5) {
            base += "++";
        } else if (base.size() >= 3 && base.rfind("gcc") == base.size() - 3) {
            base.replace(base.size() - 3, 3, "g++");
        }
    }
    return base;
}

bool cross_compiler_is_clang(const std::string& path) {
    return path.find("clang") != std::string::npos;
}

bool has_explicit_target_sysroot(const DriverOptions& opts) {
    if (!opts.sysroots.empty()) {
        return true;
    }
    return target_is_linux(opts) && std::getenv("ABURI_LINUX_SYSROOT") != nullptr;
}

StdLibKind effective_stdlib(const DriverOptions& opts) {
    return resolve_effective_stdlib(opts.target_triple,
        opts.requested_stdlib,
        has_explicit_target_sysroot(opts));
}

// Everything the final link needs in order to put Adinkra on the command line.
// Inactive whenever the user is supplying the C++ standard library themselves.
struct AdinkraLinkPlan {
    bool active = false;
    std::string library;
    std::string rpath_dir;
    std::string error;
};

AdinkraLinkPlan plan_adinkra_link(const DriverOptions& opts,
                                  bool link_as_cxx,
                                  const char* argv0) {
    AdinkraLinkPlan plan;
    if (!link_as_cxx || effective_stdlib(opts) != StdLibKind::Adinkra) {
        return plan;
    }
    if (opts.nostdlib || opts.nostdlibxx) {
        return plan;
    }

    if (!opts.adinkra_library.empty()) {
        plan.active = true;
        plan.library = opts.adinkra_library;
        return plan;
    }
    if (!target_is_native_host(opts.target_triple) && opts.adinkra_root.empty()) {
        plan.error = "aburi: error: '-stdlib=adinkra' for target '" +
            opts.target_triple +
            "' needs a target-built Adinkra runtime; pass --adinkra-lib=PATH "
            "or --adinkra-root=DIR";
        return plan;
    }

    const AdinkraLayout& layout = discover_adinkra_layout(argv0, opts.adinkra_root);
    const bool want_shared = opts.adinkra_runtime == AdinkraRuntimeKind::Shared;
    plan.library = want_shared ? layout.shared_library : layout.static_library;
    if (plan.library.empty()) {
        return plan;
    }
    plan.active = true;
    if (want_shared && layout.from_build_tree) {
        plan.rpath_dir = layout.shared_library_dir;
    }
    return plan;
}

bool require_adinkra_when_requested(const DriverOptions& opts, const char* argv0) {
    if (opts.requested_stdlib != StdLibKind::Adinkra) {
        return true;
    }
    if (!opts.adinkra_library.empty()) {
        return true;
    }
    const AdinkraLayout& layout = discover_adinkra_layout(argv0, opts.adinkra_root);
    if (layout.found) {
        return true;
    }
    std::cerr << "aburi: error: '-stdlib=adinkra' selected but the Adinkra "
              << "headers were not found\n";
    for (const std::string& root : layout.attempted_roots) {
        std::cerr << "note:   searched " << root << '\n';
    }
    std::cerr << "note: set ABURI_ADINKRA_ROOT or pass --adinkra-root=DIR\n";
    return false;
}

std::vector<std::string> passthrough_compile_flags(const DriverOptions& opts,
                                                   const char* argv0) {
    std::vector<std::string> flags;
    for (const std::string& path : opts.include_paths) {
        flags.push_back("-I" + path);
    }
    for (const std::string& path : opts.system_include_paths) {
        flags.push_back("-isystem");
        flags.push_back(path);
    }
    for (const std::string& path : opts.quote_include_paths) {
        flags.push_back("-iquote");
        flags.push_back(path);
    }
    for (const std::string& path : opts.framework_include_paths) {
        flags.push_back("-F" + path);
    }
    for (const std::string& path : opts.system_framework_include_paths) {
        flags.push_back("-iframework");
        flags.push_back(path);
    }
    for (const auto& [name, value] : opts.defines) {
        flags.push_back("-D" + name + "=" + value);
    }
    for (const std::string& name : opts.undefines) {
        flags.push_back("-U" + name);
    }
    if (!opts.target_triple.empty()) {
        flags.push_back("-target");
        flags.push_back(opts.target_triple);
    }
    if (target_is_linux(opts)) {
        const std::string sysroot = primary_target_sysroot(opts);
        if (!sysroot.empty()) {
            flags.push_back("--sysroot=" + sysroot);
        }
    } else {
        for (const std::string& sysroot : opts.sysroots) {
            flags.push_back("-isysroot");
            flags.push_back(sysroot);
        }
    }
    if (opts.assembler_language) {
        flags.push_back("-x");
        flags.push_back("assembler-with-cpp");
    } else if (opts.lang_opts.language_mode == LanguageMode::C) {
        flags.push_back("-x");
        flags.push_back(opts.lang_opts.objc ? "objective-c" : "c");
    } else if (opts.lang_opts.language_mode == LanguageMode::CXX) {
        flags.push_back("-x");
        flags.push_back(opts.lang_opts.objc ? "objective-c++" : "c++");
    }
    if (opts.lang_opts.objc_arc) {
        flags.push_back("-fobjc-arc");
    }
    // ObjC++ and CUDA go to the system compiler. It has never heard of
    // '-stdlib=adinkra', and leaving those units on libc++ while sibling C++
    // units use Adinkra would produce two incompatible std:: namespaces that
    // link cleanly and then fail to interoperate.
    if (effective_stdlib(opts) == StdLibKind::Adinkra) {
        const AdinkraLayout& layout =
            discover_adinkra_layout(argv0, opts.adinkra_root);
        if (layout.found) {
            flags.push_back("-nostdinc++");
            flags.push_back("-isystem");
            flags.push_back(layout.include_dir);
        }
    } else if (opts.requested_stdlib != StdLibKind::Auto) {
        flags.push_back("-stdlib=" + stdlib_kind_name(opts.requested_stdlib));
    }

    if (opts.nostdinc) {
        flags.push_back("-nostdinc");
    }
    if (opts.nostdincxx) {
        flags.push_back("-nostdinc++");
    }
    for (const std::string& file : opts.pre_includes) {
        flags.push_back("-include");
        flags.push_back(file);
    }
    if (opts.keep_comments) {
        flags.push_back("-C");
    }
    if (opts.preprocess_no_linemarkers) {
        flags.push_back("-P");
    }
    for (const std::string& wa : opts.assembler_flags) {
        flags.push_back(wa);
    }
    if (opts.depfile.enabled) {

        if (opts.depfile.generate_only) {
            flags.push_back(opts.depfile.include_system_headers ? "-M" : "-MM");
        } else {
            flags.push_back(opts.depfile.include_system_headers ? "-MD" : "-MMD");
        }
        if (!opts.depfile.output_path.empty()) {
            flags.push_back("-MF");
            flags.push_back(opts.depfile.output_path);
        }
        for (const std::string& target : opts.depfile.targets) {
            flags.push_back("-MT");
            flags.push_back(target);
        }
        if (opts.depfile.phony_targets) {
            flags.push_back("-MP");
        }
    }
    return flags;
}

std::vector<std::string> linker_driver_flags(const DriverOptions& opts,
                                             bool link_as_cxx,
                                             const AdinkraLinkPlan& adinkra) {
    std::vector<std::string> flags;
    if (!opts.target_triple.empty()) {
        flags.push_back("-target");
        flags.push_back(opts.target_triple);
    }
    if (target_is_cross_elf(opts)) {
        const std::string sysroot = primary_target_sysroot(opts);
        if (!sysroot.empty()) {
            flags.push_back("--sysroot=" + sysroot);
        }
    } else {
        for (const std::string& sysroot : opts.sysroots) {
            flags.push_back("-isysroot");
            flags.push_back(sysroot);
        }
    }
    if (adinkra.active) {
        // Adinkra replaces the host driver's C++ standard library entirely.
        flags.push_back("-nostdlib++");
    } else if (link_as_cxx && opts.requested_stdlib != StdLibKind::Auto &&
               opts.requested_stdlib != StdLibKind::Adinkra) {
        // '-stdlib=adinkra' is meaningless to the host driver, and a C-only
        // link has no C++ standard library to select.
        flags.push_back("-stdlib=" + stdlib_kind_name(opts.requested_stdlib));
    }
    if (target_is_x86_32(opts) || target_is_or1k(opts)) {
        flags.push_back("-no-pie");
    }
    return flags;
}

bool validate_driver_options(const DriverOptions& opts) {
    if (output_mode_count(opts) > 1) {
        std::cerr
            << "aburi: error: choose only one of --emit-llvm, -S, -c, or --jit\n";
        return false;
    }
    if (opts.syntax_only &&
        (opts.emit_llvm || opts.emit_assembly || opts.compile_only || opts.jit)) {
        std::cerr << "aburi: error: cannot combine '-fsyntax-only' with a "
                  << "backend output stage\n";
        return false;
    }
    if (opts.lang_opts.blocks_mode == BlocksMode::Enabled) {
        std::shared_ptr<TargetInfo> target = opts.target_triple.empty()
            ? TargetInfo::create_host()
            : TargetInfo::create_for_triple(opts.target_triple);
        if (!target || target->os != TargetOS::MACOS) {
            std::cerr << "aburi: error: '-fblocks' is only supported on Darwin "
                      << "targets\n";
            return false;
        }
    }
    if ((opts.emit_llvm || opts.emit_assembly || opts.compile_only) &&
        (opts.dump_syntax || opts.dump_cir || opts.dump_air)) {
        std::cerr
            << "aburi: error: output modes cannot be combined with "
            << "--dump-syntax, --dump-cir, or --dump-air\n";
        return false;
    }
    if (opts.backend == "air") {
        if (opts.jit) {
            std::cerr << "aburi: error: --jit is not supported with "
                      << "--backend=air yet\n";
            return false;
        }
        if (opts.emit_llvm) {
            std::cerr << "aburi: error: --emit-llvm requires --backend=llvm\n";
            return false;
        }
    }
    if (!opts.output_path.empty() && opts.input_files.size() > 1 &&
        (opts.preprocess_only || opts.dump_syntax || opts.dump_cir ||
         opts.dump_air || opts.emit_llvm || opts.emit_assembly ||
         opts.compile_only)) {
        std::cerr
            << "aburi: error: -o cannot be used with multiple inputs in this mode\n";
        return false;
    }

    if (opts.jit) {
        if (opts.preprocess_only || opts.dump_macros || opts.syntax_only ||
            opts.dump_syntax || opts.dump_cir || opts.dump_air ||
            !opts.dump_cir_example.empty()) {
            std::cerr
                << "aburi: error: --jit cannot be combined with preprocessing, "
                << "syntax-only, or dump modes\n";
            return false;
        }
        if (!opts.output_path.empty()) {
            std::cerr << "aburi: error: --jit does not write an output file\n";
            return false;
        }
        if (opts.input_files.size() > 1) {
            std::cerr << "aburi: error: --jit accepts exactly one input file\n";
            return false;
        }
    }
    return true;
}

aburi::frontend::FrontendInvocation make_invocation(const DriverOptions& base_opts,
                                                    const std::string& path,
                                                    std::string source,
                                                    const char* argv0) {
    aburi::frontend::FrontendInvocation invocation;
    invocation.filename = path;
    invocation.source = std::move(source);
    invocation.lang_options = options_for_file(base_opts.lang_opts, path);
    invocation.target_triple = base_opts.target_triple;

    invocation.target = effective_target_info(base_opts);
    invocation.include_paths = base_opts.include_paths;
    invocation.system_include_paths = base_opts.system_include_paths;
    invocation.quote_include_paths = base_opts.quote_include_paths;
    invocation.framework_include_paths = base_opts.framework_include_paths;
    invocation.system_framework_include_paths =
        base_opts.system_framework_include_paths;
    invocation.sysroots = base_opts.sysroots;
    invocation.pre_includes = base_opts.pre_includes;
    if (base_opts.persona == aburi::driver::DriverPersona::GccCompat) {

        invocation.defines.emplace_back(
            "__GNUC__", std::to_string(aburi::driver::kGccPersonaMajor));
        invocation.defines.emplace_back(
            "__GNUC_MINOR__", std::to_string(aburi::driver::kGccPersonaMinor));
        invocation.defines.emplace_back(
            "__GNUC_PATCHLEVEL__", std::to_string(aburi::driver::kGccPersonaPatch));
        invocation.defines.emplace_back(
            "__VERSION__", "\"" + gcc_persona_version() + " (" +
                               aburi::driver::kGccPersonaBrand + ")\"");
        if (invocation.lang_options.is_cxx_mode()) {
            invocation.defines.emplace_back(
                "__GNUG__", std::to_string(aburi::driver::kGccPersonaMajor));
        }
        invocation.undefines = {
            "__clang__",
            "__clang_major__",
            "__clang_minor__",
            "__clang_patchlevel__",
            "__clang_version__",
        };
    }
    invocation.defines.insert(invocation.defines.end(),
                              base_opts.defines.begin(), base_opts.defines.end());
    invocation.undefines.insert(invocation.undefines.end(),
                                base_opts.undefines.begin(), base_opts.undefines.end());
    invocation.requested_stdlib = base_opts.requested_stdlib;
    invocation.adinkra_root = base_opts.adinkra_root;
    invocation.nostdinc = base_opts.nostdinc;
    invocation.nostdincxx = base_opts.nostdincxx;
    invocation.inhibit_warnings = base_opts.inhibit_warnings;
    invocation.argv0_for_header_discovery = argv0 ? argv0 : "";
    return invocation;
}

void print_frontend_failures(const aburi::frontend::FrontendResult& result) {
    if (!result.exception_text.empty()) {
        std::cerr << "aburi: error: " << result.exception_text << '\n';
    }
    for (const std::string& diagnostic : result.diagnostics) {
        std::cerr << diagnostic << '\n';
    }
    if (!result.tree_verified && !result.tree_verify_output.empty()) {
        std::cerr << result.tree_verify_output;
    }
    if (!result.cir_verified && !result.cir_verify_output.empty()) {
        std::cerr << result.cir_verify_output;
    }
}

void print_lowering_diagnostics(const std::shared_ptr<SourceManager>& sm,
                                const std::vector<Diagnostic>& diagnostics) {
    for (const Diagnostic& diag : diagnostics) {
        std::cerr << aburi::frontend::format_diagnostic(sm, diag) << '\n';
    }
}

int run_air_native_output(const DriverOptions& base_opts,
                          const std::string& path,
                          aburi::frontend::FrontendResult& frontend,
                          LinkState* link_state) {
    aburi::cir2air::AirLoweringOptions lowering_options;
    lowering_options.target = frontend.cir.target_info_ptr();
    lowering_options.module_name = path;
    lowering_options.cxx_mangling =
        options_for_file(base_opts.lang_opts, path).is_cxx_mode();
    aburi::cir2air::AirLoweringResult air_result = [&] {
        PerfScopedTimer timer(active_perf_profiler(), PerfPhase::AirLowering);
        return aburi::cir2air::lower_cir_to_air(frontend.cir,
                                                std::move(lowering_options));
    }();
    print_lowering_diagnostics(frontend.source_manager, air_result.diagnostics);
    if (!air_result.ok()) {
        return 1;
    }
    aburi::air::VerifyResult verify = aburi::air::verify_module(*air_result.module);
    if (!verify.ok()) {
        std::cerr << "aburi: error: air verifier rejected cir2air output:\n"
                  << verify.to_string() << '\n';
        return 1;
    }
    if (base_opts.opt_level >= 1) {
        aburi::air::PipelineOptions pipeline_options;
#ifdef NDEBUG
        pipeline_options.verify_each = false;
#endif
        aburi::air::PipelineResult piped =
            aburi::air::run_o1_pipeline(*air_result.module, pipeline_options);
        if (!piped.verified) {
            std::cerr << "aburi: error: air pass pipeline broke the module: "
                      << piped.verify_error << '\n';
            return 1;
        }
    }

    aburi::backend::BackendOptions backend_options;
    backend_options.opt_level = base_opts.opt_level;
    backend_options.emit_unwind_tables = true;
    backend_options.verify_mir = base_opts.verify_mir;
    auto emit_text = [&](std::ostringstream& assembly) -> bool {
        aburi::backend::EmitResult emit_result = aburi::backend::emit_assembly(
            *air_result.module, air_result.module->target(), assembly,
            backend_options);
        print_lowering_diagnostics(frontend.source_manager,
                                   emit_result.diagnostics);
        return emit_result.ok();
    };
    auto write_file = [&](const std::string& output_path,
                          const std::string& contents) -> bool {
        std::ofstream file(output_path, std::ios::binary);
        if (!file) {
            std::cerr << "aburi: error: cannot open output file " << output_path
                      << '\n';
            return false;
        }
        file << contents;
        return file.good();
    };

    if (base_opts.emit_assembly) {
        std::ostringstream assembly;
        if (!emit_text(assembly)) {
            return 1;
        }
        std::string output_path =
            derived_target_output_path(base_opts, path, ".s");
        return write_file(output_path, assembly.str()) ? 0 : 1;
    }

    std::string object_path = link_state
        ? temporary_object_path(*link_state, std::filesystem::path(path))
        : derived_target_output_path(base_opts, path, ".o");

    if (base_opts.air_object == "direct") {
        std::ostringstream object_bytes;
        aburi::backend::EmitResult emit_result = aburi::backend::emit_object(
            *air_result.module, air_result.module->target(), object_bytes,
            backend_options);
        print_lowering_diagnostics(frontend.source_manager,
                                   emit_result.diagnostics);
        if (!emit_result.ok()) {
            return 1;
        }
        if (!write_file(object_path, object_bytes.str())) {
            return 1;
        }
        if (link_state != nullptr) {
            link_state->object_files.push_back(object_path);
        }
        return 0;
    }

    std::ostringstream assembly;
    if (!emit_text(assembly)) {
        return 1;
    }

    std::shared_ptr<TargetInfo> asm_target = effective_target_info(base_opts);
    bool integrated = base_opts.air_object == "as" &&
                      base_opts.integrated_as &&
                      integrated_assembler_supports(asm_target);
    if (integrated && !base_opts.assembler_flags.empty()) {
        std::cerr << "aburi: error: -Wa options are not supported by the "
                     "integrated assembler yet; pass -fno-integrated-as or "
                     "--air-object=system-as\n";
        return 1;
    }
    if (integrated) {
        aburi::assembler::AsmOptions asm_options;
        asm_options.target = asm_target;

        asm_options.filename = "<assembly generated from " + path + ">";
        std::ostringstream object_bytes;
        aburi::assembler::AssembleResult assembled =
            aburi::assembler::assemble_string_to_object(
                assembly.str(), asm_options, object_bytes);
        if (!assembled.ok) {
            for (const Diagnostic& diag : assembled.diagnostics) {
                std::cerr << "aburi: error: " << diag.message << '\n';
            }
            return 1;
        }
        if (!write_file(object_path, object_bytes.str())) {
            return 1;
        }
        if (link_state != nullptr) {
            link_state->object_files.push_back(object_path);
        }
        return 0;
    }

    std::string s_path = object_path + ".air.s";
    if (!write_file(s_path, assembly.str())) {
        return 1;
    }
    std::string assembler = "/usr/bin/cc";
    std::vector<std::string> assemble_args = {"-c", s_path, "-o", object_path};
    if (target_is_linux(base_opts)) {
        assembler = cross_compiler_path(base_opts, false);
        assemble_args.insert(assemble_args.begin(),
                             "--target=" + base_opts.target_triple);
    } else if (!base_opts.target_triple.empty()) {

        assemble_args.insert(assemble_args.begin(),
                             "--target=" + base_opts.target_triple);
    }
    int assemble = run_command(assembler, assemble_args);
    std::error_code ignored;
    if (link_state == nullptr) {
        std::filesystem::remove(s_path, ignored);
    }
    if (assemble != 0) {
        std::cerr << "aburi: error: assembling " << s_path << " failed\n";
        return 1;
    }
    if (link_state != nullptr) {
        link_state->object_files.push_back(object_path);
    }
    return 0;
}

int run_file(const DriverOptions& base_opts,
             aburi::modules::ModuleBuildSession* module_session,
             const std::string& path,
             bool multi_input,
             const char* argv0,
             LinkState* link_state = nullptr) {
    std::string source;
    {
        PerfScopedTimer timer(active_perf_profiler(), PerfPhase::InputRead);
        source = read_file(path);
    }

    const std::string display_path = is_stdin_input(path) ? "<stdin>" : path;
    aburi::frontend::FrontendInvocation invocation =
        make_invocation(base_opts, display_path, std::move(source), argv0);
    invocation.module_loader = module_session;

    std::ofstream output_file;
    std::ostream* out = &std::cout;
    if (needs_text_output_stream(base_opts)) {
        out = &open_output_if_requested(base_opts, output_file, multi_input);
    }

    if (base_opts.preprocess_only) {
        aburi::frontend::PreprocessOutputMode mode =
            aburi::frontend::PreprocessOutputMode::Text;
        if (base_opts.dump_macros) {
            mode = aburi::frontend::PreprocessOutputMode::MacroDefinitions;
        } else if (base_opts.preprocess_no_linemarkers) {
            mode = aburi::frontend::PreprocessOutputMode::TextNoLineMarkers;
        }

        std::ostringstream discard;
        std::ostream& pp_out = base_opts.depfile.generate_only ? discard : *out;
        std::shared_ptr<SourceManager> sm =
            aburi::frontend::run_preprocessor(std::move(invocation), mode, pp_out);
        if (base_opts.depfile.enabled && sm != nullptr &&
            !write_depfile(base_opts, path, *sm)) {
            return 1;
        }
        return sm != nullptr ? 0 : 1;
    }

    if (base_opts.jit) {
        aburi::frontend::JitRunResult jit_result =
            aburi::frontend::run_jit(std::move(invocation));
        print_frontend_failures(jit_result.frontend);
        for (const std::string& diagnostic : jit_result.diagnostics) {
            std::cerr << diagnostic << '\n';
        }
        return jit_result.ok() ? jit_result.exit_code : 1;
    }

    aburi::frontend::FrontendResult local_frontend;
    aburi::frontend::FrontendResult* frontend_storage = nullptr;
    if (module_session && module_session->owns_path(path)) {
        frontend_storage = module_session->result_for_path(path);
    }
    if (frontend_storage == nullptr) {
        local_frontend = aburi::frontend::run_frontend(std::move(invocation));
        frontend_storage = &local_frontend;
    }
    aburi::frontend::FrontendResult& frontend = *frontend_storage;
    print_frontend_failures(frontend);
    bool failed = !frontend.ok();

    if (!failed && module_session &&
        (base_opts.precompile_only || base_opts.module_output)) {
        LangOptions file_opts = options_for_file(base_opts.lang_opts, path);
        std::string source_bytes = read_file(path);
        aburi::modules::ModuleScanResult scan =
            aburi::modules::scan_module_directives(source_bytes, file_opts);
        if (scan.is_interface_unit()) {
            aburi::modules::LoadedModuleUnit unit;
            unit.kind = scan.kind;
            unit.module_name = scan.module_name;
            unit.partition_name = scan.partition_name;
            unit.tokens = &frontend.tokens;
            unit.source_manager = frontend.source_manager;

            unit.cir = &frontend.cir;
            unit.template_state = frontend.template_state;
            std::string bytes = aburi::serialize::write_module_artifact(
                unit, *frontend.source_manager,
                module_session->compat_identity());
            std::string artifact_path;
            if (base_opts.precompile_only && !base_opts.output_path.empty()) {
                artifact_path = base_opts.output_path;
            } else {
                artifact_path = path;
                size_t dot = artifact_path.rfind('.');
                if (dot != std::string::npos) {
                    artifact_path.resize(dot);
                }
                artifact_path += ".abmi";
            }
            std::ofstream artifact(artifact_path, std::ios::binary);
            artifact.write(bytes.data(),
                           static_cast<std::streamsize>(bytes.size()));
            if (!artifact) {
                std::cerr << "aburi: error: cannot write module artifact '"
                          << artifact_path << "'\n";
                failed = true;
            }
        } else if (base_opts.precompile_only) {
            std::cerr << "aburi: error: --precompile requires a module "
                         "interface unit, but '"
                      << path << "' is not one\n";
            failed = true;
        }
    }
    if (base_opts.precompile_only) {
        return failed ? 1 : 0;
    }

    if (base_opts.dump_syntax && !base_opts.emit_llvm) {
        frontend.parse_result.tree.dump(*out, frontend.tokens);
    }
    if (base_opts.dump_cir && !base_opts.emit_llvm) {
        frontend.cir.dump(*out);
    }
    if (base_opts.dump_air && !failed) {
        aburi::cir2air::AirLoweringOptions lowering_options;
        lowering_options.target = frontend.cir.target_info_ptr();
        lowering_options.module_name = path;
        lowering_options.cxx_mangling =
            options_for_file(base_opts.lang_opts, path).is_cxx_mode();
        aburi::cir2air::AirLoweringResult air_result =
            aburi::cir2air::lower_cir_to_air(frontend.cir,
                                             std::move(lowering_options));
        print_lowering_diagnostics(frontend.source_manager, air_result.diagnostics);
        if (!air_result.ok()) {
            failed = true;
        } else {
            aburi::air::VerifyResult verify =
                aburi::air::verify_module(*air_result.module);
            if (!verify.ok()) {
                std::cerr << "aburi: error: air verifier rejected cir2air output:\n"
                          << verify.to_string() << '\n';
                failed = true;
            } else {
                if (base_opts.opt_level >= 1) {
                    aburi::air::PipelineResult piped =
                        aburi::air::run_o1_pipeline(*air_result.module);
                    if (!piped.verified) {
                        std::cerr << "aburi: error: air pass pipeline broke "
                                  << "the module: " << piped.verify_error << '\n';
                        failed = true;
                    }
                }
                if (!failed) {
                    *out << aburi::air::print_module(*air_result.module);
                }
            }
        }
    }

    if (base_opts.emit_llvm) {
        if (!failed) {
            PerfScopedTimer timer(active_perf_profiler(), PerfPhase::EmitLlvm);
            aburi::cir2llvm::LoweringOptions lowering_options;
            lowering_options.target = frontend.cir.target_info_ptr();
            lowering_options.module_name = path;
            lowering_options.cxx_mangling =
                options_for_file(base_opts.lang_opts, path).is_cxx_mode();
            lowering_options.objc = options_for_file(base_opts.lang_opts, path).is_objc();
            lowering_options.branch_target_enforcement =
                base_opts.branch_target_enforcement;
            lowering_options.sign_return_address = base_opts.sign_return_address;
            lowering_options.keep_frame_pointer = base_opts.keep_frame_pointer;
            lowering_options.fcommon = base_opts.fcommon;
            std::vector<Diagnostic> lowering_diagnostics;
            if (!aburi::cir2llvm::write_llvm_ir(
                    frontend.cir, std::move(lowering_options), *out, &lowering_diagnostics)) {
                print_lowering_diagnostics(frontend.source_manager, lowering_diagnostics);
                failed = true;
            }
        }
    } else if (base_opts.emit_assembly || base_opts.compile_only || link_state != nullptr) {
        if (!failed && base_opts.backend == "air") {
            if (link_state == nullptr && multi_input && !base_opts.output_path.empty()) {
                throw std::runtime_error(
                    "-o cannot be used with multiple inputs in this driver");
            }
            failed = run_air_native_output(base_opts, path, frontend,
                                           link_state) != 0;
        } else if (!failed) {
            if (link_state == nullptr && multi_input && !base_opts.output_path.empty()) {
                throw std::runtime_error(
                    "-o cannot be used with multiple inputs in this driver");
            }
            PerfScopedTimer timer(active_perf_profiler(),
                base_opts.emit_assembly ? PerfPhase::EmitAssembly
                                        : PerfPhase::EmitObject);
            aburi::cir2llvm::TargetOutputOptions output_options;
            output_options.target = frontend.cir.target_info_ptr();
            output_options.module_name = path;
            output_options.cxx_mangling =
                options_for_file(base_opts.lang_opts, path).is_cxx_mode();
            output_options.objc = options_for_file(base_opts.lang_opts, path).is_objc();
            output_options.opt_level = base_opts.opt_level;
            output_options.pic = base_opts.pic;
            output_options.features = codegen_feature_string(base_opts);
            output_options.branch_target_enforcement =
                base_opts.branch_target_enforcement;
            output_options.sign_return_address = base_opts.sign_return_address;
            output_options.keep_frame_pointer = base_opts.keep_frame_pointer;
            output_options.fcommon = base_opts.fcommon;
            output_options.freestanding = base_opts.freestanding;
            output_options.kind = base_opts.emit_assembly
                ? aburi::cir2llvm::OutputKind::Assembly
                : aburi::cir2llvm::OutputKind::Object;
            output_options.output_path = link_state
                ? temporary_object_path(*link_state, std::filesystem::path(path))
                : derived_target_output_path(
                      base_opts, path, base_opts.emit_assembly ? ".s" : ".o");
            aburi::cir2llvm::TargetOutputResult output_result =
                aburi::cir2llvm::emit_target_output(frontend.cir, output_options);
            print_lowering_diagnostics(frontend.source_manager, output_result.diagnostics);
            if (!output_result.ok()) {
                failed = true;
            } else if (link_state != nullptr) {
                link_state->object_files.push_back(output_options.output_path);
            }
        }
    }

    if (!failed && base_opts.depfile.enabled &&
        frontend.source_manager != nullptr &&
        !write_depfile(base_opts, path, *frontend.source_manager)) {
        failed = true;
    }

    return failed ? 1 : 0;
}

void pin_assembler_input_language(std::vector<std::string>& args,
                                  const std::filesystem::path& input_path) {
    const std::string real_ext =
        to_lower_ascii(input_path.extension().string());
    if (real_ext != ".s") {
        return;
    }
    const bool needs_cpp = input_path.extension().string() != ".s";
    args.push_back("-x");
    args.push_back(needs_cpp ? "assembler-with-cpp" : "assembler");
}

int run_assembler_source(const DriverOptions& opts,
                         const std::string& path,
                         LinkState* link_state) {
    std::string source;
    try {
        source = read_file(path);
    } catch (const std::exception& ex) {
        std::cerr << "aburi: error: " << ex.what() << '\n';
        return 1;
    }
    aburi::assembler::AsmOptions asm_options;
    asm_options.target = effective_target_info(opts);
    asm_options.filename = path;
    std::ostringstream object_bytes;
    aburi::assembler::AssembleResult assembled =
        aburi::assembler::assemble_string_to_object(source, asm_options,
                                                    object_bytes);
    for (const Diagnostic& diag : assembled.diagnostics) {
        std::cerr << "aburi: error: " << diag.message << '\n';
    }
    if (!assembled.ok) {
        return 1;
    }
    std::string object_path = link_state
        ? temporary_object_path(*link_state, std::filesystem::path(path))
        : derived_target_output_path(opts, path, ".o");
    std::ofstream out(object_path, std::ios::binary);
    if (!out) {
        std::cerr << "aburi: error: cannot write " << object_path << '\n';
        return 1;
    }
    out << object_bytes.str();
    if (!out.good()) {
        std::cerr << "aburi: error: cannot write " << object_path << '\n';
        return 1;
    }
    if (link_state != nullptr) {
        link_state->object_files.push_back(object_path);
    }
    return 0;
}

int run_passthrough_source(const DriverOptions& opts,
                           const std::string& path,
                           bool multi_input,
                           LinkState* link_state,
                           const char* argv0) {
    std::filesystem::path input_path(path);
    const std::string ext = input_extension(input_path);
    const bool as_cxx = file_selects_cxx_linker(opts, input_path);
    const std::string compiler = target_is_linux(opts)
        ? cross_compiler_path(opts, as_cxx)
        : (as_cxx ? "/usr/bin/c++" : "/usr/bin/cc");
    std::vector<std::string> args = passthrough_compile_flags(opts, argv0);

    if (opts.dump_syntax || opts.dump_cir || opts.dump_air) {
        std::cerr << "aburi: error: cannot dump frontend output for "
                  << "passthrough source kind '" << ext << "' in " << path << '\n';
        return 1;
    }
    if (opts.preprocess_only) {

        if (!opts.depfile.generate_only) {
            args.push_back("-E");
        }
        pin_assembler_input_language(args, input_path);
        args.push_back(path);
        if (!opts.output_path.empty() && !multi_input &&
            !opts.depfile.generate_only) {
            args.push_back("-o");
            args.push_back(opts.output_path);
        }
        return run_command(compiler, args);
    }
    if (opts.syntax_only) {
        args.push_back("-fsyntax-only");
        pin_assembler_input_language(args, input_path);
        args.push_back(path);
        return run_command(compiler, args);
    }
    if (opts.emit_llvm) {
        std::cerr << "aburi: error: --emit-llvm is not supported for "
                  << "passthrough source kind '" << ext << "' in " << path << '\n';
        return 1;
    }

    if (opts.emit_assembly) {
        std::string asm_output = !opts.output_path.empty() && !multi_input
            ? opts.output_path
            : input_path.stem().string() + ".s";
        args.push_back("-S");
        pin_assembler_input_language(args, input_path);
        args.push_back(path);
        args.push_back("-o");
        args.push_back(asm_output);
        return run_command(compiler, args);
    }

    std::string object_output;
    if (link_state != nullptr) {
        object_output = temporary_object_path(*link_state, input_path);
    } else if (opts.compile_only && !opts.output_path.empty() && !multi_input) {
        object_output = opts.output_path;
    } else {
        object_output = input_path.stem().string() + ".o";
    }

    args.push_back("-c");
    pin_assembler_input_language(args, input_path);
    args.push_back(path);
    args.push_back("-o");
    args.push_back(object_output);
    int result = run_command(compiler, args);
    if (result == 0 && link_state != nullptr) {
        link_state->object_files.push_back(object_output);
    }
    return result;
}

int run_final_link(const DriverOptions& opts,
                   LinkState& link_state,
                   const char* argv0) {
    const AdinkraLinkPlan adinkra =
        plan_adinkra_link(opts, link_state.link_as_cxx, argv0);
    if (!adinkra.error.empty()) {
        std::cerr << adinkra.error << '\n';
        return 1;
    }
    std::vector<std::string> args =
        linker_driver_flags(opts, link_state.link_as_cxx, adinkra);
    std::string linker;
    if (target_is_cross_elf(opts)) {

        if (primary_target_sysroot(opts).empty()) {
            std::cerr << "aburi: error: linking for a Linux or FreeBSD target "
                      << "requires a sysroot (pass --sysroot or set "
                      << "ABURI_LINUX_SYSROOT)\n";
            return 1;
        }
        linker = cross_compiler_path(opts, link_state.link_as_cxx);
        if (cross_compiler_is_clang(linker)) {
            // Honor an explicit linker path; otherwise select the default ELF
            // linker by name.
            if (!opts.ld_path.empty()) {
                args.push_back("--ld-path=" + opts.ld_path);
            } else {
                args.push_back("-fuse-ld=lld");
            }
        }
    } else {
        linker = link_state.link_as_cxx ? "/usr/bin/c++" : "/usr/bin/cc";
    }
    args.insert(args.end(), link_state.object_files.begin(), link_state.object_files.end());
    args.insert(args.end(),
        link_state.linker_input_files.begin(),
        link_state.linker_input_files.end());
    args.insert(args.end(), opts.linker_flags.begin(), opts.linker_flags.end());
    // The archive follows every user input so static resolution can satisfy
    // their references to it.
    if (adinkra.active) {
        args.push_back(adinkra.library);
        if (!adinkra.rpath_dir.empty()) {
            args.push_back("-Wl,-rpath," + adinkra.rpath_dir);
        }
    }
    bool linked_cxxabi = false;
    if (link_state.link_objc_runtime) {
        args.push_back("-lobjc");

        args.push_back("-lc++abi");
        linked_cxxabi = true;
    }
    // we use libc++abi from clang
    if (adinkra.active && !linked_cxxabi) {
        args.push_back("-lc++abi");
    }
    args.push_back("-o");
    args.push_back(opts.output_path.empty() ? "a.out" : opts.output_path);

    PerfScopedTimer timer(active_perf_profiler(), PerfPhase::Link);
    return run_command(linker, args);
}

int run_inputs(const DriverOptions& opts, const char* argv0) {
    const bool link_mode = is_final_link_mode(opts);
    const bool multi_input = opts.input_files.size() > 1;
    LinkState link_state;
    int exit_code = 0;

    std::unique_ptr<aburi::modules::ModuleBuildSession> module_session;
    auto ensure_module_session = [&]() {
        if (module_session) {
            return;
        }
        module_session =
            std::make_unique<aburi::modules::ModuleBuildSession>(
                [&opts, argv0](const std::string& path,
                               aburi::modules::ModuleLoader* loader) {
                    aburi::frontend::FrontendInvocation invocation =
                        make_invocation(opts, path, read_file(path), argv0);
                    invocation.module_loader = loader;

                    invocation.export_template_state = true;
                    return aburi::frontend::run_frontend(
                        std::move(invocation));
                });
        LangOptions module_lang =
            options_for_file(opts.lang_opts, "module.cppm");
        module_session->set_target_info(effective_target_info(opts));
        module_session->set_compat_identity(
            aburi::serialize::CompatIdentity::build(
                aburi::driver::kAburiVersionString,
                effective_target_info(opts)->triple,
                module_lang,
                opts.defines,
                opts.undefines));
    };
    if (!opts.module_files.empty() || !opts.prebuilt_module_paths.empty()) {
        ensure_module_session();
        for (const auto& [name, path] : opts.module_files) {
            module_session->register_module_artifact(name, path);
        }
        for (const std::string& directory : opts.prebuilt_module_paths) {
            module_session->add_prebuilt_module_path(directory);
        }
    }
    if (!opts.preprocess_only) {
        for (const std::string& input_filename : opts.input_files) {
            if (is_stdin_input(input_filename)) {
                continue;
            }
            std::filesystem::path input_path(input_filename);
            if (!std::filesystem::exists(input_path) ||
                !is_frontend_source(opts, input_path)) {
                continue;
            }
            LangOptions file_opts =
                options_for_file(opts.lang_opts, input_filename);
            if (!file_opts.is_cxx_mode() || !file_opts.modules_enabled()) {
                continue;
            }
            aburi::modules::ModuleScanResult scan =
                aburi::modules::scan_module_directives(
                    read_file(input_filename), file_opts);
            if (!scan.is_module_unit() && scan.imports.empty()) {
                continue;
            }
            ensure_module_session();
            if (scan.is_module_unit()) {
                std::string conflict = module_session->register_module_source(
                    scan, input_filename);
                if (!conflict.empty()) {
                    std::cerr << "aburi: error: " << conflict << '\n';
                    exit_code = 1;
                }
            }
        }
    }

    bool saw_source_input = false;
    for (const std::string& input_filename : opts.input_files) {
        std::filesystem::path input_path(input_filename);
        if (!is_stdin_input(input_filename) &&
            !std::filesystem::exists(input_path)) {
            std::cerr << "aburi: error: file not found: " << input_filename << '\n';
            exit_code = 1;
            continue;
        }

        const std::string ext = input_extension(input_path);
        if (is_linker_input_extension(ext)) {
            if (link_mode) {
                link_state.linker_input_files.push_back(input_filename);
            }
            continue;
        }

        saw_source_input = true;
        if (is_frontend_source(opts, input_path)) {
            if (file_selects_cxx_linker(opts, input_path)) {
                link_state.link_as_cxx = true;
            }
            if (options_for_file(opts.lang_opts, input_filename).is_objc()) {
                link_state.link_objc_runtime = true;
            }
            try {
                exit_code |= run_file(opts,
                    module_session.get(),
                    input_filename,
                    multi_input,
                    argv0,
                    link_mode ? &link_state : nullptr);
            } catch (const std::exception& ex) {
                std::cerr << "aburi: error: " << ex.what() << '\n';
                exit_code = 1;
            }
            continue;
        }

        if (!is_passthrough_source_extension(opts, ext) &&
            !opts.assembler_language) {
            std::cerr << "aburi: error: unsupported source file kind for "
                      << input_filename << " (extension '" << ext << "')\n";
            exit_code = 1;
            continue;
        }
        if (file_selects_cxx_linker(opts, input_path)) {
            link_state.link_as_cxx = true;
        }
        if (options_for_file(opts.lang_opts, input_filename).is_objc()) {
            link_state.link_objc_runtime = true;
        }

        std::shared_ptr<TargetInfo> asm_target = effective_target_info(opts);
        const bool plain_assembler_input =
            input_path.extension() == ".s" ||
            (opts.assembler_language && !opts.assembler_with_cpp);
        bool integrated_asm_input =
            plain_assembler_input &&
            opts.integrated_as && opts.assembler_flags.empty() &&
            (opts.compile_only || link_mode) &&
            integrated_assembler_supports(asm_target);
        if (integrated_asm_input) {
            exit_code |= run_assembler_source(
                opts, input_filename, link_mode ? &link_state : nullptr);
            continue;
        }
        exit_code |= run_passthrough_source(opts,
            input_filename,
            multi_input,
            link_mode ? &link_state : nullptr,
            argv0);
    }

    // A link with no sources cannot tell C++ objects from C ones by extension.
    // Naming a C++ standard library is the user saying which one this is; without
    // it such a link silently used the C driver and failed on the C++ runtime.
    if (link_mode && !saw_source_input && !link_state.link_as_cxx &&
        opts.requested_stdlib != StdLibKind::Auto) {
        link_state.link_as_cxx = true;
    }

    if (exit_code == 0 && link_mode) {
        exit_code = run_final_link(opts, link_state, argv0);
    }
    cleanup_temp_objects(link_state);
    return exit_code;
}

int run_cir_example(const std::string& name) {
    auto example = aburi::cir::build_example(name);
    if (!example.has_value()) {
        std::cerr << "aburi: error: unknown CIR example '" << name << "'\n";
        std::cerr << "available examples:";
        for (const std::string& example_name : aburi::cir::example_names()) {
            std::cerr << ' ' << example_name;
        }
        std::cerr << '\n';
        return 1;
    }
    if (!example->verify(&std::cerr)) {
        return 1;
    }
    example->dump(std::cout);
    return 0;
}

} // namespace

int main(int argc, char** argv) {
    DriverOptions opts;
    if (!aburi::driver::parse_driver_options(argc, argv, opts)) {
        return 1;
    }
    if (target_is_linux(opts) && opts.sysroots.empty()) {

        if (const char* env = std::getenv("ABURI_LINUX_SYSROOT")) {
            opts.sysroots.push_back(env);
        }
    }
    if (opts.show_help) {
        aburi::driver::print_driver_help(std::cout);
        return 0;
    }
    if (opts.early_query != aburi::driver::EarlyDriverQuery::None) {
        return handle_early_driver_query(opts, argc > 0 ? argv[0] : nullptr);
    }
    if (!validate_driver_options(opts)) {
        return 1;
    }
    if (!require_adinkra_when_requested(opts, argc > 0 ? argv[0] : nullptr)) {
        return 1;
    }
    if (!opts.dump_cir_example.empty()) {
        return run_cir_example(opts.dump_cir_example);
    }
    if (opts.input_files.empty()) {

        if (is_final_link_mode(opts) && !opts.linker_flags.empty()) {
            LinkState link_state;
            return run_final_link(opts, link_state, argc > 0 ? argv[0] : nullptr);
        }
        std::cerr << "aburi: error: no input files\n";
        return 1;
    }

    std::optional<PerfProfiler> profiler;
    if (opts.perf_detail.has_value()) {
        profiler.emplace(*opts.perf_detail);
        set_active_perf_profiler(&*profiler);
    }

    int exit_code;
    {
        PerfScopedTimer timer(active_perf_profiler(), PerfPhase::Driver);
        exit_code = run_inputs(opts, argc > 0 ? argv[0] : nullptr);
    }

    if (profiler.has_value()) {
        set_active_perf_profiler(nullptr);
        profiler->print_text_report(std::cerr);
        if (!opts.perf_json_path.empty()) {
            std::string error;
            if (!profiler->write_json_report(opts.perf_json_path, error)) {
                std::cerr << "aburi: error: " << error << '\n';
                exit_code = exit_code == 0 ? 1 : exit_code;
            }
        }
    }
    return exit_code;
}
