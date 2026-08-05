#include "toolchain_profile.h"

#include "abi/target_info.h"

#include <algorithm>
#include <cctype>
#include <cstdlib>
#include <filesystem>
#include <initializer_list>
#include <string>
#include <unordered_map>
#include <unordered_set>

namespace {

std::string to_lower_ascii(std::string_view value) {
    std::string lowered(value);
    std::transform(lowered.begin(), lowered.end(), lowered.begin(),
        [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
    return lowered;
}

std::string normalize_candidate_path(const std::filesystem::path& path) {
    std::error_code ec;
    auto normalized = std::filesystem::weakly_canonical(path, ec);
    if (!ec) {
        return normalized.string();
    }
    return path.lexically_normal().string();
}
std::filesystem::path resolve_argv0_path(const char* argv0) {
    const std::filesystem::path given(argv0);
    if (given.has_parent_path()) {
        return given;
    }
    const char* path_env = std::getenv("PATH");
    if (path_env == nullptr) {
        return given;
    }
    std::string_view remaining(path_env);
    while (!remaining.empty()) {
        const size_t separator = remaining.find(':');
        const std::string_view entry = remaining.substr(0, separator);
        remaining = separator == std::string_view::npos
            ? std::string_view()
            : remaining.substr(separator + 1);
        if (entry.empty()) {
            continue;
        }
        const std::filesystem::path candidate =
            std::filesystem::path(entry) / given;
        std::error_code ec;
        if (std::filesystem::exists(candidate, ec) &&
            !std::filesystem::is_directory(candidate, ec)) {
            return candidate;
        }
    }
    return given;
}

std::filesystem::path resolve_installed_dir(const char* argv0) {
    if (argv0 == nullptr || *argv0 == '\0') {
        return std::filesystem::path(".");
    }
    const std::filesystem::path located = resolve_argv0_path(argv0);
    std::error_code ec;
    auto absolute_path = std::filesystem::absolute(located, ec);
    if (ec) {
        absolute_path = located;
    }
    auto parent = absolute_path.lexically_normal().parent_path();
    if (parent.empty()) {
        return std::filesystem::path(".");
    }
    return parent;
}

void maybe_record_candidate(const std::filesystem::path& candidate,
                            std::vector<std::string>& attempted_paths,
                            std::unordered_set<std::string>& attempted_seen,
                            std::vector<std::string>& include_paths,
                            std::unordered_set<std::string>& include_seen) {
    if (candidate.empty()) {
        return;
    }
    const std::string normalized = normalize_candidate_path(candidate);
    if (attempted_seen.insert(normalized).second) {
        attempted_paths.push_back(normalized);
    }
    std::error_code ec;
    if (!std::filesystem::exists(candidate, ec) ||
        !std::filesystem::is_directory(candidate, ec)) {
        return;
    }
    if (include_seen.insert(normalized).second) {
        include_paths.push_back(normalized);
    }
}

void add_latest_darwin_sdk_candidate(const std::filesystem::path& sdk_dir,
                                     std::vector<std::string>& attempted_paths,
                                     std::unordered_set<std::string>& attempted_seen,
                                     std::vector<std::string>& include_paths,
                                     std::unordered_set<std::string>& include_seen) {
    std::error_code ec;
    if (!std::filesystem::exists(sdk_dir, ec) || !std::filesystem::is_directory(sdk_dir, ec)) {
        return;
    }

    const std::filesystem::path default_sdk = sdk_dir / "MacOSX.sdk";
    if (std::filesystem::exists(default_sdk, ec)) {
        maybe_record_candidate(default_sdk / "usr" / "include" / "c++" / "v1",
            attempted_paths, attempted_seen, include_paths, include_seen);
        return;
    }

    std::vector<std::filesystem::path> candidates;
    for (const auto& entry : std::filesystem::directory_iterator(sdk_dir, ec)) {
        if (ec) {
            break;
        }
        if (!entry.is_directory(ec)) {
            continue;
        }
        auto path = entry.path();
        const std::string name = path.filename().string();
        if (name.rfind("MacOSX", 0) == 0 && path.extension() == ".sdk") {
            candidates.push_back(path);
        }
    }
    if (candidates.empty()) {
        return;
    }

    std::sort(candidates.begin(), candidates.end());
    maybe_record_candidate(candidates.back() / "usr" / "include" / "c++" / "v1",
        attempted_paths, attempted_seen, include_paths, include_seen);
}

void add_darwin_libcxx_candidates(const char* argv0,
                                  const std::vector<std::string>& sysroots,
                                  std::vector<std::string>& attempted_paths,
                                  std::unordered_set<std::string>& attempted_seen,
                                  std::vector<std::string>& include_paths,
                                  std::unordered_set<std::string>& include_seen) {
    const std::filesystem::path installed_dir = resolve_installed_dir(argv0);
    maybe_record_candidate(installed_dir.parent_path() / "include" / "c++" / "v1",
        attempted_paths, attempted_seen, include_paths, include_seen);
    maybe_record_candidate(installed_dir / "include" / "c++" / "v1",
        attempted_paths, attempted_seen, include_paths, include_seen);

    if (const char* sdkroot = std::getenv("SDKROOT")) {
        maybe_record_candidate(std::filesystem::path(sdkroot) / "usr" / "include" / "c++" / "v1",
            attempted_paths, attempted_seen, include_paths, include_seen);
    }
    for (const auto& sysroot : sysroots) {
        maybe_record_candidate(std::filesystem::path(sysroot) / "usr" / "include" / "c++" / "v1",
            attempted_paths, attempted_seen, include_paths, include_seen);
    }
    add_latest_darwin_sdk_candidate("/Library/Developer/CommandLineTools/SDKs",
        attempted_paths, attempted_seen, include_paths, include_seen);
    add_latest_darwin_sdk_candidate(
        "/Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs",
        attempted_paths,
        attempted_seen,
        include_paths,
        include_seen);

    maybe_record_candidate("/Library/Developer/CommandLineTools/usr/include/c++/v1",
        attempted_paths, attempted_seen, include_paths, include_seen);
    maybe_record_candidate(
        "/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/include/c++/v1",
        attempted_paths,
        attempted_seen,
        include_paths,
        include_seen);
}

bool try_add_include_path(const std::filesystem::path& path,
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

void add_sdk_include_from_root(const std::filesystem::path& sdk_root,
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
    (void)try_add_include_path(sdk_root / "usr" / "include", paths, seen);
    std::filesystem::path frameworks_root = sdk_root / "System" / "Library" / "Frameworks";
    std::filesystem::path private_frameworks_root =
        sdk_root / "System" / "Library" / "PrivateFrameworks";
    (void)try_add_include_path(frameworks_root, paths, seen);
    (void)try_add_include_path(private_frameworks_root, paths, seen);
    add_subframework_roots(frameworks_root);
    add_subframework_roots(private_frameworks_root);
}

void add_sdk_from_dir(const std::filesystem::path& sdk_dir,
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
        auto path = entry.path();
        const std::string name = path.filename().string();
        if (name.rfind("MacOSX", 0) == 0 && path.extension() == ".sdk") {
            candidates.push_back(path);
        }
    }
    if (candidates.empty()) {
        return;
    }
    std::sort(candidates.begin(), candidates.end());
    add_sdk_include_from_root(candidates.back(), paths, seen);
}

void discover_clang_resource_includes(std::vector<std::string>& paths,
                                      std::unordered_set<std::string>& seen) {
    const std::filesystem::path bases[] = {
        "/Library/Developer/CommandLineTools/usr/lib/clang",
        "/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/lib/clang",
    };
    for (const auto& base : bases) {
        std::error_code ec;
        if (!std::filesystem::exists(base, ec) || !std::filesystem::is_directory(base, ec)) {
            continue;
        }
        std::vector<std::filesystem::path> versions;
        for (const auto& entry : std::filesystem::directory_iterator(base, ec)) {
            if (ec) break;
            if (!entry.is_directory(ec)) continue;
            auto include_dir = entry.path() / "include";
            if (std::filesystem::exists(include_dir, ec)) {
                versions.push_back(include_dir);
            }
        }
        if (!versions.empty()) {
            std::sort(versions.begin(), versions.end());
            (void)try_add_include_path(versions.back(), paths, seen);
            return;
        }
    }
}

std::string linux_multiarch_name(std::string_view triple) {

    const std::string lowered = to_lower_ascii(triple);
    if (lowered.find("aarch64") != std::string::npos ||
        lowered.find("arm64") != std::string::npos) {
        return "aarch64-linux-gnu";
    }
    if (lowered.find("x86_64") != std::string::npos ||
        lowered.find("amd64") != std::string::npos) {
        return "x86_64-linux-gnu";
    }
    return {};
}
std::vector<std::string> effective_linux_sysroots(
    const std::vector<std::string>& sysroots) {
#if defined(__linux__)
    if (sysroots.empty()) {
        return {"/"};
    }
#endif
    return sysroots;
}

std::filesystem::path latest_version_subdir(const std::filesystem::path& base) {
    std::error_code ec;
    if (!std::filesystem::exists(base, ec) ||
        !std::filesystem::is_directory(base, ec)) {
        return {};
    }
    std::filesystem::path best;
    long best_version = -1;
    for (const auto& entry : std::filesystem::directory_iterator(base, ec)) {
        if (ec) break;
        if (!entry.is_directory(ec)) continue;
        const std::string name = entry.path().filename().string();

        char* end = nullptr;
        long version = std::strtol(name.c_str(), &end, 10);
        if (end == name.c_str()) continue;
        if (version > best_version) {
            best_version = version;
            best = entry.path();
        }
    }
    return best;
}

void add_linux_libstdcxx_candidates(const std::vector<std::string>& sysroots,
                                    std::string_view multiarch,
                                    std::vector<std::string>& attempted_paths,
                                    std::unordered_set<std::string>& attempted_seen,
                                    std::vector<std::string>& include_paths,
                                    std::unordered_set<std::string>& include_seen) {
    for (const auto& sysroot : sysroots) {
        const std::filesystem::path base =
            std::filesystem::path(sysroot) / "usr" / "include" / "c++";
        const std::filesystem::path versioned = latest_version_subdir(base);
        if (versioned.empty()) {
            maybe_record_candidate(base, attempted_paths, attempted_seen,
                                   include_paths, include_seen);
            continue;
        }
        const std::string version = versioned.filename().string();
        maybe_record_candidate(versioned, attempted_paths, attempted_seen,
                               include_paths, include_seen);
        if (!multiarch.empty()) {
            maybe_record_candidate(std::filesystem::path(sysroot) / "usr" /
                                       "include" / multiarch / "c++" / version,
                                   attempted_paths, attempted_seen,
                                   include_paths, include_seen);
        }
        maybe_record_candidate(versioned / "backward", attempted_paths,
                               attempted_seen, include_paths, include_seen);
    }
}

// One Adinkra prefix, in the two layouts the project produces: an installed
// tree (adinkra/CMakeLists.txt installs headers under include/adinkra/c++/v1)
// and a build tree next to the compiler.
struct AdinkraCandidate {
    std::filesystem::path include_dir;
    std::filesystem::path library_dir;
    bool from_build_tree = false;
};

void collect_adinkra_candidates(const char* argv0,
                                const std::string& root_override,
                                std::vector<AdinkraCandidate>& candidates) {
    auto add_install_layout = [&candidates](const std::filesystem::path& prefix,
                                            bool from_build_tree) {
        candidates.push_back({prefix / "include" / "adinkra" / "c++" / "v1",
            prefix / "lib", from_build_tree});
    };
    auto add_source_layout = [&candidates](const std::filesystem::path& source_root,
                                           const std::filesystem::path& library_dir,
                                           bool from_build_tree) {
        candidates.push_back({source_root / "include" / "c++" / "v1",
            library_dir, from_build_tree});
    };
    std::string explicit_root = root_override;
    if (explicit_root.empty()) {
        if (const char* env = std::getenv("ABURI_ADINKRA_ROOT")) {
            explicit_root = env;
        }
    }
    if (!explicit_root.empty()) {
        const std::filesystem::path root(explicit_root);
        add_install_layout(root, false);
        add_source_layout(root, root, false);
        add_source_layout(root / "adinkra", root / "adinkra", false);
        return;
    }

    const std::filesystem::path installed_dir = resolve_installed_dir(argv0);

    // Installed compiler: <prefix>/bin/aburi alongside <prefix>/include|lib.
    add_install_layout(installed_dir.parent_path(), false);
    add_install_layout(installed_dir, false);

    // Build tree: the compiler sits in a build directory inside the checkout,
    // so the headers come from the source tree while the archive is built
    // beside the compiler.
    add_source_layout(installed_dir.parent_path() / "adinkra",
        installed_dir / "adinkra", true);
    add_source_layout(installed_dir.parent_path().parent_path() / "adinkra",
        installed_dir / "adinkra", true);
}

std::string first_existing_library(const std::filesystem::path& directory,
                                   std::initializer_list<const char*> names) {
    for (const char* name : names) {
        const std::filesystem::path candidate = directory / name;
        std::error_code ec;
        if (std::filesystem::exists(candidate, ec) &&
            !std::filesystem::is_directory(candidate, ec)) {
            return normalize_candidate_path(candidate);
        }
    }
    return {};
}

AdinkraLayout compute_adinkra_layout(const char* argv0,
                                     const std::string& root_override) {
    AdinkraLayout layout;
    std::vector<AdinkraCandidate> candidates;
    collect_adinkra_candidates(argv0, root_override, candidates);

    std::unordered_set<std::string> attempted_seen;
    for (const AdinkraCandidate& candidate : candidates) {
        const std::string normalized = normalize_candidate_path(candidate.include_dir);
        if (attempted_seen.insert(normalized).second) {
            layout.attempted_roots.push_back(normalized);
        }
        if (layout.found) {
            continue;
        }
        std::error_code ec;
        if (!std::filesystem::exists(candidate.include_dir, ec) ||
            !std::filesystem::is_directory(candidate.include_dir, ec)) {
            continue;
        }

        layout.found = true;
        layout.include_dir = normalized;
        layout.root = normalize_candidate_path(candidate.library_dir);
        layout.from_build_tree = candidate.from_build_tree;
        // The libraries are optional: -fsyntax-only and -c need headers alone,
        // and a headers-only checkout must not become a hard error.
        layout.static_library =
            first_existing_library(candidate.library_dir, {"libadinkra.a"});
        layout.shared_library = first_existing_library(candidate.library_dir,
            {"libadinkra.dylib", "libadinkra.so"});
        if (!layout.shared_library.empty()) {
            layout.shared_library_dir =
                normalize_candidate_path(candidate.library_dir);
        }
    }
    return layout;
}

constexpr bool kAdinkraIsAutomatic = true;

std::string triple_architecture(std::string_view triple) {
    const std::string lowered = to_lower_ascii(triple);
    const size_t separator = lowered.find('-');
    std::string arch =
        separator == std::string::npos ? lowered : lowered.substr(0, separator);
    // Apple spells the same architecture both ways depending on the tool.
    if (arch == "arm64") {
        return "aarch64";
    }
    return arch;
}

void discover_aburi_builtin_includes(const char* argv0,
                                     std::vector<std::string>& paths,
                                     std::unordered_set<std::string>& seen) {
    std::filesystem::path installed_dir = resolve_installed_dir(argv0);
    const std::filesystem::path candidates[] = {
        installed_dir / "builtin_headers",
        // Build tree: the compiler sits in a build directory in the checkout.
        installed_dir.parent_path() / "builtin_headers",
        // Install prefix: <prefix>/bin/aburi beside <prefix>/lib/aburi.
        installed_dir.parent_path() / "lib" / "aburi" / "builtin_headers",
    };
    for (const auto& candidate : candidates) {
        std::error_code ec;
        if (!std::filesystem::exists(candidate, ec) ||
            !std::filesystem::is_directory(candidate, ec)) {
            continue;
        }
        (void)try_add_include_path(candidate, paths, seen);
        return;
    }
}

} // namespace

TargetOS target_os_from_triple(std::string_view triple) {
    const std::string lowered = to_lower_ascii(triple);
    if (lowered.empty()) {
        return TargetInfo::create_host()->os;
    }
    if (lowered.find("darwin") != std::string::npos ||
        lowered.find("apple") != std::string::npos ||
        lowered.find("macos") != std::string::npos) {
        return TargetOS::MACOS;
    }
    if (lowered.find("linux") != std::string::npos) {
        return TargetOS::LINUX;
    }
    if (lowered.find("windows") != std::string::npos ||
        lowered.find("mingw") != std::string::npos ||
        lowered.find("msvc") != std::string::npos) {
        return TargetOS::WINDOWS;
    }
    if (lowered.find("freebsd") != std::string::npos) {
        return TargetOS::FREEBSD;
    }
    if (lowered.find("netbsd") != std::string::npos) {
        return TargetOS::NETBSD;
    }
    return TargetOS::NONE;
}

std::optional<StdLibKind> parse_stdlib_kind(std::string_view value) {
    const std::string lowered = to_lower_ascii(value);
    if (lowered == "auto") {
        return StdLibKind::Auto;
    }
    if (lowered == "libc++") {
        return StdLibKind::LibCxx;
    }
    if (lowered == "libstdc++") {
        return StdLibKind::LibStdCxx;
    }
    if (lowered == "adinkra" || lowered == "libadinkra") {
        return StdLibKind::Adinkra;
    }
    return std::nullopt;
}

std::string stdlib_kind_name(StdLibKind kind) {
    switch (kind) {
        case StdLibKind::Auto:
            return "auto";
        case StdLibKind::LibCxx:
            return "libc++";
        case StdLibKind::LibStdCxx:
            return "libstdc++";
        case StdLibKind::Adinkra:
            return "adinkra";
    }
    return "auto";
}

std::optional<AdinkraRuntimeKind> parse_adinkra_runtime_kind(std::string_view value) {
    const std::string lowered = to_lower_ascii(value);
    if (lowered == "static") {
        return AdinkraRuntimeKind::Static;
    }
    if (lowered == "shared") {
        return AdinkraRuntimeKind::Shared;
    }
    return std::nullopt;
}

std::string default_driver_target_triple() {
    return "aarch64-apple-darwin";
}

std::string native_host_triple() {
#if defined(__APPLE__) && defined(__aarch64__)
    return "aarch64-apple-darwin";
#elif defined(__APPLE__) && defined(__arm64__)
    return "arm64-apple-darwin";
#elif defined(__APPLE__) && defined(__x86_64__)
    return "x86_64-apple-darwin";
#elif defined(__linux__) && defined(__aarch64__)
    return "aarch64-unknown-linux-gnu";
#elif defined(__linux__) && defined(__x86_64__)
    return "x86_64-unknown-linux-gnu";
#else
    return "unknown-unknown-unknown";
#endif
}

std::string default_target_triple() {
    return default_driver_target_triple();
}

const AdinkraLayout& discover_adinkra_layout(const char* argv0,
                                             const std::string& root_override) {
    // Resolved once per (argv0, override) pair: every translation unit and the
    // final link ask for this, and the answer cannot change within a process.
    static std::unordered_map<std::string, AdinkraLayout> cache;
    std::string key = (argv0 == nullptr ? std::string() : std::string(argv0));
    key.push_back('\n');
    key += root_override;

    auto it = cache.find(key);
    if (it == cache.end()) {
        it = cache.emplace(std::move(key),
            compute_adinkra_layout(argv0, root_override)).first;
    }
    return it->second;
}

bool target_is_native_host(std::string_view triple) {
    if (triple.empty()) {
        return true;
    }
    const std::string host = native_host_triple();
    return target_os_from_triple(triple) == target_os_from_triple(host) &&
        triple_architecture(triple) == triple_architecture(host);
}

StdLibKind resolve_effective_stdlib(std::string_view target_triple,
                                    StdLibKind requested,
                                    bool has_explicit_sysroot) {
    if (requested != StdLibKind::Auto) {
        return requested;
    }

    const TargetOS target_os = target_os_from_triple(target_triple);
    const bool hosted_os =
        target_os == TargetOS::MACOS || target_os == TargetOS::LINUX;
    // On Linux an explicit sysroot names a different root filesystem, whose C++
    // library is not the one built beside this compiler. On Darwin "-isysroot"
    // only selects an SDK for the platform headers, which Xcode-driven builds
    // pass routinely, so it must not change the standard library.
    const bool sysroot_redirects_root =
        has_explicit_sysroot && target_os == TargetOS::LINUX;
    if (kAdinkraIsAutomatic && hosted_os && !sysroot_redirects_root &&
        target_is_native_host(target_triple)) {
        return StdLibKind::Adinkra;
    }

    if (target_os == TargetOS::MACOS) {
        return StdLibKind::LibCxx;
    }
    if (target_os == TargetOS::LINUX) {
        return StdLibKind::LibStdCxx;
    }
    return StdLibKind::Auto;
}

CxxStdlibDiscoveryResult discover_cxx_stdlib_include_paths(
    const char* argv0,
    std::string_view target_triple,
    bool cxx_mode,
    StdLibKind requested_kind) {
    return discover_cxx_stdlib_include_paths(
        argv0, target_triple, cxx_mode, requested_kind, {});
}

CxxStdlibDiscoveryResult discover_cxx_stdlib_include_paths(
    const char* argv0,
    std::string_view target_triple,
    bool cxx_mode,
    StdLibKind requested_kind,
    const std::vector<std::string>& sysroots) {
    return discover_cxx_stdlib_include_paths(
        argv0, target_triple, cxx_mode, requested_kind, sysroots, {});
}

CxxStdlibDiscoveryResult discover_cxx_stdlib_include_paths(
    const char* argv0,
    std::string_view target_triple,
    bool cxx_mode,
    StdLibKind requested_kind,
    const std::vector<std::string>& sysroots,
    const std::string& adinkra_root) {
    CxxStdlibDiscoveryResult result;
    result.requested = requested_kind;
    result.resolved = requested_kind;

    if (!cxx_mode) {
        return result;
    }

    const TargetOS target_os = target_os_from_triple(target_triple);
    result.resolved =
        resolve_effective_stdlib(target_triple, requested_kind, !sysroots.empty());
    if (result.resolved == StdLibKind::Auto) {
        return result;
    }

    if (result.resolved == StdLibKind::Adinkra) {
        const AdinkraLayout& layout = discover_adinkra_layout(argv0, adinkra_root);
        result.attempted_paths.insert(result.attempted_paths.end(),
            layout.attempted_roots.begin(), layout.attempted_roots.end());
        if (layout.found) {
            result.include_paths.push_back(layout.include_dir);
            return result;
        }
        if (requested_kind == StdLibKind::Adinkra) {
            // report the miss rather than silently compiling against a different standard library
            return result;
        }
        // todo: are there any linux distros that use libc++?
        result.resolved = target_os == TargetOS::MACOS ? StdLibKind::LibCxx
                                                       : StdLibKind::LibStdCxx;
    }

    std::unordered_set<std::string> attempted_seen;
    std::unordered_set<std::string> include_seen;

    if (target_os == TargetOS::LINUX &&
        result.resolved == StdLibKind::LibStdCxx) {
        add_linux_libstdcxx_candidates(effective_linux_sysroots(sysroots),
            linux_multiarch_name(target_triple),
            result.attempted_paths,
            attempted_seen,
            result.include_paths,
            include_seen);
        return result;
    }

    if (target_os == TargetOS::MACOS && result.resolved == StdLibKind::LibCxx) {
        add_darwin_libcxx_candidates(argv0,
            sysroots,
            result.attempted_paths,
            attempted_seen,
            result.include_paths,
            include_seen);

        if (result.include_paths.size() > 1) {
            result.include_paths.resize(1);
        }
    }

    return result;
}

std::vector<std::string> discover_macos_sdk_include_paths(const char* argv0) {
    return discover_macos_sdk_include_paths(argv0, {});
}

std::vector<std::string> discover_macos_sdk_include_paths(
    const char* argv0,
    const std::vector<std::string>& sysroots) {
    (void)argv0;

    std::vector<std::string> paths;
    std::unordered_set<std::string> seen;

    for (const auto& sysroot : sysroots) {
        add_sdk_include_from_root(std::filesystem::path(sysroot), paths, seen);
    }

    if (const char* sdkroot = std::getenv("SDKROOT")) {
        add_sdk_include_from_root(std::filesystem::path(sdkroot), paths, seen);
    }

    add_sdk_from_dir("/Library/Developer/CommandLineTools/SDKs", paths, seen);
    add_sdk_from_dir(
        "/Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs",
        paths,
        seen);

    discover_clang_resource_includes(paths, seen);
    return paths;
}

HeaderSearchResult build_header_search_paths(const HeaderSearchOptions& options) {
    HeaderSearchResult result;
    const char* argv0 = options.argv0.empty() ? nullptr : options.argv0.c_str();
    std::unordered_set<std::string> include_seen;
    std::unordered_set<std::string> quote_seen;

    for (const auto& path : options.include_paths) {
        (void)try_add_include_path(path, result.include_paths, include_seen);
    }
    for (const auto& path : options.system_include_paths) {
        (void)try_add_include_path(path, result.include_paths, include_seen);
    }
    for (const auto& path : options.quote_include_paths) {
        (void)try_add_include_path(path, result.quote_include_paths, quote_seen);
    }

    if (!options.discover_platform_paths) {
        return result;
    }

    if (options.discover_cxx_stdlib_paths) {
        result.cxx_stdlib = discover_cxx_stdlib_include_paths(
            argv0,
            options.target_triple,
            options.cxx_mode,
            options.requested_stdlib,
            options.sysroots,
            options.adinkra_root);
        for (const auto& path : result.cxx_stdlib.include_paths) {
            (void)try_add_include_path(path, result.include_paths, include_seen);
        }
    }

    const TargetOS target_os = target_os_from_triple(options.target_triple);
    if (target_os == TargetOS::MACOS) {
        discover_aburi_builtin_includes(argv0, result.include_paths, include_seen);
        for (const auto& path : discover_macos_sdk_include_paths(argv0, options.sysroots)) {
            (void)try_add_include_path(path, result.include_paths, include_seen);
        }
    } else if (target_os == TargetOS::LINUX) {
        discover_aburi_builtin_includes(argv0, result.include_paths, include_seen);
        const std::string multiarch =
            linux_multiarch_name(options.target_triple);
        for (const auto& sysroot : effective_linux_sysroots(options.sysroots)) {
            const std::filesystem::path root(sysroot);
            if (!multiarch.empty()) {

                const std::filesystem::path gcc_dir = latest_version_subdir(
                    root / "usr" / "lib" / "gcc" / multiarch);
                if (!gcc_dir.empty()) {
                    (void)try_add_include_path(gcc_dir / "include",
                                               result.include_paths,
                                               include_seen);
                }
                (void)try_add_include_path(root / "usr" / "include" / multiarch,
                                           result.include_paths, include_seen);
            }
            (void)try_add_include_path(root / "usr" / "include",
                                       result.include_paths, include_seen);
        }
    }
    return result;
}
