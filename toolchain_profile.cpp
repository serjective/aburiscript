#include "toolchain_profile.h"

#include "abi/target_info.h"

#include <algorithm>
#include <cctype>
#include <cstdlib>
#include <filesystem>
#include <string>
#include <unordered_set>

namespace {

std::string to_lower_ascii(std::string_view value) {
    std::string lowered(value);
    std::transform(lowered.begin(), lowered.end(), lowered.begin(),
        [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
    return lowered;
}

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
    return TargetOS::NONE;
}

std::string normalize_candidate_path(const std::filesystem::path& path) {
    std::error_code ec;
    auto normalized = std::filesystem::weakly_canonical(path, ec);
    if (!ec) {
        return normalized.string();
    }
    return path.lexically_normal().string();
}

std::filesystem::path resolve_installed_dir(const char* argv0) {
    if (argv0 == nullptr || *argv0 == '\0') {
        return std::filesystem::path(".");
    }
    std::error_code ec;
    auto absolute_path = std::filesystem::absolute(std::filesystem::path(argv0), ec);
    if (ec) {
        absolute_path = std::filesystem::path(argv0);
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

} // namespace

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
    }
    return "auto";
}

std::string default_target_triple() {
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

CxxStdlibDiscoveryResult discover_cxx_stdlib_include_paths(
    const char* argv0,
    std::string_view target_triple,
    bool cxx_mode,
    StdLibKind requested_kind) {
    CxxStdlibDiscoveryResult result;
    result.requested = requested_kind;
    result.resolved = requested_kind;

    if (!cxx_mode) {
        return result;
    }

    const TargetOS target_os = target_os_from_triple(target_triple);
    if (requested_kind == StdLibKind::Auto) {
        if (target_os == TargetOS::MACOS) {
            result.resolved = StdLibKind::LibCxx;
        } else {
            return result;
        }
    }

    std::unordered_set<std::string> attempted_seen;
    std::unordered_set<std::string> include_seen;

    if (target_os == TargetOS::MACOS && result.resolved == StdLibKind::LibCxx) {
        add_darwin_libcxx_candidates(argv0,
            result.attempted_paths,
            attempted_seen,
            result.include_paths,
            include_seen);
        // Use one active libc++ root. Keeping multiple libc++ wrapper roots in the
        // search list breaks headers like <stdint.h> that rely on include_next to
        // drop from the C++ wrapper layer to the C header layer.
        if (result.include_paths.size() > 1) {
            result.include_paths.resize(1);
        }
    }

    return result;
}

std::vector<std::string> discover_macos_sdk_include_paths(const char* argv0) {
    (void)argv0;

    std::vector<std::string> paths;
    std::unordered_set<std::string> seen;

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
