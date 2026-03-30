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

    maybe_record_candidate("/Library/Developer/CommandLineTools/usr/include/c++/v1",
        attempted_paths, attempted_seen, include_paths, include_seen);
    maybe_record_candidate(
        "/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/include/c++/v1",
        attempted_paths,
        attempted_seen,
        include_paths,
        include_seen);
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
    }

    return result;
}
