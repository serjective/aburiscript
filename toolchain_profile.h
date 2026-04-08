#ifndef ABURI_TOOLCHAIN_PROFILE_H
#define ABURI_TOOLCHAIN_PROFILE_H

#include <optional>
#include <string>
#include <string_view>
#include <vector>

enum class StdLibKind {
    Auto,
    LibCxx,
    LibStdCxx,
};

std::optional<StdLibKind> parse_stdlib_kind(std::string_view value);
std::string stdlib_kind_name(StdLibKind kind);

struct CxxStdlibDiscoveryResult {
    StdLibKind requested = StdLibKind::Auto;
    StdLibKind resolved = StdLibKind::Auto;
    std::vector<std::string> include_paths;
    std::vector<std::string> attempted_paths;
};

CxxStdlibDiscoveryResult discover_cxx_stdlib_include_paths(
    const char* argv0,
    std::string_view target_triple,
    bool cxx_mode,
    StdLibKind requested_kind);

std::vector<std::string> discover_macos_sdk_include_paths(const char* argv0);

#endif // ABURI_TOOLCHAIN_PROFILE_H
