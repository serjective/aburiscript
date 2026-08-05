#ifndef ABURI_TOOLCHAIN_PROFILE_H
#define ABURI_TOOLCHAIN_PROFILE_H

#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "abi/target_info.h"

enum class StdLibKind {
    Auto,
    LibCxx,
    LibStdCxx,
    Adinkra,
};

// Adinkra ships a static archive for ordinary single-image programs and a
// shared runtime for images that exchange exceptions, RTTI, or runtime-owned
// objects across a dynamic-library boundary.
enum class AdinkraRuntimeKind {
    Static,
    Shared,
};

std::optional<StdLibKind> parse_stdlib_kind(std::string_view value);
std::string stdlib_kind_name(StdLibKind kind);
std::optional<AdinkraRuntimeKind> parse_adinkra_runtime_kind(std::string_view value);

TargetOS target_os_from_triple(std::string_view triple);
std::string default_driver_target_triple();
std::string native_host_triple();
std::string default_target_triple();

// Where the Adinkra headers and runtime live for this compiler. Header search
// and the final link both resolve through this one function so they can never
// select a header set and an archive from different trees, which would be an
// undetectable ABI mismatch.
struct AdinkraLayout {
    bool found = false;
    std::string root;
    std::string include_dir;
    std::string static_library;
    std::string shared_library;
    std::string shared_library_dir;
    bool from_build_tree = false;
    std::vector<std::string> attempted_roots;
};

const AdinkraLayout& discover_adinkra_layout(const char* argv0,
                                             const std::string& root_override = {});

// The single source of truth for which C++ standard library an invocation uses.
// Header search and the final link both resolve through this so they cannot
// disagree. `has_explicit_sysroot` means the user named a different root
// filesystem, which suppresses the automatic Adinkra selection on Linux.
StdLibKind resolve_effective_stdlib(std::string_view target_triple,
                                    StdLibKind requested,
                                    bool has_explicit_sysroot);

// The Adinkra runtime beside the compiler is built by and for the host, so a
// cross target needs one supplied explicitly.
bool target_is_native_host(std::string_view triple);

struct CxxStdlibDiscoveryResult {
    StdLibKind requested = StdLibKind::Auto;
    StdLibKind resolved = StdLibKind::Auto;
    std::vector<std::string> include_paths;
    std::vector<std::string> attempted_paths;
};

struct HeaderSearchOptions {
    std::string argv0;
    std::string target_triple;
    bool cxx_mode = false;
    StdLibKind requested_stdlib = StdLibKind::Auto;
    std::string adinkra_root;
    std::vector<std::string> include_paths;
    std::vector<std::string> system_include_paths;
    std::vector<std::string> quote_include_paths;
    std::vector<std::string> sysroots;
    bool discover_platform_paths = true;
    bool discover_cxx_stdlib_paths = true;
};

struct HeaderSearchResult {
    std::vector<std::string> include_paths;
    std::vector<std::string> quote_include_paths;
    CxxStdlibDiscoveryResult cxx_stdlib;
};

CxxStdlibDiscoveryResult discover_cxx_stdlib_include_paths(
    const char* argv0,
    std::string_view target_triple,
    bool cxx_mode,
    StdLibKind requested_kind);
CxxStdlibDiscoveryResult discover_cxx_stdlib_include_paths(
    const char* argv0,
    std::string_view target_triple,
    bool cxx_mode,
    StdLibKind requested_kind,
    const std::vector<std::string>& sysroots);
CxxStdlibDiscoveryResult discover_cxx_stdlib_include_paths(
    const char* argv0,
    std::string_view target_triple,
    bool cxx_mode,
    StdLibKind requested_kind,
    const std::vector<std::string>& sysroots,
    const std::string& adinkra_root);

std::vector<std::string> discover_macos_sdk_include_paths(const char* argv0);
std::vector<std::string> discover_macos_sdk_include_paths(
    const char* argv0,
    const std::vector<std::string>& sysroots);

HeaderSearchResult build_header_search_paths(const HeaderSearchOptions& options);

#endif // ABURI_TOOLCHAIN_PROFILE_H
