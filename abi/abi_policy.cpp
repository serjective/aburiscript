#include "abi_policy.h"

#include <algorithm>
#include <cctype>
#include <limits>
#include <string>

namespace {
std::string lowercase_ascii(std::string_view value) {
    std::string out(value);
    std::transform(out.begin(), out.end(), out.begin(), [](unsigned char c) {
        return static_cast<char>(std::tolower(c));
    });
    return out;
}

ManglingKind mangling_for_cxx_abi(CxxAbiKind abi) {
    switch (abi) {
        case CxxAbiKind::Itanium:
            return ManglingKind::Itanium;
        case CxxAbiKind::Microsoft:
            return ManglingKind::Msvc;
    }
    return ManglingKind::C;
}

DataModelKind data_model_for_target(const TargetInfo& target) {
    if (target.pointer_width == 64 && target.long_width == 64) {
        return DataModelKind::LP64;
    }
    if (target.pointer_width == 64 && target.long_width == 32) {
        return DataModelKind::LLP64;
    }
    if (target.pointer_width == 32 && target.long_width == 32) {
        return DataModelKind::ILP32;
    }
    return DataModelKind::Unknown;
}
} // namespace

EhRuntimeHooks eh_runtime_hooks_for_kind(EhRuntimeKind kind) {
    // LLVM and GCC Itanium C++ EH runtimes share the same public symbol ABI.
    // `Custom` defaults to Itanium-compatible names until user/runtime-specific
    // overrides are threaded through policy configuration.
    switch (kind) {
        case EhRuntimeKind::LLVM:
        case EhRuntimeKind::GCC:
        case EhRuntimeKind::Custom:
            return EhRuntimeHooks{};
    }
    return EhRuntimeHooks{};
}

EhRuntimeLinkProfile eh_runtime_link_profile_for_kind(EhRuntimeKind kind,
                                                      TargetOS target_os) {
    EhRuntimeLinkProfile profile;
    profile.cxx_linker_candidates = {"/usr/bin/c++", "c++"};

    switch (kind) {
        case EhRuntimeKind::LLVM:
            // Keep explicit runtime-library selection conservative and host-tuned
            // until target/driver probing is expanded.
            if (target_os == TargetOS::MACOS) {
                profile.runtime_link_args = {"-rtlib=compiler-rt", "-unwindlib=libunwind"};
            }
            return profile;

        case EhRuntimeKind::GCC:
            profile.cxx_linker_candidates = {
                "/opt/homebrew/bin/g++-15",
                "/usr/local/bin/g++-15",
                "g++-15"
            };
            profile.require_runtime_specific_driver = true;
            return profile;

        case EhRuntimeKind::Custom:
            // Custom profile keeps a neutral default driver/args; embedders can
            // override policy hooks/symbols while the driver path stays stable.
            return profile;
    }
    return profile;
}

AbiPolicy abi_policy_for_target(const TargetInfo& target) {
    AbiPolicy policy;
    policy.data_model = data_model_for_target(target);
    policy.endianness = EndiannessKind::Little;
    policy.plain_int_bitfield_signed = true;
    policy.allow_ms_struct_layout_overrides = true;

    if (target.os == TargetOS::WINDOWS) {
        policy.cxx_abi = CxxAbiKind::Microsoft;
        policy.bitfield_abi = BitfieldABI::MSVC;
    } else {
        policy.cxx_abi = CxxAbiKind::Itanium;
        policy.bitfield_abi = BitfieldABI::ITANIUM;
    }

    // Default to C-style naming in C mode; C++ mode can opt into ABI mangling
    // through driver overrides for now.
    policy.mangling = ManglingKind::C;
    policy.eh_runtime_hooks = eh_runtime_hooks_for_kind(policy.eh_runtime);
    return policy;
}

void apply_driver_abi_overrides(AbiPolicy& policy, const DriverAbiOptions& options) {
    if (options.cxx_abi.has_value()) {
        policy.cxx_abi = *options.cxx_abi;
        policy.mangling = mangling_for_cxx_abi(*options.cxx_abi);
    }
    if (options.cxx_abi_version.has_value()) {
        policy.cxx_abi_version = *options.cxx_abi_version;
    }
    if (options.bitfield_abi.has_value()) {
        policy.bitfield_abi = *options.bitfield_abi;
    }
    if (options.eh_runtime.has_value()) {
        policy.eh_runtime = *options.eh_runtime;
        policy.eh_runtime_hooks = eh_runtime_hooks_for_kind(*options.eh_runtime);
    }
}

std::optional<CxxAbiKind> parse_cxx_abi_kind(std::string_view value) {
    const std::string lowered = lowercase_ascii(value);
    if (lowered == "itanium") {
        return CxxAbiKind::Itanium;
    }
    if (lowered == "microsoft" || lowered == "msvc") {
        return CxxAbiKind::Microsoft;
    }
    return std::nullopt;
}

std::optional<EhRuntimeKind> parse_eh_runtime_kind(std::string_view value) {
    const std::string lowered = lowercase_ascii(value);
    if (lowered == "llvm") {
        return EhRuntimeKind::LLVM;
    }
    if (lowered == "gcc") {
        return EhRuntimeKind::GCC;
    }
    if (lowered == "custom") {
        return EhRuntimeKind::Custom;
    }
    return std::nullopt;
}

std::optional<int> parse_non_negative_int(std::string_view value) {
    if (value.empty()) {
        return std::nullopt;
    }

    long long parsed = 0;
    for (char ch : value) {
        if (ch < '0' || ch > '9') {
            return std::nullopt;
        }
        parsed = parsed * 10 + static_cast<long long>(ch - '0');
        if (parsed > std::numeric_limits<int>::max()) {
            return std::nullopt;
        }
    }
    return static_cast<int>(parsed);
}
