#ifndef ABURI_ABI_POLICY_H
#define ABURI_ABI_POLICY_H

#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "bitfield_layout.h"
#include "target_info.h"

enum class CxxAbiKind {
    Itanium,
    Microsoft,
};

enum class ManglingKind {
    C,
    Itanium,
    Msvc,
};

enum class DataModelKind {
    LP64,
    LLP64,
    ILP32,
    Unknown,
};

enum class EndiannessKind {
    Little,
    Big,
};

enum class EhRuntimeKind {
    LLVM,
    GCC,
    Custom,
};

struct EhRuntimeHooks {
    std::string personality = "__gxx_personality_v0";
    std::string allocate_exception = "__cxa_allocate_exception";
    std::string throw_exception = "__cxa_throw";
    std::string rethrow_exception = "__cxa_rethrow";
    std::string dynamic_cast_symbol = "__dynamic_cast";
    std::string bad_cast = "__cxa_bad_cast";
    std::string bad_typeid = "__cxa_bad_typeid";
    std::string begin_catch = "__cxa_begin_catch";
    std::string end_catch = "__cxa_end_catch";
    std::string unwind_resume = "_Unwind_Resume";
    std::string terminate = "_ZSt9terminatev";
};

struct EhRuntimeLinkProfile {
    // Candidate C++ linker drivers for this runtime profile, in priority order.
    std::vector<std::string> cxx_linker_candidates;
    // Extra linker args needed to bias runtime selection for this profile.
    std::vector<std::string> runtime_link_args;
    // If true, missing candidates is a hard error instead of fallback.
    bool require_runtime_specific_driver = false;
};

struct AbiPolicy {
    // C++ object model ABI family used for language-level lowering decisions.
    CxxAbiKind cxx_abi = CxxAbiKind::Itanium;
    // Compatibility/version selector for ABI-specific behavior changes.
    int cxx_abi_version = 0;
    // Symbol naming scheme to use during linkage name emission.
    ManglingKind mangling = ManglingKind::C;
    // Bitfield packing/layout rules for record field placement.
    BitfieldABI bitfield_abi = BitfieldABI::ITANIUM;
    // Signedness rule for plain 'int' bitfields.
    bool plain_int_bitfield_signed = true;
    // Target byte order used by ABI-sensitive layout/details.
    EndiannessKind endianness = EndiannessKind::Little;
    // Integer/pointer size model (LP64/LLP64/ILP32).
    DataModelKind data_model = DataModelKind::Unknown;
    // Whether MS-style per-record layout overrides are honored.
    bool allow_ms_struct_layout_overrides = true;
    // Exception runtime profile for ABI/lowering/linker integration.
    EhRuntimeKind eh_runtime = EhRuntimeKind::LLVM;
    // Runtime hook symbol names used by EH lowering/codegen.
    EhRuntimeHooks eh_runtime_hooks;
};

struct DriverAbiOptions {
    std::optional<CxxAbiKind> cxx_abi;
    std::optional<int> cxx_abi_version;
    std::optional<BitfieldABI> bitfield_abi;
    std::optional<EhRuntimeKind> eh_runtime;
};

AbiPolicy abi_policy_for_target(const TargetInfo& target);
void apply_driver_abi_overrides(AbiPolicy& policy, const DriverAbiOptions& options);

std::optional<CxxAbiKind> parse_cxx_abi_kind(std::string_view value);
std::optional<EhRuntimeKind> parse_eh_runtime_kind(std::string_view value);
std::optional<int> parse_non_negative_int(std::string_view value);
EhRuntimeHooks eh_runtime_hooks_for_kind(EhRuntimeKind kind);
EhRuntimeLinkProfile eh_runtime_link_profile_for_kind(EhRuntimeKind kind,
                                                      TargetOS target_os);

#endif // ABURI_ABI_POLICY_H
