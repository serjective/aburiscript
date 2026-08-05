#ifndef ABURI_ABI_POLICY_H
#define ABURI_ABI_POLICY_H

#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "target_info.h"

enum class BitfieldABI {
    ITANIUM,
    MSVC,
};

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
    std::vector<std::string> cxx_linker_candidates;
    std::vector<std::string> runtime_link_args;
    bool require_runtime_specific_driver = false;
};

struct AbiPolicy {
    CxxAbiKind cxx_abi = CxxAbiKind::Itanium;
    int cxx_abi_version = 0;
    ManglingKind mangling = ManglingKind::C;
    BitfieldABI bitfield_abi = BitfieldABI::ITANIUM;
    bool plain_int_bitfield_signed = true;
    EndiannessKind endianness = EndiannessKind::Little;
    DataModelKind data_model = DataModelKind::Unknown;
    bool allow_ms_struct_layout_overrides = true;
    bool can_key_function_be_inline = true;
    EhRuntimeKind eh_runtime = EhRuntimeKind::LLVM;
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
