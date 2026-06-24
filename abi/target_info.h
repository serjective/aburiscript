#ifndef ABURI_TARGET_INFO_H
#define ABURI_TARGET_INFO_H

#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

// Forward declarations to avoid circular includes
class TypeContext;
struct CType;
class QualType;

enum class TargetArch {
    AARCH64,
    X86_64,
    X86,
    ARM32,
    RISCV64,
    RISCV32,
};

enum class TargetOS {
    MACOS,
    LINUX,
    WINDOWS,
    FREEBSD,
    NONE,
};

enum class LongDoubleFormat {
    IEEE_DOUBLE,    // 64-bit, same as double (Apple ARM64)
    X87_EXTENDED,   // 80-bit x87 extended precision (x86/x86_64)
    IEEE_QUAD,      // 128-bit IEEE quad (AArch64 Linux, RISC-V)
};

enum class VaListKind {
    CHAR_PTR,           // Apple ARM64: va_list is char*
    AARCH64_VA_LIST,    // AArch64 Linux: __va_list struct
    X86_64_VA_LIST,     // x86_64 SysV: __va_list_tag[1]
};

struct TargetInfo {
    TargetArch arch;
    TargetOS os;

    int pointer_width;       // in bits (64 for ARM64)
    int long_width;          // in bits (64 for LP64, 32 for LLP64/Windows)
    int long_double_width;   // in bits (64 Apple ARM64, 80 x87, 128 IEEE quad)
    int wchar_width = 32;    // in bits
    bool wchar_is_unsigned = false;
    LongDoubleFormat long_double_format;
    VaListKind va_list_kind;
    size_t max_alignment_bytes = 16;

    std::string triple;      // LLVM target triple
    int gnu_major = 4;
    int gnu_minor = 2;
    int gnu_patch = 1;
    int clang_major = 16;
    int clang_minor = 0;
    int clang_patch = 0;

    // Construct the va_list CType appropriate for this target.
    // Requires a TypeContext to look up builtin types.
    std::shared_ptr<CType> get_va_list_type(TypeContext& ctx) const;
    std::vector<std::pair<std::string, std::string>> get_builtin_macros() const;
    std::vector<std::pair<std::string, std::string>> get_builtin_type_macros() const;
    std::string wchar_type_spelling() const;
    size_t max_pack_alignment_bytes() const { return max_alignment_bytes; }

    // Create a TargetInfo for the native host machine.
    static std::shared_ptr<TargetInfo> create_host();
    static std::shared_ptr<TargetInfo> create_apple_aarch64();
    static std::shared_ptr<TargetInfo> create_for_triple(std::string_view triple);
};

#endif // ABURI_TARGET_INFO_H
