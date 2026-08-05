#ifndef ABURI_TARGET_INFO_H
#define ABURI_TARGET_INFO_H

#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

enum class TargetArch {
    AARCH64,
    X86_64,
    X86,
    ARM32,
    RISCV64,
    RISCV32,
    OR1K,
};

enum class EndiannessKind {
    Little,
    Big,
};

enum class TargetOS {
    MACOS,
    LINUX,
    WINDOWS,
    FREEBSD,
    NETBSD,
    NONE,
};

enum class LongDoubleFormat {
    IEEE_DOUBLE,
    X87_EXTENDED,
    IEEE_QUAD,
};

enum class VaListKind {
    CHAR_PTR,
    AARCH64_VA_LIST,
    X86_64_VA_LIST,
};

struct TargetInfo {
    TargetArch arch;
    TargetOS os;

    int pointer_width;
    int long_width;
    int long_double_width;
    int long_double_storage_bytes = 0;
    int long_double_align_bytes = 0;
    bool real_mode_16 = false;
    int wchar_width = 32;
    bool wchar_is_unsigned = false;
    bool char_is_unsigned = false;
    EndiannessKind endianness = EndiannessKind::Little;
    LongDoubleFormat long_double_format;
    VaListKind va_list_kind;
    size_t max_alignment_bytes = 16;
    size_t default_new_alignment_bytes = 16;

    std::string triple;
    int gnu_major = 4;
    int gnu_minor = 2;
    int gnu_patch = 1;
    int clang_major = 16;
    int clang_minor = 0;
    int clang_patch = 0;

    std::vector<std::pair<std::string, std::string>> get_builtin_macros() const;
    std::vector<std::pair<std::string, std::string>> get_builtin_type_macros() const;
    std::string wchar_type_spelling() const;
    size_t max_pack_alignment_bytes() const { return max_alignment_bytes; }
    static std::shared_ptr<TargetInfo> create_host();
    static std::shared_ptr<TargetInfo> create_apple_aarch64();
    static std::shared_ptr<TargetInfo> create_for_triple(std::string_view triple);
};

#endif // ABURI_TARGET_INFO_H
