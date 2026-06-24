#include "target_info.h"
#include "ast/types.h"
#include <algorithm>
#include <cctype>

namespace {

std::string lowercase_ascii(std::string_view value) {
    std::string out(value);
    std::transform(out.begin(), out.end(), out.begin(), [](unsigned char c) {
        return static_cast<char>(std::tolower(c));
    });
    return out;
}

std::shared_ptr<TargetInfo> make_aarch64_darwin(std::string triple) {
    auto ti = std::make_shared<TargetInfo>();
    ti->arch = TargetArch::AARCH64;
    ti->os = TargetOS::MACOS;
    ti->pointer_width = 64;
    ti->long_width = 64;
    ti->long_double_width = 64;
    ti->wchar_width = 32;
    ti->wchar_is_unsigned = false;
    ti->long_double_format = LongDoubleFormat::IEEE_DOUBLE;
    ti->va_list_kind = VaListKind::CHAR_PTR;
    ti->max_alignment_bytes = 16;
    ti->triple = std::move(triple);
    return ti;
}

std::shared_ptr<TargetInfo> make_x86_64_darwin(std::string triple) {
    auto ti = std::make_shared<TargetInfo>();
    ti->arch = TargetArch::X86_64;
    ti->os = TargetOS::MACOS;
    ti->pointer_width = 64;
    ti->long_width = 64;
    ti->long_double_width = 80;
    ti->wchar_width = 32;
    ti->wchar_is_unsigned = false;
    ti->long_double_format = LongDoubleFormat::X87_EXTENDED;
    ti->va_list_kind = VaListKind::X86_64_VA_LIST;
    ti->max_alignment_bytes = 16;
    ti->triple = std::move(triple);
    return ti;
}

std::shared_ptr<TargetInfo> make_aarch64_linux(std::string triple) {
    auto ti = std::make_shared<TargetInfo>();
    ti->arch = TargetArch::AARCH64;
    ti->os = TargetOS::LINUX;
    ti->pointer_width = 64;
    ti->long_width = 64;
    ti->long_double_width = 128;
    ti->wchar_width = 32;
    ti->wchar_is_unsigned = false;
    ti->long_double_format = LongDoubleFormat::IEEE_QUAD;
    ti->va_list_kind = VaListKind::AARCH64_VA_LIST;
    ti->max_alignment_bytes = 16;
    ti->triple = std::move(triple);
    return ti;
}

std::shared_ptr<TargetInfo> make_x86_64_linux(std::string triple) {
    auto ti = std::make_shared<TargetInfo>();
    ti->arch = TargetArch::X86_64;
    ti->os = TargetOS::LINUX;
    ti->pointer_width = 64;
    ti->long_width = 64;
    ti->long_double_width = 80;
    ti->wchar_width = 32;
    ti->wchar_is_unsigned = false;
    ti->long_double_format = LongDoubleFormat::X87_EXTENDED;
    ti->va_list_kind = VaListKind::X86_64_VA_LIST;
    ti->max_alignment_bytes = 16;
    ti->triple = std::move(triple);
    return ti;
}

} // namespace

std::shared_ptr<CType> TargetInfo::get_va_list_type(TypeContext& ctx) const {
    switch (va_list_kind) {
        case VaListKind::CHAR_PTR: {
            // Apple ARM64: va_list is char*
            return std::make_shared<PointerType>(
                QualType(ctx.get_builtin(BuiltinTypes::Char)));
        }
        case VaListKind::AARCH64_VA_LIST:
        case VaListKind::X86_64_VA_LIST:
            // Future: build the appropriate struct type
            // For now, fall back to char*
            return std::make_shared<PointerType>(
                QualType(ctx.get_builtin(BuiltinTypes::Char)));
    }
    // Unreachable, but satisfy compiler
    return std::make_shared<PointerType>(
        QualType(ctx.get_builtin(BuiltinTypes::Char)));
}

std::shared_ptr<TargetInfo> TargetInfo::create_host() {
#if defined(__APPLE__) && (defined(__aarch64__) || defined(__arm64__))
    return create_for_triple("aarch64-apple-darwin");
#elif defined(__APPLE__) && defined(__x86_64__)
    return create_for_triple("x86_64-apple-darwin");
#elif defined(__linux__) && defined(__aarch64__)
    return create_for_triple("aarch64-unknown-linux-gnu");
#elif defined(__linux__) && defined(__x86_64__)
    return create_for_triple("x86_64-unknown-linux-gnu");
#else
    auto ti = create_apple_aarch64();
    ti->triple = "unknown-unknown-unknown";
    ti->os = TargetOS::NONE;
    return ti;
#endif
}

std::shared_ptr<TargetInfo> TargetInfo::create_apple_aarch64() {
    return make_aarch64_darwin("aarch64-apple-darwin");
}

std::shared_ptr<TargetInfo> TargetInfo::create_for_triple(std::string_view triple) {
    const std::string original(triple);
    const std::string lowered = lowercase_ascii(triple);

    if ((lowered.find("aarch64") != std::string::npos ||
         lowered.find("arm64") != std::string::npos) &&
        (lowered.find("apple") != std::string::npos ||
         lowered.find("darwin") != std::string::npos ||
         lowered.find("macos") != std::string::npos)) {
        return make_aarch64_darwin(original.empty() ? "aarch64-apple-darwin" : original);
    }

    if ((lowered.find("x86_64") != std::string::npos ||
         lowered.find("amd64") != std::string::npos) &&
        (lowered.find("apple") != std::string::npos ||
         lowered.find("darwin") != std::string::npos ||
         lowered.find("macos") != std::string::npos)) {
        return make_x86_64_darwin(original.empty() ? "x86_64-apple-darwin" : original);
    }

    if ((lowered.find("aarch64") != std::string::npos ||
         lowered.find("arm64") != std::string::npos) &&
        lowered.find("linux") != std::string::npos) {
        return make_aarch64_linux(original.empty() ? "aarch64-unknown-linux-gnu" : original);
    }

    if ((lowered.find("x86_64") != std::string::npos ||
         lowered.find("amd64") != std::string::npos) &&
        lowered.find("linux") != std::string::npos) {
        return make_x86_64_linux(original.empty() ? "x86_64-unknown-linux-gnu" : original);
    }

    auto ti = create_apple_aarch64();
    ti->triple = original;
    ti->os = TargetOS::NONE;
    return ti;
}

std::string TargetInfo::wchar_type_spelling() const {
    if (wchar_width <= 16) {
        return wchar_is_unsigned ? "unsigned short" : "short";
    }
    if (wchar_width <= 32) {
        return wchar_is_unsigned ? "unsigned int" : "int";
    }
    if (wchar_width <= long_width) {
        return wchar_is_unsigned ? "unsigned long" : "long";
    }
    return wchar_is_unsigned ? "unsigned long long" : "long long";
}

std::vector<std::pair<std::string, std::string>> TargetInfo::get_builtin_macros() const {
    std::vector<std::pair<std::string, std::string>> out;
    auto add = [&](const std::string& name, const std::string& value) {
        out.emplace_back(name, value);
    };

    switch (os) {
        case TargetOS::MACOS:
            add("__APPLE__", "1");
            add("__MACH__", "1");
            add("__APPLE_CC__", "6000");
            // Clang defines PIC builtins by default on Darwin.
            // Configure scripts (e.g. ffmpeg) rely on these to detect PIC mode.
            add("__PIC__", "2");
            add("__pic__", "2");
            // Mirror Clang's default deployment target macros so Apple SDK
            // Availability logic enables expected API surface.
            add("__ENVIRONMENT_MAC_OS_X_VERSION_MIN_REQUIRED__", "260000");
            add("__ENVIRONMENT_OS_VERSION_MIN_REQUIRED__", "260000");
            break;
        case TargetOS::LINUX:
            add("__linux__", "1");
            break;
        case TargetOS::WINDOWS:
            add("_WIN32", "1");
            add("_WIN64", "1");
            break;
        case TargetOS::FREEBSD:
            add("__FreeBSD__", "1");
            break;
        case TargetOS::NONE:
            break;
    }

    switch (arch) {
        case TargetArch::AARCH64:
            add("__aarch64__", "1");
            add("__arm64__", "1");
            add("__ARM_ARCH", "8");
            add("__ARM_ARCH_ISA_A64", "1");
            add("__ARM_ARCH_PROFILE", "'A'");
            add("__ARM_FP", "0xE");
            add("__ARM_FP16_ARGS", "1");
            add("__ARM_FP16_FORMAT_IEEE", "1");
            add("__ARM_NEON", "1");
            add("__ARM_NEON__", "1");
            add("__ARM_NEON_FP", "0xE");
            add("__ARM_FEATURE_AES", "1");
            add("__ARM_FEATURE_CRYPTO", "1");
            break;
        case TargetArch::X86_64:
            add("__x86_64__", "1");
            add("__amd64__", "1");
            break;
        case TargetArch::X86:
            add("__i386__", "1");
            break;
        case TargetArch::ARM32:
            add("__arm__", "1");
            break;
        case TargetArch::RISCV64:
            add("__riscv", "1");
            add("__riscv_xlen", "64");
            break;
        case TargetArch::RISCV32:
            add("__riscv", "1");
            add("__riscv_xlen", "32");
            break;
    }

    if (pointer_width == 64) {
        add("__LP64__", "1");
        add("_LP64", "1");
    }

    add("__LITTLE_ENDIAN__", "1");
    add("__ORDER_LITTLE_ENDIAN__", "1234");
    add("__ORDER_BIG_ENDIAN__", "4321");
    add("__BYTE_ORDER__", "__ORDER_LITTLE_ENDIAN__");

    add("__GNUC__", std::to_string(gnu_major));
    add("__GNUC_MINOR__", std::to_string(gnu_minor));
    add("__GNUC_PATCHLEVEL__", std::to_string(gnu_patch));

    add("__clang__", "1");
    add("__clang_major__", std::to_string(clang_major));
    add("__clang_minor__", std::to_string(clang_minor));
    add("__clang_patchlevel__", std::to_string(clang_patch));
    add("__clang_version__", "\"" + std::to_string(clang_major) + "." +
        std::to_string(clang_minor) + "." + std::to_string(clang_patch) + " (Aburi)\"");

    return out;
}

std::vector<std::pair<std::string, std::string>> TargetInfo::get_builtin_type_macros() const {
    std::vector<std::pair<std::string, std::string>> out;
    auto add = [&](const std::string& name, const std::string& value) {
        out.emplace_back(name, value);
    };

    auto integer_type_for_width = [&](int width, bool is_unsigned) -> std::string {
        if (width <= 32) {
            return is_unsigned ? "unsigned int" : "int";
        }
        if (width <= long_width) {
            return is_unsigned ? "unsigned long" : "long";
        }
        return is_unsigned ? "unsigned long long" : "long long";
    };

    add("__SIZE_TYPE__", integer_type_for_width(pointer_width, true));
    add("__PTRDIFF_TYPE__", integer_type_for_width(pointer_width, false));
    add("__INTPTR_TYPE__", integer_type_for_width(pointer_width, false));
    add("__UINTPTR_TYPE__", integer_type_for_width(pointer_width, true));
    add("__INTMAX_TYPE__", integer_type_for_width(std::max(64, long_width), false));
    add("__UINTMAX_TYPE__", integer_type_for_width(std::max(64, long_width), true));

    // Fixed-width integer builtin type macros used by GCC torture tests and libc headers.
    add("__INT8_TYPE__", "signed char");
    add("__UINT8_TYPE__", "unsigned char");
    add("__INT16_TYPE__", "short");
    add("__UINT16_TYPE__", "unsigned short");
    add("__INT32_TYPE__", "int");
    add("__UINT32_TYPE__", "unsigned int");
    add("__INT64_TYPE__", "long long");
    add("__UINT64_TYPE__", "unsigned long long");

    add("__INT_LEAST8_TYPE__", "signed char");
    add("__UINT_LEAST8_TYPE__", "unsigned char");
    add("__INT_LEAST16_TYPE__", "short");
    add("__UINT_LEAST16_TYPE__", "unsigned short");
    add("__INT_LEAST32_TYPE__", "int");
    add("__UINT_LEAST32_TYPE__", "unsigned int");
    add("__INT_LEAST64_TYPE__", "long long");
    add("__UINT_LEAST64_TYPE__", "unsigned long long");

    add("__WCHAR_TYPE__", wchar_type_spelling());
    add("__WINT_TYPE__", wchar_type_spelling());

    // Floating-point limit macros
    // float (IEEE 754 binary32) — same on all targets
    add("__FLT_MIN__", "1.17549435082228750797e-38F");
    add("__FLT_MAX__", "3.40282346638528859812e+38F");
    add("__FLT_EPSILON__", "1.19209289550781250000e-7F");
    add("__FLT_DENORM_MIN__", "1.40129846432481707092e-45F");
    add("__FLT_HAS_DENORM__", "1");
    add("__FLT_HAS_INFINITY__", "1");
    add("__FLT_HAS_QUIET_NAN__", "1");
    add("__FLT_MANT_DIG__", "24");
    add("__FLT_MAX_EXP__", "128");
    add("__FLT_MAX_10_EXP__", "38");
    add("__FLT_MIN_EXP__", "-125");
    add("__FLT_MIN_10_EXP__", "-37");
    add("__FLT_DIG__", "6");
    add("__FLT_DECIMAL_DIG__", "9");

    // double (IEEE 754 binary64) — same on all targets
    add("__DBL_MIN__", "2.2250738585072014e-308");
    add("__DBL_MAX__", "1.7976931348623157e+308");
    add("__DBL_EPSILON__", "2.2204460492503131e-16");
    add("__DBL_DENORM_MIN__", "4.9406564584124654e-324");
    add("__DBL_HAS_DENORM__", "1");
    add("__DBL_HAS_INFINITY__", "1");
    add("__DBL_HAS_QUIET_NAN__", "1");
    add("__DBL_MANT_DIG__", "53");
    add("__DBL_MAX_EXP__", "1024");
    add("__DBL_MAX_10_EXP__", "308");
    add("__DBL_MIN_EXP__", "-1021");
    add("__DBL_MIN_10_EXP__", "-307");
    add("__DBL_DIG__", "15");
    add("__DBL_DECIMAL_DIG__", "17");

    // long double — target-dependent
    switch (long_double_format) {
        case LongDoubleFormat::IEEE_DOUBLE:
            // Apple ARM64: long double == double
            add("__LDBL_MIN__", "2.2250738585072014e-308L");
            add("__LDBL_MAX__", "1.7976931348623157e+308L");
            add("__LDBL_EPSILON__", "2.2204460492503131e-16L");
            add("__LDBL_DENORM_MIN__", "4.9406564584124654e-324L");
            add("__LDBL_MANT_DIG__", "53");
            add("__LDBL_MAX_EXP__", "1024");
            add("__LDBL_MAX_10_EXP__", "308");
            add("__LDBL_MIN_EXP__", "-1021");
            add("__LDBL_MIN_10_EXP__", "-307");
            add("__LDBL_DIG__", "15");
            add("__LDBL_DECIMAL_DIG__", "17");
            break;
        case LongDoubleFormat::X87_EXTENDED:
            // x86/x86_64: 80-bit extended
            add("__LDBL_MIN__", "3.36210314311209350626e-4932L");
            add("__LDBL_MAX__", "1.18973149535723176502e+4932L");
            add("__LDBL_EPSILON__", "1.08420217248550443401e-19L");
            add("__LDBL_DENORM_MIN__", "3.64519953188247460253e-4951L");
            add("__LDBL_MANT_DIG__", "64");
            add("__LDBL_MAX_EXP__", "16384");
            add("__LDBL_MAX_10_EXP__", "4932");
            add("__LDBL_MIN_EXP__", "-16381");
            add("__LDBL_MIN_10_EXP__", "-4931");
            add("__LDBL_DIG__", "18");
            add("__LDBL_DECIMAL_DIG__", "21");
            break;
        case LongDoubleFormat::IEEE_QUAD:
            // AArch64 Linux, RISC-V: 128-bit quad
            add("__LDBL_MIN__", "3.36210314311209350626267781732175260e-4932L");
            add("__LDBL_MAX__", "1.18973149535723176508575932662800702e+4932L");
            add("__LDBL_EPSILON__", "1.92592994438723585305597794258492732e-34L");
            add("__LDBL_DENORM_MIN__", "6.47517511943802511092443895822764655e-4966L");
            add("__LDBL_MANT_DIG__", "113");
            add("__LDBL_MAX_EXP__", "16384");
            add("__LDBL_MAX_10_EXP__", "4932");
            add("__LDBL_MIN_EXP__", "-16381");
            add("__LDBL_MIN_10_EXP__", "-4931");
            add("__LDBL_DIG__", "33");
            add("__LDBL_DECIMAL_DIG__", "36");
            break;
    }
    add("__LDBL_HAS_DENORM__", "1");
    add("__LDBL_HAS_INFINITY__", "1");
    add("__LDBL_HAS_QUIET_NAN__", "1");

    // _Float16 (IEEE 754 binary16)
    add("__FLT16_MIN__", "6.103515625e-5");
    add("__FLT16_MAX__", "6.5504e+4");
    add("__FLT16_EPSILON__", "9.765625e-4");
    add("__FLT16_MANT_DIG__", "11");
    add("__FLT16_DIG__", "3");
    add("__FLT16_MAX_EXP__", "16");
    add("__FLT16_MIN_EXP__", "-13");

    return out;
}
