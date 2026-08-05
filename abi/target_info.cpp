#include "target_info.h"
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

    ti->wchar_is_unsigned = true;
    ti->char_is_unsigned = true;
    ti->long_double_format = LongDoubleFormat::IEEE_QUAD;
    ti->va_list_kind = VaListKind::AARCH64_VA_LIST;
    ti->max_alignment_bytes = 16;
    ti->triple = std::move(triple);
    return ti;
}

std::shared_ptr<TargetInfo> make_aarch64_freebsd(std::string triple) {
    auto ti = make_aarch64_linux(std::move(triple));
    ti->os = TargetOS::FREEBSD;
    return ti;
}

std::shared_ptr<TargetInfo> make_aarch64_netbsd(std::string triple) {
    auto ti = make_aarch64_linux(std::move(triple));
    ti->os = TargetOS::NETBSD;
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

std::shared_ptr<TargetInfo> make_x86_64_windows(std::string triple) {
    auto ti = std::make_shared<TargetInfo>();
    ti->arch = TargetArch::X86_64;
    ti->os = TargetOS::WINDOWS;
    ti->pointer_width = 64;
    ti->long_width = 32;
    ti->long_double_width = 64;
    ti->wchar_width = 16;
    ti->wchar_is_unsigned = true;
    ti->long_double_format = LongDoubleFormat::IEEE_DOUBLE;
    ti->va_list_kind = VaListKind::CHAR_PTR;
    ti->max_alignment_bytes = 16;
    ti->triple = std::move(triple);
    return ti;
}

// 32-bit x86 (i686 Linux, ILP32, SysV i386 ABI). Second-class per the
// architecture policy. long double is 80-bit x87 stored in 12 bytes at
// 4-byte alignment (unlike the 16-byte x86-64 storage); the layout query
// applies the alignment. va_list is a plain char* cursor with 4-byte slots.
std::shared_ptr<TargetInfo> make_x86_linux(std::string triple) {
    auto ti = std::make_shared<TargetInfo>();
    ti->arch = TargetArch::X86;
    ti->os = TargetOS::LINUX;
    ti->pointer_width = 32;
    ti->long_width = 32;
    ti->long_double_width = 80;

    ti->long_double_storage_bytes = 12;
    ti->long_double_align_bytes = 4;
    ti->wchar_width = 32;
    ti->wchar_is_unsigned = false;
    ti->char_is_unsigned = false;
    ti->long_double_format = LongDoubleFormat::X87_EXTENDED;
    ti->va_list_kind = VaListKind::CHAR_PTR;
    ti->max_alignment_bytes = 16;
    ti->triple = std::move(triple);
    return ti;
}

std::shared_ptr<TargetInfo> make_x86_bare(std::string triple) {
    auto ti = make_x86_linux(triple);
    ti->os = TargetOS::NONE;
    ti->real_mode_16 = true;
    return ti;
}

std::shared_ptr<TargetInfo> make_or1k_linux(std::string triple) {
    auto ti = std::make_shared<TargetInfo>();
    ti->arch = TargetArch::OR1K;
    ti->os = TargetOS::LINUX;
    ti->pointer_width = 32;
    ti->long_width = 32;
    ti->long_double_width = 64;
    ti->wchar_width = 32;
    ti->wchar_is_unsigned = false;
    ti->char_is_unsigned = false;
    ti->endianness = EndiannessKind::Big;
    ti->long_double_format = LongDoubleFormat::IEEE_DOUBLE;
    ti->va_list_kind = VaListKind::CHAR_PTR;
    ti->max_alignment_bytes = 16;
    ti->triple = std::move(triple);
    return ti;
}

std::shared_ptr<TargetInfo> make_x86_64_freebsd(std::string triple) {
    auto ti = make_x86_64_linux(std::move(triple));
    ti->os = TargetOS::FREEBSD;
    return ti;
}

std::shared_ptr<TargetInfo> make_x86_64_netbsd(std::string triple) {
    auto ti = make_x86_64_linux(std::move(triple));
    ti->os = TargetOS::NETBSD;
    return ti;
}

} // namespace

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

    if ((lowered.find("x86_64") != std::string::npos ||
         lowered.find("amd64") != std::string::npos) &&
        (lowered.find("windows") != std::string::npos ||
         lowered.find("win32") != std::string::npos ||
         lowered.find("mingw") != std::string::npos ||
         lowered.find("msvc") != std::string::npos)) {
        return make_x86_64_windows(
            original.empty() ? "x86_64-pc-windows-msvc" : original);
    }

    if ((lowered.find("aarch64") != std::string::npos ||
         lowered.find("arm64") != std::string::npos) &&
        lowered.find("freebsd") != std::string::npos) {
        return make_aarch64_freebsd(original.empty() ? "aarch64-unknown-freebsd" : original);
    }

    if ((lowered.find("x86_64") != std::string::npos ||
         lowered.find("amd64") != std::string::npos) &&
        lowered.find("freebsd") != std::string::npos) {
        return make_x86_64_freebsd(original.empty() ? "x86_64-unknown-freebsd" : original);
    }

    if ((lowered.find("aarch64") != std::string::npos ||
         lowered.find("arm64") != std::string::npos) &&
        lowered.find("netbsd") != std::string::npos) {
        return make_aarch64_netbsd(original.empty() ? "aarch64-unknown-netbsd" : original);
    }

    if ((lowered.find("x86_64") != std::string::npos ||
         lowered.find("amd64") != std::string::npos) &&
        lowered.find("netbsd") != std::string::npos) {
        return make_x86_64_netbsd(original.empty() ? "x86_64-unknown-netbsd" : original);
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

    bool is_x86_32 = lowered.find("i386") != std::string::npos ||
                     lowered.find("i486") != std::string::npos ||
                     lowered.find("i586") != std::string::npos ||
                     lowered.find("i686") != std::string::npos;
    if (is_x86_32 && lowered.find("linux") != std::string::npos) {
        return make_x86_linux(original.empty() ? "i686-unknown-linux-gnu" : original);
    }

    if (is_x86_32) {
        return make_x86_bare(original.empty() ? "i386-unknown-none" : original);
    }

    if (lowered.find("or1k") != std::string::npos ||
        lowered.find("openrisc") != std::string::npos) {
        return make_or1k_linux(original.empty() ? "or1k-unknown-linux-musl"
                                                : original);
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

            add("__PIC__", "2");
            add("__pic__", "2");

            add("__ENVIRONMENT_MAC_OS_X_VERSION_MIN_REQUIRED__", "260000");
            add("__ENVIRONMENT_OS_VERSION_MIN_REQUIRED__", "260000");
            break;
        case TargetOS::LINUX:
            add("__linux__", "1");
            add("__linux", "1");
            add("linux", "1");
            add("__gnu_linux__", "1");
            add("__unix__", "1");
            add("__unix", "1");
            add("unix", "1");
            add("__ELF__", "1");
            break;
        case TargetOS::WINDOWS:
            add("_WIN32", "1");
            add("_WIN64", "1");
            break;
        case TargetOS::FREEBSD: {

            std::string lowered_triple = lowercase_ascii(triple);
            std::string major = "14";
            size_t pos = lowered_triple.find("freebsd");
            if (pos != std::string::npos) {
                size_t d = pos + std::string_view("freebsd").size();
                std::string digits;
                while (d < lowered_triple.size() &&
                       lowered_triple[d] >= '0' && lowered_triple[d] <= '9') {
                    digits.push_back(lowered_triple[d++]);
                }
                if (!digits.empty()) {
                    major = digits;
                }
            }
            add("__FreeBSD__", major);
            add("__FreeBSD_cc_version", major + "00001");
            add("__ELF__", "1");
            add("__unix__", "1");
            add("__unix", "1");
            add("unix", "1");
            break;
        }
        case TargetOS::NETBSD:

            add("__NetBSD__", "1");
            add("__ELF__", "1");
            add("__unix__", "1");
            add("__unix", "1");
            add("unix", "1");
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

            add("__ARM_PCS_AAPCS64", "1");
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

            add("__float128", "long double");
            add("__amd64__", "1");
            break;
        case TargetArch::X86:
            add("__i386__", "1");

            add("__float128", "long double");
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
        case TargetArch::OR1K:
            add("__or1k__", "1");
            add("__OR1K__", "1");
            break;
    }

    if (pointer_width == 64) {
        add("__LP64__", "1");
        add("_LP64", "1");

        add("__SIZEOF_INT128__", "16");
    }

    if (char_is_unsigned) {
        add("__CHAR_UNSIGNED__", "1");
    }
    if (wchar_is_unsigned) {
        add("__WCHAR_UNSIGNED__", "1");
    }

    add("__UINT16_MAX__", "65535");
    add("__UINT32_MAX__", "4294967295U");
    uint64_t ptrdiff_max = pointer_width >= 64
        ? uint64_t{INT64_MAX}
        : (uint64_t{1} << (pointer_width - 1)) - 1;
    std::string ptrdiff_max_spelling = std::to_string(ptrdiff_max);
    if (pointer_width > 32) {
        ptrdiff_max_spelling += pointer_width <= long_width ? "L" : "LL";
    }
    add("__PTRDIFF_MAX__", ptrdiff_max_spelling);
    uint64_t wchar_max = 0;
    if (wchar_is_unsigned) {
        wchar_max = wchar_width >= 64
            ? UINT64_MAX
            : (uint64_t{1} << wchar_width) - 1;
    } else {
        wchar_max = wchar_width >= 64
            ? uint64_t{INT64_MAX}
            : (uint64_t{1} << (wchar_width - 1)) - 1;
    }
    std::string wchar_max_spelling = std::to_string(wchar_max);
    if (wchar_is_unsigned && wchar_max > uint64_t{INT32_MAX}) {
        wchar_max_spelling += wchar_width > 32 ? "ULL" : "U";
    } else if (!wchar_is_unsigned && wchar_width > 32) {
        wchar_max_spelling += "LL";
    }
    add("__WCHAR_MAX__", wchar_max_spelling);

    add("__ORDER_LITTLE_ENDIAN__", "1234");
    add("__ORDER_BIG_ENDIAN__", "4321");
    if (endianness == EndiannessKind::Big) {
        add("__BIG_ENDIAN__", "1");
        add("__BYTE_ORDER__", "__ORDER_BIG_ENDIAN__");
    } else {
        add("__LITTLE_ENDIAN__", "1");
        add("__BYTE_ORDER__", "__ORDER_LITTLE_ENDIAN__");
    }

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

    add("__INT8_TYPE__", "signed char");
    add("__UINT8_TYPE__", "unsigned char");
    add("__INT16_TYPE__", "short");
    add("__UINT16_TYPE__", "unsigned short");
    add("__INT32_TYPE__", "int");
    add("__UINT32_TYPE__", "unsigned int");

    const bool int64_is_long =
        (os == TargetOS::LINUX || os == TargetOS::FREEBSD ||
         os == TargetOS::NETBSD) && long_width == 64;
    const char* int64_spelling = int64_is_long ? "long" : "long long";
    const char* uint64_spelling =
        int64_is_long ? "unsigned long" : "unsigned long long";
    add("__INT64_TYPE__", int64_spelling);
    add("__UINT64_TYPE__", uint64_spelling);

    add("__INT_LEAST8_TYPE__", "signed char");
    add("__UINT_LEAST8_TYPE__", "unsigned char");
    add("__INT_LEAST16_TYPE__", "short");
    add("__UINT_LEAST16_TYPE__", "unsigned short");
    add("__INT_LEAST32_TYPE__", "int");
    add("__UINT_LEAST32_TYPE__", "unsigned int");
    add("__INT_LEAST64_TYPE__", int64_spelling);
    add("__UINT_LEAST64_TYPE__", uint64_spelling);

    add("__INT_FAST8_TYPE__", "signed char");
    add("__UINT_FAST8_TYPE__", "unsigned char");
    if (os == TargetOS::LINUX && pointer_width == 64) {
        add("__INT_FAST16_TYPE__", "long");
        add("__UINT_FAST16_TYPE__", "unsigned long");
        add("__INT_FAST32_TYPE__", "long");
        add("__UINT_FAST32_TYPE__", "unsigned long");
        add("__INT_FAST64_TYPE__", "long");
        add("__UINT_FAST64_TYPE__", "unsigned long");
    } else {
        add("__INT_FAST16_TYPE__", "short");
        add("__UINT_FAST16_TYPE__", "unsigned short");
        add("__INT_FAST32_TYPE__", "int");
        add("__UINT_FAST32_TYPE__", "unsigned int");
        add("__INT_FAST64_TYPE__", "long long");
        add("__UINT_FAST64_TYPE__", "unsigned long long");
    }

    add("__WCHAR_TYPE__", wchar_type_spelling());
    add("__WINT_TYPE__", wchar_type_spelling());

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

    add("__FLT_EVAL_METHOD__", "0");

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

    switch (long_double_format) {
        case LongDoubleFormat::IEEE_DOUBLE:

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

    add("__DECIMAL_DIG__", "__LDBL_DECIMAL_DIG__");

    add("__FLT16_MIN__", "6.103515625e-5");
    add("__FLT16_MAX__", "6.5504e+4");
    add("__FLT16_EPSILON__", "9.765625e-4");
    add("__FLT16_MANT_DIG__", "11");
    add("__FLT16_DIG__", "3");
    add("__FLT16_MAX_EXP__", "16");
    add("__FLT16_MIN_EXP__", "-13");

    return out;
}
