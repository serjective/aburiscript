#ifndef ABURI_TARGET_FEATURE_GATE_H
#define ABURI_TARGET_FEATURE_GATE_H

#include <cctype>
#include <optional>
#include <string>
#include <string_view>
#include "abi/target_info.h"

enum class TargetFeatureFamily {
    Unknown,
    X86,
    Arm,
    Ppc,
    Riscv,
};

inline bool tf_starts_with(std::string_view value, std::string_view prefix) {
    return value.rfind(prefix, 0) == 0;
}

inline std::string tf_to_lower(std::string_view value) {
    std::string lowered(value);
    for (char& c : lowered) {
        c = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
    }
    return lowered;
}

inline std::optional<TargetFeatureFamily> tf_family_from_triple(std::string_view triple) {
    const std::string lowered = tf_to_lower(triple);
    if (lowered.find("powerpc") != std::string::npos || lowered.find("ppc") != std::string::npos) {
        return TargetFeatureFamily::Ppc;
    }
    if (lowered.find("x86_64") != std::string::npos ||
        lowered.find("amd64") != std::string::npos ||
        lowered.find("i386") != std::string::npos ||
        lowered.find("i486") != std::string::npos ||
        lowered.find("i586") != std::string::npos ||
        lowered.find("i686") != std::string::npos) {
        return TargetFeatureFamily::X86;
    }
    if (lowered.find("aarch64") != std::string::npos ||
        lowered.find("arm64") != std::string::npos ||
        tf_starts_with(lowered, "arm")) {
        return TargetFeatureFamily::Arm;
    }
    if (lowered.find("riscv") != std::string::npos) {
        return TargetFeatureFamily::Riscv;
    }
    return std::nullopt;
}

inline std::optional<TargetFeatureFamily> tf_family_from_arch_name(std::string_view arch_name) {
    const std::string lowered = tf_to_lower(arch_name);
    if (lowered == "x86_64" || lowered == "amd64" ||
        lowered == "i386" || lowered == "i486" ||
        lowered == "i586" || lowered == "i686") {
        return TargetFeatureFamily::X86;
    }
    if (lowered == "arm64" || lowered == "aarch64" || tf_starts_with(lowered, "arm")) {
        return TargetFeatureFamily::Arm;
    }
    if (lowered == "ppc" || lowered == "ppc64" || lowered == "powerpc" || lowered == "powerpc64") {
        return TargetFeatureFamily::Ppc;
    }
    if (lowered == "riscv32" || lowered == "riscv64") {
        return TargetFeatureFamily::Riscv;
    }
    return std::nullopt;
}

inline TargetFeatureFamily tf_family_from_arch(TargetArch arch) {
    switch (arch) {
        case TargetArch::X86:
        case TargetArch::X86_64:
            return TargetFeatureFamily::X86;
        case TargetArch::AARCH64:
        case TargetArch::ARM32:
            return TargetFeatureFamily::Arm;
        case TargetArch::RISCV32:
        case TargetArch::RISCV64:
            return TargetFeatureFamily::Riscv;
    }
    return TargetFeatureFamily::Unknown;
}

class TargetFeatureGate {
public:
    static TargetFeatureGate from_target_info(const TargetInfo& target) {
        if (!target.triple.empty()) {
            if (auto family = tf_family_from_triple(target.triple)) {
                return TargetFeatureGate(*family);
            }
        }
        return TargetFeatureGate(tf_family_from_arch(target.arch));
    }

    static TargetFeatureGate from_driver_args(int argc, char** argv, std::string_view default_triple) {
        std::optional<TargetFeatureFamily> family;

        for (int i = 1; i < argc; ++i) {
            std::string arg = argv[i];
            if (arg.empty()) continue;
            if (arg == "--target" || arg == "-target") {
                if (i + 1 < argc) {
                    family = tf_family_from_triple(argv[i + 1]);
                    ++i;
                }
                continue;
            }
            if (tf_starts_with(arg, "--target=")) {
                family = tf_family_from_triple(arg.substr(std::string("--target=").size()));
                continue;
            }
            if (tf_starts_with(arg, "-target=")) {
                family = tf_family_from_triple(arg.substr(std::string("-target=").size()));
                continue;
            }
            if (arg == "-arch" && i + 1 < argc) {
                family = tf_family_from_arch_name(argv[i + 1]);
                ++i;
                continue;
            }
        }

        if (!family.has_value()) {
            family = tf_family_from_triple(default_triple);
        }
        return TargetFeatureGate(family.value_or(TargetFeatureFamily::Unknown));
    }

    TargetFeatureFamily family() const {
        return family_;
    }

    bool supports(TargetFeatureFamily feature_family) const {
        return feature_family == TargetFeatureFamily::Unknown || feature_family == family_;
    }

    bool is_builtin_available(std::string_view builtin_name) const {
        if (tf_starts_with(builtin_name, "__builtin_altivec_") ||
            tf_starts_with(builtin_name, "__builtin_vsx_")) {
            return supports(TargetFeatureFamily::Ppc);
        }
        if (builtin_name == "__builtin_ia32_bzhi_si") {
            return supports(TargetFeatureFamily::X86);
        }
        return true;
    }

    bool should_strip_compat_flag(std::string_view arg,
                                  std::optional<std::string_view> next_arg,
                                  bool& consume_next_arg) const {
        consume_next_arg = false;
        auto family = classify_arch_feature_flag(arg, next_arg, consume_next_arg);
        if (!family.has_value()) {
            return false;
        }
        return !supports(*family);
    }

private:
    explicit TargetFeatureGate(TargetFeatureFamily family) : family_(family) {}

    std::optional<TargetFeatureFamily> classify_arch_feature_flag(
        std::string_view arg,
        std::optional<std::string_view> next_arg,
        bool& consume_next_arg) const {
        const std::string lowered = tf_to_lower(arg);

        auto is_altivec_abi_value = [](std::string_view value) {
            std::string lowered_value = tf_to_lower(value);
            return lowered_value == "altivec" || lowered_value == "no-altivec";
        };

        if (lowered == "-maltivec" || lowered == "-mno-altivec" ||
            lowered == "-mvsx" || lowered == "-mno-vsx" ||
            tf_starts_with(lowered, "-maltivec=") || tf_starts_with(lowered, "-mvsx=") ||
            lowered == "-faltivec" || lowered == "-fno-altivec") {
            return TargetFeatureFamily::Ppc;
        }
        if (tf_starts_with(lowered, "-mabi=")) {
            const std::string_view abi = std::string_view(lowered).substr(std::string("-mabi=").size());
            if (is_altivec_abi_value(abi)) {
                return TargetFeatureFamily::Ppc;
            }
        }
        if (lowered == "-mabi" && next_arg.has_value() && is_altivec_abi_value(*next_arg)) {
            consume_next_arg = true;
            return TargetFeatureFamily::Ppc;
        }

        if (tf_starts_with(lowered, "-msse") || tf_starts_with(lowered, "-mno-sse") ||
            tf_starts_with(lowered, "-mavx") || tf_starts_with(lowered, "-mno-avx") ||
            tf_starts_with(lowered, "-mxop") || tf_starts_with(lowered, "-mno-xop") ||
            tf_starts_with(lowered, "-mfma") || tf_starts_with(lowered, "-mno-fma") ||
            tf_starts_with(lowered, "-m3dnow") || tf_starts_with(lowered, "-mno-3dnow") ||
            lowered == "-maes" || lowered == "-mno-aes" ||
            lowered == "-mpclmul" || lowered == "-mno-pclmul") {
            return TargetFeatureFamily::X86;
        }

        if (lowered == "-mfpu" && next_arg.has_value()) {
            consume_next_arg = true;
            return TargetFeatureFamily::Arm;
        }
        if (tf_starts_with(lowered, "-mfpu=") ||
            lowered == "-mneon" || lowered == "-mno-neon" ||
            lowered == "-msve" || lowered == "-mno-sve") {
            return TargetFeatureFamily::Arm;
        }

        if (tf_starts_with(lowered, "-march=rv")) {
            if (lowered.find('v') != std::string::npos) {
                return TargetFeatureFamily::Riscv;
            }
        }
        if (lowered == "-march" && next_arg.has_value()) {
            std::string lowered_next = tf_to_lower(*next_arg);
            if (tf_starts_with(lowered_next, "rv") && lowered_next.find('v') != std::string::npos) {
                consume_next_arg = true;
                return TargetFeatureFamily::Riscv;
            }
        }

        return std::nullopt;
    }

    TargetFeatureFamily family_ = TargetFeatureFamily::Unknown;
};

#endif // ABURI_TARGET_FEATURE_GATE_H
