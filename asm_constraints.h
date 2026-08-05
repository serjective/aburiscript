#ifndef ABURI_ASM_CONSTRAINTS_H
#define ABURI_ASM_CONSTRAINTS_H

#include <string>
#include <string_view>

#include "abi/target_info.h"

namespace aburi {

enum class AsmLetterClass : uint8_t {
    GeneralReg,
    SpecificReg,
    FpReg,
    Memory,
    Immediate,
    Any,
    Unknown,
};

inline AsmLetterClass classify_asm_letter(TargetArch arch, char letter) {
    switch (letter) {
        case 'r': return AsmLetterClass::GeneralReg;
        case 'g':
        case 'X': return AsmLetterClass::Any;
        case 'i':
        case 'n':
        case 's': return AsmLetterClass::Immediate;
        case 'm':
        case 'o':
        case 'V':
        case 'p': return AsmLetterClass::Memory;
        default: break;
    }
    if (arch == TargetArch::X86_64 || arch == TargetArch::X86) {
        switch (letter) {
            case 'a': case 'b': case 'c': case 'd':
            case 'S': case 'D': case 'q': case 'Q': case 'R': case 'A':
                return AsmLetterClass::SpecificReg;
            case 'x': case 'y': case 'v': case 't': case 'u': case 'f':
                return AsmLetterClass::FpReg;
            case 'I': case 'J': case 'K': case 'L': case 'M': case 'N':
            case 'O': case 'e': case 'Z': case 'G': case 'C':
                return AsmLetterClass::Immediate;
            default: break;
        }
        return AsmLetterClass::Unknown;
    }
    if (arch == TargetArch::AARCH64 || arch == TargetArch::ARM32) {
        switch (letter) {
            case 'w': case 'x': case 'y':
                return AsmLetterClass::FpReg;
            case 'I': case 'J': case 'K': case 'L': case 'M': case 'N':
                return AsmLetterClass::Immediate;
            case 'Q':
                return AsmLetterClass::Memory;
            case 'S':
                return AsmLetterClass::Immediate;
            default: break;
        }
        return AsmLetterClass::Unknown;
    }
    return AsmLetterClass::Unknown;
}

inline bool asm_letter_is_memory(TargetArch arch, char letter) {
    return classify_asm_letter(arch, letter) == AsmLetterClass::Memory;
}

namespace detail {

inline bool is_reg_number(std::string_view digits, unsigned max) {
    if (digits.empty() || digits.size() > 2) {
        return false;
    }
    unsigned value = 0;
    for (char c : digits) {
        if (c < '0' || c > '9') {
            return false;
        }
        value = value * 10 + static_cast<unsigned>(c - '0');
    }
    if (digits.size() == 2 && digits[0] == '0') {
        return false;
    }
    return value <= max;
}

} // namespace detail

inline bool asm_valid_clobber(TargetArch arch, std::string_view name) {
    if (name == "memory" || name == "cc") {
        return true;
    }
    if (arch == TargetArch::AARCH64) {
        if (name == "lr" || name == "fp" || name == "sp" ||
            name == "xzr" || name == "wzr" || name == "nzcv" ||
            name == "fpsr" || name == "fpcr") {
            return true;
        }
        if (name.size() >= 2) {
            char kind = name[0];
            std::string_view digits = name.substr(1);
            if ((kind == 'x' || kind == 'w' || kind == 'r') &&
                detail::is_reg_number(digits, 30)) {
                return true;
            }
            if ((kind == 'v' || kind == 'q' || kind == 'd' || kind == 's' ||
                 kind == 'h' || kind == 'b') &&
                detail::is_reg_number(digits, 31)) {
                return true;
            }
        }
        return false;
    }
    if (arch == TargetArch::X86_64 || arch == TargetArch::X86) {
        static constexpr std::string_view named[] = {
            "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "rsp",
            "eax", "ebx", "ecx", "edx", "esi", "edi", "ebp", "esp",
            "ax",  "bx",  "cx",  "dx",  "si",  "di",  "bp",  "sp",
            "al",  "bl",  "cl",  "dl",  "ah",  "bh",  "ch",  "dh",
            "st",  "flags", "dirflag", "fpsr", "fpcr",
        };
        for (std::string_view candidate : named) {
            if (name == candidate) {
                return true;
            }
        }
        if (name.size() >= 2 && name[0] == 'r' &&
            detail::is_reg_number(name.substr(1), 15)) {
            return true;
        }
        if (name.size() > 3 &&
            (name.substr(0, 3) == "xmm" || name.substr(0, 3) == "ymm" ||
             name.substr(0, 3) == "zmm") &&
            detail::is_reg_number(name.substr(3), 31)) {
            return true;
        }
        if (name.size() > 2 && name.substr(0, 2) == "mm" &&
            detail::is_reg_number(name.substr(2), 7)) {
            return true;
        }
        if (name.size() == 5 && name.substr(0, 3) == "st(" &&
            name[4] == ')' && name[3] >= '0' && name[3] <= '7') {
            return true;
        }
        return false;
    }

    return true;
}

inline std::string normalize_asm_register_name(TargetArch arch,
                                               std::string reg,
                                               unsigned operand_bits) {
    if (arch != TargetArch::AARCH64 || reg.size() < 2) {
        return reg;
    }
    if (reg[0] != 'r' && reg[0] != 'x' && reg[0] != 'w') {
        return reg;
    }
    std::string digits = reg.substr(1);
    if (!detail::is_reg_number(digits, 30)) {
        return reg;
    }
    int number = std::atoi(digits.c_str());
    if (number == 30) {
        return "lr";
    }
    if (number == 29) {
        return "fp";
    }
    if (reg[0] == 'r') {
        return (operand_bits > 32 ? "x" : "w") + digits;
    }
    return reg;
}

} // namespace aburi

#endif // ABURI_ASM_CONSTRAINTS_H
