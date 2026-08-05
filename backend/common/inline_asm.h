#ifndef ABURI_BACKEND_COMMON_INLINE_ASM_H
#define ABURI_BACKEND_COMMON_INLINE_ASM_H

#include <cstdlib>
#include <string>

namespace aburi::backend {

enum class AsmOperandRole : uint8_t {
    Input,
    Output,
    ReadWriteOutput,
};

enum class AsmOperandKind : uint8_t {
    Register,
    Immediate,
    Memory,
    Tied,
    Unsupported,
};

struct AsmConstraint {
    AsmOperandRole role = AsmOperandRole::Input;
    AsmOperandKind kind = AsmOperandKind::Register;
    char letter = 'r';
    int tied_output = -1;
    bool ok = true;
    std::string error;
};

inline AsmConstraint parse_asm_constraint(const std::string& raw) {
    AsmConstraint result;
    std::string c = raw;
    if (!c.empty() && c[0] == '=') {
        result.role = AsmOperandRole::Output;
        c.erase(0, 1);
    } else if (!c.empty() && c[0] == '+') {
        result.role = AsmOperandRole::ReadWriteOutput;
        c.erase(0, 1);
    }

    if (!c.empty() && c[0] == '&') {
        c.erase(0, 1);
    }
    if (!c.empty() &&
        c.find_first_not_of("0123456789") == std::string::npos) {
        result.kind = AsmOperandKind::Tied;
        result.tied_output = std::atoi(c.c_str());
        return result;
    }
    if (c.size() != 1) {
        result.ok = false;
        result.error = "unsupported asm constraint '" + raw + "'";
        return result;
    }
    char letter = c[0];
    switch (letter) {
        case 'a': case 'b': case 'c': case 'd': case 'S': case 'D':
        case 'r':
        case 'w': case 'x':
            result.kind = AsmOperandKind::Register;
            result.letter = letter;
            return result;
        case 'i': case 'n':
            result.kind = AsmOperandKind::Immediate;
            return result;
        case 'm':
            result.kind = AsmOperandKind::Memory;
            return result;
        default:
            result.ok = false;
            result.error = "unsupported asm constraint '" + raw + "'";
            return result;
    }
}

} // namespace aburi::backend

#endif // ABURI_BACKEND_COMMON_INLINE_ASM_H
