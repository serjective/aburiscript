#ifndef ABURI_BACKEND_X86_ENCODE_H
#define ABURI_BACKEND_X86_ENCODE_H

#include <cstdint>
#include <string>

#include "../common/mir.h"

namespace aburi::backend::x86 {

enum class TextFixup : uint8_t {
    None,
    SymBranch32,
    SymRip32,
    LabelRel32,
};

struct EncodedInst {
    bool ok = true;
    std::string error;
    uint8_t bytes[16] = {};
    uint8_t size = 0;
    TextFixup fixup = TextFixup::None;
    uint8_t fixup_offset = 0;
    uint8_t fixup_operand = 0;
    uint32_t fixup_label = 0;
};

EncodedInst encode_x86(const MInst& inst);

} // namespace aburi::backend::x86

#endif // ABURI_BACKEND_X86_ENCODE_H
