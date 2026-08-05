#ifndef ABURI_BACKEND_AARCH64_ENCODE_H
#define ABURI_BACKEND_AARCH64_ENCODE_H

#include <cstdint>
#include <string>

#include "../common/mir.h"

namespace aburi::backend::aarch64 {

enum class TextFixup : uint8_t {
    None,
    SymBranch26,
    SymPage21,
    SymPageOff12,
    LabelBranch26,
    LabelBranch19,
};

struct EncodedInst {
    bool ok = false;
    std::string error;
    uint32_t word = 0;
    TextFixup fixup = TextFixup::None;
    uint32_t fixup_operand = 0;
    uint32_t fixup_label = 0;
};

EncodedInst encode_a64(const MInst& inst);

uint32_t patch_branch26(uint32_t word, int64_t byte_displacement);
uint32_t patch_branch19(uint32_t word, int64_t byte_displacement);

} // namespace aburi::backend::aarch64

#endif // ABURI_BACKEND_AARCH64_ENCODE_H
