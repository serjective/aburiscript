#ifndef ABURI_BACKEND_AARCH64_ELF_UNWIND_H
#define ABURI_BACKEND_AARCH64_ELF_UNWIND_H

#include <cstdint>
#include <string>
#include <vector>

#include "../common/elf.h"
#include "../common/mir.h"

namespace aburi::backend::aarch64 {

inline void append_u8(std::vector<uint8_t>& out, uint8_t value) {
    out.push_back(value);
}

inline void append_u32(std::vector<uint8_t>& out, uint32_t value) {
    for (int i = 0; i < 4; ++i) {
        out.push_back(static_cast<uint8_t>(value >> (8 * i)));
    }
}

inline void append_uleb(std::vector<uint8_t>& out, uint64_t value) {
    do {
        uint8_t byte = static_cast<uint8_t>(value & 0x7F);
        value >>= 7;
        out.push_back(value != 0 ? (byte | 0x80) : byte);
    } while (value != 0);
}

inline void append_sleb(std::vector<uint8_t>& out, int64_t value) {
    bool more = true;
    while (more) {
        uint8_t byte = static_cast<uint8_t>(value & 0x7F);
        bool sign = (byte & 0x40) != 0;
        value >>= 7;
        more = !((value == 0 && !sign) || (value == -1 && sign));
        out.push_back(more ? (byte | 0x80) : byte);
    }
}

inline size_t uleb_size(uint64_t value) {
    size_t size = 0;
    do {
        value >>= 7;
        ++size;
    } while (value != 0);
    return size;
}

struct EhFrameFunction {
    uint64_t start = 0;
    uint64_t size = 0;
    bool has_lsda = false;
    uint64_t lsda_offset = 0;
    uint64_t frame_setup_offset = 0;
    bool has_frame = false;
    std::vector<std::pair<uint32_t, int64_t>> saved_registers;
};

uint64_t append_eh_frame_cie(std::vector<uint8_t>& eh_frame,
                             bool with_personality,
                             uint64_t& personality_offset_out);

void append_eh_frame_fde(std::vector<uint8_t>& eh_frame, uint64_t cie_offset,
                         const EhFrameFunction& function,
                         uint64_t& pc_offset_out, uint64_t& lsda_offset_out);

} // namespace aburi::backend::aarch64

#endif // ABURI_BACKEND_AARCH64_ELF_UNWIND_H
