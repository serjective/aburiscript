#include "elf_unwind.h"

#include "target.h"

namespace aburi::backend::aarch64 {

namespace {

constexpr uint8_t DW_CFA_advance_loc = 0x40;
constexpr uint8_t DW_CFA_offset = 0x80;
constexpr uint8_t DW_CFA_nop = 0x00;
constexpr uint8_t DW_CFA_advance_loc1 = 0x02;
constexpr uint8_t DW_CFA_advance_loc2 = 0x03;
constexpr uint8_t DW_CFA_advance_loc4 = 0x04;
constexpr uint8_t DW_CFA_def_cfa = 0x0C;

constexpr uint8_t DW_EH_PE_pcrel_sdata4 = 0x1B;
constexpr uint8_t DW_EH_PE_indirect_pcrel_sdata4 = 0x9B;

constexpr int64_t kCodeAlignment = 4;
constexpr int64_t kDataAlignment = -8;
constexpr uint64_t kReturnAddressColumn = 30;

uint64_t dwarf_register(uint32_t phys) {
    return is_fpr_index(phys) ? 64 + (phys - V0) : phys;
}

void append_advance(std::vector<uint8_t>& out, uint64_t delta_bytes) {
    uint64_t units = delta_bytes / static_cast<uint64_t>(kCodeAlignment);
    if (units == 0) {
        return;
    }
    if (units < 64) {
        append_u8(out, static_cast<uint8_t>(DW_CFA_advance_loc | units));
    } else if (units <= 0xFF) {
        append_u8(out, DW_CFA_advance_loc1);
        append_u8(out, static_cast<uint8_t>(units));
    } else if (units <= 0xFFFF) {
        append_u8(out, DW_CFA_advance_loc2);
        append_u8(out, static_cast<uint8_t>(units));
        append_u8(out, static_cast<uint8_t>(units >> 8));
    } else {
        append_u8(out, DW_CFA_advance_loc4);
        append_u32(out, static_cast<uint32_t>(units));
    }
}

void append_saved_register(std::vector<uint8_t>& out, uint32_t phys,
                           int64_t cfa_offset) {
    uint64_t number = dwarf_register(phys);
    uint64_t factored =
        static_cast<uint64_t>(cfa_offset / kDataAlignment);
    if (number < 64) {
        append_u8(out, static_cast<uint8_t>(DW_CFA_offset | number));
    } else {

        append_u8(out, 0x05);
        append_uleb(out, number);
    }
    append_uleb(out, factored);
}

void pad_to_multiple(std::vector<uint8_t>& out, size_t start,
                     size_t alignment) {
    while ((out.size() - start) % alignment != 0) {
        append_u8(out, DW_CFA_nop);
    }
}

} // namespace

uint64_t append_eh_frame_cie(std::vector<uint8_t>& eh_frame,
                             bool with_personality,
                             uint64_t& personality_offset_out) {
    uint64_t cie_offset = eh_frame.size();
    size_t length_slot = eh_frame.size();
    append_u32(eh_frame, 0);
    size_t body_start = eh_frame.size();

    append_u32(eh_frame, 0);
    append_u8(eh_frame, 1);

    const char* augmentation = with_personality ? "zPLR" : "zR";
    for (const char* c = augmentation; *c != '\0'; ++c) {
        append_u8(eh_frame, static_cast<uint8_t>(*c));
    }
    append_u8(eh_frame, 0);

    append_uleb(eh_frame, static_cast<uint64_t>(kCodeAlignment));
    append_sleb(eh_frame, kDataAlignment);
    append_uleb(eh_frame, kReturnAddressColumn);

    std::vector<uint8_t> augmentation_data;
    uint64_t personality_slot = 0;
    if (with_personality) {
        append_u8(augmentation_data, DW_EH_PE_indirect_pcrel_sdata4);
        personality_slot = augmentation_data.size();
        append_u32(augmentation_data, 0);
        append_u8(augmentation_data, DW_EH_PE_pcrel_sdata4); // LSDA
    }
    append_u8(augmentation_data, DW_EH_PE_pcrel_sdata4);
    append_uleb(eh_frame, augmentation_data.size());
    uint64_t augmentation_base = eh_frame.size();
    eh_frame.insert(eh_frame.end(), augmentation_data.begin(),
                    augmentation_data.end());
    personality_offset_out =
        with_personality ? augmentation_base + personality_slot : 0;

    append_u8(eh_frame, DW_CFA_def_cfa);
    append_uleb(eh_frame, SP);
    append_uleb(eh_frame, 0);

    pad_to_multiple(eh_frame, body_start, 4);
    uint32_t length = static_cast<uint32_t>(eh_frame.size() - body_start);
    for (int i = 0; i < 4; ++i) {
        eh_frame[length_slot + i] = static_cast<uint8_t>(length >> (8 * i));
    }
    return cie_offset;
}

void append_eh_frame_fde(std::vector<uint8_t>& eh_frame, uint64_t cie_offset,
                         const EhFrameFunction& function,
                         uint64_t& pc_offset_out, uint64_t& lsda_offset_out) {
    size_t length_slot = eh_frame.size();
    append_u32(eh_frame, 0);
    size_t body_start = eh_frame.size();

    append_u32(eh_frame,
               static_cast<uint32_t>(body_start - cie_offset));

    pc_offset_out = eh_frame.size();
    append_u32(eh_frame, 0);
    append_u32(eh_frame, static_cast<uint32_t>(function.size));

    append_uleb(eh_frame, 4);
    lsda_offset_out = eh_frame.size();
    append_u32(eh_frame, 0);
    if (!function.has_lsda) {
        lsda_offset_out = 0;
    }

    if (function.has_frame) {
        append_advance(eh_frame, function.frame_setup_offset - function.start);
        append_u8(eh_frame, DW_CFA_def_cfa);
        append_uleb(eh_frame, X29);
        append_uleb(eh_frame, 16);
        append_saved_register(eh_frame, X30, -8);
        append_saved_register(eh_frame, X29, -16);
        for (const auto& [phys, cfa_offset] : function.saved_registers) {
            append_saved_register(eh_frame, phys, cfa_offset);
        }
    }

    pad_to_multiple(eh_frame, body_start, 4);
    uint32_t length = static_cast<uint32_t>(eh_frame.size() - body_start);
    for (int i = 0; i < 4; ++i) {
        eh_frame[length_slot + i] = static_cast<uint8_t>(length >> (8 * i));
    }
}

} // namespace aburi::backend::aarch64
