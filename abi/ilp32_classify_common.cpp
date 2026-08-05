#include "ilp32_classify_common.h"

#include <algorithm>

#include "../cir/layout.h"
#include "aarch64_call_classify.h"

namespace aburi::abi {

std::optional<Ilp32SizeAlign> aggregate_size_align(const cir::File& file,
                                                   cir::TypeId resolved) {
    if (!file.valid(resolved)) {
        return std::nullopt;
    }
    bool is_complex = file.type(resolved).kind == cir::TypeKind::Complex;
    if (!is_complex && !is_complete_record_type(file, resolved)) {
        return std::nullopt;
    }
    auto size_align = cir::size_align_of_type(file, resolved);
    if (!size_align) {
        return std::nullopt;
    }
    Ilp32SizeAlign out;
    out.size_bytes = size_align->size_bytes;
    out.align_bytes = static_cast<uint32_t>(
        std::max<size_t>(1, size_align->alignment_bytes));
    return out;
}

bool is_ignored_empty_record(const cir::File& file, cir::TypeId resolved) {
    return is_empty_record_abi_ignored(file, resolved);
}

AggregateClass coerce_word_slots(uint64_t size_bytes, uint32_t align_bytes) {
    AggregateClass result;
    result.pass = AggregatePass::CoerceIntSlots;
    result.slot_bytes = 4;
    result.int_slot_count =
        static_cast<uint8_t>(std::max<uint64_t>(1, (size_bytes + 3) / 4));
    result.byte_size = size_bytes;
    result.byte_align = std::max<uint32_t>(1, align_bytes);
    return result;
}

AggregateClass pass_indirect(uint64_t size_bytes, uint32_t align_bytes) {
    AggregateClass result;
    result.pass = AggregatePass::Indirect;
    result.byte_size = size_bytes;
    result.byte_align = std::max<uint32_t>(1, align_bytes);
    return result;
}

AggregateClass pass_memory_byval(uint64_t size_bytes, uint32_t align_bytes) {
    AggregateClass result;
    result.pass = AggregatePass::MemoryByval;
    result.byte_size = size_bytes;
    result.byte_align = std::max<uint32_t>(1, align_bytes);
    return result;
}

} // namespace aburi::abi
