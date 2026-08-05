#ifndef ABURI_ABI_ILP32_CLASSIFY_COMMON_H
#define ABURI_ABI_ILP32_CLASSIFY_COMMON_H

#include <cstdint>
#include <optional>

#include "call_classify.h"

namespace aburi::abi {

struct Ilp32SizeAlign {
    uint64_t size_bytes = 0;
    uint32_t align_bytes = 1;
};

std::optional<Ilp32SizeAlign> aggregate_size_align(const cir::File& file,
                                                   cir::TypeId resolved);

bool is_ignored_empty_record(const cir::File& file, cir::TypeId resolved);

AggregateClass coerce_word_slots(uint64_t size_bytes, uint32_t align_bytes);

AggregateClass pass_indirect(uint64_t size_bytes, uint32_t align_bytes);

AggregateClass pass_memory_byval(uint64_t size_bytes, uint32_t align_bytes);

} // namespace aburi::abi

#endif // ABURI_ABI_ILP32_CLASSIFY_COMMON_H
