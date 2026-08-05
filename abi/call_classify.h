#ifndef ABURI_ABI_CALL_CLASSIFY_H
#define ABURI_ABI_CALL_CLASSIFY_H

#include <cstdint>

#include "../cir/file.h"
#include "target_info.h"

namespace aburi::abi {

enum class AggregatePass : uint8_t {
    UseSourceType,
    Ignore,
    CoerceHfa,
    CoerceIntSlots,
    CoerceClassedSlots,
    Indirect,
    MemoryByval,
};

struct AggregateClass {
    AggregatePass pass = AggregatePass::UseSourceType;
    cir::BuiltinTypeKind hfa_element = cir::BuiltinTypeKind::Other;
    uint8_t hfa_count = 0;
    uint8_t int_slot_count = 0;
    uint8_t slot_bytes = 8;
    uint8_t sse_slot_mask = 0;
    uint64_t byte_size = 0;
    uint32_t byte_align = 1;
};

AggregateClass classify_argument_native(const cir::File& file,
                                        cir::TypeRef type,
                                        const TargetInfo* target);
AggregateClass classify_vararg_native(const cir::File& file,
                                      cir::TypeRef type,
                                      const TargetInfo* target);

} // namespace aburi::abi

#endif // ABURI_ABI_CALL_CLASSIFY_H
