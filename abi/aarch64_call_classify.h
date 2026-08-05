#ifndef ABURI_ABI_AARCH64_CALL_CLASSIFY_H
#define ABURI_ABI_AARCH64_CALL_CLASSIFY_H

#include <cstdint>

#include "../cir/file.h"
#include "call_classify.h"
#include "target_info.h"

namespace aburi::abi {

AggregateClass classify_aarch64_argument(const cir::File& file,
                                         cir::TypeRef type,
                                         const TargetInfo* target);

AggregateClass classify_aarch64_vararg(const cir::File& file,
                                       cir::TypeRef type,
                                       const TargetInfo* target);

AggregateClass classify_aarch64_argument_native(const cir::File& file,
                                                cir::TypeRef type,
                                                const TargetInfo* target);
AggregateClass classify_aarch64_vararg_native(const cir::File& file,
                                              cir::TypeRef type,
                                              const TargetInfo* target);

bool is_complete_record_type(const cir::File& file, cir::TypeId type_id);

bool is_empty_record_abi_ignored(const cir::File& file, cir::TypeId type_id);

bool collect_hfa_members(const cir::File& file,
                         const TargetInfo& target,
                         cir::TypeRef type,
                         cir::BuiltinTypeKind& element_kind,
                         unsigned& element_count);

} // namespace aburi::abi

#endif // ABURI_ABI_AARCH64_CALL_CLASSIFY_H
