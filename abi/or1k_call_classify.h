#ifndef ABURI_ABI_OR1K_CALL_CLASSIFY_H
#define ABURI_ABI_OR1K_CALL_CLASSIFY_H

#include "call_classify.h"

namespace aburi::abi {

AggregateClass classify_or1k_argument_native(const cir::File& file,
                                             cir::TypeRef type,
                                             const TargetInfo* target);
AggregateClass classify_or1k_vararg_native(const cir::File& file,
                                           cir::TypeRef type,
                                           const TargetInfo* target);

} // namespace aburi::abi

#endif // ABURI_ABI_OR1K_CALL_CLASSIFY_H
