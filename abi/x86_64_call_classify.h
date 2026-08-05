#ifndef ABURI_ABI_X86_64_CALL_CLASSIFY_H
#define ABURI_ABI_X86_64_CALL_CLASSIFY_H

#include "call_classify.h"

namespace aburi::abi {

AggregateClass classify_x86_64_argument_native(const cir::File& file,
                                               cir::TypeRef type,
                                               const TargetInfo* target);

AggregateClass classify_x86_64_vararg_native(const cir::File& file,
                                             cir::TypeRef type,
                                             const TargetInfo* target);

} // namespace aburi::abi

#endif // ABURI_ABI_X86_64_CALL_CLASSIFY_H
