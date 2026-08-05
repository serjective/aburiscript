#ifndef ABURI_NUMERIC_FLOATING_CIR_H
#define ABURI_NUMERIC_FLOATING_CIR_H

#include "floating_point.h"
#include "../cir/ids.h"

struct TargetInfo;

namespace aburi::cir {
class File;
enum class BuiltinTypeKind : uint16_t;
}

namespace aburi::floating {

numeric::FloatFormat semantics_for_type(const cir::File& file,
                                        cir::TypeId type);
numeric::FloatFormat semantics_for_builtin(cir::BuiltinTypeKind kind,
                                           const TargetInfo& target);

} // namespace aburi::floating

#endif // ABURI_NUMERIC_FLOATING_CIR_H
