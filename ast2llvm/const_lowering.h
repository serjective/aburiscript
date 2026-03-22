#ifndef ABURI_CONST_LOWERING_H
#define ABURI_CONST_LOWERING_H

#include "../constexpr/consteval_mode.h"

struct Expr;

namespace llvm {
class Constant;
class Type;
}

// Lowers frontend consteval results into LLVM constants for global/static
// initializer contexts. Returns nullptr when consteval cannot produce a
// supported constant for the requested target type.
llvm::Constant* lower_consteval_to_llvm_constant(
    Expr* expr,
    llvm::Type* target_type,
    bool target_is_unsigned,
    ConstEvalMode mode = ConstEvalMode::c_static_initializer());

#endif // ABURI_CONST_LOWERING_H
