#ifndef ABURI_CONSTEVAL_COMPAT_H
#define ABURI_CONSTEVAL_COMPAT_H

#include <cstdint>
#include <optional>

#include "consteval_mode.h"
#include "consteval_result.h"

struct Expr;

ConstEvalResult evaluate_with_consteval_compat(
    Expr* expr,
    ConstEvalMode mode = ConstEvalMode::c_ice());

std::optional<int64_t> try_evaluate_with_consteval_compat(
    Expr* expr,
    ConstEvalMode mode = ConstEvalMode::c_ice());

#endif // ABURI_CONSTEVAL_COMPAT_H
