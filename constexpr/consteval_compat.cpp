#include "consteval_compat.h"

#include "../lang_options.h"
#include "consteval_engine.h"

ConstEvalResult evaluate_with_consteval_compat(Expr* expr, ConstEvalMode mode) {
    if (!expr) {
        return ConstEvalResult::not_evaluated("null expression");
    }

    LangOptions options;
    options.enable_consteval_engine = true;
    ConstEvalEngine engine(options);
    return engine.evaluate(expr, mode);
}

std::optional<int64_t> try_evaluate_with_consteval_compat(Expr* expr, ConstEvalMode mode) {
    ConstEvalResult result = evaluate_with_consteval_compat(expr, mode);
    if (result.status == ConstEvalStatus::Constant && result.int_value.has_value()) {
        return result.int_value.value();
    }

    return std::nullopt;
}
