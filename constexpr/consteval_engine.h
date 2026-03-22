#ifndef ABURI_CONSTEVAL_ENGINE_H
#define ABURI_CONSTEVAL_ENGINE_H

#include <utility>

#include "../lang_options.h"
#include "consteval_mode.h"
#include "consteval_result.h"

struct Expr;

// Stage-1 constexpr engine shell.
// Behavior is intentionally minimal and gated by LangOptions to keep
// all existing constant-evaluation behavior unchanged.
class ConstEvalEngine {
public:
    explicit ConstEvalEngine(LangOptions options = LangOptions())
        : lang_options_(std::move(options)) {}

    const LangOptions& lang_options() const {
        return lang_options_;
    }

    bool is_enabled() const {
        return lang_options_.enable_consteval_engine;
    }

    ConstEvalResult evaluate(const Expr* expr, ConstEvalMode mode) const;

private:
    LangOptions lang_options_;
};

#endif // ABURI_CONSTEVAL_ENGINE_H
