#ifndef ABURI_CONSTEVAL_RESULT_H
#define ABURI_CONSTEVAL_RESULT_H

#include <cstdint>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "const_value.h"
#include "consteval_diag.h"

enum class ConstEvalStatus {
    NotEvaluated,
    Constant,
    Dependent,
    NotConstant,
    Unsupported,
    Error
};

struct ConstEvalResult {
    ConstEvalStatus status = ConstEvalStatus::NotEvaluated;
    std::optional<ConstValue> value = std::nullopt;
    aburi::cir::EntityId dependency_entity{};
    std::vector<ConstEvalDiagnostic> diagnostics;
    std::string message;

    static ConstEvalResult not_evaluated(std::string why = "") {
        ConstEvalResult result;
        result.status = ConstEvalStatus::NotEvaluated;
        result.message = std::move(why);
        return result;
    }

    static ConstEvalResult constant(int64_t value) {
        ConstEvalResult result;
        result.status = ConstEvalStatus::Constant;
        result.value = ConstValue::integer(ConstIntValue::from_signed(value, 64));
        return result;
    }

    static ConstEvalResult constant(ConstValue value) {
        ConstEvalResult result;
        result.status = ConstEvalStatus::Constant;
        result.value = std::move(value);
        return result;
    }

    static ConstEvalResult not_constant(std::string why = "") {
        ConstEvalResult result;
        result.status = ConstEvalStatus::NotConstant;
        result.message = std::move(why);
        return result;
    }

    static ConstEvalResult dependent(std::string why = "") {
        ConstEvalResult result;
        result.status = ConstEvalStatus::Dependent;
        result.message = std::move(why);
        return result;
    }

    static ConstEvalResult unsupported(std::string why,
        ConstEvalDiagCode code = ConstEvalDiagCode::UnsupportedExpression,
        SrcLoc loc = SrcLoc()) {
        ConstEvalResult result;
        result.status = ConstEvalStatus::Unsupported;
        result.message = std::move(why);
        result.diagnostics.push_back(ConstEvalDiagnostic::make(code, result.message, loc));
        return result;
    }

    static ConstEvalResult error(std::string why,
        ConstEvalDiagCode code = ConstEvalDiagCode::None, SrcLoc loc = SrcLoc()) {
        ConstEvalResult result;
        result.status = ConstEvalStatus::Error;
        result.message = std::move(why);
        result.diagnostics.push_back(ConstEvalDiagnostic::make(code, result.message, loc));
        return result;
    }

};

#endif // ABURI_CONSTEVAL_RESULT_H
