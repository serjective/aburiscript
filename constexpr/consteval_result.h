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
    NotConstant,
    Error
};

struct ConstEvalResult {
    ConstEvalStatus status = ConstEvalStatus::NotEvaluated;
    std::optional<ConstValue> value = std::nullopt;
    // Compatibility field during migration while old callsites still expect int.
    std::optional<int64_t> int_value = std::nullopt;
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
        result.int_value = value;
        return result;
    }

    static ConstEvalResult constant(ConstValue value) {
        ConstEvalResult result;
        result.status = ConstEvalStatus::Constant;
        result.int_value = value.try_as_int64();
        result.value = std::move(value);
        return result;
    }

    static ConstEvalResult not_constant(std::string why = "") {
        ConstEvalResult result;
        result.status = ConstEvalStatus::NotConstant;
        result.message = std::move(why);
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

    bool has_int_value() const {
        return status == ConstEvalStatus::Constant && int_value.has_value();
    }
};

#endif // ABURI_CONSTEVAL_RESULT_H
