#ifndef ABURI_CONSTEVAL_DIAG_H
#define ABURI_CONSTEVAL_DIAG_H

#include <string>
#include <utility>

#include "../source_mgnt.h"

enum class ConstEvalDiagCode {
    None,
    EngineDisabled,
    NullExpression,
    EvaluationNotImplemented,
    UnsupportedExpression,
    StepLimitExceeded,
    RecursionLimitExceeded,
    DivisionByZero,
    InvalidShiftAmount,
    InvalidDeallocation,
    DynamicAllocationLeaked,
    DynamicAllocationEscaped
};

struct ConstEvalDiagnostic {
    ConstEvalDiagCode code = ConstEvalDiagCode::None;
    std::string message;
    SrcLoc loc = SrcLoc();

    static ConstEvalDiagnostic make(ConstEvalDiagCode code, std::string message, SrcLoc loc = SrcLoc()) {
        ConstEvalDiagnostic diag;
        diag.code = code;
        diag.message = std::move(message);
        diag.loc = loc;
        return diag;
    }
};

#endif // ABURI_CONSTEVAL_DIAG_H
