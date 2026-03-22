#ifndef ABURI_PP_CONSTEVAL_H
#define ABURI_PP_CONSTEVAL_H

#include <cstdint>
#include <string>
#include <vector>

#include "../lexer.h"

struct PPConstEvalResult {
    bool ok = false;
    int64_t value = 0;
    std::string message;
    SrcLoc loc{};

    static PPConstEvalResult success(int64_t value);
    static PPConstEvalResult failure(std::string message, SrcLoc loc = SrcLoc());
};

PPConstEvalResult evaluate_pp_constant_expression(const std::vector<Token>& tokens);

#endif // ABURI_PP_CONSTEVAL_H
