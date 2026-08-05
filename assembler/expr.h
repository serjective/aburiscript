#ifndef ABURI_ASSEMBLER_EXPR_H
#define ABURI_ASSEMBLER_EXPR_H

#include <cstdint>
#include <string>
#include <string_view>

#include "lexer.h"
#include "symbols.h"

namespace aburi::assembler {

struct ExprValue {
    bool ok = false;
    int64_t constant = 0;
    SymId pos_sym = no_sym;
    SymId neg_sym = no_sym;

    bool is_absolute() const {
        return ok && pos_sym == no_sym && neg_sym == no_sym;
    }

    static ExprValue absolute(int64_t value) {
        ExprValue result;
        result.ok = true;
        result.constant = value;
        return result;
    }

    static ExprValue failed() { return ExprValue{}; }
};

class ExprContext {
public:
    virtual ~ExprContext() = default;

    virtual SymId expr_symbol(std::string_view name) = 0;
    virtual SymId expr_here() = 0;
    virtual SymId expr_local_ref(uint32_t number, bool backward, uint32_t line,
                                 uint32_t col) = 0;
    virtual bool expr_constant_value(SymId id, int64_t& out) const = 0;
    virtual void expr_error(uint32_t line, uint32_t col,
                            const std::string& message) = 0;
};

ExprValue parse_expression(Lexer& lexer, ExprContext& context);

}

#endif
