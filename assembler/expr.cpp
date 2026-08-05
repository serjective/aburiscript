#include "expr.h"

namespace aburi::assembler {

namespace {

int binary_level(const Token& token) {
    if (token.kind == TokKind::LShift || token.kind == TokKind::RShift) {
        return 3;
    }
    if (token.kind != TokKind::Punct) {
        return 0;
    }
    switch (token.punct) {
        case '*':
        case '/':
        case '%':
            return 3;
        case '&':
        case '|':
        case '^':
            return 2;
        case '+':
        case '-':
            return 1;
        default:
            return 0;
    }
}

std::string op_spelling(const Token& token) {
    if (token.kind == TokKind::LShift) {
        return "<<";
    }
    if (token.kind == TokKind::RShift) {
        return ">>";
    }
    return std::string(1, token.punct);
}

ExprValue negate(ExprValue value) {
    value.constant = -value.constant;
    SymId pos = value.pos_sym;
    value.pos_sym = value.neg_sym;
    value.neg_sym = pos;
    return value;
}

ExprValue add(ExprContext& context, const Token& at, ExprValue lhs,
              ExprValue rhs) {
    if (rhs.pos_sym != no_sym && rhs.pos_sym == lhs.neg_sym) {
        lhs.neg_sym = no_sym;
        rhs.pos_sym = no_sym;
    }
    if (rhs.neg_sym != no_sym && rhs.neg_sym == lhs.pos_sym) {
        lhs.pos_sym = no_sym;
        rhs.neg_sym = no_sym;
    }
    if ((lhs.pos_sym != no_sym && rhs.pos_sym != no_sym) ||
        (lhs.neg_sym != no_sym && rhs.neg_sym != no_sym)) {
        context.expr_error(at.line, at.col,
                           "expression combines too many symbols to be "
                           "representable");
        return ExprValue::failed();
    }
    lhs.constant += rhs.constant;
    if (rhs.pos_sym != no_sym) {
        lhs.pos_sym = rhs.pos_sym;
    }
    if (rhs.neg_sym != no_sym) {
        lhs.neg_sym = rhs.neg_sym;
    }
    return lhs;
}

ExprValue apply_binary(ExprContext& context, const Token& op, ExprValue lhs,
                       ExprValue rhs) {
    if (op.kind == TokKind::Punct && op.punct == '+') {
        return add(context, op, lhs, rhs);
    }
    if (op.kind == TokKind::Punct && op.punct == '-') {
        return add(context, op, lhs, negate(rhs));
    }

    if (!lhs.is_absolute() || !rhs.is_absolute()) {
        context.expr_error(op.line, op.col,
                           "operator '" + op_spelling(op) +
                               "' requires absolute operands");
        return ExprValue::failed();
    }
    int64_t a = lhs.constant;
    int64_t b = rhs.constant;
    int64_t result = 0;
    if (op.kind == TokKind::LShift || op.kind == TokKind::RShift) {
        if (b < 0 || b > 63) {
            context.expr_error(op.line, op.col,
                               "shift amount is out of range");
            return ExprValue::failed();
        }
        uint64_t bits = static_cast<uint64_t>(a);
        result = op.kind == TokKind::LShift
                     ? static_cast<int64_t>(bits << b)
                     : static_cast<int64_t>(bits >> b);
        return ExprValue::absolute(result);
    }
    switch (op.punct) {
        case '*':
            result = a * b;
            break;
        case '/':
        case '%':
            if (b == 0) {
                context.expr_error(op.line, op.col, "division by zero");
                return ExprValue::failed();
            }
            result = op.punct == '/' ? a / b : a % b;
            break;
        case '&':
            result = a & b;
            break;
        case '|':
            result = a | b;
            break;
        case '^':
            result = a ^ b;
            break;
        default:
            context.expr_error(op.line, op.col, "unsupported operator");
            return ExprValue::failed();
    }
    return ExprValue::absolute(result);
}

class ExprParser {
public:
    ExprParser(Lexer& lexer, ExprContext& context)
        : lexer_(lexer), context_(context) {}

    ExprValue parse() { return parse_binary(1); }

private:
    ExprValue parse_binary(int min_level) {
        ExprValue lhs = parse_unary();
        if (!lhs.ok) {
            return lhs;
        }
        for (;;) {
            int level = binary_level(lexer_.peek());
            if (level == 0 || level < min_level) {
                return lhs;
            }
            Token op = lexer_.take();
            ExprValue rhs = parse_binary(level + 1);
            if (!rhs.ok) {
                return rhs;
            }
            lhs = apply_binary(context_, op, lhs, rhs);
            if (!lhs.ok) {
                return lhs;
            }
        }
    }

    ExprValue parse_unary() {
        const Token& token = lexer_.peek();
        if (token.kind == TokKind::Punct &&
            (token.punct == '-' || token.punct == '+' || token.punct == '~')) {
            Token op = lexer_.take();
            ExprValue operand = parse_unary();
            if (!operand.ok) {
                return operand;
            }
            if (op.punct == '+') {
                return operand;
            }
            if (op.punct == '-') {
                return negate(operand);
            }
            if (!operand.is_absolute()) {
                context_.expr_error(op.line, op.col,
                                    "operator '~' requires an absolute "
                                    "operand");
                return ExprValue::failed();
            }
            return ExprValue::absolute(~operand.constant);
        }
        return parse_primary();
    }

    ExprValue parse_primary() {
        const Token& token = lexer_.peek();
        switch (token.kind) {
            case TokKind::Integer: {
                Token literal = lexer_.take();
                return ExprValue::absolute(literal.value);
            }
            case TokKind::LocalRef: {
                Token ref = lexer_.take();
                SymId id = context_.expr_local_ref(
                    static_cast<uint32_t>(ref.value), ref.backward, ref.line,
                    ref.col);
                if (id == no_sym) {
                    return ExprValue::failed();
                }
                ExprValue value = ExprValue::absolute(0);
                value.pos_sym = id;
                return value;
            }
            case TokKind::Ident: {
                Token name = lexer_.take();
                if (name.text == ".") {
                    ExprValue value = ExprValue::absolute(0);
                    value.pos_sym = context_.expr_here();
                    return value;
                }
                SymId id = context_.expr_symbol(name.text);
                int64_t constant = 0;
                if (context_.expr_constant_value(id, constant)) {
                    return ExprValue::absolute(constant);
                }
                ExprValue value = ExprValue::absolute(0);
                value.pos_sym = id;
                return value;
            }
            case TokKind::Punct:
                if (token.punct == '(') {
                    lexer_.take();
                    ExprValue inner = parse_binary(1);
                    if (!inner.ok) {
                        return inner;
                    }
                    const Token& close = lexer_.peek();
                    if (close.kind != TokKind::Punct || close.punct != ')') {
                        context_.expr_error(close.line, close.col,
                                            "expected ')'");
                        return ExprValue::failed();
                    }
                    lexer_.take();
                    return inner;
                }
                break;
            default:
                break;
        }
        context_.expr_error(token.line, token.col,
                            "expected an expression operand");
        return ExprValue::failed();
    }

    Lexer& lexer_;
    ExprContext& context_;
};

}

ExprValue parse_expression(Lexer& lexer, ExprContext& context) {
    ExprParser parser(lexer, context);
    return parser.parse();
}

}
