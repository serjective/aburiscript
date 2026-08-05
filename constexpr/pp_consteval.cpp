#include "pp_consteval.h"

#include "../numeric_utils.h"
#include "const_value.h"

#include <cstdint>
#include <string>

namespace {
constexpr uint16_t kPPIntWidth = 64;

bool is_integer_token(TokenType type) {
    switch (type) {
        case TokenType::INTEGER_CONST:
        case TokenType::UNSIGNED_INTEGER_CONST:
        case TokenType::LONG_CONST:
        case TokenType::UNSIGNED_LONG_CONST:
        case TokenType::LONG_LONG_CONST:
        case TokenType::UNSIGNED_LONG_LONG_CONST:
            return true;
        default:
            return false;
    }
}

bool is_unsigned_integer_token(TokenType type) {
    switch (type) {
        case TokenType::UNSIGNED_INTEGER_CONST:
        case TokenType::UNSIGNED_LONG_CONST:
        case TokenType::UNSIGNED_LONG_LONG_CONST:
            return true;
        default:
            return false;
    }
}

ConstIntValue make_zero_value() {
    return ConstIntValue::from_signed(0, kPPIntWidth);
}

ConstIntValue make_bool_value(bool value) {
    return ConstIntValue::from_signed(value ? 1 : 0, kPPIntWidth);
}

bool is_truthy(ConstIntValue value) {
    return value.to_unsigned_u64() != 0;
}

int64_t parse_char_literal_bits(const Token& tok) {
    int64_t out = 0;
    for (unsigned char c : tok.value) {
        out <<= 8;
        out |= static_cast<int64_t>(c);
    }
    return out;
}

class PPConstExprParser {
public:
    explicit PPConstExprParser(const std::vector<Token>& tokens)
        : tokens_(tokens) {}

    PPConstEvalResult evaluate() {
        if (tokens_.empty()) {
            return PPConstEvalResult::failure(
                "Invalid constant expression in #if/#elif");
        }

        EvalResult parsed = parse_conditional_expression(true);
        if (!parsed.ok) {
            return PPConstEvalResult::failure(parsed.message, parsed.loc);
        }
        if (!at_end()) {
            return PPConstEvalResult::failure(
                "Invalid constant expression in #if/#elif",
                peek().loc);
        }

        return PPConstEvalResult::success(parsed.value.to_signed_i64());
    }

private:
    struct EvalResult {
        bool ok = false;
        ConstIntValue value = make_zero_value();
        std::string message;
        SrcLoc loc{};
    };

    const std::vector<Token>& tokens_;
    size_t index_ = 0;

    bool at_end() const {
        return index_ >= tokens_.size();
    }

    const Token& peek() const {
        static Token eof_token(TokenType::Eof, "", SrcLoc());
        if (at_end()) {
            return eof_token;
        }
        return tokens_[index_];
    }

    const Token& advance() {
        return tokens_[index_++];
    }

    bool consume(TokenType type) {
        if (!at_end() && tokens_[index_].type == type) {
            ++index_;
            return true;
        }
        return false;
    }

    EvalResult success(ConstIntValue value) const {
        EvalResult out;
        out.ok = true;
        out.value = value;
        return out;
    }

    EvalResult failure(const std::string& message, SrcLoc loc) const {
        EvalResult out;
        out.ok = false;
        out.message = message;
        out.loc = loc;
        return out;
    }

    static bool use_unsigned_comparison(ConstIntValue lhs, ConstIntValue rhs) {
        return lhs.is_unsigned || rhs.is_unsigned;
    }

    static ConstIntValue cast_pp_int(ConstIntValue value, bool as_unsigned) {
        return value.cast(kPPIntWidth, as_unsigned);
    }

    EvalResult eval_add(ConstIntValue lhs, ConstIntValue rhs, bool evaluate) const {
        if (!evaluate) {
            return success(make_zero_value());
        }
        bool as_unsigned = use_unsigned_comparison(lhs, rhs);
        ConstIntValue l = cast_pp_int(lhs, as_unsigned);
        ConstIntValue r = cast_pp_int(rhs, as_unsigned);
        if (as_unsigned) {
            return success(ConstIntValue::from_unsigned(
                l.to_unsigned_u64() + r.to_unsigned_u64(), kPPIntWidth));
        }
        return success(ConstIntValue::from_signed(
            l.to_signed_i64() + r.to_signed_i64(), kPPIntWidth));
    }

    EvalResult eval_sub(ConstIntValue lhs, ConstIntValue rhs, bool evaluate) const {
        if (!evaluate) {
            return success(make_zero_value());
        }
        bool as_unsigned = use_unsigned_comparison(lhs, rhs);
        ConstIntValue l = cast_pp_int(lhs, as_unsigned);
        ConstIntValue r = cast_pp_int(rhs, as_unsigned);
        if (as_unsigned) {
            return success(ConstIntValue::from_unsigned(
                l.to_unsigned_u64() - r.to_unsigned_u64(), kPPIntWidth));
        }
        return success(ConstIntValue::from_signed(
            l.to_signed_i64() - r.to_signed_i64(), kPPIntWidth));
    }

    EvalResult eval_mul(ConstIntValue lhs, ConstIntValue rhs, bool evaluate) const {
        if (!evaluate) {
            return success(make_zero_value());
        }
        bool as_unsigned = use_unsigned_comparison(lhs, rhs);
        ConstIntValue l = cast_pp_int(lhs, as_unsigned);
        ConstIntValue r = cast_pp_int(rhs, as_unsigned);
        if (as_unsigned) {
            return success(ConstIntValue::from_unsigned(
                l.to_unsigned_u64() * r.to_unsigned_u64(), kPPIntWidth));
        }
        return success(ConstIntValue::from_signed(
            l.to_signed_i64() * r.to_signed_i64(), kPPIntWidth));
    }

    EvalResult eval_div(ConstIntValue lhs, ConstIntValue rhs, SrcLoc loc, bool evaluate) const {
        if (!evaluate) {
            return success(make_zero_value());
        }
        bool as_unsigned = use_unsigned_comparison(lhs, rhs);
        ConstIntValue l = cast_pp_int(lhs, as_unsigned);
        ConstIntValue r = cast_pp_int(rhs, as_unsigned);
        auto div_res = const_int_div(l, r);
        if (!div_res.value.has_value()) {
            return failure("division by zero in preprocessor expression", loc);
        }
        return success(div_res.value.value());
    }

    EvalResult eval_mod(ConstIntValue lhs, ConstIntValue rhs, SrcLoc loc, bool evaluate) const {
        if (!evaluate) {
            return success(make_zero_value());
        }
        bool as_unsigned = use_unsigned_comparison(lhs, rhs);
        ConstIntValue l = cast_pp_int(lhs, as_unsigned);
        ConstIntValue r = cast_pp_int(rhs, as_unsigned);
        auto mod_res = const_int_mod(l, r);
        if (!mod_res.value.has_value()) {
            return failure("modulo by zero in preprocessor expression", loc);
        }
        return success(mod_res.value.value());
    }

    EvalResult eval_shift_left(ConstIntValue lhs, ConstIntValue rhs, SrcLoc loc, bool evaluate) const {
        if (!evaluate) {
            return success(make_zero_value());
        }
        ConstIntValue l = lhs.cast(kPPIntWidth, lhs.is_unsigned);
        ConstIntValue r = rhs.cast(kPPIntWidth, true);
        auto shl_res = const_int_shl(l, r);
        if (!shl_res.value.has_value()) {
            return failure("invalid shift amount in preprocessor expression", loc);
        }
        return success(shl_res.value.value());
    }

    EvalResult eval_shift_right(ConstIntValue lhs, ConstIntValue rhs, SrcLoc loc, bool evaluate) const {
        if (!evaluate) {
            return success(make_zero_value());
        }

        ConstIntValue l = lhs.cast(kPPIntWidth, lhs.is_unsigned);
        uint64_t shift = rhs.cast(kPPIntWidth, true).to_unsigned_u64();
        if (shift >= kPPIntWidth) {
            return failure("invalid shift amount in preprocessor expression", loc);
        }
        if (l.is_unsigned) {
            return success(ConstIntValue::from_unsigned(
                l.to_unsigned_u64() >> shift, kPPIntWidth));
        }
        return success(ConstIntValue::from_signed(
            l.to_signed_i64() >> shift, kPPIntWidth));
    }

    EvalResult eval_relational(TokenType op, ConstIntValue lhs, ConstIntValue rhs, bool evaluate) const {
        if (!evaluate) {
            return success(make_zero_value());
        }
        bool as_unsigned = use_unsigned_comparison(lhs, rhs);
        ConstIntValue l = cast_pp_int(lhs, as_unsigned);
        ConstIntValue r = cast_pp_int(rhs, as_unsigned);
        bool out = false;
        if (as_unsigned) {
            uint64_t lu = l.to_unsigned_u64();
            uint64_t ru = r.to_unsigned_u64();
            switch (op) {
                case TokenType::LESS_THAN:
                    out = lu < ru;
                    break;
                case TokenType::LESS_EQUAL_THAN:
                    out = lu <= ru;
                    break;
                case TokenType::GREATER_THAN:
                    out = lu > ru;
                    break;
                case TokenType::GREATER_EQUAL_THAN:
                    out = lu >= ru;
                    break;
                default:
                    break;
            }
        } else {
            int64_t ls = l.to_signed_i64();
            int64_t rs = r.to_signed_i64();
            switch (op) {
                case TokenType::LESS_THAN:
                    out = ls < rs;
                    break;
                case TokenType::LESS_EQUAL_THAN:
                    out = ls <= rs;
                    break;
                case TokenType::GREATER_THAN:
                    out = ls > rs;
                    break;
                case TokenType::GREATER_EQUAL_THAN:
                    out = ls >= rs;
                    break;
                default:
                    break;
            }
        }
        return success(make_bool_value(out));
    }

    EvalResult eval_equality(TokenType op, ConstIntValue lhs, ConstIntValue rhs, bool evaluate) const {
        if (!evaluate) {
            return success(make_zero_value());
        }
        bool as_unsigned = use_unsigned_comparison(lhs, rhs);
        ConstIntValue l = cast_pp_int(lhs, as_unsigned);
        ConstIntValue r = cast_pp_int(rhs, as_unsigned);
        bool eq = l.to_unsigned_u64() == r.to_unsigned_u64();
        bool out = (op == TokenType::EQUAL_TO) ? eq : !eq;
        return success(make_bool_value(out));
    }

    EvalResult parse_conditional_expression(bool evaluate) {
        EvalResult condition = parse_logical_or_expression(evaluate);
        if (!condition.ok) {
            return condition;
        }
        if (!consume(TokenType::QUESTION)) {
            return condition;
        }

        bool cond_truthy = evaluate && is_truthy(condition.value);
        EvalResult true_branch = parse_conditional_expression(cond_truthy);
        if (!true_branch.ok) {
            return true_branch;
        }
        if (!consume(TokenType::COLON)) {
            return failure("expected ':' in preprocessor conditional expression",
                at_end() ? SrcLoc() : peek().loc);
        }
        EvalResult false_branch = parse_conditional_expression(evaluate && !cond_truthy);
        if (!false_branch.ok) {
            return false_branch;
        }

        if (!evaluate) {
            return success(make_zero_value());
        }
        return cond_truthy ? true_branch : false_branch;
    }

    EvalResult parse_logical_or_expression(bool evaluate) {
        EvalResult lhs = parse_logical_and_expression(evaluate);
        if (!lhs.ok) {
            return lhs;
        }

        while (consume(TokenType::LOGICAL_OR)) {
            bool lhs_truthy = evaluate && is_truthy(lhs.value);
            EvalResult rhs = parse_logical_and_expression(evaluate && !lhs_truthy);
            if (!rhs.ok) {
                return rhs;
            }
            if (!evaluate) {
                lhs.value = make_zero_value();
                continue;
            }
            lhs.value = make_bool_value(lhs_truthy || is_truthy(rhs.value));
        }
        return lhs;
    }

    EvalResult parse_logical_and_expression(bool evaluate) {
        EvalResult lhs = parse_bitwise_or_expression(evaluate);
        if (!lhs.ok) {
            return lhs;
        }

        while (consume(TokenType::LOGICAL_AND)) {
            bool lhs_truthy = evaluate && is_truthy(lhs.value);
            EvalResult rhs = parse_bitwise_or_expression(evaluate && lhs_truthy);
            if (!rhs.ok) {
                return rhs;
            }
            if (!evaluate) {
                lhs.value = make_zero_value();
                continue;
            }
            lhs.value = make_bool_value(lhs_truthy && is_truthy(rhs.value));
        }
        return lhs;
    }

    EvalResult parse_bitwise_or_expression(bool evaluate) {
        EvalResult lhs = parse_bitwise_xor_expression(evaluate);
        if (!lhs.ok) {
            return lhs;
        }

        while (consume(TokenType::BITWISE_OR)) {
            EvalResult rhs = parse_bitwise_xor_expression(evaluate);
            if (!rhs.ok) {
                return rhs;
            }
            if (!evaluate) {
                lhs.value = make_zero_value();
                continue;
            }

            bool as_unsigned = use_unsigned_comparison(lhs.value, rhs.value);
            ConstIntValue l = cast_pp_int(lhs.value, as_unsigned);
            ConstIntValue r = cast_pp_int(rhs.value, as_unsigned);
            lhs.value = ConstIntValue::from_unsigned(
                l.to_unsigned_u64() | r.to_unsigned_u64(), kPPIntWidth).cast(kPPIntWidth, as_unsigned);
        }
        return lhs;
    }

    EvalResult parse_bitwise_xor_expression(bool evaluate) {
        EvalResult lhs = parse_bitwise_and_expression(evaluate);
        if (!lhs.ok) {
            return lhs;
        }

        while (consume(TokenType::BITWISE_XOR)) {
            EvalResult rhs = parse_bitwise_and_expression(evaluate);
            if (!rhs.ok) {
                return rhs;
            }
            if (!evaluate) {
                lhs.value = make_zero_value();
                continue;
            }

            bool as_unsigned = use_unsigned_comparison(lhs.value, rhs.value);
            ConstIntValue l = cast_pp_int(lhs.value, as_unsigned);
            ConstIntValue r = cast_pp_int(rhs.value, as_unsigned);
            lhs.value = ConstIntValue::from_unsigned(
                l.to_unsigned_u64() ^ r.to_unsigned_u64(), kPPIntWidth).cast(kPPIntWidth, as_unsigned);
        }
        return lhs;
    }

    EvalResult parse_bitwise_and_expression(bool evaluate) {
        EvalResult lhs = parse_equality_expression(evaluate);
        if (!lhs.ok) {
            return lhs;
        }

        while (consume(TokenType::BITWISE_AND)) {
            EvalResult rhs = parse_equality_expression(evaluate);
            if (!rhs.ok) {
                return rhs;
            }
            if (!evaluate) {
                lhs.value = make_zero_value();
                continue;
            }

            bool as_unsigned = use_unsigned_comparison(lhs.value, rhs.value);
            ConstIntValue l = cast_pp_int(lhs.value, as_unsigned);
            ConstIntValue r = cast_pp_int(rhs.value, as_unsigned);
            lhs.value = ConstIntValue::from_unsigned(
                l.to_unsigned_u64() & r.to_unsigned_u64(), kPPIntWidth).cast(kPPIntWidth, as_unsigned);
        }
        return lhs;
    }

    EvalResult parse_equality_expression(bool evaluate) {
        EvalResult lhs = parse_relational_expression(evaluate);
        if (!lhs.ok) {
            return lhs;
        }

        while (!at_end()) {
            TokenType op = peek().type;
            if (op != TokenType::EQUAL_TO && op != TokenType::NOT_EQUAL) {
                break;
            }
            SrcLoc loc = advance().loc;
            EvalResult rhs = parse_relational_expression(evaluate);
            if (!rhs.ok) {
                return rhs;
            }
            EvalResult eq = eval_equality(op, lhs.value, rhs.value, evaluate);
            if (!eq.ok) {
                eq.loc = eq.loc.isInvalid() ? loc : eq.loc;
                return eq;
            }
            lhs.value = eq.value;
        }
        return lhs;
    }

    EvalResult parse_relational_expression(bool evaluate) {
        EvalResult lhs = parse_shift_expression(evaluate);
        if (!lhs.ok) {
            return lhs;
        }

        while (!at_end()) {
            TokenType op = peek().type;
            if (op != TokenType::LESS_THAN &&
                op != TokenType::LESS_EQUAL_THAN &&
                op != TokenType::GREATER_THAN &&
                op != TokenType::GREATER_EQUAL_THAN) {
                break;
            }
            SrcLoc loc = advance().loc;
            EvalResult rhs = parse_shift_expression(evaluate);
            if (!rhs.ok) {
                return rhs;
            }
            EvalResult rel = eval_relational(op, lhs.value, rhs.value, evaluate);
            if (!rel.ok) {
                rel.loc = rel.loc.isInvalid() ? loc : rel.loc;
                return rel;
            }
            lhs.value = rel.value;
        }
        return lhs;
    }

    EvalResult parse_shift_expression(bool evaluate) {
        EvalResult lhs = parse_additive_expression(evaluate);
        if (!lhs.ok) {
            return lhs;
        }

        while (!at_end()) {
            TokenType op = peek().type;
            if (op != TokenType::LEFT_SHIFT && op != TokenType::RIGHT_SHIFT) {
                break;
            }
            SrcLoc op_loc = advance().loc;
            EvalResult rhs = parse_additive_expression(evaluate);
            if (!rhs.ok) {
                return rhs;
            }
            EvalResult shifted = (op == TokenType::LEFT_SHIFT)
                ? eval_shift_left(lhs.value, rhs.value, op_loc, evaluate)
                : eval_shift_right(lhs.value, rhs.value, op_loc, evaluate);
            if (!shifted.ok) {
                shifted.loc = shifted.loc.isInvalid() ? op_loc : shifted.loc;
                return shifted;
            }
            lhs.value = shifted.value;
        }
        return lhs;
    }

    EvalResult parse_additive_expression(bool evaluate) {
        EvalResult lhs = parse_multiplicative_expression(evaluate);
        if (!lhs.ok) {
            return lhs;
        }

        while (!at_end()) {
            TokenType op = peek().type;
            if (op != TokenType::PLUS && op != TokenType::NEGATE) {
                break;
            }
            SrcLoc op_loc = advance().loc;
            EvalResult rhs = parse_multiplicative_expression(evaluate);
            if (!rhs.ok) {
                return rhs;
            }
            EvalResult folded = (op == TokenType::PLUS)
                ? eval_add(lhs.value, rhs.value, evaluate)
                : eval_sub(lhs.value, rhs.value, evaluate);
            if (!folded.ok) {
                folded.loc = folded.loc.isInvalid() ? op_loc : folded.loc;
                return folded;
            }
            lhs.value = folded.value;
        }
        return lhs;
    }

    EvalResult parse_multiplicative_expression(bool evaluate) {
        EvalResult lhs = parse_unary_expression(evaluate);
        if (!lhs.ok) {
            return lhs;
        }

        while (!at_end()) {
            TokenType op = peek().type;
            if (op != TokenType::MULTIPLY &&
                op != TokenType::DIVIDE &&
                op != TokenType::MODULO) {
                break;
            }
            SrcLoc op_loc = advance().loc;
            EvalResult rhs = parse_unary_expression(evaluate);
            if (!rhs.ok) {
                return rhs;
            }

            EvalResult folded;
            if (op == TokenType::MULTIPLY) {
                folded = eval_mul(lhs.value, rhs.value, evaluate);
            } else if (op == TokenType::DIVIDE) {
                folded = eval_div(lhs.value, rhs.value, op_loc, evaluate);
            } else {
                folded = eval_mod(lhs.value, rhs.value, op_loc, evaluate);
            }

            if (!folded.ok) {
                folded.loc = folded.loc.isInvalid() ? op_loc : folded.loc;
                return folded;
            }
            lhs.value = folded.value;
        }
        return lhs;
    }

    EvalResult parse_unary_expression(bool evaluate) {
        if (consume(TokenType::PLUS)) {
            EvalResult inner = parse_unary_expression(evaluate);
            if (!inner.ok || !evaluate) {
                return inner.ok ? success(make_zero_value()) : inner;
            }
            inner.value = inner.value.cast(kPPIntWidth, inner.value.is_unsigned);
            return inner;
        }

        if (consume(TokenType::NEGATE)) {
            EvalResult inner = parse_unary_expression(evaluate);
            if (!inner.ok) {
                return inner;
            }
            if (!evaluate) {
                return success(make_zero_value());
            }
            inner.value = inner.value.cast(kPPIntWidth, inner.value.is_unsigned);
            if (inner.value.is_unsigned) {
                return success(ConstIntValue::from_unsigned(
                    uint64_t(0) - inner.value.to_unsigned_u64(), kPPIntWidth));
            }
            return success(ConstIntValue::from_signed(
                -inner.value.to_signed_i64(), kPPIntWidth));
        }

        if (consume(TokenType::BITWISE_NOT)) {
            EvalResult inner = parse_unary_expression(evaluate);
            if (!inner.ok) {
                return inner;
            }
            if (!evaluate) {
                return success(make_zero_value());
            }
            inner.value = inner.value.cast(kPPIntWidth, inner.value.is_unsigned);
            return success(ConstIntValue::from_unsigned(
                ~inner.value.to_unsigned_u64(), kPPIntWidth).cast(kPPIntWidth, inner.value.is_unsigned));
        }

        if (consume(TokenType::LOGICAL_NOT)) {
            EvalResult inner = parse_unary_expression(evaluate);
            if (!inner.ok) {
                return inner;
            }
            if (!evaluate) {
                return success(make_zero_value());
            }
            return success(make_bool_value(!is_truthy(inner.value)));
        }

        return parse_primary_expression(evaluate);
    }

    EvalResult parse_primary_expression(bool evaluate) {
        if (consume(TokenType::LEFT_PAREN)) {
            EvalResult inner = parse_conditional_expression(evaluate);
            if (!inner.ok) {
                return inner;
            }
            if (!consume(TokenType::RIGHT_PAREN)) {
                return failure("expected ')' in preprocessor expression",
                    at_end() ? SrcLoc() : peek().loc);
            }
            if (!evaluate) {
                inner.value = make_zero_value();
            }
            return inner;
        }

        if (at_end()) {
            return failure("Invalid constant expression in #if/#elif", SrcLoc());
        }

        const Token tok = advance();
        if (is_integer_token(tok.type)) {
            if (!evaluate) {
                return success(make_zero_value());
            }
            auto parsed = parse_integer_literal_u64(tok.value);
            if (!parsed.has_value()) {
                return failure("invalid integer literal in preprocessor expression", tok.loc);
            }
            if (is_unsigned_integer_token(tok.type)) {
                return success(ConstIntValue::from_unsigned(parsed.value(), kPPIntWidth));
            }
            return success(ConstIntValue::from_signed(
                static_cast<int64_t>(parsed.value()), kPPIntWidth));
        }

        if (tok.type == TokenType::CHAR_LITERAL) {
            if (!evaluate) {
                return success(make_zero_value());
            }
            return success(ConstIntValue::from_signed(parse_char_literal_bits(tok), kPPIntWidth));
        }

        if (!evaluate) {
            return success(make_zero_value());
        }

        return failure("invalid token in preprocessor expression: " + std::string(tok.value), tok.loc);
    }
};
}

PPConstEvalResult PPConstEvalResult::success(int64_t value) {
    PPConstEvalResult out;
    out.ok = true;
    out.value = value;
    return out;
}

PPConstEvalResult PPConstEvalResult::failure(std::string message, SrcLoc loc) {
    PPConstEvalResult out;
    out.ok = false;
    out.message = std::move(message);
    out.loc = loc;
    return out;
}

PPConstEvalResult evaluate_pp_constant_expression(const std::vector<Token>& tokens) {
    PPConstExprParser parser(tokens);
    return parser.evaluate();
}
