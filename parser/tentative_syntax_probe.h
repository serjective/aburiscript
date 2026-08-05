#ifndef ABURI_TENTATIVE_SYNTAX_PROBE_H
#define ABURI_TENTATIVE_SYNTAX_PROBE_H

#include "../lexer.h"

#include <cstdint>

namespace aburi::syntax::tentative_syntax_probe {

enum class Result : uint8_t {
    Match,
    NoMatch,
    Inconclusive,
    Error
};

inline Result probe_declaration_statement_start(TokenType type) {
    switch (type) {
        case TokenType::VOID:
        case TokenType::CHAR:
        case TokenType::SHORT:
        case TokenType::INT:
        case TokenType::LONG:
        case TokenType::FLOAT:
        case TokenType::DOUBLE:
        case TokenType::SIGNED:
        case TokenType::UNSIGNED:
        case TokenType::BOOL:
        case TokenType::WCHAR_T:
        case TokenType::CHAR8_T:
        case TokenType::CHAR16_T:
        case TokenType::CHAR32_T:
        case TokenType::STRUCT:
        case TokenType::UNION:
        case TokenType::CLASS:
        case TokenType::ENUM:
        case TokenType::CONST:
        case TokenType::VOLATILE:
        case TokenType::RESTRICT:
        case TokenType::STATIC:
        case TokenType::EXTERN:
        case TokenType::AUTO:
        case TokenType::REGISTER:
        case TokenType::TYPEDEF:
        case TokenType::INLINE:
        case TokenType::NORETURN_KW:
        case TokenType::THREAD_LOCAL:
        case TokenType::INT128:
        case TokenType::UINT128_T:
        case TokenType::BITINT_KW:
        case TokenType::FLOAT16:
        case TokenType::AUTO_TYPE:
        case TokenType::ATOMIC:
        case TokenType::COMPLEX:
        case TokenType::TYPEOF_KW:
        case TokenType::TYPEOF_UNQUAL_KW:
        case TokenType::EXTENSION_KW:
        case TokenType::ALIGNAS:
        case TokenType::ATTRIBUTE_KW:
        case TokenType::CONSTEXPR_KW:
        case TokenType::CONSTEVAL_KW:
        case TokenType::CONSTINIT_KW:
        case TokenType::FRIEND_KW:
        case TokenType::MUTABLE_KW:
        case TokenType::EXPLICIT_KW:
        case TokenType::DECLTYPE_KW:

        case TokenType::TYPENAME:
            return Result::Match;
        case TokenType::IDENTIFIER:

        case TokenType::SCOPE_RESOLUTION:
            return Result::Inconclusive;
        default:
            return Result::NoMatch;
    }
}

inline Result probe_expression_statement_start(TokenType type) {
    switch (type) {
        case TokenType::SEMICOLON:
        case TokenType::IDENTIFIER:
        case TokenType::OPERATOR_KW:
        case TokenType::THIS_KW:
        case TokenType::INTEGER_CONST:
        case TokenType::UNSIGNED_INTEGER_CONST:
        case TokenType::LONG_CONST:
        case TokenType::UNSIGNED_LONG_CONST:
        case TokenType::LONG_LONG_CONST:
        case TokenType::UNSIGNED_LONG_LONG_CONST:
        case TokenType::BITINT_CONST:
        case TokenType::UNSIGNED_BITINT_CONST:
        case TokenType::PP_NUMBER:
        case TokenType::FLOAT_CONST:
        case TokenType::DOUBLE_CONST:
        case TokenType::LONG_DOUBLE_CONST:
        case TokenType::TRUE_KW:
        case TokenType::FALSE_KW:
        case TokenType::NULLPTR_KW:
        case TokenType::REQUIRES_KW:
        case TokenType::CHAR_LITERAL:
        case TokenType::STRING_LITERAL:
        case TokenType::LEFT_PAREN:
        case TokenType::INCREMENT:
        case TokenType::DECREMENT:
        case TokenType::PLUS:
        case TokenType::NEGATE:
        case TokenType::LOGICAL_NOT:
        case TokenType::BITWISE_NOT:
        case TokenType::MULTIPLY:
        case TokenType::BITWISE_AND:
        case TokenType::SIZEOF:
        case TokenType::ALIGNOF:
        case TokenType::EXTENSION_KW:
        case TokenType::REAL_PART:
        case TokenType::IMAG_PART:

        case TokenType::SPLICE_OPEN:
        case TokenType::REFLECT:

        case TokenType::CO_AWAIT_KW:
        case TokenType::CO_YIELD_KW:
            return Result::Match;
        default:
            return Result::NoMatch;
    }
}

} // namespace aburi::syntax::tentative_syntax_probe

#endif // ABURI_TENTATIVE_SYNTAX_PROBE_H
