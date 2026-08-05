#ifndef ABURI_TOKEN_SPELLING_H
#define ABURI_TOKEN_SPELLING_H

#include <string>
#include <string_view>

#include "lexer.h"

namespace aburi {

inline std::string literal_prefix_spelling(LiteralPrefix prefix) {
    switch (prefix) {
        case LiteralPrefix::L: return "L";
        case LiteralPrefix::U8: return "u8";
        case LiteralPrefix::U: return "U";
        case LiteralPrefix::u: return "u";
        case LiteralPrefix::None:
        default:
            return "";
    }
}

inline void append_hex_escape(std::string& out, unsigned char byte) {
    static const char kHex[] = "0123456789ABCDEF";
    out += "\\x";
    out.push_back(kHex[(byte >> 4) & 0xF]);
    out.push_back(kHex[byte & 0xF]);
}

inline std::string escape_literal_payload(std::string_view payload,
                                          bool is_char_literal) {
    std::string escaped;
    escaped.reserve(payload.size());
    for (unsigned char byte : payload) {
        switch (byte) {
            case '\a': escaped += "\\a"; break;
            case '\b': escaped += "\\b"; break;
            case '\f': escaped += "\\f"; break;
            case '\n': escaped += "\\n"; break;
            case '\r': escaped += "\\r"; break;
            case '\t': escaped += "\\t"; break;
            case '\v': escaped += "\\v"; break;
            case '\\': escaped += "\\\\"; break;
            case '"':
                if (is_char_literal) {
                    escaped.push_back('"');
                } else {
                    escaped += "\\\"";
                }
                break;
            case '\'':
                if (is_char_literal) {
                    escaped += "\\'";
                } else {
                    escaped.push_back('\'');
                }
                break;
            default:
                if (byte < 0x20 || byte >= 0x7F) {
                    append_hex_escape(escaped, byte);
                } else {
                    escaped.push_back(static_cast<char>(byte));
                }
                break;
        }
    }
    return escaped;
}

inline std::string token_spelling_for_output(const Token& t) {
    switch (t.type) {
        case TokenType::STRING_LITERAL:
            return literal_prefix_spelling(t.literal_prefix) + "\"" +
                escape_literal_payload(t.value, false) + "\"";
        case TokenType::CHAR_LITERAL:
            return literal_prefix_spelling(t.literal_prefix) + "'" +
                escape_literal_payload(t.value, true) + "'";
        case TokenType::UNSIGNED_INTEGER_CONST:
            return std::string(t.value) + "U";
        case TokenType::LONG_CONST:
            return std::string(t.value) + "L";
        case TokenType::UNSIGNED_LONG_CONST:
            return std::string(t.value) + "UL";
        case TokenType::LONG_LONG_CONST:
            return std::string(t.value) + "LL";
        case TokenType::UNSIGNED_LONG_LONG_CONST:
            return std::string(t.value) + "ULL";
        case TokenType::BITINT_CONST:
            return std::string(t.value) + "wb";
        case TokenType::UNSIGNED_BITINT_CONST:
            return std::string(t.value) + "uwb";
        case TokenType::FLOAT_CONST:
            return std::string(t.value) + "F";
        case TokenType::LONG_DOUBLE_CONST:
            return std::string(t.value) + "L";
        case TokenType::IMAG_INTEGER_CONST:
            return std::string(t.value) + "i";
        case TokenType::IMAG_UNSIGNED_INTEGER_CONST:
            return std::string(t.value) + "Ui";
        case TokenType::IMAG_LONG_CONST:
            return std::string(t.value) + "Li";
        case TokenType::IMAG_UNSIGNED_LONG_CONST:
            return std::string(t.value) + "ULi";
        case TokenType::IMAG_LONG_LONG_CONST:
            return std::string(t.value) + "LLi";
        case TokenType::IMAG_UNSIGNED_LONG_LONG_CONST:
            return std::string(t.value) + "ULLi";
        case TokenType::IMAG_FLOAT_CONST:
            return std::string(t.value) + "Fi";
        case TokenType::IMAG_DOUBLE_CONST:
            return std::string(t.value) + "i";
        case TokenType::IMAG_LONG_DOUBLE_CONST:
            return std::string(t.value) + "Li";
        default:
            return std::string(t.value);
    }
}

} // namespace aburi

#endif // ABURI_TOKEN_SPELLING_H
