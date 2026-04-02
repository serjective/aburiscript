#include "lexer.h"
#include "diagnostics.h"
#include <algorithm>
#include <cctype>
#include <optional>
#include <string_view>
#include <unordered_map>

namespace {
inline bool is_ascii_space(char c) {
    return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f' || c == '\v';
}

inline bool is_ascii_digit(char c) {
    return c >= '0' && c <= '9';
}

inline bool is_ascii_alpha(char c) {
    return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');
}

inline bool is_ascii_identifier_start(char c) {
    return is_ascii_alpha(c) || c == '_' || c == '$';
}

inline bool is_ascii_identifier_continue(char c) {
    return is_ascii_identifier_start(c) || is_ascii_digit(c);
}

const std::unordered_map<std::string_view, TokenType>& common_keyword_table() {
    static const std::unordered_map<std::string_view, TokenType> keywords = {
        {"int", TokenType::INT},
        {"return", TokenType::RETURN},
        {"if", TokenType::IF},
        {"else", TokenType::ELSE},
        {"unsigned", TokenType::UNSIGNED},
        {"signed", TokenType::SIGNED},
        {"long", TokenType::LONG},
        {"short", TokenType::SHORT},
        {"char", TokenType::CHAR},
        {"default", TokenType::DEFAULT},
        {"void", TokenType::VOID},
        {"float", TokenType::FLOAT},
        {"double", TokenType::DOUBLE},
        {"const", TokenType::CONST},
        {"inline", TokenType::INLINE},
        {"volatile", TokenType::VOLATILE},
        {"restrict", TokenType::RESTRICT},
        {"_Atomic", TokenType::ATOMIC},
        {"static", TokenType::STATIC},
        {"extern", TokenType::EXTERN},
        {"auto", TokenType::AUTO},
        {"register", TokenType::REGISTER},
        {"typedef", TokenType::TYPEDEF},
        {"do", TokenType::DO},
        {"while", TokenType::WHILE},
        {"continue", TokenType::CONTINUE},
        {"break", TokenType::BREAK},
        {"for", TokenType::FOR},
        {"switch", TokenType::SWITCH},
        {"case", TokenType::CASE},
        {"goto", TokenType::GOTO},
        {"struct", TokenType::STRUCT},
        {"union", TokenType::UNION},
        {"enum", TokenType::ENUM},
        {"sizeof", TokenType::SIZEOF},
        {"__attribute__", TokenType::ATTRIBUTE_KW},
        {"__attribute", TokenType::ATTRIBUTE_KW},
        {"asm", TokenType::ASM_KW},
        {"__asm__", TokenType::ASM_KW},
        {"__asm", TokenType::ASM_KW},
        {"__volatile__", TokenType::VOLATILE},
        {"__volatile", TokenType::VOLATILE},
        {"__inline__", TokenType::INLINE},
        {"__inline", TokenType::INLINE},
        {"_Bool", TokenType::BOOL},
        {"_Noreturn", TokenType::NORETURN_KW},
        {"_Static_assert", TokenType::STATIC_ASSERT},
        {"_Alignof", TokenType::ALIGNOF},
        {"__alignof__", TokenType::ALIGNOF},
        {"__alignof", TokenType::ALIGNOF},
        {"_Alignas", TokenType::ALIGNAS},
        {"_Thread_local", TokenType::THREAD_LOCAL},
        {"__thread", TokenType::THREAD_LOCAL},
        {"_Generic", TokenType::GENERIC},
        {"__const", TokenType::CONST},
        {"__const__", TokenType::CONST},
        {"__restrict", TokenType::RESTRICT},
        {"__restrict__", TokenType::RESTRICT},
        {"__signed", TokenType::SIGNED},
        {"__signed__", TokenType::SIGNED},
        {"__extension__", TokenType::EXTENSION_KW},
        {"__label__", TokenType::LABEL_KW},
        {"typeof", TokenType::TYPEOF_KW},
        {"__typeof__", TokenType::TYPEOF_KW},
        {"__typeof", TokenType::TYPEOF_KW},
        {"__int128", TokenType::INT128},
        {"__int128_t", TokenType::INT128},
        {"__uint128_t", TokenType::UINT128_T},
        {"__auto_type", TokenType::AUTO_TYPE},
        {"_Complex", TokenType::COMPLEX},
        {"__complex__", TokenType::COMPLEX},
        {"__complex", TokenType::COMPLEX},
        {"__real__", TokenType::REAL_PART},
        {"__real", TokenType::REAL_PART},
        {"__imag__", TokenType::IMAG_PART},
        {"__imag", TokenType::IMAG_PART},
        {"_Float16", TokenType::FLOAT16},
        {"__fp16", TokenType::FLOAT16},
        {"_Nonnull", TokenType::NULLABILITY_QUALIFIER},
        {"_Nullable", TokenType::NULLABILITY_QUALIFIER},
        {"_Null_unspecified", TokenType::NULLABILITY_QUALIFIER},
        {"_Nullable_result", TokenType::NULLABILITY_QUALIFIER},
        {"__nonnull", TokenType::NULLABILITY_QUALIFIER},
        {"__nullable", TokenType::NULLABILITY_QUALIFIER},
        {"__null_unspecified", TokenType::NULLABILITY_QUALIFIER},
    };
    return keywords;
}

const std::unordered_map<std::string_view, TokenType>& cxx_keyword_table() {
    static const std::unordered_map<std::string_view, TokenType> keywords = {
        {"bool", TokenType::BOOL},
        {"wchar_t", TokenType::WCHAR_T},
        {"char16_t", TokenType::CHAR16_T},
        {"char32_t", TokenType::CHAR32_T},
        {"class", TokenType::CLASS},
        {"using", TokenType::USING},
        {"namespace", TokenType::NAMESPACE},
        {"template", TokenType::TEMPLATE},
        {"typename", TokenType::TYPENAME},
        {"new", TokenType::NEW},
        {"delete", TokenType::DELETE},
        {"try", TokenType::TRY_KW},
        {"catch", TokenType::CATCH_KW},
        {"throw", TokenType::THROW_KW},
        {"noexcept", TokenType::NOEXCEPT_KW},
        {"operator", TokenType::OPERATOR_KW},
        {"this", TokenType::THIS_KW},
        {"true", TokenType::TRUE_KW},
        {"false", TokenType::FALSE_KW},
        {"nullptr", TokenType::NULLPTR_KW},
        {"decltype", TokenType::DECLTYPE_KW},
        {"public", TokenType::PUBLIC_KW},
        {"private", TokenType::PRIVATE_KW},
        {"protected", TokenType::PROTECTED_KW},
        {"virtual", TokenType::VIRTUAL_KW},
        {"friend", TokenType::FRIEND_KW},
        {"explicit", TokenType::EXPLICIT_KW},
        {"constexpr", TokenType::CONSTEXPR_KW},
    };
    return keywords;
}

TokenType lookup_keyword(const std::string_view ident, const LangOptions& lang_opts) {
    if (lang_opts.is_cxx_mode()) {
        const auto& cxx_keywords = cxx_keyword_table();
        auto cxx_it = cxx_keywords.find(ident);
        if (cxx_it != cxx_keywords.end()) {
            if ((cxx_it->second == TokenType::CONCEPT_KW ||
                 cxx_it->second == TokenType::REQUIRES_KW) &&
                !lang_opts.is_cxx20_or_later()) {
                return TokenType::IDENTIFIER;
            }
            return cxx_it->second;
        }
        if (lang_opts.is_cxx20_or_later()) {
            if (ident == "concept") {
                return TokenType::CONCEPT_KW;
            }
            if (ident == "requires") {
                return TokenType::REQUIRES_KW;
            }
        }
    }
    const auto& common_keywords = common_keyword_table();
    auto it = common_keywords.find(ident);
    if (it == common_keywords.end()) {
        return TokenType::IDENTIFIER;
    }
    return it->second;
}
} // namespace

Lexer::Lexer(const std::string_view source, SrcLoc baseLoc, SourceManager* diag_sm, LangOptions options)
        : source(source), position(0), error_happened(false), base_loc(baseLoc), diag_sm(diag_sm),
           lang_opts(std::move(options)),
           pending_start_of_line(false),
           enable_new_line_token(false), enable_whitespace_token(false), emit_comment_whitespace(false),
           pp_number_mode(false) {
    // Skip UTF-8 BOM if present at the start of the source
    if (source.size() >= 3 &&
        static_cast<unsigned char>(source[0]) == 0xEF &&
        static_cast<unsigned char>(source[1]) == 0xBB &&
        static_cast<unsigned char>(source[2]) == 0xBF) {
        position = 3;
    }
}
char Lexer::current_char() const {
    if (position >= source.length()) {
        return '\0';
    }
    return source[position];
}
char Lexer::prev_char() const {
    if (position == 0) {
        return '\0';
    }
    return source[position-1];
}

size_t Lexer::get_char_idx() const {
    return position;
}

size_t Lexer::set_char_idx(size_t new_pos) {
    position = new_pos;
    return position;
}
char Lexer::peek_char_rev(size_t offset) const {
    if (offset > position) { // overflow
        return '\0';
    }
    size_t peek_pos = position - offset;
    return source[peek_pos];
}
char Lexer::peek_char(size_t offset) const {
    size_t peek_pos = position + offset;
    if (peek_pos >= source.length()) {
        return '\0';
    }
    return source[peek_pos];
}
void Lexer::advance() {
    if (position < source.length()) {
        position++;
    }
}
void Lexer::skip_whitespace() {
    // todo: we may need to handle \n as its own token
    while (is_ascii_space(current_char())) {
        advance();
    }
}

bool Lexer::is_digit(char c) {
    return is_ascii_digit(c);
}
bool Lexer::is_oct_digit(char c) {
    return c >= '0' && c <= '7';
}
bool Lexer::is_bin_digit(char c) {
    return c == '0' || c == '1';
}
bool Lexer::is_hex_digit(char c) {
    return is_ascii_digit(c) ||
        (c >= 'a' && c <= 'f') ||
        (c >= 'A' && c <= 'F');
}
uint32_t Lexer::hex_value(char c) {
    if (c >= '0' && c <= '9') return static_cast<uint32_t>(c - '0');
    if (c >= 'a' && c <= 'f') return static_cast<uint32_t>(10 + (c - 'a'));
    if (c >= 'A' && c <= 'F') return static_cast<uint32_t>(10 + (c - 'A'));
    error_occurred("invalid hex digit");
    return 0;
}
std::string Lexer::encode_utf8(uint32_t code_point) {
    if (code_point > 0x10FFFF) {
        error_occurred("Invalid UTF-8: code point exceeds maximum");
    }
    std::string out;
    if (code_point <= 0x7F) {
        out.push_back(static_cast<char>(code_point));
    } else if (code_point <= 0x7FF) {
        out.push_back(static_cast<char>(0xC0 | ((code_point >> 6) & 0x1F)));
        out.push_back(static_cast<char>(0x80 | (code_point & 0x3F)));
    } else if (code_point <= 0xFFFF) {
        if (code_point >= 0xD800 && code_point <= 0xDFFF) {
            error_occurred("Invalid UTF-8: surrogate code point");
        }
        out.push_back(static_cast<char>(0xE0 | ((code_point >> 12) & 0x0F)));
        out.push_back(static_cast<char>(0x80 | ((code_point >> 6) & 0x3F)));
        out.push_back(static_cast<char>(0x80 | (code_point & 0x3F)));
    } else {
        out.push_back(static_cast<char>(0xF0 | ((code_point >> 18) & 0x07)));
        out.push_back(static_cast<char>(0x80 | ((code_point >> 12) & 0x3F)));
        out.push_back(static_cast<char>(0x80 | ((code_point >> 6) & 0x3F)));
        out.push_back(static_cast<char>(0x80 | (code_point & 0x3F)));
    }
    return out;
}
std::string Lexer::read_escape_sequence() {
    char code = current_char();
    if (code == '\0') {
        error_occurred("Unexpected end of file in escape sequence");
    }
    advance();
    switch (code) {
        case 'a': return std::string(1, '\a');
        case 'b': return std::string(1, '\b');
        case 'f': return std::string(1, '\f');
        case 'n': return std::string(1, '\n');
        case 'r': return std::string(1, '\r');
        case 't': return std::string(1, '\t');
        case 'v': return std::string(1, '\v');
        case 'e': return std::string(1, '\x1b');
        case 'E': return std::string(1, '\x1b');
        case '\\': return std::string(1, '\\');
        case '\'': return std::string(1, '\'');
        case '\"': return std::string(1, '\"');
        case '?': return std::string(1, '?');
        case 'x': {
            if (!is_hex_digit(current_char())) {
                error_occurred("Expected hex digit after \\x");
            }
            uint32_t value = 0;
            while (is_hex_digit(current_char())) {
                value = (value << 4) | hex_value(current_char());
                advance();
            }
            // In C, \xNN produces a raw byte value, not a Unicode code point
            return std::string(1, static_cast<char>(value & 0xFF));
        }
        case 'u': {
            uint32_t value = 0;
            for (int i = 0; i < 4; ++i) {
                if (!is_hex_digit(current_char())) {
                    error_occurred("Expected 4 hex digits after \\u");
                }
                value = (value << 4) | hex_value(current_char());
                advance();
            }
            return encode_utf8(value);
        }
        case 'U': {
            uint32_t value = 0;
            for (int i = 0; i < 8; ++i) {
                if (!is_hex_digit(current_char())) {
                    error_occurred("Expected 8 hex digits after \\U");
                }
                value = (value << 4) | hex_value(current_char());
                advance();
            }
            return encode_utf8(value);
        }
        default:
            if (is_oct_digit(code)) {
                uint32_t value = static_cast<uint32_t>(code - '0');
                int count = 1;
                while (count < 3 && is_oct_digit(current_char())) {
                    value = (value << 3) | static_cast<uint32_t>(current_char() - '0');
                    advance();
                    count++;
                }
                // In C, \NNN produces a raw byte value, not a Unicode code point
                return std::string(1, static_cast<char>(value & 0xFF));
            }
            return std::string(1, code);
    }
}
bool Lexer::is_alphabet(char c) {
    return is_ascii_alpha(c);
}
// per 6.4.2.1 in C standard, all identifiers must start with a non-digit
// aka: is letter or underscore
bool Lexer::is_nondigit(char c) {
    return is_ascii_identifier_start(c);
}
std::optional<Token> Lexer::read_number() {
    SrcLoc start_loc = get_loc_at_pos();
    std::string number;
    bool isFloat = false;
    bool isHex = false;
    bool isBin = false;
    bool saw_invalid_octal_digit = false;

    if (current_char() == '0' && (peek_char() == 'x' || peek_char() == 'X')) {
        // Hexadecimal
        isHex = true;
        number += current_char(); // '0'
        advance();
        number += current_char(); // 'x' or 'X'
        advance();

        bool saw_hex_digit = false;
        while (is_hex_digit(current_char())) {
            saw_hex_digit = true;
            number += current_char();
            advance();
        }

        if (current_char() == '.') {
            isFloat = true;
            number += current_char();
            advance();
            while (is_hex_digit(current_char())) {
                saw_hex_digit = true;
                number += current_char();
                advance();
            }
        }

        if (!saw_hex_digit) {
            error_occurred("hexadecimal constant has no digits", start_loc);
            return std::nullopt;
        }

        if (current_char() == 'p' || current_char() == 'P') {
            isFloat = true;
            number += current_char();
            advance();
            if (current_char() == '+' || current_char() == '-') {
                number += current_char();
                advance();
            }
            if (!is_digit(current_char())) {
                error_occurred("hexadecimal exponent has no digits", start_loc);
                return std::nullopt;
            }
            while (is_digit(current_char())) {
                number += current_char();
                advance();
            }
        } else if (isFloat) {
            error_occurred("hexadecimal floating constant requires an exponent", start_loc);
            return std::nullopt;
        }
    } else if (current_char() == '0' && (peek_char() == 'b' || peek_char() == 'B')) {
        // Binary (GCC/C23 extension)
        isBin = true;
        number += current_char(); // '0'
        advance();
        number += current_char(); // 'b' or 'B'
        advance();
        if (!is_bin_digit(current_char())) {
            error_occurred("binary constant has no digits", start_loc);
            return std::nullopt;
        }
        while (is_bin_digit(current_char())) {
            number += current_char();
            advance();
        }
    } else if (current_char() == '0') {
        // Octal or decimal float (if 0.123 or 0e1)
        number += current_char();
        advance();
        while (is_digit(current_char())) {
            if (!is_oct_digit(current_char())) {
                saw_invalid_octal_digit = true;
            }
            number += current_char();
            advance();
        }
        if (current_char() == '.') {
            isFloat = true;
            number += current_char();
            advance();
            while (is_digit(current_char())) {
                number += current_char();
                advance();
            }
        }
    } else {
        // Decimal
        while (is_digit(current_char())) {
            number += current_char();
            advance();
        }

        // Check for decimal point
        if (current_char() == '.') {
            isFloat = true;
            number += current_char();
            advance();
            while (is_digit(current_char())) {
                number += current_char();
                advance();
            }
        }
    }

    // Check for exponent part (only for non-hex/binary)
    if (!isHex && !isBin) {
        if (current_char() == 'e' || current_char() == 'E') {
            isFloat = true;
            number += current_char();
            advance();
            if (current_char() == '+' || current_char() == '-') {
                number += current_char();
                advance();
            }
            if (!is_digit(current_char())) {
                error_occurred("exponent has no digits", start_loc);
                return std::nullopt;
            }
            while (is_digit(current_char())) {
                number += current_char();
                advance();
            }
        }
    }

    if (!isFloat && saw_invalid_octal_digit) {
        error_occurred("invalid digit in octal constant", start_loc);
        return std::nullopt;
    }

    if (isFloat) {
        bool is_float_suffix = false;
        bool is_long_double_suffix = false;
        bool seen_fp_suffix = false;
        bool seen_imag_suffix = false;
        while (true) {
            char c = current_char();
            if ((c == 'f' || c == 'F' || c == 'l' || c == 'L') && !seen_fp_suffix) {
                if (c == 'f' || c == 'F') {
                    is_float_suffix = true;
                } else {
                    is_long_double_suffix = true;
                }
                seen_fp_suffix = true;
                advance();
                continue;
            }
            if ((c == 'i' || c == 'I' || c == 'j' || c == 'J') && !seen_imag_suffix) {
                seen_imag_suffix = true;
                advance();
                continue;
            }
            break;
        }
        TokenType float_tok = TokenType::DOUBLE_CONST;
        if (is_float_suffix) {
            float_tok = TokenType::FLOAT_CONST;
        } else if (is_long_double_suffix) {
            float_tok = TokenType::LONG_DOUBLE_CONST;
        }
        if (seen_imag_suffix) {
            if (is_float_suffix) {
                float_tok = TokenType::IMAG_FLOAT_CONST;
            } else if (is_long_double_suffix) {
                float_tok = TokenType::IMAG_LONG_DOUBLE_CONST;
            } else {
                float_tok = TokenType::IMAG_DOUBLE_CONST;
            }
        }
        if (is_nondigit(current_char()) || is_digit(current_char())) {
            error_occurred("invalid suffix on floating constant", start_loc);
            return std::nullopt;
        }
        return Token(float_tok, number, start_loc);
    }

    bool isUnsigned = false;
    int long_count = 0;
    bool lowercase_long = false;
    bool isImaginary = false;
    while (is_alphabet(current_char())) {
        char c = current_char();
        if (c == 'u' || c == 'U') {
            if (isUnsigned) {
                error_occurred("duplicate unsigned specifier", start_loc);
                return std::nullopt;
            } else {
                isUnsigned = true;
            }
        }
        else if (c == 'l' || c == 'L') {
            if (long_count >= 2) {
                error_occurred("invalid integer specifier", start_loc);
                return std::nullopt;
            } else if (long_count == 1) {
                if ((c == 'l' && lowercase_long == false) || (c == 'L' && lowercase_long == true)) {
                    error_occurred("invalid integer specifier", start_loc);
                    return std::nullopt;
                }
                long_count++;
            } else {
                if (c == 'l') lowercase_long = true; else lowercase_long = false;
                long_count++;
            }
        } else if (c == 'i' || c == 'I' || c == 'j' || c == 'J') {
            if (isImaginary) {
                error_occurred("duplicate imaginary suffix on integer constant", start_loc);
                return std::nullopt;
            }
            isImaginary = true;
        } else {
            break;
        }
        advance();
    }
    TokenType tt;
    if (long_count == 2) {
        if (isUnsigned) {
            tt = TokenType::UNSIGNED_LONG_LONG_CONST;
        } else {
            tt = TokenType::LONG_LONG_CONST;
        }
    } else if (long_count == 1) {
        if (isUnsigned) {
            tt = TokenType::UNSIGNED_LONG_CONST;
        } else {
            tt = TokenType::LONG_CONST;
        }
    } else {
        if (isUnsigned) {
            tt = TokenType::UNSIGNED_INTEGER_CONST;
        } else {
            tt = TokenType::INTEGER_CONST;
        }
    }
    if (isImaginary) {
        switch (tt) {
            case TokenType::INTEGER_CONST: tt = TokenType::IMAG_INTEGER_CONST; break;
            case TokenType::UNSIGNED_INTEGER_CONST: tt = TokenType::IMAG_UNSIGNED_INTEGER_CONST; break;
            case TokenType::LONG_CONST: tt = TokenType::IMAG_LONG_CONST; break;
            case TokenType::UNSIGNED_LONG_CONST: tt = TokenType::IMAG_UNSIGNED_LONG_CONST; break;
            case TokenType::LONG_LONG_CONST: tt = TokenType::IMAG_LONG_LONG_CONST; break;
            case TokenType::UNSIGNED_LONG_LONG_CONST: tt = TokenType::IMAG_UNSIGNED_LONG_LONG_CONST; break;
            default:
                break;
        }
    }
    if (is_nondigit(current_char()) || is_digit(current_char())) {
        error_occurred("invalid suffix on integer constant", start_loc);
        return std::nullopt;
    }
    return Token(tt, number, start_loc);

}
std::optional<Token> Lexer::read_pp_number() {
    // C standard 6.4.8: pp-number is digit | . digit followed by
    // (digit | nondigit | e[+-] | E[+-] | p[+-] | P[+-] | .)*
    SrcLoc start_loc = get_loc_at_pos();
    std::string number;
    number += current_char();
    advance();
    while (true) {
        char c = current_char();
        // Check exponent-sign sequences BEFORE is_nondigit, since e/E/p/P
        // are also nondigits and would be consumed without the +/- sign
        if ((c == 'e' || c == 'E' || c == 'p' || c == 'P') &&
            (peek_char() == '+' || peek_char() == '-')) {
            number += c;
            advance();
            number += current_char();
            advance();
            continue;
        }
        if (is_digit(c) || is_nondigit(c) || c == '.') {
            number += c;
            advance();
            continue;
        }
        break;
    }
    return Token(TokenType::PP_NUMBER, number, start_loc);
}
std::optional<Token> Lexer::read_identifier() {
    SrcLoc start_loc = get_loc_at_pos();
    const size_t identifier_start = position;
    const char* data = source.data();
    const size_t source_len = source.size();

    size_t end = identifier_start + 1;
    while (end < source_len && is_ascii_identifier_continue(data[end])) {
        ++end;
    }
    position = end;

    std::string_view identifier(data + identifier_start, position - identifier_start);
    TokenType type = lookup_keyword(identifier, lang_opts);

    return Token(type, std::string(identifier), start_loc);
}
uint32_t Lexer::get_special_char() {
    char code = current_char();
    advance();
    switch (code) {
        case 'a': return '\a';
        case 'b': return '\b';
        case 'f': return '\f';
        case 'n': return '\n';
        case 'r': return '\r';
        case 't': return '\t';
        case 'v': return '\v';
        case 'e': return '\x1b';
        case 'E': return '\x1b';
        case '\\': return '\\';
        default: return code;
    }

}
std::optional<Token> Lexer::read_char_literal(SrcLoc start_loc, LiteralPrefix prefix) {
    std::string value;
    advance(); // skip '

    char curr = current_char();
    while (curr != '\'') {
        if (curr == '\0' || curr == '\n') {
            // this is the actual symbol for null or new line, not the escape
            if (pp_number_mode) {
                // In preprocessing mode, keep invalid pp-tokens recoverable so
                // directives like '#define A ''' don't hard-stop translation.
                return Token(TokenType::UNKNOWN, "\'", start_loc);
            }
            error_occurred("error in parsing string literal", start_loc);
        }
        if (curr == '\\') {
            advance();
            value += read_escape_sequence();
            curr = current_char();
            continue;
        }
        if (static_cast<unsigned char>(curr) & 0x80) {
            // Inside char literals, non-ASCII bytes are stored as-is
            // (they may not be valid UTF-8, e.g. raw \xff)
            value += curr;
            advance();
            curr = current_char();
            continue;
        }
        value += curr;
        advance();
        curr = current_char();
    }
    advance();
    Token tok(TokenType::CHAR_LITERAL, value, start_loc);
    tok.literal_prefix = prefix;
    return tok;
}
// todo: combine with above?
std::optional<Token> Lexer::read_string_literal(SrcLoc start_loc, LiteralPrefix prefix) {
    std::string value;
    advance(); // skip "

    char curr = current_char();
    while (curr != '"') {
        if (curr == '\0' || curr == '\n') {
            // this is the actual symbol for null or new line, not the escape
            if (pp_number_mode) {
                // In preprocessing mode, keep invalid pp-tokens recoverable so
                // directives like '#define A \"' don't hard-stop translation.
                return Token(TokenType::UNKNOWN, "\"", start_loc);
            }
            error_occurred("error in parsing string literal", start_loc);
        }
        if (curr == '\\') {
            advance();
            value += read_escape_sequence();
            curr = current_char();
            continue;
        }
        if (static_cast<unsigned char>(curr) & 0x80) {
            // Inside string literals, non-ASCII bytes are stored as-is
            // (they may not be valid UTF-8, e.g. raw \xff)
            value += curr;
            advance();
            curr = current_char();
            continue;
        }
        value += curr;
        advance();
        curr = current_char();
    }
    advance();
    Token tok(TokenType::STRING_LITERAL, value, start_loc);
    tok.literal_prefix = prefix;
    return tok;
}
bool Lexer::is_exhausted() {
    return current_char() == '\0';
}

std::optional<Token> Lexer::next_token() {
    char prev_ch = prev_char();
    prev_whitespace.reset();
    auto tok = next_token2();
    if (!tok.has_value()) {
        return std::nullopt;
    }
    uint32_t bef_newline = 0;
    uint32_t bef_space = 0;
    bool prev_is_newline = (prev_ch == '\n' || prev_ch == '\0');
    bool skipped_newline = (prev_whitespace.has_value() && prev_whitespace.value() == '\n') ||
        (pending_leading_space.has_value() && pending_leading_space.value() == '\n');
    if (prev_is_newline || skipped_newline || pending_start_of_line) {
        bef_newline = 1;
    }
    if (!bef_newline) {
        if (prev_whitespace.has_value() || pending_leading_space.has_value()) {
            bef_space = 1;
        } else if (is_ascii_space(prev_ch)) {
            bef_space = 1; // todo: see if we have situation of \n (whitespace) <char>
        }
    }
    tok->flags.start_of_line = bef_newline;
    tok->flags.has_leading_space = bef_space;
    if (tok->type == TokenType::Whitespace) {
        if (tok->flags.start_of_line) {
            pending_start_of_line = true;
        }
    } else {
        pending_start_of_line = false;
    }
    if (tok->type != TokenType::Whitespace && tok->type != TokenType::Newline) {
        pending_leading_space.reset();
    }
    return tok;
}

std::optional<Token> Lexer::next_token2() {
    const bool cxx_mode = lang_opts.is_cxx_mode();
    while (current_char() != '\0') {
        if (current_char() == '/' && peek_char() == '/') {
            // Line comment: skip to newline but don't consume it.
            SrcLoc start_loc = get_loc_at_pos();
            advance();
            advance();
            while (current_char() != '\n' && current_char() != '\0') {
                advance();
            }
            if (emit_comment_whitespace) {
                pending_leading_space = ' ';
                return Token(TokenType::Whitespace, " ", start_loc);
            }
            prev_whitespace = ' '; // comment replaced with a single space
            continue;
        }
        if (current_char() == '/' && peek_char() == '*') {
            // Block comment: consume entirely and replace with a single space.
            SrcLoc start_loc = get_loc_at_pos();
            advance();
            advance();
            while (true) {
                char c = current_char();
                if (c == '\0') {
                    error_occurred("Unterminated block comment");
                }
                if (c == '*' && peek_char() == '/') {
                    advance();
                    advance();
                    break;
                }
                advance();
            }
            if (emit_comment_whitespace) {
                pending_leading_space = ' ';
                return Token(TokenType::Whitespace, " ", start_loc);
            }
            prev_whitespace = ' '; // comment replaced with a single space
            continue;
        }
        if (is_ascii_space(current_char())) {
            char cur = current_char();
            if (cur == '\n' && enable_new_line_token) {
                auto ret = Token(TokenType::Newline, "\n", get_loc_at_pos());
                advance();
                return ret;
            } else if (enable_whitespace_token) {
                auto ret = Token(TokenType::Whitespace, std::to_string(cur), get_loc_at_pos());
                advance();
                return ret;
            }
            prev_whitespace = cur;
            advance();
            continue;
        }
        SrcLoc start_loc = get_loc_at_pos();
        char c = current_char();
        if (c == '.' && peek_char() == '.' && peek_char(2) == '.') {
            SrcLoc start_loc = get_loc_at_pos();
            advance();
            advance();
            advance();
            return Token(TokenType::ELLIPSIS, "...", start_loc);
        }
        if (c == 'L' || c == 'u' || c == 'U') {
            SrcLoc start_loc = get_loc_at_pos();
            if (c == 'u' && peek_char() == '8' && (peek_char(2) == '"' || peek_char(2) == '\'')) {
                advance();
                advance();
                if (current_char() == '"') {
                    return read_string_literal(start_loc, LiteralPrefix::U8);
                }
                return read_char_literal(start_loc, LiteralPrefix::U8);
            }
            if (peek_char() == '"' || peek_char() == '\'') {
                advance();
                if (current_char() == '"') {
                    return read_string_literal(start_loc, c == 'L' ? LiteralPrefix::L
                        : (c == 'U' ? LiteralPrefix::U : LiteralPrefix::u));
                }
                return read_char_literal(start_loc, c == 'L' ? LiteralPrefix::L
                    : (c == 'U' ? LiteralPrefix::U : LiteralPrefix::u));
            }
        }
        if (is_digit(c) || (c == '.' && is_digit(peek_char()))) {
            if (pp_number_mode) {
                return read_pp_number();
            }
            return read_number();
        }
        if (cxx_mode && c == '.' && peek_char() == '*') {
            advance();
            advance();
            return Token(TokenType::DOT_STAR, ".*", start_loc);
        }
        if (is_nondigit(c)) {
            return read_identifier();
        }
        if (c == '\'') {
            return read_char_literal(get_loc_at_pos(), LiteralPrefix::None);
        }
        if (c == '"') {
            return read_string_literal(get_loc_at_pos(), LiteralPrefix::None);
        }
        if (c == '&') {
            advance();
            if (current_char() == '&') {
                advance();
                return Token(TokenType::LOGICAL_AND, "&&", start_loc);
            }
            if (current_char() == '=') {
                advance();
                return Token(TokenType::ASSIGN_AND, "&=", start_loc);
            }
            return Token(TokenType::BITWISE_AND, "&", start_loc);
        }
        if (c == '|') {
            advance();
            if (current_char() == '|') {
                advance();
                return Token(TokenType::LOGICAL_OR, "||", start_loc);
            }
            if (current_char() == '=') {
                advance();
                return Token(TokenType::ASSIGN_OR, "|=", start_loc);
            }
            return Token(TokenType::BITWISE_OR, "|", start_loc);
        }
        if (c == '<') {
            advance();
            if (current_char() == '<') {
                advance();
                if (current_char() == '=') {
                    advance();
                    return Token(TokenType::ASSIGN_LSHIFT, "<<=", start_loc);
                }
                return Token(TokenType::LEFT_SHIFT, "<<", start_loc);
            }
            if (current_char() == '=') {
                advance();
                return Token(TokenType::LESS_EQUAL_THAN, "<=", start_loc);
            }
            return Token(TokenType::LESS_THAN, "<", start_loc);
        }
        if (c == '>') {
            advance();
            if (current_char() == '>') {
                advance();
                if (current_char() == '=') {
                    advance();
                    return Token(TokenType::ASSIGN_RSHIFT, ">>=", start_loc);
                }
                return Token(TokenType::RIGHT_SHIFT, ">>", start_loc);
            }
            if (current_char() == '=') {
                advance();
                return Token(TokenType::GREATER_EQUAL_THAN, ">=", start_loc);
            }
            return Token(TokenType::GREATER_THAN, ">", start_loc);
        }
        if (c == '=') {
            advance();
            if (current_char() == '=') {
                advance();
                return Token(TokenType::EQUAL_TO, "==", start_loc);
            }
            return Token(TokenType::ASSIGN, "=", start_loc);
        }
        if (c == '!') {
            advance();
            if (current_char() == '=') {
                advance();
                return Token(TokenType::NOT_EQUAL, "!=", start_loc);
            }
            return Token(TokenType::LOGICAL_NOT, "!", start_loc);
        }
        if (c == '+') {
            advance();
            if (current_char() == '+') {
                advance();
                return Token(TokenType::INCREMENT, "++", start_loc);
            }
            if (current_char() == '=') {
                advance();
                return Token(TokenType::ASSIGN_ADD, "+=", start_loc);
            }
            return Token(TokenType::PLUS, "+", start_loc);
        }
        if (c == '-') {
            advance();
            if (current_char() == '=') {
                advance();
                return Token(TokenType::ASSIGN_SUB, "-=", start_loc);
            }
            if (current_char() == '-') {
                advance();
                return Token(TokenType::DECREMENT, "--", start_loc);
            }
            if (current_char() == '>') {
                advance();
                if (cxx_mode && current_char() == '*') {
                    advance();
                    return Token(TokenType::ARROW_STAR, "->*", start_loc);
                }
                return Token(TokenType::ARROW, "->", start_loc);
            }
            // Already handled decrement and arrow, so this is just unary/binary minus
            return Token(TokenType::NEGATE, "-", start_loc);
        }
        if (cxx_mode && c == ':' && peek_char() == ':') {
            advance();
            advance();
            return Token(TokenType::SCOPE_RESOLUTION, "::", start_loc);
        }
        if (c == '*') {
            advance();
            if (current_char() == '=') {
                advance();
                return Token(TokenType::ASSIGN_MUL, "*=", start_loc);
            }
            return Token(TokenType::MULTIPLY, "*", start_loc);
        }
        if (c == '/') {
            advance();
            if (current_char() == '=') {
                advance();
                return Token(TokenType::ASSIGN_DIV, "/=", start_loc);
            }
            return Token(TokenType::DIVIDE, "/", start_loc);
        }
        if (c == '%') {
            advance();
            if (current_char() == '=') {
                advance();
                return Token(TokenType::ASSIGN_MOD, "%=", start_loc);
            }
            return Token(TokenType::MODULO, "%", start_loc);
        }
        if (c == '^') {
            advance();
            if (current_char() == '=') {
                advance();
                return Token(TokenType::ASSIGN_XOR, "^=", start_loc);
            }
            return Token(TokenType::BITWISE_XOR, "^", start_loc);
        }
        if (c == '#') {
            advance();
            return Token(TokenType::POUND, "#", start_loc);
        }
        if (c == '\\') {
            advance();
            if (current_char() == '\n') {
                advance();
                continue;
            }
        }
        advance();
        switch (c) {
            case ':': return Token(TokenType::COLON, ":", start_loc);
            case '?': return Token(TokenType::QUESTION, "?", start_loc);
            case '(': return Token(TokenType::LEFT_PAREN, "(", start_loc);
            case ')': return Token(TokenType::RIGHT_PAREN, ")", start_loc);
            case '{': return Token(TokenType::LEFT_BRACE, "{", start_loc);
            case '}': return Token(TokenType::RIGHT_BRACE, "}", start_loc);
            case '[': return Token(TokenType::LEFT_BRACKET, "[", start_loc);
            case ']': return Token(TokenType::RIGHT_BRACKET, "]", start_loc);
            case ';': return Token(TokenType::SEMICOLON, ";", start_loc);
            case '~': return Token(TokenType::BITWISE_NOT, "~", start_loc);
            case ',': return Token(TokenType::COMMA, ",", start_loc);
            case '.': return Token(TokenType::DOT, ".", start_loc);

            default:
                return Token(TokenType::UNKNOWN, std::string(1, c), start_loc);
        }
    }
    return Token(TokenType::Eof, "", get_loc_at_pos());
}
std::vector<Token> Lexer::tokenize() {
    std::vector<Token> tokens;

    while (true) {
        auto token = next_token();
        if (!token.has_value() || token->type == TokenType::UNKNOWN) {
            error_occurred("Internal error: no token returned or unknown token returned from next_token()");
            break;
        }
        tokens.push_back(token.value());

        if (token->type == TokenType::Eof) {
            break;
        }
    }

    return tokens;
}
// for extract_utf8()
uint8_t Lexer::get_byte_continuation() {
    char byte = current_char();
    if ((byte & 0xC0) != 0x80) {
        error_occurred("Invalid UTF-8 continuation byte");
    }
    advance();
    return byte & 0x3F;
}

uint32_t Lexer::extract_utf8_code_point() {
    char first = current_char();
    advance();

    // Single byte (ASCII): 0xxxxxxx
    if ((first & 0x80) == 0) {
        return first;
    }
    // Two bytes: 110xxxxx 10xxxxxx
    if ((first & 0xE0) == 0xC0) {
        uint32_t codePoint = (first & 0x1F) << 6;
        codePoint |= get_byte_continuation();

        if (codePoint < 0x80) {
            error_occurred("Overlong UTF-8 encoding");
        }
        return codePoint;
    }
    // Three bytes: 1110xxxx 10xxxxxx 10xxxxxx
    if ((first & 0xF0) == 0xE0) {
        uint32_t codePoint = (first & 0x0F) << 12;
        codePoint |= get_byte_continuation() << 6;
        codePoint |= get_byte_continuation();

        if (codePoint < 0x800) {
            error_occurred("Overlong UTF-8 encoding");
        }
        if (codePoint >= 0xD800 && codePoint <= 0xDFFF) {
            error_occurred("Invalid UTF-8: surrogate code point");
        }
        return codePoint;
    }

    // Four bytes: 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
    if ((first & 0xF8) == 0xF0) {
        uint32_t codePoint = (first & 0x07) << 18;
        codePoint |= get_byte_continuation() << 12;
        codePoint |= get_byte_continuation() << 6;
        codePoint |= get_byte_continuation();

        if (codePoint < 0x10000) {
            error_occurred("Overlong UTF-8 encoding");
        }
        if (codePoint > 0x10FFFF) {
            error_occurred("Invalid UTF-8: code point exceeds maximum");
        }
        return codePoint;
    }

    error_occurred("Invalid UTF-8 leading byte");
    return 0; // should be unreachable
}

static const Token kEofToken{TokenType::Eof, "", 0};

const Token& TokenMgnt::peek_token(size_t offset) const {
    if (!split_tokens.empty()) {
        const size_t split_suffix_count = split_tokens.size() - 1;
        if (offset <= split_suffix_count) {
            return split_tokens[offset];
        }
        size_t underlying_offset = 0;
        if (split_tokens_replace_current) {
            underlying_offset = offset - split_suffix_count;
        } else {
            underlying_offset = offset - split_suffix_count - 1;
        }
        size_t peek_pos = current + underlying_offset;
        if (peek_pos >= tokens.size()) {
            return kEofToken;
        }
        return tokens[peek_pos];
    }
    size_t peek_pos = current + offset;
    if (peek_pos >= tokens.size()) {
        return kEofToken;
    }
    return tokens[peek_pos];
}

void TokenMgnt::advance() {
    if (!split_tokens.empty()) {
        split_tokens.pop_front();
        if (split_tokens.empty() && split_tokens_replace_current && current < tokens.size()) {
            ++current;
        }
        if (split_tokens.empty()) {
            split_tokens_replace_current = false;
        }
        return;
    }
    if (current < tokens.size()) {
        current++;
    }
}
void TokenMgnt::rewind() {
    if (current > 0) {
        current--;
    }
}

bool TokenMgnt::gentle_check_and_consume(TokenType type) {
    if (gentle_check(type)) {
        advance();
        return true;
    }
    return false;
}

bool TokenMgnt::gentle_check(TokenType type) {
    return current_token().type == type;
}

void TokenMgnt::check_custom(TokenType type, std::string &message) {
    if (!gentle_check(type)) {
        error(message, current_token().loc);
    }
}

void TokenMgnt::check_and_consume(TokenType type) {
    check(type);
    // if successful, we will be here
    advance();
}

void TokenMgnt::check(TokenType type) {
    if (!gentle_check(type)) {
        Token got = current_token();
        std::string err = "expected " + token_type_to_string(type) + " but got "
            + (got.type == TokenType::Eof ? "end of file"
               : "'" + got.value + "'");
        error(err, got.loc);
    }
}

void TokenMgnt::error(std::string &str, SrcLoc loc) {
    SrcLoc curr_loc = loc;
    if (curr_loc.isInvalid()) {
        Token curr_tok = current_token();
        if (curr_tok.type != TokenType::Eof) {
            curr_loc = curr_tok.loc;
        } else if (!tokens.empty() && current > 0) {
            size_t idx = std::min(current, tokens.size()) - 1;
            curr_loc = tokens[idx].loc;
        } else {
            curr_loc = curr_tok.loc;
        }
    }
    if (diag_engine) {
        diag_engine->report_error(str, curr_loc);
        throw ParseError(str, curr_loc);
    }
    if (sm && !curr_loc.isInvalid()) {
        throw std::runtime_error(sm->formatDiagnostic(DiagnosticLevel::Error, str, curr_loc));
    }
    throw std::runtime_error("error: " + str);
}

const Token& TokenMgnt::current_token() const {
    if (!split_tokens.empty()) {
        return split_tokens.front();
    }
    if (current >= tokens.size()) {
        return kEofToken;
    }
    return tokens[current];
}

size_t TokenMgnt::get_token_idx() {
    return current;
}

void TokenMgnt::set_token_idx(size_t idx) {
    current = idx;
    split_tokens.clear();
    split_tokens_replace_current = false;
}

TokenMgnt::SplitTokenState TokenMgnt::get_split_token_state() const {
    SplitTokenState state;
    state.tokens.assign(split_tokens.begin(), split_tokens.end());
    state.replaces_current = split_tokens_replace_current;
    return state;
}

void TokenMgnt::set_split_token_state(const SplitTokenState& state) {
    split_tokens.clear();
    split_tokens.insert(split_tokens.end(), state.tokens.begin(), state.tokens.end());
    split_tokens_replace_current = state.replaces_current && !split_tokens.empty();
}

void TokenMgnt::replace_current_token_sequence(std::vector<Token> replacement_tokens) {
    split_tokens.clear();
    split_tokens.insert(split_tokens.end(),
                        replacement_tokens.begin(),
                        replacement_tokens.end());
    split_tokens_replace_current = !split_tokens.empty();
}

std::string token_type_to_string(TokenType type) {
    switch (type) {
        case TokenType::LEFT_PAREN: return "'('";
        case TokenType::RIGHT_PAREN: return "')'";
        case TokenType::LEFT_BRACE: return "'{'";
        case TokenType::RIGHT_BRACE: return "'}'";
        case TokenType::LEFT_BRACKET: return "'['";
        case TokenType::RIGHT_BRACKET: return "']'";
        case TokenType::SEMICOLON: return "';'";
        case TokenType::COMMA: return "','";
        case TokenType::COLON: return "':'";
        case TokenType::DOT: return "'.'";
        case TokenType::DOT_STAR: return "'.*'";
        case TokenType::ARROW: return "'->'";
        case TokenType::ARROW_STAR: return "'->*'";
        case TokenType::SCOPE_RESOLUTION: return "'::'";
        case TokenType::ELLIPSIS: return "'...'";
        case TokenType::QUESTION: return "'?'";
        case TokenType::POUND: return "'#'";
        case TokenType::PLUS: return "'+'";
        case TokenType::NEGATE: return "'-'";
        case TokenType::MULTIPLY: return "'*'";
        case TokenType::DIVIDE: return "'/'";
        case TokenType::MODULO: return "'%'";
        case TokenType::BITWISE_AND: return "'&'";
        case TokenType::BITWISE_OR: return "'|'";
        case TokenType::BITWISE_XOR: return "'^'";
        case TokenType::BITWISE_NOT: return "'~'";
        case TokenType::LOGICAL_AND: return "'&&'";
        case TokenType::LOGICAL_OR: return "'||'";
        case TokenType::LOGICAL_NOT: return "'!'";
        case TokenType::INCREMENT: return "'++'";
        case TokenType::DECREMENT: return "'--'";
        case TokenType::LEFT_SHIFT: return "'<<'";
        case TokenType::RIGHT_SHIFT: return "'>>'";
        case TokenType::LESS_THAN: return "'<'";
        case TokenType::LESS_EQUAL_THAN: return "'<='";
        case TokenType::GREATER_THAN: return "'>'";
        case TokenType::GREATER_EQUAL_THAN: return "'>='";
        case TokenType::EQUAL_TO: return "'=='";
        case TokenType::NOT_EQUAL: return "'!='";
        case TokenType::ASSIGN: return "'='";
        case TokenType::ASSIGN_ADD: return "'+='";
        case TokenType::ASSIGN_SUB: return "'-='";
        case TokenType::ASSIGN_MUL: return "'*='";
        case TokenType::ASSIGN_DIV: return "'/='";
        case TokenType::ASSIGN_MOD: return "'%='";
        case TokenType::ASSIGN_LSHIFT: return "'<<='";
        case TokenType::ASSIGN_RSHIFT: return "'>>='";
        case TokenType::ASSIGN_AND: return "'&='";
        case TokenType::ASSIGN_XOR: return "'^='";
        case TokenType::ASSIGN_OR: return "'|='";
        case TokenType::INT: return "'int'";
        case TokenType::LONG: return "'long'";
        case TokenType::SHORT: return "'short'";
        case TokenType::CHAR: return "'char'";
        case TokenType::VOID: return "'void'";
        case TokenType::FLOAT: return "'float'";
        case TokenType::DOUBLE: return "'double'";
        case TokenType::SIGNED: return "'signed'";
        case TokenType::UNSIGNED: return "'unsigned'";
        case TokenType::BOOL: return "'_Bool'";
        case TokenType::WCHAR_T: return "'wchar_t'";
        case TokenType::CHAR16_T: return "'char16_t'";
        case TokenType::CHAR32_T: return "'char32_t'";
        case TokenType::STRUCT: return "'struct'";
        case TokenType::UNION: return "'union'";
        case TokenType::ENUM: return "'enum'";
        case TokenType::CONST: return "'const'";
        case TokenType::VOLATILE: return "'volatile'";
        case TokenType::RESTRICT: return "'restrict'";
        case TokenType::ATOMIC: return "'_Atomic'";
        case TokenType::STATIC: return "'static'";
        case TokenType::EXTERN: return "'extern'";
        case TokenType::AUTO: return "'auto'";
        case TokenType::REGISTER: return "'register'";
        case TokenType::TYPEDEF: return "'typedef'";
        case TokenType::INLINE: return "'inline'";
        case TokenType::RETURN: return "'return'";
        case TokenType::IF: return "'if'";
        case TokenType::ELSE: return "'else'";
        case TokenType::SWITCH: return "'switch'";
        case TokenType::CASE: return "'case'";
        case TokenType::DEFAULT: return "'default'";
        case TokenType::GOTO: return "'goto'";
        case TokenType::DO: return "'do'";
        case TokenType::WHILE: return "'while'";
        case TokenType::CONTINUE: return "'continue'";
        case TokenType::BREAK: return "'break'";
        case TokenType::FOR: return "'for'";
        case TokenType::SIZEOF: return "'sizeof'";
        case TokenType::CLASS: return "'class'";
        case TokenType::USING: return "'using'";
        case TokenType::NAMESPACE: return "'namespace'";
        case TokenType::TEMPLATE: return "'template'";
        case TokenType::TYPENAME: return "'typename'";
        case TokenType::NEW: return "'new'";
        case TokenType::DELETE: return "'delete'";
        case TokenType::TRY_KW: return "'try'";
        case TokenType::CATCH_KW: return "'catch'";
        case TokenType::THROW_KW: return "'throw'";
        case TokenType::NOEXCEPT_KW: return "'noexcept'";
        case TokenType::OPERATOR_KW: return "'operator'";
        case TokenType::THIS_KW: return "'this'";
        case TokenType::TRUE_KW: return "'true'";
        case TokenType::FALSE_KW: return "'false'";
        case TokenType::NULLPTR_KW: return "'nullptr'";
        case TokenType::DECLTYPE_KW: return "'decltype'";
        case TokenType::PUBLIC_KW: return "'public'";
        case TokenType::PRIVATE_KW: return "'private'";
        case TokenType::PROTECTED_KW: return "'protected'";
        case TokenType::VIRTUAL_KW: return "'virtual'";
        case TokenType::FRIEND_KW: return "'friend'";
        case TokenType::EXPLICIT_KW: return "'explicit'";
        case TokenType::CONSTEXPR_KW: return "'constexpr'";
        case TokenType::CONCEPT_KW: return "'concept'";
        case TokenType::REQUIRES_KW: return "'requires'";
        case TokenType::NULLABILITY_QUALIFIER: return "nullability qualifier";
        case TokenType::IDENTIFIER: return "identifier";
        case TokenType::INTEGER_CONST: return "integer constant";
        case TokenType::UNSIGNED_INTEGER_CONST: return "unsigned integer constant";
        case TokenType::LONG_CONST: return "long integer constant";
        case TokenType::UNSIGNED_LONG_CONST: return "unsigned long integer constant";
        case TokenType::LONG_LONG_CONST: return "long long integer constant";
        case TokenType::UNSIGNED_LONG_LONG_CONST: return "unsigned long long integer constant";
        case TokenType::FLOAT_CONST: return "float constant";
        case TokenType::DOUBLE_CONST: return "double constant";
        case TokenType::LONG_DOUBLE_CONST: return "long double constant";
        case TokenType::IMAG_FLOAT_CONST: return "imaginary float constant";
        case TokenType::IMAG_DOUBLE_CONST: return "imaginary double constant";
        case TokenType::IMAG_LONG_DOUBLE_CONST: return "imaginary long double constant";
        case TokenType::IMAG_INTEGER_CONST: return "imaginary integer constant";
        case TokenType::IMAG_UNSIGNED_INTEGER_CONST: return "imaginary unsigned integer constant";
        case TokenType::IMAG_LONG_CONST: return "imaginary long integer constant";
        case TokenType::IMAG_UNSIGNED_LONG_CONST: return "imaginary unsigned long integer constant";
        case TokenType::IMAG_LONG_LONG_CONST: return "imaginary long long integer constant";
        case TokenType::IMAG_UNSIGNED_LONG_LONG_CONST: return "imaginary unsigned long long integer constant";
        case TokenType::CHAR_LITERAL: return "character literal";
        case TokenType::STRING_LITERAL: return "string literal";
        case TokenType::PP_NUMBER: return "preprocessing number";
        case TokenType::Eof: return "end of file";
        default: return "token";
    }
}
