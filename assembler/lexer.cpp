#include "lexer.h"

namespace aburi::assembler {

namespace {

bool is_ident_start(char c) {
    return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_' ||
           c == '.';
}

bool is_ident_char(char c) {
    return is_ident_start(c) || (c >= '0' && c <= '9') || c == '$';
}

bool is_digit(char c) {
    return c >= '0' && c <= '9';
}

bool is_hex_digit(char c) {
    return is_digit(c) || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F');
}

int hex_value(char c) {
    if (is_digit(c)) {
        return c - '0';
    }
    if (c >= 'a' && c <= 'f') {
        return c - 'a' + 10;
    }
    return c - 'A' + 10;
}

}

Lexer::Lexer(std::string_view source) : source_(source) {}

char Lexer::current() const {
    return pos_ < source_.size() ? source_[pos_] : '\0';
}

char Lexer::lookahead(size_t distance) const {
    return pos_ + distance < source_.size() ? source_[pos_ + distance] : '\0';
}

void Lexer::advance() {
    if (pos_ >= source_.size()) {
        return;
    }
    if (source_[pos_] == '\n') {
        ++line_;
        col_ = 1;
    } else {
        ++col_;
    }
    ++pos_;
}

const Token& Lexer::peek() {
    fill(1);
    return buffer_[0];
}

const Token& Lexer::peek_second() {
    fill(2);
    return buffer_[1];
}

Token Lexer::take() {
    fill(1);
    Token token = buffer_[0];
    buffer_[0] = buffer_[1];
    --buffered_;
    return token;
}

void Lexer::skip_to_statement_end() {
    for (;;) {
        Token token = take();
        if (token.kind == TokKind::Newline || token.kind == TokKind::End) {
            return;
        }
    }
}

void Lexer::fill(int count) {
    while (buffered_ < count) {
        buffer_[buffered_++] = scan();
    }
}

bool Lexer::skip_trivia() {
    for (;;) {
        char c = current();
        if (c == ' ' || c == '\t' || c == '\r') {
            advance();
            continue;
        }
        if (c == '\\' &&
            (lookahead() == '\n' ||
             (lookahead() == '\r' && lookahead(2) == '\n'))) {
            advance();
            if (current() == '\r') {
                advance();
            }
            advance();
            continue;
        }
        if (c == '/' && lookahead() == '/') {
            while (current() != '\n' && current() != '\0') {
                advance();
            }
            continue;
        }
        if (c == '/' && lookahead() == '*') {
            advance();
            advance();
            while (current() != '\0' &&
                   !(current() == '*' && lookahead() == '/')) {
                advance();
            }
            if (current() != '\0') {
                advance();
                advance();
            }
            continue;
        }
        if (c == '#' && (statement_start_ || hash_comments_)) {
            while (current() != '\n' && current() != '\0') {
                advance();
            }
            continue;
        }
        return c != '\0';
    }
}

Token Lexer::scan() {
    if (!skip_trivia()) {
        Token token;
        token.kind = TokKind::End;
        token.line = line_;
        token.col = col_;
        return token;
    }

    char c = current();
    if (c == '\n' || c == ';') {
        Token token;
        token.kind = TokKind::Newline;
        token.line = line_;
        token.col = col_;
        advance();
        statement_start_ = true;
        return token;
    }

    statement_start_ = false;
    if (is_ident_start(c)) {
        return scan_ident();
    }
    if (is_digit(c)) {
        return scan_number();
    }
    if (c == '"') {
        return scan_string();
    }
    if (c == '\'') {
        return scan_char_literal();
    }

    Token token;
    token.line = line_;
    token.col = col_;
    if (c == '<' && lookahead() == '<') {
        token.kind = TokKind::LShift;
        advance();
        advance();
        return token;
    }
    if (c == '>' && lookahead() == '>') {
        token.kind = TokKind::RShift;
        advance();
        advance();
        return token;
    }
    token.kind = TokKind::Punct;
    token.punct = c;
    advance();
    return token;
}

Token Lexer::scan_ident() {
    Token token;
    token.kind = TokKind::Ident;
    token.line = line_;
    token.col = col_;
    size_t start = pos_;
    while (is_ident_char(current())) {
        advance();
    }
    token.text = source_.substr(start, pos_ - start);
    return token;
}

Token Lexer::scan_number() {
    Token token;
    token.kind = TokKind::Integer;
    token.line = line_;
    token.col = col_;

    uint64_t value = 0;
    if (current() == '0' && (lookahead() == 'x' || lookahead() == 'X') &&
        is_hex_digit(lookahead(2))) {
        advance();
        advance();
        while (is_hex_digit(current())) {
            value = value * 16 + static_cast<uint64_t>(hex_value(current()));
            advance();
        }
        token.value = static_cast<int64_t>(value);
        return token;
    }
    if (current() == '0' && (lookahead() == 'b' || lookahead() == 'B') &&
        (lookahead(2) == '0' || lookahead(2) == '1')) {
        advance();
        advance();
        while (current() == '0' || current() == '1') {
            value = value * 2 + static_cast<uint64_t>(current() - '0');
            advance();
        }
        token.value = static_cast<int64_t>(value);
        return token;
    }

    size_t start = pos_;
    bool octal = current() == '0';
    uint64_t decimal = 0;
    while (is_digit(current())) {
        decimal = decimal * 10 + static_cast<uint64_t>(current() - '0');
        advance();
    }
    if ((current() == 'b' || current() == 'f') && !is_ident_char(lookahead())) {
        token.kind = TokKind::LocalRef;
        token.value = static_cast<int64_t>(decimal);
        token.backward = current() == 'b';
        advance();
        return token;
    }
    if (octal) {
        for (size_t i = start; i < pos_; ++i) {
            value = value * 8 + static_cast<uint64_t>(source_[i] - '0');
        }
    } else {
        value = decimal;
    }
    token.value = static_cast<int64_t>(value);
    return token;
}

Token Lexer::scan_string() {
    Token token;
    token.kind = TokKind::String;
    token.line = line_;
    token.col = col_;
    advance();

    std::string decoded;
    while (current() != '"' && current() != '\n' && current() != '\0') {
        char c = current();
        if (c != '\\') {
            decoded.push_back(c);
            advance();
            continue;
        }
        advance();
        char escape = current();
        switch (escape) {
            case 'b': decoded.push_back('\b'); advance(); break;
            case 'f': decoded.push_back('\f'); advance(); break;
            case 'n': decoded.push_back('\n'); advance(); break;
            case 'r': decoded.push_back('\r'); advance(); break;
            case 't': decoded.push_back('\t'); advance(); break;
            case '\\': decoded.push_back('\\'); advance(); break;
            case '"': decoded.push_back('"'); advance(); break;
            case '\'': decoded.push_back('\''); advance(); break;
            case 'x': {
                advance();
                unsigned value = 0;
                while (is_hex_digit(current())) {
                    value = value * 16 +
                            static_cast<unsigned>(hex_value(current()));
                    advance();
                }
                decoded.push_back(static_cast<char>(value & 0xFF));
                break;
            }
            default:
                if (escape >= '0' && escape <= '7') {
                    unsigned value = 0;
                    int digits = 0;
                    while (digits < 3 && current() >= '0' && current() <= '7') {
                        value = value * 8 +
                                static_cast<unsigned>(current() - '0');
                        advance();
                        ++digits;
                    }
                    decoded.push_back(static_cast<char>(value & 0xFF));
                } else {
                    decoded.push_back(escape);
                    advance();
                }
                break;
        }
    }
    if (current() == '"') {
        advance();
    }
    decoded_strings_.push_back(std::move(decoded));
    token.text = decoded_strings_.back();
    return token;
}

Token Lexer::scan_char_literal() {
    Token token;
    token.kind = TokKind::Integer;
    token.line = line_;
    token.col = col_;
    advance();

    char c = current();
    if (c == '\\') {
        advance();
        switch (current()) {
            case 'b': c = '\b'; break;
            case 'f': c = '\f'; break;
            case 'n': c = '\n'; break;
            case 'r': c = '\r'; break;
            case 't': c = '\t'; break;
            case '\\': c = '\\'; break;
            case '\'': c = '\''; break;
            case '"': c = '"'; break;
            case '0': c = '\0'; break;
            default: c = current(); break;
        }
        advance();
    } else if (c != '\0' && c != '\n') {
        advance();
    }
    if (current() == '\'') {
        advance();
    }
    token.value = static_cast<unsigned char>(c);
    return token;
}

}
