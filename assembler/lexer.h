#ifndef ABURI_ASSEMBLER_LEXER_H
#define ABURI_ASSEMBLER_LEXER_H

#include <cstdint>
#include <deque>
#include <string>
#include <string_view>

namespace aburi::assembler {

enum class TokKind : uint8_t {
    End,
    Newline,
    Ident,
    Integer,
    LocalRef,
    String,
    LShift,
    RShift,
    Punct,
};

struct Token {
    TokKind kind = TokKind::End;
    std::string_view text;
    int64_t value = 0;
    bool backward = false;
    char punct = 0;
    uint32_t line = 0;
    uint32_t col = 0;
};

class Lexer {
public:
    explicit Lexer(std::string_view source);

    void set_hash_comments(bool enabled) { hash_comments_ = enabled; }

    const Token& peek();
    const Token& peek_second();
    Token take();

    void skip_to_statement_end();

private:
    void fill(int count);
    Token scan();
    char current() const;
    char lookahead(size_t distance = 1) const;
    void advance();
    bool skip_trivia();

    Token scan_ident();
    Token scan_number();
    Token scan_string();
    Token scan_char_literal();

    std::string_view source_;
    size_t pos_ = 0;
    uint32_t line_ = 1;
    uint32_t col_ = 1;
    bool statement_start_ = true;
    bool hash_comments_ = false;

    Token buffer_[2];
    int buffered_ = 0;
    std::deque<std::string> decoded_strings_;
};

}

#endif
