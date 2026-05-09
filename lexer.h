#ifndef ABURI_LEXER_H
#define ABURI_LEXER_H

#include <string>
#include <utility>
#include <vector>
#include <deque>
#include "source_mgnt.h"
#include "lang_options.h"
#include <set>
#include <unordered_set>
// Note: We always assume the source document is in UTF-8



enum class TokenType {
    UNKNOWN,
    // Literals
    IDENTIFIER,
    INTEGER_CONST,
    UNSIGNED_INTEGER_CONST,
    LONG_CONST,
    UNSIGNED_LONG_CONST,
    LONG_LONG_CONST,
    UNSIGNED_LONG_LONG_CONST,
    FLOAT_CONST,
    DOUBLE_CONST,
    LONG_DOUBLE_CONST,
    CHAR_LITERAL,
    STRING_LITERAL,
    // Delimiters
    LEFT_PAREN, // (
    RIGHT_PAREN, // )
    LEFT_BRACE,     // {
    RIGHT_BRACE,    // }
    LEFT_BRACKET,   // [
    RIGHT_BRACKET,  // ]
    SEMICOLON, // ;
    // Arithmetic/Logical
    NEGATE, // -
    BITWISE_NOT, // ~
    LOGICAL_NOT, // !
    INCREMENT, // ++
    DECREMENT, // --
    PLUS, // +
    MULTIPLY, // *
    DIVIDE, // /
    MODULO, // %
    BITWISE_AND, // &
    BITWISE_OR, // |
    BITWISE_XOR, // ^
    LOGICAL_AND, // &&
    LOGICAL_OR, // ||
    LEFT_SHIFT, // <<
    RIGHT_SHIFT, // >>
    QUESTION, // ?
    COLON, // :
    COMMA, // ,
    DOT, // .
    DOT_STAR, // .*
    ELLIPSIS, // ...
    ARROW, // ->
    ARROW_STAR, // ->*
    SCOPE_RESOLUTION, // ::
    POUND, // #
    BACKSLASH, // \
    // Type specifiers
    INT,
    LONG,
    SIGNED,
    UNSIGNED,
    BOOL,
    WCHAR_T,
    CHAR16_T,
    CHAR32_T,
    FLOAT,
    DOUBLE,
    CHAR,
    VOID,
    SHORT,
    STRUCT,
    UNION,
    ENUM,
    // Type Qualifiers
    CONST,
    VOLATILE,
    RESTRICT,
    ATOMIC, // _Atomic
    // Storage Class Specifiers
    STATIC,
    EXTERN,
    AUTO,
    REGISTER,
    TYPEDEF,
    // Control flow keywords
    RETURN,
    IF,
    ELSE,
    SWITCH,
    CASE,
    DEFAULT,
    GOTO,
    // Loops
    DO,
    WHILE,
    CONTINUE,
    BREAK,
    FOR,
    INLINE,
    // C11 keywords
    NORETURN_KW,     // _Noreturn
    STATIC_ASSERT,   // _Static_assert
    ALIGNOF,         // _Alignof
    ALIGNAS,         // _Alignas
    THREAD_LOCAL,    // _Thread_local
    GENERIC,         // _Generic
    // C++ keywords
    CLASS,
    USING,
    NAMESPACE,
    TEMPLATE,
    TYPENAME,
    NEW,
    DELETE,
    TRY_KW,
    CATCH_KW,
    THROW_KW,
    NOEXCEPT_KW,
    OPERATOR_KW,
    THIS_KW,
    TRUE_KW,
    FALSE_KW,
    NULLPTR_KW,
    DECLTYPE_KW,
    PUBLIC_KW,
    PRIVATE_KW,
    PROTECTED_KW,
    VIRTUAL_KW,
    FRIEND_KW,
    EXPLICIT_KW,
    CONSTEXPR_KW,
    CONSTEVAL_KW,
    CONCEPT_KW,
    REQUIRES_KW,
    // GCC extensions
    EXTENSION_KW,    // __extension__
    TYPEOF_KW,       // typeof, __typeof__, __typeof
    LABEL_KW,        // __label__
    INT128,          // __int128, __int128_t
    UINT128_T,       // __uint128_t
    AUTO_TYPE,       // __auto_type
    COMPLEX,         // _Complex, __complex__, __complex
    FLOAT16,         // _Float16, __fp16
    REAL_PART,       // __real__, __real
    IMAG_PART,       // __imag__, __imag
    IMAG_FLOAT_CONST,  // 1.0fi, 1.0fj
    IMAG_DOUBLE_CONST, // 1.0i, 1.0j
    IMAG_LONG_DOUBLE_CONST, // 1.0li, 1.0lj
    IMAG_INTEGER_CONST,             // 1i, 1j
    IMAG_UNSIGNED_INTEGER_CONST,    // 1ui
    IMAG_LONG_CONST,                // 1li
    IMAG_UNSIGNED_LONG_CONST,       // 1uli
    IMAG_LONG_LONG_CONST,           // 1lli
    IMAG_UNSIGNED_LONG_LONG_CONST,  // 1ulli
    NULLABILITY_QUALIFIER, // _Nonnull, _Nullable, _Null_unspecified, _Nullable_result
    // Operators
    SIZEOF,
    // Comparision
    LESS_THAN, // <
    LESS_EQUAL_THAN, // <=
    THREE_WAY_COMPARE, // <=>
    GREATER_THAN, // >
    GREATER_EQUAL_THAN, // >=
    EQUAL_TO, // ==
    NOT_EQUAL, // !=
    // Assignment
    ASSIGN, // =
    ASSIGN_MUL, // *=
    ASSIGN_DIV, // /=
    ASSIGN_MOD, // %=
    ASSIGN_ADD, // +=
    ASSIGN_SUB, // -=
    ASSIGN_LSHIFT, // <<=
    ASSIGN_RSHIFT, // >>=
    ASSIGN_AND, // &=
    ASSIGN_XOR, // ^=
    ASSIGN_OR, // |=
    // Attributes
    ATTRIBUTE_KW, // __attribute__
    // Inline assembly
    ASM_KW, // asm, __asm__, __asm
    // Special
    PP_NUMBER, // preprocessing number (e.g. 2A0) - valid only during preprocessing
    Newline, // to be used later
    Whitespace, // " ", "\t", ...
    Eof, // End of file

};
std::string token_type_to_string(TokenType type);

enum class LiteralPrefix {
    None,
    L,
    U8,
    U,
    u
};
using HideSetType = std::shared_ptr<std::unordered_set<std::string>>;
struct Token {
    TokenType type;
    std::string value;
    SrcLoc loc;
    LiteralPrefix literal_prefix;
    struct {
        uint32_t has_leading_space: 1;
        uint32_t start_of_line: 1;
        uint32_t part_of_macro_define: 1; // we can't call preproc direcrives from tokens derived from base
        uint32_t padding: 29;
    } flags;
    HideSetType hide_set; // nullptr = empty hideset. We should never have an initalized set that is empty
    Token(): type(TokenType::UNKNOWN), value(""), loc(0), literal_prefix(LiteralPrefix::None), hide_set(nullptr) {};
    Token(TokenType t, const std::string& v, uint32_t global_offset)
        : type(t), value(v), loc(global_offset), literal_prefix(LiteralPrefix::None),
        flags({0, 0, 0}), hide_set(nullptr) {}
    Token(TokenType t, const std::string& v, SrcLoc srcloc)
    : type(t), value(v), loc(srcloc), literal_prefix(LiteralPrefix::None),
    flags({0, 0, 0}), hide_set(nullptr) {}

    bool isIdentifierLike() const {
        switch (type) {
            case TokenType::IDENTIFIER:
            // Type specifiers
            case TokenType::INT:
            case TokenType::LONG:
            case TokenType::SIGNED:
            case TokenType::UNSIGNED:
            case TokenType::BOOL:
            case TokenType::WCHAR_T:
            case TokenType::CHAR16_T:
            case TokenType::CHAR32_T:
            case TokenType::FLOAT:
            case TokenType::DOUBLE:
            case TokenType::CHAR:
            case TokenType::VOID:
            case TokenType::SHORT:
            case TokenType::STRUCT:
            case TokenType::UNION:
            case TokenType::ENUM:
            // Type qualifiers
            case TokenType::CONST:
            case TokenType::VOLATILE:
            case TokenType::RESTRICT:
            case TokenType::ATOMIC:
            // Storage class specifiers
            case TokenType::STATIC:
            case TokenType::EXTERN:
            case TokenType::AUTO:
            case TokenType::REGISTER:
            case TokenType::TYPEDEF:
            // Control flow keywords
            case TokenType::RETURN:
            case TokenType::IF:
            case TokenType::ELSE:
            case TokenType::SWITCH:
            case TokenType::CASE:
            case TokenType::DEFAULT:
            case TokenType::GOTO:
            // Loops
            case TokenType::DO:
            case TokenType::WHILE:
            case TokenType::CONTINUE:
            case TokenType::BREAK:
            case TokenType::FOR:
            case TokenType::INLINE:
            // C11 keywords
            case TokenType::NORETURN_KW:
            case TokenType::STATIC_ASSERT:
            case TokenType::ALIGNOF:
            case TokenType::ALIGNAS:
            case TokenType::THREAD_LOCAL:
            case TokenType::GENERIC:
            // C++ keywords
            case TokenType::CLASS:
            case TokenType::USING:
            case TokenType::NAMESPACE:
            case TokenType::TEMPLATE:
            case TokenType::TYPENAME:
            case TokenType::NEW:
            case TokenType::DELETE:
            case TokenType::TRY_KW:
            case TokenType::CATCH_KW:
            case TokenType::THROW_KW:
            case TokenType::NOEXCEPT_KW:
            case TokenType::OPERATOR_KW:
            case TokenType::THIS_KW:
            case TokenType::TRUE_KW:
            case TokenType::FALSE_KW:
            case TokenType::NULLPTR_KW:
            case TokenType::DECLTYPE_KW:
            case TokenType::PUBLIC_KW:
            case TokenType::PRIVATE_KW:
            case TokenType::PROTECTED_KW:
            case TokenType::VIRTUAL_KW:
            case TokenType::FRIEND_KW:
            case TokenType::EXPLICIT_KW:
            case TokenType::CONSTEXPR_KW:
            case TokenType::CONSTEVAL_KW:
            case TokenType::CONCEPT_KW:
            case TokenType::REQUIRES_KW:
            // GCC extensions
            case TokenType::EXTENSION_KW:
            case TokenType::TYPEOF_KW:
            case TokenType::INT128:
            case TokenType::UINT128_T:
            case TokenType::AUTO_TYPE:
            case TokenType::FLOAT16:
            // Operators that are keywords
            case TokenType::SIZEOF:
            // Complex number keywords
            case TokenType::REAL_PART:
            case TokenType::IMAG_PART:
            // Attributes/asm keywords
            case TokenType::ATTRIBUTE_KW:
            case TokenType::ASM_KW:
            case TokenType::NULLABILITY_QUALIFIER:
                return true;
            default:
                return false;
        }
    }
};
struct TokenMgnt {
    struct SplitTokenState {
        std::vector<Token> tokens;
        bool replaces_current = false;
    };

    explicit TokenMgnt(std::vector<Token> tokens): tokens(std::move(tokens)), current(0) {};
    explicit TokenMgnt(std::vector<Token> tokens, std::shared_ptr<SourceManager> sm):
    tokens(std::move(tokens)), current(0), sm(std::move(sm)) {};

    std::vector<Token> tokens;
    size_t current;
    std::shared_ptr<SourceManager> sm;
    std::shared_ptr<class DiagnosticEngine> diag_engine;

    const Token& peek_token(size_t offset = 1) const;
    void advance();

    void rewind();

    bool gentle_check_and_consume(TokenType type);
    bool gentle_check(TokenType type);
    void check_custom(TokenType type, std::string &message);
    void check_and_consume(TokenType type);
    void check(TokenType type);
    void error(std::string &str, SrcLoc loc = {});

    const Token& current_token() const;
    size_t get_token_idx();

    void set_token_idx(size_t idx);
    SplitTokenState get_split_token_state() const;
    void set_split_token_state(const SplitTokenState& state);
    void replace_current_token_sequence(std::vector<Token> replacement_tokens);
    bool has_split_tokens() const { return !split_tokens.empty(); }

    std::deque<Token> split_tokens;
    bool split_tokens_replace_current = false;

};
struct Lexer {
    std::string_view source;
    std::optional<char> prev_whitespace;
    // Pending whitespace emitted from comments that should apply to the next real token.
    std::optional<char> pending_leading_space;
    size_t position;
    bool error_happened;
    bool pending_start_of_line;
    bool enable_new_line_token;
    // todo: is this whitespace tihng needed?
    bool enable_whitespace_token;
    bool emit_comment_whitespace;
    bool pp_number_mode;
    SrcLoc base_loc;
    SourceManager* diag_sm;
    LangOptions lang_opts;
    explicit Lexer(const std::string_view source, SrcLoc baseLoc, SourceManager* diag_sm = nullptr,
        LangOptions options = LangOptions());

    char current_char() const;
    char prev_char() const;

    size_t get_char_idx() const;
    size_t set_char_idx(size_t new_pos);

    char peek_char_rev(size_t offset) const;

    char peek_char(size_t offset = 1) const;
    void advance();
    bool is_digit(char c);

    bool is_alphabet(char c);

    bool is_nondigit(char c);
    bool is_oct_digit(char c);
    bool is_bin_digit(char c);
    bool is_hex_digit(char c);
    uint32_t hex_value(char c);
    std::string encode_utf8(uint32_t code_point);
    std::string read_escape_sequence();
    void skip_whitespace();

    void error_occurred(const std::string& err, SrcLoc loc = SrcLoc()) {
        error_happened = true;
        SrcLoc curr_loc = loc;
        if (curr_loc.isInvalid()) {
            curr_loc = get_loc_at_pos();
        }
        if (diag_sm && !curr_loc.isInvalid()) {
            throw std::runtime_error(diag_sm->formatDiagnostic(DiagnosticLevel::Error, err, curr_loc));
        }
        throw std::runtime_error("error in lexer: " + err);
    }
    SrcLoc get_loc_at_pos() const {
        return { base_loc.offset + static_cast<uint32_t>(position) };
    }
    std::optional<Token> read_number();
    std::optional<Token> read_pp_number();
    std::optional<Token> read_identifier();
    std::optional<Token> read_char_literal(SrcLoc start_loc, LiteralPrefix prefix);
    std::optional<Token> read_string_literal(SrcLoc start_loc, LiteralPrefix prefix);

    bool is_exhausted();

    std::optional<Token> next_token();

    std::optional<Token> next_token2();

    std::vector<Token> tokenize();
    uint8_t get_byte_continuation();
    uint32_t get_special_char();
    uint32_t extract_utf8_code_point();

    struct LexerState {
        size_t position;
        std::optional<char> pending_leading_space;
        bool pending_start_of_line;
    };
    LexerState get_state() const {
        return {position, pending_leading_space, pending_start_of_line};
    }
    void set_state(const LexerState& st) {
        position = st.position;
        pending_leading_space = st.pending_leading_space;
        pending_start_of_line = st.pending_start_of_line;
    }
};

#endif //ABURI_LEXER_H
