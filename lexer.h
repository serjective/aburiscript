#ifndef ABURI_LEXER_H
#define ABURI_LEXER_H

#include <string>
#include <type_traits>
#include <utility>
#include <vector>
#include <deque>
#include "source_mgnt.h"
#include "lang_options.h"
#include <memory>
#include <set>
#include <unordered_set>

enum class TokenType {
    UNKNOWN,
    IDENTIFIER,
    INTEGER_CONST,
    UNSIGNED_INTEGER_CONST,
    LONG_CONST,
    UNSIGNED_LONG_CONST,
    LONG_LONG_CONST,
    UNSIGNED_LONG_LONG_CONST,
    BITINT_CONST,
    UNSIGNED_BITINT_CONST,
    FLOAT_CONST,
    DOUBLE_CONST,
    LONG_DOUBLE_CONST,
    CHAR_LITERAL,
    STRING_LITERAL,
    LEFT_PAREN,
    RIGHT_PAREN,
    LEFT_BRACE,
    RIGHT_BRACE,
    LEFT_BRACKET,
    RIGHT_BRACKET,
    AT,
    SEMICOLON,
    NEGATE,
    BITWISE_NOT,
    LOGICAL_NOT,
    INCREMENT,
    DECREMENT,
    PLUS,
    MULTIPLY,
    DIVIDE,
    MODULO,
    BITWISE_AND,
    BITWISE_OR,
    BITWISE_XOR,
    LOGICAL_AND,
    LOGICAL_OR,
    LEFT_SHIFT,
    RIGHT_SHIFT,
    QUESTION,
    COLON,
    COMMA,
    DOT,
    DOT_STAR,
    ELLIPSIS,
    ARROW,
    ARROW_STAR,
    SCOPE_RESOLUTION,
    REFLECT,
    SPLICE_OPEN,
    SPLICE_CLOSE,
    POUND,
    BACKSLASH,
    INT,
    LONG,
    SIGNED,
    UNSIGNED,
    BOOL,
    WCHAR_T,
    CHAR8_T,
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
    CONST,
    VOLATILE,
    RESTRICT,
    ATOMIC,
    STATIC,
    EXTERN,
    AUTO,
    REGISTER,
    TYPEDEF,
    RETURN,
    IF,
    ELSE,
    SWITCH,
    CASE,
    DEFAULT,
    GOTO,
    DO,
    WHILE,
    CONTINUE,
    BREAK,
    FOR,
    INLINE,
    NORETURN_KW,
    STATIC_ASSERT,
    ALIGNOF,
    ALIGNAS,
    THREAD_LOCAL,
    GENERIC,
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
    TYPEID_KW,
    PUBLIC_KW,
    PRIVATE_KW,
    PROTECTED_KW,
    VIRTUAL_KW,
    FRIEND_KW,
    EXPLICIT_KW,
    MUTABLE_KW,
    CONSTEXPR_KW,
    CONSTEVAL_KW,
    CONSTINIT_KW,
    CONCEPT_KW,
    REQUIRES_KW,
    CO_AWAIT_KW,
    CO_YIELD_KW,
    CO_RETURN_KW,
    EXTENSION_KW,
    TYPEOF_KW,
    TYPEOF_UNQUAL_KW,
    LABEL_KW,
    INT128,
    UINT128_T,
    BITINT_KW,
    AUTO_TYPE,
    COMPLEX,
    FLOAT16,
    REAL_PART,
    IMAG_PART,
    IMAG_FLOAT_CONST,
    IMAG_DOUBLE_CONST,
    IMAG_LONG_DOUBLE_CONST,
    IMAG_INTEGER_CONST,
    IMAG_UNSIGNED_INTEGER_CONST,
    IMAG_LONG_CONST,
    IMAG_UNSIGNED_LONG_CONST,
    IMAG_LONG_LONG_CONST,
    IMAG_UNSIGNED_LONG_LONG_CONST,
    NULLABILITY_QUALIFIER,
    SIZEOF,
    LESS_THAN,
    LESS_EQUAL_THAN,
    THREE_WAY_COMPARE,
    GREATER_THAN,
    GREATER_EQUAL_THAN,
    EQUAL_TO,
    NOT_EQUAL,
    ASSIGN,
    ASSIGN_MUL,
    ASSIGN_DIV,
    ASSIGN_MOD,
    ASSIGN_ADD,
    ASSIGN_SUB,
    ASSIGN_LSHIFT,
    ASSIGN_RSHIFT,
    ASSIGN_AND,
    ASSIGN_XOR,
    ASSIGN_OR,
    ATTRIBUTE_KW,
    ASM_KW,
    MODULE_KEYWORD,
    IMPORT_KEYWORD,
    EXPORT_KEYWORD,
    PP_NUMBER,
    Newline,
    Whitespace,
    Eof,
    LITERAL_SUFFIX,

};
std::string token_type_to_string(TokenType type);
struct LangOptions;

TokenType aburi_lookup_keyword(std::string_view ident, const LangOptions& lang_opts);

enum class LiteralPrefix {
    None,
    L,
    U8,
    U,
    u
};

using HideSetId = uint32_t;

class IdentTable {
public:
    struct Info {
        std::string_view spelling;
        TokenType keyword;
        bool maybe_macro = false;
    };

    uint32_t lookup(std::string_view name) const {
        auto it = map_.find(name);
        return it == map_.end() ? 0 : it->second;
    }
    template <typename KeywordFn>
    uint32_t intern(std::string_view stable_name, KeywordFn&& classify) {
        auto [it, inserted] =
            map_.emplace(stable_name, static_cast<uint32_t>(infos_.size() + 1));
        if (inserted) {
            infos_.push_back(Info{stable_name, classify(stable_name), false});
        }
        return it->second;
    }
    Info& info(uint32_t id) { return infos_[id - 1]; }
    const Info& info(uint32_t id) const { return infos_[id - 1]; }

private:
    std::unordered_map<std::string_view, uint32_t> map_;
    std::vector<Info> infos_;
};

struct Token {
    TokenType type;
    HideSetId hide_set = 0;
    std::string_view value;
    SrcLoc loc;
    LiteralPrefix literal_prefix;
    struct {
        uint32_t has_leading_space: 1;
        uint32_t start_of_line: 1;
        uint32_t part_of_macro_define: 1;
        uint32_t padding: 29;
    } flags;
    uint32_t ident = 0;
    Token(): type(TokenType::UNKNOWN), hide_set(0), value(), loc(0), literal_prefix(LiteralPrefix::None), flags({0, 0, 0}), ident(0) {};
    Token(TokenType t, std::string_view v, uint32_t global_offset)
        : type(t), hide_set(0), value(v), loc(global_offset), literal_prefix(LiteralPrefix::None),
        flags({0, 0, 0}), ident(0) {}
    Token(TokenType t, std::string_view v, SrcLoc srcloc)
    : type(t), hide_set(0), value(v), loc(srcloc), literal_prefix(LiteralPrefix::None),
    flags({0, 0, 0}), ident(0) {}

    bool isIdentifierLike() const {
        switch (type) {
            case TokenType::IDENTIFIER:

            case TokenType::INT:
            case TokenType::LONG:
            case TokenType::SIGNED:
            case TokenType::UNSIGNED:
            case TokenType::BOOL:
            case TokenType::WCHAR_T:
            case TokenType::CHAR8_T:
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

            case TokenType::CONST:
            case TokenType::VOLATILE:
            case TokenType::RESTRICT:
            case TokenType::ATOMIC:

            case TokenType::STATIC:
            case TokenType::EXTERN:
            case TokenType::AUTO:
            case TokenType::REGISTER:
            case TokenType::TYPEDEF:

            case TokenType::RETURN:
            case TokenType::IF:
            case TokenType::ELSE:
            case TokenType::SWITCH:
            case TokenType::CASE:
            case TokenType::DEFAULT:
            case TokenType::GOTO:

            case TokenType::DO:
            case TokenType::WHILE:
            case TokenType::CONTINUE:
            case TokenType::BREAK:
            case TokenType::FOR:
            case TokenType::INLINE:

            case TokenType::NORETURN_KW:
            case TokenType::STATIC_ASSERT:
            case TokenType::ALIGNOF:
            case TokenType::ALIGNAS:
            case TokenType::THREAD_LOCAL:
            case TokenType::GENERIC:

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
            case TokenType::MUTABLE_KW:
            case TokenType::CONSTEXPR_KW:
            case TokenType::CONSTEVAL_KW:
            case TokenType::CONSTINIT_KW:
            case TokenType::CONCEPT_KW:
            case TokenType::REQUIRES_KW:
            case TokenType::CO_AWAIT_KW:
            case TokenType::CO_YIELD_KW:
            case TokenType::CO_RETURN_KW:

            case TokenType::EXTENSION_KW:
            case TokenType::TYPEOF_KW:
            case TokenType::TYPEOF_UNQUAL_KW:
            case TokenType::INT128:
            case TokenType::UINT128_T:
            case TokenType::AUTO_TYPE:
            case TokenType::FLOAT16:

            case TokenType::SIZEOF:

            case TokenType::REAL_PART:
            case TokenType::IMAG_PART:

            case TokenType::ATTRIBUTE_KW:
            case TokenType::ASM_KW:
            case TokenType::NULLABILITY_QUALIFIER:
                return true;
            default:
                return false;
        }
    }
};

static_assert(std::is_trivially_copyable_v<Token>);
static_assert(sizeof(Token) <= 40);
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
    size_t token_count() const;

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
    std::string_view phase2_original_source;
    const std::vector<MappingStep>* phase2_mapping = nullptr;
    std::optional<char> prev_whitespace;
    std::optional<char> pending_leading_space;
    size_t position;
    bool error_happened;
    bool pending_start_of_line;
    bool enable_new_line_token;
    bool enable_whitespace_token;
    bool emit_comment_whitespace;
    bool pp_number_mode;
    SrcLoc base_loc;
    SourceManager* diag_sm;
    SpellingArena* spelling_arena = nullptr;
    IdentTable* ident_table = nullptr;
    std::optional<Token> pending_literal_suffix;
    std::unique_ptr<SpellingArena> owned_arena_;
    SpellingArena& arena() {
        if (spelling_arena) {
            return *spelling_arena;
        }
        if (diag_sm) {
            return diag_sm->spellings;
        }
        if (!owned_arena_) {
            owned_arena_ = std::make_unique<SpellingArena>();
        }
        return *owned_arena_;
    }
    LangOptions lang_opts;
    explicit Lexer(const std::string_view source, SrcLoc baseLoc, SourceManager* diag_sm = nullptr,
        LangOptions options = LangOptions());
    void reset(std::string_view new_source, SrcLoc new_base);
    void set_phase2_source(std::string_view original_source,
                           const std::vector<MappingStep>* mapping);

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
    void attach_user_defined_literal_suffix(Token& token);
    std::optional<Token> read_char_literal(SrcLoc start_loc, LiteralPrefix prefix);
    std::optional<Token> read_string_literal(SrcLoc start_loc, LiteralPrefix prefix);
    std::optional<Token> read_raw_string_literal(SrcLoc start_loc, LiteralPrefix prefix);

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
        std::optional<Token> pending_literal_suffix;
    };
    LexerState get_state() const {
        return {position, pending_leading_space, pending_start_of_line,
                pending_literal_suffix};
    }
    void set_state(const LexerState& st) {
        position = st.position;
        pending_leading_space = st.pending_leading_space;
        pending_start_of_line = st.pending_start_of_line;
        pending_literal_suffix = st.pending_literal_suffix;
    }
};

#endif //ABURI_LEXER_H
