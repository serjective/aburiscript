#ifndef ABURI_TENTATIVE_SYNTAX_PROBE_H
#define ABURI_TENTATIVE_SYNTAX_PROBE_H

#include "../lexer.h"

#include <cstddef>
#include <cstdint>
#include <optional>

namespace tentative_syntax_probe {

enum class Result : uint8_t {
    Match,
    NoMatch,
    Inconclusive,
    Error
};

enum class CxxStatementDisambiguation : uint8_t {
    Declaration,
    Expression,
    Ambiguous,
    Invalid
};

struct Config {
    bool cxx_mode = false;
    bool blocks_enabled = false;
};

namespace detail {

inline bool is_gnu_attribute_token_syntax(const Token& tok) {
    if (tok.type == TokenType::ATTRIBUTE_KW) {
        return true;
    }
    if (tok.type != TokenType::IDENTIFIER) {
        return false;
    }
    return tok.value == "__attribute__" || tok.value == "__attribute";
}

inline bool can_start_cxx_function_style_cast_statement(TokenType token_type) {
    switch (token_type) {
        case TokenType::IDENTIFIER:
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
        case TokenType::CHAR16_T:
        case TokenType::CHAR32_T:
        case TokenType::INT128:
        case TokenType::UINT128_T:
        case TokenType::CONST:
        case TokenType::VOLATILE:
        case TokenType::TYPENAME:
        case TokenType::DECLTYPE_KW:
        case TokenType::TYPEOF_KW:
            return true;
        default:
            return false;
    }
}

inline bool is_cxx_function_style_builtin_type_token(TokenType token_type) {
    switch (token_type) {
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
        case TokenType::CHAR16_T:
        case TokenType::CHAR32_T:
        case TokenType::INT128:
        case TokenType::UINT128_T:
            return true;
        default:
            return false;
    }
}

inline bool is_cxx_function_style_type_qualifier(TokenType token_type) {
    switch (token_type) {
        case TokenType::CONST:
        case TokenType::VOLATILE:
            return true;
        default:
            return false;
    }
}

inline bool can_start_cxx_parenthesized_declarator(TokenType token_type) {
    switch (token_type) {
        case TokenType::IDENTIFIER:
        case TokenType::MULTIPLY:
        case TokenType::BITWISE_AND:
        case TokenType::LOGICAL_AND:
        case TokenType::LEFT_PAREN:
        case TokenType::SCOPE_RESOLUTION:
            return true;
        default:
            return false;
    }
}

inline bool is_cxx_expression_only_in_parenthesized_declarator(TokenType token_type) {
    switch (token_type) {
        case TokenType::INTEGER_CONST:
        case TokenType::UNSIGNED_INTEGER_CONST:
        case TokenType::LONG_CONST:
        case TokenType::UNSIGNED_LONG_CONST:
        case TokenType::LONG_LONG_CONST:
        case TokenType::UNSIGNED_LONG_LONG_CONST:
        case TokenType::FLOAT_CONST:
        case TokenType::DOUBLE_CONST:
        case TokenType::LONG_DOUBLE_CONST:
        case TokenType::CHAR_LITERAL:
        case TokenType::STRING_LITERAL:
        case TokenType::TRUE_KW:
        case TokenType::FALSE_KW:
        case TokenType::NULLPTR_KW:
        case TokenType::THIS_KW:
        case TokenType::SIZEOF:
        case TokenType::ALIGNOF:
        case TokenType::NEW:
        case TokenType::DELETE:
        case TokenType::THROW_KW:
        case TokenType::INCREMENT:
        case TokenType::DECREMENT:
        case TokenType::PLUS:
        case TokenType::NEGATE:
        case TokenType::LOGICAL_NOT:
        case TokenType::BITWISE_NOT:
        case TokenType::DIVIDE:
        case TokenType::MODULO:
        case TokenType::BITWISE_OR:
        case TokenType::BITWISE_XOR:
        case TokenType::LOGICAL_OR:
        case TokenType::LEFT_SHIFT:
        case TokenType::RIGHT_SHIFT:
        case TokenType::LESS_THAN:
        case TokenType::LESS_EQUAL_THAN:
        case TokenType::GREATER_THAN:
        case TokenType::GREATER_EQUAL_THAN:
        case TokenType::THREE_WAY_COMPARE:
        case TokenType::EQUAL_TO:
        case TokenType::NOT_EQUAL:
        case TokenType::QUESTION:
        case TokenType::ASSIGN:
        case TokenType::ASSIGN_MUL:
        case TokenType::ASSIGN_DIV:
        case TokenType::ASSIGN_MOD:
        case TokenType::ASSIGN_ADD:
        case TokenType::ASSIGN_SUB:
        case TokenType::ASSIGN_LSHIFT:
        case TokenType::ASSIGN_RSHIFT:
        case TokenType::ASSIGN_AND:
        case TokenType::ASSIGN_XOR:
        case TokenType::ASSIGN_OR:
        case TokenType::DOT:
        case TokenType::ARROW:
        case TokenType::DOT_STAR:
        case TokenType::ARROW_STAR:
            return true;
        default:
            return false;
    }
}

inline bool can_follow_cxx_parenthesized_declarator(TokenType token_type) {
    switch (token_type) {
        case TokenType::SEMICOLON:
        case TokenType::COMMA:
        case TokenType::ASSIGN:
        case TokenType::LEFT_BRACE:
        case TokenType::LEFT_BRACKET:
        case TokenType::LEFT_PAREN:
        case TokenType::ATTRIBUTE_KW:
        case TokenType::ASM_KW:
            return true;
        default:
            return false;
    }
}

inline TokenType matching_close_token(TokenType open_tok) {
    switch (open_tok) {
        case TokenType::LEFT_PAREN:
            return TokenType::RIGHT_PAREN;
        case TokenType::LEFT_BRACKET:
            return TokenType::RIGHT_BRACKET;
        case TokenType::LEFT_BRACE:
            return TokenType::RIGHT_BRACE;
        default:
            return TokenType::UNKNOWN;
    }
}

class SyntaxProbe {
public:
    SyntaxProbe(TokenMgnt& mgnt, Config cfg) : mgnt_(mgnt), cfg_(cfg) {}

    Result probe_type_name() {
        bool saw_specifier = false;
        bool saw_definite_type_specifier = false;
        SpecScanStatus spec_status = consume_decl_specifier_sequence(
            saw_specifier, saw_definite_type_specifier);
        if (spec_status == SpecScanStatus::Error) {
            return Result::Error;
        }
        if (spec_status == SpecScanStatus::Inconclusive) {
            return Result::Inconclusive;
        }
        if (spec_status == SpecScanStatus::NoMatch || !saw_specifier) {
            return Result::NoMatch;
        }
        if (!saw_definite_type_specifier) {
            return Result::Inconclusive;
        }

        bool saw_identifier = false;
        bool consumed_declarator = false;
        if (is_type_name_declarator_start()) {
            if (!consume_declarator(
                    /*allow_identifier_name=*/false,
                    saw_identifier,
                    consumed_declarator,
                    /*depth=*/0)) {
                return inconclusive_ ? Result::Inconclusive : Result::Error;
            }
        }
        if (saw_identifier) {
            return Result::NoMatch;
        }
        return Result::Match;
    }

    Result probe_declarator() {
        if (!is_declarator_start(/*allow_identifier_name=*/true)) {
            return Result::NoMatch;
        }

        bool saw_identifier = false;
        bool consumed_declarator = false;
        if (!consume_declarator(
                /*allow_identifier_name=*/true,
                saw_identifier,
                consumed_declarator,
                /*depth=*/0)) {
            return inconclusive_ ? Result::Inconclusive : Result::Error;
        }
        if (!consumed_declarator) {
            return Result::NoMatch;
        }
        return Result::Match;
    }

    Result probe_cpp_qualified_declarator() {
        if (!cfg_.cxx_mode) {
            return Result::NoMatch;
        }

        bool saw_specifier = false;
        bool saw_definite_type_specifier = false;
        SpecScanStatus spec_status = consume_decl_specifier_sequence(
            saw_specifier, saw_definite_type_specifier);
        if (spec_status == SpecScanStatus::Error) {
            return Result::Error;
        }
        if (spec_status == SpecScanStatus::Inconclusive) {
            return Result::Inconclusive;
        }
        if (spec_status == SpecScanStatus::NoMatch || !saw_specifier) {
            return Result::NoMatch;
        }
        if (!saw_definite_type_specifier) {
            return Result::Inconclusive;
        }

        bool saw_identifier = false;
        bool consumed_declarator = false;
        if (!consume_declarator(
                /*allow_identifier_name=*/true,
                saw_identifier,
                consumed_declarator,
                /*depth=*/0)) {
            return inconclusive_ ? Result::Inconclusive : Result::Error;
        }
        if (!consumed_declarator) {
            return Result::NoMatch;
        }
        return is_scope_resolution_here() ? Result::Match : Result::NoMatch;
    }

    CxxStatementDisambiguation probe_cxx_statement_disambiguation() {
        if (!cfg_.cxx_mode) {
            return CxxStatementDisambiguation::Invalid;
        }

        bool attr_consumed = consume_attributes();
        if (inconclusive_) {
            return CxxStatementDisambiguation::Invalid;
        }
        if (attr_consumed && current_token().type == TokenType::SEMICOLON) {
            return CxxStatementDisambiguation::Expression;
        }

        auto function_style_result =
            classify_cxx_function_style_cast_statement();
        if (function_style_result) {
            return *function_style_result;
        }

        return CxxStatementDisambiguation::Ambiguous;
    }

private:
    enum class SpecScanStatus : uint8_t {
        Matched,
        NoMatch,
        Inconclusive,
        Error
    };

    TokenMgnt& mgnt_;
    Config cfg_;
    bool inconclusive_ = false;

    const Token& current_token() const {
        return mgnt_.current_token();
    }

    const Token& peek_token(size_t offset = 1) const {
        return mgnt_.peek_token(offset);
    }

    const Token& token_at(size_t offset) const {
        return offset == 0 ? current_token() : peek_token(offset);
    }

    bool consume(TokenType tok) {
        return mgnt_.gentle_check_and_consume(tok);
    }

    void advance() {
        mgnt_.advance();
    }

    bool is_scope_resolution_here() const {
        return current_token().type == TokenType::SCOPE_RESOLUTION ||
               (current_token().type == TokenType::COLON &&
                peek_token().type == TokenType::COLON);
    }

    bool consume_scope_resolution() {
        if (consume(TokenType::SCOPE_RESOLUTION)) {
            return true;
        }
        if (current_token().type == TokenType::COLON &&
            peek_token().type == TokenType::COLON) {
            advance();
            advance();
            return true;
        }
        return false;
    }

    bool consume_scope_resolution_at(size_t& offset) const {
        Token tok = token_at(offset);
        if (tok.type == TokenType::SCOPE_RESOLUTION) {
            ++offset;
            return true;
        }
        if (tok.type == TokenType::COLON &&
            token_at(offset + 1).type == TokenType::COLON) {
            offset += 2;
            return true;
        }
        return false;
    }

    bool skip_balanced_tokens_at(size_t& offset,
                                 TokenType open_tok,
                                 TokenType close_tok) const {
        if (token_at(offset).type != open_tok) {
            return false;
        }
        int depth = 0;
        while (token_at(offset).type != TokenType::Eof) {
            TokenType tok_type = token_at(offset).type;
            if (tok_type == open_tok) {
                ++depth;
            } else if (tok_type == close_tok) {
                --depth;
                ++offset;
                return depth == 0;
            }
            ++offset;
        }
        return false;
    }

    bool skip_template_argument_list_at(size_t& offset) const {
        if (token_at(offset).type != TokenType::LESS_THAN) {
            return true;
        }
        int depth = 0;
        while (token_at(offset).type != TokenType::Eof) {
            TokenType tok_type = token_at(offset).type;
            if (tok_type == TokenType::LEFT_PAREN) {
                if (!skip_balanced_tokens_at(
                        offset,
                        TokenType::LEFT_PAREN,
                        TokenType::RIGHT_PAREN)) {
                    return false;
                }
                continue;
            }
            if (tok_type == TokenType::LEFT_BRACKET) {
                if (!skip_balanced_tokens_at(
                        offset,
                        TokenType::LEFT_BRACKET,
                        TokenType::RIGHT_BRACKET)) {
                    return false;
                }
                continue;
            }
            if (tok_type == TokenType::LEFT_BRACE) {
                if (!skip_balanced_tokens_at(
                        offset,
                        TokenType::LEFT_BRACE,
                        TokenType::RIGHT_BRACE)) {
                    return false;
                }
                continue;
            }
            if (tok_type == TokenType::LESS_THAN) {
                ++depth;
                ++offset;
                continue;
            }
            if (tok_type == TokenType::GREATER_THAN) {
                --depth;
                ++offset;
                return depth == 0;
            }
            if (tok_type == TokenType::RIGHT_SHIFT) {
                depth -= 2;
                ++offset;
                return depth <= 0;
            }
            ++offset;
        }
        return false;
    }

    bool consume_qualified_type_name_at(size_t& offset) const {
        consume_scope_resolution_at(offset);
        if (token_at(offset).type != TokenType::IDENTIFIER) {
            return false;
        }
        ++offset;
        if (!skip_template_argument_list_at(offset)) {
            return false;
        }
        while (consume_scope_resolution_at(offset)) {
            if (token_at(offset).type == TokenType::TEMPLATE) {
                ++offset;
            }
            if (token_at(offset).type != TokenType::IDENTIFIER) {
                return false;
            }
            ++offset;
            if (!skip_template_argument_list_at(offset)) {
                return false;
            }
        }
        return true;
    }

    bool consume_decltype_or_typeof_at(size_t& offset) const {
        TokenType tok_type = token_at(offset).type;
        if (tok_type != TokenType::DECLTYPE_KW &&
            tok_type != TokenType::TYPEOF_KW) {
            return false;
        }
        ++offset;
        return skip_balanced_tokens_at(
            offset,
            TokenType::LEFT_PAREN,
            TokenType::RIGHT_PAREN);
    }

    std::optional<size_t> find_cxx_function_style_cast_lparen() const {
        if (!can_start_cxx_function_style_cast_statement(
                current_token().type)) {
            return std::nullopt;
        }
        size_t offset = 0;
        while (is_cxx_function_style_type_qualifier(token_at(offset).type)) {
            ++offset;
        }
        if (token_at(offset).type == TokenType::TYPENAME) {
            ++offset;
            if (!consume_qualified_type_name_at(offset)) {
                return std::nullopt;
            }
        } else if (token_at(offset).type == TokenType::DECLTYPE_KW ||
                   token_at(offset).type == TokenType::TYPEOF_KW) {
            if (!consume_decltype_or_typeof_at(offset)) {
                return std::nullopt;
            }
        } else if (is_cxx_function_style_builtin_type_token(
                       token_at(offset).type)) {
            do {
                ++offset;
            } while (is_cxx_function_style_builtin_type_token(
                         token_at(offset).type) ||
                     is_cxx_function_style_type_qualifier(
                         token_at(offset).type));
        } else if (!consume_qualified_type_name_at(offset)) {
            return std::nullopt;
        }
        while (is_cxx_function_style_type_qualifier(token_at(offset).type)) {
            ++offset;
        }
        if (token_at(offset).type != TokenType::LEFT_PAREN) {
            return std::nullopt;
        }
        return offset;
    }

    std::optional<size_t> find_matching_paren_at(size_t open_offset) const {
        size_t offset = open_offset;
        if (token_at(offset).type != TokenType::LEFT_PAREN) {
            return std::nullopt;
        }
        int depth = 0;
        while (token_at(offset).type != TokenType::Eof) {
            TokenType tok_type = token_at(offset).type;
            if (tok_type == TokenType::LEFT_PAREN) {
                ++depth;
            } else if (tok_type == TokenType::RIGHT_PAREN) {
                --depth;
                if (depth == 0) {
                    return offset;
                }
            }
            ++offset;
        }
        return std::nullopt;
    }

    bool cxx_cast_parentheses_force_expression(size_t open_offset,
                                               size_t close_offset) const {
        if (close_offset == open_offset + 1) {
            return true;
        }
        TokenType first_type = token_at(open_offset + 1).type;
        if (!can_start_cxx_parenthesized_declarator(first_type)) {
            return true;
        }

        int paren_depth = 0;
        int bracket_depth = 0;
        int brace_depth = 0;
        for (size_t offset = open_offset + 1;
             offset < close_offset;
             ++offset) {
            TokenType tok_type = token_at(offset).type;
            if (tok_type == TokenType::LEFT_PAREN) {
                ++paren_depth;
                continue;
            }
            if (tok_type == TokenType::RIGHT_PAREN) {
                if (paren_depth > 0) {
                    --paren_depth;
                }
                continue;
            }
            if (tok_type == TokenType::LEFT_BRACKET) {
                ++bracket_depth;
                continue;
            }
            if (tok_type == TokenType::RIGHT_BRACKET) {
                if (bracket_depth > 0) {
                    --bracket_depth;
                }
                continue;
            }
            if (tok_type == TokenType::LEFT_BRACE) {
                ++brace_depth;
                continue;
            }
            if (tok_type == TokenType::RIGHT_BRACE) {
                if (brace_depth > 0) {
                    --brace_depth;
                }
                continue;
            }
            if (paren_depth != 0 || bracket_depth != 0 || brace_depth != 0) {
                continue;
            }
            if ((tok_type == TokenType::MULTIPLY ||
                 tok_type == TokenType::BITWISE_AND ||
                 tok_type == TokenType::LOGICAL_AND) &&
                offset != open_offset + 1 &&
                token_at(offset - 1).type != TokenType::SCOPE_RESOLUTION) {
                return true;
            }
            if (tok_type == TokenType::COMMA ||
                is_cxx_expression_only_in_parenthesized_declarator(tok_type)) {
                return true;
            }
        }
        return false;
    }

    std::optional<CxxStatementDisambiguation>
    classify_cxx_function_style_cast_statement() const {
        auto lparen_offset = find_cxx_function_style_cast_lparen();
        if (!lparen_offset) {
            return std::nullopt;
        }
        auto close_offset = find_matching_paren_at(*lparen_offset);
        if (!close_offset) {
            return CxxStatementDisambiguation::Invalid;
        }
        if (cxx_cast_parentheses_force_expression(
                *lparen_offset, *close_offset)) {
            return CxxStatementDisambiguation::Expression;
        }
        if (!can_follow_cxx_parenthesized_declarator(
                token_at(*close_offset + 1).type)) {
            return CxxStatementDisambiguation::Expression;
        }
        return CxxStatementDisambiguation::Ambiguous;
    }

    bool skip_balanced_group() {
        TokenType opening = current_token().type;
        TokenType first_close = matching_close_token(opening);
        if (first_close == TokenType::UNKNOWN) {
            return false;
        }
        advance();

        size_t stack_size = 1;
        TokenType close_stack[128];
        close_stack[0] = first_close;
        while (stack_size > 0) {
            TokenType tok = current_token().type;
            if (tok == TokenType::Eof) {
                return false;
            }

            TokenType nested_close = matching_close_token(tok);
            if (nested_close != TokenType::UNKNOWN) {
                if (stack_size >= 128) {
                    inconclusive_ = true;
                    return false;
                }
                close_stack[stack_size++] = nested_close;
                advance();
                continue;
            }

            if (tok == close_stack[stack_size - 1]) {
                --stack_size;
                advance();
                continue;
            }

            advance();
        }

        return true;
    }

    bool skip_cxx_attribute_specifier() {
        if (current_token().type != TokenType::LEFT_BRACKET ||
            peek_token().type != TokenType::LEFT_BRACKET) {
            return false;
        }

        advance();
        advance();
        size_t depth = 1;
        while (depth > 0) {
            TokenType tok = current_token().type;
            if (tok == TokenType::Eof) {
                return false;
            }

            if (tok == TokenType::LEFT_BRACKET &&
                peek_token().type == TokenType::LEFT_BRACKET) {
                ++depth;
                advance();
                advance();
                continue;
            }

            if (tok == TokenType::RIGHT_BRACKET &&
                peek_token().type == TokenType::RIGHT_BRACKET) {
                --depth;
                advance();
                advance();
                continue;
            }

            if (tok == TokenType::LEFT_PAREN ||
                tok == TokenType::LEFT_BRACKET ||
                tok == TokenType::LEFT_BRACE) {
                if (!skip_balanced_group()) {
                    return false;
                }
                continue;
            }

            advance();
        }
        return true;
    }

    bool consume_attributes() {
        bool consumed_any = false;
        while (true) {
            if (is_gnu_attribute_token_syntax(current_token())) {
                consumed_any = true;
                advance();
                if (!consume(TokenType::LEFT_PAREN)) {
                    inconclusive_ = true;
                    return false;
                }
                if (!skip_balanced_group()) {
                    return false;
                }
                continue;
            }
            if (skip_cxx_attribute_specifier()) {
                consumed_any = true;
                continue;
            }
            break;
        }
        return consumed_any;
    }

    bool is_declarator_start(bool allow_identifier_name) const {
        TokenType tok = current_token().type;
        if (tok == TokenType::MULTIPLY ||
            tok == TokenType::BITWISE_XOR ||
            tok == TokenType::BITWISE_AND ||
            tok == TokenType::LOGICAL_AND ||
            tok == TokenType::LEFT_PAREN ||
            tok == TokenType::LEFT_BRACKET) {
            return true;
        }
        return allow_identifier_name && tok == TokenType::IDENTIFIER;
    }

    bool is_type_name_declarator_start() const {
        TokenType tok = current_token().type;
        return tok == TokenType::MULTIPLY ||
               tok == TokenType::BITWISE_XOR ||
               tok == TokenType::BITWISE_AND ||
               tok == TokenType::LOGICAL_AND ||
               tok == TokenType::LEFT_PAREN ||
               tok == TokenType::LEFT_BRACKET;
    }

    bool consume_pointer_operator_tail_qualifiers() {
        while (true) {
            if (consume(TokenType::CONST) ||
                consume(TokenType::VOLATILE) ||
                consume(TokenType::RESTRICT) ||
                consume(TokenType::ATOMIC) ||
                consume(TokenType::NULLABILITY_QUALIFIER)) {
                continue;
            }
            bool attr_consumed = consume_attributes();
            if (inconclusive_) {
                return false;
            }
            if (attr_consumed) {
                continue;
            }
            break;
        }
        return true;
    }

    bool try_consume_member_pointer_operator() {
        if (!cfg_.cxx_mode) {
            return false;
        }

        size_t saved = mgnt_.get_token_idx();
        bool saw_scope = false;
        if (consume_scope_resolution()) {
            saw_scope = true;
        }

        if (current_token().type != TokenType::IDENTIFIER) {
            mgnt_.set_token_idx(saved);
            return false;
        }
        advance();

        while (consume_scope_resolution()) {
            saw_scope = true;
            if (current_token().type != TokenType::IDENTIFIER) {
                mgnt_.set_token_idx(saved);
                inconclusive_ = true;
                return false;
            }
            advance();
        }

        if (!saw_scope || !consume(TokenType::MULTIPLY)) {
            mgnt_.set_token_idx(saved);
            return false;
        }
        return true;
    }

    bool consume_pointer_operators(bool& consumed_any) {
        consumed_any = false;
        while (true) {
            bool attr_consumed = consume_attributes();
            if (inconclusive_) {
                return false;
            }
            if (attr_consumed) {
                continue;
            }

            size_t saved = mgnt_.get_token_idx();
            if (try_consume_member_pointer_operator()) {
                consumed_any = true;
                if (!consume_pointer_operator_tail_qualifiers()) {
                    return false;
                }
                continue;
            }
            mgnt_.set_token_idx(saved);

            if (consume(TokenType::MULTIPLY) ||
                consume(TokenType::BITWISE_XOR) ||
                consume(TokenType::BITWISE_AND) ||
                consume(TokenType::LOGICAL_AND)) {
                consumed_any = true;
                if (!consume_pointer_operator_tail_qualifiers()) {
                    return false;
                }
                continue;
            }
            break;
        }
        return true;
    }

    void consume_function_suffix_qualifiers() {
        while (true) {
            if (consume(TokenType::CONST) ||
                consume(TokenType::VOLATILE)) {
                continue;
            }
            if (cfg_.cxx_mode &&
                (consume(TokenType::BITWISE_AND) ||
                 consume(TokenType::LOGICAL_AND))) {
                continue;
            }
            if (cfg_.cxx_mode && consume(TokenType::NOEXCEPT_KW)) {
                if (current_token().type == TokenType::LEFT_PAREN &&
                    !skip_balanced_group()) {
                    inconclusive_ = true;
                }
                continue;
            }

            bool attr_consumed = consume_attributes();
            if (attr_consumed) {
                continue;
            }
            break;
        }
    }

    bool consume_direct_declarator(bool allow_identifier_name,
                                   bool& saw_identifier,
                                   bool& consumed_any,
                                   size_t depth) {
        consumed_any = false;

        if (current_token().type == TokenType::LEFT_PAREN) {
            size_t lparen_idx = mgnt_.get_token_idx();
            advance();
            bool inner_saw_identifier = false;
            bool inner_consumed = false;
            if (!consume_declarator(
                    /*allow_identifier_name=*/true,
                    inner_saw_identifier,
                    inner_consumed,
                    depth + 1) ||
                !consume(TokenType::RIGHT_PAREN)) {
                mgnt_.set_token_idx(lparen_idx);
                inconclusive_ = true;
                return false;
            }
            if (!inner_consumed) {
                mgnt_.set_token_idx(lparen_idx);
                inconclusive_ = true;
                return false;
            }
            consumed_any = true;
            saw_identifier = saw_identifier || inner_saw_identifier;
        } else if (allow_identifier_name &&
                   current_token().type == TokenType::IDENTIFIER) {
            saw_identifier = true;
            consumed_any = true;
            advance();
        }

        while (current_token().type == TokenType::LEFT_BRACKET ||
               current_token().type == TokenType::LEFT_PAREN) {
            TokenType suffix_open = current_token().type;
            if (!skip_balanced_group()) {
                inconclusive_ = true;
                return false;
            }
            consumed_any = true;
            if (suffix_open == TokenType::LEFT_PAREN) {
                consume_function_suffix_qualifiers();
                if (inconclusive_) {
                    return false;
                }
            }
        }

        return true;
    }

    bool consume_declarator(bool allow_identifier_name,
                            bool& saw_identifier,
                            bool& consumed_any,
                            size_t depth) {
        if (depth > 64) {
            inconclusive_ = true;
            return false;
        }
        bool prefix_consumed = false;
        if (!consume_pointer_operators(prefix_consumed)) {
            return false;
        }

        bool direct_consumed = false;
        if (!consume_direct_declarator(
                allow_identifier_name, saw_identifier, direct_consumed, depth)) {
            return false;
        }

        consumed_any = prefix_consumed || direct_consumed;
        return true;
    }

    bool consume_record_or_enum_specifier_suffix(bool is_enum) {
        bool attr_consumed = consume_attributes();
        if (inconclusive_) {
            return false;
        }
        if (attr_consumed) {
            // Keep scanning name/body after attributes.
        }

        if (is_enum && cfg_.cxx_mode &&
            (current_token().type == TokenType::CLASS ||
             current_token().type == TokenType::STRUCT)) {
            advance();
        }

        if (cfg_.cxx_mode && consume_scope_resolution()) {
            if (current_token().type != TokenType::IDENTIFIER) {
                inconclusive_ = true;
                return false;
            }
        }

        if (current_token().type == TokenType::IDENTIFIER) {
            advance();
            while (cfg_.cxx_mode && consume_scope_resolution()) {
                if (current_token().type != TokenType::IDENTIFIER) {
                    inconclusive_ = true;
                    return false;
                }
                advance();
            }
        }

        if (cfg_.cxx_mode &&
            current_token().type == TokenType::IDENTIFIER &&
            current_token().value == "final") {
            advance();
        }

        if (current_token().type == TokenType::COLON &&
            peek_token().type != TokenType::COLON) {
            advance();
            while (true) {
                TokenType tok = current_token().type;
                if (tok == TokenType::Eof) {
                    return false;
                }
                if (tok == TokenType::LEFT_BRACE ||
                    tok == TokenType::SEMICOLON ||
                    tok == TokenType::COMMA ||
                    tok == TokenType::ASSIGN ||
                    tok == TokenType::RIGHT_PAREN ||
                    tok == TokenType::RIGHT_BRACKET) {
                    break;
                }
                if (tok == TokenType::LEFT_PAREN ||
                    tok == TokenType::LEFT_BRACKET ||
                    tok == TokenType::LEFT_BRACE) {
                    if (!skip_balanced_group()) {
                        return false;
                    }
                    continue;
                }
                advance();
            }
        }

        if (current_token().type == TokenType::LEFT_BRACE) {
            return skip_balanced_group();
        }
        return true;
    }

    SpecScanStatus consume_decl_specifier_sequence(bool& saw_specifier,
                                                   bool& saw_definite_type_specifier) {
        saw_specifier = false;
        saw_definite_type_specifier = false;

        while (true) {
            bool attr_consumed = consume_attributes();
            if (inconclusive_) {
                return SpecScanStatus::Inconclusive;
            }
            if (attr_consumed) {
                saw_specifier = true;
                continue;
            }

            TokenType tok = current_token().type;
            switch (tok) {
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
                case TokenType::CHAR16_T:
                case TokenType::CHAR32_T:
                case TokenType::INT128:
                case TokenType::UINT128_T:
                case TokenType::AUTO_TYPE:
                case TokenType::COMPLEX:
                case TokenType::FLOAT16:
                    saw_specifier = true;
                    saw_definite_type_specifier = true;
                    advance();
                    continue;

                case TokenType::STATIC:
                case TokenType::EXTERN:
                case TokenType::REGISTER:
                case TokenType::TYPEDEF:
                case TokenType::THREAD_LOCAL:
                case TokenType::INLINE:
                case TokenType::NORETURN_KW:
                case TokenType::EXTENSION_KW:
                case TokenType::CONSTEXPR_KW:
                case TokenType::CONSTEVAL_KW:
                case TokenType::MUTABLE_KW:
                    if (tok == TokenType::MUTABLE_KW && !cfg_.cxx_mode) {
                        return saw_specifier
                            ? SpecScanStatus::Matched
                            : SpecScanStatus::NoMatch;
                    }
                    saw_specifier = true;
                    advance();
                    continue;

                case TokenType::IDENTIFIER:
                    if (cfg_.blocks_enabled &&
                        current_token().value == "__block") {
                        saw_specifier = true;
                        advance();
                        continue;
                    }
                    break;

                case TokenType::AUTO:
                    saw_specifier = true;
                    if (cfg_.cxx_mode) {
                        saw_definite_type_specifier = true;
                    }
                    advance();
                    continue;

                case TokenType::CONST:
                case TokenType::VOLATILE:
                case TokenType::RESTRICT:
                case TokenType::NULLABILITY_QUALIFIER:
                    saw_specifier = true;
                    advance();
                    continue;

                case TokenType::ATOMIC:
                    saw_specifier = true;
                    advance();
                    if (current_token().type == TokenType::LEFT_PAREN) {
                        saw_definite_type_specifier = true;
                        if (!skip_balanced_group()) {
                            return SpecScanStatus::Error;
                        }
                    }
                    continue;

                case TokenType::ALIGNAS:
                case TokenType::TYPEOF_KW:
                    saw_specifier = true;
                    saw_definite_type_specifier = true;
                    advance();
                    if (current_token().type != TokenType::LEFT_PAREN ||
                        !skip_balanced_group()) {
                        return SpecScanStatus::Error;
                    }
                    continue;

                case TokenType::STRUCT:
                case TokenType::UNION:
                    saw_specifier = true;
                    saw_definite_type_specifier = true;
                    advance();
                    if (!consume_record_or_enum_specifier_suffix(/*is_enum=*/false)) {
                        return inconclusive_
                            ? SpecScanStatus::Inconclusive
                            : SpecScanStatus::Error;
                    }
                    continue;

                case TokenType::CLASS:
                    if (!cfg_.cxx_mode) {
                        return saw_specifier
                            ? SpecScanStatus::Matched
                            : SpecScanStatus::NoMatch;
                    }
                    saw_specifier = true;
                    saw_definite_type_specifier = true;
                    advance();
                    if (!consume_record_or_enum_specifier_suffix(/*is_enum=*/false)) {
                        return inconclusive_
                            ? SpecScanStatus::Inconclusive
                            : SpecScanStatus::Error;
                    }
                    continue;

                case TokenType::TYPENAME:
                    if (!cfg_.cxx_mode) {
                        return saw_specifier
                            ? SpecScanStatus::Matched
                            : SpecScanStatus::NoMatch;
                    }
                    saw_specifier = true;
                    saw_definite_type_specifier = true;
                    advance();
                    continue;

                case TokenType::ENUM:
                    saw_specifier = true;
                    saw_definite_type_specifier = true;
                    advance();
                    if (!consume_record_or_enum_specifier_suffix(/*is_enum=*/true)) {
                        return inconclusive_
                            ? SpecScanStatus::Inconclusive
                            : SpecScanStatus::Error;
                    }
                    continue;

                default:
                    if (tok == TokenType::IDENTIFIER &&
                        current_token().value == "constexpr") {
                        saw_specifier = true;
                        advance();
                        continue;
                    }
                    if (!saw_definite_type_specifier &&
                        (tok == TokenType::IDENTIFIER ||
                         (cfg_.cxx_mode && is_scope_resolution_here()))) {
                        return SpecScanStatus::Inconclusive;
                    }
                    return saw_specifier
                        ? SpecScanStatus::Matched
                        : SpecScanStatus::NoMatch;
            }
        }
    }
};

} // namespace detail

inline Result probe_type_name(TokenMgnt& mgnt, const Config& cfg) {
    detail::SyntaxProbe probe(mgnt, cfg);
    return probe.probe_type_name();
}

inline Result probe_declarator(TokenMgnt& mgnt, const Config& cfg) {
    detail::SyntaxProbe probe(mgnt, cfg);
    return probe.probe_declarator();
}

inline Result probe_cpp_qualified_declarator(TokenMgnt& mgnt, const Config& cfg) {
    detail::SyntaxProbe probe(mgnt, cfg);
    return probe.probe_cpp_qualified_declarator();
}

inline CxxStatementDisambiguation
probe_cxx_statement_disambiguation(TokenMgnt& mgnt, const Config& cfg) {
    detail::SyntaxProbe probe(mgnt, cfg);
    return probe.probe_cxx_statement_disambiguation();
}

inline bool can_start_cxx_function_style_cast_statement(TokenType token_type) {
    return detail::can_start_cxx_function_style_cast_statement(token_type);
}

} // namespace tentative_syntax_probe

#endif // ABURI_TENTATIVE_SYNTAX_PROBE_H
