#ifndef ABURI_TENTATIVE_SYNTAX_PROBE_H
#define ABURI_TENTATIVE_SYNTAX_PROBE_H

#include "../lexer.h"

#include <cstddef>

namespace tentative_syntax_probe {

enum class Result : uint8_t {
    Match,
    NoMatch,
    Inconclusive,
    Error
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

} // namespace tentative_syntax_probe

#endif // ABURI_TENTATIVE_SYNTAX_PROBE_H
