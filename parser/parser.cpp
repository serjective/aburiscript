#include "parser.h"
#include "../helpers/casting.h"
#include "../ast/special_members.h"
#include "../collect/lookup_engine.h"
#include <set>
#include "../numeric_utils.h"
#include "../abi/target_info.h"
#include <cassert>
#include <cstdint>
#include <functional>
#include <limits>
#include <vector>

std::vector<uint32_t> decode_utf8_codepoints(const std::string& text) {
    std::vector<uint32_t> out;
    size_t i = 0;
    while (i < text.size()) {
        unsigned char c0 = static_cast<unsigned char>(text[i]);
        if ((c0 & 0x80) == 0) {
            out.push_back(c0);
            ++i;
            continue;
        }

        auto is_cont = [](unsigned char c) { return (c & 0xC0) == 0x80; };

        if ((c0 & 0xE0) == 0xC0 && i + 1 < text.size()) {
            unsigned char c1 = static_cast<unsigned char>(text[i + 1]);
            if (c0 >= 0xC2 && is_cont(c1)) {
                uint32_t cp = ((c0 & 0x1F) << 6) | (c1 & 0x3F);
                out.push_back(cp);
                i += 2;
                continue;
            }
        } else if ((c0 & 0xF0) == 0xE0 && i + 2 < text.size()) {
            unsigned char c1 = static_cast<unsigned char>(text[i + 1]);
            unsigned char c2 = static_cast<unsigned char>(text[i + 2]);
            if (is_cont(c1) && is_cont(c2)) {
                uint32_t cp = ((c0 & 0x0F) << 12) | ((c1 & 0x3F) << 6) | (c2 & 0x3F);
                bool overlong = cp < 0x800;
                bool surrogate = (cp >= 0xD800 && cp <= 0xDFFF);
                if (!overlong && !surrogate) {
                    out.push_back(cp);
                    i += 3;
                    continue;
                }
            }
        } else if ((c0 & 0xF8) == 0xF0 && i + 3 < text.size()) {
            unsigned char c1 = static_cast<unsigned char>(text[i + 1]);
            unsigned char c2 = static_cast<unsigned char>(text[i + 2]);
            unsigned char c3 = static_cast<unsigned char>(text[i + 3]);
            if (is_cont(c1) && is_cont(c2) && is_cont(c3)) {
                uint32_t cp = ((c0 & 0x07) << 18) | ((c1 & 0x3F) << 12) |
                              ((c2 & 0x3F) << 6) | (c3 & 0x3F);
                bool overlong = cp < 0x10000;
                if (!overlong && cp <= 0x10FFFF) {
                    out.push_back(cp);
                    i += 4;
                    continue;
                }
            }
        }

        // Keep invalid bytes as-is to preserve implementation-defined behavior.
        out.push_back(c0);
        ++i;
    }
    return out;
}

bool is_c23_family_standard(const std::string& std_name) {
    return std_name == "c23" || std_name == "gnu23" ||
           std_name == "c2x" || std_name == "gnu2x";
}

bool token_can_start_cast_operand(TokenType tok) {
    switch (tok) {
        case TokenType::RIGHT_PAREN:
        case TokenType::COMMA:
        case TokenType::SEMICOLON:
        case TokenType::RIGHT_BRACKET:
        case TokenType::COLON:
        case TokenType::QUESTION:
            return false;
        default:
            return true;
    }
}



PrecLevel get_prec(TokenType tok) {
    switch (tok) {
        case TokenType::COMMA:
            return PrecLevel::COMMA;
        case TokenType::MULTIPLY:
        case TokenType::MODULO:
        case TokenType::DIVIDE:
            return PrecLevel::MULTDIV;
        case TokenType::DOT_STAR:
        case TokenType::ARROW_STAR:
            return PrecLevel::PM;
        case TokenType::PLUS:
        case TokenType::NEGATE:
            return PrecLevel::ADDSUB;
        case TokenType::GREATER_THAN:
        case TokenType::GREATER_EQUAL_THAN:
        case TokenType::LESS_THAN:
        case TokenType::LESS_EQUAL_THAN:
            return PrecLevel::RELATIONAL;
        case TokenType::EQUAL_TO:
        case TokenType::NOT_EQUAL:
            return PrecLevel::EQUALITY;
        case TokenType::LOGICAL_OR:
            return PrecLevel::LOGICAL_OR;
        case TokenType::LOGICAL_AND:
            return PrecLevel::LOGICAL_AND;
        case TokenType::BITWISE_OR:
            return PrecLevel::INCLUSIVE_OR;
        case TokenType::BITWISE_AND:
            return PrecLevel::AND;
        case TokenType::BITWISE_XOR:
            return PrecLevel::EXCLUSIVE_OR;
        case TokenType::LEFT_SHIFT:
        case TokenType::RIGHT_SHIFT:
            return PrecLevel::SHIFT;
        case TokenType::QUESTION:
            return PrecLevel::CONDITIONAL;
        case TokenType::ASSIGN:
        case TokenType::ASSIGN_ADD:
        case TokenType::ASSIGN_SUB:
        case TokenType::ASSIGN_DIV:
        case TokenType::ASSIGN_LSHIFT:
        case TokenType::ASSIGN_AND:
        case TokenType::ASSIGN_MOD:
        case TokenType::ASSIGN_MUL:
        case TokenType::ASSIGN_XOR:
        case TokenType::ASSIGN_RSHIFT:
        case TokenType::ASSIGN_OR:
            return PrecLevel::ASSIGNMENT;
        default:
            return PrecLevel::UNKNOWN;

    }
}
bool is_integer_literal(TokenType tok) {
    switch (tok) {
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
bool is_imaginary_integer_literal(TokenType tok) {
    switch (tok) {
        case TokenType::IMAG_INTEGER_CONST:
        case TokenType::IMAG_UNSIGNED_INTEGER_CONST:
        case TokenType::IMAG_LONG_CONST:
        case TokenType::IMAG_UNSIGNED_LONG_CONST:
        case TokenType::IMAG_LONG_LONG_CONST:
        case TokenType::IMAG_UNSIGNED_LONG_LONG_CONST:
            return true;
        default:
            return false;
    }
}
TokenType imaginary_integer_to_real_token(TokenType tok) {
    switch (tok) {
        case TokenType::IMAG_INTEGER_CONST:
            return TokenType::INTEGER_CONST;
        case TokenType::IMAG_UNSIGNED_INTEGER_CONST:
            return TokenType::UNSIGNED_INTEGER_CONST;
        case TokenType::IMAG_LONG_CONST:
            return TokenType::LONG_CONST;
        case TokenType::IMAG_UNSIGNED_LONG_CONST:
            return TokenType::UNSIGNED_LONG_CONST;
        case TokenType::IMAG_LONG_LONG_CONST:
            return TokenType::LONG_LONG_CONST;
        case TokenType::IMAG_UNSIGNED_LONG_LONG_CONST:
            return TokenType::UNSIGNED_LONG_LONG_CONST;
        default:
            return tok;
    }
}
bool is_floating_literal(TokenType tok) {
    switch (tok) {
        case TokenType::FLOAT_CONST:
        case TokenType::DOUBLE_CONST:
        case TokenType::LONG_DOUBLE_CONST:
        case TokenType::IMAG_FLOAT_CONST:
        case TokenType::IMAG_DOUBLE_CONST:
        case TokenType::IMAG_LONG_DOUBLE_CONST:
            return true;
        default:
            return false;
    }
}
bool is_unary_operator_token(TokenType tok) {
    switch (tok) {
        case TokenType::BITWISE_AND:  // &
        case TokenType::MULTIPLY:     // *
        case TokenType::PLUS:         // +
        case TokenType::NEGATE:       // -
        case TokenType::BITWISE_NOT:  // ~
        case TokenType::LOGICAL_NOT:  // !
        case TokenType::INCREMENT:    // ++
        case TokenType::DECREMENT:    // --
            return true;
        default:
            return false;
    }
}
bool is_assignment_token(TokenType tok) {
    // for assignments
    switch (tok) {
        case TokenType::ASSIGN:
        case TokenType::ASSIGN_ADD:
        case TokenType::ASSIGN_SUB:
        case TokenType::ASSIGN_DIV:
        case TokenType::ASSIGN_LSHIFT:
        case TokenType::ASSIGN_AND:
        case TokenType::ASSIGN_MOD:
        case TokenType::ASSIGN_MUL:
        case TokenType::ASSIGN_XOR:
        case TokenType::ASSIGN_RSHIFT:
        case TokenType::ASSIGN_OR:
            return true;
        default:
            return false;
    }
}
Token Parser::current_token() {
    return tok_mgnt.current_token();
}
size_t Parser::get_token_idx() {
    return tok_mgnt.get_token_idx();
}
void Parser::set_token_idx(size_t idx) {
    tok_mgnt.set_token_idx(idx);
}
Token Parser::peek_token(size_t offset) {
    return tok_mgnt.peek_token(offset);
}
void Parser::advance() {
    tok_mgnt.advance();
}
// gentle_check_and_consume advances the token if true
bool Parser::gentle_check_and_consume(TokenType type) {
    return tok_mgnt.gentle_check_and_consume(type);
}
void Parser::check_and_consume(TokenType type) {
    check(type);
    advance();
}
// we merely gentle_check to see if token matches
bool Parser::gentle_check(TokenType type) {
    return tok_mgnt.gentle_check(type);
}
// if token isn't what we want it to be then error (via diag_engine + ParseError)
void Parser::check(TokenType type) {
    if (!gentle_check(type)) {
        Token got = current_token();
        std::string err = "expected " + token_type_to_string(type) + " but got "
            + (got.type == TokenType::Eof ? "end of file"
               : "'" + got.value + "'");
        error(err);
    }
}
void Parser::check_custom(TokenType type, std::string& message) {
    if (!gentle_check(type)) {
        error(message);
    }
}
// small todo: combine error and error_custloc
void Parser::error(std::string err) {
    SrcLoc loc;
    Token curr_tok = current_token();
    if (curr_tok.type != TokenType::Eof) {
        loc = curr_tok.loc;
    } else if (!tok_mgnt.tokens.empty() && tok_mgnt.current > 0) {
        size_t idx = std::min(tok_mgnt.current, tok_mgnt.tokens.size()) - 1;
        loc = tok_mgnt.tokens[idx].loc;
    }
    diag_engine->report_error(err, loc);
    throw ParseError(err, loc);
}
void Parser::error_custloc(std::string err, SrcLoc loc) {
    diag_engine->report_error(err, loc);
    throw ParseError(err, loc);
}

void Parser::skip_to_stmt_sync_point() {
    if (is_in_tentative_context()) {
        return;
    }
    int brace_depth = 0;
    while (!gentle_check(TokenType::Eof)) {
        TokenType tt = current_token().type;

        if (tt == TokenType::LEFT_BRACE) {
            brace_depth++;
            advance();
            continue;
        }
        if (tt == TokenType::RIGHT_BRACE) {
            if (brace_depth > 0) {
                brace_depth--;
                advance();
                continue;
            }
            // At depth 0, stop before the '}' — let the caller handle it
            return;
        }
        if (brace_depth == 0) {
            if (tt == TokenType::SEMICOLON) {
                advance(); // consume the ';'
                return;
            }
            // Statement-starting keywords
            if (tt == TokenType::IF || tt == TokenType::WHILE || tt == TokenType::FOR ||
                tt == TokenType::DO || tt == TokenType::SWITCH || tt == TokenType::RETURN ||
                tt == TokenType::BREAK || tt == TokenType::CONTINUE || tt == TokenType::GOTO ||
                tt == TokenType::CASE || tt == TokenType::DEFAULT) {
                return;
            }
            // Declaration-starting tokens
            if (isTokenDeclarationSpec(current_token())) {
                return;
            }
        }
        advance();
    }
}

void Parser::skip_to_next_top_level_decl() {
    if (is_in_tentative_context()) {
        return;
    }
    int brace_depth = 0;
    while (!gentle_check(TokenType::Eof)) {
        TokenType tt = current_token().type;

        if (tt == TokenType::LEFT_BRACE) {
            brace_depth++;
            advance();
            continue;
        }
        if (tt == TokenType::RIGHT_BRACE) {
            if (brace_depth > 0) {
                brace_depth--;
                advance();
                if (brace_depth == 0) {
                    gentle_check_and_consume(TokenType::SEMICOLON);
                    return;
                }
                continue;
            }
            // Unexpected '}' at depth 0 — skip it
            advance();
            continue;
        }
        if (brace_depth == 0) {
            if (tt == TokenType::SEMICOLON) {
                advance();
                return;
            }
            if (isTokenDeclarationSpec(current_token())) {
                if (is_cxx_mode_active() && is_cpp_qualified_id_start()) {
                    while (gentle_check(TokenType::IDENTIFIER) ||
                           gentle_check(TokenType::SCOPE_RESOLUTION) ||
                           (gentle_check(TokenType::COLON) &&
                            peek_token().type == TokenType::COLON)) {
                        if (gentle_check(TokenType::COLON) &&
                            peek_token().type == TokenType::COLON) {
                            advance();
                            advance();
                            continue;
                        }
                        advance();
                    }
                    continue;
                }
                return;
            }
        }
        advance();
    }
}

void Parser::reset_top_level_state() {
    loop_count = 0;
    switch_count = 0;
    has_default = false;
    case_values.clear();
    func_type = nullptr;
    if (func_type == nullptr) {
        seen_stmt_labels.clear();
        stmt_labels.clear();
        local_label_scopes_.clear();
        local_label_unique_id_ = 0;
    }
}
void Parser::skip_to_field_sync_point() {
    if (is_in_tentative_context()) {
        return;
    }
    int brace_depth = 0;
    while (!gentle_check(TokenType::Eof)) {
        TokenType tt = current_token().type;
        if (tt == TokenType::LEFT_BRACE) {
            brace_depth++;
            advance();
            continue;
        }
        if (tt == TokenType::RIGHT_BRACE) {
            if (brace_depth > 0) {
                brace_depth--;
                advance();
                continue;
            }
            return; // stop before '}' at depth 0
        }
        if (brace_depth == 0) {
            if (tt == TokenType::SEMICOLON) {
                advance(); // consume ';'
                return;
            }
            if (isTokenDeclarationSpec(current_token())) {
                return;
            }
            if ((tt == TokenType::PUBLIC_KW ||
                 tt == TokenType::PRIVATE_KW ||
                 tt == TokenType::PROTECTED_KW) &&
                peek_token().type == TokenType::COLON) {
                return;
            }
        }
        advance();
    }
}

void Parser::skip_to_enum_sync_point() {
    if (is_in_tentative_context()) {
        return;
    }
    int brace_depth = 0;
    while (!gentle_check(TokenType::Eof)) {
        TokenType tt = current_token().type;
        if (tt == TokenType::LEFT_BRACE) {
            brace_depth++;
            advance();
            continue;
        }
        if (tt == TokenType::RIGHT_BRACE) {
            if (brace_depth > 0) {
                brace_depth--;
                advance();
                continue;
            }
            return; // stop before '}' at depth 0
        }
        if (brace_depth == 0 && tt == TokenType::COMMA) {
            advance(); // consume ','
            return;
        }
        advance();
    }
}

void Parser::skip_to_init_list_sync_point() {
    if (is_in_tentative_context()) {
        return;
    }
    int brace_depth = 0;
    while (!gentle_check(TokenType::Eof)) {
        TokenType tt = current_token().type;
        if (tt == TokenType::LEFT_BRACE) {
            brace_depth++;
            advance();
            continue;
        }
        if (tt == TokenType::RIGHT_BRACE) {
            if (brace_depth > 0) {
                brace_depth--;
                advance();
                continue;
            }
            return; // stop before '}' at depth 0
        }
        if (brace_depth == 0 && tt == TokenType::COMMA) {
            advance(); // consume ','
            return;
        }
        advance();
    }
}

void Parser::skip_to_param_sync_point() {
    if (is_in_tentative_context()) {
        return;
    }
    int paren_depth = 0;
    while (!gentle_check(TokenType::Eof)) {
        TokenType tt = current_token().type;
        if (tt == TokenType::LEFT_PAREN) {
            paren_depth++;
            advance();
            continue;
        }
        if (tt == TokenType::RIGHT_PAREN) {
            if (paren_depth > 0) {
                paren_depth--;
                advance();
                continue;
            }
            return; // stop before ')' at depth 0
        }
        if (paren_depth == 0 && tt == TokenType::COMMA) {
            advance(); // consume ','
            return;
        }
        advance();
    }
}

// ---- Attribute parsing ----

std::vector<ParsedAttribute> Parser::try_parse_attributes() {
    std::vector<ParsedAttribute> attrs;

    while (true) {
        if (is_gnu_attribute_token(current_token())) {
            auto gnu_attrs = parse_gnu_attribute_list();
            attrs.insert(attrs.end(),
                std::make_move_iterator(gnu_attrs.begin()),
                std::make_move_iterator(gnu_attrs.end()));
        } else if (gentle_check(TokenType::LEFT_BRACKET) &&
                   peek_token().type == TokenType::LEFT_BRACKET) {
            auto c23_attrs = parse_c23_attribute_list();
            attrs.insert(attrs.end(),
                std::make_move_iterator(c23_attrs.begin()),
                std::make_move_iterator(c23_attrs.end()));
        } else {
            break;
        }
    }

    // Resolve attribute kinds once so downstream Collect/codegen can query by kind.
    auto& registry = AttributeRegistry::instance();
    for (auto& attr : attrs) {
        const auto* desc = registry.find(attr.canonical_name());
        attr.resolved_kind = desc ? desc->kind : AttributeKind::UNKNOWN;
        if (attr.resolved_kind != AttributeKind::UNKNOWN) {
            continue;
        }

        DiagnosticSeverity sev = DiagnosticSeverity::Warning;
        if (tok_mgnt.sm) {
            sev = tok_mgnt.sm->getDiagnosticState(attr.loc).get(WarningId::UnknownAttributes);
        }
        if (sev == DiagnosticSeverity::Ignored) {
            continue;
        }

        std::string msg = "unknown attribute '" + attr.name + "'";
        if (sev == DiagnosticSeverity::Error) {
            error_custloc(msg, attr.loc);
        } else {
            diag_engine->report_warning(msg, attr.loc);
        }
    }

    return attrs;
}

bool Parser::is_c23_constexpr_enabled() const {
    if (is_cxx_mode_active()) {
        return true;
    }
    return lang_opts.enable_c23_constexpr &&
           is_c23_family_standard(lang_opts.standard);
}

LanguageLinkage Parser::current_decl_language_linkage() const {
    if (current_language_linkage_ != LanguageLinkage::None) {
        return current_language_linkage_;
    }
    return lang_opts.is_cxx_mode() ? LanguageLinkage::CXX : LanguageLinkage::C;
}

std::vector<ParsedAttribute> Parser::parse_gnu_attribute_list() {
    std::vector<ParsedAttribute> attrs;

    while (is_gnu_attribute_token(current_token())) {
        advance(); // consume __attribute__ token (keyword or identifier fallback)
        // Expect ((
        check_and_consume(TokenType::LEFT_PAREN);
        check_and_consume(TokenType::LEFT_PAREN);

        // Parse comma-separated attribute list
        while (!gentle_check(TokenType::RIGHT_PAREN)) {
            if (gentle_check(TokenType::COMMA)) {
                advance(); // skip empty attribute (allowed per spec)
                continue;
            }

            auto attr = parse_single_attribute();
            attrs.push_back(std::move(attr));

            if (!gentle_check(TokenType::RIGHT_PAREN)) {
                check_and_consume(TokenType::COMMA);
            }
        }

        // Expect ))
        check_and_consume(TokenType::RIGHT_PAREN);
        check_and_consume(TokenType::RIGHT_PAREN);
    }

    return attrs;
}

std::vector<ParsedAttribute> Parser::parse_c23_attribute_list() {
    std::vector<ParsedAttribute> attrs;

    // We already know current token is LEFT_BRACKET and peek is LEFT_BRACKET
    check_and_consume(TokenType::LEFT_BRACKET);
    check_and_consume(TokenType::LEFT_BRACKET);

    // Parse comma-separated attribute list until ]]
    while (!(gentle_check(TokenType::RIGHT_BRACKET) &&
             peek_token().type == TokenType::RIGHT_BRACKET)) {

        if (gentle_check(TokenType::COMMA)) {
            advance();
            continue;
        }

        ParsedAttribute attr;
        attr.loc = current_token().loc;

        // Parse attribute name (possibly scoped: gnu::noreturn)
        Token name_tok = current_token();
        if (name_tok.type != TokenType::IDENTIFIER &&
            name_tok.type != TokenType::CONST &&
            name_tok.type != TokenType::VOLATILE &&
            name_tok.type != TokenType::NORETURN_KW) {
            error("expected attribute name in [[...]], got \"" + name_tok.value + "\"");
            break;
        }
        std::string first_name = name_tok.value;
        advance();

        // Check for :: scope resolution (e.g., gnu::noreturn)
        if (is_cpp_scope_resolution_here()) {
            // Scoped attribute: namespace::name
            consume_cpp_scope_resolution();
            attr.ns = first_name;
            Token scoped_name = current_token();
            if (scoped_name.type == TokenType::IDENTIFIER ||
                scoped_name.type == TokenType::CONST) {
                attr.name = scoped_name.value;
                advance();
            } else {
                error("expected attribute name after '::', got \"" + scoped_name.value + "\"");
                break;
            }
        } else {
            attr.name = first_name;
        }

        // Check for arguments in parentheses
        if (gentle_check_and_consume(TokenType::LEFT_PAREN)) {
            auto is_attr_ident = [](TokenType t) {
                return t == TokenType::IDENTIFIER || t == TokenType::CONST ||
                       t == TokenType::VOLATILE || t == TokenType::INLINE ||
                       t == TokenType::NORETURN_KW;
            };
            while (!gentle_check(TokenType::RIGHT_PAREN)) {
                Token arg_tok = current_token();
                if (is_attr_ident(arg_tok.type) && peek_token().type == TokenType::ASSIGN) {
                    std::string key = arg_tok.value;
                    advance(); // key
                    advance(); // '='
                    Token val_tok = current_token();
                    std::string val;
                    SrcLoc val_loc = val_tok.loc;
                    if (val_tok.type == TokenType::STRING_LITERAL) {
                        val = val_tok.value;
                        advance();
                    } else if (is_integer_literal(val_tok.type)) {
                        val = val_tok.value;
                        advance();
                    } else if (is_floating_literal(val_tok.type)) {
                        val = val_tok.value;
                        advance();
                    } else if (is_attr_ident(val_tok.type)) {
                        val = val_tok.value;
                        advance();
                    } else if (val_tok.type == TokenType::LEFT_PAREN) {
                        skip_balanced_parens();
                    } else {
                        advance();
                    }
                    attr.args.push_back(AttributeArg::make_key_value(key, val, val_loc));
                } else if (arg_tok.type == TokenType::STRING_LITERAL) {
                    attr.args.push_back(AttributeArg::make_string(arg_tok.value, arg_tok.loc));
                    advance();
                } else if (is_integer_literal(arg_tok.type)) {
                    auto parsed_val = parse_integer_literal_u64(arg_tok.value);
                    int64_t val = parsed_val.has_value()
                        ? static_cast<int64_t>(parsed_val.value())
                        : 0;
                    attr.args.push_back(AttributeArg::make_int(val, arg_tok.loc));
                    advance();
                } else if (is_floating_literal(arg_tok.type)) {
                    double val = 0.0;
                    try {
                        val = std::stod(arg_tok.value);
                    } catch (...) {
                        val = 0.0;
                    }
                    attr.args.push_back(AttributeArg::make_float(arg_tok.value, val, arg_tok.loc));
                    advance();
                } else if (is_attr_ident(arg_tok.type)) {
                    attr.args.push_back(AttributeArg::make_ident(arg_tok.value, arg_tok.loc));
                    advance();
                } else if (arg_tok.type == TokenType::LEFT_PAREN) {
                    skip_balanced_parens();
                } else {
                    advance();
                }

                if (!gentle_check(TokenType::RIGHT_PAREN)) {
                    gentle_check_and_consume(TokenType::COMMA);
                }
            }
            check_and_consume(TokenType::RIGHT_PAREN);
        }

        attrs.push_back(std::move(attr));

        // Comma between attributes
        if (!gentle_check(TokenType::RIGHT_BRACKET)) {
            if (!gentle_check_and_consume(TokenType::COMMA)) {
                // Not comma, not ]], something is wrong but try to continue
            }
        }
    }

    // Expect ]]
    check_and_consume(TokenType::RIGHT_BRACKET);
    check_and_consume(TokenType::RIGHT_BRACKET);

    return attrs;
}

void Parser::skip_balanced_brackets() {
    check_and_consume(TokenType::LEFT_BRACKET);
    int depth = 1;
    while (depth > 0 && !gentle_check(TokenType::Eof)) {
        if (gentle_check(TokenType::LEFT_BRACKET)) {
            depth++;
        } else if (gentle_check(TokenType::RIGHT_BRACKET)) {
            depth--;
            if (depth == 0) {
                advance();
                return;
            }
        }
        advance();
    }
}

ParsedAttribute Parser::parse_single_attribute() {
    ParsedAttribute attr;
    attr.loc = current_token().loc;

    // Attribute name can be an identifier or certain keywords (e.g., 'const')
    Token name_tok = current_token();
    if (name_tok.type == TokenType::IDENTIFIER || name_tok.type == TokenType::CONST
        || name_tok.type == TokenType::VOLATILE || name_tok.type == TokenType::INLINE) {
        attr.name = name_tok.value;
        advance();
    } else {
        error("expected attribute name, got \"" + name_tok.value + "\"");
        return attr;
    }
    const bool parse_args_as_constexpr =
        (attr.canonical_name() == "vector_size" || attr.canonical_name() == "aligned");

    // Check for arguments in parentheses
    if (gentle_check_and_consume(TokenType::LEFT_PAREN)) {
        // Parse arguments: identifiers, integers, strings, floats, or key=value pairs
        while (!gentle_check(TokenType::RIGHT_PAREN)) {
            Token arg_tok = current_token();
            auto is_attr_ident = [](TokenType t) {
                return t == TokenType::IDENTIFIER || t == TokenType::CONST ||
                       t == TokenType::VOLATILE || t == TokenType::INLINE ||
                       t == TokenType::NORETURN_KW;
            };

            if (is_attr_ident(arg_tok.type) && peek_token().type == TokenType::ASSIGN) {
                std::string key = arg_tok.value;
                advance(); // key
                advance(); // '='
                Token val_tok = current_token();
                std::string val;
                SrcLoc val_loc = val_tok.loc;
                if (val_tok.type == TokenType::STRING_LITERAL) {
                    val = val_tok.value;
                    advance();
                } else if (is_integer_literal(val_tok.type)) {
                    val = val_tok.value;
                    advance();
                } else if (is_floating_literal(val_tok.type)) {
                    val = val_tok.value;
                    advance();
                } else if (is_attr_ident(val_tok.type)) {
                    val = val_tok.value;
                    advance();
                } else if (val_tok.type == TokenType::PP_NUMBER) {
                    val = val_tok.value;
                    advance();
                } else if (val_tok.type == TokenType::LEFT_PAREN) {
                    skip_balanced_parens();
                } else {
                    advance();
                }
                attr.args.push_back(AttributeArg::make_key_value(key, val, val_loc));
            } else if (parse_args_as_constexpr) {
                size_t arg_start_idx = get_token_idx();
                auto expr = parse_conditional_expression();
                if (get_token_idx() == arg_start_idx) {
                    // Recovery guard for malformed expressions to avoid infinite loops.
                    advance();
                }
                int64_t val = 0;
                if (!expr) {
                    error("vector_size requires an integer constant expression");
                } else {
                    auto eval = try_evaluate_with_consteval_compat(
                        expr.get(), ConstEvalMode::c_ice());
                    if (!eval.has_value()) {
                        error("vector_size requires an integer constant expression");
                    } else {
                        val = eval.value();
                    }
                }
                attr.args.push_back(AttributeArg::make_int(val, arg_tok.loc));
            } else if (arg_tok.type == TokenType::STRING_LITERAL) {
                attr.args.push_back(AttributeArg::make_string(arg_tok.value, arg_tok.loc));
                advance();
            } else if (is_integer_literal(arg_tok.type) || arg_tok.type == TokenType::SIZEOF) {
                // Parse as a constant expression to handle things like 2 * sizeof(int)
                auto expr = parse_binary_expression();
                int64_t val = 0;
                if (expr) {
                    auto eval = try_evaluate_with_consteval_compat(
                        expr.get(), ConstEvalMode::c_ice());
                    if (eval.has_value()) {
                        val = eval.value();
                    }
                }
                attr.args.push_back(AttributeArg::make_int(val, arg_tok.loc));
            } else if (is_floating_literal(arg_tok.type)) {
                double val = 0.0;
                try {
                    val = std::stod(arg_tok.value);
                } catch (...) {
                    val = 0.0;
                }
                attr.args.push_back(AttributeArg::make_float(arg_tok.value, val, arg_tok.loc));
                advance();
            } else if (is_attr_ident(arg_tok.type)) {
                attr.args.push_back(AttributeArg::make_ident(arg_tok.value, arg_tok.loc));
                advance();
            } else if (arg_tok.type == TokenType::PP_NUMBER) {
                // PP-numbers like 10.12.1 (e.g. in availability attributes) - treat as string
                attr.args.push_back(AttributeArg::make_string(arg_tok.value, arg_tok.loc));
                advance();
            } else if (arg_tok.type == TokenType::LEFT_PAREN) {
                // Nested parentheses - skip balanced
                skip_balanced_parens();
            } else {
                // Skip unrecognized tokens within attribute arguments
                advance();
            }

            if (!gentle_check(TokenType::RIGHT_PAREN)) {
                if (!gentle_check_and_consume(TokenType::COMMA)) {
                    // If not comma or rparen, just continue consuming
                    // This handles complex expressions in attribute args
                }
            }
        }
        check_and_consume(TokenType::RIGHT_PAREN);
    }

    return attr;
}

void Parser::skip_balanced_parens() {
    check_and_consume(TokenType::LEFT_PAREN);
    int depth = 1;
    while (depth > 0 && !gentle_check(TokenType::Eof)) {
        if (gentle_check(TokenType::LEFT_PAREN)) {
            depth++;
        } else if (gentle_check(TokenType::RIGHT_PAREN)) {
            depth--;
            if (depth == 0) {
                advance();
                return;
            }
        }
        advance();
    }
}

// This assumes lon
int ranking_const(TokenType t) {
    switch (t) {
        case TokenType::INTEGER_CONST:
            return 1;
        case TokenType::UNSIGNED_INTEGER_CONST:
            return 2;
        case TokenType::LONG_CONST:
            return 3;
        case TokenType::UNSIGNED_LONG_CONST:
            return 4;
        case TokenType::LONG_LONG_CONST:
            return 5;
        case TokenType::UNSIGNED_LONG_LONG_CONST:
            return 6;
        default:
            return -1;
    }
}
static bool is_decimal_integer_literal(const std::string& text) {
    if (text.size() >= 2 && text[0] == '0' &&
        (text[1] == 'x' || text[1] == 'X' || text[1] == 'b' || text[1] == 'B')) {
        return false;
    }
    if (text.size() > 1 && text[0] == '0') {
        return false;
    }
    return true;
}

std::shared_ptr<CType> getNumericTypeConstant(Token tok, TypeContext * type_ctx) {
    auto parsed = parse_integer_literal_u64(tok.value);
    if (!parsed.has_value()) {
        return nullptr;
    }
    uint64_t val = parsed.value();
    TokenType tt = tok.type;
    bool has_unsigned = (tt == TokenType::UNSIGNED_INTEGER_CONST ||
        tt == TokenType::UNSIGNED_LONG_CONST || tt == TokenType::UNSIGNED_LONG_LONG_CONST);
    bool has_long = (tt == TokenType::LONG_CONST || tt == TokenType::UNSIGNED_LONG_CONST);
    bool has_long_long = (tt == TokenType::LONG_LONG_CONST || tt == TokenType::UNSIGNED_LONG_LONG_CONST);
    bool is_decimal = is_decimal_integer_literal(tok.value);

    uint64_t int32_max = static_cast<uint64_t>(std::numeric_limits<int32_t>::max());
    uint64_t int64_max = static_cast<uint64_t>(std::numeric_limits<int64_t>::max());
    uint64_t uint32_max = static_cast<uint64_t>(std::numeric_limits<uint32_t>::max());

    // u/ul/ull suffix families
    if (has_unsigned) {
        if (!has_long && !has_long_long && val <= uint32_max) {
            return type_ctx->get_builtin(BuiltinTypes::UInt);
        }
        if (has_long_long) {
            return type_ctx->get_builtin(BuiltinTypes::ULongLong);
        }
        if (has_long) {
            return type_ctx->get_builtin(BuiltinTypes::ULong);
        }
        if (val <= int64_max) {
            return type_ctx->get_builtin(BuiltinTypes::ULong);
        }
        return type_ctx->get_builtin(BuiltinTypes::ULongLong);
    }

    // ll suffix family
    if (has_long_long) {
        if (val <= int64_max) {
            return type_ctx->get_builtin(BuiltinTypes::LongLong);
        }
        // GCC/Clang accept this as an extension (with warning)
        return type_ctx->get_builtin(BuiltinTypes::ULongLong);
    }

    // l suffix family
    if (has_long) {
        if (val <= int64_max) {
            return type_ctx->get_builtin(BuiltinTypes::Long);
        }
        if (!is_decimal) {
            return type_ctx->get_builtin(BuiltinTypes::ULong);
        }
        // GCC/Clang accept this as an extension (with warning)
        return type_ctx->get_builtin(BuiltinTypes::ULongLong);
    }

    // no suffix family
    if (val <= int32_max) {
        return type_ctx->get_builtin(BuiltinTypes::Int);
    }
    // C11 6.4.4.1: For hex/octal/binary, unsigned int comes before long
    if (!is_decimal && val <= uint32_max) {
        return type_ctx->get_builtin(BuiltinTypes::UInt);
    }
    if (val <= int64_max) {
        return type_ctx->get_builtin(BuiltinTypes::Long);
    }
    if (!is_decimal) {
        return type_ctx->get_builtin(BuiltinTypes::ULong);
    }
    // GCC/Clang extension for oversized unsuffixed decimal integer constants
    return type_ctx->get_builtin(BuiltinTypes::ULongLong);
}



std::unique_ptr<Decl> Parser::parse() {
    current_language_linkage_ = LanguageLinkage::None;
    cxx_namespace_canonical_decl_cache_.clear();
    cxx_namespace_latest_decl_cache_.clear();
    cxx_record_parse_stack_.clear();
    cpp_transient_semantic_decls_.clear();
    ASTContextSideTableScope side_table_scope(ast_ctx.get());
    if (ast_ctx) {
        ast_ctx->clear_external_semantic_side_tables();
    }
    collect_->set_lang_options(lang_opts);
    std::unique_ptr<Decl> trans;
    try {
        trans = parse_translation_unit();
    } catch (FatalErrorLimitReached&) {
        // Error limit reached — diagnostics already recorded
    }

    if (diag_engine->has_errors()) {
        diag_engine->flush_diagnostics();
        return nullptr;
    }

    return trans;
}
