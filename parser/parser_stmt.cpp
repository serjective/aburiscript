#include "parser.h"

#include <limits>

// Shared literal-token helpers are implemented in parser/parser.cpp.
bool is_integer_literal(TokenType tok);
bool is_floating_literal(TokenType tok);

namespace {
struct LocalLabelScopeGuard {
    std::vector<std::unordered_map<std::string, std::string>>& scopes;

    explicit LocalLabelScopeGuard(
        std::vector<std::unordered_map<std::string, std::string>>& scopes)
        : scopes(scopes) {
        scopes.emplace_back();
    }

    ~LocalLabelScopeGuard() {
        if (!scopes.empty()) {
            scopes.pop_back();
        }
    }
};

} // namespace

std::string Parser::resolve_local_label_name(const std::string& name) const {
    for (auto it = local_label_scopes_.rbegin(); it != local_label_scopes_.rend(); ++it) {
        auto found = it->find(name);
        if (found != it->end()) {
            return found->second;
        }
    }
    return name;
}

void Parser::declare_local_labels(const std::vector<std::string>& labels, SrcLoc loc) {
    if (local_label_scopes_.empty()) {
        local_label_scopes_.emplace_back();
    }
    auto& scope_map = local_label_scopes_.back();
    for (const auto& label : labels) {
        if (scope_map.find(label) != scope_map.end()) {
            diag_engine->report_error("redefinition of local label '" + label + "'", loc);
            continue;
        }
        std::string mangled = "__aburi_local_label_" + std::to_string(++local_label_unique_id_) + "_" + label;
        scope_map.emplace(label, std::move(mangled));
    }
}

std::unique_ptr<Stmt> Parser::parse_goto() {
    Token t = current_token();
    check_and_consume(TokenType::GOTO);
    if (gentle_check(TokenType::MULTIPLY)) {
        advance(); // consume '*'
        if (gentle_check(TokenType::SEMICOLON)) {
            error("expected expression after 'goto *'");
            return nullptr;
        }
        auto expr = parse_expression();
        check_and_consume(TokenType::SEMICOLON);
        return collect_->collect_computed_goto_statement(std::move(expr), t.loc);
    }
    if (!gentle_check(TokenType::IDENTIFIER)) {
        error("error in parse_goto");
        return nullptr;
    }
    std::string name = resolve_local_label_name(current_token().value);
    advance(); // done with identifer
    check_and_consume(TokenType::SEMICOLON);
    return collect_->collect_goto_statement(name, t.loc);

}
std::unique_ptr<Stmt> Parser::parse_break() {
    Token t = current_token();
    check_and_consume(TokenType::BREAK);
    check_and_consume(TokenType::SEMICOLON);
    return collect_->collect_break_statement(t.loc);
}
std::unique_ptr<Stmt> Parser::parse_continue() {
    Token t = current_token();
    check_and_consume(TokenType::CONTINUE);
    check_and_consume(TokenType::SEMICOLON);
    return collect_->collect_continue_statement(t.loc);
}
std::unique_ptr<Stmt> Parser::parse_return() {
    Token t = current_token();
    if (!gentle_check_and_consume(TokenType::RETURN)) {
        // first token wasn't return
        error("error in parse_return");
        return {};
    }
    std::unique_ptr<Expr> expr = nullptr;
    if (!gentle_check(TokenType::SEMICOLON)) {
        if (is_cxx_mode_active() && gentle_check(TokenType::LEFT_BRACE)) {
            expr = parse_init_list();
        } else {
            expr = parse_expression();
        }
    }
    if (!gentle_check_and_consume(TokenType::SEMICOLON)) {
        error("error in parse_return; missing semicolon");
        return {};
    }
    QualType expected_return = nullptr;
    if (func_type) {
        auto func_ty = dyn_cast_shared<FunctionType>(func_type);
        if (func_ty) {
            expected_return = func_ty->ret_type;
        }
    }
    return collect_->collect_return_statement(std::move(expr), t.loc, expected_return);
}
// aka block-item/6.8.2
std::unique_ptr<Stmt> Parser::parse_stmt_or_decl() {
    // Handle __extension__ as a no-op prefix in statement/decl context
    if (gentle_check(TokenType::EXTENSION_KW)) {
        advance(); // consume __extension__
        return parse_stmt_or_decl();
    }
    // Handle __label__ local label declarations (GCC extension) — parse and ignore
    if (gentle_check(TokenType::LABEL_KW)) {
        auto loc = current_token().loc;
        advance(); // consume __label__
        // Parse comma-separated list of identifiers and scope-mangle them.
        if (!gentle_check(TokenType::IDENTIFIER)) {
            error("expected identifier after __label__");
        }
        std::vector<std::string> labels;
        labels.push_back(current_token().value);
        advance();
        while (gentle_check(TokenType::COMMA)) {
            advance(); // consume ','
            if (!gentle_check(TokenType::IDENTIFIER)) {
                error("expected identifier in __label__ declaration");
            }
            labels.push_back(current_token().value);
            advance();
        }
        check_and_consume(TokenType::SEMICOLON);
        declare_local_labels(labels, loc);
        // Return a null statement — __label__ has no runtime effect
        return collect_->collect_empty_statement(loc);
    }
    // When we see attributes, look ahead past them to determine if this is
    // a declaration or a statement with attributes (e.g. [[fallthrough]];)
    if (is_gnu_attribute_token(current_token()) ||
        (gentle_check(TokenType::LEFT_BRACKET) && peek_token().type == TokenType::LEFT_BRACKET)) {
        {
            TentativeParsingAction tentative(*this);
            try {
                auto decl = parse_declaration();
                tentative.commit();
                return collect_->collect_decl_statement(std::move(decl));
            } catch (const ParseError&) {
            } catch (const FatalErrorLimitReached&) {
            }
        }
        // Not a declaration - treat as statement with attributes
        return parse_stmt();
    }
    if (is_cxx_mode_active() && gentle_check(TokenType::NAMESPACE)) {
        auto decl = parse_declaration();
        return collect_->collect_decl_statement(std::move(decl));
    }
    auto starts_with_record_qualified_id = [&]() -> bool {
        if (!is_cxx_mode_active()) {
            return false;
        }
        auto consume_scope_resolution = [&](size_t& offset) -> bool {
            Token tok = peek_token_shortcut(offset);
            if (tok.type == TokenType::SCOPE_RESOLUTION) {
                ++offset;
                return true;
            }
            if (tok.type == TokenType::COLON &&
                peek_token_shortcut(offset + 1).type == TokenType::COLON) {
                offset += 2;
                return true;
            }
            return false;
        };

        size_t offset = 0;
        bool has_global_qualifier = consume_scope_resolution(offset);
        Token owner_tok = peek_token_shortcut(offset);
        if (owner_tok.type != TokenType::IDENTIFIER) {
            return false;
        }
        size_t sep_offset = offset + 1;
        if (!consume_scope_resolution(sep_offset)) {
            return false;
        }
        auto* owner_tag_decl = collect_->collect_lookup_tag_decl(
            owner_tok.value, !has_global_qualifier);
        return dyn_cast<ObjectDecl>(owner_tag_decl) != nullptr;
    };
    if (isTokenDeclarationSpec(current_token())) {
        if (is_cxx_mode_active()) {
            if (current_token().type == TokenType::IDENTIFIER) {
                if (starts_with_record_qualified_id()) {
                    return parse_stmt();
                }
                if (starts_with_cpp_dependent_qualified_call_expression()) {
                    return parse_stmt();
                }
                CxxStmtDisambiguation disambiguated =
                    classify_cxx_stmt_disambiguation();
                if (disambiguated == CxxStmtDisambiguation::Expression ||
                    disambiguated == CxxStmtDisambiguation::Invalid) {
                    return parse_stmt();
                }
            } else if (current_token().type == TokenType::SCOPE_RESOLUTION ||
                       (current_token().type == TokenType::COLON &&
                        peek_token().type == TokenType::COLON)) {
                if (starts_with_record_qualified_id()) {
                    return parse_stmt();
                }
            }
            auto decl = parse_declaration();
            return collect_->collect_decl_statement(std::move(decl));
        }
        if (current_token().type == TokenType::IDENTIFIER) {
            {
                TentativeParsingAction tentative(*this);
                try {
                    auto decl = parse_declaration();
                    tentative.commit();
                    return collect_->collect_decl_statement(std::move(decl));
                } catch (const ParseError&) {
                } catch (const FatalErrorLimitReached&) {
                }
            }
            return parse_stmt();
        }
        auto decl = parse_declaration();
        return collect_->collect_decl_statement(std::move(decl));
    }
    return parse_stmt();
}
// todo: look at this, have optiona to disable decl parsing
// Todo: there are many tokens that indicate expressions. We should use parse_Expressions as a fall back
// and should have parse_expressions return nullptr if invalid.
// If it is invalid then we throw and error as we dont know token state
// (and we dont know where to progress as the parse_expresssion cal was a fallback)

std::unique_ptr<Stmt> Parser::parse_stmt() {
    // Parse leading C23 [[...]] statement attributes
    auto stmt_attrs = try_parse_attributes();

    Token t = current_token();
    if (gentle_check(TokenType::SEMICOLON)) {
        advance();
        auto empty = collect_->collect_empty_statement(t.loc);
        if (!stmt_attrs.empty()) {
            ast_ctx->append_attrs(empty->node_id, std::move(stmt_attrs));
        }
        return empty;
    }
    if (is_cxx_mode_active() && gentle_check(TokenType::TRY_KW)) {
        return parse_cpp_try_statement();
    }
    if (gentle_check(TokenType::IF)) {
        return parse_if_stmt();
    }
    if (gentle_check(TokenType::DO)) {
        return parse_do_while_stmt();
    }
    if (gentle_check(TokenType::WHILE)) {
        return parse_while_stmt();
    }
    if (gentle_check(TokenType::FOR)) {
        return parse_for_stmt();
    }
    if (gentle_check(TokenType::SWITCH)) {
        return parse_switch();
    }
    if (gentle_check(TokenType::CASE)) {
        return parse_case_stmt();
    }
    if (gentle_check(TokenType::DEFAULT)) {
        return parse_default_stmt();
    }
    if (gentle_check(TokenType::RETURN)) {
        return parse_return();
    }
    if (gentle_check(TokenType::BREAK)) {
        return parse_break();
    }
    if (gentle_check(TokenType::GOTO)) {
        return parse_goto();
    }
    if (gentle_check(TokenType::CONTINUE)) {
        return parse_continue();
    }
    if (gentle_check(TokenType::ASM_KW)) {
        return parse_asm_stmt();
    }
    if (gentle_check(TokenType::LEFT_BRACE)) {
        return parse_compound_stmt();
    }
    if (gentle_check(TokenType::IDENTIFIER)) {
        Token next = peek_token(1);
        if (next.type == TokenType::COLON) {
            std::string name = resolve_local_label_name(current_token().value);
            stmt_labels.insert(name);
            advance();
            advance(); // consume colon
            // Parse optional label attributes: label: __attribute__((unused)) stmt
            auto label_attrs = try_parse_attributes();
            std::unique_ptr<Stmt> stmt;
            if (gentle_check(TokenType::RIGHT_BRACE)) {
                // GNU extension: allow a trailing label at end-of-block.
                // Model it as an empty statement without consuming '}'.
                stmt = collect_->collect_empty_statement(current_token().loc);
            } else {
                stmt = parse_stmt();
            }
            auto labeled = collect_->collect_labeled_statement(name, std::move(stmt), t.loc);
            if (!label_attrs.empty()) {
                ast_ctx->append_attrs(labeled->node_id, std::move(label_attrs));
            }
            return labeled;
        }
        // todo: check if valid identifier
        auto exp = parse_expression();
        check_and_consume(TokenType::SEMICOLON);
        return collect_->collect_expression_statement(std::move(exp), t.loc);
    }
    if (is_integer_literal(current_token().type) || is_floating_literal(current_token().type)
        || gentle_check(TokenType::INCREMENT)
    || gentle_check(TokenType::DECREMENT) || gentle_check(TokenType::LEFT_PAREN)
    || gentle_check(TokenType::LEFT_BRACKET)
    || gentle_check(TokenType::MULTIPLY) || gentle_check(TokenType::BITWISE_AND)
    || gentle_check(TokenType::CHAR_LITERAL) || gentle_check(TokenType::STRING_LITERAL)
    || gentle_check(TokenType::GENERIC)
    || gentle_check(TokenType::THIS_KW)
    || gentle_check(TokenType::THROW_KW)
    || gentle_check(TokenType::REAL_PART) || gentle_check(TokenType::IMAG_PART)
    || gentle_check(TokenType::SIZEOF) || gentle_check(TokenType::ALIGNOF)
    || gentle_check(TokenType::LOGICAL_NOT) || gentle_check(TokenType::BITWISE_NOT)
    || gentle_check(TokenType::PLUS) || gentle_check(TokenType::NEGATE)
    || gentle_check(TokenType::LOGICAL_AND)
    || gentle_check(TokenType::NEW) || gentle_check(TokenType::DELETE)) {
        auto exp = parse_expression();
        check_and_consume(TokenType::SEMICOLON);
        return collect_->collect_expression_statement(std::move(exp), t.loc);
    }
    error("unsupported statement");
    return nullptr;
}
std::optional<size_t> Parser::find_cpp_if_init_semicolon() {
    if (!is_cxx_mode_active()) {
        return std::nullopt;
    }

    int paren_depth = 0;
    int bracket_depth = 0;
    int brace_depth = 0;
    int conditional_depth = 0;
    size_t offset = 0;
    while (true) {
        Token tok = peek_token_shortcut(offset);
        if (tok.type == TokenType::Eof) {
            return std::nullopt;
        }
        if (tok.type == TokenType::RIGHT_PAREN &&
            paren_depth == 0 &&
            bracket_depth == 0 &&
            brace_depth == 0) {
            return std::nullopt;
        }

        switch (tok.type) {
            case TokenType::LEFT_PAREN:
                ++paren_depth;
                break;
            case TokenType::RIGHT_PAREN:
                if (paren_depth > 0) {
                    --paren_depth;
                }
                break;
            case TokenType::LEFT_BRACKET:
                ++bracket_depth;
                break;
            case TokenType::RIGHT_BRACKET:
                if (bracket_depth > 0) {
                    --bracket_depth;
                }
                break;
            case TokenType::LEFT_BRACE:
                ++brace_depth;
                break;
            case TokenType::RIGHT_BRACE:
                if (brace_depth > 0) {
                    --brace_depth;
                }
                break;
            case TokenType::QUESTION:
                if (paren_depth == 0 && bracket_depth == 0 && brace_depth == 0) {
                    ++conditional_depth;
                }
                break;
            case TokenType::COLON:
                if (peek_token_shortcut(offset + 1).type == TokenType::COLON) {
                    ++offset;
                    break;
                }
                if (paren_depth == 0 && bracket_depth == 0 &&
                    brace_depth == 0 && conditional_depth > 0) {
                    --conditional_depth;
                }
                break;
            case TokenType::SEMICOLON:
                if (paren_depth == 0 && bracket_depth == 0 &&
                    brace_depth == 0 && conditional_depth == 0) {
                    return offset;
                }
                break;
            default:
                break;
        }
        ++offset;
    }
}

std::unique_ptr<Stmt> Parser::parse_if_stmt() {
    Token t = current_token();
    check_and_consume(TokenType::IF);
    bool is_constexpr_if = false;
    if (gentle_check(TokenType::CONSTEXPR_KW)) {
        if (!is_cxx_mode_active()) {
            error_custloc("'if constexpr' is only allowed in C++", current_token().loc);
        }
        is_constexpr_if = true;
        advance();
    }
    check_and_consume(TokenType::LEFT_PAREN);

    auto entered_scope = is_cxx_mode_active()
        ? collect_->collect_enter_scope(ScopeFlags::BlockScope)
        : Collect::ScopeEnterResult{};
    struct IfScopeGuard {
        Parser* parser = nullptr;
        bool active = false;
        ~IfScopeGuard() {
            if (active && parser && parser->collect_) {
                parser->collect_->collect_leave_scope();
            }
        }
    } if_scope_guard{this, is_cxx_mode_active()};

    auto starts_with_record_qualified_id = [&]() -> bool {
        if (!is_cxx_mode_active()) {
            return false;
        }
        auto consume_scope_resolution = [&](size_t& offset) -> bool {
            Token tok = peek_token_shortcut(offset);
            if (tok.type == TokenType::SCOPE_RESOLUTION) {
                ++offset;
                return true;
            }
            if (tok.type == TokenType::COLON &&
                peek_token_shortcut(offset + 1).type == TokenType::COLON) {
                offset += 2;
                return true;
            }
            return false;
        };

        size_t offset = 0;
        bool has_global_qualifier = consume_scope_resolution(offset);
        Token owner_tok = peek_token_shortcut(offset);
        if (owner_tok.type != TokenType::IDENTIFIER) {
            return false;
        }
        size_t sep_offset = offset + 1;
        if (!consume_scope_resolution(sep_offset)) {
            return false;
        }
        auto* owner_tag_decl = collect_->collect_lookup_tag_decl(
            owner_tok.value, !has_global_qualifier);
        return dyn_cast<ObjectDecl>(owner_tag_decl) != nullptr;
    };

    auto should_parse_if_init_as_declaration = [&]() -> bool {
        if (gentle_check(TokenType::SEMICOLON) ||
            !isTokenDeclarationSpec(current_token())) {
            return false;
        }
        if (is_cxx_mode_active() &&
            (current_token().type == TokenType::IDENTIFIER ||
             current_token().type == TokenType::SCOPE_RESOLUTION ||
             (current_token().type == TokenType::COLON &&
              peek_token().type == TokenType::COLON))) {
            if (starts_with_record_qualified_id()) {
                return false;
            }
            if (starts_with_cpp_dependent_qualified_call_expression()) {
                return false;
            }
            CxxStmtDisambiguation disambiguated =
                classify_cxx_stmt_disambiguation();
            return disambiguated == CxxStmtDisambiguation::Declaration;
        }
        return true;
    };

    auto parse_if_init_statement = [&]() -> std::unique_ptr<Stmt> {
        if (should_parse_if_init_as_declaration()) {
            auto decl = parse_declaration();
            for (const auto& d : decl) {
                if (isa<FuncDecl>(d.get())) {
                    error("function declaration not allowed in if init-statement");
                }
            }
            return collect_->collect_decl_statement(std::move(decl));
        }
        if (gentle_check(TokenType::SEMICOLON)) {
            advance();
            return nullptr;
        }
        auto init_loc = current_token().loc;
        auto init_expr = parse_expression();
        auto stmt = collect_->collect_expression_statement(
            std::move(init_expr), init_loc);
        check_and_consume(TokenType::SEMICOLON);
        return stmt;
    };

    std::unique_ptr<Stmt> init_stmt = nullptr;
    if (find_cpp_if_init_semicolon()) {
        init_stmt = parse_if_init_statement();
    }

    auto condition = parse_expression();
    check_and_consume(TokenType::RIGHT_PAREN);
    auto condition_info = collect_->collect_if_condition(
        std::move(condition),
        is_constexpr_if ? IfStatementKind::Constexpr : IfStatementKind::Runtime,
        t.loc);

    auto branch_state = [&](bool then_branch) -> CppConstexprIfBranchState {
        if (!is_constexpr_if) {
            return CppConstexprIfBranchState::Active;
        }
        if (!condition_info.constexpr_value.has_value()) {
            return CppConstexprIfBranchState::Deferred;
        }
        bool active = *condition_info.constexpr_value == then_branch;
        return active ? CppConstexprIfBranchState::Active
                      : CppConstexprIfBranchState::Discarded;
    };
    struct ConstexprIfBranchGuard {
        Collect* collect = nullptr;
        bool active = false;
        ConstexprIfBranchGuard(Collect* collect,
                               bool enabled,
                               CppConstexprIfBranchState state)
            : collect(collect), active(enabled) {
            if (active && collect) {
                collect->collect_enter_constexpr_if_branch(state);
            }
        }
        ~ConstexprIfBranchGuard() {
            if (active && collect) {
                collect->collect_leave_constexpr_if_branch();
            }
        }
    };

    // Warn on extraneous semicolon: if (x);
    if (gentle_check(TokenType::SEMICOLON) && !gentle_check(TokenType::Eof)) {
        Token semi = current_token();
        Token after_semi = peek_token(1);
        // Only warn if followed by something that looks like it should be the body
        if (after_semi.type == TokenType::LEFT_BRACE || after_semi.type == TokenType::IDENTIFIER ||
            after_semi.type == TokenType::RETURN || after_semi.type == TokenType::IF) {
            diag_engine->report_warning("if statement has empty body; did you mean to remove the ';'?", semi.loc);
        }
    }
    std::unique_ptr<Stmt> then_stmt;
    {
        ConstexprIfBranchGuard guard(
            collect_.get(), is_constexpr_if, branch_state(true));
        then_stmt = parse_stmt();
    }

    std::unique_ptr<Stmt> else_stmt = nullptr;
    if (gentle_check_and_consume(TokenType::ELSE)) {
        ConstexprIfBranchGuard guard(
            collect_.get(), is_constexpr_if, branch_state(false));
        else_stmt = parse_stmt();
    }

    auto selection_scope = entered_scope.scope;
    if_scope_guard.active = false;
    if (is_cxx_mode_active()) {
        collect_->collect_leave_scope();
    }
    return collect_->collect_if_statement(
        std::move(init_stmt),
        std::move(condition_info.condition),
        std::move(then_stmt),
        std::move(else_stmt),
        is_constexpr_if ? IfStatementKind::Constexpr : IfStatementKind::Runtime,
        std::move(selection_scope),
        condition_info.constexpr_value,
        t.loc);
}
std::unique_ptr<Stmt> Parser::parse_switch() {
    Token t = current_token();
    check_and_consume(TokenType::SWITCH);
    check_and_consume(TokenType::LEFT_PAREN);
    auto condition = parse_expression();
    check_and_consume(TokenType::RIGHT_PAREN);
    collect_->collect_enter_switch();
    condition = collect_->collect_switch_condition(std::move(condition), t.loc);
    auto body_stmt = parse_stmt();
    collect_->collect_leave_switch();
    return collect_->collect_switch_statement(std::move(condition), std::move(body_stmt), t.loc);
}
std::unique_ptr<Stmt> Parser::parse_case_stmt() {
    struct PendingLabel {
        bool is_default = false;
        std::unique_ptr<Expr> begin;
        std::unique_ptr<Expr> end;
        SrcLoc loc;
    };

    std::vector<PendingLabel> labels;
    while (gentle_check(TokenType::CASE) || gentle_check(TokenType::DEFAULT)) {
        if (gentle_check(TokenType::CASE)) {
            Token t = current_token();
            check_and_consume(TokenType::CASE);
            auto begin = parse_conditional_expression(); // Case expression must be a constant expression
            std::unique_ptr<Expr> end = nullptr;
            if (gentle_check_and_consume(TokenType::ELLIPSIS)) {
                end = parse_conditional_expression();
            }
            check_and_consume(TokenType::COLON);
            labels.push_back(PendingLabel{
                .is_default = false,
                .begin = std::move(begin),
                .end = std::move(end),
                .loc = t.loc
            });
            continue;
        }

        Token t = current_token();
        check_and_consume(TokenType::DEFAULT);
        check_and_consume(TokenType::COLON);
        labels.push_back(PendingLabel{
            .is_default = true,
            .begin = nullptr,
            .end = nullptr,
            .loc = t.loc
        });
    }

    auto stmt = parse_stmt();
    for (auto it = labels.rbegin(); it != labels.rend(); ++it) {
        if (it->is_default) {
            stmt = collect_->collect_default_statement(std::move(stmt), it->loc);
        } else {
            stmt = collect_->collect_case_statement(
                std::move(it->begin), std::move(it->end), std::move(stmt), it->loc);
        }
    }
    return stmt;
}
std::unique_ptr<Stmt> Parser::parse_default_stmt() {
    // Reuse the iterative labeled-statement path to avoid deep recursion on
    // long case/default chains.
    return parse_case_stmt();
}
std::unique_ptr<Stmt> Parser::parse_while_stmt() {
    Token t = current_token();
    check_and_consume(TokenType::WHILE);
    check_and_consume(TokenType::LEFT_PAREN);
    auto condition = parse_expression();
    check_and_consume(TokenType::RIGHT_PAREN);
    collect_->collect_enter_loop();
    auto body_stmt = parse_stmt();
    collect_->collect_leave_loop();
    return collect_->collect_while_statement(std::move(condition),
        std::move(body_stmt), t.loc);
}

std::unique_ptr<Stmt> Parser::parse_do_while_stmt() {
    Token t = current_token();
    check_and_consume(TokenType::DO);
    collect_->collect_enter_loop();
    auto body_stmt = parse_stmt();
    check_and_consume(TokenType::WHILE);
    check_and_consume(TokenType::LEFT_PAREN);
    auto condition = parse_expression();
    check_and_consume(TokenType::RIGHT_PAREN);
    check_and_consume(TokenType::SEMICOLON); // Do-while loops require a semicolon after the while condition
    collect_->collect_leave_loop();
    return collect_->collect_do_while_statement(std::move(condition),
                                         std::move(body_stmt), t.loc);
}

std::optional<size_t> Parser::find_cpp_range_for_colon_semicolon_count() {
    if (!is_cxx_mode_active()) {
        return std::nullopt;
    }

    int paren_depth = 0;
    int bracket_depth = 0;
    int brace_depth = 0;
    int conditional_depth = 0;
    size_t top_level_semicolons = 0;
    size_t offset = 0;
    while (true) {
        Token tok = peek_token_shortcut(offset);
        if (tok.type == TokenType::Eof) {
            return std::nullopt;
        }
        if (tok.type == TokenType::RIGHT_PAREN &&
            paren_depth == 0 &&
            bracket_depth == 0 &&
            brace_depth == 0) {
            return std::nullopt;
        }

        switch (tok.type) {
            case TokenType::LEFT_PAREN:
                ++paren_depth;
                break;
            case TokenType::RIGHT_PAREN:
                if (paren_depth > 0) {
                    --paren_depth;
                }
                break;
            case TokenType::LEFT_BRACKET:
                ++bracket_depth;
                break;
            case TokenType::RIGHT_BRACKET:
                if (bracket_depth > 0) {
                    --bracket_depth;
                }
                break;
            case TokenType::LEFT_BRACE:
                ++brace_depth;
                break;
            case TokenType::RIGHT_BRACE:
                if (brace_depth > 0) {
                    --brace_depth;
                }
                break;
            case TokenType::QUESTION:
                if (paren_depth == 0 && bracket_depth == 0 && brace_depth == 0) {
                    ++conditional_depth;
                }
                break;
            case TokenType::SEMICOLON:
                if (paren_depth == 0 && bracket_depth == 0 &&
                    brace_depth == 0 && conditional_depth == 0) {
                    ++top_level_semicolons;
                    if (top_level_semicolons > 1) {
                        return std::nullopt;
                    }
                }
                break;
            case TokenType::SCOPE_RESOLUTION:
                break;
            case TokenType::COLON:
                if (peek_token_shortcut(offset + 1).type == TokenType::COLON) {
                    ++offset;
                    break;
                }
                if (paren_depth == 0 && bracket_depth == 0 &&
                    brace_depth == 0) {
                    if (conditional_depth > 0) {
                        --conditional_depth;
                        break;
                    }
                    return top_level_semicolons;
                }
                break;
            default:
                break;
        }
        ++offset;
    }
}

CppRangeForDeclarationInfo Parser::parse_cpp_range_for_declaration() {
    Token start_tok = current_token();
    DeclarationParser decl_parser(this);
    std::vector<std::unique_ptr<Decl>> side_decls;
    auto base_type = parse_declaration_head(start_tok, decl_parser, side_decls);
    auto parsed_type = decl_parser.parse_declarator(base_type);
    retain_type_specifier_decl_if_needed(decl_parser);
    auto trailing_attrs = try_parse_attributes();
    (void)trailing_attrs;

    if (!parsed_type) {
        error_custloc("expected declaration in range-for declaration",
                      start_tok.loc);
    }
    if (decl_parser.name.empty()) {
        error_custloc("range-for declaration requires a variable name",
                      decl_parser.loc.isInvalid() ? start_tok.loc : decl_parser.loc);
    }
    if (canonical_type_kind(parsed_type, ast_ctx.get()) == TypeKind::Function) {
        error_custloc("range-for declaration cannot declare a function",
                      decl_parser.loc.isInvalid() ? start_tok.loc : decl_parser.loc);
    }

    CppRangeForDeclarationInfo info;
    info.declared_type = QualType(parsed_type, decl_parser.qualifiers);
    info.name = decl_parser.name;
    info.storage_class = decl_parser.str_class;
    info.is_constexpr = decl_parser.is_constexpr;
    info.is_consteval = decl_parser.is_consteval;
    info.is_thread_local = decl_parser.is_thread_local;
    info.is_block_byref = decl_parser.is_block_byref;
    info.loc = decl_parser.loc.isInvalid() ? start_tok.loc : decl_parser.loc;
    info.side_decls = std::move(side_decls);
    return info;
}

std::unique_ptr<Stmt> Parser::parse_for_stmt() {
    Token t = current_token();
    check_and_consume(TokenType::FOR);
    check_and_consume(TokenType::LEFT_PAREN);
    const size_t for_header_begin_idx = get_token_idx();
    std::unique_ptr<Stmt> first_clause;
    std::unique_ptr<Expr> second_clause;
    std::unique_ptr<Expr> third_clause;

    auto entered_scope = collect_->collect_enter_scope(
        ScopeFlags::BlockScope | ScopeFlags::LoopScope);
    auto new_scope = entered_scope.scope;

    auto parse_second_and_third_clause = [&]() {
        if (gentle_check(TokenType::SEMICOLON)) {
            second_clause = nullptr;
        } else {
            second_clause = parse_expression();
        }
        check_and_consume(TokenType::SEMICOLON);

        if (gentle_check(TokenType::RIGHT_PAREN)) {
            third_clause = nullptr;
        } else {
            third_clause = parse_expression();
        }
        check_and_consume(TokenType::RIGHT_PAREN);
    };

    auto parse_for_init_as_declaration = [&]() {
        auto decl = parse_declaration();
        for (const auto& d : decl) {
            if (isa<FuncDecl>(d.get())) {
                error("function declaration not allowed in for-loop init");
            }
        }
        first_clause = collect_->collect_decl_statement(std::move(decl));
        parse_second_and_third_clause();
    };

    auto parse_for_init_as_expression = [&]() {
        if (gentle_check(TokenType::SEMICOLON)) {
            first_clause = nullptr;
        } else {
            auto first_expr = parse_expression();
            first_clause = collect_->collect_expression_statement(
                std::move(first_expr), t.loc);
        }
        check_and_consume(TokenType::SEMICOLON);
        parse_second_and_third_clause();
    };

    auto recover_after_for_header_error = [&]() {
        set_token_idx(for_header_begin_idx);
        int paren_depth = 0;
        int bracket_depth = 0;
        int brace_depth = 0;
        while (!gentle_check(TokenType::Eof)) {
            if (gentle_check(TokenType::LEFT_PAREN)) {
                ++paren_depth;
                advance();
                continue;
            }
            if (gentle_check(TokenType::RIGHT_PAREN)) {
                if (paren_depth > 0) {
                    --paren_depth;
                    advance();
                    continue;
                }
                if (bracket_depth == 0 && brace_depth == 0) {
                    advance();
                    break;
                }
            }
            if (gentle_check(TokenType::LEFT_BRACKET)) {
                ++bracket_depth;
                advance();
                continue;
            }
            if (gentle_check(TokenType::RIGHT_BRACKET)) {
                if (bracket_depth > 0) {
                    --bracket_depth;
                }
                advance();
                continue;
            }
            if (gentle_check(TokenType::LEFT_BRACE)) {
                ++brace_depth;
                advance();
                continue;
            }
            if (gentle_check(TokenType::RIGHT_BRACE)) {
                if (brace_depth > 0) {
                    --brace_depth;
                    advance();
                    continue;
                }
                break;
            }
            advance();
        }
    };

    auto starts_with_record_qualified_id = [&]() -> bool {
        if (!is_cxx_mode_active()) {
            return false;
        }
        auto consume_scope_resolution = [&](size_t& offset) -> bool {
            Token tok = peek_token_shortcut(offset);
            if (tok.type == TokenType::SCOPE_RESOLUTION) {
                ++offset;
                return true;
            }
            if (tok.type == TokenType::COLON &&
                peek_token_shortcut(offset + 1).type == TokenType::COLON) {
                offset += 2;
                return true;
            }
            return false;
        };

        size_t offset = 0;
        bool has_global_qualifier = consume_scope_resolution(offset);
        Token owner_tok = peek_token_shortcut(offset);
        if (owner_tok.type != TokenType::IDENTIFIER) {
            return false;
        }
        size_t sep_offset = offset + 1;
        if (!consume_scope_resolution(sep_offset)) {
            return false;
        }
        auto* owner_tag_decl = collect_->collect_lookup_tag_decl(
            owner_tok.value, !has_global_qualifier);
        return dyn_cast<ObjectDecl>(owner_tag_decl) != nullptr;
    };

    auto should_parse_for_init_as_declaration = [&]() -> bool {
        if (gentle_check(TokenType::SEMICOLON) ||
            !isTokenDeclarationSpec(current_token())) {
            return false;
        }
        if (is_cxx_mode_active() &&
            (current_token().type == TokenType::IDENTIFIER ||
             current_token().type == TokenType::SCOPE_RESOLUTION ||
             (current_token().type == TokenType::COLON &&
              peek_token().type == TokenType::COLON))) {
            if (starts_with_record_qualified_id()) {
                return false;
            }
            if (starts_with_cpp_dependent_qualified_call_expression()) {
                return false;
            }
            CxxStmtDisambiguation disambiguated =
                classify_cxx_stmt_disambiguation();
            return disambiguated == CxxStmtDisambiguation::Declaration;
        }
        return true;
    };

    auto parse_for_init_statement = [&]() -> std::unique_ptr<Stmt> {
        if (should_parse_for_init_as_declaration()) {
            auto decl = parse_declaration();
            for (const auto& d : decl) {
                if (isa<FuncDecl>(d.get())) {
                    error("function declaration not allowed in for-loop init");
                }
            }
            return collect_->collect_decl_statement(std::move(decl));
        }
        if (gentle_check(TokenType::SEMICOLON)) {
            advance();
            return nullptr;
        }
        auto first_expr = parse_expression();
        auto stmt = collect_->collect_expression_statement(
            std::move(first_expr), t.loc);
        check_and_consume(TokenType::SEMICOLON);
        return stmt;
    };

    try {
        if (auto range_init_semicolons =
                find_cpp_range_for_colon_semicolon_count()) {
            if (*range_init_semicolons == 1) {
                if (!lang_opts.is_cxx20_or_later()) {
                    diag_engine->report_warning(
                        "range-for init-statement is a C++20 extension",
                        current_token().loc);
                }
                first_clause = parse_for_init_statement();
            }

            auto range_decl = parse_cpp_range_for_declaration();
            check_and_consume(TokenType::COLON);
            auto range_init = gentle_check(TokenType::LEFT_BRACE)
                ? parse_init_list()
                : parse_expression();
            check_and_consume(TokenType::RIGHT_PAREN);

            auto range_stmt = collect_->collect_cpp_range_for_statement(
                std::move(first_clause),
                std::move(range_decl),
                std::move(range_init),
                nullptr,
                new_scope,
                t.loc);

            collect_->collect_enter_loop();
            auto body_stmt = parse_stmt();
            collect_->collect_leave_loop();
            range_stmt->body_stmt = std::move(body_stmt);
            collect_->collect_leave_scope();
            return range_stmt;
        }

        if (should_parse_for_init_as_declaration()) {
            parse_for_init_as_declaration();
        } else {
            parse_for_init_as_expression();
        }
    } catch (ParseError& e) {
        if (is_in_tentative_context()) {
            throw;
        }
        // Keep the original header diagnostic as the primary error and
        // recover locally to avoid cascading follow-on diagnostics.
        recover_after_for_header_error();
        if (!gentle_check(TokenType::Eof)) {
            collect_->collect_enter_loop();
            try {
                (void)parse_stmt();
            } catch (ParseError&) {
                size_t recover_start_idx = get_token_idx();
                skip_to_stmt_sync_point();
                if (get_token_idx() == recover_start_idx &&
                    !gentle_check(TokenType::Eof)) {
                    advance();
                }
            }
            collect_->collect_leave_loop();
        }
        collect_->collect_leave_scope();
        return collect_->collect_error_statement(e.message, e.location);
    }
    collect_->collect_enter_loop();
    auto body_stmt = parse_stmt();
    collect_->collect_leave_loop();

    collect_->collect_leave_scope();

    return collect_->collect_for_statement(std::move(first_clause),
        std::move(second_clause),
        std::move(third_clause),
        std::move(body_stmt), new_scope, t.loc);
}

std::unique_ptr<Stmt> Parser::parse_compound_stmt(std::shared_ptr<Scope> use_scope) {
    Token t = current_token();
    std::vector<std::unique_ptr<Stmt>> statements;
    LocalLabelScopeGuard local_label_scope(local_label_scopes_);
    auto new_scope = use_scope;
    bool scope_entered = false;
    if (new_scope == nullptr) {
        auto entered_scope = collect_->collect_enter_scope(ScopeFlags::BlockScope);
        new_scope = entered_scope.scope;
        scope_entered = entered_scope.created_new;
    }
    check_and_consume(TokenType::LEFT_BRACE);
    size_t last_recovery_idx = std::numeric_limits<size_t>::max();
    while (!gentle_check(TokenType::RIGHT_BRACE) && !gentle_check(TokenType::Eof)) {
        try {
            std::unique_ptr<Stmt> stmt = parse_stmt_or_decl();
            diag_engine->sync_point_reached();
            last_recovery_idx = std::numeric_limits<size_t>::max();
            statements.push_back(std::move(stmt));
        } catch (ParseError& e) {
            if (is_in_tentative_context()) {
                throw;
            }
            // Error already recorded by diag_engine
            size_t recover_start_idx = get_token_idx();
            skip_to_stmt_sync_point();
            if (get_token_idx() == recover_start_idx &&
                recover_start_idx == last_recovery_idx &&
                !gentle_check(TokenType::Eof)) {
                advance();
            }
            last_recovery_idx = get_token_idx();
            diag_engine->sync_point_reached();
            statements.push_back(collect_->collect_error_statement(e.message, e.location));
        }
    }
    check_and_consume(TokenType::RIGHT_BRACE);
    if (scope_entered) {
        collect_->collect_leave_scope();
    }
    return collect_->collect_compound_statement(std::move(statements), new_scope, t.loc);

}

std::string Parser::parse_asm_string_literal() {
    std::string result;
    if (!gentle_check(TokenType::STRING_LITERAL)) {
        error("expected string literal in asm statement");
    }
    result = current_token().value;
    advance();
    // Concatenate adjacent string literals
    while (gentle_check(TokenType::STRING_LITERAL)) {
        result += current_token().value;
        advance();
    }
    return result;
}

std::unique_ptr<Stmt> Parser::parse_asm_stmt() {
    SrcLoc loc = current_token().loc;
    advance(); // consume asm/__asm__/__asm

    // Parse asm qualifiers: volatile, inline, goto (in any order)
    bool qual_volatile = false;
    bool qual_inline = false;
    bool qual_goto = false;
    while (true) {
        if (gentle_check(TokenType::VOLATILE)) {
            qual_volatile = true;
            advance();
        } else if (gentle_check(TokenType::INLINE)) {
            qual_inline = true;
            advance();
        } else if (gentle_check(TokenType::GOTO)) {
            qual_goto = true;
            advance();
        } else {
            break;
        }
    }

    check_and_consume(TokenType::LEFT_PAREN);
    std::string asm_template = parse_asm_string_literal();

    bool has_colon = false;
    std::vector<AsmOperand> outputs;
    std::vector<AsmOperand> inputs;
    std::vector<std::string> clobbers;
    std::vector<std::string> goto_labels;

    // Check for extended asm (colon after template)
    if (gentle_check(TokenType::COLON)) {
        has_colon = true;
        advance(); // consume first colon

        // Parse output operands
        while (!gentle_check(TokenType::COLON) && !gentle_check(TokenType::RIGHT_PAREN)) {
            AsmOperand op;
            op.loc = current_token().loc;
            // Optional symbolic name: [name]
            if (gentle_check(TokenType::LEFT_BRACKET)) {
                advance();
                if (!gentle_check(TokenType::IDENTIFIER)) {
                    error("expected identifier in asm operand symbolic name");
                }
                op.symbolic_name = current_token().value;
                advance();
                check_and_consume(TokenType::RIGHT_BRACKET);
            }
            // Constraint string
            if (!gentle_check(TokenType::STRING_LITERAL)) {
                error("expected constraint string in asm operand");
            }
            op.constraint = current_token().value;
            advance();
            // (expression)
            check_and_consume(TokenType::LEFT_PAREN);
            op.expr = parse_expression();
            check_and_consume(TokenType::RIGHT_PAREN);
            outputs.push_back(std::move(op));
            if (!gentle_check_and_consume(TokenType::COMMA)) break;
        }

        // Parse input operands (second colon)
        if (gentle_check(TokenType::COLON)) {
            advance();
            while (!gentle_check(TokenType::COLON) && !gentle_check(TokenType::RIGHT_PAREN)) {
                AsmOperand op;
                op.loc = current_token().loc;
                if (gentle_check(TokenType::LEFT_BRACKET)) {
                    advance();
                    if (!gentle_check(TokenType::IDENTIFIER)) {
                        error("expected identifier in asm operand symbolic name");
                    }
                    op.symbolic_name = current_token().value;
                    advance();
                    check_and_consume(TokenType::RIGHT_BRACKET);
                }
                if (!gentle_check(TokenType::STRING_LITERAL)) {
                    error("expected constraint string in asm operand");
                }
                op.constraint = current_token().value;
                advance();
                check_and_consume(TokenType::LEFT_PAREN);
                op.expr = parse_expression();
                check_and_consume(TokenType::RIGHT_PAREN);
                inputs.push_back(std::move(op));
                if (!gentle_check_and_consume(TokenType::COMMA)) break;
            }

            // Parse clobbers (third colon)
            if (gentle_check(TokenType::COLON)) {
                advance();
                while (!gentle_check(TokenType::COLON) && !gentle_check(TokenType::RIGHT_PAREN)) {
                    if (!gentle_check(TokenType::STRING_LITERAL)) {
                        error("expected string literal in asm clobber list");
                    }
                    clobbers.push_back(current_token().value);
                    advance();
                    if (!gentle_check_and_consume(TokenType::COMMA)) break;
                }

                // Parse goto labels (fourth colon, only if goto qualifier)
                if (gentle_check(TokenType::COLON)) {
                    if (!qual_goto) {
                        error("fourth colon in asm requires 'goto' qualifier");
                    }
                    advance();
                    while (!gentle_check(TokenType::RIGHT_PAREN)) {
                        if (!gentle_check(TokenType::IDENTIFIER)) {
                            error("expected label name in asm goto");
                        }
                        goto_labels.push_back(current_token().value);
                        advance();
                        if (!gentle_check_and_consume(TokenType::COMMA)) break;
                    }
                }
            }
        }
    }

    check_and_consume(TokenType::RIGHT_PAREN);
    check_and_consume(TokenType::SEMICOLON);
    return collect_->collect_asm_statement(
        std::move(asm_template),
        qual_volatile,
        qual_inline,
        qual_goto,
        has_colon,
        std::move(outputs),
        std::move(inputs),
        std::move(clobbers),
        std::move(goto_labels),
        loc);
}
