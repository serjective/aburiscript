#include "parser.h"

#include <algorithm>
#include <limits>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace aburi::syntax {

Parser::ParsedStmt Parser::parse_statement() {
    if (!collect_session_.collecting_pattern()) {
        return parse_statement_inner();
    }

    TokenType head = current().type;
    bool is_constexpr_if_recipe =
        head == TokenType::IF && peek(1).type == TokenType::CONSTEXPR_KW;
    bool is_expansion_statement_recipe =
        head == TokenType::TEMPLATE && peek(1).type == TokenType::FOR;
    if (head == TokenType::SWITCH || head == TokenType::GOTO ||
        head == TokenType::ASM_KW || head == TokenType::LABEL_KW ||
        head == TokenType::CASE || head == TokenType::DEFAULT ||
        head == TokenType::TRY_KW ||
        (is_identifier_token(head) && peek(1).type == TokenType::COLON)) {
        collect_session_.mark_pattern_unusable();
        return parse_statement_inner();
    }
    size_t token_begin = current_raw_index();
    uint64_t taint_before = collect_session_.pattern_taint();
    size_t events_before = collect_session_.pattern_event_count();
    ParsedStmt stmt = parse_statement_inner();
    if (collect_session_.pattern_taint() != taint_before) {
        size_t token_end = current_raw_index();
        stmt.sem = collect_session_.make_pattern_hole_stmt(
            token_begin, token_end, taint_before, events_before,
            token_range_display(token_begin, token_end),
            loc_for_index(token_begin),
            is_constexpr_if_recipe
                ? collect::Session::PatternHole::Kind::ConstexprIf
                : is_expansion_statement_recipe
                    ? collect::Session::PatternHole::Kind::ExpansionStatement
                : collect::Session::PatternHole::Kind::Statement);
    }
    return stmt;
}

Parser::ParsedStmt Parser::parse_statement_inner() {
    if (at_end()) {
        size_t begin = current_raw_index();
        return {parse_error_node("expected statement", begin, begin), {}};
    }
    if (lang_opts_.is_objc() && check(TokenType::AT) &&
        peek(1).type != TokenType::STRING_LITERAL) {
        std::string directive = objc_directive_spelling();
        if (directive == "throw" || directive == "autoreleasepool" ||
            directive == "try" || directive == "synchronized") {
            return parse_objc_at_statement();
        }
    }
    if (is_attribute_start()) {
        RevertingTentativeParsingAction tentative(*this, TentativeMode::ParserOnly);
        (void)try_parse_attributes();
        bool is_attributed_empty = check(TokenType::SEMICOLON);
        bool is_attributed_declaration = is_type_start(current().type) || is_attribute_start();
        tentative.revert();

        if (is_attributed_empty) {
            size_t begin = current_raw_index();
            ParsedAttributes attrs = try_parse_attributes();
            consume();
            collect::StmtResult sem =
                collect_session_.collect_compound_stmt({}, loc_for_index(begin));
            return {make_node(NodeKind::ExprStmt,
                              begin,
                              last_consumed_raw_end(),
                              attrs.syntax),
                    sem};
        }
        if (!is_attributed_declaration) {
            size_t begin = current_raw_index();
            ParsedAttributes attrs = try_parse_attributes();
            ParsedStmt child = parse_statement();
            attrs.syntax.push_back(child.syntax);
            return {make_node(NodeKind::AmbiguousSyntax,
                              begin,
                              last_consumed_raw_end(),
                              attrs.syntax),
                    child.sem};
        }
    }
    if (check(TokenType::STATIC_ASSERT)) {
        SrcLoc loc = current().loc;
        ParsedDecl decl = parse_static_assert_declaration();
        collect::StmtResult sem = collect_session_.collect_compound_stmt({}, loc);
        return {decl.syntax, sem};
    }
    if (lang_opts_.is_cxx_mode() && check(TokenType::USING)) {
        SrcLoc loc = current().loc;
        ParsedDecl decl = parse_cxx_using_declaration();
        collect::StmtResult sem =
            collect_session_.collect_decl_stmt(std::move(decl.sem), loc);
        return {decl.syntax, std::move(sem)};
    }
    if (lang_opts_.is_cxx_mode() && check(TokenType::NAMESPACE) &&
        is_identifier_token(peek(1).type) &&
        peek(2).type == TokenType::ASSIGN) {

        SrcLoc loc = current().loc;
        ParsedDecl decl = parse_cxx_namespace_declaration();
        collect::StmtResult sem =
            collect_session_.collect_decl_stmt(std::move(decl.sem), loc);
        return {decl.syntax, std::move(sem)};
    }
    if (check(TokenType::LEFT_BRACE)) return parse_compound_statement();
    if (check(TokenType::RETURN)) return parse_return_statement();
    if (check(TokenType::CO_RETURN_KW)) return parse_co_return_statement();
    if (lang_opts_.is_cxx_mode() && check(TokenType::TRY_KW)) {
        return parse_try_statement();
    }
    if (check(TokenType::IF)) return parse_if_statement();
    if (check(TokenType::WHILE)) return parse_while_statement();
    if (check(TokenType::DO)) return parse_do_while_statement();
    if (check(TokenType::FOR)) {
        if (lang_opts_.is_objc() && objc_for_in_ahead()) {
            return parse_objc_for_in_statement();
        }
        return parse_for_statement();
    }
    if (lang_opts_.is_cxx_mode() && check(TokenType::TEMPLATE) &&
        peek(1).type == TokenType::FOR) {
        return parse_expansion_statement();
    }
    if (check(TokenType::SWITCH)) return parse_switch_statement();
    if (check(TokenType::CASE) || check(TokenType::DEFAULT)) return parse_case_or_default_statement();
    if (check(TokenType::LABEL_KW)) return parse_local_label_declaration_statement();
    if (check(TokenType::GOTO)) return parse_goto_statement();
    if (check(TokenType::ASM_KW)) return parse_asm_statement();
    if (is_identifier_token(current().type) && peek(1).type == TokenType::COLON) {
        return parse_label_statement();
    }
    if (check(TokenType::BREAK)) {
        size_t begin = current_raw_index();
        SrcLoc loc = current().loc;
        consume();
        match(TokenType::SEMICOLON);
        collect::StmtResult sem = collect_session_.collect_break_stmt(loc);
        return {make_node(NodeKind::BreakStmt, begin, last_consumed_raw_end()), sem};
    }
    if (check(TokenType::CONTINUE)) {
        size_t begin = current_raw_index();
        SrcLoc loc = current().loc;
        consume();
        match(TokenType::SEMICOLON);
        collect::StmtResult sem = collect_session_.collect_continue_stmt(loc);
        return {make_node(NodeKind::ContinueStmt, begin, last_consumed_raw_end()), sem};
    }
    StmtDeclDisambiguation disambiguation = classify_stmt_or_decl();
    if (disambiguation == StmtDeclDisambiguation::Declaration ||
        disambiguation == StmtDeclDisambiguation::Ambiguous) {
        ParsedDecl decl = parse_declaration(false);
        collect::StmtResult sem =
            collect_session_.collect_decl_stmt(std::move(decl.sem), tree_.node(decl.syntax).loc);
        return {decl.syntax, sem};
    }
    return parse_expression_statement();
}

Parser::ParsedStmt Parser::parse_compound_statement() {
    size_t begin = current_raw_index();
    match(TokenType::LEFT_BRACE);
    std::vector<NodeId> statements;
    std::vector<collect::StmtResult> sem_children;
    collect_session_.begin_scope();
    collect_session_.begin_local_label_scope();
    while (!at_end() && !check(TokenType::RIGHT_BRACE)) {
        size_t before = mark();
        ParsedStmt stmt = parse_statement();
        statements.push_back(stmt.syntax);
        sem_children.push_back(stmt.sem);
        if (!made_progress(before)) {
            size_t error_begin = current_raw_index();
            statements.push_back(
                parse_error_node("parser made no progress in compound statement", error_begin, error_begin + 1));
            consume();
        }
    }
    collect::StmtResult scope_cleanups =
        collect_session_.collect_scope_cleanups(loc_for_index(begin));
    if (!scope_cleanups.fragment.empty()) {
        sem_children.push_back(std::move(scope_cleanups));
    }
    collect_session_.end_local_label_scope(loc_for_index(begin));
    collect_session_.end_scope();
    if (!match(TokenType::RIGHT_BRACE)) {
        diagnose(DiagnosticLevel::Error, "expected '}'", current_loc());
        collect::StmtResult sem =
            collect_session_.collect_compound_stmt(std::move(sem_children), loc_for_index(begin));
        sem.has_error = true;
        return {make_node(NodeKind::CompoundStmt, begin, last_consumed_raw_end(), statements, {}, NodeFlagHasError), sem};
    }
    collect::StmtResult sem = collect_session_.collect_compound_stmt(std::move(sem_children), loc_for_index(begin));
    return {make_node(NodeKind::CompoundStmt, begin, last_consumed_raw_end(), statements), sem};
}

Parser::ParsedStmt Parser::parse_return_statement() {
    size_t begin = current_raw_index();
    SrcLoc loc = current().loc;
    consume();
    std::vector<NodeId> children;
    std::optional<collect::ExprResult> expr_sem;
    collect::Session::LifetimeBoundary return_boundary =
        collect_session_.begin_lifetime_boundary();
    if (!check(TokenType::SEMICOLON)) {
        ParsedExpr expr = parse_expression();
        children.push_back(expr.syntax);
        expr_sem = expr.sem;
    }
    if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error, "expected ';' after return statement", current_loc());
        skip_until_statement_boundary();
    }
    collect::StmtResult sem = collect_session_.collect_return_stmt(
        expr_sem, loc, return_boundary);
    return {make_node(NodeKind::ReturnStmt, begin, last_consumed_raw_end(), children), sem};
}

Parser::ParsedStmt Parser::parse_co_return_statement() {

    size_t begin = current_raw_index();
    SrcLoc loc = current().loc;
    consume();
    std::vector<NodeId> children;
    std::optional<collect::ExprResult> expr_sem;
    collect::Session::LifetimeBoundary boundary =
        collect_session_.begin_lifetime_boundary();
    if (!check(TokenType::SEMICOLON)) {
        ParsedExpr expr = check(TokenType::LEFT_BRACE)
            ? parse_init_list_expression()
            : parse_expression();
        children.push_back(expr.syntax);
        expr_sem = expr.sem;
    }
    if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error, "expected ';' after co_return statement", current_loc());
        skip_until_statement_boundary();
    }
    collect::StmtResult sem = collect_session_.collect_co_return_stmt(
        std::move(expr_sem), loc, boundary);
    return {make_node(NodeKind::CoReturnStmt, begin, last_consumed_raw_end(), children), sem};
}

Parser::ParsedStmt Parser::parse_if_statement() {
    size_t begin = current_raw_index();
    SrcLoc loc = current().loc;
    consume();
    bool is_constexpr_if = false;
    if (lang_opts_.is_cxx_mode() && check(TokenType::CONSTEXPR_KW)) {
        consume();
        is_constexpr_if = true;
    }
    std::vector<NodeId> children;
    ParsedExpr cond;
    collect::Session::LifetimeBoundary condition_boundary;
    std::optional<collect::StmtResult> init_sem;
    bool scope_opened = false;
    uint64_t condition_taint_before = collect_session_.pattern_taint();
    if (!match(TokenType::LEFT_PAREN)) {
        diagnose(DiagnosticLevel::Error, "expected '(' after if", current_loc());
    } else {
        if (lang_opts_.is_cxx_mode() && cxx_if_has_init_statement()) {

            collect_session_.begin_scope();
            scope_opened = true;
            if (check(TokenType::SEMICOLON)) {
                consume();
            } else {
                StmtDeclDisambiguation disambiguation = classify_stmt_or_decl();
                if (disambiguation == StmtDeclDisambiguation::Declaration ||
                    disambiguation == StmtDeclDisambiguation::Ambiguous) {
                    ParsedDecl init_decl = parse_declaration(false);
                    children.push_back(init_decl.syntax);
                    init_sem = collect_session_.collect_decl_stmt(
                        std::move(init_decl.sem), tree_.node(init_decl.syntax).loc);
                } else {
                    collect::Session::LifetimeBoundary init_boundary =
                        collect_session_.begin_lifetime_boundary();
                    ParsedExpr init = parse_expression();
                    children.push_back(init.syntax);
                    init_sem = collect_session_.collect_expr_stmt(
                        std::move(init.sem), tree_.node(init.syntax).loc,
                        &init_boundary);
                    if (!match(TokenType::SEMICOLON)) {
                        diagnose(DiagnosticLevel::Error,
                                 "expected ';' after if init-statement",
                                 current_loc());
                    }
                }
            }
        }
        condition_taint_before = collect_session_.pattern_taint();
        condition_boundary = collect_session_.begin_lifetime_boundary();
        bool condition_is_declaration =
            lang_opts_.is_cxx_mode() && cxx_condition_is_declaration();
        if (condition_is_declaration) {

            if (!scope_opened) {
                collect_session_.begin_scope();
                scope_opened = true;
            }
            cond = parse_cxx_condition_declaration();
            children.push_back(cond.syntax);
        } else {
            cond = parse_expression();
            children.push_back(cond.syntax);
        }
        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error, "expected ')' after if condition", current_loc());
        }

        cond.sem = collect_session_.require_value(
            std::move(cond.sem), collect::UseContext::Condition, loc);
        collect_session_.close_lifetime_boundary_without_cleanup(
            condition_boundary);
    }

    auto finish_if_scope = [&](collect::StmtResult core) -> collect::StmtResult {
        if (!scope_opened) {
            return core;
        }
        std::vector<collect::StmtResult> parts;
        if (init_sem.has_value()) {
            parts.push_back(std::move(*init_sem));
        }
        parts.push_back(std::move(core));
        collect::StmtResult cleanups = collect_session_.collect_scope_cleanups(loc);
        if (!cleanups.fragment.empty()) {
            parts.push_back(std::move(cleanups));
        }
        collect_session_.end_scope();
        return collect_session_.collect_compound_stmt(std::move(parts), loc);
    };

    if (is_constexpr_if) {
        bool condition_dependent =
            collect_session_.pattern_taint() != condition_taint_before ||
            collect_session_.expr_is_value_dependent(cond.sem);
        int64_t condition_value = 0;
        bool condition_error = false;
        if (!condition_dependent && !cond.sem.has_error) {

            cond.sem = collect_session_.require_value(
                std::move(cond.sem), collect::UseContext::Condition, loc);
        }
        if (!condition_dependent) {
            if (cond.sem.has_error) {
                condition_error = true;
            } else if (!collect_session_.try_evaluate_required_integer_constant(
                           cond.sem, condition_value, loc)) {
                if (collect_session_.collecting_pattern()) {

                    condition_dependent = true;
                } else {
                    diagnose(DiagnosticLevel::Error,
                             "constexpr if condition is not a constant expression",
                             loc);
                    condition_error = true;
                }
            }
        }
        if (!condition_dependent) {

            bool take_then = condition_error || condition_value != 0;

            auto parse_constexpr_substatement =
                [&](bool discarded) -> collect::StmtResult {
                size_t statement_begin = current_raw_index();
                if (discarded && collect_session_.is_instantiating()) {

                    children.push_back(skip_discarded_if_substatement());
                    return collect_session_.collect_compound_stmt({}, loc);
                }
                size_t error_watermark =
                    collect_session_.file().errors().size();
                size_t warning_watermark =
                    collect_session_.file().warnings().size();
                size_t note_watermark =
                    collect_session_.file().notes().size();
                if (discarded) {
                    collect_session_.begin_speculative_parse();
                }
                size_t label_event_watermark = discarded
                    ? collect_session_.begin_discarded_statement_validation()
                    : 0;
                collect_session_.begin_control_flow_limited_statement();
                collect_session_.begin_scope();
                ParsedStmt statement = parse_statement();
                collect::StmtResult cleanups =
                    collect_session_.collect_scope_cleanups(loc);
                collect_session_.end_scope();
                collect_session_.end_control_flow_limited_statement();
                std::vector<collect::StmtResult> parts;
                parts.push_back(std::move(statement.sem));
                if (!cleanups.fragment.empty()) {
                    parts.push_back(std::move(cleanups));
                }
                collect::StmtResult result =
                    collect_session_.collect_compound_stmt(std::move(parts), loc);
                if (!discarded) {
                    children.push_back(statement.syntax);
                    return result;
                }

                const auto& collected_errors =
                    collect_session_.file().errors();
                const auto& collected_warnings =
                    collect_session_.file().warnings();
                const auto& collected_notes =
                    collect_session_.file().notes();
                std::vector<std::pair<SrcLoc, std::string>> new_errors(
                    collected_errors.begin() + error_watermark,
                    collected_errors.end());
                std::vector<std::pair<SrcLoc, std::string>> new_warnings(
                    collected_warnings.begin() + warning_watermark,
                    collected_warnings.end());
                std::vector<std::pair<SrcLoc, std::string>> new_notes(
                    collected_notes.begin() + note_watermark,
                    collected_notes.end());
                collect_session_.end_discarded_statement_validation();
                collect_session_.rollback_speculative_parse();
                for (auto& [diagnostic_loc, message] : new_errors) {
                    collect_session_.file().add_error(
                        std::move(message), diagnostic_loc);
                }
                for (auto& [diagnostic_loc, message] : new_warnings) {
                    collect_session_.file().add_warning(
                        std::move(message), diagnostic_loc);
                }
                for (auto& [diagnostic_loc, message] : new_notes) {
                    collect_session_.file().add_note(
                        std::move(message), diagnostic_loc);
                }
                collect_session_.merge_discarded_control_flow_events(
                    label_event_watermark);
                children.push_back(make_node(NodeKind::DiscardedStmt,
                                             statement_begin,
                                             last_consumed_raw_end(),
                                             {statement.syntax}));
                return collect_session_.collect_compound_stmt({}, loc);
            };

            std::optional<collect::StmtResult> selected_sem;
            if (take_then) {
                selected_sem = parse_constexpr_substatement(false);
            } else {
                (void)parse_constexpr_substatement(true);
            }
            if (match(TokenType::ELSE)) {
                if (take_then) {
                    (void)parse_constexpr_substatement(true);
                } else {
                    selected_sem = parse_constexpr_substatement(false);
                }
            }
            collect::StmtResult sem = selected_sem.has_value()
                ? std::move(*selected_sem)
                : collect_session_.collect_compound_stmt({}, loc);
            collect_session_.discard_lifetime_boundary(condition_boundary);
            sem = finish_if_scope(std::move(sem));
            sem.has_error = sem.has_error || condition_error;
            return {make_node(NodeKind::IfStmt, begin, last_consumed_raw_end(), children), sem};
        }

        collect_session_.bump_pattern_taint();
        collect_session_.begin_control_flow_limited_statement();
        ParsedStmt then_stmt = parse_statement();
        collect_session_.end_control_flow_limited_statement();
        children.push_back(then_stmt.syntax);
        std::optional<collect::StmtResult> else_sem;
        if (match(TokenType::ELSE)) {
            collect_session_.begin_control_flow_limited_statement();
            ParsedStmt else_stmt = parse_statement();
            collect_session_.end_control_flow_limited_statement();
            children.push_back(else_stmt.syntax);
            else_sem = std::move(else_stmt.sem);
        }
        collect::StmtResult sem = collect_session_.collect_if_stmt(
            std::move(cond.sem), std::move(then_stmt.sem), std::move(else_sem),
            loc, condition_boundary);
        sem = finish_if_scope(std::move(sem));
        return {make_node(NodeKind::IfStmt, begin, last_consumed_raw_end(), children), sem};
    }

    int64_t condition_value = 0;
    bool condition_is_constant =
        collect_session_.try_evaluate_integer_constant(cond.sem, condition_value);
    bool then_is_dead = condition_is_constant && condition_value == 0;
    bool else_is_dead = condition_is_constant && condition_value != 0;

    if (then_is_dead) collect_session_.enter_dead_branch();
    ParsedStmt then_stmt = parse_statement();
    if (then_is_dead) collect_session_.leave_dead_branch();
    children.push_back(then_stmt.syntax);
    std::optional<collect::StmtResult> else_sem;
    if (match(TokenType::ELSE)) {
        if (else_is_dead) collect_session_.enter_dead_branch();
        ParsedStmt else_stmt = parse_statement();
        if (else_is_dead) collect_session_.leave_dead_branch();
        children.push_back(else_stmt.syntax);
        else_sem = std::move(else_stmt.sem);
    }
    collect::StmtResult sem = collect_session_.collect_if_stmt(
        std::move(cond.sem), std::move(then_stmt.sem), std::move(else_sem),
        loc, condition_boundary);
    sem = finish_if_scope(std::move(sem));
    return {make_node(NodeKind::IfStmt, begin, last_consumed_raw_end(), children), sem};
}

bool Parser::cxx_condition_is_declaration() {
    StmtDeclDisambiguation disambiguation = classify_stmt_or_decl();
    bool declaration =
        disambiguation == StmtDeclDisambiguation::Declaration ||
        disambiguation == StmtDeclDisambiguation::Ambiguous;
    size_t type_name_tokens = 1;
    if (declaration && starts_cxx_qualified_name()) {
        if (std::optional<QualifiedTypeLookahead> qualified =
                peek_cxx_qualified_type()) {
            type_name_tokens = qualified->tokens_to_consume;
        }
    }

    if (declaration &&
        (peek(type_name_tokens).type == TokenType::LEFT_PAREN ||
         peek(type_name_tokens).type == TokenType::LEFT_BRACE)) {
        declaration = false;
    }
    return declaration;
}

Parser::ParsedExpr Parser::parse_cxx_condition_declaration() {
    ParsedDecl declaration = parse_declaration(false, true);
    ParsedExpr condition;
    condition.syntax = declaration.syntax;
    cir::EntityId entity = declaration.sem.entity;
    if (entity.valid() && collect_session_.file().valid(entity)) {
        const cir::Entity& record = collect_session_.file().entity(entity);
        std::string_view name = record.name.valid()
            ? collect_session_.file().name(record.name)
            : std::string_view{};
        condition.sem = collect_session_.make_entity_reference(
            entity, name, tree_.node(declaration.syntax).loc);
        condition.sem.fragment = collect_session_.chain(
            std::move(declaration.sem.fragment),
            std::move(condition.sem.fragment),
            tree_.node(declaration.syntax).loc);
        condition.sem.has_error =
            condition.sem.has_error || declaration.sem.has_error;
    } else {
        condition.sem.has_error = true;
        condition.sem.type = collect_session_.file().unknown_type();
    }
    return condition;
}

bool Parser::cxx_if_has_init_statement() const {

    int parens = 0;
    int brackets = 0;
    int braces = 0;
    for (size_t offset = 0;; ++offset) {
        const Token& token = peek(offset);
        switch (token.type) {
            case TokenType::Eof:
                return false;
            case TokenType::SEMICOLON:
                if (parens == 0 && brackets == 0 && braces == 0) {
                    return true;
                }
                break;
            case TokenType::LEFT_PAREN: ++parens; break;
            case TokenType::RIGHT_PAREN:
                if (parens == 0) {
                    return false;
                }
                --parens;
                break;
            case TokenType::LEFT_BRACKET: ++brackets; break;
            case TokenType::RIGHT_BRACKET:
                if (brackets > 0) {
                    --brackets;
                }
                break;
            case TokenType::LEFT_BRACE: ++braces; break;
            case TokenType::RIGHT_BRACE:
                if (braces == 0) {
                    return false;
                }
                --braces;
                break;
            default: break;
        }
    }
}

NodeId Parser::skip_discarded_if_substatement() {
    size_t begin = current_raw_index();
    skip_discarded_statement_tokens();
    return make_node(NodeKind::DiscardedStmt, begin, last_consumed_raw_end());
}

void Parser::skip_discarded_parenthesized_tokens() {
    if (!check(TokenType::LEFT_PAREN)) {
        return;
    }
    consume();
    int depth = 1;
    while (!at_end() && depth > 0) {
        TokenType inner = current().type;
        consume();
        if (inner == TokenType::LEFT_PAREN) ++depth;
        if (inner == TokenType::RIGHT_PAREN) --depth;
    }
}

void Parser::skip_discarded_statement_tokens() {

    if (at_end()) {
        return;
    }
    switch (current().type) {
        case TokenType::LEFT_BRACE: {
            consume();
            int depth = 1;
            while (!at_end() && depth > 0) {
                TokenType inner = current().type;
                consume();
                if (inner == TokenType::LEFT_BRACE) ++depth;
                if (inner == TokenType::RIGHT_BRACE) --depth;
            }
            return;
        }
        case TokenType::IF: {
            consume();
            if (check(TokenType::CONSTEXPR_KW)) {
                consume();
            }
            skip_discarded_parenthesized_tokens();
            skip_discarded_statement_tokens();
            if (check(TokenType::ELSE)) {
                consume();
                skip_discarded_statement_tokens();
            }
            return;
        }
        case TokenType::WHILE:
        case TokenType::SWITCH:
        case TokenType::FOR: {
            consume();
            skip_discarded_parenthesized_tokens();
            skip_discarded_statement_tokens();
            return;
        }
        case TokenType::DO: {
            consume();
            skip_discarded_statement_tokens();
            if (check(TokenType::WHILE)) {
                consume();
                skip_discarded_parenthesized_tokens();
            }
            if (check(TokenType::SEMICOLON)) {
                consume();
            }
            return;
        }
        case TokenType::TRY_KW: {
            consume();
            skip_discarded_statement_tokens();
            while (check(TokenType::CATCH_KW)) {
                consume();
                skip_discarded_parenthesized_tokens();
                skip_discarded_statement_tokens();
            }
            return;
        }
        default:
            break;
    }
    if (is_identifier_token(current().type) && peek(1).type == TokenType::COLON) {
        consume();
        consume();
        skip_discarded_statement_tokens();
        return;
    }
    int parens = 0;
    int brackets = 0;
    int braces = 0;
    while (!at_end()) {
        TokenType type = current().type;
        if (parens == 0 && brackets == 0 && braces == 0) {
            if (type == TokenType::SEMICOLON) {
                consume();
                return;
            }
            if (type == TokenType::RIGHT_BRACE || type == TokenType::RIGHT_PAREN ||
                type == TokenType::RIGHT_BRACKET || type == TokenType::ELSE) {

                return;
            }
        }
        if (type == TokenType::LEFT_PAREN) ++parens;
        if (type == TokenType::RIGHT_PAREN) --parens;
        if (type == TokenType::LEFT_BRACKET) ++brackets;
        if (type == TokenType::RIGHT_BRACKET) --brackets;
        if (type == TokenType::LEFT_BRACE) ++braces;
        if (type == TokenType::RIGHT_BRACE) --braces;
        consume();
    }
}

Parser::ParsedStmt Parser::parse_while_statement() {
    size_t begin = current_raw_index();
    SrcLoc loc = current().loc;
    consume();
    std::vector<NodeId> children;
    collect::WhileControl control = collect_session_.begin_while(loc);
    ParsedExpr cond;
    collect::Session::LifetimeBoundary condition_boundary =
        collect_session_.begin_lifetime_boundary();
    if (match(TokenType::LEFT_PAREN)) {
        bool condition_is_declaration =
            lang_opts_.is_cxx_mode() && cxx_condition_is_declaration();
        if (condition_is_declaration) {
            collect_session_.begin_scope();
            control.has_condition_scope = true;
            cond = parse_cxx_condition_declaration();
        } else {
            cond = parse_expression();
        }
        children.push_back(cond.syntax);
        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error, "expected ')' after while condition", current_loc());
        }
    } else {
        diagnose(DiagnosticLevel::Error, "expected '(' after while", current_loc());
    }
    collect_session_.begin_while_body(control, cond.sem, condition_boundary);
    ParsedStmt body = parse_statement();
    children.push_back(body.syntax);
    collect::StmtResult sem = collect_session_.finish_while(control, body.sem);
    return {make_node(NodeKind::WhileStmt, begin, last_consumed_raw_end(), children), sem};
}

Parser::ParsedStmt Parser::parse_for_statement() {
    size_t begin = current_raw_index();
    SrcLoc loc = current().loc;
    consume();
    std::vector<NodeId> children;
    collect::ForControl control = collect_session_.begin_for(loc);
    std::optional<collect::StmtResult> init_sem;
    std::optional<collect::ExprResult> condition_sem;
    std::optional<collect::ExprResult> step_sem;
    collect::Session::LifetimeBoundary condition_boundary;
    collect::Session::LifetimeBoundary step_boundary;
    if (!match(TokenType::LEFT_PAREN)) {
        diagnose(DiagnosticLevel::Error, "expected '(' after for", current_loc());
    } else {
        ForControlScan scan = scan_for_control();
        if (lang_opts_.is_cxx_mode() && scan.is_range) {
            return parse_range_for_statement(begin, loc, control,
                                             scan.has_init_statement);
        }
        if (check(TokenType::SEMICOLON)) {
            consume();
        } else {
            StmtDeclDisambiguation disambiguation = classify_stmt_or_decl();
            if (disambiguation == StmtDeclDisambiguation::Declaration ||
                disambiguation == StmtDeclDisambiguation::Ambiguous) {
                ParsedDecl init_decl = parse_declaration(false);
                children.push_back(init_decl.syntax);
                init_sem = collect_session_.collect_decl_stmt(std::move(init_decl.sem),
                                                              tree_.node(init_decl.syntax).loc);
            } else {
                collect::Session::LifetimeBoundary init_boundary =
                    collect_session_.begin_lifetime_boundary();
                ParsedExpr init = parse_expression();
                children.push_back(init.syntax);
                init_sem = collect_session_.collect_expr_stmt(
                    std::move(init.sem), tree_.node(init.syntax).loc,
                    &init_boundary);
                if (!match(TokenType::SEMICOLON)) {
                    diagnose(DiagnosticLevel::Error, "expected ';' after for initializer", current_loc());
                    skip_until_statement_boundary();
                }
            }
        }

        if (!check(TokenType::SEMICOLON) && !check(TokenType::RIGHT_PAREN)) {
            condition_boundary = collect_session_.begin_lifetime_boundary();
            ParsedExpr condition = parse_expression();
            children.push_back(condition.syntax);
            condition_sem = std::move(condition.sem);
            collect_session_.close_lifetime_boundary_without_cleanup(
                condition_boundary);
        }
        if (!match(TokenType::SEMICOLON)) {
            diagnose(DiagnosticLevel::Error, "expected ';' after for condition", current_loc());
        }

        if (!at_end() && !check(TokenType::RIGHT_PAREN)) {
            step_boundary = collect_session_.begin_lifetime_boundary();
            ParsedExpr step = parse_expression();
            children.push_back(step.syntax);
            step_sem = std::move(step.sem);
            collect_session_.close_lifetime_boundary_without_cleanup(
                step_boundary);
        }
        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error, "expected ')' after for control", current_loc());
        }
    }
    collect_session_.begin_for_body(control,
                                    std::move(init_sem),
                                    std::move(condition_sem),
                                    std::move(step_sem),
                                    condition_boundary,
                                    step_boundary);
    ParsedStmt body = parse_statement();
    children.push_back(body.syntax);
    collect::StmtResult sem = collect_session_.finish_for(control, body.sem);
    return {make_node(NodeKind::ForStmt, begin, last_consumed_raw_end(), children), sem};
}

Parser::ForControlScan Parser::scan_for_control() const {
    ForControlScan result;
    int paren_depth = 0;
    int bracket_depth = 0;
    int brace_depth = 0;
    int conditional_depth = 0;
    size_t top_level_semicolons = 0;
    for (size_t offset = 0; offset < 4096; ++offset) {
        TokenType type = peek(offset).type;
        if (type == TokenType::Eof) {
            break;
        }
        bool top = paren_depth == 0 && bracket_depth == 0 &&
                   brace_depth == 0;
        if (top) {
            if (type == TokenType::QUESTION) {
                ++conditional_depth;
                continue;
            }
            if (type == TokenType::COLON) {
                if (conditional_depth > 0) {
                    --conditional_depth;
                } else {
                    result.is_range = true;
                    result.has_init_statement = top_level_semicolons != 0;
                    return result;
                }
                continue;
            }
            if (type == TokenType::SEMICOLON) {
                ++top_level_semicolons;
                continue;
            }
            if (type == TokenType::RIGHT_PAREN) {
                return result;
            }
        }
        switch (type) {
            case TokenType::LEFT_PAREN: ++paren_depth; break;
            case TokenType::RIGHT_PAREN:
                if (paren_depth > 0) --paren_depth;
                break;
            case TokenType::LEFT_BRACKET: ++bracket_depth; break;
            case TokenType::RIGHT_BRACKET:
                if (bracket_depth > 0) --bracket_depth;
                break;
            case TokenType::LEFT_BRACE: ++brace_depth; break;
            case TokenType::RIGHT_BRACE:
                if (brace_depth > 0) --brace_depth;
                break;
            default: break;
        }
    }
    return result;
}

Parser::ParsedStmt Parser::parse_range_for_statement(
    size_t begin,
    SrcLoc loc,
    collect::ForControl control,
    bool has_init_statement) {
    std::vector<NodeId> children;
    std::optional<collect::StmtResult> init_statement;
    if (has_init_statement) {
        if (!lang_opts_.is_cxx20_or_later()) {
            diagnose(DiagnosticLevel::Error,
                     "range-for init-statements require C++20",
                     loc);
        }
        if (check(TokenType::USING)) {
            if (!lang_opts_.is_cxx26_or_later()) {
                diagnose(DiagnosticLevel::Error,
                         "alias declarations in range-for init-statements "
                         "require C++26",
                         current_loc());
            }
            ParsedDecl declaration = parse_cxx_using_declaration();
            children.push_back(declaration.syntax);
            init_statement = collect_session_.collect_decl_stmt(
                std::move(declaration.sem),
                tree_.node(declaration.syntax).loc);
        } else if (match(TokenType::SEMICOLON)) {
            init_statement = collect_session_.collect_compound_stmt({}, loc);
        } else {
            StmtDeclDisambiguation disambiguation = classify_stmt_or_decl();
            if (disambiguation == StmtDeclDisambiguation::Declaration ||
                disambiguation == StmtDeclDisambiguation::Ambiguous) {
                ParsedDecl declaration = parse_declaration(false);
                children.push_back(declaration.syntax);
                init_statement = collect_session_.collect_decl_stmt(
                    std::move(declaration.sem),
                    tree_.node(declaration.syntax).loc);
            } else {
                collect::Session::LifetimeBoundary boundary =
                    collect_session_.begin_lifetime_boundary();
                ParsedExpr expression = parse_expression();
                children.push_back(expression.syntax);
                init_statement = collect_session_.collect_expr_stmt(
                    std::move(expression.sem),
                    tree_.node(expression.syntax).loc,
                    &boundary);
                if (!match(TokenType::SEMICOLON)) {
                    diagnose(DiagnosticLevel::Error,
                             "expected ';' after range-for init-statement",
                             current_loc());
                }
            }
        }
    }

    RangeDeclarationRecipe declaration =
        parse_range_declaration(RangeDeclarationContext::Ordinary);
    children.push_back(declaration.syntax);
    if (!match(TokenType::COLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ':' in range-based for statement",
                 current_loc());
        declaration.has_error = true;
    }

    collect::Session::LifetimeBoundary initializer_boundary =
        collect_session_.begin_lifetime_boundary();
    ParsedExpr initializer = check(TokenType::LEFT_BRACE)
        ? parse_init_list_expression()
        : parse_expression();
    children.push_back(initializer.syntax);
    if (!match(TokenType::RIGHT_PAREN)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ')' after range-based for initializer",
                 current_loc());
    }

    if (initializer.sem.category == collect::ValueCategory::InitList) {
        initializer.sem.type = deduce_auto_copy_list_type(
            initializer.sem, loc);
        initializer.sem.has_error = initializer.sem.has_error ||
                                    !initializer.sem.type.valid();
    }

    const size_t hidden_index = collect_session_.file().entity_ids().size();
    const std::string range_name =
        ".range.for.range." + std::to_string(hidden_index);
    cir::TypeId range_pattern = collect_session_.reference_type(
        collect_session_.type_ref(
            collect_session_.auto_type(cir::AutoTypeFlavor::Cxx)),
        cir::ReferenceKind::RValue);
    cir::TypeId range_type;
    if (initializer.sem.has_error) {
        range_type = collect_session_.file().unknown_type();
    } else if (initializer.sem.category == collect::ValueCategory::InitList) {

        range_type = collect_session_.replace_auto_type(
            range_pattern,
            collect_session_.type_ref(initializer.sem.type),
            loc);
    } else {
        range_type = collect_session_.deduce_auto_type(
            range_pattern, initializer.sem, loc);
    }
    collect::DeclFlags hidden_flags;
    hidden_flags.suppress_name_binding = true;
    collect::DeclResult range = collect_session_.declare_local_variable(
        range_name, range_type, std::nullopt, loc, hidden_flags, true);
    range = collect_session_.finish_variable_declaration(
        std::move(range),
        range_type,
        std::move(initializer.sem),
        loc,
        hidden_flags,
        range_name,
        collect::ConstructorInitializationKind::Copy);
    cir::Fragment initializer_cleanup = lang_opts_.is_cxx26_or_later()
        ? collect_session_.extend_lifetime_boundary_to_scope(
              initializer_boundary, loc)
        : collect_session_.finish_lifetime_boundary(
              initializer_boundary, loc);
    range.fragment = collect_session_.chain(
        std::move(range.fragment),
        std::move(initializer_cleanup),
        loc);

    const cir::File& file = collect_session_.file();
    collect::DeclResult begin_variable;
    collect::DeclResult end_variable;
    collect::ExprResult condition;
    collect::ExprResult step;
    collect::ExprResult element;
    auto range_reference = [&]() {
        return collect_session_.make_entity_reference(
            range.entity, range_name, loc);
    };
    collect::RangeEndpointPlan endpoint_plan =
        collect_session_.plan_range_endpoints(
            range_reference(),
            /*allow_array=*/true,
            /*diagnose_missing=*/true,
            loc);
    bool endpoint_error = endpoint_plan.has_error ||
        endpoint_plan.kind == collect::RangeEndpointKind::Invalid;
    if (!endpoint_error) {
        const std::string begin_name =
            ".range.for.begin." + std::to_string(hidden_index);
        const std::string end_name =
            ".range.for.end." + std::to_string(hidden_index);
        auto endpoint_type = [&](const collect::ExprResult& initializer,
                                 std::string_view dependent_name) {
            if (endpoint_plan.kind == collect::RangeEndpointKind::Array) {
                return collect_session_.pointer_type(
                    endpoint_plan.array_element);
            }
            cir::TypeId type = collect_session_.deduce_auto_type(
                collect_session_.auto_type(cir::AutoTypeFlavor::Cxx),
                initializer,
                loc);
            if (!type.valid() &&
                endpoint_plan.kind == collect::RangeEndpointKind::Dependent) {
                type = collect_session_.dependent_type(dependent_name);
            }
            return type;
        };

        collect::Session::LifetimeBoundary begin_boundary =
            collect_session_.begin_lifetime_boundary();
        collect::ExprResult begin_initializer =
            collect_session_.collect_range_endpoint(
                endpoint_plan, range_reference(), true, loc);
        cir::TypeId begin_type = endpoint_type(
            begin_initializer, ".range.begin.type");
        endpoint_error = begin_initializer.has_error || !begin_type.valid();
        if (!endpoint_error) {
            begin_variable = collect_session_.declare_local_variable(
                begin_name,
                begin_type,
                std::nullopt,
                loc,
                hidden_flags,
                true);
            begin_variable = collect_session_.finish_variable_declaration(
                std::move(begin_variable),
                begin_type,
                std::move(begin_initializer),
                loc,
                hidden_flags,
                begin_name,
                collect::ConstructorInitializationKind::Copy);
            begin_variable.fragment = collect_session_.chain(
                std::move(begin_variable.fragment),
                collect_session_.finish_lifetime_boundary(begin_boundary, loc),
                loc);
            endpoint_error = begin_variable.has_error;
        } else {
            collect_session_.discard_lifetime_boundary(begin_boundary);
        }

        if (!endpoint_error) {
            collect::Session::LifetimeBoundary end_boundary =
                collect_session_.begin_lifetime_boundary();
            collect::ExprResult end_initializer =
                collect_session_.collect_range_endpoint(
                    endpoint_plan, range_reference(), false, loc);
            cir::TypeId end_type = endpoint_type(
                end_initializer, ".range.end.type");
            endpoint_error = end_initializer.has_error || !end_type.valid();
            if (!endpoint_error) {
                end_variable = collect_session_.declare_local_variable(
                    end_name,
                    end_type,
                    std::nullopt,
                    loc,
                    hidden_flags,
                    true);
                end_variable = collect_session_.finish_variable_declaration(
                    std::move(end_variable),
                    end_type,
                    std::move(end_initializer),
                    loc,
                    hidden_flags,
                    end_name,
                    collect::ConstructorInitializationKind::Copy);
                end_variable.fragment = collect_session_.chain(
                    std::move(end_variable.fragment),
                    collect_session_.finish_lifetime_boundary(
                        end_boundary, loc),
                    loc);
                endpoint_error = end_variable.has_error;
            } else {
                collect_session_.discard_lifetime_boundary(end_boundary);
            }
        }

        if (!endpoint_error) {
            auto begin_reference = [&]() {
                return collect_session_.make_entity_reference(
                    begin_variable.entity, begin_name, loc);
            };
            condition = collect_session_.collect_binary_expr(
                BinaryOperator::NotEqual,
                begin_reference(),
                collect_session_.make_entity_reference(
                    end_variable.entity, end_name, loc),
                loc);
            step = collect_session_.collect_unary_expr(
                UnaryOperator::PrefixIncrement, begin_reference(), loc);
            element = collect_session_.collect_unary_expr(
                UnaryOperator::Dereference, begin_reference(), loc);
            endpoint_error = begin_variable.has_error ||
                             end_variable.has_error || condition.has_error ||
                             step.has_error || element.has_error;
        }
    }

    std::vector<collect::StmtResult> init_parts;
    if (init_statement.has_value()) {
        init_parts.push_back(std::move(*init_statement));
    }
    init_parts.push_back(collect_session_.collect_decl_stmt(
        std::move(range), loc));
    if (!endpoint_error) {
        init_parts.push_back(collect_session_.collect_decl_stmt(
            std::move(begin_variable), loc));
        init_parts.push_back(collect_session_.collect_decl_stmt(
            std::move(end_variable), loc));
    }
    collect::StmtResult synthesized_init =
        collect_session_.collect_compound_stmt(std::move(init_parts), loc);
    if (endpoint_error) {
        synthesized_init.has_error = true;
    }

    collect_session_.begin_for_body(
        control,
        std::move(synthesized_init),
        endpoint_error ? std::optional<collect::ExprResult>{}
                       : std::optional<collect::ExprResult>{std::move(condition)},
        endpoint_error ? std::optional<collect::ExprResult>{}
                       : std::optional<collect::ExprResult>{std::move(step)},
        {},
        {});

    collect_session_.begin_scope();
    collect::DeclResult loop_variable = endpoint_error
        ? collect::DeclResult{}
        : materialize_range_declaration(declaration, std::move(element));
    ParsedStmt body = parse_statement();
    children.push_back(body.syntax);
    std::vector<collect::StmtResult> body_parts;
    if (!endpoint_error) {
        body_parts.push_back(collect_session_.collect_decl_stmt(
            std::move(loop_variable), declaration.loc));
    }
    body_parts.push_back(std::move(body.sem));
    collect::StmtResult body_cleanups =
        collect_session_.collect_scope_cleanups(loc);
    if (!body_cleanups.fragment.empty()) {
        body_parts.push_back(std::move(body_cleanups));
    }
    collect_session_.end_scope();
    collect::StmtResult ranged_body =
        collect_session_.collect_compound_stmt(std::move(body_parts), loc);
    ranged_body.has_error = ranged_body.has_error || declaration.has_error ||
                            endpoint_error;
    collect::StmtResult sem = collect_session_.finish_for(control, ranged_body);
    return {make_node(NodeKind::RangeForStmt,
                      begin,
                      last_consumed_raw_end(),
                      children,
                      {},
                      sem.has_error ? NodeFlagHasError : NodeFlagNone),
            std::move(sem)};
}

Parser::RangeDeclarationRecipe Parser::parse_range_declaration(
    RangeDeclarationContext context) {
    size_t begin = current_raw_index();
    RangeDeclarationRecipe result;
    result.loc = current_loc();
    result.context = context;
    const bool ordinary = context == RangeDeclarationContext::Ordinary;

    DeclarationParser declaration_parser(*this);
    cir::TypeRef base = declaration_parser.parse_declaration(false, true);
    result.type_syntax = declaration_parser.type_syntax;
    result.flags.attrs = declaration_parser.leading_attrs;
    result.flags.is_constexpr = declaration_parser.is_constexpr;
    result.flags.is_consteval = declaration_parser.is_consteval;
    result.flags.is_constinit = declaration_parser.is_constinit;
    result.flags.is_inline = declaration_parser.is_inline;
    result.flags.is_thread_local = declaration_parser.is_thread_local;
    result.flags.is_extern =
        declaration_parser.storage_class == StorageClass::Extern;
    result.flags.is_static =
        declaration_parser.storage_class == StorageClass::Static;
    result.flags.is_auto_storage =
        declaration_parser.storage_class == StorageClass::Auto;
    result.flags.is_register =
        declaration_parser.storage_class == StorageClass::Register;
    result.flags.is_mutable = declaration_parser.is_mutable;
    result.flags.is_friend = declaration_parser.is_friend;
    result.flags.is_block_byref = declaration_parser.is_block_byref;

    bool invalid_specifier =
        declaration_parser.storage_class != StorageClass::None ||
        declaration_parser.is_consteval || declaration_parser.is_constinit ||
        declaration_parser.is_inline || declaration_parser.is_thread_local ||
        declaration_parser.is_mutable || declaration_parser.is_friend ||
        declaration_parser.is_block_byref;
    if (invalid_specifier) {
        diagnose(DiagnosticLevel::Error,
                 ordinary
                     ? "invalid declaration specifier in for-range-declaration"
                     : "invalid declaration specifier in expansion statement",
                 result.loc);
        result.has_error = true;
    }

    bool structured_syntax =
        check(TokenType::LEFT_BRACKET) ||
        ((check(TokenType::BITWISE_AND) ||
          check(TokenType::LOGICAL_AND)) &&
         peek(1).type == TokenType::LEFT_BRACKET);
    if (!structured_syntax) {
        result.declarator = declaration_parser.parse_declarator(base, false);
        result.flags.type_qualifiers = result.declarator.type_ref.qualifiers;
        result.flags.attrs.append(result.declarator.attrs);
        if (!result.declarator.has_name) {
            diagnose(DiagnosticLevel::Error,
                     ordinary
                         ? "for-range-declaration requires a name"
                         : "expansion statement declaration requires a name",
                     result.loc);
            result.has_error = true;
        }
        if (result.declarator.is_function ||
            result.declarator.has_unsupported_semantics ||
            result.declarator.qualified_context.valid()) {
            diagnose(DiagnosticLevel::Error,
                     ordinary
                         ? "invalid for-range-declaration"
                         : "invalid for-range-declaration in expansion statement",
                     result.declarator.loc);
            result.has_error = true;
        }
        result.syntax = make_node(NodeKind::VarDecl,
                                  begin,
                                  last_consumed_raw_end(),
                                  {result.type_syntax,
                                   result.declarator.syntax});
        return result;
    }

    result.is_structured = true;
    result.structured_pattern = base;
    if (!collect_session_.contains_auto_type(base.type,
                                             cir::AutoTypeFlavor::Cxx)) {
        diagnose(DiagnosticLevel::Error,
                 ordinary
                     ? "structured binding in for-range-declaration requires 'auto'"
                     : "structured binding in expansion statement requires 'auto'",
                 result.loc);
        result.has_error = true;
    }
    if (check(TokenType::BITWISE_AND) || check(TokenType::LOGICAL_AND)) {
        bool rvalue = check(TokenType::LOGICAL_AND);
        consume();
        result.structured_pattern = collect_session_.type_ref(
            collect_session_.reference_type(
                base,
                rvalue ? cir::ReferenceKind::RValue
                       : cir::ReferenceKind::LValue));
    }
    if (!match(TokenType::LEFT_BRACKET)) {
        diagnose(DiagnosticLevel::Error,
                 "expected '[' in structured binding declaration",
                 current_loc());
        result.has_error = true;
    }

    bool saw_pack = false;
    if (check(TokenType::RIGHT_BRACKET)) {
        diagnose(DiagnosticLevel::Error,
                 "structured binding declaration requires at least one name",
                 current_loc());
        result.has_error = true;
    }
    while (!at_end() && !check(TokenType::RIGHT_BRACKET)) {
        size_t name_begin = current_raw_index();
        bool is_pack = match(TokenType::ELLIPSIS);
        if (is_pack) {
            if (ordinary && !lang_opts_.is_cxx26_or_later()) {
                diagnose(DiagnosticLevel::Error,
                         "structured binding packs require C++26",
                         last_consumed_loc());
                result.has_error = true;
            }
            if (saw_pack) {
                diagnose(DiagnosticLevel::Error,
                         "structured binding declaration may contain only one pack",
                         last_consumed_loc());
                result.has_error = true;
            }
            saw_pack = true;
        }
        if (!is_identifier_token(current().type)) {
            diagnose(DiagnosticLevel::Error,
                     "expected identifier in structured binding declaration",
                     current_loc());
            result.has_error = true;
            while (!at_end() && !check(TokenType::COMMA) &&
                   !check(TokenType::RIGHT_BRACKET)) {
                consume();
            }
        } else {
            Token name = consume();
            collect::StructuredBindingNameInput input;
            input.name = name.value;
            input.loc = name.loc;
            input.is_pack = is_pack;
            ParsedAttributes attrs = try_parse_attributes();
            if (ordinary && !attrs.attrs.empty() &&
                !lang_opts_.is_cxx26_or_later()) {
                diagnose(DiagnosticLevel::Error,
                         "attributes on structured binding names require C++26",
                         name.loc);
                result.has_error = true;
            }
            input.attrs = std::move(attrs.attrs);
            result.structured_name_syntax.push_back(
                make_node(NodeKind::StructuredBindingName,
                          name_begin,
                          last_consumed_raw_end(),
                          std::move(attrs.syntax),
                          TextPayload{input.name}));
            result.structured_names.push_back(std::move(input));
        }
        if (!match(TokenType::COMMA)) {
            break;
        }
        if (check(TokenType::RIGHT_BRACKET)) {
            diagnose(DiagnosticLevel::Error,
                     "expected identifier after ',' in structured binding declaration",
                     current_loc());
            result.has_error = true;
        }
    }
    if (!match(TokenType::RIGHT_BRACKET)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ']' after structured binding names",
                 current_loc());
        result.has_error = true;
    }
    result.flags.type_qualifiers = result.structured_pattern.qualifiers;
    std::vector<NodeId> children{result.type_syntax};
    children.insert(children.end(),
                    result.structured_name_syntax.begin(),
                    result.structured_name_syntax.end());
    result.syntax = make_node(NodeKind::StructuredBindingDecl,
                              begin,
                              last_consumed_raw_end(),
                              std::move(children));
    return result;
}

collect::DeclResult Parser::materialize_range_declaration(
    const RangeDeclarationRecipe& declaration,
    collect::ExprResult initializer) {
    if (declaration.is_structured) {
        collect::StructuredBindingStart structured =
            collect_session_.begin_structured_binding(
                declaration.structured_names, declaration.loc);
        cir::TypeId type = declaration.structured_pattern.type;
        if (collect_session_.contains_auto_type(type)) {
            type = collect_session_.deduce_auto_type(
                type, initializer, declaration.loc);
        }
        if (!type.valid() &&
            (collect_session_.collecting_pattern() ||
             initializer.category == collect::ValueCategory::Dependent ||
             initializer.value_dependent)) {
            cir::TypeId dependent = collect_session_.dependent_type(
                ".expansion.element");
            type = collect_session_.replace_auto_type(
                declaration.structured_pattern.type,
                collect_session_.type_ref(dependent),
                declaration.loc);
            initializer.type = dependent;
            initializer.category = collect::ValueCategory::Dependent;
        }
        collect::DeclFlags flags = declaration.flags;
        flags.suppress_name_binding = true;
        flags.type_qualifiers = declaration.structured_pattern.qualifiers;
        collect::DeclResult backing =
            collect_session_.declare_local_variable(
                structured.backing_name,
                type,
                std::nullopt,
                declaration.loc,
                flags,
                true);
        backing = collect_session_.finish_variable_declaration(
            std::move(backing),
            type,
            std::move(initializer),
            declaration.loc,
            flags,
            structured.backing_name,
            collect::ConstructorInitializationKind::Copy);
        size_t pack_position = std::numeric_limits<size_t>::max();
        for (size_t i = 0; i < structured.names.size(); ++i) {
            if (structured.names[i].is_pack) {
                pack_position = i;
                break;
            }
        }
        collect::StructuredBindingTupleInput tuple =
            resolve_structured_binding_tuple(backing,
                                             structured.names.size(),
                                             pack_position,
                                             declaration.loc);
        backing = collect_session_.finish_structured_binding(
            std::move(structured),
            std::move(backing),
            declaration.loc,
            false,
            std::move(tuple));
        backing.has_error = backing.has_error || declaration.has_error;
        return backing;
    }

    cir::TypeId type = declaration.declarator.type;
    uint8_t deduced_qualifiers = cir::QualNone;
    bool has_decltype_auto = collect_session_.contains_auto_type(
        type, cir::AutoTypeFlavor::DecltypeAuto);
    if (has_decltype_auto) {
        if (initializer.category == collect::ValueCategory::InitList) {
            diagnose(DiagnosticLevel::Error,
                     declaration.context == RangeDeclarationContext::Ordinary
                         ? "cannot use 'decltype(auto)' with a range element"
                         : "cannot use 'decltype(auto)' with an expansion "
                           "initializer list element",
                     declaration.loc);
            collect::DeclResult error;
            error.has_error = true;
            return error;
        }
        cir::TypeRef deduced = collect_session_.resolve_decltype_expr_type(
            initializer,
            initializer.unparenthesized_id_or_member,
            declaration.loc);
        type = deduced.type;
        deduced_qualifiers = deduced.qualifiers;
    } else if (collect_session_.contains_auto_type(type)) {
        const cir::File& file = collect_session_.file();
        cir::TypeId resolved_pattern = file.resolved_type(type);
        bool plain_auto = file.valid(resolved_pattern) &&
            file.type(resolved_pattern).kind == cir::TypeKind::Auto;
        cir::TypeId resolved_initializer =
            file.resolved_type(initializer.type);
        if (plain_auto && file.valid(resolved_initializer) &&
            file.type(resolved_initializer).kind == cir::TypeKind::Array) {
            type = collect_session_.replace_auto_type(
                type,
                collect_session_.type_ref(collect_session_.pointer_type(
                    file.array_element_ref(resolved_initializer))),
                declaration.loc);
        } else if (plain_auto && file.valid(resolved_initializer) &&
                   file.type(resolved_initializer).kind ==
                       cir::TypeKind::Function) {
            type = collect_session_.replace_auto_type(
                type,
                collect_session_.type_ref(collect_session_.pointer_type(
                    collect_session_.type_ref(resolved_initializer))),
                declaration.loc);
        } else {
            type = collect_session_.deduce_auto_type(
                type, initializer, declaration.loc);
        }
    }
    if (!type.valid() &&
        (collect_session_.collecting_pattern() ||
         initializer.category == collect::ValueCategory::Dependent ||
         initializer.value_dependent)) {
        cir::TypeId dependent = collect_session_.dependent_type(
            ".expansion.element");
        type = collect_session_.replace_auto_type(
            declaration.declarator.type,
            collect_session_.type_ref(dependent),
            declaration.loc);
        initializer.type = dependent;
        initializer.category = collect::ValueCategory::Dependent;
    }
    if (!type.valid()) {
        diagnose(DiagnosticLevel::Error,
                 declaration.context == RangeDeclarationContext::Ordinary
                     ? "cannot deduce for-range-declaration type"
                     : "cannot deduce expansion statement declaration type",
                 declaration.loc);
        collect::DeclResult error;
        error.has_error = true;
        return error;
    }
    type = collect_session_.complete_initializer_type(
        type, initializer, declaration.loc);
    collect::DeclFlags flags = declaration.flags;
    flags.type_qualifiers = static_cast<uint8_t>(
        declaration.declarator.type_ref.qualifiers | deduced_qualifiers);
    flags.vla_bounds = declaration.declarator.vla_bounds;
    collect::DeclResult variable = collect_session_.declare_local_variable(
        declaration.declarator.name,
        type,
        std::nullopt,
        declaration.loc,
        flags,
        true);
    variable = collect_session_.finish_variable_declaration(
        std::move(variable),
        type,
        std::move(initializer),
        declaration.loc,
        flags,
        declaration.declarator.name,
        collect::ConstructorInitializationKind::Copy);
    variable.has_error = variable.has_error || declaration.has_error;
    return variable;
}

Parser::ParsedStmt Parser::parse_expansion_statement() {
    size_t begin = current_raw_index();
    SrcLoc loc = current_loc();
    consume();
    consume();
    bool has_error = false;
    if (!lang_opts_.is_cxx26_or_later()) {
        diagnose(DiagnosticLevel::Error,
                 "expansion statements require C++26",
                 loc);
        has_error = true;
    }

    std::vector<NodeId> children;
    collect_session_.begin_scope();
    std::optional<collect::StmtResult> init_statement;
    if (!match(TokenType::LEFT_PAREN)) {
        diagnose(DiagnosticLevel::Error,
                 "expected '(' after 'template for'",
                 current_loc());
        has_error = true;
    } else {

        bool has_init_statement = false;
        int paren_depth = 0;
        int bracket_depth = 0;
        int brace_depth = 0;
        for (size_t offset = 0; offset < 4096; ++offset) {
            TokenType type = peek(offset).type;
            if (type == TokenType::Eof) {
                break;
            }
            bool top = paren_depth == 0 && bracket_depth == 0 &&
                       brace_depth == 0;
            if (top && type == TokenType::SEMICOLON) {
                has_init_statement = true;
                break;
            }
            if (top && (type == TokenType::COLON ||
                        type == TokenType::RIGHT_PAREN)) {
                break;
            }
            switch (type) {
                case TokenType::LEFT_PAREN: ++paren_depth; break;
                case TokenType::RIGHT_PAREN:
                    if (paren_depth > 0) --paren_depth;
                    break;
                case TokenType::LEFT_BRACKET: ++bracket_depth; break;
                case TokenType::RIGHT_BRACKET:
                    if (bracket_depth > 0) --bracket_depth;
                    break;
                case TokenType::LEFT_BRACE: ++brace_depth; break;
                case TokenType::RIGHT_BRACE:
                    if (brace_depth > 0) --brace_depth;
                    break;
                default: break;
            }
        }
        if (has_init_statement) {
            if (match(TokenType::SEMICOLON)) {
                init_statement = collect_session_.collect_compound_stmt({}, loc);
            } else {
                StmtDeclDisambiguation disambiguation = classify_stmt_or_decl();
                if (disambiguation == StmtDeclDisambiguation::Declaration ||
                    disambiguation == StmtDeclDisambiguation::Ambiguous) {
                    ParsedDecl declaration = parse_declaration(false);
                    children.push_back(declaration.syntax);
                    init_statement = collect_session_.collect_decl_stmt(
                        std::move(declaration.sem),
                        tree_.node(declaration.syntax).loc);
                } else {
                    collect::Session::LifetimeBoundary boundary =
                        collect_session_.begin_lifetime_boundary();
                    ParsedExpr expression = parse_expression();
                    children.push_back(expression.syntax);
                    init_statement = collect_session_.collect_expr_stmt(
                        std::move(expression.sem),
                        tree_.node(expression.syntax).loc,
                        &boundary);
                    if (!match(TokenType::SEMICOLON)) {
                        diagnose(DiagnosticLevel::Error,
                                 "expected ';' after expansion init-statement",
                                 current_loc());
                        has_error = true;
                    }
                }
            }
        }
    }

    RangeDeclarationRecipe range_declaration =
        parse_range_declaration(RangeDeclarationContext::Expansion);
    children.push_back(range_declaration.syntax);
    has_error = has_error || range_declaration.has_error;
    if (!match(TokenType::COLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ':' in expansion statement",
                 current_loc());
        has_error = true;
    }

    ParsedExpr initializer = check(TokenType::LEFT_BRACE)
        ? parse_init_list_expression()
        : parse_expression();
    children.push_back(initializer.syntax);
    if (!match(TokenType::RIGHT_PAREN)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ')' after expansion statement initializer",
                 current_loc());
        has_error = true;
    }
    if (!check(TokenType::LEFT_BRACE)) {
        diagnose(DiagnosticLevel::Error,
                 "expansion statement requires a compound statement body",
                 current_loc());
        ParsedStmt recovery = parse_statement();
        children.push_back(recovery.syntax);
        recovery.sem.has_error = true;
        collect::StmtResult outer_cleanups =
            collect_session_.collect_scope_cleanups(loc);
        collect_session_.end_scope();
        std::vector<collect::StmtResult> sequence;
        if (init_statement.has_value()) {
            sequence.push_back(std::move(*init_statement));
        }
        sequence.push_back(std::move(recovery.sem));
        sequence.push_back(std::move(outer_cleanups));
        collect::StmtResult sem = collect_session_.collect_compound_stmt(
            std::move(sequence), loc);
        sem.has_error = true;
        return {make_node(NodeKind::ExpansionStmt,
                          begin,
                          last_consumed_raw_end(),
                          children,
                          {},
                          NodeFlagHasError),
                std::move(sem)};
    }

    std::vector<collect::ExprResult> elements;
    collect::DeclResult expansion_prefix;
    if (initializer.sem.category == collect::ValueCategory::InitList &&
        initializer.sem.init_list) {
        for (collect::InitElementInput& element :
             initializer.sem.init_list->elements) {
            if (!element.designators.empty()) {
                diagnose(DiagnosticLevel::Error,
                         "designators are not permitted in an expansion initializer",
                         element.loc);
                has_error = true;
            }
            elements.push_back(std::move(element.value));
        }
    } else {
        bool initializer_is_lvalue =
            initializer.sem.category == collect::ValueCategory::LValue;
        collect::ExprResult constant_iteration_source = initializer.sem;
        std::string range_name = ".expansion.range." +
            std::to_string(collect_session_.file().entity_ids().size());
        cir::TypeId range_pattern = collect_session_.reference_type(
            collect_session_.type_ref(
                collect_session_.auto_type(cir::AutoTypeFlavor::Cxx)),
            cir::ReferenceKind::RValue);
        cir::TypeId range_type = collect_session_.deduce_auto_type(
            range_pattern, initializer.sem, loc);
        collect::DeclFlags range_flags;
        range_flags.is_constexpr = range_declaration.flags.is_constexpr;
        range_flags.suppress_name_binding = true;
        collect::DeclResult range = collect_session_.declare_local_variable(
            range_name,
            range_type,
            std::nullopt,
            loc,
            range_flags,
            true);
        range = collect_session_.finish_variable_declaration(
            std::move(range),
            range_type,
            std::move(initializer.sem),
            loc,
            range_flags,
            range_name,
            collect::ConstructorInitializationKind::Copy);

        auto range_reference = [&]() {
            return collect_session_.make_entity_reference(
                range.entity, range_name, loc);
        };
        collect::RangeEndpointPlan endpoint_plan =
            collect_session_.plan_range_endpoints(
                range_reference(),
                /*allow_array=*/false,
                /*diagnose_missing=*/false,
                loc);
        bool range_iterable =
            endpoint_plan.kind == collect::RangeEndpointKind::Member ||
            endpoint_plan.kind ==
                collect::RangeEndpointKind::ArgumentDependent;

        if (range_iterable) {
            auto make_endpoint_call = [&](bool begin,
                                          bool constant_probe = false) {
                collect::ExprResult object = constant_probe
                    ? constant_iteration_source
                    : range_reference();
                return collect_session_.collect_range_endpoint(
                    endpoint_plan, std::move(object), begin, loc);
            };

            collect::ExprResult begin_call = make_endpoint_call(true);
            collect::ExprResult difference_left = make_endpoint_call(
                true, true);
            collect::ExprResult difference_right = make_endpoint_call(
                true, true);
            collect::ExprResult difference =
                collect_session_.collect_binary_expr(
                    BinaryOperator::Sub,
                    std::move(difference_left),
                    std::move(difference_right),
                    loc);
            cir::TypeId difference_type = difference.type;
            std::string begin_name = ".expansion.begin." +
                std::to_string(collect_session_.file().entity_ids().size());
            cir::TypeId begin_pattern =
                collect_session_.auto_type(cir::AutoTypeFlavor::Cxx);
            cir::TypeId begin_type = collect_session_.deduce_auto_type(
                begin_pattern, begin_call, loc);
            collect::DeclFlags begin_flags;
            begin_flags.is_constexpr = range_declaration.flags.is_constexpr;
            begin_flags.suppress_name_binding = true;
            collect::DeclResult begin_variable =
                collect_session_.declare_local_variable(
                    begin_name,
                    begin_type,
                    std::nullopt,
                    loc,
                    begin_flags,
                    true);
            begin_variable = collect_session_.finish_variable_declaration(
                std::move(begin_variable),
                begin_type,
                std::move(begin_call),
                loc,
                begin_flags,
                begin_name,
                collect::ConstructorInitializationKind::Copy);

            int64_t count = 0;
            bool found_end = false;
            bool iteration_has_error = difference.has_error ||
                                       !difference_type.valid();
            collect_session_.begin_speculative_parse();
            for (; !iteration_has_error && count <= 100000; ++count) {
                collect::ExprResult iterator = make_endpoint_call(true, true);
                if (count != 0) {
                    collect::ExprResult offset =
                        collect_session_.collect_cast_expr(
                            difference_type,
                            collect_session_.make_integer_literal(
                                count, std::to_string(count), loc),
                            loc);
                    iterator = collect_session_.collect_binary_expr(
                        BinaryOperator::Add,
                        std::move(iterator),
                        std::move(offset),
                        loc);
                }
                collect::ExprResult not_at_end =
                    collect_session_.collect_binary_expr(
                        BinaryOperator::NotEqual,
                        std::move(iterator),
                        make_endpoint_call(false, true),
                        loc);
                int64_t remains = 0;
                if (!collect_session_.try_evaluate_required_integer_constant(
                        not_at_end, remains, loc)) {
                    iteration_has_error = true;
                    break;
                }
                if (remains == 0) {
                    found_end = true;
                    break;
                }
            }
            collect_session_.rollback_speculative_parse();
            if (iteration_has_error || !found_end) {
                diagnose(DiagnosticLevel::Error,
                         iteration_has_error
                             ? "expansion statement range does not have a constant length"
                             : "expansion statement produces too many elements",
                         loc);
                has_error = true;
                count = 0;
            }
            elements.reserve(static_cast<size_t>(count));
            for (int64_t index = 0; index < count; ++index) {
                collect::ExprResult iterator =
                    collect_session_.collect_binary_expr(
                        BinaryOperator::Add,
                        collect_session_.make_entity_reference(
                            begin_variable.entity, begin_name, loc),
                        collect_session_.collect_cast_expr(
                            difference_type,
                            collect_session_.make_integer_literal(
                                index, std::to_string(index), loc),
                            loc),
                        loc);
                elements.push_back(collect_session_.collect_unary_expr(
                    UnaryOperator::Dereference,
                    std::move(iterator),
                    loc));
            }
            expansion_prefix = std::move(range);
            expansion_prefix.fragment = collect_session_.chain(
                std::move(expansion_prefix.fragment),
                std::move(begin_variable.fragment),
                loc);
            expansion_prefix.has_error = expansion_prefix.has_error ||
                                         begin_variable.has_error ||
                                         iteration_has_error;
        } else {

            collect::StructuredBindingNameInput pack;
            pack.name = ".expansion.elements." +
                std::to_string(collect_session_.file().entity_ids().size());
            pack.loc = loc;
            pack.is_pack = true;
            collect::StructuredBindingStart structured =
                collect_session_.begin_structured_binding({pack}, loc);
            collect::StructuredBindingTupleInput tuple =
                resolve_structured_binding_tuple(range, 1, 0, loc);
            expansion_prefix = collect_session_.finish_structured_binding(
                std::move(structured),
                std::move(range),
                loc,
                false,
                std::move(tuple));
            if (const cir::StructuredBindingFact* fact =
                    collect_session_.file().structured_binding_fact(
                        expansion_prefix.entity)) {
                elements.reserve(fact->projections.size());
                for (const cir::StructuredBindingProjectionFact& projection :
                     fact->projections) {
                    collect::ExprResult element =
                        collect_session_.structured_binding_expr_result(
                            projection.binding, pack.name, projection.loc);
                    if (!initializer_is_lvalue &&
                        element.category == collect::ValueCategory::LValue) {
                        element.category = collect::ValueCategory::XValue;
                    }
                    elements.push_back(std::move(element));
                }
            } else {
                has_error = true;
            }
        }
    }

    size_t body_cursor = cursor_;
    size_t body_last_consumed = last_consumed_raw_end_;
    size_t after_body_cursor = body_cursor;
    size_t after_body_last_consumed = body_last_consumed;
    cir::BlockId break_target =
        collect_session_.create_statement_target("expansion.end");
    std::vector<collect::StmtResult> expanded;
    NodeId body_syntax = InvalidNodeId;

    for (size_t index = 0; index < elements.size(); ++index) {
        cursor_ = body_cursor;
        last_consumed_raw_end_ = body_last_consumed;
        cir::BlockId continue_target =
            collect_session_.create_statement_target(
                "expansion.next." + std::to_string(index));
        collect_session_.begin_expansion_statement(continue_target,
                                                   break_target);
        collect_session_.begin_scope();
        collect::DeclResult declaration = materialize_range_declaration(
            range_declaration, std::move(elements[index]));
        collect_session_.begin_expansion_label_region();
        ParsedStmt body = parse_compound_statement();
        collect_session_.end_expansion_label_region();
        if (index == 0) {
            body_syntax = body.syntax;
            after_body_cursor = cursor_;
            after_body_last_consumed = last_consumed_raw_end_;
        }
        collect::StmtResult cleanups =
            collect_session_.collect_scope_cleanups(loc);
        collect_session_.end_scope();
        collect::Session::ExpansionControlSummary control_summary =
            collect_session_.end_expansion_statement();
        if (control_summary.has_break && body.sem.break_exits.empty()) {
            body.sem.break_exits.push_back(break_target);
        }
        if (control_summary.has_continue && body.sem.continue_exits.empty()) {
            body.sem.continue_exits.push_back(continue_target);
        }
        expanded.push_back(collect_session_.collect_expansion_element(
            std::move(declaration),
            std::move(body.sem),
            std::move(cleanups),
            continue_target,
            loc));
    }

    if (elements.empty()) {

        collect_session_.begin_speculative_parse();
        cir::BlockId continue_target =
            collect_session_.create_statement_target("expansion.empty.next");
        collect_session_.begin_expansion_statement(continue_target,
                                                   break_target);
        collect_session_.begin_scope();
        collect::ExprResult placeholder;
        placeholder.type = collect_session_.dependent_type(
            ".expansion.empty.element");
        placeholder.category = collect::ValueCategory::Dependent;
        (void)materialize_range_declaration(
            range_declaration, std::move(placeholder));
        collect_session_.begin_expansion_label_region();
        ParsedStmt body = parse_compound_statement();
        collect_session_.end_expansion_label_region();
        collect_session_.end_scope();
        (void)collect_session_.end_expansion_statement();
        collect_session_.rollback_speculative_parse();
        body_syntax = body.syntax;
        after_body_cursor = cursor_;
        after_body_last_consumed = last_consumed_raw_end_;
    }
    cursor_ = after_body_cursor;
    last_consumed_raw_end_ = after_body_last_consumed;
    if (body_syntax != InvalidNodeId) {
        children.push_back(body_syntax);
    }

    collect::StmtResult expansion =
        collect_session_.collect_expansion_sequence(
            std::move(expanded), break_target, loc);
    std::vector<collect::StmtResult> sequence;
    if (init_statement.has_value()) {
        sequence.push_back(std::move(*init_statement));
    }
    if (expansion_prefix.entity.valid() ||
        !expansion_prefix.fragment.empty() || expansion_prefix.has_error) {
        sequence.push_back(collect_session_.collect_decl_stmt(
            std::move(expansion_prefix), loc));
    }
    sequence.push_back(std::move(expansion));
    collect::StmtResult outer_cleanups =
        collect_session_.collect_scope_cleanups(loc);
    if (!outer_cleanups.fragment.empty()) {
        sequence.push_back(std::move(outer_cleanups));
    }
    collect_session_.end_scope();
    collect::StmtResult sem = collect_session_.collect_compound_stmt(
        std::move(sequence), loc);
    sem.has_error = sem.has_error || has_error;
    return {make_node(NodeKind::ExpansionStmt,
                      begin,
                      last_consumed_raw_end(),
                      children,
                      {},
                      sem.has_error ? NodeFlagHasError : NodeFlagNone),
            std::move(sem)};
}

Parser::ParsedStmt Parser::parse_do_while_statement() {
    size_t begin = current_raw_index();
    SrcLoc loc = current().loc;
    consume();
    std::vector<NodeId> children;
    collect::DoWhileControl control = collect_session_.begin_do_while(loc);
    ParsedStmt body = parse_statement();
    children.push_back(body.syntax);

    ParsedExpr condition;
    collect::Session::LifetimeBoundary condition_boundary;
    if (!match(TokenType::WHILE)) {
        diagnose(DiagnosticLevel::Error, "expected while after do body", current_loc());
    } else if (!match(TokenType::LEFT_PAREN)) {
        diagnose(DiagnosticLevel::Error, "expected '(' after do-while", current_loc());
    } else {
        condition_boundary = collect_session_.begin_lifetime_boundary();
        condition = parse_expression();
        children.push_back(condition.syntax);
        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error, "expected ')' after do-while condition", current_loc());
        }
    }
    if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error, "expected ';' after do-while statement", current_loc());
        skip_until_statement_boundary();
    }
    collect::StmtResult sem =
        collect_session_.finish_do_while(control, std::move(condition.sem),
                                         body.sem, condition_boundary);
    return {make_node(NodeKind::DoWhileStmt, begin, last_consumed_raw_end(), children), sem};
}

Parser::ParsedStmt Parser::parse_switch_statement() {
    size_t begin = current_raw_index();
    SrcLoc loc = current().loc;
    consume();
    std::vector<NodeId> children;
    ParsedExpr condition;
    collect::Session::LifetimeBoundary condition_boundary =
        collect_session_.begin_lifetime_boundary();
    if (!match(TokenType::LEFT_PAREN)) {
        diagnose(DiagnosticLevel::Error, "expected '(' after switch", current_loc());
    } else {
        condition = parse_expression();
        children.push_back(condition.syntax);
        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error, "expected ')' after switch condition", current_loc());
        }
    }

    collect::SwitchControl control =
        collect_session_.begin_switch(std::move(condition.sem), loc,
                                      condition_boundary);
    ParsedStmt body = parse_statement();
    children.push_back(body.syntax);
    collect::StmtResult sem = collect_session_.finish_switch(control, body.sem);
    return {make_node(NodeKind::SwitchStmt, begin, last_consumed_raw_end(), children), sem};
}

Parser::ParsedStmt Parser::parse_case_or_default_statement() {
    size_t begin = current_raw_index();
    SrcLoc loc = current().loc;
    std::vector<NodeId> children;
    std::vector<collect::SwitchLabelInput> labels;
    NodeKind node_kind = check(TokenType::DEFAULT) ? NodeKind::DefaultStmt : NodeKind::CaseStmt;

    while (check(TokenType::CASE) || check(TokenType::DEFAULT)) {
        if (check(TokenType::DEFAULT)) {
            size_t label_begin = current_raw_index();
            SrcLoc default_loc = current().loc;
            consume();
            if (!match(TokenType::COLON)) {
                diagnose(DiagnosticLevel::Error, "expected ':' after default label", current_loc());
            }
            children.push_back(make_node(NodeKind::DefaultStmt,
                                         label_begin,
                                         last_consumed_raw_end()));
            collect::SwitchLabelInput label;
            label.kind = collect::SwitchLabelKind::Default;
            label.loc = default_loc;
            labels.push_back(std::move(label));
            continue;
        }

        size_t label_begin = current_raw_index();
        SrcLoc case_loc = current().loc;
        consume();
        ParsedExpr value = parse_conditional_expression();
        std::vector<NodeId> label_children{value.syntax};
        collect::SwitchLabelInput label;
        label.kind = collect::SwitchLabelKind::Case;
        label.value = std::move(value.sem);
        label.loc = case_loc;
        if (match(TokenType::ELLIPSIS)) {
            ParsedExpr range_end = parse_conditional_expression();
            label_children.push_back(range_end.syntax);
            label.range_end = std::move(range_end.sem);
            label.has_range = true;
        }
        if (!match(TokenType::COLON)) {
            diagnose(DiagnosticLevel::Error, "expected ':' after case label", current_loc());
        }
        children.push_back(make_node(NodeKind::CaseStmt,
                                     label_begin,
                                     last_consumed_raw_end(),
                                     label_children));
        labels.push_back(std::move(label));
    }

    ParsedStmt child = parse_statement();
    children.push_back(child.syntax);
    collect::StmtResult sem =
        collect_session_.collect_case_stmt(std::move(labels), std::move(child.sem), loc);
    return {make_node(node_kind, begin, last_consumed_raw_end(), children), sem};
}

Parser::ParsedStmt Parser::parse_label_statement() {
    size_t begin = current_raw_index();
    NodeId label = parse_name_node(NodeKind::Name);
    std::string label_name = node_text(tree_.node(label));
    SrcLoc loc = tree_.node(label).loc;
    if (collect_session_.identifier_labels_forbidden()) {
        diagnose(DiagnosticLevel::Error,
                 "identifier labels are not permitted in an expansion statement",
                 loc);
    }
    if (!match(TokenType::COLON)) {
        diagnose(DiagnosticLevel::Error, "expected ':' after label", current_loc());
    }

    ParsedStmt child = check(TokenType::RIGHT_BRACE)
        ? ParsedStmt{make_node(NodeKind::ExprStmt, begin, last_consumed_raw_end(), {}),
                     collect_session_.collect_compound_stmt({}, loc)}
        : parse_statement();
    collect::StmtResult sem =
        collect_session_.collect_label_stmt(label_name, std::move(child.sem), loc);
    return {make_node(NodeKind::LabelStmt,
                      begin,
                      last_consumed_raw_end(),
                      {label, child.syntax}),
            sem};
}

Parser::ParsedStmt Parser::parse_local_label_declaration_statement() {
    size_t begin = current_raw_index();
    if (collect_session_.identifier_labels_forbidden()) {
        diagnose(DiagnosticLevel::Error,
                 "identifier labels are not permitted in an expansion statement",
                 current_loc());
    }
    SrcLoc loc = current().loc;
    consume();
    std::vector<NodeId> children;
    std::vector<std::string> names;
    do {
        if (!is_identifier_token(current().type)) {
            diagnose(DiagnosticLevel::Error, "expected identifier in __label__ declaration", current_loc());
            break;
        }
        NodeId name = parse_name_node(NodeKind::Name);
        children.push_back(name);
        names.push_back(node_text(tree_.node(name)));
    } while (match(TokenType::COMMA));

    if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error, "expected ';' after __label__ declaration", current_loc());
        skip_until_statement_boundary();
    }
    collect::StmtResult sem =
        collect_session_.declare_local_labels(std::move(names), loc);
    return {make_node(NodeKind::LocalLabelDeclStmt,
                      begin,
                      last_consumed_raw_end(),
                      children),
            sem};
}

Parser::ParsedStmt Parser::parse_goto_statement() {
    size_t begin = current_raw_index();
    SrcLoc loc = current().loc;
    consume();
    std::vector<NodeId> children;
    collect::StmtResult sem;
    if (match(TokenType::MULTIPLY)) {
        ParsedExpr target = parse_expression();
        children.push_back(target.syntax);
        if (!match(TokenType::SEMICOLON)) {
            diagnose(DiagnosticLevel::Error, "expected ';' after computed goto", current_loc());
            skip_until_statement_boundary();
        }
        sem = collect_session_.collect_computed_goto_stmt(std::move(target.sem), loc);
    } else {
        if (!is_identifier_token(current().type)) {
            diagnose(DiagnosticLevel::Error, "expected label name after goto", current_loc());
            skip_until_statement_boundary();
            collect::StmtResult error = collect_session_.collect_compound_stmt({}, loc);
            error.has_error = true;
            return {make_node(NodeKind::GotoStmt,
                              begin,
                              last_consumed_raw_end(),
                              children,
                              {},
                              NodeFlagHasError),
                    error};
        }
        NodeId label = parse_name_node(NodeKind::Name);
        std::string label_name = node_text(tree_.node(label));
        children.push_back(label);
        if (!match(TokenType::SEMICOLON)) {
            diagnose(DiagnosticLevel::Error, "expected ';' after goto statement", current_loc());
            skip_until_statement_boundary();
        }
        sem = collect_session_.collect_goto_stmt(label_name, loc);
    }
    return {make_node(NodeKind::GotoStmt, begin, last_consumed_raw_end(), children), sem};
}

Parser::ParsedAsmString Parser::parse_asm_string_literal(std::string_view context) {
    ParsedAsmString result;
    if (!check(TokenType::STRING_LITERAL)) {
        diagnose(DiagnosticLevel::Error,
                 "expected string literal in " + std::string(context),
                 current_loc());
        result.has_error = true;
        return result;
    }
    while (check(TokenType::STRING_LITERAL)) {
        size_t begin = current_raw_index();
        Token token = current();
        consume();
        result.text += token.value;
        StringLiteralPayload payload{token.literal_prefix, std::string(token.value), std::string(token.value)};
        result.syntax.push_back(make_node(NodeKind::StringLiteral,
                                          begin,
                                          last_consumed_raw_end(),
                                          {},
                                          std::move(payload)));
    }
    return result;
}

bool Parser::at_asm_section_colon(int pending_colons) const {
    return pending_colons > 0 || check(TokenType::COLON) ||
        check(TokenType::SCOPE_RESOLUTION);
}

bool Parser::match_asm_section_colon(int& pending_colons) {
    if (pending_colons > 0) {
        --pending_colons;
        return true;
    }
    if (match(TokenType::COLON)) {
        return true;
    }
    if (match(TokenType::SCOPE_RESOLUTION)) {

        pending_colons = 1;
        return true;
    }
    return false;
}

Parser::ParsedAsmOperandList Parser::parse_asm_operand_list(
    int& pending_colons) {
    ParsedAsmOperandList result;
    while (!at_end() &&
           !at_asm_section_colon(pending_colons) &&
           !check(TokenType::RIGHT_PAREN)) {
        result.any = true;
        size_t begin = current_raw_index();
        std::vector<NodeId> children;
        std::string symbolic_name;
        if (match(TokenType::LEFT_BRACKET)) {
            if (!is_identifier_token(current().type)) {
                diagnose(DiagnosticLevel::Error, "expected symbolic asm operand name", current_loc());
            } else {
                symbolic_name = current().value;
                children.push_back(parse_name_node(NodeKind::Name));
            }
            if (!match(TokenType::RIGHT_BRACKET)) {
                diagnose(DiagnosticLevel::Error, "expected ']' after asm operand name", current_loc());
            }
        }

        ParsedAsmString constraint = parse_asm_string_literal("asm operand");
        children.insert(children.end(), constraint.syntax.begin(), constraint.syntax.end());
        if (!match(TokenType::LEFT_PAREN)) {
            diagnose(DiagnosticLevel::Error, "expected '(' after asm operand constraint", current_loc());
            break;
        }
        ParsedExpr expr = parse_expression();
        children.push_back(expr.syntax);
        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error, "expected ')' after asm operand expression", current_loc());
        }
        result.syntax.push_back(make_node(NodeKind::AmbiguousSyntax,
                                          begin,
                                          last_consumed_raw_end(),
                                          children,
                                          TextPayload{"asm_operand"}));
        collect::AsmOperand operand;
        operand.symbolic_name = std::move(symbolic_name);
        operand.constraint = std::move(constraint.text);
        operand.expr = std::move(expr.sem);
        operand.loc = loc_for_index(begin);
        result.operands.push_back(std::move(operand));
        if (!match(TokenType::COMMA)) {
            break;
        }
    }
    return result;
}

std::vector<NodeId> Parser::parse_asm_clobber_list(
    std::vector<std::string>& clobbers,
    int& pending_colons) {
    std::vector<NodeId> children;
    while (!at_end() &&
           !at_asm_section_colon(pending_colons) &&
           !check(TokenType::RIGHT_PAREN)) {
        ParsedAsmString clobber = parse_asm_string_literal("asm clobber list");
        children.insert(children.end(), clobber.syntax.begin(), clobber.syntax.end());
        if (!clobber.text.empty()) {
            clobbers.push_back(std::move(clobber.text));
        }
        if (!match(TokenType::COMMA)) {
            break;
        }
    }
    return children;
}

std::vector<NodeId> Parser::parse_asm_goto_label_list(std::vector<std::string>& labels) {
    std::vector<NodeId> children;
    while (!at_end() && !check(TokenType::RIGHT_PAREN)) {
        if (!is_identifier_token(current().type)) {
            diagnose(DiagnosticLevel::Error, "expected label name in asm goto", current_loc());
            break;
        }
        labels.push_back(std::string(current().value));
        children.push_back(parse_name_node(NodeKind::Name));
        if (!match(TokenType::COMMA)) {
            break;
        }
    }
    return children;
}

Parser::ParsedStmt Parser::parse_asm_statement() {
    size_t begin = current_raw_index();
    SrcLoc loc = current().loc;
    consume();

    bool is_volatile = false;
    bool is_inline = false;
    bool is_goto = false;
    while (check(TokenType::VOLATILE) || check(TokenType::INLINE) || check(TokenType::GOTO)) {
        is_volatile = is_volatile || check(TokenType::VOLATILE);
        is_inline = is_inline || check(TokenType::INLINE);
        is_goto = is_goto || check(TokenType::GOTO);
        consume();
    }

    std::vector<NodeId> children;
    std::vector<collect::AsmOperand> outputs;
    std::vector<collect::AsmOperand> inputs;
    std::vector<std::string> clobbers;
    std::vector<std::string> goto_labels;
    bool has_error = false;
    std::string asm_string;

    if (!match(TokenType::LEFT_PAREN)) {
        diagnose(DiagnosticLevel::Error, "expected '(' after asm", current_loc());
        has_error = true;
    } else {
        ParsedAsmString parsed_string = parse_asm_string_literal("asm statement");
        asm_string = std::move(parsed_string.text);
        has_error = has_error || parsed_string.has_error;
        children.insert(children.end(), parsed_string.syntax.begin(), parsed_string.syntax.end());

        bool saw_label_section = false;
        int pending_colons = 0;
        if (match_asm_section_colon(pending_colons)) {
            ParsedAsmOperandList parsed_outputs =
                parse_asm_operand_list(pending_colons);
            outputs = std::move(parsed_outputs.operands);
            children.insert(children.end(), parsed_outputs.syntax.begin(), parsed_outputs.syntax.end());
            if (match_asm_section_colon(pending_colons)) {
                ParsedAsmOperandList parsed_inputs =
                    parse_asm_operand_list(pending_colons);
                children.insert(children.end(), parsed_inputs.syntax.begin(), parsed_inputs.syntax.end());
                inputs = std::move(parsed_inputs.operands);
                if (match_asm_section_colon(pending_colons)) {
                    std::vector<NodeId> clobber_nodes =
                        parse_asm_clobber_list(clobbers, pending_colons);
                    children.insert(children.end(), clobber_nodes.begin(), clobber_nodes.end());
                    if (match_asm_section_colon(pending_colons)) {
                        is_goto = true;
                        saw_label_section = true;
                        std::vector<NodeId> labels = parse_asm_goto_label_list(goto_labels);
                        children.insert(children.end(), labels.begin(), labels.end());
                    }
                }
            }
        }
        if (is_goto && !saw_label_section) {
            diagnose(DiagnosticLevel::Error,
                     "asm goto requires a goto-label section",
                     loc);
            has_error = true;
        }

        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error, "expected ')' after asm statement", current_loc());
            has_error = true;
        }
    }

    if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error, "expected ';' after asm statement", current_loc());
        skip_until_statement_boundary();
        has_error = true;
    }

    collect::StmtResult sem =
        collect_session_.collect_asm_stmt(std::move(asm_string),
                                          std::move(outputs),
                                          std::move(inputs),
                                          std::move(clobbers),
                                          std::move(goto_labels),
                                          is_volatile,
                                          is_inline,
                                          is_goto,
                                          loc);
    sem.has_error = sem.has_error || has_error;
    return {make_node(NodeKind::AsmStmt,
                      begin,
                      last_consumed_raw_end(),
                      children,
                      {},
                      has_error ? NodeFlagHasError : NodeFlagNone),
            sem};
}

Parser::ParsedStmt Parser::parse_expression_statement() {
    size_t begin = current_raw_index();
    std::vector<NodeId> children;
    std::optional<collect::ExprResult> expr_sem;

    collect::Session::FullExpressionWatermark full_expression =
        collect_session_.begin_full_expression();
    if (!check(TokenType::SEMICOLON)) {
        ParsedExpr expr = parse_expression();
        children.push_back(expr.syntax);
        expr_sem = expr.sem;
    }
    if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error, "expected ';' after expression", current_loc());
        skip_until_statement_boundary();
    }
    collect::StmtResult sem;
    if (expr_sem.has_value()) {
        sem = collect_session_.collect_expr_stmt(*expr_sem,
                                                 loc_for_index(begin),
                                                 &full_expression);
    } else {
        sem = collect_session_.collect_compound_stmt({}, loc_for_index(begin));
        collect_session_.discard_lifetime_boundary(full_expression);
    }
    return {make_node(NodeKind::ExprStmt, begin, last_consumed_raw_end(), children), sem};
}

bool Parser::parse_handler_sequence(collect::TryControl& control,
                                    std::vector<NodeId>& children) {
    bool saw_handler = false;
    while (check(TokenType::CATCH_KW)) {
        size_t catch_begin_index = current_raw_index();
        SrcLoc catch_loc = current().loc;
        consume();
        std::vector<NodeId> catch_children;
        if (!match(TokenType::LEFT_PAREN)) {
            diagnose(DiagnosticLevel::Error, "expected '(' after 'catch'",
                     current_loc());
        }
        collect_session_.enter_scope(collect::ScopeFlags::BlockScope);
        std::optional<cir::TypeRef> catch_type;
        std::string param_name;
        if (check(TokenType::ELLIPSIS)) {
            consume();
        } else {
            DeclarationParser catch_parser(*this);
            cir::TypeRef base = catch_parser.parse_declaration(false, true);
            ParsedDeclarator declarator =
                catch_parser.parse_declarator(base, true);
            catch_type = declarator.type_ref;
            if (declarator.has_name) {
                param_name = declarator.name;
            }
            if (catch_parser.type_syntax != InvalidNodeId) {
                catch_children.push_back(catch_parser.type_syntax);
            }
            if (declarator.syntax != InvalidNodeId) {
                catch_children.push_back(declarator.syntax);
            }
        }
        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ')' after exception declaration",
                     current_loc());
        }
        collect_session_.begin_catch_handler(control, catch_type, param_name,
                                             catch_loc);
        if (!check(TokenType::LEFT_BRACE)) {
            diagnose(DiagnosticLevel::Error,
                     "expected '{' after exception declaration",
                     current_loc());
        }
        ParsedStmt handler_body = parse_compound_statement();
        catch_children.push_back(handler_body.syntax);
        collect_session_.finish_catch_handler(control,
                                              std::move(handler_body.sem),
                                              catch_loc);
        collect_session_.leave_scope();
        children.push_back(make_node(NodeKind::CatchClause,
                                     catch_begin_index,
                                     last_consumed_raw_end(),
                                     catch_children));
        saw_handler = true;
    }
    return saw_handler;
}

Parser::ParsedStmt Parser::parse_try_statement() {

    size_t begin = current_raw_index();
    SrcLoc loc = current().loc;
    consume();
    collect::TryControl control = collect_session_.begin_try(loc);
    std::vector<NodeId> children;
    if (!check(TokenType::LEFT_BRACE)) {
        diagnose(DiagnosticLevel::Error, "expected '{' after 'try'",
                 current_loc());
    }
    ParsedStmt body = parse_compound_statement();
    children.push_back(body.syntax);
    collect_session_.finish_try_body(control, std::move(body.sem));

    bool saw_handler = parse_handler_sequence(control, children);
    if (!saw_handler) {
        diagnose(DiagnosticLevel::Error,
                 "expected at least one 'catch' handler after try block",
                 current_loc());
    }
    collect::StmtResult sem = collect_session_.finish_try(control, loc);
    return {make_node(NodeKind::TryStmt,
                      begin,
                      last_consumed_raw_end(),
                      children),
            std::move(sem)};
}

Parser::ParsedStmt Parser::parse_constructor_function_try() {

    size_t begin = current_raw_index();
    SrcLoc loc = current().loc;
    consume();
    collect::TryControl control = collect_session_.begin_try(
        loc, collect::TryRegionKind::ConstructorFunction);
    collect_session_.mark_pattern_unusable();

    std::vector<collect::Session::MemberInitializerInput> initializers;
    if (match(TokenType::COLON)) {
        parse_member_initializer_list(initializers);
    }
    collect::StmtResult initialization =
        collect_session_.collect_constructor_initializers(
            std::move(initializers), loc);

    std::vector<NodeId> children;
    if (!check(TokenType::LEFT_BRACE)) {
        diagnose(DiagnosticLevel::Error,
                 "expected constructor body in function try block",
                 current_loc());
    }
    ParsedStmt body = parse_compound_statement();
    children.push_back(body.syntax);
    body.sem.fragment = collect_session_.chain(
        std::move(initialization.fragment), std::move(body.sem.fragment), loc);
    body.sem.has_error = body.sem.has_error || initialization.has_error;
    collect_session_.finish_try_body(control, std::move(body.sem));

    bool saw_handler = parse_handler_sequence(control, children);
    if (!saw_handler) {
        diagnose(DiagnosticLevel::Error,
                 "expected at least one 'catch' handler after function try "
                 "block",
                 current_loc());
    }
    collect::StmtResult sem = collect_session_.finish_try(control, loc);
    return {make_node(NodeKind::TryStmt,
                      begin,
                      last_consumed_raw_end(),
                      children),
            std::move(sem)};
}

size_t Parser::skip_function_try_block_tokens() {
    if (!match(TokenType::TRY_KW)) {
        return last_consumed_raw_end();
    }
    if (match(TokenType::COLON)) {
        int depth = 0;
        TokenType previous = TokenType::COLON;
        while (!at_end()) {
            TokenType type = current().type;
            if (depth == 0 && type == TokenType::LEFT_BRACE &&
                !is_identifier_token(previous) &&
                previous != TokenType::GREATER_THAN) {
                break;
            }
            if (depth == 0 && (type == TokenType::SEMICOLON ||
                               type == TokenType::RIGHT_BRACE)) {
                break;
            }
            if (type == TokenType::LEFT_PAREN ||
                type == TokenType::LEFT_BRACE) {
                ++depth;
            } else if (type == TokenType::RIGHT_PAREN ||
                       type == TokenType::RIGHT_BRACE) {
                --depth;
            }
            previous = type;
            consume();
        }
    }
    if (check(TokenType::LEFT_BRACE)) {
        skip_balanced_until_semicolon_or_brace();
    }
    while (match(TokenType::CATCH_KW)) {
        if (match(TokenType::LEFT_PAREN)) {
            int depth = 1;
            while (!at_end() && depth > 0) {
                TokenType type = current().type;
                consume();
                if (type == TokenType::LEFT_PAREN) {
                    ++depth;
                } else if (type == TokenType::RIGHT_PAREN) {
                    --depth;
                }
            }
        }
        if (check(TokenType::LEFT_BRACE)) {
            skip_balanced_until_semicolon_or_brace();
        }
    }
    return last_consumed_raw_end();
}

} // namespace aburi::syntax
