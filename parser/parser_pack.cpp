#include "parser.h"

#include <algorithm>
#include <cstdint>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace aburi::syntax {

namespace {

TextPayload text_payload(std::string_view text) {
    return TextPayload{std::string(text)};
}

} // namespace

cir::TemplateValuePackReference Parser::retained_pack_reference(
    const collect::Session::ParameterPackIdentity& pack) {
    cir::TemplateValuePackReference reference;
    switch (pack.kind) {
        case collect::Session::ParameterPackKind::Function:
            reference.kind = cir::TemplateValuePackKind::Function;
            break;
        case collect::Session::ParameterPackKind::Type:
            reference.kind = cir::TemplateValuePackKind::Type;
            break;
        case collect::Session::ParameterPackKind::Value:
            reference.kind = cir::TemplateValuePackKind::Value;
            break;
        case collect::Session::ParameterPackKind::Template:
            reference.kind = cir::TemplateValuePackKind::Template;
            break;
    }
    reference.declaration = pack.declaration;
    reference.owner = pack.owner;
    reference.depth = pack.depth;
    reference.index = pack.index;
    reference.parameter_type = pack.parameter_type;
    if (!pack.name.empty()) {
        reference.name = collect_session_.file().intern_name(pack.name);
    }
    return reference;
}

bool Parser::expression_list_element_has_pack_ellipsis(
    TokenType first_terminator,
    TokenType second_terminator) const {
    int paren_depth = 0;
    int bracket_depth = 0;
    int brace_depth = 0;
    int angle_depth = 0;
    for (size_t offset = 0; true; ++offset) {
        TokenType type = peek(offset).type;
        if (type == TokenType::Eof) {
            return false;
        }
        if (paren_depth == 0 && bracket_depth == 0 && brace_depth == 0 &&
            (type == first_terminator || type == second_terminator)) {

            if (type != TokenType::COMMA || angle_depth == 0) {
                return false;
            }
        }
        if (type == TokenType::ELLIPSIS &&
            peek(offset + 1).type != TokenType::LEFT_BRACKET) {
            return true;
        }
        bool grouped =
            paren_depth > 0 || bracket_depth > 0 || brace_depth > 0;
        if (!grouped) {
            if (type == TokenType::LESS_THAN) {
                ++angle_depth;
            } else if (type == TokenType::GREATER_THAN &&
                       angle_depth > 0) {
                --angle_depth;
            } else if (type == TokenType::RIGHT_SHIFT &&
                       angle_depth > 0) {
                angle_depth = std::max(0, angle_depth - 2);
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
            default:
                break;
        }
    }
}

bool Parser::template_argument_has_pack_ellipsis() const {

    int paren_depth = 0;
    int bracket_depth = 0;
    int brace_depth = 0;
    int angle_depth = 0;
    for (size_t offset = 0; offset < 4096; ++offset) {
        TokenType type = peek(offset).type;
        if (type == TokenType::Eof || type == TokenType::SEMICOLON) {
            return false;
        }
        bool grouped =
            paren_depth > 0 || bracket_depth > 0 || brace_depth > 0;
        if (!grouped) {
            if (angle_depth == 0 &&
                (type == TokenType::COMMA ||
                 type == TokenType::GREATER_THAN ||
                 type == TokenType::RIGHT_SHIFT)) {
                return false;
            }
            if (angle_depth == 1 && type == TokenType::RIGHT_SHIFT) {

                return false;
            }
            if (angle_depth == 0 && type == TokenType::ELLIPSIS &&
                peek(offset + 1).type != TokenType::LEFT_BRACKET) {
                return true;
            }
            if (type == TokenType::LESS_THAN) {
                ++angle_depth;
            } else if (type == TokenType::GREATER_THAN) {
                --angle_depth;
            } else if (type == TokenType::RIGHT_SHIFT) {
                angle_depth -= 2;
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
            default:
                break;
        }
    }
    return false;
}

std::optional<Parser::PackExpansionPattern>
Parser::try_parse_pack_expansion_pattern(
    const std::function<void()>& parse_pattern,
    bool expect_trailing_ellipsis) {
    size_t replay_cursor = cursor_;
    size_t replay_last_consumed_raw_end = last_consumed_raw_end_;
    size_t syntax_begin = current_raw_index();
    size_t replay_end_cursor = cursor_;
    size_t after_ellipsis_cursor = cursor_;
    size_t after_ellipsis_last_consumed_raw_end = last_consumed_raw_end_;
    SrcLoc ellipsis_loc{};
    std::vector<collect::Session::ParameterPackIdentity> packs;
    {
        RevertingTentativeParsingAction tentative(*this);

        auto capture_scope =
            collect_session_.begin_parameter_pack_pattern_capture();
        parse_pattern();
        bool has_ellipsis = check(TokenType::ELLIPSIS);
        if (!expect_trailing_ellipsis) {

            replay_end_cursor = cursor_;
            after_ellipsis_cursor = cursor_;
            after_ellipsis_last_consumed_raw_end = last_consumed_raw_end_;
            ellipsis_loc = current().loc;
        } else if (has_ellipsis) {
            replay_end_cursor = cursor_;
            ellipsis_loc = current().loc;
            consume();
            after_ellipsis_cursor = cursor_;
            after_ellipsis_last_consumed_raw_end = last_consumed_raw_end_;
        }
        packs = collect_session_.finish_parameter_pack_pattern_capture(
            capture_scope);
        tentative.revert();
        if (expect_trailing_ellipsis && !has_ellipsis) {
            return std::nullopt;
        }
    }

    PackExpansionPattern pattern;
    pattern.syntax = make_node(NodeKind::AmbiguousSyntax,
                               syntax_begin,
                               after_ellipsis_last_consumed_raw_end,
                               {},
                               text_payload("pack-expansion"));
    pattern.packs = std::move(packs);
    pattern.replay_cursor = replay_cursor;
    pattern.replay_last_consumed_raw_end = replay_last_consumed_raw_end;
    pattern.replay_end_cursor = replay_end_cursor;
    pattern.after_ellipsis_cursor = after_ellipsis_cursor;
    pattern.after_ellipsis_last_consumed_raw_end =
        after_ellipsis_last_consumed_raw_end;
    pattern.ellipsis_loc = ellipsis_loc;
    return pattern;
}

std::optional<size_t> Parser::resolve_pack_expansion_element_count(
    const PackExpansionPattern& pattern,
    bool* dependent_out) {
    std::optional<size_t> element_count;
    bool dependent = false;
    bool length_mismatch = false;
    auto note_count = [&](size_t count) {
        if (element_count.has_value() && *element_count != count) {
            diagnose(DiagnosticLevel::Error,
                     "pack expansion contains packs with different lengths",
                     pattern.ellipsis_loc);
            length_mismatch = true;
        } else if (!element_count.has_value()) {
            element_count = count;
        }
    };
    for (const collect::Session::ParameterPackIdentity& pack : pattern.packs) {
        std::optional<size_t> count =
            collect_session_.parameter_pack_element_count(pack);
        if (!count.has_value()) {
            dependent = true;
            break;
        }
        note_count(*count);
    }
    if (dependent_out) {
        *dependent_out = dependent;
    }
    if (dependent) {
        return std::nullopt;
    }
    if (length_mismatch) {

        return size_t{0};
    }
    return element_count;
}

void Parser::replay_pack_expansion_elements(
    const PackExpansionPattern& pattern,
    size_t count,
    const std::function<void(size_t element_index)>& replay_element) {
    for (size_t i = 0; i < count; ++i) {
        cursor_ = pattern.replay_cursor;
        last_consumed_raw_end_ = pattern.replay_last_consumed_raw_end;
        auto replay_scope =
            collect_session_.begin_parameter_pack_element_replay(
                pattern.packs, i);

        auto capture_checkpoint =
            collect_session_.checkpoint_parameter_pack_pattern_capture();
        replay_element(i);
        collect_session_.restore_parameter_pack_pattern_capture(
            capture_checkpoint);
        collect_session_.finish_parameter_pack_element_replay(replay_scope);
        if (cursor_ != pattern.replay_end_cursor) {
            diagnose(DiagnosticLevel::Error,
                     "could not replay pack expansion pattern",
                     pattern.ellipsis_loc);
            cursor_ = pattern.replay_end_cursor;
        }
    }
    cursor_ = pattern.after_ellipsis_cursor;
    last_consumed_raw_end_ = pattern.after_ellipsis_last_consumed_raw_end;
}

void Parser::parse_pack_expansion_pattern_deferred(
    const std::function<void()>& parse_pattern) {

    auto capture_scope =
        collect_session_.begin_parameter_pack_pattern_capture();
    parse_pattern();
    (void)collect_session_.finish_parameter_pack_pattern_capture(
        capture_scope);
}

std::optional<Parser::PackExpansionPattern>
Parser::try_parse_expression_pack_expansion(TokenType terminator) {
    if (!expression_list_element_has_pack_ellipsis(terminator,
                                                   TokenType::COMMA)) {
        return std::nullopt;
    }

    return try_parse_pack_expansion_pattern(
        [&] { (void)parse_assignment_expression(); });
}

bool Parser::expand_expression_pack(
    const PackExpansionPattern& pattern,
    std::vector<collect::ExprResult>& elements) {
    auto append_dependent = [&](std::string_view name) {
        collect::ExprResult dependent;
        dependent.name = std::string(name);
        dependent.type = collect_session_.file().dependent_type(
            "function parameter pack expansion");
        dependent.category = collect::ValueCategory::Dependent;
        elements.push_back(std::move(dependent));
    };
    if (!pattern.has_pack_names()) {
        diagnose(DiagnosticLevel::Error,
                 "pack expansion pattern does not contain an unexpanded pack",
                 pattern.ellipsis_loc);
        collect::ExprResult error;
        error.has_error = true;
        error.type = collect_session_.file().dependent_type(
            "invalid function parameter pack expansion");
        error.category = collect::ValueCategory::Dependent;
        elements.push_back(std::move(error));
        cursor_ = pattern.after_ellipsis_cursor;
        last_consumed_raw_end_ = pattern.after_ellipsis_last_consumed_raw_end;
        return false;
    }

    bool dependent = false;
    std::optional<size_t> element_count =
        resolve_pack_expansion_element_count(pattern, &dependent);
    if (dependent) {

        cursor_ = pattern.replay_cursor;
        last_consumed_raw_end_ = pattern.replay_last_consumed_raw_end;
        auto capture_scope =
            collect_session_.begin_parameter_pack_pattern_capture();
        ParsedExpr retained = parse_assignment_expression();
        std::vector<collect::Session::ParameterPackIdentity> retained_packs =
            collect_session_.finish_parameter_pack_pattern_capture(
                capture_scope);
        if (cursor_ != pattern.replay_end_cursor) {
            diagnose(DiagnosticLevel::Error,
                     "could not retain pack expansion pattern",
                     pattern.ellipsis_loc);
            cursor_ = pattern.replay_end_cursor;
        }
        const auto& identities = retained_packs.empty()
            ? pattern.packs
            : retained_packs;
        retained.sem.pack_expansion_references.reserve(identities.size());
        for (const collect::Session::ParameterPackIdentity& pack :
             identities) {
            retained.sem.pack_expansion_references.push_back(
                retained_pack_reference(pack));
        }
        if (retained.sem.pack_expansion_references.empty()) {
            append_dependent(pattern.packs.front().name);
        } else {
            elements.push_back(std::move(retained.sem));
        }
        cursor_ = pattern.after_ellipsis_cursor;
        last_consumed_raw_end_ = pattern.after_ellipsis_last_consumed_raw_end;
        return true;
    }

    replay_pack_expansion_elements(
        pattern,
        element_count.value_or(0),
        [&](size_t) { elements.push_back(parse_assignment_expression().sem); });
    return false;
}

} // namespace aburi::syntax
