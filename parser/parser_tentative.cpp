#include "parser.h"

#include "../perf_stats.h"

namespace aburi::syntax {

namespace {

void bump_parser_counter(PerfCounter counter) {
    if (auto* profiler = active_perf_profiler()) {
        profiler->add_counter(counter);
    }
}

} // namespace

Parser::TentativeParsingAction::TentativeParsingAction(Parser& parser,
                                                       TentativeMode mode)
    : parser_(parser), context_id_(parser_.begin_tentative_context(mode)) {}

Parser::TentativeParsingAction::~TentativeParsingAction() {
    revert();
}

void Parser::TentativeParsingAction::commit() {
    if (!active_) {
        return;
    }
    parser_.commit_tentative_context(context_id_);
    active_ = false;
}

void Parser::TentativeParsingAction::revert() {
    if (!active_) {
        return;
    }
    parser_.rollback_tentative_context(context_id_);
    active_ = false;
}

Parser::ParserCheckpoint Parser::capture_parser_checkpoint() const {
    bump_parser_counter(PerfCounter::ParserTentativeStateCaptures);
    return ParserCheckpoint{
        cursor_,
        last_consumed_raw_end_,
        pending_template_closes_,
        diagnostics_.size(),
        tree_.checkpoint(),
        constraint_concept_id_syntax_.size(),
        constraint_fold_operand_syntax_.size()
    };
}

void Parser::restore_parser_checkpoint(const ParserCheckpoint& checkpoint) {
    bump_parser_counter(PerfCounter::ParserTentativeStateRestores);
    cursor_ = checkpoint.cursor;
    last_consumed_raw_end_ = checkpoint.last_consumed_raw_end;
    pending_template_closes_ = checkpoint.pending_template_closes;
    diagnostics_.resize(checkpoint.diagnostics_size);
    tree_.rollback_to(checkpoint.tree_checkpoint);
    constraint_concept_id_syntax_.resize(
        checkpoint.constraint_concept_id_syntax_size);
    constraint_fold_operand_syntax_.resize(
        checkpoint.constraint_fold_operand_syntax_size);
}

bool Parser::declaration_attributes_terminate_template_head_constraint() {
    if (template_head_constraint_attribute_boundary_depth_ == 0 ||
        !check(TokenType::LEFT_BRACKET) ||
        peek(1).type != TokenType::LEFT_BRACKET) {
        return false;
    }

    RevertingTentativeParsingAction tentative(*this,
                                               TentativeMode::ParserOnly);
    const size_t diagnostic_watermark = diagnostics_.size();
    const size_t attribute_begin = current_raw_index();
    ParsedAttributes attributes = try_parse_standard_or_gnu_attributes();
    const bool parsed_attributes =
        current_raw_index() != attribute_begin &&
        !attributes.syntax.empty() &&
        diagnostics_.size() == diagnostic_watermark;
    if (!parsed_attributes) {
        return false;
    }

    return is_type_start(current().type) ||
           current().type == TokenType::OPERATOR_KW ||
           current().type == TokenType::BITWISE_NOT;
}

size_t Parser::begin_tentative_context(TentativeMode mode) {
    bump_parser_counter(PerfCounter::ParserTentativeBegins);
    bump_parser_counter(mode == TentativeMode::ParserOnly
                            ? PerfCounter::ParserTentativeParserOnlyBegins
                            : PerfCounter::ParserTentativeCollectBackedBegins);
    TentativeContextFrame frame;
    frame.id = next_tentative_context_id_++;
    if (next_tentative_context_id_ == 0) {
        next_tentative_context_id_ = 1;
    }
    frame.mode = mode;
    frame.parser_checkpoint = capture_parser_checkpoint();
    if (mode == TentativeMode::CollectBacked) {
        collect_session_.begin_speculative_parse();
    }
    tentative_context_stack_.push_back(std::move(frame));
    return tentative_context_stack_.back().id;
}

void Parser::commit_tentative_context(size_t context_id) {
    if (tentative_context_stack_.empty() ||
        tentative_context_stack_.back().id != context_id) {
        return;
    }
    bump_parser_counter(PerfCounter::ParserTentativeCommits);
    TentativeContextFrame frame = std::move(tentative_context_stack_.back());
    tentative_context_stack_.pop_back();
    if (frame.mode == TentativeMode::CollectBacked) {
        collect_session_.commit_speculative_parse();
    }
}

void Parser::rollback_tentative_context(size_t context_id) {
    if (tentative_context_stack_.empty() ||
        tentative_context_stack_.back().id != context_id) {
        return;
    }
    bump_parser_counter(PerfCounter::ParserTentativeRollbacks);
    TentativeContextFrame frame = std::move(tentative_context_stack_.back());
    tentative_context_stack_.pop_back();
    if (frame.mode == TentativeMode::CollectBacked) {
        collect_session_.rollback_speculative_parse();
    }
    restore_parser_checkpoint(frame.parser_checkpoint);
}

bool Parser::probe_declaration_statement_start() {
    if (is_attribute_start()) {
        RevertingTentativeParsingAction tentative(*this, TentativeMode::ParserOnly);
        (void)try_parse_attributes();
        return is_type_start(current().type) || is_attribute_start() ||
               (lang_opts_.is_cxx_mode() &&
                starts_type_constraint_placeholder());
    }
    if (lang_opts_.is_cxx_mode() &&
        starts_type_constraint_placeholder()) {
        return true;
    }

    uint32_t config_key = lang_opts_.is_cxx_mode() ? 1u : 0u;
    if (auto cached = annotation_store_.lookup_result(
            mark(),
            ParserAnnotationStore::ResultKind::DeclarationStatementStart,
            config_key,
            0,
            0)) {
        bump_parser_counter(PerfCounter::ParserAnnotationStoreHits);
        if (*cached != tentative_syntax_probe::Result::Inconclusive) {
            return *cached == tentative_syntax_probe::Result::Match;
        }
    } else {
        bump_parser_counter(PerfCounter::ParserAnnotationStoreMisses);
        tentative_syntax_probe::Result syntax_result =
            tentative_syntax_probe::probe_declaration_statement_start(current().type);
        annotation_store_.store_result(
            mark(),
            ParserAnnotationStore::ResultKind::DeclarationStatementStart,
            config_key,
            0,
            0,
            syntax_result);
        if (syntax_result != tentative_syntax_probe::Result::Inconclusive) {
            return syntax_result == tentative_syntax_probe::Result::Match;
        }
    }

    uint64_t lookup_generation = collect_session_.lookup_generation();
    uint64_t scope = collect_session_.current_scope();
    if (auto cached_semantic = annotation_store_.lookup_result(
            mark(),
            ParserAnnotationStore::ResultKind::DeclarationStatementStart,
            config_key,
            lookup_generation,
            scope)) {
        bump_parser_counter(PerfCounter::ParserAnnotationStoreHits);
        return *cached_semantic == tentative_syntax_probe::Result::Match;
    }
    bump_parser_counter(PerfCounter::ParserAnnotationStoreMisses);

    bool names_a_type;
    if (lang_opts_.is_cxx_mode() &&
        (check(TokenType::SCOPE_RESOLUTION) ||
         (is_identifier_token(current().type) &&
          peek(1).type == TokenType::SCOPE_RESOLUTION))) {

        names_a_type = peek_cxx_qualified_type().has_value();
    } else if (lang_opts_.is_cxx_mode() &&
               is_identifier_token(current().type) &&
               peek(1).type == TokenType::LESS_THAN &&
               template_id_precedes_scope(0)) {

        names_a_type = peek_cxx_qualified_type().has_value();
    } else if (lang_opts_.is_cxx_mode() &&
               is_identifier_token(current().type) &&
               peek(1).type == TokenType::LESS_THAN) {

        const collect::Session::TemplateInfo* info =
            collect_session_.template_info_for_name(current().value);
        names_a_type =
            info && (info->is_class_template || info->is_alias_template);
    } else if (is_deduced_class_template_declaration_start()) {

        names_a_type = true;
    } else {
        names_a_type = collect_session_.is_type_name(current().value);
    }
    tentative_syntax_probe::Result result = names_a_type
        ? tentative_syntax_probe::Result::Match
        : tentative_syntax_probe::Result::NoMatch;
    annotation_store_.store_result(
        mark(),
        ParserAnnotationStore::ResultKind::DeclarationStatementStart,
        config_key,
        lookup_generation,
        scope,
        result);
    return result == tentative_syntax_probe::Result::Match;
}

bool Parser::probe_expression_statement_start() {
    if (is_attribute_start()) {
        RevertingTentativeParsingAction tentative(*this, TentativeMode::ParserOnly);
        (void)try_parse_attributes();
        return check(TokenType::SEMICOLON);
    }

    uint32_t config_key = lang_opts_.is_cxx_mode() ? 1u : 0u;
    if (auto cached = annotation_store_.lookup_result(
            mark(),
            ParserAnnotationStore::ResultKind::ExpressionStatementStart,
            config_key,
            0,
            0)) {
        bump_parser_counter(PerfCounter::ParserAnnotationStoreHits);
        return *cached == tentative_syntax_probe::Result::Match;
    }
    bump_parser_counter(PerfCounter::ParserAnnotationStoreMisses);

    tentative_syntax_probe::Result result =
        tentative_syntax_probe::probe_expression_statement_start(current().type);
    annotation_store_.store_result(
        mark(),
        ParserAnnotationStore::ResultKind::ExpressionStatementStart,
        config_key,
        0,
        0,
        result);
    return result == tentative_syntax_probe::Result::Match;
}

Parser::StmtDeclDisambiguation Parser::classify_stmt_or_decl() {
    if (current().type == TokenType::IDENTIFIER && current().value == "__block") {

        return StmtDeclDisambiguation::Declaration;
    }
    if (lang_opts_.is_objc() && current().type == TokenType::IDENTIFIER &&
        (current().value == "__strong" || current().value == "__weak" ||
         current().value == "__unsafe_unretained" ||
         current().value == "__autoreleasing")) {

        return StmtDeclDisambiguation::Declaration;
    }
    if (current().type == TokenType::EXTENSION_KW) {

        size_t index = 1;
        while (peek(index).type == TokenType::EXTENSION_KW) {
            ++index;
        }
        if (peek(index).type == TokenType::LEFT_PAREN) {
            return StmtDeclDisambiguation::Expression;
        }
    }
    const bool can_parse_decl = probe_declaration_statement_start();
    const bool can_parse_expr = probe_expression_statement_start();
    if (can_parse_decl && can_parse_expr) {
        if (lang_opts_.is_cxx_mode() &&
            is_identifier_token(current().type)) {
            std::optional<QualifiedTypeLookahead> qualified_type;
            if (starts_cxx_qualified_name()) {
                qualified_type = peek_cxx_qualified_type();
            }

            if (peek(1).type == TokenType::LEFT_BRACE ||
                (qualified_type &&
                 peek(qualified_type->tokens_to_consume).type ==
                     TokenType::LEFT_BRACE)) {
                return StmtDeclDisambiguation::Expression;
            }
            if (peek(1).type == TokenType::LESS_THAN &&
                template_id_precedes_postfix(
                    0, TokenType::LEFT_BRACE)) {

                return StmtDeclDisambiguation::Expression;
            }

            size_t left_paren_offset = 0;
            if (peek(1).type == TokenType::LEFT_PAREN) {
                left_paren_offset = 1;
            } else if (qualified_type &&
                       peek(qualified_type->tokens_to_consume).type ==
                           TokenType::LEFT_PAREN) {
                left_paren_offset = qualified_type->tokens_to_consume;
            } else if (peek(1).type == TokenType::LESS_THAN) {
                int angle_depth = 0;
                for (size_t offset = 1; offset < 4096; ++offset) {
                    TokenType type = peek(offset).type;
                    if (type == TokenType::LESS_THAN) {
                        ++angle_depth;
                        continue;
                    }
                    if (type == TokenType::GREATER_THAN) {
                        --angle_depth;
                    } else if (type == TokenType::RIGHT_SHIFT) {
                        angle_depth -= 2;
                    } else if (type == TokenType::SEMICOLON ||
                               type == TokenType::Eof) {
                        break;
                    } else {
                        continue;
                    }
                    if (angle_depth == 0) {
                        if (peek(offset + 1).type ==
                            TokenType::LEFT_PAREN) {
                            left_paren_offset = offset + 1;
                        }
                        break;
                    }
                    if (angle_depth < 0) {
                        break;
                    }
                }
            }
            if (left_paren_offset != 0) {

                if (peek(left_paren_offset + 1).type ==
                        TokenType::MULTIPLY &&
                    peek(left_paren_offset + 2).type ==
                        TokenType::THIS_KW &&
                    peek(left_paren_offset + 3).type ==
                        TokenType::RIGHT_PAREN) {
                    return StmtDeclDisambiguation::Expression;
                }
                int paren_depth = 0;
                for (size_t offset = left_paren_offset;
                     offset < left_paren_offset + 4096;
                     ++offset) {
                    TokenType type = peek(offset).type;
                    if (type == TokenType::LEFT_PAREN) {
                        ++paren_depth;
                        continue;
                    }
                    if (type == TokenType::COMMA &&
                        paren_depth == 1) {

                        return StmtDeclDisambiguation::Expression;
                    }
                    if (type != TokenType::RIGHT_PAREN) {
                        if (type == TokenType::Eof) {
                            break;
                        }
                        continue;
                    }
                    --paren_depth;
                    if (paren_depth != 0) {
                        continue;
                    }
                    TokenType next = peek(offset + 1).type;
                    bool binary_expression_continuation =
                        get_prec(next) != PrecLevel::UNKNOWN &&
                        next != TokenType::ASSIGN &&
                        next != TokenType::COMMA;
                    if (offset == left_paren_offset + 1 ||
                        next == TokenType::DOT ||
                        next == TokenType::ARROW ||
                        next == TokenType::DOT_STAR ||
                        next == TokenType::ARROW_STAR ||
                        next == TokenType::INCREMENT ||
                        next == TokenType::DECREMENT ||
                        binary_expression_continuation) {

                        return StmtDeclDisambiguation::Expression;
                    }
                    break;
                }
            }
        }
        return lang_opts_.is_cxx_mode()
            ? StmtDeclDisambiguation::Declaration
            : StmtDeclDisambiguation::Declaration;
    }
    if (can_parse_decl) {
        return StmtDeclDisambiguation::Declaration;
    }
    if (can_parse_expr) {
        return StmtDeclDisambiguation::Expression;
    }
    return StmtDeclDisambiguation::Invalid;
}

} // namespace aburi::syntax
