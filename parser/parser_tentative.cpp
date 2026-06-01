#include "parser.h"
#include "tentative_syntax_probe.h"
#include "../perf_stats.h"

#include <cstdlib>
#include <cstdint>
#include <cassert>
#include <iostream>

bool token_can_start_cast_operand(TokenType tok);

namespace {
struct ParserTentativeMetrics {
    uint64_t tentative_context_begins = 0;
    uint64_t tentative_context_commits = 0;
    uint64_t tentative_context_rollbacks = 0;
    uint64_t tentative_state_captures = 0;
    uint64_t tentative_state_restores = 0;
};

bool refactor_metrics_enabled() {
    static const bool enabled = []() {
        const char* env = std::getenv("ABURI_REFACTOR_METRICS");
        return env && env[0] != '\0' && env[0] != '0';
    }();
    return enabled;
}

ParserTentativeMetrics& parser_tentative_metrics() {
    static ParserTentativeMetrics metrics;
    return metrics;
}

void emit_parser_tentative_metrics_at_exit() {
    if (!refactor_metrics_enabled()) {
        return;
    }
    const auto& metrics = parser_tentative_metrics();
    std::cerr
        << "[refactor-metrics] parser.tentative "
        << "begins=" << metrics.tentative_context_begins
        << " commits=" << metrics.tentative_context_commits
        << " rollbacks=" << metrics.tentative_context_rollbacks
        << " captures=" << metrics.tentative_state_captures
        << " restores=" << metrics.tentative_state_restores
        << '\n';
}

struct ParserTentativeMetricsReporter {
    ~ParserTentativeMetricsReporter() {
        emit_parser_tentative_metrics_at_exit();
    }
};

ParserTentativeMetricsReporter g_parser_tentative_metrics_reporter;

class TokenStreamCheckpoint {
public:
    explicit TokenStreamCheckpoint(TokenMgnt& tok_mgnt)
        : tok_mgnt_(tok_mgnt),
          token_idx_(tok_mgnt.get_token_idx()),
          split_state_(tok_mgnt.get_split_token_state()) {}

    TokenStreamCheckpoint(const TokenStreamCheckpoint&) = delete;
    TokenStreamCheckpoint& operator=(const TokenStreamCheckpoint&) = delete;

    ~TokenStreamCheckpoint() {
        restore();
    }

    void restore() {
        if (!active_) {
            return;
        }
        tok_mgnt_.set_token_idx(token_idx_);
        tok_mgnt_.set_split_token_state(split_state_);
        active_ = false;
    }

private:
    TokenMgnt& tok_mgnt_;
    size_t token_idx_ = 0;
    TokenMgnt::SplitTokenState split_state_;
    bool active_ = true;
};

void bump_tentative_context_begins() {
    if (auto* profiler = active_perf_profiler()) {
        profiler->add_counter(PerfCounter::ParserTentativeBegins);
        return;
    }
    if (!refactor_metrics_enabled()) {
        return;
    }
    ++parser_tentative_metrics().tentative_context_begins;
}

void bump_tentative_context_mode_begin(Parser::TentativeMode mode) {
    auto* profiler = active_perf_profiler();
    if (!profiler) {
        return;
    }
    profiler->add_counter(
        mode == Parser::TentativeMode::ParserOnly
            ? PerfCounter::ParserTentativeParserOnlyBegins
            : PerfCounter::ParserTentativeCollectBackedBegins);
}

void bump_tentative_context_commits() {
    if (auto* profiler = active_perf_profiler()) {
        profiler->add_counter(PerfCounter::ParserTentativeCommits);
        return;
    }
    if (!refactor_metrics_enabled()) {
        return;
    }
    ++parser_tentative_metrics().tentative_context_commits;
}

void bump_tentative_context_rollbacks() {
    if (auto* profiler = active_perf_profiler()) {
        profiler->add_counter(PerfCounter::ParserTentativeRollbacks);
        return;
    }
    if (!refactor_metrics_enabled()) {
        return;
    }
    ++parser_tentative_metrics().tentative_context_rollbacks;
}

void bump_tentative_state_captures() {
    if (auto* profiler = active_perf_profiler()) {
        profiler->add_counter(PerfCounter::ParserTentativeStateCaptures);
        return;
    }
    if (!refactor_metrics_enabled()) {
        return;
    }
    ++parser_tentative_metrics().tentative_state_captures;
}

void bump_tentative_state_restores() {
    if (auto* profiler = active_perf_profiler()) {
        profiler->add_counter(PerfCounter::ParserTentativeStateRestores);
        return;
    }
    if (!refactor_metrics_enabled()) {
        return;
    }
    ++parser_tentative_metrics().tentative_state_restores;
}

void bump_annotation_cache_hit() {
    if (auto* profiler = active_perf_profiler()) {
        profiler->add_counter(PerfCounter::ParserAnnotationCacheHits);
    }
}

void bump_annotation_cache_miss() {
    if (auto* profiler = active_perf_profiler()) {
        profiler->add_counter(PerfCounter::ParserAnnotationCacheMisses);
    }
}

void bump_declarator_annotation_hit() {
    if (auto* profiler = active_perf_profiler();
        profiler && profiler->wants_full()) {
        profiler->add_counter(PerfCounter::ParserDeclaratorAnnotationHits);
    }
}

void bump_declarator_annotation_miss() {
    if (auto* profiler = active_perf_profiler();
        profiler && profiler->wants_full()) {
        profiler->add_counter(PerfCounter::ParserDeclaratorAnnotationMisses);
    }
}

void bump_declarator_annotation_publish() {
    if (auto* profiler = active_perf_profiler();
        profiler && profiler->wants_full()) {
        profiler->add_counter(PerfCounter::ParserDeclaratorAnnotationPublishes);
    }
}

void bump_declarator_paren_suffix_type_scope_reject() {
    if (auto* profiler = active_perf_profiler();
        profiler && profiler->wants_full()) {
        profiler->add_counter(
            PerfCounter::ParserDeclaratorParenSuffixTypeScopeRejects);
    }
}

void bump_declarator_paren_suffix_type_scope_fallback() {
    if (auto* profiler = active_perf_profiler();
        profiler && profiler->wants_full()) {
        profiler->add_counter(
            PerfCounter::ParserDeclaratorParenSuffixTypeScopeFallbacks);
    }
}
} // namespace

size_t Parser::begin_tentative_context(TentativeMode mode) {
    bump_tentative_context_begins();
    bump_tentative_context_mode_begin(mode);
    TentativeContextFrame frame;
    frame.id = next_tentative_context_id_++;
    frame.mode = mode;
    if (mode == TentativeMode::ParserOnly) {
        frame.token_checkpoint = capture_tentative_token_state();
    } else {
        frame.parser_checkpoint = capture_tentative_state();
    }
    frame.cxx_disambiguation_state = cxx_tentative_state_;
    if (diag_engine) {
        frame.diag_checkpoint = diag_engine->checkpoint();
    }
    if (collect_ && mode == TentativeMode::CollectBacked) {
        collect_->collect_begin_speculative_parse();
    }
    tentative_context_stack_.push_back(std::move(frame));
    return tentative_context_stack_.back().id;
}

void Parser::restore_tentative_context_frame(const TentativeContextFrame& frame) {
    if (collect_ && frame.mode == TentativeMode::CollectBacked) {
        collect_->collect_rollback_speculative_parse();
    }
    if (frame.mode == TentativeMode::ParserOnly) {
        restore_tentative_token_state(frame.token_checkpoint);
    } else {
        restore_tentative_state(frame.parser_checkpoint);
    }
    cxx_tentative_state_ = frame.cxx_disambiguation_state;
    if (diag_engine) {
        diag_engine->restore(frame.diag_checkpoint);
    }
}

void Parser::commit_tentative_context(size_t context_id) {
    if (tentative_context_stack_.empty()) {
        assert(false && "commit_tentative_context with empty stack");
        return;
    }
    while (!tentative_context_stack_.empty() &&
           tentative_context_stack_.back().id != context_id) {
        assert(false && "tentative commit order violation");
        auto stray = std::move(tentative_context_stack_.back());
        tentative_context_stack_.pop_back();
        restore_tentative_context_frame(stray);
    }
    if (tentative_context_stack_.empty()) {
        return;
    }

    auto frame = std::move(tentative_context_stack_.back());
    tentative_context_stack_.pop_back();
    bump_tentative_context_commits();
    if (collect_ && frame.mode == TentativeMode::CollectBacked) {
        collect_->collect_commit_speculative_parse();
    }
}

void Parser::rollback_tentative_context(size_t context_id) {
    if (tentative_context_stack_.empty()) {
        assert(false && "rollback_tentative_context with empty stack");
        return;
    }
    while (!tentative_context_stack_.empty() &&
           tentative_context_stack_.back().id != context_id) {
        assert(false && "tentative rollback order violation");
        auto stray = std::move(tentative_context_stack_.back());
        tentative_context_stack_.pop_back();
        restore_tentative_context_frame(stray);
    }
    if (tentative_context_stack_.empty()) {
        return;
    }

    auto frame = std::move(tentative_context_stack_.back());
    tentative_context_stack_.pop_back();
    bump_tentative_context_rollbacks();
    restore_tentative_context_frame(frame);
}

bool Parser::is_in_tentative_context() const {
    return !tentative_context_stack_.empty();
}

tentative_syntax_probe::Config Parser::syntax_probe_config() const {
    return tentative_syntax_probe::Config{
        .cxx_mode = is_cxx_mode_active(),
        .blocks_enabled = type_ctx && type_ctx->target &&
            darwin_blocks::blocks_enabled_for_langopts(
                lang_opts, *type_ctx->target)};
}

bool Parser::can_use_annotation_cache() const {
    return !tok_mgnt.has_split_tokens();
}

bool Parser::can_use_semantic_annotation_cache() const {
    return can_use_annotation_cache() && collect_ &&
           !is_in_tentative_context() &&
           !collect_->collect_is_speculative_parsing();
}

ParserAnnotationCache::SemanticKey Parser::semantic_annotation_key() const {
    ParserAnnotationCache::SemanticKey key;
    key.syntax_key =
        ParserAnnotationCache::make_config_key(syntax_probe_config());
    if (!collect_) {
        return key;
    }
    key.lookup_generation = collect_->collect_lookup_generation();
    key.scope = collect_->collect_current_scope().get();
    key.decl_context = collect_->get_current_decl_context().get();
    return key;
}

tentative_syntax_probe::Result Parser::probe_type_name_syntax() {
    auto cfg = syntax_probe_config();
    uint32_t key = ParserAnnotationCache::make_config_key(cfg);
    size_t token_idx = tok_mgnt.get_token_idx();
    bool use_cache = can_use_annotation_cache();
    if (use_cache) {
        if (auto cached = annotation_cache_.lookup_result(
                token_idx,
                ParserAnnotationCache::ResultKind::TypeName,
                key)) {
            bump_annotation_cache_hit();
            return *cached;
        }
        bump_annotation_cache_miss();
    }

    TokenStreamCheckpoint checkpoint(tok_mgnt);
    auto result = tentative_syntax_probe::probe_type_name(tok_mgnt, cfg);
    if (use_cache) {
        annotation_cache_.store_result(
            token_idx,
            ParserAnnotationCache::ResultKind::TypeName,
            key,
            result);
    }
    return result;
}

tentative_syntax_probe::Result Parser::probe_declarator_syntax() {
    auto cfg = syntax_probe_config();
    uint32_t key = ParserAnnotationCache::make_config_key(cfg);
    size_t token_idx = tok_mgnt.get_token_idx();
    bool use_cache = can_use_annotation_cache();
    if (use_cache) {
        if (auto cached = annotation_cache_.lookup_result(
                token_idx,
                ParserAnnotationCache::ResultKind::Declarator,
                key)) {
            bump_annotation_cache_hit();
            return *cached;
        }
        bump_annotation_cache_miss();
    }

    TokenStreamCheckpoint checkpoint(tok_mgnt);
    auto result = tentative_syntax_probe::probe_declarator(tok_mgnt, cfg);
    if (use_cache) {
        annotation_cache_.store_result(
            token_idx,
            ParserAnnotationCache::ResultKind::Declarator,
            key,
            result);
    }
    return result;
}

tentative_syntax_probe::Result
Parser::probe_cxx_constrained_placeholder_type_specifier_syntax() {
    auto cfg = syntax_probe_config();
    uint32_t key = ParserAnnotationCache::make_config_key(cfg);
    size_t token_idx = tok_mgnt.get_token_idx();
    bool use_cache = can_use_annotation_cache();
    if (use_cache) {
        if (auto cached = annotation_cache_.lookup_result(
                token_idx,
                ParserAnnotationCache::ResultKind::CxxConstrainedPlaceholder,
                key)) {
            bump_annotation_cache_hit();
            return *cached;
        }
        bump_annotation_cache_miss();
    }

    TokenStreamCheckpoint checkpoint(tok_mgnt);
    auto result =
        tentative_syntax_probe::probe_cxx_constrained_placeholder_type_specifier(
        tok_mgnt,
        cfg);
    if (use_cache) {
        annotation_cache_.store_result(
            token_idx,
            ParserAnnotationCache::ResultKind::CxxConstrainedPlaceholder,
            key,
            result);
    }
    return result;
}

tentative_syntax_probe::Result Parser::probe_cpp_qualified_id_start_syntax() {
    auto cfg = syntax_probe_config();
    uint32_t key = ParserAnnotationCache::make_config_key(cfg);
    size_t token_idx = tok_mgnt.get_token_idx();
    bool use_cache = can_use_annotation_cache();
    if (use_cache) {
        if (auto cached = annotation_cache_.lookup_result(
                token_idx,
                ParserAnnotationCache::ResultKind::CppQualifiedIdStart,
                key)) {
            bump_annotation_cache_hit();
            return *cached;
        }
        bump_annotation_cache_miss();
    }

    TokenStreamCheckpoint checkpoint(tok_mgnt);
    auto result = tentative_syntax_probe::probe_cpp_qualified_id_start(
        tok_mgnt,
        cfg);
    if (use_cache) {
        annotation_cache_.store_result(
            token_idx,
            ParserAnnotationCache::ResultKind::CppQualifiedIdStart,
            key,
            result);
    }
    return result;
}

tentative_syntax_probe::Result Parser::probe_cpp_qualified_declarator_syntax() {
    auto cfg = syntax_probe_config();
    uint32_t key = ParserAnnotationCache::make_config_key(cfg);
    size_t token_idx = tok_mgnt.get_token_idx();
    bool use_cache = can_use_annotation_cache();
    if (use_cache) {
        if (auto cached = annotation_cache_.lookup_result(
                token_idx,
                ParserAnnotationCache::ResultKind::CppQualifiedDeclarator,
                key)) {
            bump_annotation_cache_hit();
            return *cached;
        }
        bump_annotation_cache_miss();
    }

    TokenStreamCheckpoint checkpoint(tok_mgnt);
    auto result = tentative_syntax_probe::probe_cpp_qualified_declarator(
        tok_mgnt,
        cfg);
    if (use_cache) {
        annotation_cache_.store_result(
            token_idx,
            ParserAnnotationCache::ResultKind::CppQualifiedDeclarator,
            key,
            result);
    }
    return result;
}

tentative_syntax_probe::Result
Parser::probe_cpp_template_name_argument_prefix_syntax() {
    auto cfg = syntax_probe_config();
    uint32_t key = ParserAnnotationCache::make_config_key(cfg);
    size_t token_idx = tok_mgnt.get_token_idx();
    bool use_cache = can_use_annotation_cache();
    if (use_cache) {
        if (auto cached = annotation_cache_.lookup_result(
                token_idx,
                ParserAnnotationCache::ResultKind::CppTemplateNameArgumentPrefix,
                key)) {
            bump_annotation_cache_hit();
            return *cached;
        }
        bump_annotation_cache_miss();
    }

    TokenStreamCheckpoint checkpoint(tok_mgnt);
    auto result = tentative_syntax_probe::probe_cpp_template_name_argument_prefix(
        tok_mgnt,
        cfg);
    if (use_cache) {
        annotation_cache_.store_result(
            token_idx,
            ParserAnnotationCache::ResultKind::CppTemplateNameArgumentPrefix,
            key,
            result);
    }
    return result;
}

tentative_syntax_probe::Result Parser::probe_parenthesized_type_name_syntax() {
    auto cfg = syntax_probe_config();
    uint32_t key = ParserAnnotationCache::make_config_key(cfg);
    size_t token_idx = tok_mgnt.get_token_idx();
    bool use_cache = can_use_annotation_cache();
    if (use_cache) {
        if (auto cached = annotation_cache_.lookup_result(
                token_idx,
                ParserAnnotationCache::ResultKind::ParenthesizedTypeName,
                key)) {
            bump_annotation_cache_hit();
            return *cached;
        }
        bump_annotation_cache_miss();
    }

    TokenStreamCheckpoint checkpoint(tok_mgnt);
    tentative_syntax_probe::Result result =
        tentative_syntax_probe::Result::NoMatch;
    if (tok_mgnt.gentle_check_and_consume(TokenType::LEFT_PAREN) &&
        current_token().type != TokenType::EXTENSION_KW) {
        result = tentative_syntax_probe::probe_type_name(tok_mgnt, cfg);
    }
    if (use_cache) {
        annotation_cache_.store_result(
            token_idx,
            ParserAnnotationCache::ResultKind::ParenthesizedTypeName,
            key,
            result);
    }
    return result;
}

ParserAnnotationCache::CxxParenthesizedTypeIdAnnotation
Parser::classify_cxx_parenthesized_type_id_for_lookahead() {
    ParserAnnotationCache::CxxParenthesizedTypeIdAnnotation inconclusive;
    inconclusive.kind =
        ParserAnnotationCache::CxxParenthesizedTypeIdKind::Inconclusive;
    inconclusive.close_token_idx = tok_mgnt.get_token_idx();
    inconclusive.end_token_idx = tok_mgnt.get_token_idx();
    inconclusive.dependent_or_ambiguous = true;

    if (!is_cxx_mode_active()) {
        ParserAnnotationCache::CxxParenthesizedTypeIdAnnotation no_match;
        no_match.close_token_idx = tok_mgnt.get_token_idx();
        no_match.end_token_idx = tok_mgnt.get_token_idx();
        return no_match;
    }
    if (tok_mgnt.has_split_tokens()) {
        return inconclusive;
    }

    const bool use_cache = can_use_semantic_annotation_cache();
    const size_t token_idx = tok_mgnt.get_token_idx();
    ParserAnnotationCache::SemanticKey key;
    if (use_cache) {
        key = semantic_annotation_key();
        if (auto cached =
                annotation_cache_
                    .lookup_cxx_parenthesized_type_id_annotation(
                        token_idx,
                        key)) {
            bump_annotation_cache_hit();
            return *cached;
        }
        bump_annotation_cache_miss();
    }

    auto annotation = compute_cxx_parenthesized_type_id_for_lookahead();
    if (use_cache) {
        annotation_cache_.store_cxx_parenthesized_type_id_annotation(
            token_idx,
            key,
            annotation);
    }
    return annotation;
}

ParserAnnotationCache::CxxParenthesizedTypeIdAnnotation
Parser::compute_cxx_parenthesized_type_id_for_lookahead() {
    using Kind = ParserAnnotationCache::CxxParenthesizedTypeIdKind;
    ParserAnnotationCache::CxxParenthesizedTypeIdAnnotation result;
    const size_t start_idx = tok_mgnt.get_token_idx();
    result.close_token_idx = start_idx;
    result.end_token_idx = start_idx;

    auto finish = [&](Kind kind) {
        result.kind = kind;
        return result;
    };
    auto finish_inconclusive = [&]() {
        result.kind = Kind::Inconclusive;
        result.dependent_or_ambiguous = true;
        return result;
    };
    auto is_cv_or_nullability_qualifier = [](TokenType type) {
        switch (type) {
            case TokenType::CONST:
            case TokenType::VOLATILE:
            case TokenType::RESTRICT:
            case TokenType::ATOMIC:
            case TokenType::NULLABILITY_QUALIFIER:
                return true;
            default:
                return false;
        }
    };
    auto should_semantically_classify_start = [](TokenType type) {
        return type == TokenType::IDENTIFIER ||
               type == TokenType::SCOPE_RESOLUTION ||
               type == TokenType::TYPENAME ||
               type == TokenType::DECLTYPE_KW ||
               type == TokenType::COLON;
    };
    auto scan_parenthesized_follow_token = [&]() -> std::optional<TokenType> {
        if (peek_token_shortcut(0).type != TokenType::LEFT_PAREN) {
            return std::nullopt;
        }
        size_t offset = 0;
        size_t depth = 0;
        while (peek_token_shortcut(offset).type != TokenType::Eof) {
            TokenType type = peek_token_shortcut(offset).type;
            if (type == TokenType::LEFT_PAREN) {
                ++depth;
            } else if (type == TokenType::RIGHT_PAREN) {
                --depth;
                ++offset;
                if (depth == 0) {
                    return peek_token_shortcut(offset).type;
                }
                continue;
            }
            ++offset;
        }
        return std::nullopt;
    };

    if (!is_cxx_mode_active() || !collect_ ||
        tok_mgnt.current_token().type != TokenType::LEFT_PAREN) {
        return result;
    }

    bool semantic_start_dependent_or_ambiguous = false;
    {
        TokenStreamCheckpoint checkpoint(tok_mgnt);
        tok_mgnt.advance(); // consume '('
        if (tok_mgnt.current_token().type == TokenType::EXTENSION_KW) {
            return result;
        }
        while (is_cv_or_nullability_qualifier(tok_mgnt.current_token().type)) {
            tok_mgnt.advance();
        }
        TokenType semantic_start = tok_mgnt.current_token().type;
        if (should_semantically_classify_start(semantic_start)) {
            auto type_scope = classify_cpp_type_scope_for_lookahead(
                ParserAnnotationCache::CppTypeScopeContext::TypeId);
            switch (type_scope.kind) {
                case ParserAnnotationCache::CppTypeScopeKind::TypeName:
                case ParserAnnotationCache::CppTypeScopeKind::TypeTemplateId:
                case ParserAnnotationCache::CppTypeScopeKind::DependentType:
                case ParserAnnotationCache::CppTypeScopeKind::
                    PlaceholderConstraint:
                    break;
                case ParserAnnotationCache::CppTypeScopeKind::NoMatch:
                case ParserAnnotationCache::CppTypeScopeKind::NonType:
                    return result;
                case ParserAnnotationCache::CppTypeScopeKind::ScopeOnly:
                case ParserAnnotationCache::CppTypeScopeKind::DependentScope:
                case ParserAnnotationCache::CppTypeScopeKind::Inconclusive:
                    semantic_start_dependent_or_ambiguous = true;
                    break;
                case ParserAnnotationCache::CppTypeScopeKind::Error:
                    return finish(Kind::Error);
            }
        }
    }

    TokenStreamCheckpoint checkpoint(tok_mgnt);
    tok_mgnt.advance(); // consume '('
    if (tok_mgnt.current_token().type == TokenType::EXTENSION_KW) {
        return result;
    }

    auto syntax_result =
        tentative_syntax_probe::probe_type_name(tok_mgnt, syntax_probe_config());
    switch (syntax_result) {
        case tentative_syntax_probe::Result::NoMatch:
            return result;
        case tentative_syntax_probe::Result::Inconclusive:
            if (auto follow = scan_parenthesized_follow_token();
                follow && *follow != TokenType::LEFT_BRACE &&
                !token_can_start_cast_operand(*follow)) {
                return result;
            }
            return finish_inconclusive();
        case tentative_syntax_probe::Result::Error:
            return finish(Kind::Error);
        case tentative_syntax_probe::Result::Match:
            break;
    }

    if (tok_mgnt.current_token().type != TokenType::RIGHT_PAREN) {
        return finish_inconclusive();
    }
    result.close_token_idx = tok_mgnt.get_token_idx();
    tok_mgnt.advance(); // consume ')'
    result.end_token_idx = tok_mgnt.get_token_idx();
    TokenType follow = tok_mgnt.current_token().type;
    result.followed_by_left_brace = follow == TokenType::LEFT_BRACE;
    result.followed_by_cast_operand =
        follow != TokenType::LEFT_BRACE && token_can_start_cast_operand(follow);
    result.dependent_or_ambiguous = semantic_start_dependent_or_ambiguous;
    return finish(Kind::TypeId);
}

tentative_syntax_probe::TemplateArgumentListScan
Parser::scan_template_argument_list_scope_follow_syntax() {
    auto cfg = syntax_probe_config();
    uint32_t key = ParserAnnotationCache::make_config_key(cfg);
    size_t token_idx = tok_mgnt.get_token_idx();
    bool use_cache = can_use_annotation_cache();
    if (use_cache) {
        if (auto cached =
                annotation_cache_.lookup_template_argument_list_scan(
                    token_idx,
                    key)) {
            bump_annotation_cache_hit();
            return *cached;
        }
        bump_annotation_cache_miss();
    }

    TokenStreamCheckpoint checkpoint(tok_mgnt);
    auto scan =
        tentative_syntax_probe::scan_template_argument_list_scope_follow(
            tok_mgnt,
            cfg);
    if (use_cache) {
        annotation_cache_.store_template_argument_list_scan(
            token_idx,
            key,
            scan);
    }
    return scan;
}

tentative_syntax_probe::TemplateArgumentListScopeFollow
Parser::classify_template_argument_list_scope_follow_syntax() {
    return scan_template_argument_list_scope_follow_syntax().scope_follow;
}

tentative_syntax_probe::CxxTypeConstructionScan
Parser::scan_cpp_type_construction_candidate_syntax() {
    auto cfg = syntax_probe_config();
    uint32_t key = ParserAnnotationCache::make_config_key(cfg);
    size_t token_idx = tok_mgnt.get_token_idx();
    bool use_cache = can_use_annotation_cache();
    if (use_cache) {
        if (auto cached =
                annotation_cache_.lookup_type_construction_scan(
                    token_idx,
                    key)) {
            bump_annotation_cache_hit();
            return *cached;
        }
        bump_annotation_cache_miss();
    }

    TokenStreamCheckpoint checkpoint(tok_mgnt);
    auto scan = tentative_syntax_probe::scan_cpp_type_construction_candidate(
        tok_mgnt,
        cfg);
    if (use_cache) {
        annotation_cache_.store_type_construction_scan(
            token_idx,
            key,
            scan);
    }
    return scan;
}

tentative_syntax_probe::CxxParameterClauseShape
Parser::scan_cxx_parameter_clause_shape_syntax() {
    auto cfg = syntax_probe_config();
    uint32_t key = ParserAnnotationCache::make_config_key(cfg);
    size_t token_idx = tok_mgnt.get_token_idx();
    bool use_cache = can_use_annotation_cache();
    if (use_cache) {
        if (auto cached = annotation_cache_.lookup_parameter_clause_shape(
                token_idx,
                key)) {
            bump_annotation_cache_hit();
            return *cached;
        }
        bump_annotation_cache_miss();
    }

    TokenStreamCheckpoint checkpoint(tok_mgnt);
    auto shape = tentative_syntax_probe::scan_cxx_parameter_clause_shape(
        tok_mgnt,
        cfg);
    if (use_cache) {
        annotation_cache_.store_parameter_clause_shape(
            token_idx,
            key,
            shape);
    }
    return shape;
}

ParserAnnotationCache::CxxDeclaratorParenSuffixAnnotation
Parser::classify_cxx_declarator_paren_suffix_for_lookahead() {
    ParserAnnotationCache::CxxDeclaratorParenSuffixAnnotation inconclusive;
    inconclusive.kind =
        ParserAnnotationCache::CxxDeclaratorParenSuffixKind::Inconclusive;
    inconclusive.dependent_or_ambiguous = true;

    if (tok_mgnt.has_split_tokens()) {
        return inconclusive;
    }

    const bool use_cache = can_use_semantic_annotation_cache();
    const size_t token_idx = tok_mgnt.get_token_idx();
    ParserAnnotationCache::SemanticKey key;
    if (use_cache) {
        key = semantic_annotation_key();
        if (auto cached =
                annotation_cache_
                    .lookup_cxx_declarator_paren_suffix_annotation(
                        token_idx,
                        key)) {
            bump_declarator_annotation_hit();
            return *cached;
        }
        bump_declarator_annotation_miss();
    }

    auto annotation = compute_cxx_declarator_paren_suffix_for_lookahead();
    if (use_cache) {
        annotation_cache_.store_cxx_declarator_paren_suffix_annotation(
            token_idx,
            key,
            annotation);
        bump_declarator_annotation_publish();
    }
    return annotation;
}

ParserAnnotationCache::CxxDeclaratorParenSuffixAnnotation
Parser::compute_cxx_declarator_paren_suffix_for_lookahead() {
    ParserAnnotationCache::CxxDeclaratorParenSuffixAnnotation result;
    result.kind =
        ParserAnnotationCache::CxxDeclaratorParenSuffixKind::NoMatch;
    result.end_token_idx = tok_mgnt.get_token_idx();

    if (!is_cxx_mode_active()) {
        return result;
    }

    auto finish = [&](ParserAnnotationCache::CxxDeclaratorParenSuffixKind kind) {
        result.kind = kind;
        return result;
    };

    if (tok_mgnt.current_token().type == TokenType::RIGHT_PAREN) {
        return finish(
            ParserAnnotationCache::CxxDeclaratorParenSuffixKind::
                EmptyParameterClause);
    }
    if (tok_mgnt.current_token().type == TokenType::ELLIPSIS) {
        return finish(
            ParserAnnotationCache::CxxDeclaratorParenSuffixKind::
                EllipsisParameterClause);
    }
    if (is_gnu_attribute_token(tok_mgnt.current_token()) ||
        (tok_mgnt.current_token().type == TokenType::LEFT_BRACKET &&
         tok_mgnt.peek_token().type == TokenType::LEFT_BRACKET)) {
        return finish(
            ParserAnnotationCache::CxxDeclaratorParenSuffixKind::
                DefiniteParameterClause);
    }

    auto shape = scan_cxx_parameter_clause_shape_syntax();
    if (shape == tentative_syntax_probe::CxxParameterClauseShape::NoMatch) {
        return finish(
            ParserAnnotationCache::CxxDeclaratorParenSuffixKind::
                DefiniteDirectInitializer);
    }
    if (shape == tentative_syntax_probe::CxxParameterClauseShape::Empty) {
        return finish(
            ParserAnnotationCache::CxxDeclaratorParenSuffixKind::
                EmptyParameterClause);
    }
    if (shape == tentative_syntax_probe::CxxParameterClauseShape::Ellipsis) {
        return finish(
            ParserAnnotationCache::CxxDeclaratorParenSuffixKind::
                EllipsisParameterClause);
    }
    if (shape ==
        tentative_syntax_probe::CxxParameterClauseShape::PotentialParameter) {
        result.kind =
            ParserAnnotationCache::CxxDeclaratorParenSuffixKind::Ambiguous;
        result.dependent_or_ambiguous = true;
        return result;
    }

    TokenType parameter_start_type = tok_mgnt.current_token().type;
    if (parameter_start_type == TokenType::IDENTIFIER ||
        parameter_start_type == TokenType::SCOPE_RESOLUTION ||
        (parameter_start_type == TokenType::COLON &&
         tok_mgnt.peek_token().type == TokenType::COLON)) {
        auto type_scope = classify_cpp_type_scope_for_lookahead(
            ParserAnnotationCache::CppTypeScopeContext::DeclaratorParameter);
        switch (type_scope.kind) {
            case ParserAnnotationCache::CppTypeScopeKind::NoMatch:
            case ParserAnnotationCache::CppTypeScopeKind::NonType:
                bump_declarator_paren_suffix_type_scope_reject();
                return finish(
                    ParserAnnotationCache::CxxDeclaratorParenSuffixKind::
                        DefiniteDirectInitializer);
            case ParserAnnotationCache::CppTypeScopeKind::TypeName:
            case ParserAnnotationCache::CppTypeScopeKind::TypeTemplateId:
            case ParserAnnotationCache::CppTypeScopeKind::DependentType:
            case ParserAnnotationCache::CppTypeScopeKind::DependentScope:
            case ParserAnnotationCache::CppTypeScopeKind::ScopeOnly:
            case ParserAnnotationCache::CppTypeScopeKind::
                PlaceholderConstraint:
            case ParserAnnotationCache::CppTypeScopeKind::Inconclusive:
            case ParserAnnotationCache::CppTypeScopeKind::Error:
                bump_declarator_paren_suffix_type_scope_fallback();
                break;
        }
        result.kind =
            ParserAnnotationCache::CxxDeclaratorParenSuffixKind::Ambiguous;
        result.dependent_or_ambiguous = true;
        return result;
    }

    result.kind =
        ParserAnnotationCache::CxxDeclaratorParenSuffixKind::Inconclusive;
    result.dependent_or_ambiguous = true;
    return result;
}

ParserAnnotationCache::CppQualifiedDeclaratorPrefixAnnotation
Parser::classify_cpp_qualified_declarator_prefix_for_lookahead() {
    ParserAnnotationCache::CppQualifiedDeclaratorPrefixAnnotation inconclusive;
    inconclusive.kind =
        ParserAnnotationCache::CppQualifiedDeclaratorPrefixKind::Inconclusive;
    inconclusive.dependent_or_ambiguous = true;

    if (tok_mgnt.has_split_tokens()) {
        return inconclusive;
    }

    const bool use_cache = can_use_annotation_cache();
    const size_t token_idx = tok_mgnt.get_token_idx();
    const uint32_t key =
        ParserAnnotationCache::make_config_key(syntax_probe_config());
    if (use_cache) {
        if (auto cached =
                annotation_cache_
                    .lookup_cpp_qualified_declarator_prefix_annotation(
                        token_idx,
                        key)) {
            bump_declarator_annotation_hit();
            return *cached;
        }
        bump_declarator_annotation_miss();
    }

    auto annotation = compute_cpp_qualified_declarator_prefix_for_lookahead();
    if (use_cache) {
        annotation_cache_.store_cpp_qualified_declarator_prefix_annotation(
            token_idx,
            key,
            annotation);
        bump_declarator_annotation_publish();
    }
    return annotation;
}

ParserAnnotationCache::CppQualifiedDeclaratorPrefixAnnotation
Parser::compute_cpp_qualified_declarator_prefix_for_lookahead() {
    ParserAnnotationCache::CppQualifiedDeclaratorPrefixAnnotation result;
    result.kind =
        ParserAnnotationCache::CppQualifiedDeclaratorPrefixKind::NoMatch;
    result.end_token_idx = tok_mgnt.get_token_idx();

    if (!is_cxx_mode_active()) {
        return result;
    }

    const size_t start_idx = tok_mgnt.get_token_idx();
    auto token_at = [&](size_t offset) -> const Token& {
        if (offset == 0) {
            return tok_mgnt.current_token();
        }
        return tok_mgnt.peek_token(offset);
    };
    auto finish_inconclusive = [&]() {
        result.kind =
            ParserAnnotationCache::CppQualifiedDeclaratorPrefixKind::
                Inconclusive;
        result.dependent_or_ambiguous = true;
        return result;
    };
    auto skip_balanced_group_at =
        [&](size_t& offset,
            TokenType open_tok,
            TokenType close_tok) {
        if (token_at(offset).type != open_tok) {
            return false;
        }
        size_t depth = 0;
        while (token_at(offset).type != TokenType::Eof) {
            TokenType type = token_at(offset).type;
            if (type == open_tok) {
                ++depth;
            } else if (type == close_tok) {
                --depth;
                ++offset;
                if (depth == 0) {
                    return true;
                }
                continue;
            }
            ++offset;
        }
        return false;
    };
    auto skip_template_argument_list_at = [&](size_t& offset) {
        if (token_at(offset).type != TokenType::LESS_THAN) {
            return true;
        }
        int depth = 0;
        while (token_at(offset).type != TokenType::Eof) {
            TokenType type = token_at(offset).type;
            if (type == TokenType::LEFT_PAREN) {
                if (!skip_balanced_group_at(
                        offset,
                        TokenType::LEFT_PAREN,
                        TokenType::RIGHT_PAREN)) {
                    return false;
                }
                continue;
            }
            if (type == TokenType::LEFT_BRACKET) {
                if (!skip_balanced_group_at(
                        offset,
                        TokenType::LEFT_BRACKET,
                        TokenType::RIGHT_BRACKET)) {
                    return false;
                }
                continue;
            }
            if (type == TokenType::LEFT_BRACE) {
                if (!skip_balanced_group_at(
                        offset,
                        TokenType::LEFT_BRACE,
                        TokenType::RIGHT_BRACE)) {
                    return false;
                }
                continue;
            }
            if (type == TokenType::LESS_THAN) {
                ++depth;
                ++offset;
                continue;
            }
            if (type == TokenType::GREATER_THAN) {
                --depth;
                ++offset;
                if (depth == 0) {
                    return true;
                }
                if (depth < 0) {
                    return false;
                }
                continue;
            }
            if (type == TokenType::RIGHT_SHIFT ||
                type == TokenType::ASSIGN_RSHIFT) {
                if (depth <= 0) {
                    return false;
                }
                if (depth <= 2) {
                    ++offset;
                    return true;
                }
                depth -= 2;
                ++offset;
                continue;
            }
            ++offset;
        }
        return false;
    };
    auto consume_scope_resolution_at = [&](size_t& offset) {
        if (token_at(offset).type == TokenType::SCOPE_RESOLUTION) {
            ++offset;
            return true;
        }
        if (token_at(offset).type == TokenType::COLON &&
            token_at(offset + 1).type == TokenType::COLON) {
            offset += 2;
            return true;
        }
        return false;
    };
    auto skip_post_pointer_qualifiers_at = [&](size_t& offset) {
        while (true) {
            TokenType type = token_at(offset).type;
            if (type == TokenType::CONST ||
                type == TokenType::VOLATILE ||
                type == TokenType::RESTRICT ||
                type == TokenType::ATOMIC ||
                type == TokenType::NULLABILITY_QUALIFIER) {
                ++offset;
                continue;
            }
            if (is_gnu_attribute_token(token_at(offset))) {
                ++offset;
                if (token_at(offset).type == TokenType::LEFT_PAREN &&
                    !skip_balanced_group_at(offset,
                                            TokenType::LEFT_PAREN,
                                            TokenType::RIGHT_PAREN)) {
                    return false;
                }
                continue;
            }
            return true;
        }
    };
    auto skip_leading_declarator_prefix_at = [&](size_t& offset) {
        while (true) {
            TokenType type = token_at(offset).type;
            if (type == TokenType::MULTIPLY ||
                type == TokenType::BITWISE_XOR) {
                ++offset;
                if (!skip_post_pointer_qualifiers_at(offset)) {
                    return false;
                }
                continue;
            }
            if (type == TokenType::LOGICAL_AND ||
                type == TokenType::BITWISE_AND) {
                ++offset;
                continue;
            }
            return true;
        }
    };
    auto parse_identifier_component_at = [&](size_t& offset) {
        if (token_at(offset).type != TokenType::IDENTIFIER) {
            return false;
        }
        ++offset;
        if (token_at(offset).type == TokenType::LESS_THAN) {
            result.has_template_id_component = true;
            if (!skip_template_argument_list_at(offset)) {
                return false;
            }
        }
        return true;
    };

    size_t offset = 0;
    if (!skip_leading_declarator_prefix_at(offset)) {
        return finish_inconclusive();
    }

    bool has_global_qualifier = consume_scope_resolution_at(offset);
    result.has_global_qualifier = has_global_qualifier;
    bool saw_scope = has_global_qualifier;

    if (has_global_qualifier &&
        token_at(offset).type == TokenType::OPERATOR_KW) {
        result.terminal_is_operator_id = true;
        result.end_token_idx = start_idx + offset;
        result.kind =
            ParserAnnotationCache::CppQualifiedDeclaratorPrefixKind::
                QualifiedDeclarator;
        return result;
    }

    if (!parse_identifier_component_at(offset)) {
        if (has_global_qualifier) {
            return finish_inconclusive();
        }
        return result;
    }

    while (consume_scope_resolution_at(offset)) {
        saw_scope = true;
        if (token_at(offset).type == TokenType::OPERATOR_KW) {
            result.terminal_is_operator_id = true;
            result.end_token_idx = start_idx + offset;
            result.kind =
                ParserAnnotationCache::CppQualifiedDeclaratorPrefixKind::
                    QualifiedDeclarator;
            return result;
        }
        if (!parse_identifier_component_at(offset)) {
            return finish_inconclusive();
        }
    }

    result.end_token_idx = start_idx + offset;
    if (saw_scope) {
        result.kind =
            ParserAnnotationCache::CppQualifiedDeclaratorPrefixKind::
                QualifiedDeclarator;
    }
    return result;
}

Parser::TentativeParsingAction::TentativeParsingAction(
    Parser& parser,
    std::source_location loc)
    : TentativeParsingAction(
          parser,
          TentativeMode::CollectBacked,
          loc) {}

Parser::TentativeParsingAction::TentativeParsingAction(
    Parser& parser,
    TentativeMode mode,
    std::source_location loc)
    : parser_(parser),
      tentative_mode_(mode) {
    if (auto* profiler = active_perf_profiler(); profiler && profiler->wants_full()) {
        tentative_profiler_ = profiler;
        tentative_file_ = loc.file_name();
        tentative_function_ = loc.function_name();
        tentative_line_ = loc.line();
        tentative_start_token_idx_ = parser_.get_token_idx();
        tentative_depth_ = parser_.tentative_context_stack_.size() + 1;
        tentative_start_ = std::chrono::steady_clock::now();
    }
    context_id_ = parser_.begin_tentative_context(mode);
}

Parser::TentativeParsingAction::~TentativeParsingAction() {
    revert();
}

void Parser::TentativeParsingAction::commit() {
    if (!active_) {
        return;
    }
    record_tentative_outcome(true);
    parser_.commit_tentative_context(context_id_);
    active_ = false;
}

void Parser::TentativeParsingAction::revert() {
    if (!active_) {
        return;
    }
    record_tentative_outcome(false);
    parser_.rollback_tentative_context(context_id_);
    active_ = false;
}

void Parser::TentativeParsingAction::record_tentative_outcome(bool committed) {
    if (!tentative_profiler_) {
        return;
    }

    tentative_profiler_->record_tentative_parse_site(
        tentative_file_,
        tentative_function_,
        tentative_line_,
        committed,
        tentative_mode_ == TentativeMode::CollectBacked,
        tentative_start_token_idx_,
        parser_.get_token_idx(),
        tentative_depth_,
        std::chrono::steady_clock::now() - tentative_start_);
    tentative_profiler_ = nullptr;
}

Parser::TentativeParserState Parser::capture_tentative_state() {
    bump_tentative_state_captures();
    TentativeParserState state;
    state.token_idx = get_token_idx();
    state.split_token_state = tok_mgnt.get_split_token_state();
    state.func_type = func_type;
    state.active_language_linkage = current_language_linkage_;
    state.seen_stmt_labels = seen_stmt_labels;
    state.stmt_labels = stmt_labels;
    state.local_label_scopes = local_label_scopes_;
    state.local_label_unique_id = local_label_unique_id_;
    state.loop_count = loop_count;
    state.switch_count = switch_count;
    state.has_default = has_default;
    state.case_values = case_values;
    state.template_pattern_depth = template_pattern_depth_;
    state.template_parameter_depth = template_parameter_depth_;
    state.template_argument_expression_depth =
        template_argument_expression_depth_;
    state.template_argument_group_depth = template_argument_group_depth_;
    state.cpp_template_declaration_subject_parse_depth =
        cpp_template_declaration_subject_parse_depth_;
    return state;
}

void Parser::restore_tentative_state(const TentativeParserState& state) {
    bump_tentative_state_restores();
    set_token_idx(state.token_idx);
    tok_mgnt.set_split_token_state(state.split_token_state);
    func_type = state.func_type;
    current_language_linkage_ = state.active_language_linkage;
    seen_stmt_labels = state.seen_stmt_labels;
    stmt_labels = state.stmt_labels;
    local_label_scopes_ = state.local_label_scopes;
    local_label_unique_id_ = state.local_label_unique_id;
    loop_count = state.loop_count;
    switch_count = state.switch_count;
    has_default = state.has_default;
    case_values = state.case_values;
    template_pattern_depth_ = state.template_pattern_depth;
    template_parameter_depth_ = state.template_parameter_depth;
    template_argument_expression_depth_ =
        state.template_argument_expression_depth;
    template_argument_group_depth_ = state.template_argument_group_depth;
    cpp_template_declaration_subject_parse_depth_ =
        state.cpp_template_declaration_subject_parse_depth;
}

Parser::TentativeTokenState Parser::capture_tentative_token_state() {
    bump_tentative_state_captures();
    TentativeTokenState state;
    state.token_idx = get_token_idx();
    state.split_token_state = tok_mgnt.get_split_token_state();
    return state;
}

void Parser::restore_tentative_token_state(const TentativeTokenState& state) {
    bump_tentative_state_restores();
    set_token_idx(state.token_idx);
    tok_mgnt.set_split_token_state(state.split_token_state);
}

Parser::TPResult Parser::try_parse_type_name() {
    if (!isTokenDeclarationSpec(current_token())) {
        return TPResult::False;
    }
    size_t start_idx = tok_mgnt.get_token_idx();

    tentative_syntax_probe::Result syntax_probe_result = probe_type_name_syntax();
    if (syntax_probe_result == tentative_syntax_probe::Result::Match) {
        return TPResult::True;
    }
    if (syntax_probe_result == tentative_syntax_probe::Result::NoMatch) {
        return TPResult::False;
    }
    if (syntax_probe_result == tentative_syntax_probe::Result::Error) {
        return TPResult::Error;
    }

    RevertingTentativeParsingAction tentative(*this);
    try {
        DeclarationParser decl(this);
        auto parsed_type = decl.parse_declaration();
        if (!parsed_type) {
            return TPResult::Error;
        }
        if (tok_mgnt.get_token_idx() == start_idx) {
            return TPResult::False;
        }
        if (!decl.name.empty()) {
            return TPResult::False;
        }
        return TPResult::True;
    } catch (const FatalErrorLimitReached&) {
        return TPResult::Error;
    } catch (const ParseError&) {
        return TPResult::Error;
    }
}

Parser::TPResult Parser::try_parse_declarator() {
    TokenType tok = current_token().type;
    if (tok != TokenType::MULTIPLY &&
        tok != TokenType::BITWISE_XOR &&
        tok != TokenType::BITWISE_AND &&
        tok != TokenType::LOGICAL_AND &&
        tok != TokenType::LEFT_PAREN &&
        tok != TokenType::IDENTIFIER &&
        tok != TokenType::LEFT_BRACKET) {
        return TPResult::False;
    }
    size_t start_idx = tok_mgnt.get_token_idx();

    tentative_syntax_probe::Result syntax_probe_result = probe_declarator_syntax();
    if (syntax_probe_result == tentative_syntax_probe::Result::Match) {
        return TPResult::True;
    }
    if (syntax_probe_result == tentative_syntax_probe::Result::NoMatch) {
        return TPResult::False;
    }
    if (syntax_probe_result == tentative_syntax_probe::Result::Error) {
        return TPResult::Error;
    }

    RevertingTentativeParsingAction tentative(*this);
    try {
        DeclarationParser decl(this);
        auto placeholder = std::make_shared<PlaceholderType>();
        auto parsed_type = decl.parse_declarator(placeholder);
        if (!parsed_type) {
            return TPResult::Error;
        }
        if (tok_mgnt.get_token_idx() == start_idx) {
            return TPResult::False;
        }
        return TPResult::True;
    } catch (const FatalErrorLimitReached&) {
        return TPResult::Error;
    } catch (const ParseError&) {
        return TPResult::Error;
    }
}

Parser::TPResult Parser::try_parse_simple_declaration() {
    RevertingTentativeParsingAction tentative(*this);
    size_t start_idx = get_token_idx();
    bool had_leading_attrs = false;
    try {
        if (is_gnu_attribute_token(current_token()) ||
            (gentle_check(TokenType::LEFT_BRACKET) && peek_token().type == TokenType::LEFT_BRACKET)) {
            had_leading_attrs = true;
            try_parse_attributes();
        }
        if (!isTokenDeclarationSpec(current_token())) {
            return had_leading_attrs ? TPResult::Ambiguous : TPResult::False;
        }
        auto parsed_decls = parse_declaration();
        if (parsed_decls.empty()) {
            return TPResult::Error;
        }
        if (get_token_idx() == start_idx) {
            return TPResult::False;
        }
        return TPResult::True;
    } catch (const FatalErrorLimitReached&) {
        return TPResult::Error;
    } catch (const ParseError&) {
        return TPResult::Error;
    }
}

Parser::TPResult Parser::try_parse_expression_statement_start() {
    RevertingTentativeParsingAction tentative(*this);
    if (gentle_check(TokenType::SEMICOLON)) {
        return TPResult::True;
    }
    size_t start_idx = get_token_idx();
    try {
        auto expr = parse_expression();
        if (!expr) {
            return TPResult::Error;
        }
        if (get_token_idx() == start_idx) {
            return TPResult::False;
        }
        return TPResult::True;
    } catch (const FatalErrorLimitReached&) {
        return TPResult::Error;
    } catch (const ParseError&) {
        return TPResult::Error;
    }
}

Parser::CxxStmtDisambiguation Parser::classify_cxx_stmt_disambiguation() {
    if (!is_cxx_mode_active()) {
        return CxxStmtDisambiguation::Invalid;
    }
    if (!isTokenDeclarationSpec(current_token())) {
        return CxxStmtDisambiguation::Expression;
    }
    // C++ [stmt.ambig]: if a statement can be parsed as either declaration
    // or expression-statement, it is interpreted as a declaration.
    auto start_idx = tok_mgnt.get_token_idx();
    auto split_state = tok_mgnt.get_split_token_state();
    auto syntax_result =
        tentative_syntax_probe::probe_cxx_statement_disambiguation(
            tok_mgnt,
            syntax_probe_config());
    tok_mgnt.set_token_idx(start_idx);
    tok_mgnt.set_split_token_state(split_state);

    switch (syntax_result) {
        case tentative_syntax_probe::CxxStatementDisambiguation::Declaration:
            return CxxStmtDisambiguation::Declaration;
        case tentative_syntax_probe::CxxStatementDisambiguation::Expression:
            return CxxStmtDisambiguation::Expression;
        case tentative_syntax_probe::CxxStatementDisambiguation::Ambiguous:
            return CxxStmtDisambiguation::Ambiguous;
        case tentative_syntax_probe::CxxStatementDisambiguation::Invalid:
            return CxxStmtDisambiguation::Invalid;
    }
    return CxxStmtDisambiguation::Invalid;
}
