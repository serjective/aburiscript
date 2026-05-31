#include "parser.h"
#include "tentative_syntax_probe.h"
#include "../perf_stats.h"

#include <cstdlib>
#include <cstdint>
#include <cassert>
#include <iostream>

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
