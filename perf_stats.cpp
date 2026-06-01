#include "perf_stats.h"

#include <algorithm>
#include <array>
#include <fstream>
#include <iomanip>
#include <ostream>
#include <sstream>

namespace {

thread_local PerfProfiler* g_active_perf_profiler = nullptr;

constexpr auto kPhaseNames = std::to_array<const char*>({
    "driver",
    "input_read",
    "include_discovery",
    "preprocess",
    "preprocess_emit",
    "tokenize",
    "parse_collect",
    "ast_memory_report",
    "llvm_lowering",
    "llvm_optimize",
    "emit_llvm",
    "emit_assembly",
    "emit_object",
    "link",
    "source_read",
    "include_search",
    "include_guard_scan",
});

constexpr auto kCounterNames = std::to_array<const char*>({
    "input.files",
    "source.bytes",
    "source.files_loaded",
    "source.file_open_attempts",
    "source.file_open_failures",
    "source.missing_file_cache_hits",
    "source.framework_lookup_attempts",
    "source.framework_lookup_hits",
    "include.requests",
    "include.system_requests",
    "include.quote_requests",
    "include.next_requests",
    "include.import_requests",
    "include.entered",
    "include.builtin_entered",
    "include.lookup_failures",
    "include.skipped_import_once",
    "include.skipped_import_already",
    "include.skipped_pragma_once",
    "include.skipped_macro_guard",
    "include.search_cache_hits",
    "include.search_cache_misses",
    "include.next_search_cache_hits",
    "include.next_search_cache_misses",
    "include.quote_search_cache_hits",
    "include.quote_search_cache_misses",
    "include.quote_next_search_cache_hits",
    "include.quote_next_search_cache_misses",
    "include.guard_checks",
    "include.guard_fast_hits",
    "include.guard_fast_misses",
    "include.guard_slow_checks",
    "include.guard_macro_hits",
    "include.pragma_once_detected",
    "tokens.parser_emitted",
    "tokens.raw_lexed",
    "tokens.pp_number_relex_attempts",
    "tokens.pp_number_relex_successes",
    "tokens.string_literal_concats",
    "tokens.skipped_conditional_scans",
    "tokens.skipped_conditional_bytes",
    "macro.object_expansions",
    "macro.function_expansions",
    "macro.expansion_tokens",
    "macro.argument_tokens",
    "macro.expansion_max_depth",
    "parser.tentative_begins",
    "parser.tentative_parser_only_begins",
    "parser.tentative_collect_backed_begins",
    "parser.tentative_commits",
    "parser.tentative_rollbacks",
    "parser.tentative_state_captures",
    "parser.tentative_state_restores",
    "parser.annotation.store_hits",
    "parser.annotation.store_misses",
    "parser.annotation.semantic_overlay_hits",
    "parser.annotation.semantic_overlay_misses",
    "parser.annotation.semantic_overlay_publishes",
    "parser.annotation.typed_hits",
    "parser.annotation.typed_misses",
    "parser.annotation.typed_publishes",
    "parser.annotation.typed_consumes",
    "parser.template_id_annotation_hits",
    "parser.template_id_annotation_misses",
    "parser.template_id_annotation_publishes",
    "parser.template_id_fast_no_match",
    "parser.template_id_fast_accepts",
    "parser.template_id_inconclusive_fallbacks",
    "parser.template_id_split_token_fallbacks",
    "parser.qualified_id_annotation_hits",
    "parser.qualified_id_annotation_misses",
    "parser.qualified_id_annotation_publishes",
    "parser.qualified_id_fast_accepts",
    "parser.qualified_id_fast_rejects",
    "parser.qualified_id_inconclusive_fallbacks",
    "parser.dependent_qualified_call_fast_rejects",
    "parser.type_construction_fast_rejects",
    "parser.type_construction_lookup_rejects",
    "parser.template_arg.template_name",
    "parser.template_arg.nullptr",
    "parser.template_arg.direct_type",
    "parser.template_arg.tentative_type",
    "parser.template_arg.tentative_type_failures",
    "parser.template_arg.typed_braced",
    "parser.template_arg.expression",
    "parser.template_arg.annotation_hits",
    "parser.template_arg.annotation_misses",
    "parser.template_arg.annotation_publishes",
    "parser.template_arg.fast_type",
    "parser.template_arg.fast_expression",
    "parser.template_arg.inconclusive_fallbacks",
    "parser.template_arg.annotated_type_direct",
    "parser.template_arg.annotated_type_fallback",
    "parser.template_arg.annotated_type_complex_fallback",
    "parser.template_arg.tentative_type_avoided",
    "parser.declarator.annotation_hits",
    "parser.declarator.annotation_misses",
    "parser.declarator.annotation_publishes",
    "parser.declarator.parameter_clause_fast_accepts",
    "parser.declarator.direct_initializer_fast_rejects",
    "parser.declarator.paren_suffix_type_scope_rejects",
    "parser.declarator.paren_suffix_type_scope_fallbacks",
    "parser.qualified_declarator.fast_rejects",
    "parser.cast_disambiguation.fast_accepts",
    "parser.cast_disambiguation.fast_rejects",
    "parser.cast_disambiguation.inconclusive_fallbacks",
    "parser.postfix_template_suffix.fast_rejects",
    "parser.direct_type_id.parses",
    "parser.direct_type_id.fallbacks",
    "parser.direct_type_id.complex_fallbacks",
    "parser.cast.direct_type_id_parses",
    "parser.cast.direct_type_id_fallbacks",
    "parser.type_construction.direct_type_id_parses",
    "parser.type_construction.direct_type_id_fallbacks",
    "parser.type_scope_annotation_hits",
    "parser.type_scope_annotation_misses",
    "parser.type_scope_annotation_publishes",
    "parser.type_scope_fast_type_accepts",
    "parser.type_scope_fast_non_type_rejects",
    "parser.type_scope_scope_only_accepts",
    "parser.type_scope_inconclusive_fallbacks",
    "parser.skipped_system_function_bodies",
    "collect.tentative_begins",
    "collect.tentative_commits",
    "collect.tentative_rollbacks",
    "collect.snapshot_materializations",
    "collect.decl_context_clone_roots",
    "collect.decl_context_nodes_cloned",
    "collect.scope_nodes_cloned",
    "collect.query_record_hits",
    "collect.query_record_misses",
    "collect.query_record_publishes",
    "collect.query_enum_hits",
    "collect.query_enum_misses",
    "collect.query_enum_publishes",
    "collect.query_template_type_hits",
    "collect.query_template_type_misses",
    "collect.query_template_type_publishes",
    "collect.query_dependent_name_hits",
    "collect.query_dependent_name_misses",
    "collect.query_dependent_name_publishes",
    "collect.query_overlay_begins",
    "collect.query_overlay_materializations",
    "collect.query_overlay_commits",
    "collect.query_overlay_rollbacks",
    "collect.query_overlay_merges",
    "collect.overload_resolve_calls",
    "collect.overload_candidate_evaluations",
    "collect.overload_pairwise_comparisons",
    "collect.overload_frontier_prunes",
    "collect.overload_viable_candidates",
    "collect.overload_conversion_cache_hits",
    "collect.overload_conversion_cache_misses",
});

static_assert(kPhaseNames.size() == static_cast<size_t>(PerfPhase::Count));
static_assert(kCounterNames.size() == static_cast<size_t>(PerfCounter::Count));

const char* phase_name(PerfPhase phase) {
    return kPhaseNames[static_cast<size_t>(phase)];
}

const char* counter_name(PerfCounter counter) {
    return kCounterNames[static_cast<size_t>(counter)];
}

double ms(std::chrono::nanoseconds duration) {
    return static_cast<double>(duration.count()) / 1000000.0;
}

std::string json_escape(std::string_view value) {
    std::string out;
    out.reserve(value.size() + 8);
    for (char c : value) {
        switch (c) {
            case '\\':
                out += "\\\\";
                break;
            case '"':
                out += "\\\"";
                break;
            case '\n':
                out += "\\n";
                break;
            case '\r':
                out += "\\r";
                break;
            case '\t':
                out += "\\t";
                break;
            default:
                if (static_cast<unsigned char>(c) < 0x20) {
                    std::ostringstream escaped;
                    escaped << "\\u" << std::hex << std::setw(4)
                            << std::setfill('0')
                            << static_cast<int>(static_cast<unsigned char>(c));
                    out += escaped.str();
                } else {
                    out.push_back(c);
                }
                break;
        }
    }
    return out;
}

std::string tentative_site_key(std::string_view file,
                               std::string_view function,
                               uint32_t line) {
    std::string key;
    key.reserve(file.size() + function.size() + 32);
    key.append(file);
    key.push_back(':');
    key += std::to_string(line);
    key.push_back(':');
    key.append(function);
    return key;
}

template <typename Pair>
auto sorted_top_by_value(const std::unordered_map<std::string, Pair>& map,
                         uint64_t Pair::*member,
                         size_t limit) {
    std::vector<const std::pair<const std::string, Pair>*> rows;
    rows.reserve(map.size());
    for (const auto& row : map) {
        if (row.second.*member != 0) {
            rows.push_back(&row);
        }
    }
    std::sort(rows.begin(), rows.end(), [member](const auto* lhs, const auto* rhs) {
        auto lhs_value = lhs->second.*member;
        auto rhs_value = rhs->second.*member;
        if (lhs_value != rhs_value) {
            return lhs_value > rhs_value;
        }
        return lhs->first < rhs->first;
    });
    if (rows.size() > limit) {
        rows.resize(limit);
    }
    return rows;
}

std::vector<const std::pair<const std::string, PerfProfiler::HeaderStats>*>
sorted_headers_by_inclusive(
    const std::unordered_map<std::string, PerfProfiler::HeaderStats>& headers,
    size_t limit) {
    std::vector<const std::pair<const std::string, PerfProfiler::HeaderStats>*> rows;
    rows.reserve(headers.size());
    for (const auto& row : headers) {
        if (row.second.entered != 0 || row.second.requests != 0) {
            rows.push_back(&row);
        }
    }
    std::sort(rows.begin(), rows.end(), [](const auto* lhs, const auto* rhs) {
        if (lhs->second.inclusive != rhs->second.inclusive) {
            return lhs->second.inclusive > rhs->second.inclusive;
        }
        if (lhs->second.requests != rhs->second.requests) {
            return lhs->second.requests > rhs->second.requests;
        }
        return lhs->first < rhs->first;
    });
    if (rows.size() > limit) {
        rows.resize(limit);
    }
    return rows;
}

std::vector<const std::pair<const std::string, PerfProfiler::TentativeParseSiteStats>*>
sorted_tentative_sites_by_time(
    const std::unordered_map<std::string, PerfProfiler::TentativeParseSiteStats>& sites,
    size_t limit) {
    std::vector<const std::pair<const std::string, PerfProfiler::TentativeParseSiteStats>*> rows;
    rows.reserve(sites.size());
    for (const auto& row : sites) {
        if (row.second.begins != 0) {
            rows.push_back(&row);
        }
    }
    std::sort(rows.begin(), rows.end(), [](const auto* lhs, const auto* rhs) {
        if (lhs->second.duration != rhs->second.duration) {
            return lhs->second.duration > rhs->second.duration;
        }
        if (lhs->second.rollbacks != rhs->second.rollbacks) {
            return lhs->second.rollbacks > rhs->second.rollbacks;
        }
        return lhs->first < rhs->first;
    });
    if (rows.size() > limit) {
        rows.resize(limit);
    }
    return rows;
}

} // namespace

std::optional<PerfDetail> parse_perf_detail(std::string_view value) {
    if (value == "summary") {
        return PerfDetail::Summary;
    }
    if (value == "headers") {
        return PerfDetail::Headers;
    }
    if (value == "full") {
        return PerfDetail::Full;
    }
    return std::nullopt;
}

const char* perf_detail_name(PerfDetail detail) {
    switch (detail) {
        case PerfDetail::Summary:
            return "summary";
        case PerfDetail::Headers:
            return "headers";
        case PerfDetail::Full:
            return "full";
    }
    return "summary";
}

PerfProfiler::PerfProfiler(PerfDetail detail)
    : detail_(detail),
      start_(Clock::now()),
      phases_(static_cast<size_t>(PerfPhase::Count)),
      counters_(static_cast<size_t>(PerfCounter::Count), 0) {}

void PerfProfiler::add_phase_duration(
    PerfPhase phase,
    std::chrono::steady_clock::duration duration) {
    auto& stats = phases_[static_cast<size_t>(phase)];
    ++stats.count;
    stats.duration += std::chrono::duration_cast<std::chrono::nanoseconds>(duration);
}

void PerfProfiler::add_counter(PerfCounter counter, uint64_t amount) {
    counters_[static_cast<size_t>(counter)] += amount;
}

void PerfProfiler::set_counter_max(PerfCounter counter, uint64_t value) {
    auto& current = counters_[static_cast<size_t>(counter)];
    if (value > current) {
        current = value;
    }
}

void PerfProfiler::record_header_request(std::string_view include_name) {
    (void)include_name;
    add_counter(PerfCounter::IncludeRequests);
}

void PerfProfiler::record_resolved_header_request(std::string_view header_key) {
    if (!wants_headers()) {
        return;
    }
    auto& stats = headers_[std::string(header_key)];
    ++stats.requests;
}

void PerfProfiler::record_header_skip(std::string_view header_key,
                                      PerfCounter skip_counter) {
    add_counter(skip_counter);
    if (!wants_headers()) {
        return;
    }
    auto& stats = headers_[std::string(header_key)];
    switch (skip_counter) {
        case PerfCounter::IncludeSkippedImportOnce:
            ++stats.skipped_import_once;
            break;
        case PerfCounter::IncludeSkippedImportAlready:
            ++stats.skipped_import_already;
            break;
        case PerfCounter::IncludeSkippedPragmaOnce:
            ++stats.skipped_pragma_once;
            break;
        case PerfCounter::IncludeSkippedMacroGuard:
            ++stats.skipped_macro_guard;
            break;
        default:
            break;
    }
}

void PerfProfiler::enter_header(std::string_view header_key,
                                uint64_t bytes,
                                uint64_t emitted_tokens) {
    add_counter(PerfCounter::IncludeEntered);
    if (!wants_headers()) {
        return;
    }
    std::string key(header_key);
    auto& stats = headers_[key];
    ++stats.entered;
    stats.bytes = std::max(stats.bytes, bytes);
    header_stack_.push_back({std::move(key), Clock::now(), {}, emitted_tokens});
}

void PerfProfiler::leave_header(std::string_view header_key,
                                uint64_t emitted_tokens) {
    if (!wants_headers() || header_stack_.empty()) {
        return;
    }

    auto now = Clock::now();
    auto frame_it = header_stack_.end();
    for (auto it = header_stack_.end(); it != header_stack_.begin();) {
        --it;
        if (it->key == header_key) {
            frame_it = it;
            break;
        }
    }
    if (frame_it == header_stack_.end()) {
        return;
    }

    HeaderFrame frame = std::move(*frame_it);
    header_stack_.erase(frame_it);
    auto inclusive = std::chrono::duration_cast<std::chrono::nanoseconds>(
        now - frame.start);
    auto self = inclusive > frame.child ? inclusive - frame.child : std::chrono::nanoseconds{0};
    auto& stats = headers_[frame.key];
    stats.inclusive += inclusive;
    stats.self += self;
    if (emitted_tokens >= frame.emitted_tokens_start) {
        stats.emitted_tokens += emitted_tokens - frame.emitted_tokens_start;
    }
    if (!header_stack_.empty()) {
        header_stack_.back().child += inclusive;
    }
}

void PerfProfiler::record_macro_expansion(std::string_view macro_name,
                                          uint64_t tokens,
                                          bool function_like) {
    add_counter(function_like ? PerfCounter::MacroFunctionExpansions
                              : PerfCounter::MacroObjectExpansions);
    add_counter(PerfCounter::MacroExpansionTokens, tokens);
    if (!wants_full()) {
        return;
    }
    auto& stats = macros_[std::string(macro_name)];
    ++stats.expansions;
    stats.replacement_tokens += tokens;
    if (function_like) {
        ++stats.function_like_expansions;
    }
}

void PerfProfiler::record_tentative_parse_site(
    std::string_view file,
    std::string_view function,
    uint32_t line,
    bool committed,
    bool collect_backed,
    uint64_t start_token,
    uint64_t end_token,
    uint64_t depth,
    std::chrono::steady_clock::duration duration) {
    if (!wants_full()) {
        return;
    }

    auto key = tentative_site_key(file, function, line);
    auto& stats = tentative_parse_sites_[key];
    if (stats.begins == 0) {
        stats.file = std::string(file);
        stats.function = std::string(function);
        stats.line = line;
    }

    uint64_t token_span = end_token >= start_token ? end_token - start_token : 0;
    auto nanos = std::chrono::duration_cast<std::chrono::nanoseconds>(duration);

    ++stats.begins;
    if (collect_backed) {
        ++stats.collect_backed_begins;
    } else {
        ++stats.parser_only_begins;
    }
    stats.duration += nanos;
    stats.tokens_consumed += token_span;
    stats.max_token_span = std::max(stats.max_token_span, token_span);
    stats.max_depth = std::max(stats.max_depth, depth);
    if (committed) {
        ++stats.commits;
        stats.commit_duration += nanos;
    } else {
        ++stats.rollbacks;
        stats.rollback_duration += nanos;
        stats.tokens_rewound += token_span;
    }
}

void PerfProfiler::print_text_report(std::ostream& os) const {
    auto total = std::chrono::duration_cast<std::chrono::nanoseconds>(
        Clock::now() - start_);
    os << "Aburi time report (" << perf_detail_name(detail_) << ")\n";
    os << "Total: " << std::fixed << std::setprecision(3) << ms(total) << " ms\n";

    os << "\nPhases:\n";
    for (size_t i = 0; i < phases_.size(); ++i) {
        const auto& phase = phases_[i];
        if (phase.count == 0) {
            continue;
        }
        os << "  " << kPhaseNames[i]
           << ": " << ms(phase.duration) << " ms"
           << " (" << phase.count << ")\n";
    }

    os << "\nCounters:\n";
    for (size_t i = 0; i < counters_.size(); ++i) {
        if (counters_[i] == 0) {
            continue;
        }
        os << "  " << kCounterNames[i] << ": " << counters_[i] << "\n";
    }

    if (wants_headers() && !headers_.empty()) {
        os << "\nTop headers:\n";
        for (const auto* row : sorted_headers_by_inclusive(headers_, 20)) {
            const auto& stats = row->second;
            os << "  " << row->first
               << ": inclusive=" << ms(stats.inclusive) << " ms"
               << " self=" << ms(stats.self) << " ms"
               << " requests=" << stats.requests
               << " entered=" << stats.entered
               << " tokens=" << stats.emitted_tokens
               << " bytes=" << stats.bytes
               << "\n";
        }
    }

    if (wants_full() && !macros_.empty()) {
        os << "\nTop macros:\n";
        for (const auto* row : sorted_top_by_value(macros_, &MacroStats::expansions, 20)) {
            const auto& stats = row->second;
            os << "  " << row->first
               << ": expansions=" << stats.expansions
               << " function_like=" << stats.function_like_expansions
               << " replacement_tokens=" << stats.replacement_tokens
               << "\n";
        }
    }

    if (wants_full() && !tentative_parse_sites_.empty()) {
        os << "\nTop tentative parse sites:\n";
        for (const auto* row : sorted_tentative_sites_by_time(tentative_parse_sites_, 20)) {
            const auto& stats = row->second;
            os << "  " << stats.file << ":" << stats.line
               << " " << stats.function
                << ": time=" << ms(stats.duration) << " ms"
               << " parser_only=" << stats.parser_only_begins
               << " collect_backed=" << stats.collect_backed_begins
               << " commits=" << stats.commits
               << " rollbacks=" << stats.rollbacks
               << " tokens=" << stats.tokens_consumed
               << " rewound=" << stats.tokens_rewound
               << " max_span=" << stats.max_token_span
               << " max_depth=" << stats.max_depth
               << "\n";
        }
    }
}

bool PerfProfiler::write_json_report(const std::string& path, std::string& error) const {
    std::ofstream out(path);
    if (!out.is_open()) {
        error = "unable to open profiling JSON output: " + path;
        return false;
    }

    auto total = std::chrono::duration_cast<std::chrono::nanoseconds>(
        Clock::now() - start_);
    out << "{\n";
    out << "  \"schema_version\": 2,\n";
    out << "  \"detail\": \"" << perf_detail_name(detail_) << "\",\n";
    out << "  \"total_ms\": " << std::fixed << std::setprecision(3) << ms(total) << ",\n";

    out << "  \"phases\": [\n";
    bool first = true;
    for (size_t i = 0; i < phases_.size(); ++i) {
        const auto& phase = phases_[i];
        if (phase.count == 0) {
            continue;
        }
        if (!first) {
            out << ",\n";
        }
        first = false;
        out << "    {\"name\": \"" << kPhaseNames[i]
            << "\", \"count\": " << phase.count
            << ", \"time_ms\": " << ms(phase.duration) << "}";
    }
    out << "\n  ],\n";

    out << "  \"counters\": {";
    first = true;
    for (size_t i = 0; i < counters_.size(); ++i) {
        if (counters_[i] == 0) {
            continue;
        }
        if (!first) {
            out << ",";
        }
        first = false;
        out << "\n    \"" << kCounterNames[i] << "\": " << counters_[i];
    }
    if (!first) {
        out << "\n  ";
    }
    out << "},\n";

    out << "  \"headers\": [\n";
    first = true;
    if (wants_headers()) {
        for (const auto* row : sorted_headers_by_inclusive(headers_, 200)) {
            const auto& stats = row->second;
            if (!first) {
                out << ",\n";
            }
            first = false;
            out << "    {\"path\": \"" << json_escape(row->first)
                << "\", \"requests\": " << stats.requests
                << ", \"entered\": " << stats.entered
                << ", \"bytes\": " << stats.bytes
                << ", \"tokens\": " << stats.emitted_tokens
                << ", \"inclusive_ms\": " << ms(stats.inclusive)
                << ", \"self_ms\": " << ms(stats.self)
                << ", \"skipped_import_once\": " << stats.skipped_import_once
                << ", \"skipped_import_already\": " << stats.skipped_import_already
                << ", \"skipped_pragma_once\": " << stats.skipped_pragma_once
                << ", \"skipped_macro_guard\": " << stats.skipped_macro_guard
                << "}";
        }
    }
    out << "\n  ],\n";

    out << "  \"macros\": [\n";
    first = true;
    if (wants_full()) {
        for (const auto* row : sorted_top_by_value(macros_, &MacroStats::expansions, 200)) {
            const auto& stats = row->second;
            if (!first) {
                out << ",\n";
            }
            first = false;
            out << "    {\"name\": \"" << json_escape(row->first)
                << "\", \"expansions\": " << stats.expansions
                << ", \"function_like_expansions\": " << stats.function_like_expansions
                << ", \"replacement_tokens\": " << stats.replacement_tokens
                << "}";
        }
    }
    out << "\n  ],\n";

    out << "  \"tentative_sites\": [\n";
    first = true;
    if (wants_full()) {
        for (const auto* row : sorted_tentative_sites_by_time(tentative_parse_sites_, 200)) {
            const auto& stats = row->second;
            if (!first) {
                out << ",\n";
            }
            first = false;
            out << "    {\"file\": \"" << json_escape(stats.file)
                << "\", \"function\": \"" << json_escape(stats.function)
                << "\", \"line\": " << stats.line
                << ", \"begins\": " << stats.begins
                << ", \"parser_only_begins\": " << stats.parser_only_begins
                << ", \"collect_backed_begins\": "
                << stats.collect_backed_begins
                << ", \"commits\": " << stats.commits
                << ", \"rollbacks\": " << stats.rollbacks
                << ", \"time_ms\": " << ms(stats.duration)
                << ", \"commit_time_ms\": " << ms(stats.commit_duration)
                << ", \"rollback_time_ms\": " << ms(stats.rollback_duration)
                << ", \"tokens_consumed\": " << stats.tokens_consumed
                << ", \"tokens_rewound\": " << stats.tokens_rewound
                << ", \"max_token_span\": " << stats.max_token_span
                << ", \"max_depth\": " << stats.max_depth
                << "}";
        }
    }
    out << "\n  ]\n";
    out << "}\n";
    return true;
}

PerfScopedTimer::PerfScopedTimer(PerfProfiler* profiler, PerfPhase phase)
    : profiler_(profiler),
      phase_(phase) {
    if (profiler_) {
        start_ = std::chrono::steady_clock::now();
    }
}

PerfScopedTimer::~PerfScopedTimer() {
    if (!profiler_) {
        return;
    }
    profiler_->add_phase_duration(phase_, std::chrono::steady_clock::now() - start_);
}

PerfProfiler* active_perf_profiler() {
    return g_active_perf_profiler;
}

void set_active_perf_profiler(PerfProfiler* profiler) {
    g_active_perf_profiler = profiler;
}
