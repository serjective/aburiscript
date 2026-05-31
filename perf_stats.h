#ifndef ABURI_PERF_STATS_H
#define ABURI_PERF_STATS_H

#include <chrono>
#include <cstdint>
#include <iosfwd>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

enum class PerfDetail {
    Summary,
    Headers,
    Full
};

std::optional<PerfDetail> parse_perf_detail(std::string_view value);
const char* perf_detail_name(PerfDetail detail);

enum class PerfPhase {
    Driver,
    InputRead,
    IncludeDiscovery,
    Preprocess,
    PreprocessEmit,
    Tokenize,
    ParseCollect,
    AstMemoryReport,
    LlvmLowering,
    LlvmOptimize,
    EmitLlvm,
    EmitAssembly,
    EmitObject,
    Link,
    SourceRead,
    IncludeSearch,
    IncludeGuardScan,
    Count
};

enum class PerfCounter {
    InputFiles,
    SourceBytes,
    FilesLoaded,
    FileOpenAttempts,
    FileOpenFailures,
    MissingFileCacheHits,
    FrameworkLookupAttempts,
    FrameworkLookupHits,
    IncludeRequests,
    IncludeSystemRequests,
    IncludeQuoteRequests,
    IncludeNextRequests,
    IncludeImportRequests,
    IncludeEntered,
    IncludeBuiltinEntered,
    IncludeLookupFailures,
    IncludeSkippedImportOnce,
    IncludeSkippedImportAlready,
    IncludeSkippedPragmaOnce,
    IncludeSkippedMacroGuard,
    IncludeSearchCacheHits,
    IncludeSearchCacheMisses,
    IncludeNextSearchCacheHits,
    IncludeNextSearchCacheMisses,
    QuoteIncludeSearchCacheHits,
    QuoteIncludeSearchCacheMisses,
    QuoteIncludeNextSearchCacheHits,
    QuoteIncludeNextSearchCacheMisses,
    IncludeGuardChecks,
    IncludeGuardFastHits,
    IncludeGuardFastMisses,
    IncludeGuardSlowChecks,
    IncludeGuardMacroHits,
    PragmaOnceDetected,
    ParserTokensEmitted,
    RawTokensLexed,
    PPNumberRelexAttempts,
    PPNumberRelexSuccesses,
    StringLiteralConcats,
    SkippedConditionalScans,
    SkippedConditionalBytes,
    MacroObjectExpansions,
    MacroFunctionExpansions,
    MacroExpansionTokens,
    MacroArgumentTokens,
    MacroExpansionMaxDepth,
    ParserTentativeBegins,
    ParserTentativeParserOnlyBegins,
    ParserTentativeCollectBackedBegins,
    ParserTentativeCommits,
    ParserTentativeRollbacks,
    ParserTentativeStateCaptures,
    ParserTentativeStateRestores,
    ParserTemplateArgumentTemplateName,
    ParserTemplateArgumentNullptr,
    ParserTemplateArgumentDirectType,
    ParserTemplateArgumentTentativeType,
    ParserTemplateArgumentTentativeTypeFailures,
    ParserTemplateArgumentTypedBraced,
    ParserTemplateArgumentExpression,
    ParserSkippedSystemFunctionBodies,
    CollectTentativeBegins,
    CollectTentativeCommits,
    CollectTentativeRollbacks,
    CollectSnapshotMaterializations,
    CollectDeclContextCloneRoots,
    CollectDeclContextNodesCloned,
    CollectScopeNodesCloned,
    CollectQueryRecordHits,
    CollectQueryRecordMisses,
    CollectQueryRecordPublishes,
    CollectQueryEnumHits,
    CollectQueryEnumMisses,
    CollectQueryEnumPublishes,
    CollectQueryTemplateTypeHits,
    CollectQueryTemplateTypeMisses,
    CollectQueryTemplateTypePublishes,
    CollectQueryDependentNameHits,
    CollectQueryDependentNameMisses,
    CollectQueryDependentNamePublishes,
    CollectQueryOverlayBegins,
    CollectQueryOverlayMaterializations,
    CollectQueryOverlayCommits,
    CollectQueryOverlayRollbacks,
    CollectQueryOverlayMerges,
    OverloadResolveCalls,
    OverloadCandidateEvaluations,
    OverloadPairwiseComparisons,
    OverloadFrontierPrunes,
    OverloadViableCandidates,
    OverloadConversionCacheHits,
    OverloadConversionCacheMisses,
    Count
};

class PerfProfiler {
public:
    explicit PerfProfiler(PerfDetail detail = PerfDetail::Summary);

    PerfDetail detail() const {
        return detail_;
    }
    bool wants_headers() const {
        return detail_ == PerfDetail::Headers || detail_ == PerfDetail::Full;
    }
    bool wants_full() const {
        return detail_ == PerfDetail::Full;
    }

    void add_phase_duration(PerfPhase phase, std::chrono::steady_clock::duration duration);
    void add_counter(PerfCounter counter, uint64_t amount = 1);
    void set_counter_max(PerfCounter counter, uint64_t value);

    void record_header_request(std::string_view include_name);
    void record_resolved_header_request(std::string_view header_key);
    void record_header_skip(std::string_view header_key, PerfCounter skip_counter);
    void enter_header(std::string_view header_key, uint64_t bytes, uint64_t emitted_tokens);
    void leave_header(std::string_view header_key, uint64_t emitted_tokens);
    void record_macro_expansion(std::string_view macro_name, uint64_t tokens, bool function_like);
    void record_tentative_parse_site(std::string_view file,
                                     std::string_view function,
                                     uint32_t line,
                                     bool committed,
                                     bool collect_backed,
                                     uint64_t start_token,
                                     uint64_t end_token,
                                     uint64_t depth,
                                     std::chrono::steady_clock::duration duration);

    void print_text_report(std::ostream& os) const;
    bool write_json_report(const std::string& path, std::string& error) const;

    struct HeaderStats {
        uint64_t requests = 0;
        uint64_t entered = 0;
        uint64_t bytes = 0;
        uint64_t emitted_tokens = 0;
        uint64_t skipped_import_once = 0;
        uint64_t skipped_import_already = 0;
        uint64_t skipped_pragma_once = 0;
        uint64_t skipped_macro_guard = 0;
        std::chrono::nanoseconds inclusive{0};
        std::chrono::nanoseconds self{0};
    };

    struct MacroStats {
        uint64_t expansions = 0;
        uint64_t replacement_tokens = 0;
        uint64_t function_like_expansions = 0;
    };

    struct TentativeParseSiteStats {
        std::string file;
        std::string function;
        uint32_t line = 0;
        uint64_t begins = 0;
        uint64_t parser_only_begins = 0;
        uint64_t collect_backed_begins = 0;
        uint64_t commits = 0;
        uint64_t rollbacks = 0;
        uint64_t tokens_consumed = 0;
        uint64_t tokens_rewound = 0;
        uint64_t max_token_span = 0;
        uint64_t max_depth = 0;
        std::chrono::nanoseconds duration{0};
        std::chrono::nanoseconds commit_duration{0};
        std::chrono::nanoseconds rollback_duration{0};
    };

private:
    using Clock = std::chrono::steady_clock;

    struct PhaseStats {
        uint64_t count = 0;
        std::chrono::nanoseconds duration{0};
    };

    struct HeaderFrame {
        std::string key;
        Clock::time_point start;
        std::chrono::nanoseconds child{0};
        uint64_t emitted_tokens_start = 0;
    };

    PerfDetail detail_;
    Clock::time_point start_;
    std::vector<PhaseStats> phases_;
    std::vector<uint64_t> counters_;
    std::unordered_map<std::string, HeaderStats> headers_;
    std::unordered_map<std::string, MacroStats> macros_;
    std::unordered_map<std::string, TentativeParseSiteStats> tentative_parse_sites_;
    std::vector<HeaderFrame> header_stack_;
};

class PerfScopedTimer {
public:
    PerfScopedTimer(PerfProfiler* profiler, PerfPhase phase);
    ~PerfScopedTimer();

    PerfScopedTimer(const PerfScopedTimer&) = delete;
    PerfScopedTimer& operator=(const PerfScopedTimer&) = delete;

private:
    PerfProfiler* profiler_ = nullptr;
    PerfPhase phase_;
    std::chrono::steady_clock::time_point start_;
};

PerfProfiler* active_perf_profiler();
void set_active_perf_profiler(PerfProfiler* profiler);

#endif // ABURI_PERF_STATS_H
