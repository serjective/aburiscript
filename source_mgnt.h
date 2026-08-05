#ifndef ABURI_SOURCE_MGNT_H
#define ABURI_SOURCE_MGNT_H
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <array>
#include <cstdint>
#include <cstring>
#include <memory>

struct SrcLoc {
    uint32_t offset;
    bool isInvalid() const {
        return offset == 0;
    }
    SrcLoc(): offset(0) {};
    SrcLoc(uint32_t o): offset(o) {};
    void increment() {
        offset += 1;
    }
};

struct MappingStep {
    uint32_t logical_index;
    uint32_t physical_offset;
};
struct LogicalLocation {
    std::string file;
    uint32_t line;
    uint32_t column;
};

class PerfProfiler;

class SpellingArena {
public:
    std::string_view store(std::string_view text) {
        char* out = reserve(text.size());
        std::memcpy(out, text.data(), text.size());
        return {out, text.size()};
    }
    std::string_view store_concat(std::string_view a, std::string_view b) {
        char* out = reserve(a.size() + b.size());
        std::memcpy(out, a.data(), a.size());
        std::memcpy(out + a.size(), b.data(), b.size());
        return {out, a.size() + b.size()};
    }

private:
    static constexpr size_t chunk_size = 64 * 1024;
    char* reserve(size_t n) {
        if (n > chunk_size) {
            oversized_.push_back(std::make_unique<char[]>(n));
            return oversized_.back().get();
        }
        if (chunks_.empty() || used_ + n > chunk_size) {
            chunks_.push_back(std::make_unique<char[]>(chunk_size));
            used_ = 0;
        }
        char* out = chunks_.back().get() + used_;
        used_ += n;
        return out;
    }
    std::vector<std::unique_ptr<char[]>> chunks_;
    std::vector<std::unique_ptr<char[]>> oversized_;
    size_t used_ = 0;
};

enum class DiagnosticLevel {
    Error,
    Warning,
    Note
};
enum class DiagnosticSeverity {
    Ignored,
    Warning,
    Error
};
enum class WarningId {
    DeprecatedDeclarations,
    DiscardedQualifiers,
    UnknownAttributes,
    Attributes,
    OverrideInit,
    Varargs,
    ImplicitFunctionDeclaration,
    PointerIntegerComparison,
    Count
};

struct DiagnosticState {
    std::array<DiagnosticSeverity, static_cast<size_t>(WarningId::Count)> severities;
    DiagnosticState() {
        severities.fill(DiagnosticSeverity::Warning);
    }
    DiagnosticSeverity get(WarningId id) const {
        return severities[static_cast<size_t>(id)];
    }
    void set(WarningId id, DiagnosticSeverity severity) {
        severities[static_cast<size_t>(id)] = severity;
    }
};

struct FileSrc {
    int32_t file_id;
    SrcLoc offset;
    std::string file_name;
    std::string buffer;
    std::string modified_buffer;
    std::string directory;
    std::vector<uint32_t> line_offsets;
    std::vector<MappingStep> change_lists;
    struct LineDirective {
        uint32_t line_index_for_next;
        uint32_t line_number_for_next;
        std::string file_name;
        bool has_file_name;
    };
    std::vector<LineDirective> line_directives;
    bool pragma_once = false;
    bool include_guard_checked = false;
    bool initial_preprocessed = false;
    bool is_system_header = false;
    std::string resolved_path;
    std::string include_guard;

    FileSrc(std::string name, std::string content, int32_t file_id = -1)
        : file_name(std::move(name)), buffer(std::move(content)), file_id(file_id) {
        line_offsets.push_back(0);
        for (uint32_t i = 0; i < buffer.size(); ++i) {
            if (buffer[i] == '\n') line_offsets.push_back(i + 1);
        }
    }
};

struct MacroSrc {
    SrcLoc definition;
    SrcLoc caller;
    MacroSrc(const SrcLoc &definition, const SrcLoc &caller)
        : definition(definition),
          caller(caller) {
    }
    MacroSrc() {}
};
struct SLocEntry {
    uint32_t offset;
    bool is_expansion;

    std::shared_ptr<FileSrc> file_src;
    MacroSrc macro_src;
    static SLocEntry create_file(uint32_t offset, std::shared_ptr<FileSrc> file) {
        SLocEntry e;
        e.offset = offset;
        e.is_expansion = false;
        e.file_src = std::move(file);
        e.file_src->offset = SrcLoc(e.offset);
        return e;
    }

    static SLocEntry create_expansion(uint32_t offset, SrcLoc def, SrcLoc caller) {
        SLocEntry e;
        e.offset = offset;
        e.is_expansion = true;
        e.macro_src = MacroSrc(def, caller);
        return e;
    }
};
struct SourceManager {
    std::vector<SLocEntry> sloc_entry_table;
    std::vector<std::shared_ptr<FileSrc>> files;
    std::unordered_map<std::string, std::shared_ptr<FileSrc>> file_table;
    std::unordered_set<std::string> missing_file_table;
    std::vector<std::string> source_look_paths;
    std::vector<std::string> quote_look_paths;
    std::vector<std::string> framework_look_paths;
    std::unordered_map<std::string, std::shared_ptr<FileSrc>> include_search_cache;
    std::unordered_map<std::string, std::shared_ptr<FileSrc>> include_next_search_cache;
    std::unordered_map<std::string, std::shared_ptr<FileSrc>> quote_include_search_cache;
    std::unordered_map<std::string, std::shared_ptr<FileSrc>> quote_include_next_search_cache;
    struct DirEntrySet {
        enum class State { Missing, Unlistable, Listed };
        State state = State::Missing;
        bool exists() const { return state != State::Missing; }
        std::vector<uint64_t> folded_name_hashes;
        bool may_contain(uint64_t folded_hash) const;
    };
    std::unordered_map<std::string, DirEntrySet> dir_entry_cache;
    const DirEntrySet& directoryEntries(const std::string& dir_key);
    const std::string* include_search_paths_data = nullptr;
    size_t include_search_paths_size = 0;
    const std::string* quote_include_search_paths_data = nullptr;
    size_t quote_include_search_paths_size = 0;
    struct PragmaStateEntry {
        uint32_t offset;
        uint32_t pack_alignment;
        uint32_t diag_state_id;
    };
    std::vector<DiagnosticState> diagnostic_states;
    bool inhibit_warnings = false;
    mutable std::vector<PragmaStateEntry> pragma_state_table;
    mutable bool pragma_state_sorted_ = true;
    struct PragmaWeakDirective {
        std::string alias;
        std::string target;
        SrcLoc loc{};
    };
    std::vector<PragmaWeakDirective> pragma_weak_directives;
    struct PragmaVisibilityDirective {
        bool is_push = false;
        std::string value;
        SrcLoc loc{};
    };
    std::vector<PragmaVisibilityDirective> pragma_visibility_directives;
    bool cxx_stdlib_lookup_active = false;
    std::string requested_cxx_stdlib;
    std::string resolved_cxx_stdlib;
    std::vector<std::string> attempted_cxx_stdlib_paths;
    PerfProfiler* perf_profiler = nullptr;
    SpellingArena spellings;
    bool is_virtual_env = false;
    uint32_t next_offset = 1;

    SourceManager() {
        diagnostic_states.emplace_back();
    }
    std::shared_ptr<FileSrc> lookThroughPaths(const std::string& name);
    std::shared_ptr<FileSrc> lookThroughPathsFrom(const std::string& name, size_t start_index);
    std::shared_ptr<FileSrc> lookThroughQuotePaths(const std::string& name);
    std::shared_ptr<FileSrc> lookThroughQuotePathsFrom(const std::string& name, size_t start_index);
    std::shared_ptr<FileSrc> getFileFromLoc(const std::string& name, const std::string& directory,
                                            bool framework_only = false);

    std::shared_ptr<FileSrc> createFileEntry(std::string name, std::string content, std::string directory = "",
        std::string full_path_key = "");
    void ensureIncludeSearchCacheFresh();
    std::string makeIncludeSearchCacheKey(const std::string& name, size_t start_index) const;

    std::shared_ptr<FileSrc> getFileWithId(int32_t id) {
        if (id < 0 || id >= files.size()) {
            return nullptr;
        }
        return files[id];
    }
    void addLineDirective(int32_t file_id, uint32_t line_index_for_next,
        uint32_t line_number_for_next, std::string file_name, bool has_file_name) {
        auto file = getFileWithId(file_id);
        if (!file) return;
        file->line_directives.push_back({line_index_for_next, line_number_for_next, std::move(file_name), has_file_name});
    }
    SrcLoc createMacroEntry(SrcLoc def, SrcLoc caller, size_t size);
    uint32_t import_foreign_block(const SourceManager& source);

    uint32_t addDiagnosticState(DiagnosticState state) {
        diagnostic_states.push_back(std::move(state));
        return static_cast<uint32_t>(diagnostic_states.size() - 1);
    }
    const DiagnosticState& getDiagnosticStateById(uint32_t id) const {
        if (id >= diagnostic_states.size()) {
            return diagnostic_states[0];
        }
        return diagnostic_states[id];
    }
    uint32_t defaultDiagnosticStateId() const {
        return 0;
    }
    void recordPragmaState(SrcLoc loc, size_t pack_alignment, uint32_t diag_state_id);
    void ensure_pragma_state_sorted() const;
    size_t getPackAlignment(SrcLoc loc) const;
    const DiagnosticState& getDiagnosticState(SrcLoc loc) const;

    SrcLoc getRealSrcLoc(SLocEntry const& fil, SrcLoc loc) const;

    const SLocEntry& getEntryForLocation(SrcLoc loc) const;
    mutable size_t last_entry_lookup_ = 0;

    LogicalLocation getLogicalLocation(SrcLoc loc) const;
    std::string returnReportStr(SrcLoc loc) const;
    std::string formatLocation(SrcLoc loc) const;
    std::string formatDiagnostic(DiagnosticLevel level, const std::string& message, SrcLoc loc) const;
    std::string formatIncludeLookupFailure(const std::string& name) const;
};
#endif //ABURI_SOURCE_MGNT_H
