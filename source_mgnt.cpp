#include "source_mgnt.h"
#include "perf_stats.h"
#include <algorithm>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <optional>
#include <sstream>
#include <string_view>
#include <dirent.h>
#include <unistd.h>

static std::string normalize_path(const std::filesystem::path& p) {
    if (p.is_absolute()) {
        return p.lexically_normal().string();
    }

    static const std::filesystem::path cached_cwd = [] {
        std::error_code ec;
        auto cwd = std::filesystem::current_path(ec);
        return ec ? std::filesystem::path(".") : cwd;
    }();
    return (cached_cwd / p).lexically_normal().string();
}

static uint64_t folded_name_hash(std::string_view name) {
    uint64_t hash = 1469598103934665603ull;
    for (char c : name) {
        if (c >= 'A' && c <= 'Z') {
            c = static_cast<char>(c - 'A' + 'a');
        }
        hash ^= static_cast<unsigned char>(c);
        hash *= 1099511628211ull;
    }
    return hash;
}

static std::optional<std::filesystem::path> resolve_framework_header_path(
    const std::filesystem::path& include_name,
    const std::filesystem::path& search_dir) {
    if (include_name.is_absolute() || include_name.empty()) {
        return std::nullopt;
    }

    auto it = include_name.begin();
    if (it == include_name.end()) {
        return std::nullopt;
    }
    std::string framework_name = (*it).string();
    ++it;
    if (it == include_name.end()) {
        return std::nullopt;
    }

    std::filesystem::path remainder;
    for (; it != include_name.end(); ++it) {
        remainder /= *it;
    }
    if (remainder.empty()) {
        return std::nullopt;
    }

    const char* header_dirs[] = {"Headers", "PrivateHeaders"};
    for (const char* header_dir : header_dirs) {
        std::filesystem::path candidate =
            search_dir / (framework_name + ".framework") / header_dir / remainder;
        std::error_code ec;
        if (std::filesystem::exists(candidate, ec) &&
            std::filesystem::is_regular_file(candidate, ec)) {
            return candidate;
        }
    }
    return std::nullopt;
}

namespace {
bool should_use_color() {
    const char* no_color = std::getenv("NO_COLOR");
    if (no_color && *no_color != '\0') {
        return false;
    }
    const char* term = std::getenv("TERM");
    if (!term || std::string(term) == "dumb") {
        return false;
    }
    return ::isatty(STDERR_FILENO);
}

std::string colorize(const std::string& text, const char* color, bool enable) {
    if (!enable) {
        return text;
    }
    return std::string(color) + text + "\x1b[0m";
}

const char* level_color(DiagnosticLevel level) {
    switch (level) {
        case DiagnosticLevel::Error:
            return "\x1b[1;31m";
        case DiagnosticLevel::Warning:
            return "\x1b[1;33m";
        case DiagnosticLevel::Note:
            return "\x1b[1;34m";
    }
    return "";
}
} // namespace

void SourceManager::ensureIncludeSearchCacheFresh() {
    if (include_search_paths_size == source_look_paths.size() &&
        include_search_paths_data == source_look_paths.data() &&
        quote_include_search_paths_size == quote_look_paths.size() &&
        quote_include_search_paths_data == quote_look_paths.data()) {
        return;
    }
    include_search_paths_size = source_look_paths.size();
    include_search_paths_data = source_look_paths.data();
    quote_include_search_paths_size = quote_look_paths.size();
    quote_include_search_paths_data = quote_look_paths.data();
    include_search_cache.clear();
    include_next_search_cache.clear();
    quote_include_search_cache.clear();
    quote_include_next_search_cache.clear();
}

std::string SourceManager::makeIncludeSearchCacheKey(const std::string& name, size_t start_index) const {
    std::string key;
    key.reserve(name.size() + 32);
    key += std::to_string(start_index);
    key.push_back('\n');
    key += name;
    return key;
}

std::string SourceManager::formatIncludeLookupFailure(const std::string& name) const {
    std::string message = "couldn't find file " + name;
    if (!cxx_stdlib_lookup_active) {
        return message;
    }

    message += "\nnote: C++ stdlib selection: requested '" +
               (requested_cxx_stdlib.empty() ? "auto" : requested_cxx_stdlib) + "'";
    if (!resolved_cxx_stdlib.empty() && resolved_cxx_stdlib != requested_cxx_stdlib) {
        message += ", resolved '" + resolved_cxx_stdlib + "'";
    }

    if (attempted_cxx_stdlib_paths.empty()) {
        message += "\nnote: no auto-discovered C++ stdlib roots were found";
        return message;
    }

    message += "\nnote: searched C++ stdlib roots:";
    for (const auto& path : attempted_cxx_stdlib_paths) {
        message += "\nnote:   " + path;
    }
    return message;
}

std::shared_ptr<FileSrc> SourceManager::lookThroughPaths(const std::string& name) {
    PerfScopedTimer timer(perf_profiler, PerfPhase::IncludeSearch);
    ensureIncludeSearchCacheFresh();
    auto cache_it = include_search_cache.find(name);
    if (cache_it != include_search_cache.end()) {
        if (perf_profiler) {
            perf_profiler->add_counter(PerfCounter::IncludeSearchCacheHits);
        }
        return cache_it->second;
    }
    if (perf_profiler) {
        perf_profiler->add_counter(PerfCounter::IncludeSearchCacheMisses);
    }
    for (const auto& path : framework_look_paths) {
        if (auto file = getFileFromLoc(name, path, /*framework_only=*/true)) {
            include_search_cache.emplace(name, file);
            return file;
        }
    }
    for (const auto& path : source_look_paths) {
        if (auto file = getFileFromLoc(name, path)) {
            include_search_cache.emplace(name, file);
            return file;
        }
    }
    return nullptr;
}

std::shared_ptr<FileSrc> SourceManager::lookThroughPathsFrom(const std::string& name, size_t start_index) {
    PerfScopedTimer timer(perf_profiler, PerfPhase::IncludeSearch);
    ensureIncludeSearchCacheFresh();
    const std::string cache_key = makeIncludeSearchCacheKey(name, start_index);
    auto cache_it = include_next_search_cache.find(cache_key);
    if (cache_it != include_next_search_cache.end()) {
        if (perf_profiler) {
            perf_profiler->add_counter(PerfCounter::IncludeNextSearchCacheHits);
        }
        return cache_it->second;
    }
    if (perf_profiler) {
        perf_profiler->add_counter(PerfCounter::IncludeNextSearchCacheMisses);
    }
    for (size_t i = start_index; i < source_look_paths.size(); ++i) {
        if (auto file = getFileFromLoc(name, source_look_paths[i])) {
            include_next_search_cache.emplace(cache_key, file);
            return file;
        }
    }
    return nullptr;
}

std::shared_ptr<FileSrc> SourceManager::lookThroughQuotePaths(const std::string& name) {
    PerfScopedTimer timer(perf_profiler, PerfPhase::IncludeSearch);
    ensureIncludeSearchCacheFresh();
    auto cache_it = quote_include_search_cache.find(name);
    if (cache_it != quote_include_search_cache.end()) {
        if (perf_profiler) {
            perf_profiler->add_counter(PerfCounter::QuoteIncludeSearchCacheHits);
        }
        return cache_it->second;
    }
    if (perf_profiler) {
        perf_profiler->add_counter(PerfCounter::QuoteIncludeSearchCacheMisses);
    }
    for (const auto& path : quote_look_paths) {
        if (auto file = getFileFromLoc(name, path)) {
            quote_include_search_cache.emplace(name, file);
            return file;
        }
    }

    return nullptr;
}

std::shared_ptr<FileSrc> SourceManager::lookThroughQuotePathsFrom(const std::string& name, size_t start_index) {
    PerfScopedTimer timer(perf_profiler, PerfPhase::IncludeSearch);
    ensureIncludeSearchCacheFresh();
    const std::string cache_key = makeIncludeSearchCacheKey(name, start_index);
    auto cache_it = quote_include_next_search_cache.find(cache_key);
    if (cache_it != quote_include_next_search_cache.end()) {
        if (perf_profiler) {
            perf_profiler->add_counter(PerfCounter::QuoteIncludeNextSearchCacheHits);
        }
        return cache_it->second;
    }
    if (perf_profiler) {
        perf_profiler->add_counter(PerfCounter::QuoteIncludeNextSearchCacheMisses);
    }
    for (size_t i = start_index; i < quote_look_paths.size(); ++i) {
        if (auto file = getFileFromLoc(name, quote_look_paths[i])) {
            quote_include_next_search_cache.emplace(cache_key, file);
            return file;
        }
    }
    return nullptr;
}

bool SourceManager::DirEntrySet::may_contain(uint64_t folded_hash) const {
    if (state == State::Missing) {
        return false;
    }
    if (state == State::Unlistable) {
        return true;
    }
    return std::binary_search(folded_name_hashes.begin(),
                              folded_name_hashes.end(), folded_hash);
}

const SourceManager::DirEntrySet& SourceManager::directoryEntries(const std::string& dir_key) {
    auto it = dir_entry_cache.find(dir_key);
    if (it != dir_entry_cache.end()) {
        return it->second;
    }
    DirEntrySet set;
    DIR* dir = ::opendir(dir_key.empty() ? "." : dir_key.c_str());
    if (dir) {
        set.state = DirEntrySet::State::Listed;
        while (dirent* entry = ::readdir(dir)) {
            set.folded_name_hashes.push_back(folded_name_hash(entry->d_name));
        }
        ::closedir(dir);
        std::sort(set.folded_name_hashes.begin(), set.folded_name_hashes.end());
    } else if (errno != ENOENT && errno != ENOTDIR) {

        set.state = DirEntrySet::State::Unlistable;
    }
    if (perf_profiler) {
        perf_profiler->add_counter(PerfCounter::DirEntryCacheBuilds);
    }
    return dir_entry_cache.emplace(dir_key, std::move(set)).first->second;
}

std::shared_ptr<FileSrc> SourceManager::getFileFromLoc(const std::string& name, const std::string& directory,
                                                       bool framework_only) {
    std::filesystem::path name_path(name);
    std::filesystem::path full_path;
    if (name_path.is_absolute()) {
        full_path = name_path;
    } else if (directory.empty()) {
        full_path = name_path;
    } else {
        full_path = std::filesystem::path(directory) / name_path;
    }
    std::string key = normalize_path(full_path);
    if (framework_only) {

        key += "\x01""fw";
    }
    auto it = file_table.find(key);
    if (it != file_table.end()) {
        return it->second;
    }
    if (missing_file_table.contains(key)) {
        if (perf_profiler) {
            perf_profiler->add_counter(PerfCounter::MissingFileCacheHits);
        }
        return nullptr;
    }
    if (is_virtual_env) {
        return nullptr;
    }
    auto load_file = [&](const std::filesystem::path& path, const std::string& path_key) -> std::shared_ptr<FileSrc> {
        PerfScopedTimer timer(perf_profiler, PerfPhase::SourceRead);
        if (perf_profiler) {
            perf_profiler->add_counter(PerfCounter::FileOpenAttempts);
        }
        std::ifstream input_file(path, std::ios::binary | std::ios::ate);
        if (!input_file.is_open()) {
            if (perf_profiler) {
                perf_profiler->add_counter(PerfCounter::FileOpenFailures);
            }
            return nullptr;
        }
        std::streamsize size = input_file.tellg();
        if (size < 0) {
            if (perf_profiler) {
                perf_profiler->add_counter(PerfCounter::FileOpenFailures);
            }
            return nullptr;
        }
        std::string content(static_cast<size_t>(size), '\0');
        input_file.seekg(0, std::ios::beg);
        if (size > 0) {
            input_file.read(content.data(), size);
            if (!input_file) {
                content.resize(static_cast<size_t>(input_file.gcount()));
            }
        }
        missing_file_table.erase(key);
        std::string actual_dir = path.parent_path().string();
        auto entry = createFileEntry(name, std::move(content), actual_dir, path_key);
        entry->resolved_path = path.lexically_normal().string();
        return entry;
    };

    bool may_resolve_plain = !framework_only;
    bool may_resolve_framework = false;
    if (!name_path.is_absolute()) {
        auto first_component = name_path.begin();
        bool multi_component =
            first_component != name_path.end() &&
            std::next(first_component) != name_path.end();
        std::string first =
            first_component != name_path.end() ? first_component->string()
                                               : std::string();
        const DirEntrySet& search_entries = directoryEntries(directory);
        may_resolve_plain =
            !framework_only && search_entries.exists() &&
            (first.empty() || search_entries.may_contain(folded_name_hash(first)));
        may_resolve_framework =
            multi_component && search_entries.exists() &&
            search_entries.may_contain(folded_name_hash(first + ".framework"));
        if (!may_resolve_plain && !may_resolve_framework) {
            if (perf_profiler) {
                perf_profiler->add_counter(PerfCounter::DirEntryCacheSkips);
            }
            missing_file_table.insert(key);
            return nullptr;
        }
    }

    if (may_resolve_plain) {
        if (auto file = load_file(full_path, key)) {
            return file;
        }
    }

    if (!name_path.is_absolute()) {
        if (!may_resolve_framework) {
            if (perf_profiler) {
                perf_profiler->add_counter(PerfCounter::FrameworkProbesSkipped);
            }
            missing_file_table.insert(key);
            return nullptr;
        }
        if (perf_profiler) {
            perf_profiler->add_counter(PerfCounter::FrameworkLookupAttempts);
        }
        auto framework_path = resolve_framework_header_path(name_path, std::filesystem::path(directory));
        if (framework_path.has_value()) {
            if (perf_profiler) {
                perf_profiler->add_counter(PerfCounter::FrameworkLookupHits);
            }
            std::string framework_key = normalize_path(*framework_path);
            auto loaded = file_table.find(framework_key);
            if (loaded != file_table.end()) {
                return loaded->second;
            }
            if (auto file = load_file(*framework_path, framework_key)) {
                return file;
            }
        }
    }

    missing_file_table.insert(key);
    return nullptr;

}

std::shared_ptr<FileSrc> SourceManager::createFileEntry(std::string name, std::string content, std::string directory,
    std::string full_path_key) {
    auto shared_ptr = std::make_shared<FileSrc>(name, std::move(content), files.size());
    shared_ptr->directory = directory;
    files.push_back(shared_ptr);
    std::string table_key = std::move(full_path_key);
    if (table_key.empty()) {
        if (directory.empty()) {
            table_key = name;
        } else {
            table_key = normalize_path(std::filesystem::path(directory) / std::filesystem::path(name));
        }
    }
    file_table[table_key] = shared_ptr;
    missing_file_table.erase(table_key);
    if (perf_profiler) {
        perf_profiler->add_counter(PerfCounter::FilesLoaded);
        perf_profiler->add_counter(PerfCounter::SourceBytes, shared_ptr->buffer.size());
    }

    uint32_t offset = next_offset;
    sloc_entry_table.push_back(SLocEntry::create_file(offset, files.back()));
    next_offset += files.back()->buffer.size() + 1;
    return shared_ptr;
}

SrcLoc SourceManager::createMacroEntry(SrcLoc def, SrcLoc caller, size_t size) {
    uint32_t offset = next_offset;
    sloc_entry_table.push_back(SLocEntry::create_expansion(offset, def, caller));
    next_offset += size + 1;
    return {offset};

}

uint32_t SourceManager::import_foreign_block(const SourceManager& source) {

    uint32_t delta = next_offset - 1;
    next_offset += source.next_offset - 1;
    auto rebase = [delta](SrcLoc loc) {
        return loc.isInvalid() ? loc : SrcLoc(loc.offset + delta);
    };
    for (const SLocEntry& entry : source.sloc_entry_table) {
        if (entry.is_expansion) {
            sloc_entry_table.push_back(SLocEntry::create_expansion(
                entry.offset + delta,
                rebase(entry.macro_src.definition),
                rebase(entry.macro_src.caller)));
            continue;
        }

        auto file_clone = std::make_shared<FileSrc>(*entry.file_src);
        file_clone->file_id = static_cast<int32_t>(files.size());
        files.push_back(file_clone);
        sloc_entry_table.push_back(
            SLocEntry::create_file(entry.offset + delta, std::move(file_clone)));
    }

    uint32_t diag_base = static_cast<uint32_t>(diagnostic_states.size());
    for (size_t i = 1; i < source.diagnostic_states.size(); ++i) {
        diagnostic_states.push_back(source.diagnostic_states[i]);
    }
    source.ensure_pragma_state_sorted();
    for (const PragmaStateEntry& entry : source.pragma_state_table) {
        uint32_t diag_id = entry.diag_state_id == 0
            ? 0
            : diag_base + (entry.diag_state_id - 1);
        pragma_state_table.push_back(
            {entry.offset + delta, entry.pack_alignment, diag_id});
    }
    pragma_state_sorted_ = false;
    return delta;
}

static const SourceManager::PragmaStateEntry* find_pragma_state(
    const std::vector<SourceManager::PragmaStateEntry>& table, uint32_t offset) {
    if (table.empty()) {
        return nullptr;
    }
    auto it = std::upper_bound(table.begin(), table.end(), offset,
        [](uint32_t value, const SourceManager::PragmaStateEntry& entry) {
            return value < entry.offset;
        });
    if (it == table.begin()) {
        return nullptr;
    }
    --it;
    return &(*it);
}

void SourceManager::recordPragmaState(SrcLoc loc, size_t pack_alignment, uint32_t diag_state_id) {
    if (loc.isInvalid()) {
        return;
    }
    uint32_t offset = loc.offset;
    uint32_t pack = static_cast<uint32_t>(pack_alignment);
    if (!pragma_state_table.empty()) {
        auto& last = pragma_state_table.back();
        if (last.offset == offset) {
            last.pack_alignment = pack;
            last.diag_state_id = diag_state_id;
            pragma_state_sorted_ = false;
            return;
        }

        if (offset == last.offset + 1 &&
            last.pack_alignment == pack &&
            last.diag_state_id == diag_state_id) {
            return;
        }
    }
    pragma_state_table.push_back({offset, pack, diag_state_id});
    pragma_state_sorted_ = false;
}

void SourceManager::ensure_pragma_state_sorted() const {
    if (pragma_state_sorted_) {
        return;
    }
    std::stable_sort(pragma_state_table.begin(), pragma_state_table.end(),
        [](const PragmaStateEntry& a, const PragmaStateEntry& b) {
            return a.offset < b.offset;
        });
    std::vector<PragmaStateEntry> collapsed;
    collapsed.reserve(pragma_state_table.size());
    for (const auto& entry : pragma_state_table) {
        if (!collapsed.empty() && collapsed.back().offset == entry.offset) {

            collapsed.back() = entry;
            continue;
        }
        if (!collapsed.empty() &&
            collapsed.back().pack_alignment == entry.pack_alignment &&
            collapsed.back().diag_state_id == entry.diag_state_id) {

            continue;
        }
        collapsed.push_back(entry);
    }
    pragma_state_table.swap(collapsed);
    pragma_state_sorted_ = true;
}

size_t SourceManager::getPackAlignment(SrcLoc loc) const {
    if (loc.isInvalid()) {
        return 0;
    }
    ensure_pragma_state_sorted();
    auto entry = find_pragma_state(pragma_state_table, loc.offset);
    if (!entry) {
        return 0;
    }
    return static_cast<size_t>(entry->pack_alignment);
}

const DiagnosticState& SourceManager::getDiagnosticState(SrcLoc loc) const {
    if (loc.isInvalid()) {
        return diagnostic_states[0];
    }
    ensure_pragma_state_sorted();
    auto entry = find_pragma_state(pragma_state_table, loc.offset);
    if (!entry) {
        return diagnostic_states[0];
    }
    return getDiagnosticStateById(entry->diag_state_id);
}

SrcLoc SourceManager::getRealSrcLoc(SLocEntry const &fil, SrcLoc loc) const {
    if (loc.isInvalid()) {
        return loc;
    }
    if (!fil.is_expansion) {

        if (!fil.file_src->change_lists.empty()) {

            auto local_idx_orig = loc.offset - fil.offset;
            auto it2 = std::upper_bound(fil.file_src->change_lists.begin(),
                                        fil.file_src->change_lists.end(), local_idx_orig,
                                        [](uint32_t idx, const MappingStep& entry) {
                                            return idx < entry.logical_index;
                                        });
            auto idx_entry = *(--it2);
            uint32_t diff = local_idx_orig - idx_entry.logical_index;
            uint32_t real_idx = idx_entry.physical_offset + diff;
            return {fil.offset + real_idx};

        }
    }
    return loc;
}

const SLocEntry & SourceManager::getEntryForLocation(SrcLoc loc) const {

    if (last_entry_lookup_ < sloc_entry_table.size()) {
        const SLocEntry& cached = sloc_entry_table[last_entry_lookup_];
        uint32_t end = last_entry_lookup_ + 1 < sloc_entry_table.size()
                           ? sloc_entry_table[last_entry_lookup_ + 1].offset
                           : next_offset;
        if (loc.offset >= cached.offset && loc.offset < end) {
            return cached;
        }
    }
    auto it = std::upper_bound(sloc_entry_table.begin(),
                               sloc_entry_table.end(), loc.offset,
                               [](uint32_t id, const SLocEntry& entry) {
                                   return id < entry.offset;
                               });
    --it;
    last_entry_lookup_ =
        static_cast<size_t>(it - sloc_entry_table.begin());
    return *it;
}

LogicalLocation SourceManager::getLogicalLocation(SrcLoc loc) const {
    if (loc.isInvalid()) {
        return {"", 0, 0};
    }
    const SLocEntry& entry = getEntryForLocation(loc);
    if (entry.is_expansion) {
        return getLogicalLocation(entry.macro_src.caller);
    }
    SrcLoc real_loc = getRealSrcLoc(entry, loc);
    uint32_t localOffset = real_loc.offset - entry.offset;
    const auto& lines = entry.file_src->line_offsets;

    auto it = std::upper_bound(lines.begin(),
                               lines.end(), localOffset);
    uint32_t lineIdx = std::distance(lines.begin(), it) - 1;
    uint32_t colIdx = localOffset - lines[lineIdx];
    uint32_t reported_line = lineIdx + 1;
    std::string reported_file = entry.file_src->file_name;
    if (!entry.file_src->line_directives.empty()) {
        const FileSrc::LineDirective* active = nullptr;
        for (const auto& d : entry.file_src->line_directives) {
            if (d.line_index_for_next <= lineIdx) {
                active = &d;
            } else {
                break;
            }
        }
        if (active) {
            reported_line = active->line_number_for_next + (lineIdx - active->line_index_for_next);
            if (active->has_file_name) {
                reported_file = active->file_name;
            }
        }
    }
    return {reported_file, reported_line, colIdx + 1};
}

std::string SourceManager::returnReportStr(SrcLoc loc) const {
    const SLocEntry& entry = getEntryForLocation(loc);
    SrcLoc real_loc = getRealSrcLoc(entry, loc);
    std::string ret = "";

    if (entry.is_expansion) {
        ret += "In expansion of macro: \n";

        ret += returnReportStr(entry.macro_src.caller) + "\n";

        ret += "Defined as: \n";
        ret += returnReportStr(entry.macro_src.definition) + "\n";
        return ret;
    } else {
        uint32_t localOffset = real_loc.offset - entry.offset;
        const auto& lines = entry.file_src->line_offsets;

        auto it = std::upper_bound(lines.begin(),
                                   lines.end(), localOffset);
        uint32_t lineIdx = std::distance(lines.begin(), it) - 1;
        uint32_t colIdx = localOffset - lines[lineIdx];
        uint32_t reported_line = lineIdx + 1;
        std::string reported_file = entry.file_src->file_name;
        if (!entry.file_src->line_directives.empty()) {
            const FileSrc::LineDirective* active = nullptr;
            for (const auto& d : entry.file_src->line_directives) {
                if (d.line_index_for_next <= lineIdx) {
                    active = &d;
                } else {
                    break;
                }
            }
            if (active) {
                reported_line = active->line_number_for_next + (lineIdx - active->line_index_for_next);
                if (active->has_file_name) {
                    reported_file = active->file_name;
                }
            }
        }

        ret += reported_file + ":"
                + std::to_string(reported_line) + ":" + std::to_string(colIdx + 1);
        return ret;
    }
}

std::string SourceManager::formatLocation(SrcLoc loc) const {
    if (loc.isInvalid()) {
        return "<unknown>";
    }
    LogicalLocation logical = getLogicalLocation(loc);
    if (logical.file.empty()) {
        return "<unknown>";
    }
    return logical.file + ":" + std::to_string(logical.line) + ":" + std::to_string(logical.column);
}

std::string SourceManager::formatDiagnostic(DiagnosticLevel level, const std::string& message, SrcLoc loc) const {
    const bool use_color = should_use_color();
    const char* lvl_color = level_color(level);
    const std::string level_text = (level == DiagnosticLevel::Error)
        ? "error"
        : (level == DiagnosticLevel::Warning) ? "warning" : "note";
    const std::string level_label = colorize(level_text, lvl_color, use_color);

    if (loc.isInvalid()) {
        return level_label + ": " + message;
    }

    std::vector<SrcLoc> macro_defs;
    SrcLoc display_loc = loc;
    const SLocEntry* entry = &getEntryForLocation(display_loc);
    while (entry->is_expansion) {
        macro_defs.push_back(entry->macro_src.definition);
        display_loc = entry->macro_src.caller;
        entry = &getEntryForLocation(display_loc);
    }

    LogicalLocation logical = getLogicalLocation(display_loc);
    if (logical.file.empty()) {
        return level_label + ": " + message;
    }

    std::ostringstream out;
    out << logical.file << ":" << logical.line << ":" << logical.column << ": "
        << level_label << ": " << message << "\n";

    std::string line_text;
    uint32_t col_idx = 0;
    if (entry->file_src) {
        SrcLoc real_loc = getRealSrcLoc(*entry, display_loc);
        uint32_t local_offset = real_loc.offset - entry->offset;
        const auto& lines = entry->file_src->line_offsets;
        if (!lines.empty()) {
            auto it = std::upper_bound(lines.begin(), lines.end(), local_offset);
            uint32_t line_idx = std::distance(lines.begin(), it) - 1;
            uint32_t line_start = lines[line_idx];
            uint32_t line_end = (line_idx + 1 < lines.size())
                ? lines[line_idx + 1]
                : static_cast<uint32_t>(entry->file_src->buffer.size());
            if (line_end > line_start && line_end <= entry->file_src->buffer.size()) {
                line_text = entry->file_src->buffer.substr(line_start, line_end - line_start);
                if (!line_text.empty() && line_text.back() == '\n') {
                    line_text.pop_back();
                }
                if (!line_text.empty() && line_text.back() == '\r') {
                    line_text.pop_back();
                }
            }
            col_idx = local_offset - line_start;
        }
    }

    if (!line_text.empty()) {
        if (col_idx > line_text.size()) {
            col_idx = static_cast<uint32_t>(line_text.size());
        }
        const std::string line_no = std::to_string(logical.line);
        const std::string gutter(line_no.size(), ' ');
        const std::string caret = colorize("^", lvl_color, use_color);
        out << " " << line_no << " | " << line_text << "\n";
        out << " " << gutter << " | " << std::string(col_idx, ' ') << caret << "\n";
    }

    if (!macro_defs.empty()) {
        const std::string note_label = colorize("note", level_color(DiagnosticLevel::Note), use_color);
        for (const auto& def_loc : macro_defs) {
            std::string def_str = formatLocation(def_loc);
            if (def_str == "<unknown>") {
                continue;
            }
            out << def_str << ": " << note_label << ": macro defined here\n";
        }
    }

    return out.str();
}
