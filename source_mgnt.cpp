#include "source_mgnt.h"
#include <algorithm>
#include <cstdlib>
#include <filesystem>
#include <optional>
#include <unistd.h>

static std::string normalize_path(const std::filesystem::path& p) {
    std::error_code ec;
    auto abs = std::filesystem::absolute(p, ec);
    if (!ec) {
        return abs.lexically_normal().string();
    }
    return p.lexically_normal().string();
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

std::shared_ptr<FileSrc> SourceManager::lookThroughPaths(const std::string& name) {
    ensureIncludeSearchCacheFresh();
    auto cache_it = include_search_cache.find(name);
    if (cache_it != include_search_cache.end()) {
        return cache_it->second;
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
    ensureIncludeSearchCacheFresh();
    const std::string cache_key = makeIncludeSearchCacheKey(name, start_index);
    auto cache_it = include_next_search_cache.find(cache_key);
    if (cache_it != include_next_search_cache.end()) {
        return cache_it->second;
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
    ensureIncludeSearchCacheFresh();
    auto cache_it = quote_include_search_cache.find(name);
    if (cache_it != quote_include_search_cache.end()) {
        return cache_it->second;
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
    ensureIncludeSearchCacheFresh();
    const std::string cache_key = makeIncludeSearchCacheKey(name, start_index);
    auto cache_it = quote_include_next_search_cache.find(cache_key);
    if (cache_it != quote_include_next_search_cache.end()) {
        return cache_it->second;
    }
    for (size_t i = start_index; i < quote_look_paths.size(); ++i) {
        if (auto file = getFileFromLoc(name, quote_look_paths[i])) {
            quote_include_next_search_cache.emplace(cache_key, file);
            return file;
        }
    }
    return nullptr;
}

std::shared_ptr<FileSrc> SourceManager::getFileFromLoc(const std::string& name, const std::string& directory) {
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
    auto it = file_table.find(key);
    if (it != file_table.end()) {
        return it->second;
    }
    if (missing_file_table.contains(key)) {
        return nullptr;
    }
    if (is_virtual_env) {
        return nullptr;
    }
    auto load_file = [&](const std::filesystem::path& path, const std::string& path_key) -> std::shared_ptr<FileSrc> {
        std::ifstream input_file(path, std::ios::binary | std::ios::ate);
        if (!input_file.is_open()) {
            return nullptr;
        }
        std::streamsize size = input_file.tellg();
        if (size < 0) {
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
        return createFileEntry(name, std::move(content), actual_dir, path_key);
    };

    if (auto file = load_file(full_path, key)) {
        return file;
    }

    if (!name_path.is_absolute()) {
        auto framework_path = resolve_framework_header_path(name_path, std::filesystem::path(directory));
        if (framework_path.has_value()) {
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
    auto shared_ptr = std::make_shared<FileSrc>(name, content, files.size());
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

    uint32_t offset = next_offset;
    sloc_entry_table.push_back(SLocEntry::create_file(offset, files.back()));
    next_offset += files.back()->buffer.size() + 1; // +1 for null terminator/gap
    return shared_ptr;
}

SrcLoc SourceManager::createMacroEntry(SrcLoc def, SrcLoc caller, size_t size) {
    uint32_t offset = next_offset;
    sloc_entry_table.push_back(SLocEntry::create_expansion(offset, def, caller));
    next_offset += size + 1;
    return {offset};

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
            return;
        }
        if (last.pack_alignment == pack && last.diag_state_id == diag_state_id) {
            return;
        }
    }
    pragma_state_table.push_back({offset, pack, diag_state_id});
}

size_t SourceManager::getPackAlignment(SrcLoc loc) const {
    if (loc.isInvalid()) {
        return 0;
    }
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
        // file
        if (!fil.file_src->change_lists.empty()) {
            // we want the highest index in change_lists
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
    auto it = std::upper_bound(sloc_entry_table.begin(),
                               sloc_entry_table.end(), loc.offset,
                               [](uint32_t id, const SLocEntry& entry) {
                                   return id < entry.offset;
                               });
    return *(--it);
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
        // Recursively resolve the expansion site
        ret += returnReportStr(entry.macro_src.caller) + "\n";
        // Also point to the definition
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
