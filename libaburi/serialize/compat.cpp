#include "compat.h"

#include "../../source_mgnt.h"
#include "format.h"

namespace aburi::serialize {

uint64_t hash_bytes(std::string_view bytes) {
    uint64_t hash = 1469598103934665603ull;
    for (unsigned char byte : bytes) {
        hash ^= byte;
        hash *= 1099511628211ull;
    }
    return hash;
}

CompatIdentity CompatIdentity::build(
    std::string_view compiler_version,
    std::string_view target_triple,
    const LangOptions& lang_options,
    const std::vector<std::pair<std::string, std::string>>& defines,
    const std::vector<std::string>& undefines) {
    std::string text;
    auto line = [&text](std::string_view key, std::string_view value) {
        text += key;
        text += ": ";
        text += value;
        text += '\n';
    };
    line("compiler", compiler_version);
    line("format",
         std::to_string(kArtifactFormatVersion));
    line("target", target_triple);
    line("std", lang_options.standard.empty() ? "<default>"
                                              : lang_options.standard);
    line("language", lang_options.is_cxx_mode() ? "c++" : "c");
    auto flag = [&line](std::string_view key, bool value) {
        line(key, value ? "1" : "0");
    };

    flag("reflection", lang_options.enable_cpp_reflection);
    flag("exceptions", lang_options.exceptions_enabled);
    flag("c23-constexpr", lang_options.enable_c23_constexpr);
    flag("blocks", lang_options.blocks_mode == BlocksMode::Enabled);
    flag("implicit-int", lang_options.implicit_int);
    flag("kr-definitions", lang_options.kr_style_definitions);
    flag("pattern-cloning", lang_options.template_pattern_cloning);

    for (const auto& [name, value] : defines) {
        line("define", name + "=" + value);
    }
    for (const std::string& name : undefines) {
        line("undefine", name);
    }
    CompatIdentity identity;
    identity.hash = hash_bytes(text);
    identity.text = std::move(text);
    return identity;
}

std::string describe_compat_mismatch(std::string_view ours,
                                     std::string_view theirs) {
    size_t our_pos = 0;
    size_t their_pos = 0;
    auto next_line = [](std::string_view text, size_t& pos) {
        if (pos >= text.size()) {
            return std::string_view();
        }
        size_t end = text.find('\n', pos);
        if (end == std::string_view::npos) {
            end = text.size();
        }
        std::string_view result = text.substr(pos, end - pos);
        pos = end + 1;
        return result;
    };
    while (our_pos < ours.size() || their_pos < theirs.size()) {
        std::string_view our_line = next_line(ours, our_pos);
        std::string_view their_line = next_line(theirs, their_pos);
        if (our_line != their_line) {
            std::string message = "option mismatch: this compile has '";
            message += our_line.empty() ? "<absent>" : our_line;
            message += "', the artifact was built with '";
            message += their_line.empty() ? "<absent>" : their_line;
            message += "'";
            return message;
        }
    }
    return {};
}

std::string write_dependency_section(const SourceManager& source_manager) {
    ByteWriter writer;
    uint32_t count = 0;
    for (const auto& file : source_manager.files) {
        if (file && !file->resolved_path.empty()) {
            ++count;
        }
    }
    writer.u32(count);
    for (const auto& file : source_manager.files) {
        if (!file || file->resolved_path.empty()) {
            continue;
        }
        writer.sized_string(file->resolved_path);
        writer.u64(file->buffer.size());
        writer.u64(hash_bytes(file->buffer));
    }
    return writer.take();
}

std::vector<DependencyRecord> read_dependency_section(std::string_view bytes) {
    std::vector<DependencyRecord> records;
    ByteReader reader(bytes);
    uint32_t count = reader.u32();
    for (uint32_t i = 0; i < count && reader.ok(); ++i) {
        DependencyRecord record;
        record.path = std::string(reader.sized_string());
        record.size = reader.u64();
        record.content_hash = reader.u64();
        if (reader.ok()) {
            records.push_back(std::move(record));
        }
    }
    return records;
}

} // namespace aburi::serialize
