#include "bmi.h"

#include <unordered_map>
#include <utility>

#include "../../cir/graph_serialize.h"
#include "../../collect/collect.h"
#include "../../preprocessor.h"
#include "format.h"

namespace aburi::serialize {

namespace {

struct TokenRecord {
    uint16_t type;
    uint8_t literal_prefix;
    uint8_t flags;
    uint32_t loc;
    uint32_t blob_offset;
    uint32_t blob_size;
};

constexpr uint8_t kFlagStartOfLine = 1;
constexpr uint8_t kFlagLeadingSpace = 2;

std::string write_meta(const aburi::modules::LoadedModuleUnit& unit) {
    ByteWriter writer;
    writer.u8(static_cast<uint8_t>(unit.kind));
    writer.sized_string(unit.module_name);
    writer.sized_string(unit.partition_name);
    return writer.take();
}

std::string write_sloc(const SourceManager& sm) {
    ByteWriter writer;
    writer.u32(sm.next_offset);
    writer.u32(static_cast<uint32_t>(sm.sloc_entry_table.size()));
    for (const SLocEntry& entry : sm.sloc_entry_table) {
        writer.u8(entry.is_expansion ? 1 : 0);
        writer.u32(entry.offset);
        if (entry.is_expansion) {
            writer.u32(entry.macro_src.definition.offset);
            writer.u32(entry.macro_src.caller.offset);
            continue;
        }
        const FileSrc& file = *entry.file_src;
        writer.sized_string(file.file_name);
        writer.sized_string(file.resolved_path);
        writer.sized_string(file.directory);
        writer.u8(file.is_system_header ? 1 : 0);
        writer.sized_string(file.buffer);
        writer.u32(static_cast<uint32_t>(file.line_directives.size()));
        for (const FileSrc::LineDirective& directive : file.line_directives) {
            writer.u32(directive.line_index_for_next);
            writer.u32(directive.line_number_for_next);
            writer.sized_string(directive.file_name);
            writer.u8(directive.has_file_name ? 1 : 0);
        }
    }
    sm.ensure_pragma_state_sorted();
    writer.u32(static_cast<uint32_t>(sm.diagnostic_states.size()));
    for (const DiagnosticState& state : sm.diagnostic_states) {
        for (size_t i = 0; i < state.severities.size(); ++i) {
            writer.u8(static_cast<uint8_t>(
                state.severities[static_cast<size_t>(i)]));
        }
    }
    writer.u32(static_cast<uint32_t>(sm.pragma_state_table.size()));
    for (const SourceManager::PragmaStateEntry& entry :
         sm.pragma_state_table) {
        writer.u32(entry.offset);
        writer.u32(entry.pack_alignment);
        writer.u32(entry.diag_state_id);
    }
    return writer.take();
}

bool read_sloc(ByteReader& reader, SourceManager& sm) {
    sm.next_offset = reader.u32();
    uint32_t entry_count = reader.u32();
    for (uint32_t i = 0; i < entry_count && reader.ok(); ++i) {
        bool is_expansion = reader.u8() != 0;
        uint32_t offset = reader.u32();
        if (is_expansion) {
            SrcLoc definition{reader.u32()};
            SrcLoc caller{reader.u32()};
            sm.sloc_entry_table.push_back(
                SLocEntry::create_expansion(offset, definition, caller));
            continue;
        }
        std::string file_name(reader.sized_string());
        std::string resolved_path(reader.sized_string());
        std::string directory(reader.sized_string());
        bool is_system = reader.u8() != 0;
        std::string buffer(reader.sized_string());
        auto file = std::make_shared<FileSrc>(
            std::move(file_name), std::move(buffer),
            static_cast<int32_t>(sm.files.size()));
        file->resolved_path = std::move(resolved_path);
        file->directory = std::move(directory);
        file->is_system_header = is_system;
        uint32_t directive_count = reader.u32();
        for (uint32_t d = 0; d < directive_count && reader.ok(); ++d) {
            FileSrc::LineDirective directive;
            directive.line_index_for_next = reader.u32();
            directive.line_number_for_next = reader.u32();
            directive.file_name = std::string(reader.sized_string());
            directive.has_file_name = reader.u8() != 0;
            file->line_directives.push_back(std::move(directive));
        }

        ensure_initial_preprocessed(file);
        sm.files.push_back(file);
        sm.sloc_entry_table.push_back(
            SLocEntry::create_file(offset, std::move(file)));
    }
    uint32_t diag_count = reader.u32();
    sm.diagnostic_states.clear();
    for (uint32_t i = 0; i < diag_count && reader.ok(); ++i) {
        DiagnosticState state;
        for (size_t s = 0; s < state.severities.size(); ++s) {
            state.severities[s] = static_cast<DiagnosticSeverity>(reader.u8());
        }
        sm.diagnostic_states.push_back(state);
    }
    if (sm.diagnostic_states.empty()) {
        sm.diagnostic_states.emplace_back();
    }
    uint32_t pragma_count = reader.u32();
    for (uint32_t i = 0; i < pragma_count && reader.ok(); ++i) {
        SourceManager::PragmaStateEntry entry;
        entry.offset = reader.u32();
        entry.pack_alignment = reader.u32();
        entry.diag_state_id = reader.u32();
        sm.pragma_state_table.push_back(entry);
    }
    return reader.ok();
}

} // namespace

std::string write_module_artifact(const aburi::modules::LoadedModuleUnit& unit,
                                  const SourceManager& source_manager,
                                  const CompatIdentity& identity) {
    ArtifactWriter artifact(identity.hash);
    artifact.add_section(kSectionCompat, identity.text);
    artifact.add_section(kSectionMeta, write_meta(unit));
    artifact.add_section(kSectionDeps,
                         write_dependency_section(source_manager));
    artifact.add_section(kSectionSourceLocs, write_sloc(source_manager));

    std::string blob;
    std::unordered_map<std::string_view, uint32_t> interned;
    ByteWriter tokens;
    tokens.u32(static_cast<uint32_t>(unit.tokens ? unit.tokens->size() : 0));
    if (unit.tokens) {
        for (const Token& token : *unit.tokens) {
            uint32_t blob_offset = 0;
            if (!token.value.empty()) {
                auto found = interned.find(token.value);
                if (found != interned.end()) {
                    blob_offset = found->second;
                } else {
                    blob_offset = static_cast<uint32_t>(blob.size());
                    blob.append(token.value.data(), token.value.size());
                    interned.emplace(token.value, blob_offset);
                }
            }
            tokens.u16(static_cast<uint16_t>(token.type));
            tokens.u8(static_cast<uint8_t>(token.literal_prefix));
            uint8_t flags = 0;
            if (token.flags.start_of_line) {
                flags |= kFlagStartOfLine;
            }
            if (token.flags.has_leading_space) {
                flags |= kFlagLeadingSpace;
            }
            tokens.u8(flags);
            tokens.u32(token.loc.offset);
            tokens.u32(blob_offset);
            tokens.u32(static_cast<uint32_t>(token.value.size()));
        }
    }
    artifact.add_section(kSectionTokens, tokens.take());
    artifact.add_section(kSectionSpellings, std::move(blob));
    artifact.add_section(kSectionMacros, std::string());

    if (unit.cir != nullptr && unit.template_state != nullptr &&
        cir::module_graph_serializable(*unit.cir)) {
        std::string graph_bytes;
        if (cir::write_module_graph(*unit.cir, graph_bytes)) {
            std::string template_bytes;
            collect::Session::serialize_template_state(
                unit.template_state.get(), template_bytes);
            artifact.add_section(kSectionGraph, std::move(graph_bytes));
            artifact.add_section(kSectionTemplates,
                                 std::move(template_bytes));
        }
    }
    return artifact.finish();
}

SerializedUnit::SerializedUnit() = default;
SerializedUnit::~SerializedUnit() = default;

std::unique_ptr<SerializedUnit> read_module_artifact(
    std::string_view bytes, const CompatIdentity& expected,
    std::shared_ptr<TargetInfo> target) {
    auto result = std::make_unique<SerializedUnit>();
    ArtifactView view = ArtifactView::parse(bytes);
    if (!view.valid) {
        result->error = "not a valid module artifact";
        return result;
    }
    result->compat_hash = view.compat_hash;
    result->compat_text = std::string(view.section(kSectionCompat));
    if (view.compat_hash != expected.hash) {
        std::string mismatch =
            describe_compat_mismatch(expected.text, result->compat_text);
        result->error = mismatch.empty()
            ? "module artifact was built with incompatible options"
            : "module artifact was built with incompatible options: " +
                  mismatch;
        return result;
    }

    ByteReader meta(view.section(kSectionMeta));
    result->unit.kind = static_cast<aburi::modules::ScannedUnitKind>(meta.u8());
    result->unit.module_name = std::string(meta.sized_string());
    result->unit.partition_name = std::string(meta.sized_string());
    if (!meta.ok()) {
        result->error = "module artifact metadata is truncated";
        return result;
    }
    result->dependencies =
        read_dependency_section(view.section(kSectionDeps));

    result->source_manager = std::make_shared<SourceManager>();
    ByteReader sloc(view.section(kSectionSourceLocs));
    if (!read_sloc(sloc, *result->source_manager)) {
        result->error = "module artifact source table is truncated";
        return result;
    }

    result->spelling_blob = std::string(view.section(kSectionSpellings));
    ByteReader tokens(view.section(kSectionTokens));
    uint32_t token_count = tokens.u32();
    result->tokens.reserve(token_count);
    for (uint32_t i = 0; i < token_count && tokens.ok(); ++i) {
        Token token;
        token.type = static_cast<TokenType>(tokens.u16());
        token.literal_prefix = static_cast<LiteralPrefix>(tokens.u8());
        uint8_t flags = tokens.u8();
        token.flags.start_of_line = (flags & kFlagStartOfLine) ? 1 : 0;
        token.flags.has_leading_space = (flags & kFlagLeadingSpace) ? 1 : 0;
        token.loc = SrcLoc(tokens.u32());
        uint32_t blob_offset = tokens.u32();
        uint32_t blob_size = tokens.u32();
        if (blob_size > 0) {
            if (blob_offset > result->spelling_blob.size() ||
                blob_size >
                    result->spelling_blob.size() - blob_offset) {
                result->error = "module artifact token table is corrupt";
                return result;
            }
            token.value = std::string_view(
                result->spelling_blob.data() + blob_offset, blob_size);
        }
        result->tokens.push_back(token);
    }
    if (!tokens.ok()) {
        result->error = "module artifact token table is truncated";
        return result;
    }
    result->unit.tokens = &result->tokens;
    result->unit.source_manager = result->source_manager;
    result->unit.cir = nullptr;

    if (target != nullptr) {
        std::string_view graph_bytes = view.section(kSectionGraph);
        std::string_view template_bytes = view.section(kSectionTemplates);
        if (!graph_bytes.empty() && !template_bytes.empty()) {
            result->graph =
                cir::read_module_graph(graph_bytes, std::move(target));
            if (result->graph) {
                result->template_state =
                    collect::Session::deserialize_template_state(
                        template_bytes);
            }
            if (result->graph && result->template_state) {
                result->unit.cir = result->graph.get();
                result->unit.template_state = result->template_state;
            } else {
                result->graph.reset();
                result->template_state.reset();
            }
        }
    }
    result->valid = true;
    return result;
}

} // namespace aburi::serialize
