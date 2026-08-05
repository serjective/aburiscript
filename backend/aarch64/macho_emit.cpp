#include "macho_emit.h"

#include <algorithm>
#include <limits>
#include <set>

#include "encode.h"
#include "insts.h"
#include "target.h"

namespace aburi::backend::aarch64 {

namespace {

constexpr uint32_t CPU_TYPE_ARM64 = 0x0100000Cu;
constexpr uint32_t CPU_SUBTYPE_ARM64_ALL = 0;

constexpr uint32_t MACOS_MINOS = 26u << 16;

constexpr uint32_t S_REGULAR = 0x0;
constexpr uint32_t S_ZEROFILL = 0x1;
constexpr uint32_t S_CSTRING_LITERALS = 0x2;
constexpr uint32_t S_MOD_INIT_FUNC_POINTERS = 0x9;
constexpr uint32_t S_THREAD_LOCAL_REGULAR = 0x11;
constexpr uint32_t S_THREAD_LOCAL_ZEROFILL = 0x12;
constexpr uint32_t S_THREAD_LOCAL_VARIABLES = 0x13;
constexpr uint32_t S_ATTR_DEBUG = 0x02000000u;
constexpr uint32_t S_ATTR_PURE_INSTRUCTIONS = 0x80000000u;
constexpr uint32_t S_ATTR_SOME_INSTRUCTIONS = 0x00000400u;

constexpr uint32_t UNWIND_HAS_LSDA = 0x40000000u;
constexpr uint32_t UNWIND_ARM64_MODE_FRAME = 0x04000000u;
constexpr uint32_t UNWIND_ARM64_FRAME_X19_X20_PAIR = 0x00000001u;
constexpr uint32_t UNWIND_ARM64_FRAME_X21_X22_PAIR = 0x00000002u;
constexpr uint32_t UNWIND_ARM64_FRAME_X23_X24_PAIR = 0x00000004u;
constexpr uint32_t UNWIND_ARM64_FRAME_X25_X26_PAIR = 0x00000008u;
constexpr uint32_t UNWIND_ARM64_FRAME_X27_X28_PAIR = 0x00000010u;
constexpr uint32_t UNWIND_ARM64_FRAME_D8_D9_PAIR = 0x00000100u;
constexpr uint32_t UNWIND_ARM64_FRAME_D10_D11_PAIR = 0x00000200u;
constexpr uint32_t UNWIND_ARM64_FRAME_D12_D13_PAIR = 0x00000400u;
constexpr uint32_t UNWIND_ARM64_FRAME_D14_D15_PAIR = 0x00000800u;

constexpr uint64_t NO_LSDA = std::numeric_limits<uint64_t>::max();

std::string mach_symbol(const std::string& name, bool no_prefix) {
    return no_prefix ? name : "_" + name;
}

uint32_t p2align(uint32_t align_bytes) {
    uint32_t log2 = 0;
    while ((1u << log2) < align_bytes) {
        ++log2;
    }
    return log2;
}

uint64_t align_up(uint64_t value, uint64_t align) {
    return (value + align - 1) & ~(align - 1);
}

void append_u8(std::vector<uint8_t>& bytes, uint8_t value) {
    bytes.push_back(value);
}

void append_u32(std::vector<uint8_t>& bytes, uint32_t value) {
    for (int i = 0; i < 4; ++i) {
        bytes.push_back(static_cast<uint8_t>(value >> (8 * i)));
    }
}

void append_u64(std::vector<uint8_t>& bytes, uint64_t value) {
    for (int i = 0; i < 8; ++i) {
        bytes.push_back(static_cast<uint8_t>(value >> (8 * i)));
    }
}

size_t uleb_size(uint64_t value) {
    size_t size = 0;
    do {
        value >>= 7;
        ++size;
    } while (value != 0);
    return size;
}

void append_uleb(std::vector<uint8_t>& bytes, uint64_t value) {
    do {
        uint8_t byte = static_cast<uint8_t>(value & 0x7F);
        value >>= 7;
        if (value != 0) {
            byte |= 0x80;
        }
        bytes.push_back(byte);
    } while (value != 0);
}

void append_sleb(std::vector<uint8_t>& bytes, int64_t value) {
    bool more = true;
    while (more) {
        uint8_t byte = static_cast<uint8_t>(value & 0x7F);
        bool sign_bit = (byte & 0x40) != 0;
        value >>= 7;
        more = !((value == 0 && !sign_bit) || (value == -1 && sign_bit));
        if (more) {
            byte |= 0x80;
        }
        bytes.push_back(byte);
    }
}

void pad_to(std::vector<uint8_t>& bytes, uint64_t alignment) {
    while (bytes.size() % alignment != 0) {
        bytes.push_back(0);
    }
}

bool has_reg(const std::set<uint32_t>& regs, uint32_t reg) {
    return regs.find(reg) != regs.end();
}

uint32_t compact_unwind_encoding(const MFunction& function, bool has_lsda) {
    std::set<uint32_t> saved(function.used_csrs.begin(),
                             function.used_csrs.end());
    uint32_t encoding = UNWIND_ARM64_MODE_FRAME;
    if (has_reg(saved, X19) && has_reg(saved, X19 + 1)) {
        encoding |= UNWIND_ARM64_FRAME_X19_X20_PAIR;
    }
    if (has_reg(saved, X19 + 2) && has_reg(saved, X19 + 3)) {
        encoding |= UNWIND_ARM64_FRAME_X21_X22_PAIR;
    }
    if (has_reg(saved, X19 + 4) && has_reg(saved, X19 + 5)) {
        encoding |= UNWIND_ARM64_FRAME_X23_X24_PAIR;
    }
    if (has_reg(saved, X19 + 6) && has_reg(saved, X19 + 7)) {
        encoding |= UNWIND_ARM64_FRAME_X25_X26_PAIR;
    }
    if (has_reg(saved, X19 + 8) && has_reg(saved, X19 + 9)) {
        encoding |= UNWIND_ARM64_FRAME_X27_X28_PAIR;
    }
    if (has_reg(saved, V8) && has_reg(saved, V8 + 1)) {
        encoding |= UNWIND_ARM64_FRAME_D8_D9_PAIR;
    }
    if (has_reg(saved, V8 + 2) && has_reg(saved, V8 + 3)) {
        encoding |= UNWIND_ARM64_FRAME_D10_D11_PAIR;
    }
    if (has_reg(saved, V8 + 4) && has_reg(saved, V8 + 5)) {
        encoding |= UNWIND_ARM64_FRAME_D12_D13_PAIR;
    }
    if (has_reg(saved, V8 + 6) && has_reg(saved, V8 + 7)) {
        encoding |= UNWIND_ARM64_FRAME_D14_D15_PAIR;
    }
    if (has_lsda) {
        encoding |= UNWIND_HAS_LSDA;
    }
    return encoding;
}

uint8_t fixup_reloc_length(assembler::FixupKind kind) {
    return assembler::fixup_width_bytes(kind) == 8 ? 3 : 2;
}

bool fixup_reloc_type(assembler::FixupKind kind, SymFlavor flavor,
                      uint8_t& type, bool& pcrel) {
    switch (kind) {
        case assembler::FixupKind::Abs32:
        case assembler::FixupKind::Abs64:
            type = MACHO_ARM64_RELOC_UNSIGNED;
            pcrel = false;
            return true;
        case assembler::FixupKind::Branch26:
            type = MACHO_ARM64_RELOC_BRANCH26;
            pcrel = true;
            return true;
        case assembler::FixupKind::Page21:
            type = flavor == SymFlavor::GotPage
                       ? MACHO_ARM64_RELOC_GOT_LOAD_PAGE21
                   : flavor == SymFlavor::TlvPage
                       ? MACHO_ARM64_RELOC_TLVP_LOAD_PAGE21
                       : MACHO_ARM64_RELOC_PAGE21;
            pcrel = true;
            return true;
        case assembler::FixupKind::PageOff12:
            type = flavor == SymFlavor::GotPageOff
                       ? MACHO_ARM64_RELOC_GOT_LOAD_PAGEOFF12
                   : flavor == SymFlavor::TlvPageOff
                       ? MACHO_ARM64_RELOC_TLVP_LOAD_PAGEOFF12
                       : MACHO_ARM64_RELOC_PAGEOFF12;
            pcrel = false;
            return true;
        case assembler::FixupKind::GotDelta32:
            type = MACHO_ARM64_RELOC_POINTER_TO_GOT;
            pcrel = true;
            return true;
        default:

            return false;
    }
}

bool fragment_reloc_type(const assembler::FragmentReloc& reloc, uint8_t& type,
                         bool& pcrel) {
    switch (reloc.reloc_kind) {
        case assembler::RelocKind::Subtractor:
            type = MACHO_ARM64_RELOC_SUBTRACTOR;
            pcrel = false;
            return true;
        case assembler::RelocKind::PointerToGot:
            type = MACHO_ARM64_RELOC_POINTER_TO_GOT;
            pcrel = true;
            return true;
        default:
            return fixup_reloc_type(reloc.kind, reloc.flavor, type, pcrel);
    }
}

bool parse_block_label(const std::string& name, uint32_t& block) {
    if (name.rfind("LBB", 0) != 0) {
        return false;
    }
    size_t underscore = name.find('_', 3);
    if (underscore == std::string::npos ||
        underscore + 1 >= name.size()) {
        return false;
    }
    for (size_t i = underscore + 1; i < name.size(); ++i) {
        if (!std::isdigit(static_cast<unsigned char>(name[i]))) {
            return false;
        }
    }
    block = static_cast<uint32_t>(std::atoi(name.c_str() + underscore + 1));
    return true;
}

void patch_branch_at(MachOSection& section, uint64_t offset, bool branch26,
                     int64_t displacement) {
    uint32_t word = 0;
    for (int i = 0; i < 4; ++i) {
        word |= static_cast<uint32_t>(section.bytes[offset + i]) << (8 * i);
    }
    word = branch26 ? patch_branch26(word, displacement)
                    : patch_branch19(word, displacement);
    for (int i = 0; i < 4; ++i) {
        section.bytes[offset + i] = static_cast<uint8_t>(word >> (8 * i));
    }
}

std::string reloc_target_name(const air::Module& module,
                              const air::InitReloc& reloc) {
    if (reloc.is_function) {
        const air::Function& callee =
            module.function(air::FuncId{reloc.target_index});
        return mach_symbol(callee.name(), callee.attrs().no_prefix);
    }
    const air::GlobalData& global =
        module.global(air::GlobalId{reloc.target_index});
    return mach_symbol(global.name, global.attrs.no_prefix);
}

} // namespace

MachOEmitter::MachOEmitter(std::vector<Diagnostic>& diagnostics,
                           bool emit_unwind_tables)
    : diagnostics_(diagnostics),
      builder_(CPU_TYPE_ARM64, CPU_SUBTYPE_ARM64_ALL, MACOS_MINOS),
      emit_unwind_tables_(emit_unwind_tables) {}

void MachOEmitter::error(const std::string& message) {
    Diagnostic diag;
    diag.level = DiagnosticLevel::Error;
    diag.message = "air backend: " + message;
    diagnostics_.push_back(diag);
}

int MachOEmitter::text_section() {
    auto found = section_ids_.find("__TEXT,__text");
    if (found != section_ids_.end()) {
        return found->second;
    }
    int id = builder_.add_section(
        "__TEXT", "__text",
        S_REGULAR | S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS, 2);
    section_ids_["__TEXT,__text"] = id;
    return id;
}

int MachOEmitter::gcc_except_section() {
    auto found = section_ids_.find("__TEXT,__gcc_except_tab");
    if (found != section_ids_.end()) {
        return found->second;
    }
    int id = builder_.add_section("__TEXT", "__gcc_except_tab", S_REGULAR, 2);
    section_ids_["__TEXT,__gcc_except_tab"] = id;
    return id;
}

int MachOEmitter::compact_unwind_section() {
    auto found = section_ids_.find("__LD,__compact_unwind");
    if (found != section_ids_.end()) {
        return found->second;
    }
    int id = builder_.add_section("__LD", "__compact_unwind",
                                  S_REGULAR | S_ATTR_DEBUG, 3);
    section_ids_["__LD,__compact_unwind"] = id;
    return id;
}

int MachOEmitter::section_for_global(const air::GlobalData& global,
                                     bool has_relocs) {
    std::string segname;
    std::string sectname;
    uint32_t flags = S_REGULAR;
    bool zerofill = false;

    if (global.init.kind == air::GlobalInitKind::Zero) {
        segname = "__DATA";
        sectname = "__bss";
        flags = S_ZEROFILL;
        zerofill = true;
    } else {
        switch (global.section) {
            case air::SectionKind::Cstring:
                segname = "__TEXT";
                sectname = "__cstring";
                flags = S_CSTRING_LITERALS;
                break;
            case air::SectionKind::Const:
                segname = has_relocs ? "__DATA" : "__TEXT";
                sectname = "__const";
                break;
            case air::SectionKind::Text:
                segname = "__TEXT";
                sectname = "__const";
                break;
            case air::SectionKind::Custom: {
                std::string spec = global.custom_section;
                size_t comma = spec.find(',');
                if (comma == std::string::npos) {
                    error("custom section '" + spec +
                          "' is not SEGMENT,section");
                    segname = "__DATA";
                    sectname = "__data";
                    break;
                }
                segname = spec.substr(0, comma);
                std::string rest = spec.substr(comma + 1);
                size_t attrs = rest.find(',');
                sectname = attrs == std::string::npos ? rest
                                                      : rest.substr(0, attrs);
                while (attrs != std::string::npos) {
                    size_t next = rest.find(',', attrs + 1);
                    std::string token =
                        next == std::string::npos
                            ? rest.substr(attrs + 1)
                            : rest.substr(attrs + 1, next - attrs - 1);
                    if (!apply_macho_section_attribute(token, flags)) {
                        error("custom section '" + spec +
                              "' has an unsupported attribute '" + token +
                              "'");
                    }
                    attrs = next;
                }
                break;
            }
            case air::SectionKind::Data:
            case air::SectionKind::Zerofill:
                segname = "__DATA";
                sectname = "__data";
                break;
        }
    }

    std::string key = segname + "," + sectname;
    auto found = section_ids_.find(key);
    if (found != section_ids_.end()) {
        return found->second;
    }
    int id = builder_.add_section(segname, sectname, flags, 0, zerofill);
    section_ids_[key] = id;
    return id;
}

uint64_t MachOEmitter::emit_lsda(const MFunction& function,
                                 uint64_t function_end) {
    if (function.eh_call_sites.empty()) {
        return NO_LSDA;
    }

    std::map<uint32_t, uint64_t> action_offsets;
    std::vector<uint8_t> actions;
    for (const MEhAction& action : function.eh_actions) {
        action_offsets[action.label] = actions.size();
        append_sleb(actions, action.filter);
        uint64_t next_field_offset = actions.size();
        int64_t delta = 0;
        if (action.next_label != 0) {
            auto found = action_offsets.find(action.next_label);
            if (found == action_offsets.end()) {
                error("EH action chain references a forward or missing label");
                return NO_LSDA;
            }
            delta = static_cast<int64_t>(found->second) -
                    static_cast<int64_t>(next_field_offset);
        }
        append_sleb(actions, delta);
    }

    struct ResolvedCallSite {
        uint64_t begin = 0;
        uint64_t end = 0;
        uint64_t landing_pad = 0;
        uint64_t action = 0;
    };
    std::vector<ResolvedCallSite> sites;
    sites.reserve(function.eh_call_sites.size());
    for (const MEhCallSite& site : function.eh_call_sites) {
        auto begin = eh_label_offsets_.find(site.begin_label);
        auto end = eh_label_offsets_.find(site.end_label);
        auto landing_pad = block_offsets_.find(site.landing_pad_block);
        if (begin == eh_label_offsets_.end() ||
            end == eh_label_offsets_.end() ||
            landing_pad == block_offsets_.end()) {
            error("EH call-site metadata references an unemitted label");
            return NO_LSDA;
        }
        if (end->second < begin->second) {
            error("EH call-site range has negative length");
            return NO_LSDA;
        }
        uint64_t action_value = 0;
        if (site.action_label != 0) {
            auto action = action_offsets.find(site.action_label);
            if (action == action_offsets.end()) {
                error("EH call-site metadata references a missing action");
                return NO_LSDA;
            }
            action_value = action->second + 1;
        }
        sites.push_back(
            ResolvedCallSite{begin->second, end->second, landing_pad->second,
                             action_value});
    }
    std::sort(sites.begin(), sites.end(),
              [](const ResolvedCallSite& a, const ResolvedCallSite& b) {
                  return a.begin < b.begin;
              });

    std::vector<uint8_t> call_sites;
    auto append_range = [&](uint64_t begin, uint64_t end, uint64_t landing_pad,
                            uint64_t action, bool has_landing_pad) {
        if (end <= begin) {
            return;
        }
        append_uleb(call_sites, begin - current_function_start_);
        append_uleb(call_sites, end - begin);
        append_uleb(call_sites, has_landing_pad
                                    ? landing_pad - current_function_start_
                                    : 0);
        append_uleb(call_sites, action);
    };

    uint64_t previous = current_function_start_;
    for (const ResolvedCallSite& site : sites) {
        if (site.begin < previous) {
            error("EH call-site ranges overlap or are out of order");
            return NO_LSDA;
        }
        append_range(previous, site.begin, 0, 0, false);
        append_range(site.begin, site.end, site.landing_pad, site.action, true);
        previous = site.end;
    }
    append_range(previous, function_end, 0, 0, false);

    std::vector<MEhTypeInfo> typeinfos = function.eh_typeinfos;
    std::sort(typeinfos.begin(), typeinfos.end(),
              [](const MEhTypeInfo& a, const MEhTypeInfo& b) {
                  return a.filter > b.filter;
              });

    uint64_t ttype_value = 0;
    if (!typeinfos.empty()) {
        size_t ttype_uleb_bytes = 1;
        while (true) {
            uint64_t ttype_ref_offset = 2 + ttype_uleb_bytes;
            uint64_t cursor = ttype_ref_offset;
            cursor += 1;
            cursor += uleb_size(call_sites.size());
            cursor += call_sites.size();
            cursor += actions.size();
            cursor = align_up(cursor, 4);
            uint64_t ttype_base_offset = cursor + typeinfos.size() * 4;
            uint64_t candidate = ttype_base_offset - ttype_ref_offset;
            size_t candidate_size = uleb_size(candidate);
            if (candidate_size == ttype_uleb_bytes) {
                ttype_value = candidate;
                break;
            }
            ttype_uleb_bytes = candidate_size;
        }
    }

    int id = gcc_except_section();
    MachOSection& section = builder_.section(id);
    pad_to(section.bytes, 4);
    uint64_t lsda_start = section.bytes.size();
    MachOSymbol table_symbol;
    table_symbol.name = "GCC_except_table_air" + std::to_string(function.index);
    table_symbol.section = id;
    table_symbol.offset_in_section = lsda_start;
    table_symbol.external = false;
    builder_.add_symbol(std::move(table_symbol));

    std::vector<uint8_t> lsda;
    append_u8(lsda, 255);
    if (typeinfos.empty()) {
        append_u8(lsda, 255);
    } else {
        append_u8(lsda, 155);
        append_uleb(lsda, ttype_value);
    }
    append_u8(lsda, 1);
    append_uleb(lsda, call_sites.size());
    lsda.insert(lsda.end(), call_sites.begin(), call_sites.end());
    lsda.insert(lsda.end(), actions.begin(), actions.end());

    if (!typeinfos.empty()) {
        pad_to(lsda, 4);
        for (const MEhTypeInfo& typeinfo : typeinfos) {
            uint64_t entry_offset = lsda.size();
            uint64_t entry_section_offset = lsda_start + entry_offset;
            if (typeinfo.symbol.empty()) {
                append_u32(lsda, 0);
                continue;
            }
            append_u32(lsda,
                       0u - static_cast<uint32_t>(entry_section_offset));
            MachOReloc reloc;
            reloc.offset = entry_section_offset;
            reloc.symbol = typeinfo.symbol;
            reloc.type = MACHO_ARM64_RELOC_POINTER_TO_GOT;
            reloc.length = 2;
            reloc.pcrel = true;
            section.relocs.push_back(std::move(reloc));
        }
    }
    pad_to(lsda, 4);
    section.bytes.insert(section.bytes.end(), lsda.begin(), lsda.end());
    return lsda_start;
}

void MachOEmitter::queue_compact_unwind(const MFunction& function,
                                        uint64_t function_end,
                                        uint64_t lsda_offset, bool has_lsda) {
    uint64_t function_size = function_end - current_function_start_;
    if (function_size > std::numeric_limits<uint32_t>::max()) {
        error("function is too large for compact unwind metadata: " +
              function.name);
        return;
    }
    compact_unwind_rows_.push_back(PendingCompactUnwindRow{
        current_function_start_, function_end, lsda_offset,
        compact_unwind_encoding(function, has_lsda), has_lsda});
}

void MachOEmitter::emit_pending_compact_unwind() {
    if (compact_unwind_rows_.empty()) {
        return;
    }
    int id = compact_unwind_section();
    MachOSection& section = builder_.section(id);
    int text = text_section();
    int gcc_except = -1;

    for (const PendingCompactUnwindRow& row : compact_unwind_rows_) {
        uint64_t row_start = section.bytes.size();
        uint64_t function_size = row.function_end - row.function_start;
        append_u64(section.bytes, row.function_start);
        append_u32(section.bytes, static_cast<uint32_t>(function_size));
        append_u32(section.bytes, row.encoding);
        append_u64(section.bytes, 0);
        append_u64(section.bytes, row.has_lsda ? row.lsda_offset : 0);

        MachOReloc range_start;
        range_start.offset = row_start;
        range_start.section = text;
        range_start.type = MACHO_ARM64_RELOC_UNSIGNED;
        range_start.length = 3;
        range_start.external = false;
        section.relocs.push_back(std::move(range_start));

        if (!row.has_lsda) {
            continue;
        }

        if (gcc_except < 0) {
            gcc_except = gcc_except_section();
        }

        MachOReloc personality;
        personality.offset = row_start + 16;
        personality.symbol = "___gxx_personality_v0";
        personality.type = MACHO_ARM64_RELOC_UNSIGNED;
        personality.length = 3;
        section.relocs.push_back(std::move(personality));

        MachOReloc lsda;
        lsda.offset = row_start + 24;
        lsda.section = gcc_except;
        lsda.type = MACHO_ARM64_RELOC_UNSIGNED;
        lsda.length = 3;
        lsda.external = false;
        section.relocs.push_back(std::move(lsda));
    }
}

void MachOEmitter::begin_module(const air::Module& module) {
    target_ = module.target_ptr();
}

void MachOEmitter::emit_module_asm(const std::string& text) {
    splice_asm_fragment(text, /*inside_function=*/false);
}

void MachOEmitter::splice_asm_fragment(const std::string& text,
                                       bool inside_function) {
    assembler::AsmOptions options;
    options.target = target_;
    options.filename = "<inline asm>";
    assembler::FragmentResult fragment =
        assembler::assemble_fragment(text, options);
    for (const Diagnostic& diag : fragment.diagnostics) {
        diagnostics_.push_back(diag);
    }
    if (!fragment.ok) {
        return;
    }

    std::vector<int> section_ids(fragment.sections.size(), -1);
    std::vector<uint64_t> section_bases(fragment.sections.size(), 0);
    for (size_t i = 0; i < fragment.sections.size(); ++i) {
        assembler::FragmentSection& piece = fragment.sections[i];
        if (piece.bytes.empty() && piece.zerofill_size == 0 &&
            piece.symbols.empty()) {
            continue;
        }
        int id = -1;

        if (i == 0 && piece.segname == "__TEXT" &&
            piece.sectname == "__text") {
            id = text_section();
        } else {
            std::string key = piece.segname + "," + piece.sectname;
            auto found = section_ids_.find(key);
            if (found != section_ids_.end()) {
                id = found->second;
            } else {
                id = builder_.add_section(piece.segname, piece.sectname,
                                          piece.flags, piece.align_log2,
                                          piece.zerofill);
                section_ids_[key] = id;
            }
        }
        MachOSection& target = builder_.section(id);
        if (piece.align_log2 > target.align_log2) {
            target.align_log2 = piece.align_log2;
        }
        section_ids[i] = id;
        if (piece.zerofill) {
            section_bases[i] = target.zerofill_size;
            target.zerofill_size += piece.zerofill_size;
            continue;
        }
        section_bases[i] = target.bytes.size();
        target.bytes.insert(target.bytes.end(), piece.bytes.begin(),
                            piece.bytes.end());
    }

    std::map<std::string, std::pair<int, uint64_t>> fragment_labels;
    for (size_t i = 0; i < fragment.sections.size(); ++i) {
        if (section_ids[i] < 0) {
            continue;
        }
        for (const assembler::FragmentSymbol& label :
             fragment.sections[i].symbols) {
            uint64_t offset = section_bases[i] + label.offset;
            fragment_labels[label.name] = {section_ids[i], offset};
            MachOSymbol symbol;
            symbol.name = label.name;
            symbol.section = section_ids[i];
            symbol.offset_in_section = offset;
            symbol.external = label.global;
            symbol.weak_definition = label.weak;
            symbol.private_extern = label.hidden && label.global;
            builder_.add_symbol(std::move(symbol));
        }
    }
    for (const assembler::CommonSymbol& common : fragment.commons) {
        MachOCommon entry;
        entry.name = common.name;
        entry.size = common.size;
        entry.align_log2 = common.align_log2;
        builder_.add_common(std::move(entry));
    }

    for (size_t i = 0; i < fragment.sections.size(); ++i) {
        if (section_ids[i] < 0) {
            continue;
        }
        MachOSection& target = builder_.section(section_ids[i]);
        uint64_t base = section_bases[i];
        for (const assembler::FragmentReloc& reloc :
             fragment.sections[i].relocs) {
            MachOReloc out;
            out.offset = base + reloc.offset;
            out.length = fixup_reloc_length(reloc.kind);
            if (!fragment_reloc_type(reloc, out.type, out.pcrel)) {
                error("unsupported relocation in inline assembly");
                continue;
            }
            if (reloc.symbol.empty()) {
                out.external = false;
                out.section = reloc.section_index >= 0 &&
                              static_cast<size_t>(reloc.section_index) <
                                  section_ids.size()
                    ? section_ids[static_cast<size_t>(reloc.section_index)]
                    : section_ids[i];
            } else {
                out.external = true;
                out.symbol = reloc.symbol;
            }
            target.relocs.push_back(std::move(out));
        }

        for (const assembler::FragmentFixup& fixup :
             fragment.sections[i].unresolved) {
            uint64_t offset = base + fixup.offset;
            bool branch = fixup.kind == assembler::FixupKind::Branch26 ||
                          fixup.kind == assembler::FixupKind::Branch19;

            if (branch && inside_function &&
                section_ids[i] == text_section()) {
                if (fixup.symbol == current_function_symbol_) {
                    self_call_offsets_.push_back(offset);
                    continue;
                }
                uint32_t block = 0;
                if (parse_block_label(fixup.symbol, block)) {
                    PendingLabelFixup pending;
                    pending.word_offset = offset;
                    pending.branch26 =
                        fixup.kind == assembler::FixupKind::Branch26;
                    pending.target_block = block;
                    pending_labels_.push_back(pending);
                    continue;
                }
            }
            auto found = fragment_labels.find(fixup.symbol);
            if (found != fragment_labels.end() && branch &&
                found->second.first == section_ids[i]) {
                int64_t displacement =
                    static_cast<int64_t>(found->second.second) -
                    static_cast<int64_t>(offset);
                patch_branch_at(target, offset,
                                fixup.kind ==
                                    assembler::FixupKind::Branch26,
                                displacement);
                continue;
            }
            if (fixup.addend != 0) {
                error("symbol addend on an inline-asm operand is not "
                      "supported by the direct object writer: " +
                      fixup.symbol);
                continue;
            }
            MachOReloc out;
            out.offset = offset;
            out.symbol = fixup.symbol;
            out.external = true;
            out.length = fixup_reloc_length(fixup.kind);
            if (!fixup_reloc_type(fixup.kind, fixup.flavor, out.type,
                                  out.pcrel)) {
                error("unsupported inline-asm reference to '" +
                      fixup.symbol + "'");
                continue;
            }
            target.relocs.push_back(std::move(out));
        }
    }
}

void MachOEmitter::begin_function(const MFunction& function) {
    int text = text_section();
    MachOSection& section = builder_.section(text);

    MachOSymbol symbol;
    symbol.name = mach_symbol(function.name, function.attrs.no_prefix);
    symbol.section = text;
    symbol.offset_in_section = section.bytes.size();
    symbol.external = function.linkage != air::Linkage::Internal;
    symbol.weak_definition = function.linkage == air::Linkage::LinkOnceODR ||
                             function.linkage == air::Linkage::Weak;
    symbol.private_extern = function.attrs.hidden && symbol.external;
    current_function_symbol_ = symbol.name;
    current_function_start_ = symbol.offset_in_section;
    builder_.add_symbol(std::move(symbol));

    self_call_offsets_.clear();
    block_offsets_.clear();
    eh_label_offsets_.clear();
    pending_labels_.clear();
}

void MachOEmitter::emit_block_label(const MFunction& function,
                                    uint32_t block_index) {
    int text = text_section();
    MachOSection& section = builder_.section(text);
    block_offsets_[block_index] = section.bytes.size();
    if (function.blocks[block_index].address_taken) {
        MachOSymbol symbol;
        symbol.name = "l_air_lbl_" + std::to_string(function.index) + "_" +
                      std::to_string(block_index);
        symbol.section = text;
        symbol.offset_in_section = section.bytes.size();
        symbol.external = false;
        builder_.add_symbol(std::move(symbol));
    }
}

void MachOEmitter::emit_inst(const MFunction& function, const MInst& inst) {
    if (static_cast<A64Op>(inst.opcode) == A64Op::EhLabel) {
        int text = text_section();
        MachOSection& section = builder_.section(text);
        eh_label_offsets_[inst.aux] = section.bytes.size();
        return;
    }
    if (static_cast<A64Op>(inst.opcode) == A64Op::AsmBlock) {
        splice_asm_fragment(function.asm_texts[inst.aux],
                            /*inside_function=*/true);
        return;
    }
    int text = text_section();
    MachOSection& section = builder_.section(text);
    uint64_t word_offset = section.bytes.size();

    EncodedInst encoded = encode_a64(inst);
    if (!encoded.ok) {
        error("cannot encode instruction: " + encoded.error);
        return;
    }

    switch (encoded.fixup) {
        case TextFixup::None:
            break;
        case TextFixup::SymBranch26:
        case TextFixup::SymPage21:
        case TextFixup::SymPageOff12: {
            const MOperand& operand = inst.operands[encoded.fixup_operand];
            if (operand.addend != 0) {
                error("symbol addend on an instruction operand is not "
                      "supported by the direct object writer: " +
                      operand.symbol);
                return;
            }
            if (encoded.fixup == TextFixup::SymBranch26 &&
                operand.symbol == current_function_symbol_) {
                self_call_offsets_.push_back(word_offset);
                break;
            }
            MachOReloc reloc;
            reloc.offset = word_offset;
            reloc.symbol = operand.symbol;
            reloc.length = 2;
            switch (encoded.fixup) {
                case TextFixup::SymBranch26:
                    reloc.type = MACHO_ARM64_RELOC_BRANCH26;
                    reloc.pcrel = true;
                    break;
                case TextFixup::SymPage21:
                    reloc.type =
                        operand.flavor == SymFlavor::GotPage
                            ? MACHO_ARM64_RELOC_GOT_LOAD_PAGE21
                            : (operand.flavor == SymFlavor::TlvPage
                                   ? MACHO_ARM64_RELOC_TLVP_LOAD_PAGE21
                                   : MACHO_ARM64_RELOC_PAGE21);
                    reloc.pcrel = true;
                    break;
                default:
                    reloc.type =
                        operand.flavor == SymFlavor::GotPageOff
                            ? MACHO_ARM64_RELOC_GOT_LOAD_PAGEOFF12
                            : (operand.flavor == SymFlavor::TlvPageOff
                                   ? MACHO_ARM64_RELOC_TLVP_LOAD_PAGEOFF12
                                   : MACHO_ARM64_RELOC_PAGEOFF12);
                    reloc.pcrel = false;
                    break;
            }
            section.relocs.push_back(std::move(reloc));
            break;
        }
        case TextFixup::LabelBranch26:
        case TextFixup::LabelBranch19: {
            PendingLabelFixup fixup;
            fixup.word_offset = word_offset;
            fixup.branch26 = encoded.fixup == TextFixup::LabelBranch26;
            fixup.target_block = encoded.fixup_label;
            pending_labels_.push_back(fixup);
            break;
        }
    }

    for (int i = 0; i < 4; ++i) {
        section.bytes.push_back(
            static_cast<uint8_t>(encoded.word >> (8 * i)));
    }
}

void MachOEmitter::end_function(const MFunction& function) {
    int text = text_section();
    MachOSection& section = builder_.section(text);
    for (uint64_t offset : self_call_offsets_) {
        uint32_t word = 0;
        for (int i = 0; i < 4; ++i) {
            word |= static_cast<uint32_t>(section.bytes[offset + i]) << (8 * i);
        }
        word = patch_branch26(word,
                              static_cast<int64_t>(current_function_start_) -
                                  static_cast<int64_t>(offset));
        for (int i = 0; i < 4; ++i) {
            section.bytes[offset + i] = static_cast<uint8_t>(word >> (8 * i));
        }
    }
    self_call_offsets_.clear();
    for (const PendingLabelFixup& fixup : pending_labels_) {
        auto found = block_offsets_.find(fixup.target_block);
        if (found == block_offsets_.end()) {
            error("branch to an unemitted block label");
            continue;
        }
        int64_t displacement = static_cast<int64_t>(found->second) -
                               static_cast<int64_t>(fixup.word_offset);
        uint32_t word = 0;
        for (int i = 0; i < 4; ++i) {
            word |= static_cast<uint32_t>(
                        section.bytes[fixup.word_offset + i])
                    << (8 * i);
        }
        word = fixup.branch26 ? patch_branch26(word, displacement)
                              : patch_branch19(word, displacement);
        for (int i = 0; i < 4; ++i) {
            section.bytes[fixup.word_offset + i] =
                static_cast<uint8_t>(word >> (8 * i));
        }
    }
    pending_labels_.clear();
    uint64_t function_end = section.bytes.size();
    uint64_t lsda_offset = NO_LSDA;
    bool has_lsda = emit_unwind_tables_ && !function.eh_call_sites.empty();
    if (has_lsda) {
        lsda_offset = emit_lsda(function, function_end);
        has_lsda = lsda_offset != NO_LSDA;
    }
    if (emit_unwind_tables_) {
        queue_compact_unwind(function, function_end, lsda_offset, has_lsda);
    }
    block_offsets_.clear();
    eh_label_offsets_.clear();
}

void MachOEmitter::emit_global(const air::Module& module,
                               const air::GlobalData& global) {
    if (global.init.kind == air::GlobalInitKind::None) {
        return;
    }
    std::string symbol_name = mach_symbol(global.name, global.attrs.no_prefix);

    if (global.is_thread_local) {
        if (!global.init.relocs.empty()) {
            error("thread_local initializer relocations are not supported by "
                  "the direct Mach-O writer: " + global.name);
            return;
        }
        auto section = [&](std::string key, std::string seg,
                           std::string sect, uint32_t flags,
                           uint32_t align, bool zerofill = false) {
            auto found = section_ids_.find(key);
            if (found != section_ids_.end()) {
                return found->second;
            }
            int id = builder_.add_section(std::move(seg), std::move(sect),
                                          flags, align, zerofill);
            section_ids_[std::move(key)] = id;
            return id;
        };
        bool zero = global.init.kind == air::GlobalInitKind::Zero;
        int storage_id = zero
            ? section("__DATA,__thread_bss", "__DATA", "__thread_bss",
                      S_THREAD_LOCAL_ZEROFILL,
                      p2align(global.align_bytes), true)
            : section("__DATA,__thread_data", "__DATA", "__thread_data",
                      S_THREAD_LOCAL_REGULAR,
                      p2align(global.align_bytes));
        MachOSection& storage_section = builder_.section(storage_id);
        uint64_t storage_offset;
        if (zero) {
            storage_section.zerofill_size = align_up(
                storage_section.zerofill_size, global.align_bytes);
            storage_offset = storage_section.zerofill_size;
            storage_section.zerofill_size += global.size_bytes;
        } else {
            storage_offset =
                align_up(storage_section.bytes.size(), global.align_bytes);
            storage_section.bytes.resize(storage_offset, 0);
            storage_section.bytes.insert(storage_section.bytes.end(),
                                         global.init.bytes.begin(),
                                         global.init.bytes.end());
            storage_section.bytes.resize(storage_offset + global.size_bytes,
                                         0);
        }
        std::string storage_symbol = symbol_name + "$tlv$init";
        MachOSymbol storage;
        storage.name = storage_symbol;
        storage.section = storage_id;
        storage.offset_in_section = storage_offset;
        builder_.add_symbol(std::move(storage));

        int vars_id = section("__DATA,__thread_vars", "__DATA",
                              "__thread_vars", S_THREAD_LOCAL_VARIABLES, 3);
        MachOSection& vars = builder_.section(vars_id);
        size_t descriptor_offset = align_up(vars.bytes.size(), 8);
        vars.bytes.resize(descriptor_offset + 24, 0);
        MachOSymbol descriptor;
        descriptor.name = symbol_name;
        descriptor.section = vars_id;
        descriptor.offset_in_section = descriptor_offset;
        descriptor.external = global.linkage != air::Linkage::Internal;
        descriptor.weak_definition =
            global.linkage == air::Linkage::LinkOnceODR ||
            global.linkage == air::Linkage::Weak;
        descriptor.private_extern = global.attrs.hidden && descriptor.external;
        builder_.add_symbol(std::move(descriptor));
        MachOReloc bootstrap;
        bootstrap.offset = descriptor_offset;
        bootstrap.symbol = "__tlv_bootstrap";
        bootstrap.type = MACHO_ARM64_RELOC_UNSIGNED;
        bootstrap.length = 3;
        vars.relocs.push_back(std::move(bootstrap));
        MachOReloc initial;
        initial.offset = descriptor_offset + 16;
        initial.symbol = storage_symbol;
        initial.type = MACHO_ARM64_RELOC_UNSIGNED;
        initial.length = 3;
        vars.relocs.push_back(std::move(initial));
        return;
    }

    if (global.linkage == air::Linkage::Common) {
        MachOCommon common;
        common.name = symbol_name;
        common.size = global.size_bytes;
        common.align_log2 = p2align(global.align_bytes);
        builder_.add_common(std::move(common));
        return;
    }

    int id = section_for_global(global, !global.init.relocs.empty());
    MachOSection& section = builder_.section(id);
    uint32_t align_log2 = p2align(global.align_bytes);
    if (align_log2 > section.align_log2) {
        section.align_log2 = align_log2;
    }

    MachOSymbol symbol;
    symbol.name = symbol_name;
    symbol.section = id;
    symbol.external = global.linkage != air::Linkage::Internal;
    symbol.weak_definition = global.linkage == air::Linkage::LinkOnceODR ||
                             global.linkage == air::Linkage::Weak;
    symbol.private_extern = global.attrs.hidden && symbol.external;

    if (global.init.kind == air::GlobalInitKind::Zero) {
        section.zerofill_size =
            align_up(section.zerofill_size, global.align_bytes);
        symbol.offset_in_section = section.zerofill_size;
        section.zerofill_size += global.size_bytes;
        builder_.add_symbol(std::move(symbol));
        return;
    }

    size_t start = align_up(section.bytes.size(), global.align_bytes);
    section.bytes.resize(start, 0);
    symbol.offset_in_section = start;
    builder_.add_symbol(std::move(symbol));

    section.bytes.insert(section.bytes.end(), global.init.bytes.begin(),
                         global.init.bytes.end());
    if (global.init.bytes.size() < global.size_bytes) {
        section.bytes.resize(start + global.size_bytes, 0);
    }

    for (const air::InitReloc& reloc : global.init.relocs) {
        size_t hole = start + reloc.offset;
        if (hole + 8 > section.bytes.size()) {
            error("initializer relocation outside its global: " + global.name);
            continue;
        }
        uint64_t addend = static_cast<uint64_t>(reloc.addend);
        for (int i = 0; i < 8; ++i) {
            section.bytes[hole + i] = static_cast<uint8_t>(addend >> (8 * i));
        }
        MachOReloc record;
        record.offset = hole;
        record.symbol = reloc_target_name(module, reloc);
        record.type = MACHO_ARM64_RELOC_UNSIGNED;
        record.length = 3;
        record.pcrel = false;
        section.relocs.push_back(std::move(record));
    }
}

void MachOEmitter::emit_ctor_list(const air::Module& module) {
    if (module.ctors().empty()) {
        return;
    }
    std::string key = "__DATA,__mod_init_func";
    int id;
    auto found = section_ids_.find(key);
    if (found != section_ids_.end()) {
        id = found->second;
    } else {
        id = builder_.add_section("__DATA", "__mod_init_func",
                                  S_MOD_INIT_FUNC_POINTERS, 3);
        section_ids_[key] = id;
    }
    MachOSection& section = builder_.section(id);
    for (const air::CtorEntry& ctor : module.ctors()) {
        const air::Function& function = module.function(ctor.func);
        MachOReloc record;
        record.offset = section.bytes.size();
        record.symbol = mach_symbol(function.name(),
                                    function.attrs().no_prefix);
        record.type = MACHO_ARM64_RELOC_UNSIGNED;
        record.length = 3;
        record.pcrel = false;
        section.relocs.push_back(std::move(record));
        for (int i = 0; i < 8; ++i) {
            section.bytes.push_back(0);
        }
    }
}

void MachOEmitter::end_module(const air::Module& module) {
    (void)module;
    if (emit_unwind_tables_) {
        emit_pending_compact_unwind();
    }
}

bool MachOEmitter::write(std::ostream& out) {
    std::string write_error;
    if (!builder_.write(out, write_error)) {
        error("cannot write object file: " + write_error);
        return false;
    }
    return true;
}

} // namespace aburi::backend::aarch64
