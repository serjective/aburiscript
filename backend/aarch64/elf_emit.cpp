#include "elf_emit.h"

#include "elf_unwind.h"

#include <algorithm>
#include <cctype>
#include <cstdlib>

#include "encode.h"
#include "insts.h"
#include "target.h"

namespace aburi::backend::aarch64 {

namespace {

uint64_t align_up(uint64_t value, uint64_t align) {
    return (value + align - 1) & ~(align - 1);
}

uint32_t pageoff_reloc_type(A64Op op) {
    switch (op) {
        case A64Op::AddXsym:
            return ELF_R_AARCH64_ADD_ABS_LO12_NC;
        case A64Op::LdrbW:
        case A64Op::LdrsbW:
        case A64Op::StrbW:
            return ELF_R_AARCH64_LDST8_ABS_LO12_NC;
        case A64Op::LdrhW:
        case A64Op::LdrshW:
        case A64Op::StrhW:
            return ELF_R_AARCH64_LDST16_ABS_LO12_NC;
        case A64Op::LdrW:
        case A64Op::Ldrsw:
        case A64Op::StrW:
        case A64Op::LdrS:
        case A64Op::StrS:
            return ELF_R_AARCH64_LDST32_ABS_LO12_NC;
        case A64Op::LdrX:
        case A64Op::StrX:
        case A64Op::LdrD:
        case A64Op::StrD:
            return ELF_R_AARCH64_LDST64_ABS_LO12_NC;
        case A64Op::LdrQ:
        case A64Op::StrQ:
            return ELF_R_AARCH64_LDST128_ABS_LO12_NC;
        default:
            return ELF_R_AARCH64_ADD_ABS_LO12_NC;
    }
}

std::string reloc_target_name(const air::Module& module,
                              const air::InitReloc& reloc) {
    if (reloc.is_function) {
        return module.function(air::FuncId{reloc.target_index}).name();
    }
    return module.global(air::GlobalId{reloc.target_index}).name;
}

} // namespace

namespace {

uint32_t fragment_reloc_type(assembler::FixupKind kind, SymFlavor flavor,
                             uint8_t access_bytes, bool& ok) {
    ok = true;
    switch (kind) {
        case assembler::FixupKind::Abs64:
            return ELF_R_AARCH64_ABS64;
        case assembler::FixupKind::Abs32:
            return ELF_R_AARCH64_ABS32;
        case assembler::FixupKind::Branch26:
            return ELF_R_AARCH64_CALL26;
        case assembler::FixupKind::Page21:
            return flavor == SymFlavor::GotPage ? ELF_R_AARCH64_ADR_GOT_PAGE
                                                : ELF_R_AARCH64_ADR_PREL_PG_HI21;
        case assembler::FixupKind::PageOff12:
            if (flavor == SymFlavor::GotPageOff) {
                return ELF_R_AARCH64_LD64_GOT_LO12_NC;
            }
            switch (access_bytes) {
                case 1: return ELF_R_AARCH64_LDST8_ABS_LO12_NC;
                case 2: return ELF_R_AARCH64_LDST16_ABS_LO12_NC;
                case 4: return ELF_R_AARCH64_LDST32_ABS_LO12_NC;
                case 8: return ELF_R_AARCH64_LDST64_ABS_LO12_NC;
                case 16: return ELF_R_AARCH64_LDST128_ABS_LO12_NC;
                default: return ELF_R_AARCH64_ADD_ABS_LO12_NC;
            }
        default:

            ok = false;
            return 0;
    }
}

bool parse_block_label(const std::string& name, uint32_t& block) {
    if (name.rfind(".LBB", 0) != 0) {
        return false;
    }
    size_t underscore = name.find('_', 4);
    if (underscore == std::string::npos || underscore + 1 >= name.size()) {
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

} // namespace

namespace {
constexpr uint64_t NO_ELF_LSDA = ~uint64_t{0};
}

int ElfEmitter::eh_frame_section() {
    auto found = section_ids_.find(".eh_frame");
    if (found != section_ids_.end()) {
        return found->second;
    }
    int id = builder_.add_section(".eh_frame", ELF_SHT_PROGBITS,
                                  ELF_SHF_ALLOC, 8);
    section_ids_[".eh_frame"] = id;
    return id;
}

int ElfEmitter::gcc_except_section() {
    auto found = section_ids_.find(".gcc_except_table");
    if (found != section_ids_.end()) {
        return found->second;
    }
    int id = builder_.add_section(".gcc_except_table", ELF_SHT_PROGBITS,
                                  ELF_SHF_ALLOC, 4);
    section_ids_[".gcc_except_table"] = id;
    return id;
}

std::string ElfEmitter::dw_ref_symbol(const std::string& symbol) {
    std::string name = "DW.ref." + symbol;
    if (!dw_refs_.insert(symbol).second) {
        return name;
    }
    std::string section_name = ".data.rel.local." + name;
    int id = builder_.add_section(section_name, ELF_SHT_PROGBITS,
                                  ELF_SHF_ALLOC | ELF_SHF_WRITE, 8);
    section_ids_[section_name] = id;
    ElfSection& section = builder_.section(id);
    section.bytes.assign(8, 0);
    ElfReloc reloc;
    reloc.offset = 0;
    reloc.symbol = symbol;
    reloc.type = ELF_R_AARCH64_ABS64;
    section.relocs.push_back(std::move(reloc));

    ElfSymbol object;
    object.name = name;
    object.section = id;
    object.value = 0;
    object.size = 8;
    object.type = ELF_STT_OBJECT;
    object.external = true;
    object.weak = true;
    object.hidden = true;
    builder_.add_symbol(std::move(object));
    return name;
}

void ElfEmitter::splice_asm_fragment(const std::string& text,
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
        if (piece.bytes.empty() && piece.symbols.empty()) {
            continue;
        }
        int id = -1;
        if (i == 0 && piece.sectname == ".text") {
            id = text_section();
        } else {
            auto found = section_ids_.find(piece.sectname);
            if (found != section_ids_.end()) {
                id = found->second;
            } else {
                id = builder_.add_section(piece.sectname, ELF_SHT_PROGBITS,
                                          ELF_SHF_ALLOC | ELF_SHF_WRITE, 1);
                section_ids_[piece.sectname] = id;
            }
        }
        ElfSection& target = builder_.section(id);
        uint64_t alignment = 1ull << piece.align_log2;
        if (alignment > target.align) {
            target.align = alignment;
        }
        section_ids[i] = id;
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
            ElfSymbol symbol;
            symbol.name = label.name;
            symbol.section = section_ids[i];
            symbol.value = offset;
            symbol.type = ELF_STT_FUNC;
            symbol.external = label.global;
            symbol.weak = label.weak;
            symbol.hidden = label.hidden;
            builder_.add_symbol(std::move(symbol));
        }
    }
    for (const assembler::CommonSymbol& common : fragment.commons) {
        ElfCommon entry;
        entry.name = common.name;
        entry.size = common.size;
        entry.align = 1ull << common.align_log2;
        builder_.add_common(std::move(entry));
    }

    for (size_t i = 0; i < fragment.sections.size(); ++i) {
        if (section_ids[i] < 0) {
            continue;
        }
        ElfSection& target = builder_.section(section_ids[i]);
        uint64_t base = section_bases[i];
        for (const assembler::FragmentReloc& reloc :
             fragment.sections[i].relocs) {
            bool ok = false;
            ElfReloc out;
            out.offset = base + reloc.offset;
            out.type = fragment_reloc_type(reloc.kind, reloc.flavor,
                                           reloc.access_bytes, ok);
            if (!ok) {
                error("unsupported relocation in inline assembly");
                continue;
            }
            out.symbol = reloc.symbol;
            target.relocs.push_back(std::move(out));
        }
        for (const assembler::FragmentFixup& fixup :
             fragment.sections[i].unresolved) {
            uint64_t offset = base + fixup.offset;
            bool branch = fixup.kind == assembler::FixupKind::Branch26 ||
                          fixup.kind == assembler::FixupKind::Branch19;
            if (branch && inside_function &&
                section_ids[i] == text_section()) {
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
                if (fixup.kind == assembler::FixupKind::Branch26) {
                    pending_sym_branches_.push_back({offset, fixup.symbol});
                    continue;
                }
            }
            auto found = fragment_labels.find(fixup.symbol);
            if (found != fragment_labels.end() && branch &&
                found->second.first == section_ids[i]) {
                int64_t displacement =
                    static_cast<int64_t>(found->second.second) -
                    static_cast<int64_t>(offset);
                uint32_t word = 0;
                for (int b = 0; b < 4; ++b) {
                    word |= static_cast<uint32_t>(target.bytes[offset + b])
                            << (8 * b);
                }
                word = fixup.kind == assembler::FixupKind::Branch26
                           ? patch_branch26(word, displacement)
                           : patch_branch19(word, displacement);
                for (int b = 0; b < 4; ++b) {
                    target.bytes[offset + b] =
                        static_cast<uint8_t>(word >> (8 * b));
                }
                continue;
            }
            bool ok = false;
            ElfReloc out;
            out.offset = offset;
            out.symbol = fixup.symbol;
            out.addend = fixup.addend;
            out.type = fragment_reloc_type(fixup.kind, fixup.flavor,
                                           fixup.access_bytes, ok);
            if (!ok) {
                error("unsupported inline-asm reference to '" + fixup.symbol +
                      "'");
                continue;
            }
            target.relocs.push_back(std::move(out));
        }
    }
}

ElfEmitter::ElfEmitter(std::vector<Diagnostic>& diagnostics,
                       bool emit_unwind_tables)
    : diagnostics_(diagnostics), emit_unwind_tables_(emit_unwind_tables) {}

void ElfEmitter::error(const std::string& message) {
    Diagnostic diag;
    diag.level = DiagnosticLevel::Error;
    diag.message = "air backend: " + message;
    diagnostics_.push_back(diag);
}

int ElfEmitter::text_section() {
    auto found = section_ids_.find(".text");
    if (found != section_ids_.end()) {
        return found->second;
    }
    int id = builder_.add_section(".text", ELF_SHT_PROGBITS,
                                  ELF_SHF_ALLOC | ELF_SHF_EXECINSTR, 4);
    section_ids_[".text"] = id;
    return id;
}

int ElfEmitter::section_for_global(const air::GlobalData& global,
                                   bool has_relocs) {
    std::string name;
    uint32_t sh_type = ELF_SHT_PROGBITS;
    uint64_t flags = ELF_SHF_ALLOC;
    uint64_t entsize = 0;
    bool nobits = false;

    if (global.init.kind == air::GlobalInitKind::Zero) {
        name = ".bss";
        sh_type = ELF_SHT_NOBITS;
        flags = ELF_SHF_ALLOC | ELF_SHF_WRITE;
        nobits = true;
    } else {
        switch (global.section) {
            case air::SectionKind::Cstring:
                name = ".rodata.str1.1";
                flags = ELF_SHF_ALLOC | ELF_SHF_MERGE | ELF_SHF_STRINGS;
                entsize = 1;
                break;
            case air::SectionKind::Const:
            case air::SectionKind::Text:

                name = has_relocs ? ".data.rel.ro" : ".rodata";
                if (has_relocs) {
                    flags = ELF_SHF_ALLOC | ELF_SHF_WRITE;
                }
                break;
            case air::SectionKind::Custom:
                name = global.custom_section;
                flags = ELF_SHF_ALLOC | ELF_SHF_WRITE;
                break;
            case air::SectionKind::Data:
            case air::SectionKind::Zerofill:
                name = ".data";
                flags = ELF_SHF_ALLOC | ELF_SHF_WRITE;
                break;
        }
    }

    auto found = section_ids_.find(name);
    if (found != section_ids_.end()) {
        return found->second;
    }
    int id = builder_.add_section(name, sh_type, flags, 1, entsize, nobits);
    section_ids_[name] = id;
    return id;
}

void ElfEmitter::begin_module(const air::Module& module) {
    target_ = module.target_ptr();
}

void ElfEmitter::emit_module_asm(const std::string& text) {
    splice_asm_fragment(text, /*inside_function=*/false);
}

void ElfEmitter::begin_function(const MFunction& function) {
    int text = text_section();
    ElfSection& section = builder_.section(text);

    ElfSymbol symbol;
    symbol.name = function.name;
    symbol.section = text;
    symbol.value = section.bytes.size();
    symbol.type = ELF_STT_FUNC;
    symbol.external = function.linkage != air::Linkage::Internal;
    symbol.weak = function.linkage == air::Linkage::LinkOnceODR ||
                  function.linkage == air::Linkage::Weak;
    symbol.hidden = function.attrs.hidden && symbol.external;
    current_function_symbol_ = symbol.name;
    current_function_start_ = symbol.value;
    if (!symbol.external && !symbol.weak) {
        local_text_offsets_[symbol.name] = symbol.value;
    }
    current_function_symbol_index_ = builder_.add_symbol(std::move(symbol));

    block_offsets_.clear();
    pending_labels_.clear();
    eh_label_offsets_.clear();
    has_frame_setup_ = false;
    frame_setup_offset_ = 0;
}

void ElfEmitter::emit_block_label(const MFunction& function,
                                  uint32_t block_index) {
    int text = text_section();
    ElfSection& section = builder_.section(text);
    block_offsets_[block_index] = section.bytes.size();
    if (function.blocks[block_index].address_taken) {
        ElfSymbol symbol;
        symbol.name = "l_air_lbl_" + std::to_string(function.index) + "_" +
                      std::to_string(block_index);
        symbol.section = text;
        symbol.value = section.bytes.size();
        local_text_offsets_[symbol.name] = symbol.value;
        builder_.add_symbol(std::move(symbol));
    }
}

void ElfEmitter::emit_inst(const MFunction& function, const MInst& inst) {
    if (static_cast<A64Op>(inst.opcode) == A64Op::EhLabel) {
        eh_label_offsets_[inst.aux] = builder_.section(text_section())
                                          .bytes.size();
        return;
    }
    if (static_cast<A64Op>(inst.opcode) == A64Op::AsmBlock) {
        splice_asm_fragment(function.asm_texts[inst.aux],
                            /*inside_function=*/true);
        return;
    }
    int text = text_section();
    ElfSection& section = builder_.section(text);
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
            if (encoded.fixup == TextFixup::SymBranch26) {
                pending_sym_branches_.push_back(
                    {word_offset, operand.symbol});
                break;
            }
            ElfReloc reloc;
            reloc.offset = word_offset;
            reloc.symbol = operand.symbol;
            if (encoded.fixup == TextFixup::SymPage21) {
                reloc.type = operand.flavor == SymFlavor::GotPage
                                 ? ELF_R_AARCH64_ADR_GOT_PAGE
                                 : ELF_R_AARCH64_ADR_PREL_PG_HI21;
            } else {
                reloc.type = operand.flavor == SymFlavor::GotPageOff
                                 ? ELF_R_AARCH64_LD64_GOT_LO12_NC
                                 : pageoff_reloc_type(
                                       static_cast<A64Op>(inst.opcode));
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

    if (!has_frame_setup_ && static_cast<A64Op>(inst.opcode) == A64Op::MovX &&
        inst.operands.size() == 2 &&
        inst.operands[0].kind == MOperandKind::Reg &&
        inst.operands[1].kind == MOperandKind::Reg &&
        inst.operands[0].reg.index() == X29 &&
        inst.operands[1].reg.index() == SP) {

        frame_setup_offset_ = word_offset;
        has_frame_setup_ = true;
    }

    for (int i = 0; i < 4; ++i) {
        section.bytes.push_back(
            static_cast<uint8_t>(encoded.word >> (8 * i)));
    }
}

uint64_t ElfEmitter::emit_lsda(const MFunction& function,
                               uint64_t function_end) {
    if (function.eh_call_sites.empty()) {
        return NO_ELF_LSDA;
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
                return NO_ELF_LSDA;
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
    for (const MEhCallSite& site : function.eh_call_sites) {
        auto begin = eh_label_offsets_.find(site.begin_label);
        auto end = eh_label_offsets_.find(site.end_label);
        auto landing_pad = block_offsets_.find(site.landing_pad_block);
        if (begin == eh_label_offsets_.end() ||
            end == eh_label_offsets_.end() ||
            landing_pad == block_offsets_.end()) {
            error("EH call-site metadata references an unemitted label");
            return NO_ELF_LSDA;
        }
        uint64_t action_value = 0;
        if (site.action_label != 0) {
            auto action = action_offsets.find(site.action_label);
            if (action == action_offsets.end()) {
                error("EH call-site metadata references a missing action");
                return NO_ELF_LSDA;
            }
            action_value = action->second + 1;
        }
        sites.push_back(ResolvedCallSite{begin->second, end->second,
                                         landing_pad->second, action_value});
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
            return NO_ELF_LSDA;
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
        for (;;) {
            uint64_t ttype_ref_offset = 2 + ttype_uleb_bytes;
            uint64_t cursor = ttype_ref_offset;
            cursor += 1;
            cursor += uleb_size(call_sites.size());
            cursor += call_sites.size();
            cursor += actions.size();
            cursor = (cursor + 3) & ~uint64_t{3};
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

    std::vector<std::string> typeinfo_refs;
    typeinfo_refs.reserve(typeinfos.size());
    for (const MEhTypeInfo& typeinfo : typeinfos) {
        typeinfo_refs.push_back(typeinfo.symbol.empty()
                                    ? std::string()
                                    : dw_ref_symbol(typeinfo.symbol));
    }

    int id = gcc_except_section();
    ElfSection& section = builder_.section(id);
    while (section.bytes.size() % 4 != 0) {
        section.bytes.push_back(0);
    }
    uint64_t lsda_start = section.bytes.size();

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
        while (lsda.size() % 4 != 0) {
            lsda.push_back(0);
        }
        for (size_t i = 0; i < typeinfos.size(); ++i) {
            uint64_t entry_offset = lsda.size();
            append_u32(lsda, 0);
            if (typeinfo_refs[i].empty()) {
                continue;
            }
            ElfReloc reloc;
            reloc.offset = lsda_start + entry_offset;
            reloc.symbol = typeinfo_refs[i];
            reloc.type = ELF_R_AARCH64_PREL32;
            section.relocs.push_back(std::move(reloc));
        }
    }
    while (lsda.size() % 4 != 0) {
        lsda.push_back(0);
    }
    section.bytes.insert(section.bytes.end(), lsda.begin(), lsda.end());
    return lsda_start;
}

void ElfEmitter::emit_eh_frame_entry(const MFunction& function,
                                     uint64_t function_end,
                                     uint64_t lsda_offset, bool has_lsda) {

    std::string personality_ref =
        eh_frame_started_ ? std::string()
                          : dw_ref_symbol("__gxx_personality_v0");
    int id = eh_frame_section();
    int text = text_section();
    int except = has_lsda ? gcc_except_section() : -1;
    ElfSection& section = builder_.section(id);
    if (!eh_frame_started_) {
        uint64_t personality_slot = 0;
        cie_offset_ = append_eh_frame_cie(section.bytes,
                                          /*with_personality=*/true,
                                          personality_slot);
        ElfReloc reloc;
        reloc.offset = personality_slot;
        reloc.symbol = personality_ref;
        reloc.type = ELF_R_AARCH64_PREL32;
        section.relocs.push_back(std::move(reloc));
        eh_frame_started_ = true;
    }

    EhFrameFunction entry;
    entry.start = current_function_start_;
    entry.size = function_end - current_function_start_;
    entry.has_lsda = has_lsda;
    entry.lsda_offset = lsda_offset;
    entry.frame_setup_offset = frame_setup_offset_;
    entry.has_frame = has_frame_setup_;
    for (const auto& [phys, cfa_offset] : function.csr_cfa_offsets) {
        entry.saved_registers.push_back({phys, cfa_offset});
    }

    uint64_t pc_slot = 0;
    uint64_t lsda_slot = 0;
    append_eh_frame_fde(section.bytes, cie_offset_, entry, pc_slot, lsda_slot);

    ElfReloc pc;
    pc.offset = pc_slot;
    pc.section = text;
    pc.addend = static_cast<int64_t>(current_function_start_);
    pc.type = ELF_R_AARCH64_PREL32;
    section.relocs.push_back(std::move(pc));
    if (has_lsda && lsda_slot != 0) {
        ElfReloc lsda;
        lsda.offset = lsda_slot;
        lsda.section = except;
        lsda.addend = static_cast<int64_t>(lsda_offset);
        lsda.type = ELF_R_AARCH64_PREL32;
        section.relocs.push_back(std::move(lsda));
    }
}

void ElfEmitter::end_function(const MFunction& function) {
    int text = text_section();
    ElfSection& section = builder_.section(text);
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
    builder_.symbol(current_function_symbol_index_).size =
        function_end - current_function_start_;
    if (emit_unwind_tables_) {
        uint64_t lsda_offset = emit_lsda(function, function_end);
        emit_eh_frame_entry(function, function_end, lsda_offset,
                            lsda_offset != NO_ELF_LSDA);
    }
    block_offsets_.clear();
    eh_label_offsets_.clear();
}

void ElfEmitter::emit_global(const air::Module& module,
                             const air::GlobalData& global) {
    if (global.init.kind == air::GlobalInitKind::None) {
        return;
    }

    if (global.linkage == air::Linkage::Common) {
        ElfCommon common;
        common.name = global.name;
        common.size = global.size_bytes;
        common.align = global.align_bytes ? global.align_bytes : 1;
        builder_.add_common(std::move(common));
        return;
    }

    int id = section_for_global(global, !global.init.relocs.empty());
    ElfSection& section = builder_.section(id);
    if (global.align_bytes > section.align) {
        section.align = global.align_bytes;
    }

    ElfSymbol symbol;
    symbol.name = global.name;
    symbol.section = id;
    symbol.size = global.size_bytes;
    symbol.type = ELF_STT_OBJECT;
    symbol.external = global.linkage != air::Linkage::Internal;
    symbol.weak = global.linkage == air::Linkage::LinkOnceODR ||
                  global.linkage == air::Linkage::Weak;
    symbol.hidden = global.attrs.hidden && symbol.external;

    if (global.init.kind == air::GlobalInitKind::Zero) {
        section.nobits_size =
            align_up(section.nobits_size,
                     global.align_bytes ? global.align_bytes : 1);
        symbol.value = section.nobits_size;
        section.nobits_size += global.size_bytes;
        builder_.add_symbol(std::move(symbol));
        return;
    }

    size_t start = align_up(section.bytes.size(),
                            global.align_bytes ? global.align_bytes : 1);
    section.bytes.resize(start, 0);
    symbol.value = start;
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

        for (int i = 0; i < 8; ++i) {
            section.bytes[hole + i] = 0;
        }
        ElfReloc record;
        record.offset = hole;
        record.symbol = reloc_target_name(module, reloc);
        record.type = ELF_R_AARCH64_ABS64;
        record.addend = reloc.addend;
        section.relocs.push_back(std::move(record));
    }
}

void ElfEmitter::emit_ctor_list(const air::Module& module) {
    if (module.ctors().empty()) {
        return;
    }
    int id;
    auto found = section_ids_.find(".init_array");
    if (found != section_ids_.end()) {
        id = found->second;
    } else {
        id = builder_.add_section(".init_array", ELF_SHT_INIT_ARRAY,
                                  ELF_SHF_ALLOC | ELF_SHF_WRITE, 8, 8);
        section_ids_[".init_array"] = id;
    }
    ElfSection& section = builder_.section(id);
    for (const air::CtorEntry& ctor : module.ctors()) {
        const air::Function& function = module.function(ctor.func);
        ElfReloc record;
        record.offset = section.bytes.size();
        record.symbol = function.name();
        record.type = ELF_R_AARCH64_ABS64;
        section.relocs.push_back(std::move(record));
        for (int i = 0; i < 8; ++i) {
            section.bytes.push_back(0);
        }
    }
}

void ElfEmitter::end_module(const air::Module& module) {
    (void)module;
    int text = text_section();
    ElfSection& section = builder_.section(text);
    for (const PendingSymBranch& branch : pending_sym_branches_) {
        auto found = local_text_offsets_.find(branch.symbol);
        if (found != local_text_offsets_.end()) {

            int64_t displacement = static_cast<int64_t>(found->second) -
                                   static_cast<int64_t>(branch.word_offset);
            uint32_t word = 0;
            for (int i = 0; i < 4; ++i) {
                word |= static_cast<uint32_t>(
                            section.bytes[branch.word_offset + i])
                        << (8 * i);
            }
            word = patch_branch26(word, displacement);
            for (int i = 0; i < 4; ++i) {
                section.bytes[branch.word_offset + i] =
                    static_cast<uint8_t>(word >> (8 * i));
            }
            continue;
        }
        ElfReloc reloc;
        reloc.offset = branch.word_offset;
        reloc.symbol = branch.symbol;
        reloc.type = ELF_R_AARCH64_CALL26;
        section.relocs.push_back(std::move(reloc));
    }
    pending_sym_branches_.clear();
}

bool ElfEmitter::write(std::ostream& out) {
    std::string write_error;
    if (!builder_.write(out, write_error)) {
        error("cannot write object file: " + write_error);
        return false;
    }
    return true;
}

} // namespace aburi::backend::aarch64
