#include "sink.h"

#include "../backend/common/macho.h"

namespace aburi::assembler {

namespace {

constexpr uint32_t CPU_TYPE_ARM64 = 0x0100000Cu;
constexpr uint32_t CPU_SUBTYPE_ARM64_ALL = 0;
constexpr uint32_t CPU_TYPE_X86_64 = 0x01000007u;
constexpr uint32_t CPU_SUBTYPE_X86_64_ALL = 3;
constexpr uint32_t MACOS_MINOS = 26u << 16;

uint8_t reloc_length(FixupKind kind) {
    return fixup_width_bytes(kind) == 8 ? 3 : 2;
}

void x86_reloc_type_for(const RelocRecord& reloc, uint8_t& type, bool& pcrel) {
    using backend::SymFlavor;
    switch (reloc.reloc_kind) {
        case RelocKind::Branch32:
            type = backend::MACHO_X86_64_RELOC_BRANCH;
            pcrel = true;
            return;
        case RelocKind::PcRel32:
            pcrel = true;
            if (reloc.flavor == SymFlavor::GotPcRel) {
                type = backend::MACHO_X86_64_RELOC_GOT_LOAD;
            } else if (reloc.flavor == SymFlavor::TlvPcRel) {
                type = backend::MACHO_X86_64_RELOC_TLV;
            } else {
                switch (reloc.pcrel_extra) {
                    case 1: type = backend::MACHO_X86_64_RELOC_SIGNED_1; break;
                    case 2: type = backend::MACHO_X86_64_RELOC_SIGNED_2; break;
                    case 4: type = backend::MACHO_X86_64_RELOC_SIGNED_4; break;
                    default: type = backend::MACHO_X86_64_RELOC_SIGNED; break;
                }
            }
            return;
        case RelocKind::Subtractor:
            type = backend::MACHO_X86_64_RELOC_SUBTRACTOR;
            pcrel = false;
            return;
        default:
            type = backend::MACHO_X86_64_RELOC_UNSIGNED;
            pcrel = false;
            return;
    }
}

void reloc_type_for(const RelocRecord& reloc, uint8_t& type, bool& pcrel) {
    using backend::SymFlavor;
    switch (reloc.reloc_kind) {
        case RelocKind::Absolute:
            type = backend::MACHO_ARM64_RELOC_UNSIGNED;
            pcrel = false;
            return;
        case RelocKind::Subtractor:
            type = backend::MACHO_ARM64_RELOC_SUBTRACTOR;
            pcrel = false;
            return;
        case RelocKind::Branch26:
            type = backend::MACHO_ARM64_RELOC_BRANCH26;
            pcrel = true;
            return;
        case RelocKind::Page21:
            type = reloc.flavor == SymFlavor::GotPage
                       ? backend::MACHO_ARM64_RELOC_GOT_LOAD_PAGE21
                   : reloc.flavor == SymFlavor::TlvPage
                       ? backend::MACHO_ARM64_RELOC_TLVP_LOAD_PAGE21
                       : backend::MACHO_ARM64_RELOC_PAGE21;
            pcrel = true;
            return;
        case RelocKind::PointerToGot:
            type = backend::MACHO_ARM64_RELOC_POINTER_TO_GOT;
            pcrel = true;
            return;
        case RelocKind::PageOff12:
            type = reloc.flavor == SymFlavor::GotPageOff
                       ? backend::MACHO_ARM64_RELOC_GOT_LOAD_PAGEOFF12
                   : reloc.flavor == SymFlavor::TlvPageOff
                       ? backend::MACHO_ARM64_RELOC_TLVP_LOAD_PAGEOFF12
                       : backend::MACHO_ARM64_RELOC_PAGEOFF12;
            pcrel = false;
            return;
        case RelocKind::Branch32:
        case RelocKind::PcRel32:
            break;
    }
    type = backend::MACHO_ARM64_RELOC_UNSIGNED;
    pcrel = false;
}

}

bool write_macho_object(AsmUnit& unit, const TargetInfo& target,
                        std::ostream& out, std::string& error) {
    bool x86 = target.arch == TargetArch::X86_64;
    if (target.arch != TargetArch::AARCH64 && !x86) {
        error = "the Mach-O sink only covers aarch64 and x86-64 so far";
        return false;
    }

    backend::MachOBuilder builder(
        x86 ? CPU_TYPE_X86_64 : CPU_TYPE_ARM64,
        x86 ? CPU_SUBTYPE_X86_64_ALL : CPU_SUBTYPE_ARM64_ALL, MACOS_MINOS);

    constexpr uint32_t S_ZEROFILL = 0x1;
    std::vector<int> builder_id(unit.sections.size(), -1);
    for (size_t i = 0; i < unit.sections.size(); ++i) {
        AsmSection& section = unit.sections[i];
        uint32_t flags = section.zerofill
                             ? (section.flags & ~0xFFu) | S_ZEROFILL
                             : section.flags;
        int id = builder.add_section(section.segname, section.sectname,
                                    flags, section.align_log2,
                                    section.zerofill);
        builder_id[i] = id;
        backend::MachOSection& out_section = builder.section(id);
        if (section.zerofill) {
            out_section.zerofill_size = section.zerofill_size;
        } else {
            out_section.bytes = std::move(section.bytes);
        }
    }
    for (size_t i = 0; i < unit.sections.size(); ++i) {
        AsmSection& section = unit.sections[i];
        backend::MachOSection& out_section =
            builder.section(builder_id[i]);
        for (const RelocRecord& reloc : section.relocs) {
            backend::MachOReloc macho_reloc;
            macho_reloc.offset = reloc.offset;
            if (x86) {
                x86_reloc_type_for(reloc, macho_reloc.type,
                                   macho_reloc.pcrel);
            } else {
                reloc_type_for(reloc, macho_reloc.type, macho_reloc.pcrel);
            }
            macho_reloc.length = reloc_length(reloc.kind);
            if (reloc.symbol != no_sym) {
                macho_reloc.external = true;
                macho_reloc.symbol = unit.symbols.sym(reloc.symbol).name;
            } else {
                macho_reloc.external = false;
                macho_reloc.section = builder_id[static_cast<size_t>(
                    reloc.section)];
                macho_reloc.section_relative_field = macho_reloc.pcrel;
            }
            out_section.relocs.push_back(std::move(macho_reloc));
        }
    }

    for (SymId id = 0; id < unit.symbols.size(); ++id) {
        const AsmSymbol& symbol = unit.symbols.sym(id);
        if (symbol.internal) {
            continue;
        }
        if (symbol.state == SymState::Constant) {
            if (symbol.global) {
                error = "global absolute symbol '" + symbol.name +
                        "' is not representable yet";
                return false;
            }
            continue;
        }
        if (symbol.state != SymState::Label) {
            continue;
        }
        if (!symbol.name.empty() && symbol.name[0] == 'L') {
            continue;
        }
        backend::MachOSymbol macho_symbol;
        macho_symbol.name = symbol.name;
        macho_symbol.section = builder_id[static_cast<size_t>(symbol.section)];
        macho_symbol.offset_in_section = symbol.offset;
        macho_symbol.external = symbol.global;
        macho_symbol.weak_definition = symbol.weak;
        macho_symbol.private_extern = symbol.hidden;
        builder.add_symbol(std::move(macho_symbol));
    }

    for (const CommonSymbol& common : unit.commons) {
        backend::MachOCommon macho_common;
        macho_common.name = common.name;
        macho_common.size = common.size;
        macho_common.align_log2 = common.align_log2;
        builder.add_common(std::move(macho_common));
    }

    return builder.write(out, error);
}

}
