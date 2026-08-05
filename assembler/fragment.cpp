#include "fragment.h"

#include "assembler.h"

namespace aburi::assembler {

FragmentResult assemble_fragment(std::string_view text,
                                 const AsmOptions& options) {
    FragmentResult result;
    AsmOptions fragment_options = options;
    fragment_options.fragment_mode = true;

    Assembler assembler(text, fragment_options);
    bool assembled = assembler.run();
    result.diagnostics = std::move(assembler.diagnostics());
    if (!assembled) {
        return result;
    }

    AsmUnit& unit = assembler.unit();
    result.commons = std::move(unit.commons);
    result.sections.reserve(unit.sections.size());
    for (AsmSection& section : unit.sections) {
        FragmentSection out;
        out.segname = std::move(section.segname);
        out.sectname = std::move(section.sectname);
        out.flags = section.flags;
        out.align_log2 = section.align_log2;
        out.zerofill = section.zerofill;
        out.zerofill_size = section.zerofill_size;
        out.bytes = std::move(section.bytes);
        for (const RelocRecord& reloc : section.relocs) {
            FragmentReloc entry;
            entry.offset = reloc.offset;
            entry.kind = reloc.kind;
            entry.reloc_kind = reloc.reloc_kind;
            entry.flavor = reloc.flavor;
            entry.access_bytes = reloc.access_bytes;
            entry.section_index = reloc.section;
            if (reloc.symbol != no_sym) {
                entry.symbol = unit.symbols.sym(reloc.symbol).name;
            }
            out.relocs.push_back(std::move(entry));
        }
        for (const UnresolvedFixup& fixup : section.unresolved) {
            FragmentFixup entry;
            entry.offset = fixup.offset;
            entry.kind = fixup.kind;
            entry.symbol = unit.symbols.sym(fixup.symbol).name;
            entry.addend = fixup.addend;
            entry.flavor = fixup.flavor;
            entry.access_bytes = fixup.access_bytes;
            out.unresolved.push_back(std::move(entry));
        }
        result.sections.push_back(std::move(out));
    }

    for (SymId id = 0; id < unit.symbols.size(); ++id) {
        const AsmSymbol& symbol = unit.symbols.sym(id);
        if (symbol.internal || symbol.state != SymState::Label ||
            symbol.section < 0 ||
            static_cast<size_t>(symbol.section) >= result.sections.size()) {
            continue;
        }
        bool private_label = asm_target_is_elf(*options.target)
            ? symbol.name.rfind(".L", 0) == 0
            : symbol.name[0] == 'L';
        if (private_label) {
            continue;
        }
        FragmentSymbol entry;
        entry.name = symbol.name;
        entry.offset = symbol.offset;
        entry.global = symbol.global;
        entry.weak = symbol.weak;
        entry.hidden = symbol.hidden;
        result.sections[static_cast<size_t>(symbol.section)]
            .symbols.push_back(std::move(entry));
    }

    result.ok = true;
    return result;
}

}
