#ifndef ABURI_ASSEMBLER_FRAGMENT_H
#define ABURI_ASSEMBLER_FRAGMENT_H

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "../diagnostics.h"
#include "asm_options.h"
#include "unit.h"

namespace aburi::assembler {

struct FragmentSymbol {
    std::string name;
    uint64_t offset = 0;
    bool global = false;
    bool weak = false;
    bool hidden = false;
};

struct FragmentReloc {
    uint64_t offset = 0;
    FixupKind kind = FixupKind::Abs64;
    RelocKind reloc_kind = RelocKind::Absolute;
    backend::SymFlavor flavor = backend::SymFlavor::Plain;
    uint8_t access_bytes = 0;
    std::string symbol;
    int section_index = -1;
};

struct FragmentFixup {
    uint64_t offset = 0;
    FixupKind kind = FixupKind::Abs64;
    std::string symbol;
    int64_t addend = 0;
    backend::SymFlavor flavor = backend::SymFlavor::Plain;
    uint8_t access_bytes = 0;
};

struct FragmentSection {
    std::string segname;
    std::string sectname;
    uint32_t flags = 0;
    uint32_t align_log2 = 0;
    bool zerofill = false;
    uint64_t zerofill_size = 0;
    std::vector<uint8_t> bytes;
    std::vector<FragmentSymbol> symbols;
    std::vector<FragmentReloc> relocs;
    std::vector<FragmentFixup> unresolved;
};

struct FragmentResult {
    bool ok = false;
    std::vector<Diagnostic> diagnostics;
    std::vector<FragmentSection> sections;
    std::vector<CommonSymbol> commons;
};

FragmentResult assemble_fragment(std::string_view text,
                                 const AsmOptions& options);

}

#endif
