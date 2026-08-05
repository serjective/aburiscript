#ifndef ABURI_ASSEMBLER_UNIT_H
#define ABURI_ASSEMBLER_UNIT_H

#include <cstdint>
#include <string>
#include <vector>

#include "../backend/common/mir.h"
#include "symbols.h"

namespace aburi::assembler {

enum class FixupKind : uint8_t {
    Abs8,
    Abs16,
    Abs32,
    Abs64,
    Branch26,
    Branch19,
    Page21,
    PageOff12,
    Branch32,
    PcRel32,
    GotDelta32,
};

inline bool fixup_is_data(FixupKind kind) {
    return kind == FixupKind::Abs8 || kind == FixupKind::Abs16 ||
           kind == FixupKind::Abs32 || kind == FixupKind::Abs64;
}

inline uint32_t fixup_width_bytes(FixupKind kind) {
    switch (kind) {
        case FixupKind::Abs8: return 1;
        case FixupKind::Abs16: return 2;
        case FixupKind::Abs32: return 4;
        case FixupKind::Abs64: return 8;
        default: return 4;
    }
}

struct PendingFixup {
    uint64_t offset = 0;
    FixupKind kind = FixupKind::Abs64;
    int64_t constant = 0;
    SymId pos_sym = no_sym;
    SymId neg_sym = no_sym;
    backend::SymFlavor flavor = backend::SymFlavor::Plain;
    uint8_t access_bytes = 0;
    uint8_t pcrel_extra = 0;
    uint32_t deferred_seq = 0;
    uint32_t line = 0;
    uint32_t col = 0;
};

enum class DeferredKind : uint8_t {
    Uleb,
    Sleb,
    Align,
    Branch,
};

struct DeferredBranch {
    uint8_t short_opcode = 0;
    uint8_t near_bytes[8] = {};
    uint8_t near_size = 0;
    uint8_t rel_offset = 0;
    bool patchable = false;
};

struct DeferredField {
    DeferredKind kind = DeferredKind::Uleb;
    uint64_t raw_offset = 0;
    int64_t constant = 0;
    SymId pos_sym = no_sym;
    SymId neg_sym = no_sym;
    uint32_t align_log2 = 0;
    uint8_t fill = 0;
    bool nop_fill = false;
    DeferredBranch branch;
    uint32_t line = 0;
    uint32_t col = 0;
    uint32_t size = 0;
};

enum class RelocKind : uint8_t {
    Absolute,
    Subtractor,
    Branch26,
    Page21,
    PageOff12,
    PointerToGot,
    Branch32,
    PcRel32,
};

struct RelocRecord {
    uint64_t offset = 0;
    FixupKind kind = FixupKind::Abs64;
    RelocKind reloc_kind = RelocKind::Absolute;
    backend::SymFlavor flavor = backend::SymFlavor::Plain;
    uint8_t access_bytes = 0;
    uint8_t pcrel_extra = 0;
    SymId symbol = no_sym;
    int section = -1;
};

struct UnresolvedFixup {
    uint64_t offset = 0;
    FixupKind kind = FixupKind::Abs64;
    SymId symbol = no_sym;
    int64_t addend = 0;
    backend::SymFlavor flavor = backend::SymFlavor::Plain;
    uint8_t access_bytes = 0;
    uint8_t pcrel_extra = 0;
    uint32_t line = 0;
    uint32_t col = 0;
};

struct AsmSection {
    std::string segname;
    std::string sectname;
    uint32_t flags = 0;
    uint32_t align_log2 = 0;
    bool zerofill = false;
    uint64_t zerofill_size = 0;
    std::vector<uint8_t> bytes;
    std::vector<PendingFixup> fixups;
    std::vector<RelocRecord> relocs;
    std::vector<UnresolvedFixup> unresolved;
    std::vector<DeferredField> deferred;

    uint64_t size() const { return zerofill ? zerofill_size : bytes.size(); }
};

struct CommonSymbol {
    std::string name;
    uint64_t size = 0;
    uint32_t align_log2 = 0;
};

struct AsmUnit {
    std::vector<AsmSection> sections;
    SymbolTable symbols;
    std::vector<CommonSymbol> commons;
};

}

#endif
