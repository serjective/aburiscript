#ifndef ABURI_BACKEND_COMMON_MACHO_H
#define ABURI_BACKEND_COMMON_MACHO_H

#include <cstdint>
#include <ostream>
#include <string>
#include <vector>

namespace aburi::backend {

inline constexpr uint8_t MACHO_ARM64_RELOC_UNSIGNED = 0;
inline constexpr uint8_t MACHO_ARM64_RELOC_SUBTRACTOR = 1;
inline constexpr uint8_t MACHO_ARM64_RELOC_BRANCH26 = 2;
inline constexpr uint8_t MACHO_ARM64_RELOC_PAGE21 = 3;
inline constexpr uint8_t MACHO_ARM64_RELOC_PAGEOFF12 = 4;
inline constexpr uint8_t MACHO_ARM64_RELOC_GOT_LOAD_PAGE21 = 5;
inline constexpr uint8_t MACHO_ARM64_RELOC_GOT_LOAD_PAGEOFF12 = 6;
inline constexpr uint8_t MACHO_ARM64_RELOC_POINTER_TO_GOT = 7;
inline constexpr uint8_t MACHO_ARM64_RELOC_TLVP_LOAD_PAGE21 = 8;
inline constexpr uint8_t MACHO_ARM64_RELOC_TLVP_LOAD_PAGEOFF12 = 9;

inline constexpr uint8_t MACHO_X86_64_RELOC_UNSIGNED = 0;
inline constexpr uint8_t MACHO_X86_64_RELOC_SIGNED = 1;
inline constexpr uint8_t MACHO_X86_64_RELOC_BRANCH = 2;
inline constexpr uint8_t MACHO_X86_64_RELOC_GOT_LOAD = 3;
inline constexpr uint8_t MACHO_X86_64_RELOC_GOT = 4;
inline constexpr uint8_t MACHO_X86_64_RELOC_SUBTRACTOR = 5;

inline constexpr uint8_t MACHO_X86_64_RELOC_SIGNED_1 = 6;
inline constexpr uint8_t MACHO_X86_64_RELOC_SIGNED_2 = 7;
inline constexpr uint8_t MACHO_X86_64_RELOC_SIGNED_4 = 8;
inline constexpr uint8_t MACHO_X86_64_RELOC_TLV = 9;

inline constexpr uint32_t MACHO_S_REGULAR = 0x0;
inline constexpr uint32_t MACHO_S_CSTRING_LITERALS = 0x2;
inline constexpr uint32_t MACHO_S_LITERAL_POINTERS = 0x5;
inline constexpr uint32_t MACHO_S_MOD_INIT_FUNC_POINTERS = 0x9;
inline constexpr uint32_t MACHO_S_COALESCED = 0xB;
inline constexpr uint32_t MACHO_S_THREAD_LOCAL_REGULAR = 0x11;
inline constexpr uint32_t MACHO_S_THREAD_LOCAL_ZEROFILL = 0x12;
inline constexpr uint32_t MACHO_S_THREAD_LOCAL_VARIABLES = 0x13;
inline constexpr uint32_t MACHO_S_ATTR_NO_DEAD_STRIP = 0x10000000u;
inline constexpr uint32_t MACHO_S_ATTR_PURE_INSTRUCTIONS = 0x80000000u;

bool apply_macho_section_attribute(const std::string& token, uint32_t& flags);

struct MachOReloc {
    uint64_t offset = 0;
    std::string symbol;
    int section = -1;
    uint8_t type = MACHO_ARM64_RELOC_UNSIGNED;
    uint8_t length = 2;
    bool pcrel = false;
    bool external = true;
    bool section_relative_field = false;
};

struct MachOSection {
    std::string segname;
    std::string sectname;
    uint32_t flags = 0;
    uint32_t align_log2 = 0;
    bool zerofill = false;
    std::vector<uint8_t> bytes;
    uint64_t zerofill_size = 0;
    std::vector<MachOReloc> relocs;

    uint64_t content_size() const {
        return zerofill ? zerofill_size : bytes.size();
    }
};

struct MachOSymbol {
    std::string name;
    int section = -1;
    uint64_t offset_in_section = 0;
    bool external = false;
    bool weak_definition = false;
    bool private_extern = false;
};

struct MachOCommon {
    std::string name;
    uint64_t size = 0;
    uint32_t align_log2 = 0;
};

class MachOBuilder {
public:
    MachOBuilder(uint32_t cputype, uint32_t cpusubtype, uint32_t minos_encoded);

    int add_section(std::string segname, std::string sectname, uint32_t flags,
                    uint32_t align_log2, bool zerofill = false);
    MachOSection& section(int id) { return sections_[id]; }

    void add_symbol(MachOSymbol symbol) { symbols_.push_back(std::move(symbol)); }
    void add_common(MachOCommon common) { commons_.push_back(std::move(common)); }

    bool write(std::ostream& out, std::string& error) const;

private:
    uint32_t cputype_;
    uint32_t cpusubtype_;
    uint32_t minos_;
    std::vector<MachOSection> sections_;
    std::vector<MachOSymbol> symbols_;
    std::vector<MachOCommon> commons_;
};

} // namespace aburi::backend

#endif // ABURI_BACKEND_COMMON_MACHO_H
