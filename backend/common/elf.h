#ifndef ABURI_BACKEND_COMMON_ELF_H
#define ABURI_BACKEND_COMMON_ELF_H

#include <cstdint>
#include <ostream>
#include <string>
#include <vector>

namespace aburi::backend {

enum class ElfClass : uint8_t { Elf32, Elf64 };
enum class ElfData : uint8_t { Lsb, Msb };

inline constexpr uint32_t ELF_R_AARCH64_ABS64 = 257;
inline constexpr uint32_t ELF_R_AARCH64_ABS32 = 258;
inline constexpr uint32_t ELF_R_AARCH64_PREL32 = 261;
inline constexpr uint32_t ELF_R_AARCH64_ADR_PREL_PG_HI21 = 275;
inline constexpr uint32_t ELF_R_AARCH64_ADD_ABS_LO12_NC = 277;
inline constexpr uint32_t ELF_R_AARCH64_LDST8_ABS_LO12_NC = 278;
inline constexpr uint32_t ELF_R_AARCH64_JUMP26 = 282;
inline constexpr uint32_t ELF_R_AARCH64_CALL26 = 283;
inline constexpr uint32_t ELF_R_AARCH64_LDST16_ABS_LO12_NC = 284;
inline constexpr uint32_t ELF_R_AARCH64_LDST32_ABS_LO12_NC = 285;
inline constexpr uint32_t ELF_R_AARCH64_LDST64_ABS_LO12_NC = 286;
inline constexpr uint32_t ELF_R_AARCH64_LDST128_ABS_LO12_NC = 299;
inline constexpr uint32_t ELF_R_AARCH64_ADR_GOT_PAGE = 311;
inline constexpr uint32_t ELF_R_AARCH64_LD64_GOT_LO12_NC = 312;

inline constexpr uint32_t ELF_SHT_PROGBITS = 1;
inline constexpr uint32_t ELF_SHT_NOBITS = 8;
inline constexpr uint32_t ELF_SHT_INIT_ARRAY = 14;
inline constexpr uint64_t ELF_SHF_WRITE = 0x1;
inline constexpr uint64_t ELF_SHF_ALLOC = 0x2;
inline constexpr uint64_t ELF_SHF_EXECINSTR = 0x4;
inline constexpr uint64_t ELF_SHF_MERGE = 0x10;
inline constexpr uint64_t ELF_SHF_STRINGS = 0x20;

inline constexpr uint8_t ELF_STT_NOTYPE = 0;
inline constexpr uint8_t ELF_STT_OBJECT = 1;
inline constexpr uint8_t ELF_STT_FUNC = 2;

struct ElfReloc {
    uint64_t offset = 0;
    std::string symbol;
    int section = -1;
    uint32_t type = ELF_R_AARCH64_ABS64;
    int64_t addend = 0;
};

struct ElfSection {
    std::string name;
    uint32_t sh_type = ELF_SHT_PROGBITS;
    uint64_t sh_flags = 0;
    uint32_t align = 1;
    uint64_t entsize = 0;
    bool nobits = false;
    std::vector<uint8_t> bytes;
    uint64_t nobits_size = 0;
    std::vector<ElfReloc> relocs;

    uint64_t content_size() const {
        return nobits ? nobits_size : bytes.size();
    }
};

struct ElfSymbol {
    std::string name;
    int section = -1;
    uint64_t value = 0;
    uint64_t size = 0;
    uint8_t type = ELF_STT_NOTYPE;
    bool external = false;
    bool weak = false;
    bool hidden = false;
};

struct ElfCommon {
    std::string name;
    uint64_t size = 0;
    uint32_t align = 1;
};

inline constexpr uint16_t ELF_EM_386 = 3;
inline constexpr uint16_t ELF_EM_ARM = 40;
inline constexpr uint16_t ELF_EM_X86_64 = 62;
inline constexpr uint16_t ELF_EM_OR1K = 92;
inline constexpr uint16_t ELF_EM_AARCH64 = 183;
inline constexpr uint16_t ELF_EM_RISCV = 243;

inline constexpr uint32_t ELF_R_386_32 = 1;
inline constexpr uint32_t ELF_R_386_PC32 = 2;
inline constexpr uint32_t ELF_R_386_PLT32 = 4;
inline constexpr uint32_t ELF_R_386_GOTOFF = 9;

inline constexpr uint32_t ELF_R_X86_64_64 = 1;
inline constexpr uint32_t ELF_R_X86_64_PC32 = 2;
inline constexpr uint32_t ELF_R_X86_64_PLT32 = 4;
inline constexpr uint32_t ELF_R_X86_64_GOTPCREL = 9;

class ElfBuilder {
public:
    explicit ElfBuilder(uint16_t machine = ELF_EM_AARCH64,
                        ElfClass eclass = ElfClass::Elf64,
                        ElfData data = ElfData::Lsb)
        : machine_(machine), class_(eclass), data_(data) {}

    void set_flags(uint32_t e_flags) { e_flags_ = e_flags; }

    int add_section(std::string name, uint32_t sh_type, uint64_t sh_flags,
                    uint32_t align, uint64_t entsize = 0, bool nobits = false);
    ElfSection& section(int id) { return sections_[id]; }
    size_t add_symbol(ElfSymbol symbol) {
        symbols_.push_back(std::move(symbol));
        return symbols_.size() - 1;
    }
    ElfSymbol& symbol(size_t index) { return symbols_[index]; }
    void add_common(ElfCommon common) { commons_.push_back(std::move(common)); }

    bool write(std::ostream& out, std::string& error) const;

private:
    uint16_t machine_;
    ElfClass class_ = ElfClass::Elf64;
    ElfData data_ = ElfData::Lsb;
    uint32_t e_flags_ = 0;
    std::vector<ElfSection> sections_;
    std::vector<ElfSymbol> symbols_;
    std::vector<ElfCommon> commons_;
};

} // namespace aburi::backend

#endif // ABURI_BACKEND_COMMON_ELF_H
