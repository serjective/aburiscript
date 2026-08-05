#include "elf.h"

#include <map>

namespace aburi::backend {

namespace {

constexpr uint16_t ET_REL = 1;
constexpr uint16_t EM_AARCH64 = 183;
constexpr uint32_t SHT_NULL = 0;
constexpr uint32_t SHT_SYMTAB = 2;
constexpr uint32_t SHT_STRTAB = 3;
constexpr uint32_t SHT_RELA = 4;
constexpr uint64_t SHF_INFO_LINK = 0x40;
constexpr uint16_t SHN_COMMON = 0xFFF2;
constexpr uint8_t STB_LOCAL = 0;
constexpr uint8_t STB_GLOBAL = 1;
constexpr uint8_t STB_WEAK = 2;
constexpr uint8_t STT_SECTION = 3;
constexpr uint8_t STV_HIDDEN = 2;

struct Buffer {
    std::vector<uint8_t> bytes;
    ElfData order = ElfData::Lsb;

    explicit Buffer(ElfData order = ElfData::Lsb) : order(order) {}

    void u8(uint8_t v) { bytes.push_back(v); }
    void scalar(uint64_t v, int size) {
        for (int i = 0; i < size; ++i) {
            int shift = order == ElfData::Msb ? size - 1 - i : i;
            bytes.push_back(static_cast<uint8_t>(v >> (8 * shift)));
        }
    }
    void u16(uint16_t v) { scalar(v, 2); }
    void u32(uint32_t v) { scalar(v, 4); }
    void u64(uint64_t v) { scalar(v, 8); }
    void pad_to(uint64_t alignment) {
        while (bytes.size() % alignment != 0) bytes.push_back(0);
    }
};

class StringTable {
public:
    StringTable() { bytes_.push_back(0); }
    uint32_t intern(const std::string& text) {
        if (text.empty()) {
            return 0;
        }
        auto found = offsets_.find(text);
        if (found != offsets_.end()) {
            return found->second;
        }
        uint32_t offset = static_cast<uint32_t>(bytes_.size());
        bytes_.insert(bytes_.end(), text.begin(), text.end());
        bytes_.push_back(0);
        offsets_[text] = offset;
        return offset;
    }
    const std::vector<uint8_t>& bytes() const { return bytes_; }

private:
    std::vector<uint8_t> bytes_;
    std::map<std::string, uint32_t> offsets_;
};

struct SymtabEntry {
    uint32_t name = 0;
    uint8_t info = 0;
    uint8_t other = 0;
    uint16_t shndx = 0;
    uint64_t value = 0;
    uint64_t size = 0;
};

} // namespace

int ElfBuilder::add_section(std::string name, uint32_t sh_type,
                            uint64_t sh_flags, uint32_t align,
                            uint64_t entsize, bool nobits) {
    ElfSection section;
    section.name = std::move(name);
    section.sh_type = sh_type;
    section.sh_flags = sh_flags;
    section.align = align;
    section.entsize = entsize;
    section.nobits = nobits;
    sections_.push_back(std::move(section));
    return static_cast<int>(sections_.size()) - 1;
}

bool ElfBuilder::write(std::ostream& out, std::string& error) const {
    const size_t content_count = sections_.size();

    const bool is64 = class_ == ElfClass::Elf64;
    const uint32_t ehdr_size = is64 ? 64 : 52;
    const uint32_t shdr_size = is64 ? 64 : 40;
    const uint64_t sym_entsize = is64 ? 24 : 16;
    const uint64_t rela_entsize = is64 ? 24 : 12;
    const uint64_t word_align = is64 ? 8 : 4;

    StringTable strtab;
    std::vector<SymtabEntry> symtab;
    symtab.push_back({});

    std::map<int, uint32_t> section_symbol;
    std::map<std::string, uint32_t> by_name;

    for (size_t i = 0; i < content_count; ++i) {
        SymtabEntry entry;
        entry.info = (STB_LOCAL << 4) | STT_SECTION;
        entry.shndx = static_cast<uint16_t>(i + 1);
        section_symbol[static_cast<int>(i)] =
            static_cast<uint32_t>(symtab.size());
        symtab.push_back(entry);
    }
    for (const ElfSymbol& symbol : symbols_) {
        if (symbol.external || symbol.weak) {
            continue;
        }
        SymtabEntry entry;
        entry.name = strtab.intern(symbol.name);
        entry.info = (STB_LOCAL << 4) | symbol.type;
        entry.shndx = symbol.section < 0
            ? 0
            : static_cast<uint16_t>(symbol.section + 1);
        entry.value = symbol.value;
        entry.size = symbol.size;
        by_name[symbol.name] = static_cast<uint32_t>(symtab.size());
        symtab.push_back(entry);
    }
    const uint32_t first_global = static_cast<uint32_t>(symtab.size());
    for (const ElfSymbol& symbol : symbols_) {
        if (!symbol.external && !symbol.weak) {
            continue;
        }
        SymtabEntry entry;
        entry.name = strtab.intern(symbol.name);
        entry.info = static_cast<uint8_t>(
            ((symbol.weak ? STB_WEAK : STB_GLOBAL) << 4) | symbol.type);
        entry.other = symbol.hidden ? STV_HIDDEN : 0;
        entry.shndx = symbol.section < 0
            ? 0
            : static_cast<uint16_t>(symbol.section + 1);
        entry.value = symbol.value;
        entry.size = symbol.size;
        by_name[symbol.name] = static_cast<uint32_t>(symtab.size());
        symtab.push_back(entry);
    }
    for (const ElfCommon& common : commons_) {
        SymtabEntry entry;
        entry.name = strtab.intern(common.name);
        entry.info = (STB_GLOBAL << 4) | ELF_STT_OBJECT;
        entry.shndx = SHN_COMMON;
        entry.value = common.align;
        entry.size = common.size;
        by_name[common.name] = static_cast<uint32_t>(symtab.size());
        symtab.push_back(entry);
    }
    auto symbol_index = [&](const std::string& name) -> uint32_t {
        auto found = by_name.find(name);
        if (found != by_name.end()) {
            return found->second;
        }
        SymtabEntry entry;
        entry.name = strtab.intern(name);
        entry.info = (STB_GLOBAL << 4) | ELF_STT_NOTYPE;
        entry.shndx = 0;
        uint32_t index = static_cast<uint32_t>(symtab.size());
        by_name[name] = index;
        symtab.push_back(entry);
        return index;
    };

    std::vector<std::vector<uint8_t>> rela_payloads(content_count);
    for (size_t i = 0; i < content_count; ++i) {
        const ElfSection& section = sections_[i];
        if (section.relocs.empty()) {
            continue;
        }
        Buffer rela(data_);
        for (const ElfReloc& reloc : section.relocs) {
            uint32_t index;
            if (!reloc.symbol.empty()) {
                index = symbol_index(reloc.symbol);
            } else if (reloc.section >= 0) {
                auto found = section_symbol.find(reloc.section);
                if (found == section_symbol.end()) {
                    error = "relocation against an unknown section";
                    return false;
                }
                index = found->second;
            } else {
                error = "relocation with no target";
                return false;
            }
            if (is64) {
                rela.u64(reloc.offset);
                rela.u64((static_cast<uint64_t>(index) << 32) | reloc.type);
                rela.u64(static_cast<uint64_t>(reloc.addend));
            } else {
                rela.u32(static_cast<uint32_t>(reloc.offset));
                rela.u32((index << 8) | (reloc.type & 0xff));
                rela.u32(static_cast<uint32_t>(reloc.addend));
            }
        }
        rela_payloads[i] = std::move(rela.bytes);
    }

    Buffer symtab_bytes(data_);
    for (const SymtabEntry& entry : symtab) {
        if (is64) {
            symtab_bytes.u32(entry.name);
            symtab_bytes.u8(entry.info);
            symtab_bytes.u8(entry.other);
            symtab_bytes.u16(entry.shndx);
            symtab_bytes.u64(entry.value);
            symtab_bytes.u64(entry.size);
        } else {

            symtab_bytes.u32(entry.name);
            symtab_bytes.u32(static_cast<uint32_t>(entry.value));
            symtab_bytes.u32(static_cast<uint32_t>(entry.size));
            symtab_bytes.u8(entry.info);
            symtab_bytes.u8(entry.other);
            symtab_bytes.u16(entry.shndx);
        }
    }

    struct HeaderSlot {
        uint32_t name = 0;
        uint32_t sh_type = SHT_NULL;
        uint64_t flags = 0;
        uint64_t offset = 0;
        uint64_t size = 0;
        uint32_t link = 0;
        uint32_t info = 0;
        uint64_t align = 0;
        uint64_t entsize = 0;
    };
    StringTable shstrtab;
    std::vector<HeaderSlot> headers(1);

    size_t rela_count = 0;
    for (size_t i = 0; i < content_count; ++i) {
        if (!rela_payloads[i].empty()) {
            ++rela_count;
        }
    }
    const uint32_t symtab_index =
        static_cast<uint32_t>(1 + content_count + rela_count);
    const uint32_t strtab_index = symtab_index + 1;
    const uint32_t shstrtab_index = symtab_index + 2;

    Buffer file(data_);

    for (uint32_t i = 0; i < ehdr_size; ++i) {
        file.u8(0);
    }

    for (size_t i = 0; i < content_count; ++i) {
        const ElfSection& section = sections_[i];
        HeaderSlot slot;
        slot.name = shstrtab.intern(section.name);
        slot.sh_type = section.sh_type;
        slot.flags = section.sh_flags;
        slot.align = section.align;
        slot.entsize = section.entsize;
        slot.size = section.content_size();
        if (section.nobits) {
            slot.offset = file.bytes.size();
        } else {
            file.pad_to(section.align ? section.align : 1);
            slot.offset = file.bytes.size();
            file.bytes.insert(file.bytes.end(), section.bytes.begin(),
                              section.bytes.end());
        }
        headers.push_back(slot);
    }
    for (size_t i = 0; i < content_count; ++i) {
        if (rela_payloads[i].empty()) {
            continue;
        }
        HeaderSlot slot;
        slot.name = shstrtab.intern(".rela" + sections_[i].name);
        slot.sh_type = SHT_RELA;
        slot.flags = SHF_INFO_LINK;
        slot.link = symtab_index;
        slot.info = static_cast<uint32_t>(i + 1);
        slot.align = word_align;
        slot.entsize = rela_entsize;
        file.pad_to(word_align);
        slot.offset = file.bytes.size();
        slot.size = rela_payloads[i].size();
        file.bytes.insert(file.bytes.end(), rela_payloads[i].begin(),
                          rela_payloads[i].end());
        headers.push_back(slot);
    }
    {
        HeaderSlot slot;
        slot.name = shstrtab.intern(".symtab");
        slot.sh_type = SHT_SYMTAB;
        slot.link = strtab_index;
        slot.info = first_global;
        slot.align = word_align;
        slot.entsize = sym_entsize;
        file.pad_to(word_align);
        slot.offset = file.bytes.size();
        slot.size = symtab_bytes.bytes.size();
        file.bytes.insert(file.bytes.end(), symtab_bytes.bytes.begin(),
                          symtab_bytes.bytes.end());
        headers.push_back(slot);
    }
    {
        HeaderSlot slot;
        slot.name = shstrtab.intern(".strtab");
        slot.sh_type = SHT_STRTAB;
        slot.align = 1;
        slot.offset = file.bytes.size();
        slot.size = strtab.bytes().size();
        file.bytes.insert(file.bytes.end(), strtab.bytes().begin(),
                          strtab.bytes().end());
        headers.push_back(slot);
    }
    {
        HeaderSlot slot;
        slot.name = shstrtab.intern(".shstrtab");
        slot.sh_type = SHT_STRTAB;
        slot.align = 1;
        slot.offset = file.bytes.size();

        slot.size = 0;
        headers.push_back(slot);
        const std::vector<uint8_t>& names = shstrtab.bytes();
        headers.back().size = names.size();
        file.bytes.insert(file.bytes.end(), names.begin(), names.end());
    }

    file.pad_to(word_align);
    const uint64_t shoff = file.bytes.size();
    for (const HeaderSlot& slot : headers) {
        if (is64) {
            file.u32(slot.name);
            file.u32(slot.sh_type);
            file.u64(slot.flags);
            file.u64(0);
            file.u64(slot.offset);
            file.u64(slot.size);
            file.u32(slot.link);
            file.u32(slot.info);
            file.u64(slot.align);
            file.u64(slot.entsize);
        } else {
            file.u32(slot.name);
            file.u32(slot.sh_type);
            file.u32(static_cast<uint32_t>(slot.flags));
            file.u32(0);
            file.u32(static_cast<uint32_t>(slot.offset));
            file.u32(static_cast<uint32_t>(slot.size));
            file.u32(slot.link);
            file.u32(slot.info);
            file.u32(static_cast<uint32_t>(slot.align));
            file.u32(static_cast<uint32_t>(slot.entsize));
        }
    }

    Buffer ehdr(data_);
    ehdr.u8(0x7F);
    ehdr.u8('E');
    ehdr.u8('L');
    ehdr.u8('F');
    ehdr.u8(is64 ? 2 : 1);  // ELFCLASS
    ehdr.u8(data_ == ElfData::Msb ? 2 : 1);  // ELFDATA
    ehdr.u8(1);  // EV_CURRENT
    for (int i = 7; i < 16; ++i) {
        ehdr.u8(0);
    }
    ehdr.u16(ET_REL);
    ehdr.u16(machine_);
    ehdr.u32(1);
    if (is64) {
        ehdr.u64(0);
        ehdr.u64(0);
        ehdr.u64(shoff);
    } else {
        ehdr.u32(0);
        ehdr.u32(0);
        ehdr.u32(static_cast<uint32_t>(shoff));
    }
    ehdr.u32(e_flags_);
    ehdr.u16(static_cast<uint16_t>(ehdr_size));
    ehdr.u16(0);
    ehdr.u16(0);
    ehdr.u16(static_cast<uint16_t>(shdr_size));
    ehdr.u16(static_cast<uint16_t>(headers.size()));
    ehdr.u16(static_cast<uint16_t>(shstrtab_index));
    for (size_t i = 0; i < ehdr.bytes.size(); ++i) {
        file.bytes[i] = ehdr.bytes[i];
    }

    out.write(reinterpret_cast<const char*>(file.bytes.data()),
              static_cast<std::streamsize>(file.bytes.size()));
    return out.good();
}

} // namespace aburi::backend
