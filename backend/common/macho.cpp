#include "macho.h"

#include <algorithm>
#include <cstring>
#include <map>

namespace aburi::backend {

namespace {

constexpr uint32_t MH_MAGIC_64 = 0xFEEDFACFu;
constexpr uint32_t MH_OBJECT = 0x1;
constexpr uint32_t MH_SUBSECTIONS_VIA_SYMBOLS = 0x2000;
constexpr uint32_t LC_SEGMENT_64 = 0x19;
constexpr uint32_t LC_SYMTAB = 0x2;
constexpr uint32_t LC_DYSYMTAB = 0xB;
constexpr uint32_t LC_BUILD_VERSION = 0x32;
constexpr uint32_t PLATFORM_MACOS = 1;
constexpr uint32_t VM_PROT_ALL = 7;

constexpr uint8_t N_UNDF = 0x0;
constexpr uint8_t N_SECT = 0xE;
constexpr uint8_t N_EXT = 0x1;
constexpr uint8_t N_PEXT = 0x10;
constexpr uint16_t N_WEAK_DEF = 0x0080;

struct Blob {
    std::vector<uint8_t> bytes;

    void u8(uint8_t value) { bytes.push_back(value); }
    void u16(uint16_t value) {
        for (int i = 0; i < 2; ++i) {
            bytes.push_back(static_cast<uint8_t>(value >> (8 * i)));
        }
    }
    void u32(uint32_t value) {
        for (int i = 0; i < 4; ++i) {
            bytes.push_back(static_cast<uint8_t>(value >> (8 * i)));
        }
    }
    void u64(uint64_t value) {
        for (int i = 0; i < 8; ++i) {
            bytes.push_back(static_cast<uint8_t>(value >> (8 * i)));
        }
    }
    void name16(const std::string& name) {
        char buffer[16] = {};
        std::memcpy(buffer, name.data(),
                    std::min<size_t>(name.size(), sizeof(buffer)));
        bytes.insert(bytes.end(), buffer, buffer + 16);
    }
    void pad_to(size_t boundary) {
        while (bytes.size() % boundary != 0) {
            bytes.push_back(0);
        }
    }
};

uint64_t align_up(uint64_t value, uint64_t align) {
    return (value + align - 1) & ~(align - 1);
}

struct SymtabEntry {
    std::string name;
    uint8_t n_type = 0;
    uint8_t n_sect = 0;
    uint16_t n_desc = 0;
    uint64_t n_value = 0;
};

} // namespace

bool apply_macho_section_attribute(const std::string& token, uint32_t& flags) {
    if (token == "regular") {
        flags = (flags & ~0xFFu) | MACHO_S_REGULAR;
    } else if (token == "cstring_literals") {
        flags = (flags & ~0xFFu) | MACHO_S_CSTRING_LITERALS;
    } else if (token == "literal_pointers") {
        flags = (flags & ~0xFFu) | MACHO_S_LITERAL_POINTERS;
    } else if (token == "coalesced") {
        flags = (flags & ~0xFFu) | MACHO_S_COALESCED;
    } else if (token == "mod_init_funcs") {
        flags = (flags & ~0xFFu) | MACHO_S_MOD_INIT_FUNC_POINTERS;
    } else if (token == "thread_local_regular") {
        flags = (flags & ~0xFFu) | MACHO_S_THREAD_LOCAL_REGULAR;
    } else if (token == "thread_local_zerofill") {
        flags = (flags & ~0xFFu) | MACHO_S_THREAD_LOCAL_ZEROFILL;
    } else if (token == "thread_local_variables") {
        flags = (flags & ~0xFFu) | MACHO_S_THREAD_LOCAL_VARIABLES;
    } else if (token == "no_dead_strip") {
        flags |= MACHO_S_ATTR_NO_DEAD_STRIP;
    } else if (token == "pure_instructions") {
        flags |= MACHO_S_ATTR_PURE_INSTRUCTIONS;
    } else {
        return false;
    }
    return true;
}

MachOBuilder::MachOBuilder(uint32_t cputype, uint32_t cpusubtype,
                           uint32_t minos_encoded)
    : cputype_(cputype), cpusubtype_(cpusubtype), minos_(minos_encoded) {}

int MachOBuilder::add_section(std::string segname, std::string sectname,
                              uint32_t flags, uint32_t align_log2,
                              bool zerofill) {
    MachOSection section;
    section.segname = std::move(segname);
    section.sectname = std::move(sectname);
    section.flags = flags;
    section.align_log2 = align_log2;
    section.zerofill = zerofill;
    sections_.push_back(std::move(section));
    return static_cast<int>(sections_.size()) - 1;
}

bool MachOBuilder::write(std::ostream& out, std::string& error) const {

    std::vector<int> order;
    for (int id = 0; id < static_cast<int>(sections_.size()); ++id) {
        if (!sections_[id].zerofill && sections_[id].content_size() > 0) {
            order.push_back(id);
        }
    }
    for (int id = 0; id < static_cast<int>(sections_.size()); ++id) {
        if (sections_[id].zerofill && sections_[id].content_size() > 0) {
            order.push_back(id);
        }
    }

    std::map<int, uint8_t> ordinal_of;
    for (size_t i = 0; i < order.size(); ++i) {
        ordinal_of[order[i]] = static_cast<uint8_t>(i + 1);
    }

    std::vector<uint64_t> addr(sections_.size(), 0);
    uint64_t cursor = 0;
    for (int id : order) {
        cursor = align_up(cursor, 1ull << sections_[id].align_log2);
        addr[id] = cursor;
        cursor += sections_[id].content_size();
    }
    uint64_t vmsize = cursor;
    uint64_t file_content_size = 0;
    for (int id : order) {
        if (!sections_[id].zerofill) {
            file_content_size = align_up(file_content_size,
                                         1ull << sections_[id].align_log2);
            file_content_size += sections_[id].bytes.size();
        }
    }

    std::vector<SymtabEntry> locals;
    std::vector<SymtabEntry> extdefs;
    std::vector<SymtabEntry> undefs;
    std::map<std::string, bool> defined_names;

    for (const MachOSymbol& symbol : symbols_) {
        if (symbol.section < 0 ||
            ordinal_of.find(symbol.section) == ordinal_of.end()) {
            error = "symbol '" + symbol.name + "' references an empty section";
            return false;
        }
        SymtabEntry entry;
        entry.name = symbol.name;
        entry.n_sect = ordinal_of[symbol.section];
        entry.n_value = addr[symbol.section] + symbol.offset_in_section;
        entry.n_type = N_SECT;
        if (symbol.external) {
            entry.n_type |= N_EXT;
        }
        if (symbol.private_extern) {
            entry.n_type |= N_PEXT;
        }
        if (symbol.weak_definition) {
            entry.n_desc |= N_WEAK_DEF;
        }
        defined_names[symbol.name] = true;
        if (symbol.external) {
            extdefs.push_back(std::move(entry));
        } else {
            locals.push_back(std::move(entry));
        }
    }
    for (const MachOCommon& common : commons_) {
        SymtabEntry entry;
        entry.name = common.name;
        entry.n_type = N_UNDF | N_EXT;
        entry.n_value = common.size;
        entry.n_desc = static_cast<uint16_t>((common.align_log2 & 0xF) << 8);
        defined_names[common.name] = true;
        undefs.push_back(std::move(entry));
    }

    for (const MachOSection& section : sections_) {
        for (const MachOReloc& reloc : section.relocs) {
            if (!reloc.external) {
                continue;
            }
            if (defined_names.find(reloc.symbol) == defined_names.end()) {
                SymtabEntry entry;
                entry.name = reloc.symbol;
                entry.n_type = N_UNDF | N_EXT;
                defined_names[reloc.symbol] = true;
                undefs.push_back(std::move(entry));
            }
        }
    }
    auto by_name = [](const SymtabEntry& a, const SymtabEntry& b) {
        return a.name < b.name;
    };
    std::sort(extdefs.begin(), extdefs.end(), by_name);
    std::sort(undefs.begin(), undefs.end(), by_name);

    std::vector<SymtabEntry> symtab;
    symtab.insert(symtab.end(), locals.begin(), locals.end());
    symtab.insert(symtab.end(), extdefs.begin(), extdefs.end());
    symtab.insert(symtab.end(), undefs.begin(), undefs.end());

    std::map<std::string, uint32_t> symbol_index;
    for (size_t i = 0; i < symtab.size(); ++i) {
        symbol_index[symtab[i].name] = static_cast<uint32_t>(i);
    }

    Blob strtab;
    strtab.u8(0);
    std::map<std::string, uint32_t> string_offset;
    for (const SymtabEntry& entry : symtab) {
        if (string_offset.find(entry.name) == string_offset.end()) {
            string_offset[entry.name] =
                static_cast<uint32_t>(strtab.bytes.size());
            strtab.bytes.insert(strtab.bytes.end(), entry.name.begin(),
                                entry.name.end());
            strtab.u8(0);
        }
    }
    strtab.pad_to(8);

    uint32_t nsects = static_cast<uint32_t>(order.size());
    uint32_t segment_cmd_size = 72 + nsects * 80;
    uint32_t build_version_size = 24;
    uint32_t symtab_cmd_size = 24;
    uint32_t dysymtab_cmd_size = 80;
    uint32_t sizeofcmds = segment_cmd_size + build_version_size +
                          symtab_cmd_size + dysymtab_cmd_size;
    uint64_t header_end = 32 + sizeofcmds;

    uint64_t max_align = 1;
    for (int id : order) {
        if (!sections_[id].zerofill) {
            max_align = std::max(max_align,
                                 uint64_t{1} << sections_[id].align_log2);
        }
    }
    uint64_t data_start = align_up(header_end, max_align);
    std::vector<uint64_t> file_offset(sections_.size(), 0);
    uint64_t file_cursor = data_start;
    for (int id : order) {
        if (sections_[id].zerofill) {
            continue;
        }
        file_offset[id] = data_start + addr[id];
        file_cursor = file_offset[id] + sections_[id].bytes.size();
    }
    uint64_t reloc_start = align_up(file_cursor, 8);

    std::vector<uint64_t> reloc_offset(sections_.size(), 0);
    uint64_t reloc_cursor = reloc_start;
    for (int id : order) {
        if (sections_[id].relocs.empty()) {
            continue;
        }
        reloc_offset[id] = reloc_cursor;
        reloc_cursor += sections_[id].relocs.size() * 8;
    }
    uint64_t symtab_offset = reloc_cursor;
    uint64_t strtab_offset = symtab_offset + symtab.size() * 16;

    Blob file;

    file.u32(MH_MAGIC_64);
    file.u32(cputype_);
    file.u32(cpusubtype_);
    file.u32(MH_OBJECT);
    file.u32(4);
    file.u32(sizeofcmds);
    file.u32(MH_SUBSECTIONS_VIA_SYMBOLS);
    file.u32(0);

    file.u32(LC_SEGMENT_64);
    file.u32(segment_cmd_size);
    file.name16("");
    file.u64(0);
    file.u64(vmsize);
    file.u64(data_start);
    file.u64(file_content_size == 0
                 ? 0
                 : (file_cursor - data_start));
    file.u32(VM_PROT_ALL);
    file.u32(VM_PROT_ALL);
    file.u32(nsects);
    file.u32(0);

    for (int id : order) {
        const MachOSection& section = sections_[id];
        file.name16(section.sectname);
        file.name16(section.segname);
        file.u64(addr[id]);
        file.u64(section.content_size());
        file.u32(section.zerofill
                     ? 0
                     : static_cast<uint32_t>(file_offset[id]));
        file.u32(section.align_log2);
        file.u32(section.relocs.empty()
                     ? 0
                     : static_cast<uint32_t>(reloc_offset[id]));
        file.u32(static_cast<uint32_t>(section.relocs.size()));
        file.u32(section.flags);
        file.u32(0);
        file.u32(0);
        file.u32(0);
    }

    file.u32(LC_BUILD_VERSION);
    file.u32(build_version_size);
    file.u32(PLATFORM_MACOS);
    file.u32(minos_);
    file.u32(0);
    file.u32(0);

    file.u32(LC_SYMTAB);
    file.u32(symtab_cmd_size);
    file.u32(static_cast<uint32_t>(symtab_offset));
    file.u32(static_cast<uint32_t>(symtab.size()));
    file.u32(static_cast<uint32_t>(strtab_offset));
    file.u32(static_cast<uint32_t>(strtab.bytes.size()));

    file.u32(LC_DYSYMTAB);
    file.u32(dysymtab_cmd_size);
    file.u32(0);
    file.u32(static_cast<uint32_t>(locals.size()));
    file.u32(static_cast<uint32_t>(locals.size()));
    file.u32(static_cast<uint32_t>(extdefs.size()));
    file.u32(static_cast<uint32_t>(locals.size() + extdefs.size()));
    file.u32(static_cast<uint32_t>(undefs.size()));
    for (int i = 0; i < 12; ++i) {
        file.u32(0);
    }

    for (int id : order) {
        if (sections_[id].zerofill) {
            continue;
        }
        while (file.bytes.size() <
               static_cast<size_t>(file_offset[id])) {
            file.u8(0);
        }
        std::vector<uint8_t> contents = sections_[id].bytes;
        for (const MachOReloc& reloc : sections_[id].relocs) {

            bool absolute = !reloc.pcrel &&
                            reloc.type == MACHO_ARM64_RELOC_UNSIGNED;
            if (reloc.external ||
                (!absolute && !reloc.section_relative_field)) {
                continue;
            }
            size_t width = 1ull << reloc.length;
            if (reloc.section < 0 ||
                static_cast<size_t>(reloc.section) >= addr.size() ||
                ordinal_of.find(reloc.section) == ordinal_of.end()) {
                error = "local relocation references an empty section";
                return false;
            }
            if (width > 8 || reloc.offset + width > contents.size()) {
                error = "local relocation field is outside its section";
                return false;
            }
            uint64_t value = 0;
            for (size_t i = 0; i < width; ++i) {
                value |= static_cast<uint64_t>(contents[reloc.offset + i])
                         << (8 * i);
            }
            value += reloc.section_relative_field
                         ? static_cast<uint64_t>(
                               static_cast<int64_t>(addr[reloc.section]) -
                               static_cast<int64_t>(addr[id]))
                         : addr[reloc.section];
            for (size_t i = 0; i < width; ++i) {
                contents[reloc.offset + i] =
                    static_cast<uint8_t>(value >> (8 * i));
            }
        }
        file.bytes.insert(file.bytes.end(), contents.begin(), contents.end());
    }

    while (file.bytes.size() < static_cast<size_t>(reloc_start)) {
        file.u8(0);
    }
    for (int id : order) {
        const MachOSection& section = sections_[id];
        if (section.relocs.empty()) {
            continue;
        }
        std::vector<MachOReloc> ordered = section.relocs;
        std::stable_sort(ordered.begin(), ordered.end(),
                         [](const MachOReloc& a, const MachOReloc& b) {
                             return a.offset > b.offset;
                         });
        for (const MachOReloc& reloc : ordered) {
            file.u32(static_cast<uint32_t>(reloc.offset));
            uint32_t info = 0;
            if (reloc.external) {
                auto found = symbol_index.find(reloc.symbol);
                if (found == symbol_index.end()) {
                    error = "relocation against unknown symbol '" +
                            reloc.symbol + "'";
                    return false;
                }
                info = found->second & 0x00FFFFFFu;
                info |= 1u << 27;
            } else {
                auto found = ordinal_of.find(reloc.section);
                if (found == ordinal_of.end()) {
                    error = "local relocation references an empty section";
                    return false;
                }
                info = found->second & 0x00FFFFFFu;
            }
            if (reloc.pcrel) {
                info |= 1u << 24;
            }
            info |= static_cast<uint32_t>(reloc.length & 0x3) << 25;
            info |= static_cast<uint32_t>(reloc.type & 0xF) << 28;
            file.u32(info);
        }
    }

    for (const SymtabEntry& entry : symtab) {
        file.u32(string_offset[entry.name]);
        file.u8(entry.n_type);
        file.u8(entry.n_sect);
        file.u16(entry.n_desc);
        file.u64(entry.n_value);
    }

    file.bytes.insert(file.bytes.end(), strtab.bytes.begin(),
                      strtab.bytes.end());

    out.write(reinterpret_cast<const char*>(file.bytes.data()),
              static_cast<std::streamsize>(file.bytes.size()));
    return out.good();
}

} // namespace aburi::backend
