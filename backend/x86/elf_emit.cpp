#include "elf_emit.h"

#include "encode.h"
#include "insts.h"
#include "target.h"

namespace aburi::backend::x86 {

namespace {

uint64_t align_up(uint64_t value, uint64_t align) {
    return (value + align - 1) & ~(align - 1);
}

std::string reloc_target_name(const air::Module& module,
                              const air::InitReloc& reloc) {
    if (reloc.is_function) {
        return module.function(air::FuncId{reloc.target_index}).name();
    }
    return module.global(air::GlobalId{reloc.target_index}).name;
}

void write_rel32(std::vector<uint8_t>& bytes, uint64_t field, int64_t value) {
    for (int i = 0; i < 4; ++i) {
        bytes[field + i] = static_cast<uint8_t>(value >> (8 * i));
    }
}

} // namespace

ElfEmitter::ElfEmitter(std::vector<Diagnostic>& diagnostics,
                       bool emit_unwind_tables, bool legacy32)
    : diagnostics_(diagnostics),
      builder_(legacy32 ? ELF_EM_386 : ELF_EM_X86_64),
      emit_unwind_tables_(emit_unwind_tables) {}

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
                                  ELF_SHF_ALLOC | ELF_SHF_EXECINSTR, 16);
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
    (void)module;
}

void ElfEmitter::emit_module_asm(const std::string& text) {
    (void)text;
    error("module-level assembly requires the assembler path "
          "(--air-object=as)");
}

void ElfEmitter::begin_function(const MFunction& function) {
    int text = text_section();
    ElfSection& section = builder_.section(text);
    while (section.bytes.size() % 16 != 0) {
        section.bytes.push_back(0x90);
    }

    if (emit_unwind_tables_ && !function.eh_call_sites.empty()) {
        error("C++ exception tables require the assembler path "
              "(--air-object=as) on ELF targets for now (function '" +
              function.name + "')");
    }

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
    (void)function;
    if (static_cast<X86Op>(inst.opcode) == X86Op::EhLabel) {
        return;
    }
    int text = text_section();
    ElfSection& section = builder_.section(text);
    uint64_t inst_offset = section.bytes.size();

    EncodedInst encoded = encode_x86(inst);
    if (!encoded.ok) {
        error("cannot encode instruction: " + encoded.error);
        return;
    }
    uint64_t field_offset = inst_offset + encoded.fixup_offset;

    switch (encoded.fixup) {
        case TextFixup::None:
            break;
        case TextFixup::SymBranch32:
        case TextFixup::SymRip32: {
            const MOperand& operand = inst.operands[encoded.fixup_operand];
            if (operand.addend != 0) {
                error("symbol addend on an instruction operand is not "
                      "supported by the direct object writer: " +
                      operand.symbol);
                return;
            }
            if (encoded.fixup == TextFixup::SymBranch32) {
                pending_sym_branches_.push_back({field_offset, operand.symbol});
                break;
            }

            ElfReloc reloc;
            reloc.offset = field_offset;
            reloc.symbol = operand.symbol;
            reloc.type = operand.flavor == SymFlavor::GotPcRel
                             ? ELF_R_X86_64_GOTPCREL
                             : ELF_R_X86_64_PC32;
            reloc.addend = -4;
            section.relocs.push_back(std::move(reloc));
            break;
        }
        case TextFixup::LabelRel32: {
            PendingLabelFixup fixup;
            fixup.field_offset = field_offset;
            fixup.target_block = encoded.fixup_label;
            pending_labels_.push_back(fixup);
            break;
        }
    }

    section.bytes.insert(section.bytes.end(), encoded.bytes,
                         encoded.bytes + encoded.size);
}

void ElfEmitter::end_function(const MFunction& function) {
    (void)function;
    int text = text_section();
    ElfSection& section = builder_.section(text);
    for (const PendingLabelFixup& fixup : pending_labels_) {
        auto found = block_offsets_.find(fixup.target_block);
        if (found == block_offsets_.end()) {
            error("branch to an unemitted block label");
            continue;
        }
        write_rel32(section.bytes, fixup.field_offset,
                    static_cast<int64_t>(found->second) -
                        (static_cast<int64_t>(fixup.field_offset) + 4));
    }
    pending_labels_.clear();
    builder_.symbol(current_function_symbol_index_).size =
        section.bytes.size() - current_function_start_;
    block_offsets_.clear();
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
        record.type = ELF_R_X86_64_64;
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
        record.type = ELF_R_X86_64_64;
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

            write_rel32(section.bytes, branch.field_offset,
                        static_cast<int64_t>(found->second) -
                            (static_cast<int64_t>(branch.field_offset) + 4));
            continue;
        }
        ElfReloc reloc;
        reloc.offset = branch.field_offset;
        reloc.symbol = branch.symbol;
        reloc.type = ELF_R_X86_64_PLT32;
        reloc.addend = -4;
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

} // namespace aburi::backend::x86
