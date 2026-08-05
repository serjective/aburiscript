#include "asm_emit.h"

#include <algorithm>
#include <cstdio>
#include <string>

#include "insts.h"
#include "target.h"

namespace aburi::backend::or1k {

namespace {

std::string reg_name(uint32_t phys) { return "r" + std::to_string(phys); }

uint32_t p2align(uint32_t align_bytes) {
    uint32_t log2 = 0;
    while ((1u << log2) < align_bytes) {
        ++log2;
    }
    return log2;
}

std::string escaped_ascii(const std::vector<uint8_t>& bytes, size_t begin,
                          size_t end) {
    std::string text;
    for (size_t i = begin; i < end; ++i) {
        uint8_t byte = bytes[i];
        if (byte == '"' || byte == '\\') {
            text += '\\';
            text += static_cast<char>(byte);
        } else if (byte >= 0x20 && byte < 0x7F) {
            text += static_cast<char>(byte);
        } else {
            char octal[5];
            std::snprintf(octal, sizeof(octal), "\\%03o", byte);
            text += octal;
        }
    }
    return text;
}

std::string symbol_ref(const MOperand& operand) {
    std::string text = operand.symbol;
    if (operand.addend > 0) {
        text += "+" + std::to_string(operand.addend);
    } else if (operand.addend < 0) {
        text += std::to_string(operand.addend);
    }
    return text;
}

} // namespace

std::string AsmTextEmitter::block_label(const MFunction& function,
                                        uint32_t block_index) const {
    return ".LBB" + std::to_string(function.index) + "_" +
           std::to_string(block_index);
}

std::string AsmTextEmitter::func_begin_label(const MFunction& function) const {
    return ".Lfunc_begin" + std::to_string(function.index);
}
std::string AsmTextEmitter::func_end_label(const MFunction& function) const {
    return ".Lfunc_end" + std::to_string(function.index);
}
std::string AsmTextEmitter::exception_label(const MFunction& function) const {
    return ".Lexception" + std::to_string(function.index);
}
std::string AsmTextEmitter::eh_label(const MFunction& function,
                                     uint32_t label) const {
    return ".LEH" + std::to_string(function.index) + "_" +
           std::to_string(label);
}
std::string AsmTextEmitter::action_base_label(const MFunction& function) const {
    return ".LEHaction_base" + std::to_string(function.index);
}
std::string AsmTextEmitter::action_next_label(const MFunction& function,
                                              uint32_t label) const {
    return eh_label(function, label) + "_next";
}
std::string AsmTextEmitter::typeinfo_entry_label(const MFunction& function,
                                                 uint32_t filter) const {
    return ".LEHtypeinfo" + std::to_string(function.index) + "_" +
           std::to_string(filter);
}

void AsmTextEmitter::begin_module(const air::Module&) {}

void AsmTextEmitter::emit_module_asm(const std::string& text) {
    out_ << text << '\n';
    in_text_section_ = false;
}

void AsmTextEmitter::emit_symbol_visibility(const std::string& symbol,
                                            air::Linkage linkage,
                                            const air::SymbolAttrs& attrs) {
    switch (linkage) {
        case air::Linkage::Internal:
            break;
        case air::Linkage::External:
        case air::Linkage::Common:
            out_ << "\t.globl\t" << symbol << '\n';
            break;
        case air::Linkage::LinkOnceODR:
        case air::Linkage::Weak:
            out_ << "\t.weak\t" << symbol << '\n';
            break;
    }
    if ((attrs.hidden || attrs.visibility == air::SymbolVisibility::Hidden) &&
        linkage != air::Linkage::Internal) {
        out_ << "\t.hidden\t" << symbol << '\n';
    } else if (attrs.visibility == air::SymbolVisibility::Protected &&
               linkage != air::Linkage::Internal) {
        out_ << "\t.protected\t" << symbol << '\n';
    }
}

void AsmTextEmitter::begin_function(const MFunction& function) {
    if (!function.attrs.comdat_key.empty()) {
        out_ << "\t.section\t.text." << function.name
             << ",\"axG\",@progbits," << function.attrs.comdat_key
             << ",comdat\n";
        in_text_section_ = false;
    } else if (!in_text_section_) {
        out_ << "\t.text\n";
        in_text_section_ = true;
    }
    in_function_ = true;
    cfi_frame_emitted_ = false;
    current_function_has_lsda_ =
        emit_unwind_tables_ && !function.eh_call_sites.empty();
    emit_symbol_visibility(function.name, function.linkage, function.attrs);
    out_ << "\t.p2align\t2\n";
    out_ << "\t.type\t" << function.name << ",@function\n";
    out_ << function.name << ":\n";
    if (emit_unwind_tables_) {
        out_ << func_begin_label(function) << ":\n";
        out_ << "\t.cfi_startproc\n";
        if (current_function_has_lsda_) {

            out_ << "\t.cfi_personality 0x9b, DW.ref.__gxx_personality_v0\n";
            dw_refs_.insert("__gxx_personality_v0");
            out_ << "\t.cfi_lsda 0x1b, " << exception_label(function) << '\n';
        }
    }
}

void AsmTextEmitter::emit_frame_cfi(const MFunction& function) {

    out_ << "\t.cfi_def_cfa 1, " << function.frame_size << '\n';
    for (const auto& entry : function.csr_cfa_offsets) {
        out_ << "\t.cfi_offset " << entry.first << ", " << entry.second
             << '\n';
    }
}

void AsmTextEmitter::emit_block_label(const MFunction& function,
                                      uint32_t block_index) {
    out_ << block_label(function, block_index) << ":\n";
}

void AsmTextEmitter::emit_set_bool(const MInst& inst) {

    std::string label = ".Lsb" + std::to_string(local_counter_++);
    std::string rd = reg_name(inst.operands[0].reg.index());
    const char* branch = inst.aux == 0 ? "l.bf" : "l.bnf";
    out_ << '\t' << branch << '\t' << label << '\n';
    out_ << "\tl.ori\t" << rd << ", r0, 1\n";
    out_ << "\tl.ori\t" << rd << ", r0, 0\n";
    out_ << label << ":\n";
}

void AsmTextEmitter::emit_inst(const MFunction& function, const MInst& inst) {
    Or1kOp opcode = static_cast<Or1kOp>(inst.opcode);

    if (emit_unwind_tables_ && in_function_ && !cfi_frame_emitted_) {
        emit_frame_cfi(function);
        cfi_frame_emitted_ = true;
    }
    if (opcode == Or1kOp::EhLabel) {
        if (emit_unwind_tables_) {
            out_ << eh_label(function, inst.aux) << ":\n";
        }
        return;
    }
    if (opcode == Or1kOp::SetBool) {
        emit_set_bool(inst);
        return;
    }
    if (opcode == Or1kOp::AsmBlock) {
        out_ << "\t#APP\n" << function.asm_texts[inst.aux] << "\t#NO_APP\n";
        return;
    }

    std::string_view mnemonic = or1k_mnemonic(opcode);
    InstFormat format = or1k_format(opcode);
    auto rn = [&](size_t i) { return reg_name(inst.operands[i].reg.index()); };

    out_ << '\t' << mnemonic;
    switch (format) {
        case InstFormat::RR:

            out_ << '\t' << rn(0) << ", " << rn(1) << ", " << rn(1);
            break;
        case InstFormat::RRR:
            out_ << '\t' << rn(0) << ", " << rn(1) << ", " << rn(2);
            break;
        case InstFormat::RRI:
            out_ << '\t' << rn(0) << ", " << rn(1) << ", "
                 << inst.operands[2].imm;
            break;
        case InstFormat::RImm:
            out_ << '\t' << rn(0) << ", " << inst.operands[1].imm;
            break;
        case InstFormat::RSymHi:
            out_ << '\t' << rn(0) << ", hi(" << symbol_ref(inst.operands[1])
                 << ")";
            break;
        case InstFormat::RRSymLo:
            out_ << '\t' << rn(0) << ", " << rn(1) << ", lo("
                 << symbol_ref(inst.operands[2]) << ")";
            break;
        case InstFormat::Mem:
            out_ << '\t' << rn(0) << ", " << inst.operands[2].imm << "("
                 << rn(1) << ")";
            break;
        case InstFormat::MemStore:
            out_ << '\t' << inst.operands[2].imm << "(" << rn(1) << "), "
                 << rn(0);
            break;
        case InstFormat::Sf:
            out_ << '\t' << rn(0) << ", " << rn(1);
            break;
        case InstFormat::SfI:
            out_ << '\t' << rn(0) << ", " << inst.operands[1].imm;
            break;
        case InstFormat::Branch:
            out_ << '\t' << block_label(function, inst.operands[0].label);
            break;
        case InstFormat::CallSym:
            out_ << '\t' << symbol_ref(inst.operands[0]);
            break;
        case InstFormat::CallReg:
        case InstFormat::JmpReg:
            out_ << '\t' << rn(0);
            break;
        case InstFormat::Nop:
            break;
        case InstFormat::SetBool:
        case InstFormat::AsmText:
            break;
    }
    out_ << '\n';

    if ((or1k_flags(opcode) & OR1K_DELAY) != 0) {
        out_ << "\tl.nop\n";
    }
}

void AsmTextEmitter::end_function(const MFunction& function) {
    if (emit_unwind_tables_) {
        out_ << func_end_label(function) << ":\n";
        out_ << "\t.cfi_endproc\n";
    }
    out_ << "\t.size\t" << function.name << ", .-" << function.name << '\n';
    in_function_ = false;
    in_text_section_ = true;
    if (current_function_has_lsda_) {
        emit_lsda(function);
        in_text_section_ = false;
    }
}

void AsmTextEmitter::emit_lsda(const MFunction& function) {
    out_ << "\t.section\t.gcc_except_table,\"a\",@progbits\n";
    out_ << "\t.p2align\t2\n";
    out_ << exception_label(function) << ":\n";
    out_ << "\t.byte\t255\n";
    std::string idx = std::to_string(function.index);
    const std::string ttbase = ".Lttbase" + idx;
    const std::string ttbaseref = ".Lttbaseref" + idx;
    const std::string cst_begin = ".Lcst_begin" + idx;
    const std::string cst_end = ".Lcst_end" + idx;
    if (function.eh_typeinfos.empty()) {
        out_ << "\t.byte\t255\n";
    } else {
        out_ << "\t.byte\t0x9b\n";
        out_ << "\t.uleb128\t" << ttbase << '-' << ttbaseref << '\n';
        out_ << ttbaseref << ":\n";
    }
    out_ << "\t.byte\t1\n";
    out_ << "\t.uleb128\t" << cst_end << '-' << cst_begin << '\n';
    out_ << cst_begin << ":\n";
    std::string previous = func_begin_label(function);
    auto emit_empty_range = [&](const std::string& begin,
                                const std::string& end) {
        out_ << "\t.uleb128\t" << begin << '-' << func_begin_label(function)
             << '\n';
        out_ << "\t.uleb128\t" << end << '-' << begin << '\n';
        out_ << "\t.byte\t0\n\t.byte\t0\n";
    };
    for (const MEhCallSite& site : function.eh_call_sites) {
        std::string begin = eh_label(function, site.begin_label);
        if (previous != begin) {
            emit_empty_range(previous, begin);
        }
        out_ << "\t.uleb128\t" << eh_label(function, site.begin_label) << '-'
             << func_begin_label(function) << '\n';
        out_ << "\t.uleb128\t" << eh_label(function, site.end_label) << '-'
             << eh_label(function, site.begin_label) << '\n';
        out_ << "\t.uleb128\t" << block_label(function, site.landing_pad_block)
             << '-' << func_begin_label(function) << '\n';
        if (site.action_label == 0) {
            out_ << "\t.byte\t0\n";
        } else {
            out_ << "\t.uleb128\t" << eh_label(function, site.action_label)
                 << '-' << action_base_label(function) << "+1\n";
        }
        previous = eh_label(function, site.end_label);
    }
    if (previous != func_end_label(function)) {
        emit_empty_range(previous, func_end_label(function));
    }
    out_ << cst_end << ":\n";

    if (!function.eh_actions.empty()) {
        out_ << action_base_label(function) << ":\n";
        for (const MEhAction& action : function.eh_actions) {
            out_ << eh_label(function, action.label) << ":\n";
            out_ << "\t.sleb128\t" << action.filter << '\n';
            out_ << action_next_label(function, action.label) << ":\n";
            if (action.next_label == 0) {
                out_ << "\t.sleb128\t0\n";
            } else {
                out_ << "\t.sleb128\t" << eh_label(function, action.next_label)
                     << '-' << action_next_label(function, action.label)
                     << '\n';
            }
        }
    }

    if (!function.eh_typeinfos.empty()) {
        out_ << "\t.p2align\t2\n";
        std::vector<MEhTypeInfo> typeinfos = function.eh_typeinfos;
        std::sort(typeinfos.begin(), typeinfos.end(),
                  [](const MEhTypeInfo& a, const MEhTypeInfo& b) {
                      return a.filter > b.filter;
                  });
        for (const MEhTypeInfo& typeinfo : typeinfos) {
            std::string label = typeinfo_entry_label(function, typeinfo.filter);
            out_ << label << ":\n";
            if (typeinfo.symbol.empty()) {
                out_ << "\t.long\t0\n";
            } else {
                out_ << "\t.long\tDW.ref." << typeinfo.symbol << '-' << label
                     << '\n';
                dw_refs_.insert(typeinfo.symbol);
            }
        }
        out_ << ttbase << ":\n";
    }
    out_ << "\t.p2align\t2\n";
}

void AsmTextEmitter::emit_global(const air::Module& module,
                                 const air::GlobalData& global) {
    if (global.init.kind == air::GlobalInitKind::None) {
        return;
    }
    const std::string& symbol = global.name;
    in_text_section_ = false;

    if (global.linkage == air::Linkage::Common) {
        out_ << "\t.comm\t" << symbol << ',' << global.size_bytes << ','
             << global.align_bytes << '\n';
        return;
    }
    if (global.init.kind == air::GlobalInitKind::Zero) {
        if (!global.attrs.comdat_key.empty()) {
            out_ << "\t.section\t.bss." << symbol
                 << ",\"awG\",@nobits," << global.attrs.comdat_key
                 << ",comdat\n";
        } else {
            out_ << "\t.bss\n";
        }
        emit_symbol_visibility(symbol, global.linkage, global.attrs);
        if (global.align_bytes > 1) {
            out_ << "\t.p2align\t" << p2align(global.align_bytes) << '\n';
        }
        out_ << "\t.type\t" << symbol << ",@object\n";
        out_ << "\t.size\t" << symbol << ", " << global.size_bytes << '\n';
        out_ << symbol << ":\n\t.zero\t" << global.size_bytes << '\n';
        return;
    }

    if (!global.attrs.comdat_key.empty()) {
        bool read_only = global.section == air::SectionKind::Const &&
                         global.init.relocs.empty();
        out_ << "\t.section\t." << (read_only ? "rodata." : "data.")
             << symbol << (read_only ? ",\"aG\",@progbits,"
                                     : ",\"awG\",@progbits,")
             << global.attrs.comdat_key << ",comdat\n";
    } else switch (global.section) {
        case air::SectionKind::Cstring:
            out_ << "\t.section\t.rodata.str1.1,\"aMS\",@progbits,1\n";
            break;
        case air::SectionKind::Const:
        case air::SectionKind::Text:
            out_ << (global.init.relocs.empty()
                         ? "\t.section\t.rodata\n"
                         : "\t.section\t.data.rel.ro,\"aw\"\n");
            break;
        case air::SectionKind::Custom:
            out_ << "\t.section\t" << global.custom_section << '\n';
            break;
        case air::SectionKind::Data:
        case air::SectionKind::Zerofill:
            out_ << "\t.data\n";
            break;
    }
    emit_symbol_visibility(symbol, global.linkage, global.attrs);
    if (global.align_bytes > 1) {
        out_ << "\t.p2align\t" << p2align(global.align_bytes) << '\n';
    }
    out_ << "\t.type\t" << symbol << ",@object\n";
    out_ << "\t.size\t" << symbol << ", " << global.size_bytes << '\n';
    out_ << symbol << ":\n";

    const std::vector<uint8_t>& bytes = global.init.bytes;
    if (global.section == air::SectionKind::Cstring &&
        global.init.relocs.empty() && !bytes.empty()) {
        out_ << "\t.asciz\t\"" << escaped_ascii(bytes, 0, bytes.size() - 1)
             << "\"\n";
        return;
    }

    size_t offset = 0;
    size_t reloc_index = 0;
    while (offset < bytes.size()) {
        if (reloc_index < global.init.relocs.size() &&
            global.init.relocs[reloc_index].offset == offset) {
            const air::InitReloc& reloc = global.init.relocs[reloc_index];
            std::string target;
            if (reloc.is_function) {
                const air::Function& callee =
                    module.function(air::FuncId{reloc.target_index});
                target = callee.name();
            } else {
                const air::GlobalData& g =
                    module.global(air::GlobalId{reloc.target_index});
                target = g.name;
            }

            out_ << "\t.long\t" << target;
            if (reloc.addend > 0) {
                out_ << '+' << reloc.addend;
            } else if (reloc.addend < 0) {
                out_ << reloc.addend;
            }
            out_ << '\n';
            offset += 4;
            ++reloc_index;
            continue;
        }
        out_ << "\t.byte\t" << static_cast<uint32_t>(bytes[offset]) << '\n';
        ++offset;
    }
    if (bytes.size() < global.size_bytes) {
        out_ << "\t.space\t" << (global.size_bytes - bytes.size()) << ",0\n";
    }
}

void AsmTextEmitter::emit_ctor_list(const air::Module& module) {
    if (module.ctors().empty()) {
        return;
    }
    in_text_section_ = false;
    out_ << "\t.section\t.init_array,\"aw\",@init_array\n";
    out_ << "\t.p2align\t2\n";
    for (const air::CtorEntry& ctor : module.ctors()) {
        const air::Function& function = module.function(ctor.func);
        out_ << "\t.long\t" << function.name() << '\n';
    }
}

void AsmTextEmitter::end_module(const air::Module&) {

    for (const std::string& symbol : dw_refs_) {
        out_ << "\t.hidden\tDW.ref." << symbol << '\n';
        out_ << "\t.weak\tDW.ref." << symbol << '\n';
        out_ << "\t.section\t.data.rel.local.DW.ref." << symbol
             << ",\"awG\",@progbits,DW.ref." << symbol << ",comdat\n";
        out_ << "\t.p2align\t2\n";
        out_ << "\t.type\tDW.ref." << symbol << ",@object\n";
        out_ << "\t.size\tDW.ref." << symbol << ", 4\n";
        out_ << "DW.ref." << symbol << ":\n";
        out_ << "\t.long\t" << symbol << '\n';
    }
}

} // namespace aburi::backend::or1k
