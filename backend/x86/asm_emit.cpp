#include "asm_emit.h"

#include <algorithm>
#include <cassert>
#include <string>
#include <vector>

#include "insts.h"
#include "target.h"

namespace aburi::backend::x86 {

namespace {

constexpr const char* kGpr64[] = {
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi",
    "r8",  "r9",  "r10", "r11", "r12", "r13", "r14", "r15",
};

std::string reg_name(uint32_t phys, char width) {
    return att_reg_name(phys, width);
}

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

} // namespace

namespace {

// Assembler symbol charset: anything else (Objective-C method symbols like
// -[Foo bar:], $-suffixed metadata names on ELF) must be quoted.
bool needs_symbol_quoting(const std::string& name) {
    for (char c : name) {
        bool plain = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
                     (c >= '0' && c <= '9') || c == '_' || c == '$' ||
                     c == '.';
        if (!plain) {
            return true;
        }
    }
    return false;
}

std::string quoted_symbol(std::string name) {
    if (!needs_symbol_quoting(name)) {
        return name;
    }
    return "\"" + name + "\"";
}

} // namespace

std::string AsmTextEmitter::object_symbol(const std::string& name,
                                          bool no_prefix) const {
    if (no_prefix || elf_) {
        return quoted_symbol(name);
    }
    return quoted_symbol("_" + name);
}

std::string AsmTextEmitter::rip_symbol_ref(const MOperand& operand) const {
    std::string text = quoted_symbol(operand.symbol);
    if (operand.addend != 0) {
        text += "+" + std::to_string(operand.addend);
    }

    if (operand.flavor == SymFlavor::GotPcRel) {
        text += "@GOTPCREL";
    } else if (operand.flavor == SymFlavor::TlvPcRel) {
        text += "@TLVP";
    }
    return text + "(%rip)";
}

std::string AsmTextEmitter::local_label(const std::string& stem) const {

    return (elf_ ? ".L" : "L") + stem;
}

std::string AsmTextEmitter::block_label(const MFunction& function,
                                        uint32_t block_index) const {
    return local_label("BB" + std::to_string(function.index) + "_" +
                       std::to_string(block_index));
}

std::string AsmTextEmitter::eh_label(const MFunction& function,
                                     uint32_t label) const {
    return local_label("EH" + std::to_string(function.index) + "_" +
                       std::to_string(label));
}

std::string AsmTextEmitter::func_begin_label(const MFunction& function) const {
    return local_label("func_begin_air" + std::to_string(function.index));
}

std::string AsmTextEmitter::func_end_label(const MFunction& function) const {
    return local_label("func_end_air" + std::to_string(function.index));
}

std::string AsmTextEmitter::exception_label(const MFunction& function) const {
    return local_label("exception_air" + std::to_string(function.index));
}

std::string AsmTextEmitter::action_base_label(const MFunction& function) const {
    return local_label("EH_action_base" + std::to_string(function.index));
}

std::string AsmTextEmitter::action_next_label(const MFunction& function,
                                              uint32_t label) const {
    return eh_label(function, label) + "_next";
}

std::string AsmTextEmitter::typeinfo_entry_label(const MFunction& function,
                                                 uint32_t filter) const {
    return local_label("EH_typeinfo" + std::to_string(function.index) + "_" +
                       std::to_string(filter));
}

void AsmTextEmitter::begin_module(const air::Module& module) {
    (void)module;
    if (code16_) {

        out_ << "\t.code16gcc\n";
    }
}

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
            if (elf_) {
                out_ << "\t.weak\t" << symbol << '\n';
            } else {
                out_ << "\t.globl\t" << symbol << '\n';
                out_ << "\t.weak_definition\t" << symbol << '\n';
            }
            break;
    }
    if ((attrs.hidden || attrs.visibility == air::SymbolVisibility::Hidden) &&
        linkage != air::Linkage::Internal) {
        out_ << (elf_ ? "\t.hidden\t" : "\t.private_extern\t") << symbol
             << '\n';
    } else if (elf_ &&
               attrs.visibility == air::SymbolVisibility::Protected &&
               linkage != air::Linkage::Internal) {
        out_ << "\t.protected\t" << symbol << '\n';
    }
}

void AsmTextEmitter::begin_function(const MFunction& function) {
    if (elf_ && !function.attrs.comdat_key.empty()) {
        out_ << "\t.section\t.text." << function.name
             << ",\"axG\",@progbits," << function.attrs.comdat_key
             << ",comdat\n";
        in_text_section_ = false;
    } else if (!in_text_section_) {
        out_ << (elf_ ? "\t.text\n"
                      : "\t.section\t__TEXT,__text,regular,pure_instructions\n");
        in_text_section_ = true;
    }
    in_function_ = true;
    cfi_push_emitted_ = false;
    cfi_frame_emitted_ = false;
    current_function_has_lsda_ =
        emit_unwind_tables_ && !function.eh_call_sites.empty();
    emit_symbol_visibility(quoted_symbol(function.name), function.linkage,
                           function.attrs);
    out_ << "\t.p2align\t4\n";
    if (elf_) {
        out_ << "\t.type\t" << quoted_symbol(function.name)
             << ",@function\n";
    }
    out_ << quoted_symbol(function.name) << ":\n";
    if (emit_unwind_tables_) {
        out_ << func_begin_label(function) << ":\n";
        out_ << "\t.cfi_startproc\n";
        if (current_function_has_lsda_) {
            if (elf_) {

                out_ << "\t.cfi_personality 155, "
                        "DW.ref.__gxx_personality_v0\n";
                dw_refs_.insert("__gxx_personality_v0");
                out_ << "\t.cfi_lsda 27, " << exception_label(function)
                     << '\n';
            } else {
                out_ << "\t.cfi_personality 155, ___gxx_personality_v0\n";
                out_ << "\t.cfi_lsda 16, " << exception_label(function)
                     << '\n';
            }
        }
    }
}

void AsmTextEmitter::emit_block_label(const MFunction& function,
                                      uint32_t block_index) {
    if (function.blocks[block_index].address_taken) {

        out_ << "l_air_lbl_" << function.index << '_' << block_index << ":\n";
    }
    out_ << block_label(function, block_index) << ":\n";
}

void AsmTextEmitter::emit_inst(const MFunction& function, const MInst& inst) {
    X86Op opcode = static_cast<X86Op>(inst.opcode);
    if (opcode == X86Op::EhLabel) {
        if (emit_unwind_tables_) {
            out_ << eh_label(function, inst.aux) << ":\n";
        }
        return;
    }
    if (opcode == X86Op::AsmBlock) {

        out_ << "\t#APP\n" << function.asm_texts[inst.aux] << "\t#NO_APP\n";
        return;
    }
    if (opcode == X86Op::RetQ && legacy32_ && function.callee_pop_bytes > 0) {

        out_ << "\tret\t$" << function.callee_pop_bytes << "\n";
        return;
    }
    std::string_view widths = x86_widths(opcode);
    InstFormat format = x86_format(opcode);

    bool gpr_op = widths.find('x') == std::string_view::npos;
    std::string mnemonic(x86_mnemonic(opcode));
    if (legacy32_ && gpr_op && !mnemonic.empty() && mnemonic.back() == 'q') {
        mnemonic = mnemonic == "retq" ? "ret"
                                      : mnemonic.substr(0, mnemonic.size() - 1) + "l";
    }
    auto width_of = [&](char declared) {
        return (legacy32_ && declared == 'q') ? 'l' : declared;
    };
    auto rn = [&](size_t operand_index) {
        char width = operand_index < widths.size() ? widths[operand_index]
                                                   : 'q';
        return reg_name(inst.operands[operand_index].reg.index(),
                        width_of(width));
    };
    auto mem = [&](size_t base_index) {
        std::string text;
        const MOperand& disp = inst.operands[base_index + 1];
        if (disp.imm != 0) {
            text += std::to_string(disp.imm);
        }
        text += '(';
        text += reg_name(inst.operands[base_index].reg.index(), width_of('q'));
        text += ')';
        return text;
    };

    out_ << '\t' << mnemonic;
    switch (format) {
        case InstFormat::RR:
            out_ << '\t' << rn(1) << ", " << rn(0);
            break;
        case InstFormat::RI:
        case InstFormat::MovAbs:
            out_ << "\t$" << inst.operands[1].imm << ", " << rn(0);
            break;
        case InstFormat::R1:
            out_ << '\t' << rn(0);
            break;
        case InstFormat::Load:
            out_ << '\t' << mem(1) << ", " << rn(0);
            break;
        case InstFormat::Store:
        case InstFormat::MemRmw:
            out_ << '\t' << rn(0) << ", " << mem(1);
            break;
        case InstFormat::FpuMem:
            out_ << '\t' << mem(0);
            break;
        case InstFormat::RipR:
            out_ << '\t' << rip_symbol_ref(inst.operands[1]) << ", " << rn(0);
            break;
        case InstFormat::SymImm: {
            const MOperand& sym = inst.operands[1];
            out_ << "\t$" << sym.symbol;
            if (sym.addend != 0) {
                out_ << '+' << sym.addend;
            }
            out_ << ", " << rn(0);
            break;
        }
        case InstFormat::ShiftCl:
            out_ << "\t%cl, " << rn(0);
            break;
        case InstFormat::Jmp:
            out_ << '\t' << block_label(function, inst.operands[0].label);
            break;
        case InstFormat::Jcc:
            out_ << cond_name(static_cast<Cond>(inst.aux)) << '\t'
                 << block_label(function, inst.operands[0].label);
            break;
        case InstFormat::JmpReg:
            out_ << "\t*" << rn(0);
            break;
        case InstFormat::CallSym: {
            const MOperand& callee = inst.operands[0];
            out_ << '\t' << callee.symbol;
            if (callee.addend != 0) {
                out_ << '+' << callee.addend;
            }
            break;
        }
        case InstFormat::CallReg:
            out_ << "\t*" << rn(0);
            break;
        case InstFormat::Setcc:
            out_ << cond_name(static_cast<Cond>(inst.aux)) << '\t' << rn(0);
            break;
        case InstFormat::Cmov:
            out_ << cond_name(static_cast<Cond>(inst.aux)) << '\t' << rn(1)
                 << ", " << rn(0);
            break;
        case InstFormat::DivR:
            out_ << '\t' << rn(0);
            break;
        case InstFormat::NoOps:
        case InstFormat::Ret:
        case InstFormat::AsmText:
            break;
    }
    out_ << '\n';

    if (emit_unwind_tables_ && in_function_) {
        const char* bp = legacy32_ ? "ebp" : "rbp";
        int word = legacy32_ ? 4 : 8;
        if (!cfi_push_emitted_ && opcode == X86Op::PushR &&
            inst.operands[0].kind == MOperandKind::Reg &&
            inst.operands[0].reg.index() == RBP) {
            out_ << "\t.cfi_def_cfa_offset " << (2 * word) << '\n';
            out_ << "\t.cfi_offset %" << bp << ", " << (-2 * word) << '\n';
            cfi_push_emitted_ = true;
        } else if (!cfi_frame_emitted_ && opcode == X86Op::MovRR64 &&
                   inst.operands.size() == 2 &&
                   inst.operands[0].kind == MOperandKind::Reg &&
                   inst.operands[1].kind == MOperandKind::Reg &&
                   inst.operands[0].reg.index() == RBP &&
                   inst.operands[1].reg.index() == RSP) {
            out_ << "\t.cfi_def_cfa_register %" << bp << '\n';

            for (const auto& [phys, cfa_offset] : function.csr_cfa_offsets) {
                out_ << "\t.cfi_offset %"
                     << att_reg_name(phys, legacy32_ ? 'l' : 'q').substr(1)
                     << ", " << cfa_offset << '\n';
            }
            cfi_frame_emitted_ = true;
        }
    }
}

void AsmTextEmitter::end_function(const MFunction& function) {
    if (emit_unwind_tables_) {
        out_ << func_end_label(function) << ":\n";
        out_ << "\t.cfi_endproc\n";
    }
    if (elf_) {
        out_ << "\t.size\t" << quoted_symbol(function.name) << ", .-"
             << quoted_symbol(function.name)
             << '\n';
    }
    out_ << '\n';
    in_function_ = false;
    if (current_function_has_lsda_) {
        emit_lsda(function);
    }
}

void AsmTextEmitter::emit_lsda(const MFunction& function) {
    in_text_section_ = false;
    out_ << (elf_ ? "\t.section\t.gcc_except_table,\"a\",@progbits\n"
                  : "\t.section\t__TEXT,__gcc_except_tab\n");
    out_ << "\t.p2align\t2, 0x0\n";
    out_ << "GCC_except_table_air" << function.index << ":\n";
    out_ << exception_label(function) << ":\n";
    out_ << "\t.byte\t255\n";
    const std::string ttbase =
        local_label("ttbase_air" + std::to_string(function.index));
    const std::string ttbaseref =
        local_label("ttbaseref_air" + std::to_string(function.index));
    const std::string cst_begin =
        local_label("cst_begin_air" + std::to_string(function.index));
    const std::string cst_end =
        local_label("cst_end_air" + std::to_string(function.index));
    if (function.eh_typeinfos.empty()) {
        out_ << "\t.byte\t255\n";
    } else {
        out_ << "\t.byte\t155\n";
        out_ << "\t.uleb128\t" << ttbase << "-" << ttbaseref << '\n';
        out_ << ttbaseref << ":\n";
    }
    out_ << "\t.byte\t1\n";
    out_ << "\t.uleb128\t" << cst_end << "-" << cst_begin << '\n';
    out_ << cst_begin << ":\n";
    std::string previous = func_begin_label(function);
    auto emit_empty_range = [&](const std::string& begin,
                                const std::string& end) {
        out_ << "\t.uleb128\t" << begin << "-" << func_begin_label(function)
             << '\n';
        out_ << "\t.uleb128\t" << end << "-" << begin << '\n';
        out_ << "\t.byte\t0\n";
        out_ << "\t.byte\t0\n";
    };
    for (const MEhCallSite& site : function.eh_call_sites) {
        std::string begin = eh_label(function, site.begin_label);
        if (previous != begin) {
            emit_empty_range(previous, begin);
        }
        out_ << "\t.uleb128\t" << eh_label(function, site.begin_label)
             << "-" << func_begin_label(function) << '\n';
        out_ << "\t.uleb128\t" << eh_label(function, site.end_label)
             << "-" << eh_label(function, site.begin_label) << '\n';
        out_ << "\t.uleb128\t" << block_label(function, site.landing_pad_block)
             << "-" << func_begin_label(function) << '\n';
        if (site.action_label == 0) {
            out_ << "\t.byte\t0\n";
        } else {
            out_ << "\t.uleb128\t" << eh_label(function, site.action_label)
                 << "-" << action_base_label(function) << "+1\n";
        }
        previous = eh_label(function, site.end_label);
    }
    if (previous != func_end_label(function)) {
        emit_empty_range(previous, func_end_label(function));
    }
    out_ << local_label("cst_end_air" + std::to_string(function.index))
         << ":\n";

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
                     << "-" << action_next_label(function, action.label)
                     << '\n';
            }
        }
    }

    if (!function.eh_typeinfos.empty()) {
        out_ << "\t.p2align\t2, 0x0\n";
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
            } else if (elf_) {
                out_ << "\t.long\tDW.ref." << typeinfo.symbol << "-" << label
                     << '\n';
                dw_refs_.insert(typeinfo.symbol);
            } else {

                out_ << "\t.long\t" << typeinfo.symbol << "@GOTPCREL+4\n";
            }
        }
        out_ << local_label("ttbase_air" + std::to_string(function.index))
             << ":\n";
    }
    out_ << "\t.p2align\t2, 0x0\n";
}

void AsmTextEmitter::emit_global(const air::Module& module,
                                 const air::GlobalData& global) {
    if (global.init.kind == air::GlobalInitKind::None) {
        return;
    }
    std::string symbol = object_symbol(global.name, global.attrs.no_prefix);
    in_text_section_ = false;

    if (global.is_thread_local) {
        std::string storage = symbol + "$tlv$init";
        bool zero = global.init.kind == air::GlobalInitKind::Zero;
        if (elf_) {
            if (!global.attrs.comdat_key.empty()) {
                out_ << "\t.section\t."
                     << (zero ? "tbss." : "tdata.") << symbol
                     << (zero ? ",\"awTG\",@nobits,"
                              : ",\"awTG\",@progbits,")
                     << global.attrs.comdat_key << ",comdat\n";
            } else {
                out_ << (zero ? "\t.section\t.tbss,\"awT\",@nobits\n"
                              : "\t.section\t.tdata,\"awT\",@progbits\n");
            }
            emit_symbol_visibility(symbol, global.linkage, global.attrs);
            if (global.align_bytes > 1) {
                out_ << "\t.p2align\t" << p2align(global.align_bytes) << '\n';
            }
            out_ << "\t.type\t" << symbol << ",@object\n";
            out_ << "\t.size\t" << symbol << ", " << global.size_bytes
                 << '\n';
            out_ << symbol << ":\n";
            if (zero) {
                out_ << "\t.zero\t" << global.size_bytes << '\n';
            } else {
                for (uint8_t byte : global.init.bytes) {
                    out_ << "\t.byte\t" << static_cast<uint32_t>(byte)
                         << '\n';
                }
                if (global.init.bytes.size() < global.size_bytes) {
                    out_ << "\t.zero\t"
                         << global.size_bytes - global.init.bytes.size()
                         << '\n';
                }
            }
            return;
        }
        if (zero) {
            out_ << "\t.tbss\t" << storage << ',' << global.size_bytes;
            if (global.align_bytes > 1) {
                out_ << ',' << p2align(global.align_bytes);
            }
            out_ << '\n';
        } else {
            out_ << "\t.section\t__DATA,__thread_data,thread_local_regular\n";
            if (global.align_bytes > 1) {
                out_ << "\t.p2align\t" << p2align(global.align_bytes) << '\n';
            }
            out_ << storage << ":\n";
            for (uint8_t byte : global.init.bytes) {
                out_ << "\t.byte\t" << static_cast<uint32_t>(byte) << '\n';
            }
            if (global.init.bytes.size() < global.size_bytes) {
                out_ << "\t.zero\t"
                     << global.size_bytes - global.init.bytes.size() << '\n';
            }
        }
        out_ << "\t.section\t__DATA,__thread_vars,thread_local_variables\n";
        emit_symbol_visibility(symbol, global.linkage, global.attrs);
        out_ << "\t.p2align\t3\n" << symbol << ":\n"
             << "\t.quad\t__tlv_bootstrap\n"
             << "\t.quad\t0\n"
             << "\t.quad\t" << storage << '\n';
        return;
    }

    if (global.linkage == air::Linkage::Common) {

        out_ << "\t.comm\t" << symbol << ',' << global.size_bytes << ','
             << (elf_ ? global.align_bytes : p2align(global.align_bytes))
             << '\n';
        return;
    }

    if (global.init.kind == air::GlobalInitKind::Zero) {
        if (elf_) {
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
            out_ << symbol << ":\n";
            out_ << "\t.zero\t" << global.size_bytes << '\n';
            return;
        }
        if (global.linkage != air::Linkage::Internal) {
            out_ << "\t.globl\t" << symbol << '\n';
        }
        out_ << "\t.zerofill\t__DATA,__bss," << symbol << ','
             << global.size_bytes << ',' << p2align(global.align_bytes) << '\n';
        return;
    }

    if (elf_ && !global.attrs.comdat_key.empty()) {
        bool read_only = global.section == air::SectionKind::Const &&
                         global.init.relocs.empty();
        out_ << "\t.section\t." << (read_only ? "rodata." : "data.")
             << symbol << (read_only ? ",\"aG\",@progbits,"
                                     : ",\"awG\",@progbits,")
             << global.attrs.comdat_key << ",comdat\n";
    } else switch (global.section) {
        case air::SectionKind::Cstring:
            out_ << (elf_
                         ? "\t.section\t.rodata.str1.1,\"aMS\",@progbits,1\n"
                         : "\t.section\t__TEXT,__cstring,cstring_literals\n");
            break;
        case air::SectionKind::Const:
            if (global.init.relocs.empty()) {
                out_ << (elf_ ? "\t.section\t.rodata\n"
                              : "\t.section\t__TEXT,__const\n");
            } else {

                out_ << (elf_ ? "\t.section\t.data.rel.ro,\"aw\"\n"
                              : "\t.section\t__DATA,__const\n");
            }
            break;
        case air::SectionKind::Custom:
            out_ << "\t.section\t" << global.custom_section << '\n';
            break;
        case air::SectionKind::Text:
            out_ << (elf_ ? "\t.section\t.rodata\n"
                          : "\t.section\t__TEXT,__const\n");
            break;
        case air::SectionKind::Data:
        case air::SectionKind::Zerofill:
            out_ << (elf_ ? "\t.data\n" : "\t.section\t__DATA,__data\n");
            break;
    }
    emit_symbol_visibility(symbol, global.linkage, global.attrs);
    if (global.align_bytes > 1) {
        out_ << "\t.p2align\t" << p2align(global.align_bytes) << '\n';
    }
    if (elf_) {
        out_ << "\t.type\t" << symbol << ",@object\n";
        out_ << "\t.size\t" << symbol << ", " << global.size_bytes << '\n';
    }
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
                target = object_symbol(callee.name(), callee.attrs().no_prefix);
            } else {
                const air::GlobalData& target_global =
                    module.global(air::GlobalId{reloc.target_index});
                target = object_symbol(target_global.name,
                                       target_global.attrs.no_prefix);
            }
            out_ << "\t.quad\t" << target;
            if (reloc.addend > 0) {
                out_ << '+' << reloc.addend;
            } else if (reloc.addend < 0) {
                out_ << reloc.addend;
            }
            out_ << '\n';
            offset += 8;
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
    out_ << (elf_ ? "\t.section\t.init_array,\"aw\",@init_array\n"
                  : "\t.section\t__DATA,__mod_init_func,mod_init_funcs\n");
    out_ << "\t.p2align\t3\n";
    for (const air::CtorEntry& ctor : module.ctors()) {
        const air::Function& function = module.function(ctor.func);
        out_ << "\t.quad\t"
             << object_symbol(function.name(), function.attrs().no_prefix)
             << '\n';
    }
}

void AsmTextEmitter::end_module(const air::Module& module) {
    (void)module;
    if (!elf_) {
        out_ << ".subsections_via_symbols\n";
        return;
    }

    for (const std::string& symbol : dw_refs_) {
        out_ << "\t.hidden\tDW.ref." << symbol << '\n';
        out_ << "\t.weak\tDW.ref." << symbol << '\n';
        out_ << "\t.section\t.data.rel.local.DW.ref." << symbol
             << ",\"awG\",@progbits,DW.ref." << symbol << ",comdat\n";
        out_ << "\t.p2align\t3\n";
        out_ << "\t.type\tDW.ref." << symbol << ",@object\n";
        out_ << "\t.size\tDW.ref." << symbol << ", 8\n";
        out_ << "DW.ref." << symbol << ":\n";
        out_ << "\t.quad\t" << symbol << '\n';
    }
}

} // namespace aburi::backend::x86
