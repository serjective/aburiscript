#include "print.h"

#include <cassert>
#include <cinttypes>
#include <cstdio>
#include <unordered_map>
#include <vector>

namespace aburi::air {

namespace {

std::string_view linkage_keyword(Linkage linkage) {
    switch (linkage) {
        case Linkage::External: return {};
        case Linkage::Internal: return "internal";
        case Linkage::LinkOnceODR: return "linkonce_odr";
        case Linkage::Weak: return "weak";
        case Linkage::Common: return "common";
    }
    return {};
}

std::string_view section_keyword(SectionKind section) {
    switch (section) {
        case SectionKind::Data: return {};
        case SectionKind::Const: return "const";
        case SectionKind::Cstring: return "cstring";
        case SectionKind::Zerofill: return "zerofill";
        case SectionKind::Text: return "text";
        case SectionKind::Custom: return {};
    }
    return {};
}

class Printer {
public:
    Printer(const Module& mod, PrintOptions options) : mod_(mod), options_(options) {}

    std::string module_text() {
        out_ += "target \"";
        out_ += mod_.triple();
        out_ += "\"\n";

        print_globals();
        print_ctors();
        print_module_asm();
        print_declarations();
        print_definitions();
        return std::move(out_);
    }

    std::string function_text(const Function& func) {
        print_function(func);
        return std::move(out_);
    }

private:
    std::string type_ref(TypeId id) const { return mod_.types().spelling(id); }

    std::string sig_ref(SigId id) const {
        const SigData& sig = mod_.types().signature(id);
        std::string text = "(";
        bool first = true;
        for (SigParam param : sig.params) {
            if (!first) {
                text += ", ";
            }
            first = false;
            switch (param.role) {
                case ParamRole::Normal: break;
                case ParamRole::Sret: text += "sret "; break;
                case ParamRole::IndirectByval: text += "byval "; break;
                case ParamRole::StackByval:
                    text += "stackbyval ";
                    text += std::to_string(param.byval_size);
                    text += ' ';
                    text += std::to_string(param.byval_align);
                    text += ' ';
                    break;
            }
            if (param.coerce_group > 1) {
                text += "group ";
                text += std::to_string(param.coerce_group);
                text += ' ';
            }
            text += type_ref(param.type);
        }
        if (sig.is_variadic) {
            if (!first) {
                text += ", ";
            }
            text += "... fixed ";
            text += std::to_string(sig.fixed_param_count);
        }
        text += ") -> ";
        switch (sig.ret_class) {
            case RetClass::Void:
                text += "void";
                break;
            case RetClass::Scalar:
                text += type_ref(sig.ret_type);
                break;
            case RetClass::IntPair:
                text += "pair ";
                text += type_ref(sig.ret_type);
                if (sig.ret_sse_mask != 0) {
                    text += " mask ";
                    text += std::to_string(sig.ret_sse_mask);
                }
                break;
            case RetClass::Hfa:
                text += "hfa ";
                text += type_ref(sig.ret_type);
                text += " x ";
                text += std::to_string(sig.ret_count);
                break;
            case RetClass::IndirectSret:
                text += "sret";
                break;
        }
        return text;
    }

    static void append_escaped_bytes(std::string& out, const std::vector<uint8_t>& bytes) {
        out += '"';
        for (uint8_t byte : bytes) {
            if (byte == '"' || byte == '\\') {
                out += '\\';
                out += static_cast<char>(byte);
            } else if (byte >= 0x20 && byte < 0x7F) {
                out += static_cast<char>(byte);
            } else {
                char buf[4];
                std::snprintf(buf, sizeof(buf), "\\%02X", byte);
                out += buf;
            }
        }
        out += '"';
    }

    static void append_escaped_string(std::string& out, std::string_view text) {
        std::vector<uint8_t> bytes(text.begin(), text.end());
        append_escaped_bytes(out, bytes);
    }

    void append_symbol_prefix(Linkage linkage, const SymbolAttrs& attrs) {
        std::string_view keyword = linkage_keyword(linkage);
        if (!keyword.empty()) {
            out_ += keyword;
            out_ += " ";
        }
        if (attrs.visibility == SymbolVisibility::Protected) {
            out_ += "protected ";
        } else if (attrs.hidden ||
                   attrs.visibility == SymbolVisibility::Hidden) {
            out_ += "hidden ";
        }
        if (attrs.no_prefix) {
            out_ += "no_prefix ";
        }
        if (!attrs.comdat_key.empty()) {
            out_ += "comdat ";
            append_escaped_string(out_, attrs.comdat_key);
            out_ += " ";
        }
    }

    void print_globals() {
        if (mod_.global_count() != 0) {
            out_ += "\n";
        }
        for (uint32_t i = 1; i <= mod_.global_count(); ++i) {
            const GlobalData& data = mod_.global(GlobalId{i});
            out_ += "global ";
            append_symbol_prefix(data.linkage, data.attrs);
            out_ += "@";
            out_ += data.name;
            out_ += " size ";
            out_ += std::to_string(data.size_bytes);
            out_ += " align ";
            out_ += std::to_string(data.align_bytes);
            if (data.section == SectionKind::Custom) {
                out_ += " section ";
                append_escaped_string(out_, data.custom_section);
            } else {
                std::string_view keyword = section_keyword(data.section);
                if (!keyword.empty()) {
                    out_ += " section ";
                    out_ += keyword;
                }
            }
            if (data.is_thread_local) {
                out_ += " thread_local";
            }
            switch (data.init.kind) {
                case GlobalInitKind::None:
                    out_ += " = external";
                    break;
                case GlobalInitKind::Zero:
                    out_ += " = zeroinit";
                    break;
                case GlobalInitKind::Bytes:
                    out_ += " = bytes ";
                    append_escaped_bytes(out_, data.init.bytes);
                    if (!data.init.relocs.empty()) {
                        out_ += " relocs [ ";
                        bool first = true;
                        for (const InitReloc& reloc : data.init.relocs) {
                            if (!first) {
                                out_ += ", ";
                            }
                            first = false;
                            out_ += std::to_string(reloc.offset);
                            out_ += ": @";
                            out_ += reloc.is_function
                                        ? mod_.function(FuncId{reloc.target_index}).name()
                                        : mod_.global(GlobalId{reloc.target_index}).name;
                            if (reloc.addend > 0) {
                                out_ += "+" + std::to_string(reloc.addend);
                            } else if (reloc.addend < 0) {
                                out_ += std::to_string(reloc.addend);
                            }
                        }
                        out_ += " ]";
                    }
                    break;
            }
            out_ += "\n";
        }
    }

    void print_ctors() {
        bool any = false;
        for (const CtorEntry& ctor : mod_.ctors()) {
            if (!any) {
                out_ += "\n";
                any = true;
            }
            out_ += "ctor ";
            out_ += std::to_string(ctor.priority);
            out_ += " @";
            out_ += mod_.function(ctor.func).name();
            out_ += "\n";
        }
    }

    void print_module_asm() {
        bool any = false;
        for (const std::string& text : mod_.module_asm()) {
            if (!any) {
                out_ += "\n";
                any = true;
            }
            out_ += "module_asm ";
            append_escaped_string(out_, text);
            out_ += "\n";
        }
    }

    void print_declarations() {
        bool any = false;
        for (uint32_t i = 1; i <= mod_.function_count(); ++i) {
            const Function& func = mod_.function(FuncId{i});
            if (!func.is_declaration()) {
                continue;
            }
            if (!any) {
                out_ += "\n";
                any = true;
            }
            out_ += "declare ";
            append_symbol_prefix(func.linkage(), func.attrs());
            out_ += "@";
            out_ += func.name();
            out_ += sig_ref(func.sig());
            out_ += "\n";
        }
    }

    void print_definitions() {
        for (uint32_t i = 1; i <= mod_.function_count(); ++i) {
            const Function& func = mod_.function(FuncId{i});
            if (func.is_declaration()) {
                continue;
            }
            out_ += "\n";
            print_function(func);
        }
    }

    void number_function_entities(const Function& func) {
        value_names_.clear();
        block_numbers_.clear();
        uint32_t next_value = 0;
        uint32_t next_block = 0;
        for (BlockId b = func.first_block(); b.is_valid(); b = func.block(b).next) {
            block_numbers_[b.index] = next_block++;
            for (ValueId param : func.block_params(b)) {
                name_value(func, param, next_value);
            }
            for (InstId i = func.block(b).first; i.is_valid();
                 i = func.inst(i).next) {
                ValueId result = func.inst(i).result;
                if (result.is_valid()) {
                    name_value(func, result, next_value);
                }
            }
        }
    }

    void name_value(const Function& func, ValueId id, uint32_t& next_value) {
        std::string_view name = func.value_name(id);
        if (!name.empty()) {
            value_names_[id.index] = std::string(name);
        } else {
            value_names_[id.index] = "v" + std::to_string(next_value++);
        }
    }

    std::string block_ref(BlockId id) const {
        return "b" + std::to_string(block_numbers_.at(id.index));
    }

    std::string value_ref(const Function& func, ValueId id) const {
        const ValueData& data = func.value(id);
        switch (data.kind) {
            case ValueKind::InstResult:
            case ValueKind::BlockParam:
                return "%" + value_names_.at(id.index);
            case ValueKind::ConstInt: {
                std::string text;
                if (data.payload2 != 0) {
                    char buf[40];
                    std::snprintf(buf, sizeof(buf), "0x%016" PRIX64 "%016" PRIX64,
                                  data.payload2, data.payload);
                    text = buf;
                } else {
                    text = std::to_string(data.payload);
                }
                return text + ":" + type_ref(data.type);
            }
            case ValueKind::ConstFloat: {
                char buf[40];
                const TypeData& type = mod_.types().type(data.type);
                if (type.float_kind == FloatKind::F32) {
                    std::snprintf(buf, sizeof(buf), "0x%08" PRIX64, data.payload);
                } else if (data.payload2 != 0 || type.float_kind == FloatKind::F128) {
                    std::snprintf(buf, sizeof(buf), "0x%016" PRIX64 "%016" PRIX64,
                                  data.payload2, data.payload);
                } else {
                    std::snprintf(buf, sizeof(buf), "0x%016" PRIX64, data.payload);
                }
                return std::string(buf) + ":" + type_ref(data.type);
            }
            case ValueKind::ConstNull:
                return "null:" + type_ref(data.type);
            case ValueKind::Undef:
                return "undef:" + type_ref(data.type);
            case ValueKind::GlobalAddr:
                return "@" + mod_.global(GlobalId{static_cast<uint32_t>(data.payload)}).name;
            case ValueKind::FuncAddr:
                return "@" + mod_.function(FuncId{static_cast<uint32_t>(data.payload)}).name();
            case ValueKind::LabelAddr:
                return "label " + block_ref(BlockId{static_cast<uint32_t>(data.payload)});
        }
        return "?";
    }

    std::string block_call_ref(const Function& func, BlockCallId id) const {
        const BlockCall& call = func.block_call(id);
        std::string text = block_ref(call.target) + "(";
        bool first = true;
        for (ValueId arg : func.block_call_args(id)) {
            if (!first) {
                text += ", ";
            }
            first = false;
            text += value_ref(func, arg);
        }
        text += ")";
        return text;
    }

    void print_function(const Function& func) {
        number_function_entities(func);
        out_ += "func ";
        append_symbol_prefix(func.linkage(), func.attrs());
        out_ += "@";
        out_ += func.name();
        out_ += sig_ref(func.sig());
        out_ += " {\n";
        for (BlockId b = func.first_block(); b.is_valid(); b = func.block(b).next) {
            out_ += block_ref(b);
            out_ += "(";
            bool first = true;
            for (ValueId param : func.block_params(b)) {
                if (!first) {
                    out_ += ", ";
                }
                first = false;
                out_ += "%" + value_names_.at(param.index);
                out_ += ": ";
                out_ += type_ref(func.value_type(param));
            }
            out_ += "):\n";
            for (InstId i = func.block(b).first; i.is_valid(); i = func.inst(i).next) {
                print_inst(func, i);
            }
        }
        out_ += "}\n";
    }

    void append_order(std::string_view label, MemOrder order) {
        out_ += ", ";
        out_ += label;
        out_ += " ";
        out_ += mem_order_mnemonic(order);
    }

    void print_inst(const Function& func, InstId id) {
        const InstData& data = func.inst(id);
        out_ += "    ";
        if (data.result.is_valid()) {
            out_ += "%" + value_names_.at(data.result.index);
            out_ += " = ";
        }
        out_ += opcode_mnemonic(data.op);
        auto ops = func.operands(id);

        switch (data.op) {
            case Opcode::StackAlloc:
                out_ += " " + std::to_string(stack_alloc_size(data.aux));
                out_ += ", align " +
                        std::to_string(1u << stack_alloc_align_log2(data.aux));
                break;
            case Opcode::StackAllocDyn:
                out_ += " " + value_ref(func, ops[0]);
                out_ += ", align " + std::to_string(1ull << data.aux);
                break;
            case Opcode::Load:
                out_ += "." + type_ref(data.type);
                if (data.flags & INST_FLAG_VOLATILE) {
                    out_ += " volatile";
                }
                out_ += " " + value_ref(func, ops[0]);
                out_ += ", align " + std::to_string(1ull << data.aux);
                break;
            case Opcode::Store:
                if (data.flags & INST_FLAG_VOLATILE) {
                    out_ += " volatile";
                }
                out_ += " " + value_ref(func, ops[0]);
                out_ += ", " + value_ref(func, ops[1]);
                out_ += ", align " + std::to_string(1ull << data.aux);
                break;
            case Opcode::AtomicLoad:
                out_ += "." + type_ref(data.type);
                if (data.flags & INST_FLAG_VOLATILE) {
                    out_ += " volatile";
                }
                out_ += " " + value_ref(func, ops[0]);
                out_ += ", align " +
                        std::to_string(1ull << atomic_access_align_log2(data.aux));
                append_order("order", atomic_access_order(data.aux));
                break;
            case Opcode::AtomicStore:
                if (data.flags & INST_FLAG_VOLATILE) {
                    out_ += " volatile";
                }
                out_ += " " + value_ref(func, ops[0]);
                out_ += ", " + value_ref(func, ops[1]);
                out_ += ", align " +
                        std::to_string(1ull << atomic_access_align_log2(data.aux));
                append_order("order", atomic_access_order(data.aux));
                break;
            case Opcode::AtomicRmw:
                out_ += ".";
                out_ += rmw_op_mnemonic(rmw_op(data.aux));
                out_ += "." + type_ref(data.type);
                out_ += " " + value_ref(func, ops[0]);
                out_ += ", " + value_ref(func, ops[1]);
                append_order("order", rmw_order(data.aux));
                break;
            case Opcode::AtomicCas:
                out_ += "." + type_ref(data.type);
                out_ += " " + value_ref(func, ops[0]);
                out_ += ", " + value_ref(func, ops[1]);
                out_ += ", " + value_ref(func, ops[2]);
                append_order("order", cas_success_order(data.aux));
                append_order("failure", cas_failure_order(data.aux));
                break;
            case Opcode::Fence:
                out_ += " order ";
                out_ += mem_order_mnemonic(static_cast<MemOrder>(data.aux));
                break;
            case Opcode::Icmp:
                out_ += ".";
                out_ += int_cond_mnemonic(static_cast<IntCond>(data.aux));
                print_operand_list(func, ops);
                break;
            case Opcode::Fcmp:
                out_ += ".";
                out_ += float_cond_mnemonic(static_cast<FloatCond>(data.aux));
                print_operand_list(func, ops);
                break;
            case Opcode::InlineAsm: {
                print_asm_payload(
                    mod_.asm_payload(static_cast<uint32_t>(data.aux)));
                print_call_args(func, ops);
                break;
            }
            case Opcode::AsmGoto: {
                print_asm_payload(
                    mod_.asm_payload(static_cast<uint32_t>(data.aux)));
                print_call_args(func, ops);
                std::span<const BlockCallId> calls =
                    func.block_call_list(static_cast<uint32_t>(data.aux2));
                out_ += " to ";
                out_ += calls.empty()
                    ? "^<invalid>"
                    : block_ref(func.block_call(calls[0]).target);
                out_ += " [";
                for (size_t k = 1; k < calls.size(); ++k) {
                    out_ += k == 1 ? " " : ", ";
                    out_ += block_ref(func.block_call(calls[k]).target);
                }
                out_ += calls.size() > 1 ? " ]" : "]";
                break;
            }
            case Opcode::EhAllocException:
                out_ += " " + std::to_string(data.aux);
                break;
            case Opcode::EhLandingPad: {
                const EhLandingPadPayload& payload =
                    mod_.eh_landing_pad_payload(static_cast<uint32_t>(data.aux));
                out_ += " cleanup ";
                out_ += payload.is_cleanup ? "1" : "0";
                out_ += ", catch_all ";
                out_ += payload.has_catch_all ? "1" : "0";
                out_ += ", clauses [";
                bool first = true;
                for (GlobalId clause : payload.clause_typeinfos) {
                    out_ += first ? " " : ", ";
                    first = false;
                    out_ += "@";
                    out_ += mod_.global(clause).name;
                }
                out_ += first ? "]" : " ]";
                break;
            }
            case Opcode::Jump:
                out_ += " " + block_call_ref(func, BlockCallId{aux_low(data.aux)});
                break;
            case Opcode::BrIf:
                out_ += " " + value_ref(func, ops[0]);
                out_ += ", " + block_call_ref(func, BlockCallId{aux_low(data.aux)});
                out_ += ", " + block_call_ref(func, BlockCallId{aux_high(data.aux)});
                break;
            case Opcode::Switch: {
                out_ += " " + value_ref(func, ops[0]);
                out_ += ", " + block_call_ref(func, BlockCallId{aux_low(data.aux)});
                out_ += " [";
                bool first = true;
                for (const SwitchCase& c : func.jump_table(aux_high(data.aux))) {
                    out_ += first ? " " : ", ";
                    first = false;
                    out_ += std::to_string(c.value);
                    out_ += ": " + block_call_ref(func, c.target);
                }
                out_ += first ? "]" : " ]";
                break;
            }
            case Opcode::BrIndirect: {
                out_ += " " + value_ref(func, ops[0]);
                out_ += " [";
                bool first = true;
                for (BlockCallId call : func.block_call_list(aux_low(data.aux))) {
                    out_ += first ? " " : ", ";
                    first = false;
                    out_ += block_ref(func.block_call(call).target);
                }
                out_ += first ? "]" : " ]";
                break;
            }
            case Opcode::Call: {
                out_ += " @";
                out_ += mod_.function(FuncId{static_cast<uint32_t>(data.aux)}).name();
                print_call_args(func, ops);
                break;
            }
            case Opcode::CallIndirect:
            case Opcode::TailCallIndirect: {
                out_ += " " + value_ref(func, ops[0]);
                print_call_args(func, ops.subspan(1));
                out_ += " : " + sig_ref(SigId{static_cast<uint32_t>(data.aux)});
                break;
            }
            case Opcode::Invoke: {
                out_ += " @";
                out_ += mod_.function(FuncId{static_cast<uint32_t>(data.aux)}).name();
                print_call_args(func, ops);
                out_ += ", normal ";
                out_ += block_call_ref(func, BlockCallId{aux_low(data.aux2)});
                out_ += ", unwind ";
                out_ += block_call_ref(func, BlockCallId{aux_high(data.aux2)});
                break;
            }
            case Opcode::InvokeIndirect: {
                out_ += " " + value_ref(func, ops[0]);
                print_call_args(func, ops.subspan(1));
                out_ += " : " + sig_ref(SigId{static_cast<uint32_t>(data.aux)});
                out_ += ", normal ";
                out_ += block_call_ref(func, BlockCallId{aux_low(data.aux2)});
                out_ += ", unwind ";
                out_ += block_call_ref(func, BlockCallId{aux_high(data.aux2)});
                break;
            }
            default:

                if (data.result.is_valid() && !has_fixed_result_type(data.op)) {
                    out_ += "." + type_ref(data.type);
                }
                print_operand_list(func, ops);
                break;
        }

        if (options_.locs && data.loc.offset != 0) {
            out_ += " loc(" + std::to_string(data.loc.offset) + ")";
        }
        out_ += "\n";
    }

    static bool has_fixed_result_type(Opcode op) {
        switch (op) {
            case Opcode::StackAlloc:
            case Opcode::StackAllocDyn:
            case Opcode::StackSave:
            case Opcode::FrameAddr:
            case Opcode::ReturnAddr:
            case Opcode::EhAllocException:
            case Opcode::EhLandingPad:
            case Opcode::CatchBegin:
                return true;
            default:
                return false;
        }
    }

    void print_operand_list(const Function& func, std::span<const ValueId> ops) {
        bool first = true;
        for (ValueId op : ops) {
            out_ += first ? " " : ", ";
            first = false;
            out_ += value_ref(func, op);
        }
    }

    void print_call_args(const Function& func, std::span<const ValueId> args) {
        out_ += "(";
        bool first = true;
        for (ValueId arg : args) {
            if (!first) {
                out_ += ", ";
            }
            first = false;
            out_ += value_ref(func, arg);
        }
        out_ += ")";
    }
    void print_asm_payload(const AsmPayload& payload) {
        out_ += " ";
        append_escaped_string(out_, payload.text);
        out_ += " constraints ";
        print_string_list(payload.constraints);
        out_ += " operand_types [";
        for (size_t k = 0; k < payload.operand_types.size(); ++k) {
            out_ += k == 0 ? " " : ", ";
            out_ += type_ref(payload.operand_types[k]);
        }
        out_ += " ] clobbers ";
        print_string_list(payload.clobbers);
        if (!payload.register_bindings.empty()) {
            out_ += " bindings ";
            print_string_list(payload.register_bindings);
        }
    }

    void print_string_list(const std::vector<std::string>& items) {
        out_ += "[";
        bool first = true;
        for (const std::string& item : items) {
            out_ += first ? " " : ", ";
            first = false;
            append_escaped_string(out_, item);
        }
        out_ += first ? "]" : " ]";
    }

    const Module& mod_;
    PrintOptions options_;
    std::string out_;
    std::unordered_map<uint32_t, std::string> value_names_;
    std::unordered_map<uint32_t, uint32_t> block_numbers_;
};

} // namespace

std::string print_module(const Module& mod, PrintOptions options) {
    return Printer(mod, options).module_text();
}

std::string print_function(const Module& mod, const Function& func,
                           PrintOptions options) {
    return Printer(mod, options).function_text(func);
}

void dump(const Module& mod) {
    std::string text = print_module(mod);
    std::fwrite(text.data(), 1, text.size(), stderr);
}

void dump(const Module& mod, const Function& func) {
    std::string text = print_function(mod, func);
    std::fwrite(text.data(), 1, text.size(), stderr);
}

} // namespace aburi::air
