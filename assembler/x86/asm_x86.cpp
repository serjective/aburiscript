#include "asm_x86.h"

#include <string>
#include <vector>

#include "../../backend/x86/isa.h"

namespace aburi::assembler::x86 {

namespace {

using backend::SymFlavor;
using backend::x86::AsmOperand;
using backend::x86::IsaEncoded;
using backend::x86::IsaFixup;

struct RegSpelling {
    std::string_view name;
    uint8_t number;
    char reg_class;
    bool high_byte;
};

constexpr RegSpelling kRegisters[] = {
    {"rax", 0, 'q', false},  {"rcx", 1, 'q', false},
    {"rdx", 2, 'q', false},  {"rbx", 3, 'q', false},
    {"rsp", 4, 'q', false},  {"rbp", 5, 'q', false},
    {"rsi", 6, 'q', false},  {"rdi", 7, 'q', false},
    {"r8", 8, 'q', false},   {"r9", 9, 'q', false},
    {"r10", 10, 'q', false}, {"r11", 11, 'q', false},
    {"r12", 12, 'q', false}, {"r13", 13, 'q', false},
    {"r14", 14, 'q', false}, {"r15", 15, 'q', false},

    {"eax", 0, 'l', false},  {"ecx", 1, 'l', false},
    {"edx", 2, 'l', false},  {"ebx", 3, 'l', false},
    {"esp", 4, 'l', false},  {"ebp", 5, 'l', false},
    {"esi", 6, 'l', false},  {"edi", 7, 'l', false},
    {"r8d", 8, 'l', false},  {"r9d", 9, 'l', false},
    {"r10d", 10, 'l', false},{"r11d", 11, 'l', false},
    {"r12d", 12, 'l', false},{"r13d", 13, 'l', false},
    {"r14d", 14, 'l', false},{"r15d", 15, 'l', false},

    {"ax", 0, 'w', false},   {"cx", 1, 'w', false},
    {"dx", 2, 'w', false},   {"bx", 3, 'w', false},
    {"sp", 4, 'w', false},   {"bp", 5, 'w', false},
    {"si", 6, 'w', false},   {"di", 7, 'w', false},
    {"r8w", 8, 'w', false},  {"r9w", 9, 'w', false},
    {"r10w", 10, 'w', false},{"r11w", 11, 'w', false},
    {"r12w", 12, 'w', false},{"r13w", 13, 'w', false},
    {"r14w", 14, 'w', false},{"r15w", 15, 'w', false},

    {"al", 0, 'b', false},   {"cl", 1, 'b', false},
    {"dl", 2, 'b', false},   {"bl", 3, 'b', false},
    {"spl", 4, 'b', false},  {"bpl", 5, 'b', false},
    {"sil", 6, 'b', false},  {"dil", 7, 'b', false},
    {"ah", 4, 'b', true},    {"ch", 5, 'b', true},
    {"dh", 6, 'b', true},    {"bh", 7, 'b', true},
    {"r8b", 8, 'b', false},  {"r9b", 9, 'b', false},
    {"r10b", 10, 'b', false},{"r11b", 11, 'b', false},
    {"r12b", 12, 'b', false},{"r13b", 13, 'b', false},
    {"r14b", 14, 'b', false},{"r15b", 15, 'b', false},

    {"xmm0", 0, 'x', false},  {"xmm1", 1, 'x', false},
    {"xmm2", 2, 'x', false},  {"xmm3", 3, 'x', false},
    {"xmm4", 4, 'x', false},  {"xmm5", 5, 'x', false},
    {"xmm6", 6, 'x', false},  {"xmm7", 7, 'x', false},
    {"xmm8", 8, 'x', false},  {"xmm9", 9, 'x', false},
    {"xmm10", 10, 'x', false},{"xmm11", 11, 'x', false},
    {"xmm12", 12, 'x', false},{"xmm13", 13, 'x', false},
    {"xmm14", 14, 'x', false},{"xmm15", 15, 'x', false},

    {"st", 0, 't', false},
};

std::string lowered(std::string_view text) {
    std::string out(text);
    for (char& c : out) {
        if (c >= 'A' && c <= 'Z') {
            c = static_cast<char>(c - 'A' + 'a');
        }
    }
    return out;
}

bool parse_register(std::string_view text, AsmOperand& operand) {
    for (const RegSpelling& spelling : kRegisters) {
        if (spelling.name != text) {
            continue;
        }
        operand.kind = AsmOperand::Kind::Reg;
        operand.reg = spelling.number;
        operand.reg_class = spelling.reg_class;
        operand.high_byte = spelling.high_byte;
        return true;
    }
    return false;
}

bool prefix_byte_for(std::string_view mnemonic, uint8_t& prefix) {
    if (mnemonic == "lock") {
        prefix = 0xF0;
        return true;
    }
    if (mnemonic == "rep" || mnemonic == "repe" || mnemonic == "repz") {
        prefix = 0xF3;
        return true;
    }
    if (mnemonic == "repne" || mnemonic == "repnz") {
        prefix = 0xF2;
        return true;
    }
    return false;
}

bool is_branch_mnemonic(std::string_view mnemonic) {
    return mnemonic == "jmp" || mnemonic == "jmpq" || mnemonic == "call" ||
           mnemonic == "callq" || mnemonic == "j";
}

class InstParser {
public:
    InstParser(Assembler& assembler, Lexer& lexer)
        : asm_(assembler), lexer_(lexer) {}

    void parse(const Token& mnemonic_token) {
        std::string spelling = lowered(mnemonic_token.text);
        uint8_t lock_prefix = 0;
        Token stem_token = mnemonic_token;
        if (prefix_byte_for(spelling, lock_prefix)) {
            const Token& next = lexer_.peek();
            if (next.kind != TokKind::Ident) {
                asm_.expr_error(next.line, next.col,
                                "expected an instruction after '" + spelling +
                                    "'");
                lexer_.skip_to_statement_end();
                return;
            }
            stem_token = lexer_.take();
            spelling = lowered(stem_token.text);
        }

        std::vector<AsmOperand> operands;
        operands.reserve(3);

        std::string_view mnemonic = spelling;
        if (!backend::x86::x86_known_mnemonic(mnemonic)) {
            std::string_view stem;
            uint8_t cond = 0;
            if (backend::x86::x86_split_condition(mnemonic, stem, cond)) {
                AsmOperand condition;
                condition.kind = AsmOperand::Kind::Reg;
                condition.reg_class = 'c';
                condition.reg = cond;
                operands.push_back(condition);
                mnemonic = stem;
            }
        }
        bool branch = is_branch_mnemonic(mnemonic);

        const Token& first = lexer_.peek();
        if (first.kind != TokKind::Newline && first.kind != TokKind::End) {
            for (;;) {
                AsmOperand operand;
                if (!parse_operand(operand, branch)) {
                    lexer_.skip_to_statement_end();
                    return;
                }
                operands.push_back(operand);
                const Token& next = lexer_.peek();
                if (next.kind == TokKind::Punct && next.punct == ',') {
                    lexer_.take();
                    continue;
                }
                break;
            }
        }

        IsaEncoded encoded = backend::x86::x86_match_and_encode(
            mnemonic, operands, lock_prefix);
        if (!encoded.ok) {
            asm_.expr_error(mnemonic_token.line, mnemonic_token.col,
                            encoded.error);
            lexer_.skip_to_statement_end();
            return;
        }
        emit(encoded, mnemonic_token);

        const Token& tail = lexer_.peek();
        if (tail.kind == TokKind::Newline) {
            lexer_.take();
        } else if (tail.kind != TokKind::End) {
            asm_.expr_error(tail.line, tail.col,
                            "unexpected token after the operands");
            lexer_.skip_to_statement_end();
        }
    }

private:
    bool error(const Token& at, const std::string& message) {
        asm_.expr_error(at.line, at.col, message);
        return false;
    }

    void emit(const IsaEncoded& encoded, const Token& at) {
        if (encoded.is_branch) {
            asm_.append_branch(encoded.bytes, encoded.branch_near_size,
                               encoded.fixup_offset,
                               encoded.branch_short_opcode, encoded.fixup_sym,
                               encoded.fixup_addend, at);
            return;
        }
        if (encoded.fixup == IsaFixup::None) {
            asm_.append_inst_bytes(encoded.bytes, encoded.size, at);
            return;
        }
        FixupKind kind = FixupKind::PcRel32;
        switch (encoded.fixup) {
            case IsaFixup::PcRel32: kind = FixupKind::PcRel32; break;
            case IsaFixup::Abs32: kind = FixupKind::Abs32; break;
            case IsaFixup::Abs64: kind = FixupKind::Abs64; break;
            case IsaFixup::None: break;
        }
        asm_.append_inst_bytes_fixup(
            encoded.bytes, encoded.size, kind, encoded.fixup_offset,
            encoded.fixup_sym, encoded.fixup_addend, encoded.fixup_flavor,
            encoded.pcrel_extra, at);
    }

    bool parse_percent_operand(AsmOperand& operand) {
        lexer_.take();
        const Token& name = lexer_.peek();
        if (name.kind != TokKind::Ident) {
            return error(name, "expected a register name after '%'");
        }
        std::string text = lowered(name.text);
        const Token& colon = lexer_.peek_second();
        if ((text == "fs" || text == "gs") &&
            colon.kind == TokKind::Punct && colon.punct == ':') {
            uint8_t segment = text == "fs" ? 0x64 : 0x65;
            lexer_.take();
            lexer_.take();
            const Token& next = lexer_.peek();
            bool parsed = next.kind == TokKind::Punct && next.punct == '('
                              ? parse_memory_operand(operand)
                              : parse_expression_operand(operand, false);
            if (!parsed) {
                return false;
            }
            operand.segment = segment;
            return true;
        }
        Token register_token = lexer_.take();
        if (!parse_register(text, operand)) {
            return error(register_token,
                         "unknown register '%" + text + "'");
        }
        if (operand.reg_class == 't') {
            const Token& open = lexer_.peek();
            if (open.kind == TokKind::Punct && open.punct == '(') {
                lexer_.take();
                const Token& index = lexer_.peek();
                if (index.kind != TokKind::Integer || index.value < 0 ||
                    index.value > 7) {
                    return error(index, "expected an x87 stack index 0-7");
                }
                operand.reg = static_cast<uint8_t>(index.value);
                lexer_.take();
                const Token& close = lexer_.peek();
                if (close.kind != TokKind::Punct || close.punct != ')') {
                    return error(close, "expected ')'");
                }
                lexer_.take();
            }
        }
        return true;
    }

    bool parse_memory_operand(AsmOperand& operand) {
        operand.kind = AsmOperand::Kind::Mem;
        const Token& open = lexer_.peek();
        if (open.kind != TokKind::Punct || open.punct != '(') {
            return true;
        }
        lexer_.take();
        const Token& first = lexer_.peek();
        if (first.kind == TokKind::Punct && first.punct == '%') {
            lexer_.take();
            const Token& name = lexer_.peek();
            if (name.kind != TokKind::Ident) {
                return error(name, "expected a base register");
            }
            Token base_token = lexer_.take();
            std::string text = lowered(base_token.text);
            if (text == "rip") {
                operand.rip = true;
            } else {
                AsmOperand base;
                if (!parse_register(text, base) || base.reg_class != 'q') {
                    return error(base_token,
                                 "memory base '%" + text +
                                     "' must be a 64-bit register");
                }
                operand.has_base = true;
                operand.base = base.reg;
            }
        }
        if (lexer_.peek().kind == TokKind::Punct &&
            lexer_.peek().punct == ',') {
            lexer_.take();
            if (operand.rip) {
                return error(lexer_.peek(),
                             "rip-relative addressing takes no index");
            }
            const Token& percent = lexer_.peek();
            if (percent.kind != TokKind::Punct || percent.punct != '%') {
                return error(percent, "expected an index register");
            }
            lexer_.take();
            const Token& name = lexer_.peek();
            if (name.kind != TokKind::Ident) {
                return error(name, "expected an index register");
            }
            Token index_token = lexer_.take();
            AsmOperand index;
            if (!parse_register(lowered(index_token.text), index) ||
                index.reg_class != 'q') {
                return error(index_token,
                             "memory index must be a 64-bit register");
            }
            operand.has_index = true;
            operand.index = index.reg;
            if (lexer_.peek().kind == TokKind::Punct &&
                lexer_.peek().punct == ',') {
                lexer_.take();
                const Token& scale = lexer_.peek();
                if (scale.kind != TokKind::Integer) {
                    return error(scale, "expected an index scale");
                }
                operand.scale = static_cast<uint8_t>(scale.value);
                lexer_.take();
            }
        }
        const Token& close = lexer_.peek();
        if (close.kind != TokKind::Punct || close.punct != ')') {
            return error(close, "expected ')'");
        }
        lexer_.take();
        return true;
    }

    bool parse_relocation_suffix(SymFlavor& flavor, bool& plt) {
        const Token& at = lexer_.peek();
        if (at.kind != TokKind::Punct || at.punct != '@') {
            return true;
        }
        lexer_.take();
        const Token& name = lexer_.peek();
        if (name.kind != TokKind::Ident) {
            return error(name, "expected a relocation suffix");
        }
        Token suffix = lexer_.take();
        std::string text = lowered(suffix.text);
        if (text == "gotpcrel") {
            flavor = SymFlavor::GotPcRel;
        } else if (text == "tlvp") {
            flavor = SymFlavor::TlvPcRel;
        } else if (text == "plt") {
            plt = true;
        } else {
            return error(suffix, "unknown relocation suffix '@" +
                                     std::string(suffix.text) + "'");
        }
        return true;
    }

    bool parse_immediate(AsmOperand& operand) {
        const Token& at = lexer_.peek();
        ExprValue value = parse_expression(lexer_, asm_);
        if (!value.ok) {
            return false;
        }
        SymFlavor flavor = SymFlavor::Plain;
        bool plt = false;
        if (!parse_relocation_suffix(flavor, plt)) {
            return false;
        }
        if (value.neg_sym != no_sym) {
            return error(at, "immediates cannot subtract a symbol");
        }
        if (value.pos_sym != no_sym) {
            operand.kind = AsmOperand::Kind::Sym;
            operand.sym = value.pos_sym;
            operand.addend = value.constant;
            operand.flavor = flavor;
            return true;
        }
        operand.kind = AsmOperand::Kind::Imm;
        operand.imm = value.constant;
        return true;
    }

    bool parse_expression_operand(AsmOperand& operand, bool branch) {
        const Token& at = lexer_.peek();
        ExprValue value = parse_expression(lexer_, asm_);
        if (!value.ok) {
            return false;
        }
        SymFlavor flavor = SymFlavor::Plain;
        bool plt = false;
        if (!parse_relocation_suffix(flavor, plt)) {
            return false;
        }
        if (value.neg_sym != no_sym) {
            return error(at, "instruction operands cannot subtract a symbol");
        }
        const Token& next = lexer_.peek();
        bool has_memory_tail =
            next.kind == TokKind::Punct && next.punct == '(';
        if (branch && !has_memory_tail) {
            if (value.pos_sym == no_sym) {
                return error(at, "branch target must be a label or symbol");
            }
            operand.kind = AsmOperand::Kind::Sym;
            operand.sym = value.pos_sym;
            operand.addend = value.constant;
            return true;
        }
        if (value.pos_sym != no_sym) {
            operand.sym = value.pos_sym;
            operand.addend = value.constant;
            operand.flavor = flavor;
        } else {
            operand.disp = value.constant;
        }
        return parse_memory_operand(operand);
    }

    bool parse_operand(AsmOperand& operand, bool branch) {
        const Token& token = lexer_.peek();
        if (token.kind == TokKind::Punct && token.punct == '*') {
            lexer_.take();
            if (!parse_operand(operand, false)) {
                return false;
            }
            operand.indirect = true;
            return true;
        }
        if (token.kind == TokKind::Punct && token.punct == '$') {
            lexer_.take();
            return parse_immediate(operand);
        }
        if (token.kind == TokKind::Punct && token.punct == '%') {
            return parse_percent_operand(operand);
        }
        if (token.kind == TokKind::Punct && token.punct == '(') {
            return parse_memory_operand(operand);
        }
        return parse_expression_operand(operand, branch);
    }

    Assembler& asm_;
    Lexer& lexer_;
};

}

void parse_instruction(Assembler& assembler, Lexer& lexer,
                       const Token& mnemonic) {
    InstParser parser(assembler, lexer);
    parser.parse(mnemonic);
}

}
