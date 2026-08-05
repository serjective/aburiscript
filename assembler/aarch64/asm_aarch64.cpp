#include "asm_aarch64.h"

#include <vector>

#include "../../backend/aarch64/isa.h"

namespace aburi::assembler::aarch64 {

namespace {

using backend::SymFlavor;
using backend::aarch64::AsmOperand;
using backend::aarch64::IsaEncoded;

struct CondSpelling {
    std::string_view name;
    uint8_t bits;
};
constexpr CondSpelling cond_spellings[] = {
    {"eq", 0x0}, {"ne", 0x1}, {"cs", 0x2}, {"hs", 0x2}, {"cc", 0x3},
    {"lo", 0x3}, {"mi", 0x4}, {"pl", 0x5}, {"vs", 0x6}, {"vc", 0x7},
    {"hi", 0x8}, {"ls", 0x9}, {"ge", 0xA}, {"lt", 0xB}, {"gt", 0xC},
    {"le", 0xD}, {"al", 0xE},
};

bool parse_cond_name(std::string_view text, uint8_t& bits) {
    for (const CondSpelling& spelling : cond_spellings) {
        if (spelling.name == text) {
            bits = spelling.bits;
            return true;
        }
    }
    return false;
}

bool parse_reg_number(std::string_view digits, unsigned max, uint8_t& out) {
    if (digits.empty() || digits.size() > 2) {
        return false;
    }
    unsigned value = 0;
    for (char c : digits) {
        if (c < '0' || c > '9') {
            return false;
        }
        value = value * 10 + static_cast<unsigned>(c - '0');
    }
    if (digits.size() == 2 && digits[0] == '0') {
        return false;
    }
    if (value > max) {
        return false;
    }
    out = static_cast<uint8_t>(value);
    return true;
}

bool parse_register(std::string_view text, AsmOperand& operand) {
    if (text == "sp" || text == "wsp") {
        operand.kind = AsmOperand::Kind::Reg;
        operand.reg = 31;
        operand.is_sp = true;
        operand.reg_class = text[0] == 'w' ? 'w' : 'x';
        return true;
    }
    if (text == "xzr" || text == "wzr") {
        operand.kind = AsmOperand::Kind::Reg;
        operand.reg = 31;
        operand.is_zr = true;
        operand.reg_class = text[0];
        return true;
    }
    if (text.size() >= 2 && (text[0] == 'v')) {
        size_t dot = text.find('.');
        if (dot == std::string_view::npos) {
            return false;
        }
        uint8_t number = 0;
        if (!parse_reg_number(text.substr(1, dot - 1), 31, number)) {
            return false;
        }
        std::string_view lanes = text.substr(dot + 1);
        if (lanes != "8b" && lanes != "16b") {
            return false;
        }
        operand.kind = AsmOperand::Kind::Vec;
        operand.reg = number;
        operand.reg_class = 'v';
        operand.lanes = lanes == "8b" ? 8 : 16;
        return true;
    }
    char kind = text[0];
    if (kind != 'x' && kind != 'w' && kind != 's' && kind != 'd' &&
        kind != 'q' && kind != 'b') {
        return false;
    }
    unsigned max = (kind == 'x' || kind == 'w') ? 30 : 31;
    uint8_t number = 0;
    if (!parse_reg_number(text.substr(1), max, number)) {
        return false;
    }
    operand.kind = AsmOperand::Kind::Reg;
    operand.reg = number;
    operand.reg_class = kind;
    return true;
}

class InstParser {
public:
    InstParser(Assembler& assembler, Lexer& lexer)
        : asm_(assembler), lexer_(lexer) {}

    void parse(const Token& mnemonic_token) {
        std::string_view mnemonic = mnemonic_token.text;
        std::vector<AsmOperand> operands;
        operands.reserve(5);

        size_t dot = mnemonic.find('.');
        if (dot != std::string_view::npos) {
            uint8_t bits = 0;
            if (!parse_cond_name(mnemonic.substr(dot + 1), bits)) {
                asm_.expr_error(mnemonic_token.line, mnemonic_token.col,
                                "unknown condition suffix on '" +
                                    std::string(mnemonic) + "'");
                lexer_.skip_to_statement_end();
                return;
            }
            AsmOperand cond;
            cond.kind = AsmOperand::Kind::Cond;
            cond.cond = bits;
            operands.push_back(cond);
            mnemonic = mnemonic.substr(0, dot);
        }

        bool barrier_mnemonic =
            mnemonic == "dmb" || mnemonic == "dsb" || mnemonic == "isb";

        const Token& first = lexer_.peek();
        if (first.kind != TokKind::Newline && first.kind != TokKind::End) {
            for (;;) {
                AsmOperand operand;
                if (!parse_operand(operand, barrier_mnemonic)) {
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

        IsaEncoded encoded = backend::aarch64::a64_match_and_encode(
            mnemonic, operands);
        if (!encoded.ok) {
            asm_.expr_error(mnemonic_token.line, mnemonic_token.col,
                            encoded.error);
            lexer_.skip_to_statement_end();
            return;
        }
        if (encoded.fixup == backend::aarch64::IsaFixup::None) {
            asm_.append_inst_word(encoded.word, mnemonic_token);
        } else {
            FixupKind kind = FixupKind::Branch26;
            switch (encoded.fixup) {
                case backend::aarch64::IsaFixup::Branch26:
                    kind = FixupKind::Branch26;
                    break;
                case backend::aarch64::IsaFixup::Branch19:
                    kind = FixupKind::Branch19;
                    break;
                case backend::aarch64::IsaFixup::Page21:
                    kind = FixupKind::Page21;
                    break;
                case backend::aarch64::IsaFixup::PageOff12:
                    kind = FixupKind::PageOff12;
                    break;
                case backend::aarch64::IsaFixup::None:
                    break;
            }
            asm_.append_inst_fixup(encoded.word, kind, encoded.fixup_sym,
                                   encoded.fixup_addend,
                                   encoded.fixup_flavor,
                                   encoded.fixup_access_bytes,
                                   mnemonic_token);
        }

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

    bool parse_immediate(AsmOperand& operand) {
        lexer_.take();
        const Token& at = lexer_.peek();
        ExprValue value = parse_expression(lexer_, asm_);
        if (!value.ok) {
            return false;
        }
        if (!value.is_absolute()) {
            return error(at, "instruction immediates must be absolute");
        }
        operand.kind = AsmOperand::Kind::Imm;
        operand.imm = value.constant;

        const Token& comma = lexer_.peek();
        const Token& shift = lexer_.peek_second();
        if (comma.kind == TokKind::Punct && comma.punct == ',' &&
            shift.kind == TokKind::Ident && shift.text == "lsl") {
            lexer_.take();
            lexer_.take();
            const Token& hash = lexer_.peek();
            if (hash.kind != TokKind::Punct || hash.punct != '#') {
                return error(hash, "expected '#' after 'lsl'");
            }
            lexer_.take();
            ExprValue amount = parse_expression(lexer_, asm_);
            if (!amount.ok) {
                return false;
            }
            if (!amount.is_absolute() ||
                (amount.constant != 16 && amount.constant != 32 &&
                 amount.constant != 48)) {
                return error(hash, "unsupported shift amount");
            }
            operand.shift_hw = static_cast<uint8_t>(amount.constant / 16);
        }
        return true;
    }

    bool parse_memory(AsmOperand& operand) {
        lexer_.take();
        const Token& base_token = lexer_.peek();
        AsmOperand base;
        if (base_token.kind != TokKind::Ident ||
            !parse_register(base_token.text, base) ||
            base.kind != AsmOperand::Kind::Reg || base.reg_class != 'x' ||
            base.is_zr) {
            return error(base_token, "expected an x-register base");
        }
        lexer_.take();
        operand.kind = AsmOperand::Kind::Mem;
        operand.base = base.reg;
        operand.base_is_sp = base.is_sp;
        operand.mem_mode = AsmOperand::MemMode::BaseOnly;

        const Token& after_base = lexer_.peek();
        if (after_base.kind == TokKind::Punct && after_base.punct == ',') {
            lexer_.take();
            const Token& offset = lexer_.peek();
            if (offset.kind == TokKind::Punct && offset.punct == '#') {
                lexer_.take();
                ExprValue value = parse_expression(lexer_, asm_);
                if (!value.ok) {
                    return false;
                }
                if (!value.is_absolute()) {
                    return error(offset, "memory offsets must be absolute");
                }
                operand.imm = value.constant;
                operand.mem_mode = AsmOperand::MemMode::Offset;
            } else {
                AsmOperand sym;
                if (!parse_symbol_operand(sym)) {
                    return false;
                }
                operand.offset_is_sym = true;
                operand.sym = sym.sym;
                operand.addend = sym.addend;
                operand.flavor = sym.flavor;
                operand.mem_mode = AsmOperand::MemMode::Offset;
            }
        }
        const Token& close = lexer_.peek();
        if (close.kind != TokKind::Punct || close.punct != ']') {
            return error(close, "expected ']'");
        }
        lexer_.take();

        const Token& suffix = lexer_.peek();
        if (suffix.kind == TokKind::Punct && suffix.punct == '!') {
            lexer_.take();
            operand.mem_mode = AsmOperand::MemMode::Pre;
            return true;
        }
        const Token& post_comma = lexer_.peek();
        const Token& post_hash = lexer_.peek_second();
        if (post_comma.kind == TokKind::Punct && post_comma.punct == ',' &&
            post_hash.kind == TokKind::Punct && post_hash.punct == '#') {
            lexer_.take();
            lexer_.take();
            ExprValue value = parse_expression(lexer_, asm_);
            if (!value.ok) {
                return false;
            }
            if (!value.is_absolute()) {
                return error(post_comma,
                             "post-index offsets must be absolute");
            }
            operand.imm = value.constant;
            operand.mem_mode = AsmOperand::MemMode::Post;
        }
        return true;
    }

    bool parse_symbol_operand(AsmOperand& operand) {
        operand.kind = AsmOperand::Kind::Sym;
        operand.flavor = SymFlavor::Plain;
        if (lexer_.peek().kind == TokKind::Punct &&
            lexer_.peek().punct == ':') {
            Token colon = lexer_.take();
            const Token& name = lexer_.peek();
            if (name.kind != TokKind::Ident) {
                return error(name, "expected a relocation name after ':'");
            }
            Token kind = lexer_.take();
            const Token& close = lexer_.peek();
            if (close.kind != TokKind::Punct || close.punct != ':') {
                return error(close, "expected ':' after the relocation name");
            }
            lexer_.take();
            if (kind.text == "lo12") {
                operand.flavor = SymFlavor::PageOff;
            } else if (kind.text == "got") {
                operand.flavor = SymFlavor::GotPage;
            } else if (kind.text == "got_lo12") {
                operand.flavor = SymFlavor::GotPageOff;
            } else {
                return error(kind, "unknown relocation ':" +
                                       std::string(kind.text) + ":'");
            }
            const Token& target = lexer_.peek();
            if (target.kind != TokKind::Ident &&
                target.kind != TokKind::String) {
                return error(target, "expected a symbol after the relocation");
            }
            Token name_token = lexer_.take();
            operand.sym = asm_.expr_symbol(name_token.text);
            (void)colon;
            return true;
        }
        const Token& first = lexer_.peek();
        if (first.kind == TokKind::LocalRef) {
            Token ref = lexer_.take();
            SymId id = asm_.expr_local_ref(static_cast<uint32_t>(ref.value),
                                           ref.backward, ref.line, ref.col);
            if (id == no_sym) {
                return false;
            }
            operand.sym = id;
            return true;
        }
        if (first.kind != TokKind::Ident && first.kind != TokKind::String) {
            return error(first, "expected an operand");
        }
        Token name = lexer_.take();
        operand.sym = asm_.expr_symbol(name.text);

        const Token& sign = lexer_.peek();
        if (sign.kind == TokKind::Punct &&
            (sign.punct == '+' || sign.punct == '-')) {
            bool negative = sign.punct == '-';
            const Token& magnitude = lexer_.peek_second();
            if (magnitude.kind == TokKind::Integer) {
                lexer_.take();
                Token value = lexer_.take();
                operand.addend = negative ? -value.value : value.value;
            }
        }

        const Token& at = lexer_.peek();
        if (at.kind == TokKind::Punct && at.punct == '@') {
            lexer_.take();
            const Token& suffix = lexer_.peek();
            if (suffix.kind != TokKind::Ident) {
                return error(suffix, "expected a relocation suffix");
            }
            Token suffix_token = lexer_.take();
            if (suffix_token.text == "PAGE") {
                operand.flavor = SymFlavor::Page;
            } else if (suffix_token.text == "PAGEOFF") {
                operand.flavor = SymFlavor::PageOff;
            } else if (suffix_token.text == "GOTPAGE") {
                operand.flavor = SymFlavor::GotPage;
            } else if (suffix_token.text == "GOTPAGEOFF") {
                operand.flavor = SymFlavor::GotPageOff;
            } else if (suffix_token.text == "TLVPPAGE") {
                operand.flavor = SymFlavor::TlvPage;
            } else if (suffix_token.text == "TLVPPAGEOFF") {
                operand.flavor = SymFlavor::TlvPageOff;
            } else {
                return error(suffix_token,
                             "unknown relocation suffix '@" +
                                 std::string(suffix_token.text) + "'");
            }
        }
        return true;
    }

    bool parse_operand(AsmOperand& operand, bool barrier_mnemonic) {
        const Token& token = lexer_.peek();
        if (token.kind == TokKind::Punct && token.punct == '#') {
            return parse_immediate(operand);
        }
        if (token.kind == TokKind::Punct && token.punct == '[') {
            return parse_memory(operand);
        }
        if (token.kind == TokKind::Ident) {
            if (barrier_mnemonic) {
                Token option = lexer_.take();
                if (option.text != "ish") {
                    return error(option, "unsupported barrier option '" +
                                             std::string(option.text) + "'");
                }
                operand.kind = AsmOperand::Kind::Barrier;
                return true;
            }
            AsmOperand reg;
            if (parse_register(token.text, reg)) {
                lexer_.take();
                operand = reg;
                return true;
            }
            uint8_t cond_bits = 0;
            if (parse_cond_name(token.text, cond_bits)) {
                lexer_.take();
                operand.kind = AsmOperand::Kind::Cond;
                operand.cond = cond_bits;
                return true;
            }
        }
        return parse_symbol_operand(operand);
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
