#include <algorithm>
#include <array>

#include "../backend/common/macho.h"
#include "assembler.h"

namespace aburi::assembler {

namespace {

constexpr uint32_t S_ATTR_PURE_INSTRUCTIONS = 0x80000000u;
constexpr uint32_t S_ATTR_SOME_INSTRUCTIONS = 0x00000400u;
constexpr uint32_t S_CSTRING_LITERALS = 0x2;

FixupKind data_width_for(std::string_view name) {
    if (name == ".byte") {
        return FixupKind::Abs8;
    }
    if (name == ".short" || name == ".hword" || name == ".2byte") {
        return FixupKind::Abs16;
    }
    if (name == ".quad" || name == ".xword" || name == ".8byte") {
        return FixupKind::Abs64;
    }
    return FixupKind::Abs32;
}

}

Assembler::DirectiveHandler Assembler::find_directive(std::string_view name) {
    if (name.size() > 5 && name.substr(0, 5) == ".cfi_") {
        return &Assembler::dir_ignore_line;
    }
    struct DirectiveEntry {
        std::string_view name;
        DirectiveHandler handler;
    };
    static constexpr std::array<DirectiveEntry, 60> directive_table = {{
        {".2byte", &Assembler::dir_data_value},
    {".4byte", &Assembler::dir_data_value},
    {".8byte", &Assembler::dir_data_value},
    {".align", &Assembler::dir_align},
    {".altmacro", &Assembler::dir_unsupported_yet},
    {".ascii", &Assembler::dir_ascii},
    {".asciz", &Assembler::dir_ascii},
    {".balign", &Assembler::dir_align},
    {".bss", &Assembler::dir_builtin_section},
    {".build_version", &Assembler::dir_ignore_line},
    {".byte", &Assembler::dir_data_value},
    {".comm", &Assembler::dir_comm},
    {".const", &Assembler::dir_builtin_section},
    {".cstring", &Assembler::dir_builtin_section},
    {".data", &Assembler::dir_builtin_section},
    {".else", &Assembler::dir_unsupported_yet},
    {".elseif", &Assembler::dir_unsupported_yet},
    {".endif", &Assembler::dir_unsupported_yet},
    {".endm", &Assembler::dir_unsupported_yet},
    {".endr", &Assembler::dir_unsupported_yet},
    {".equ", &Assembler::dir_set},
    {".equiv", &Assembler::dir_set},
    {".file", &Assembler::dir_ignore_line},
    {".global", &Assembler::dir_symbol_binding},
    {".globl", &Assembler::dir_symbol_binding},
    {".hword", &Assembler::dir_data_value},
    {".if", &Assembler::dir_unsupported_yet},
    {".ifb", &Assembler::dir_unsupported_yet},
    {".ifc", &Assembler::dir_unsupported_yet},
    {".ifdef", &Assembler::dir_unsupported_yet},
    {".ifndef", &Assembler::dir_unsupported_yet},
    {".incbin", &Assembler::dir_unsupported_yet},
    {".include", &Assembler::dir_unsupported_yet},
    {".int", &Assembler::dir_data_value},
    {".irp", &Assembler::dir_unsupported_yet},
    {".irpc", &Assembler::dir_unsupported_yet},
    {".loc", &Assembler::dir_ignore_line},
    {".long", &Assembler::dir_data_value},
    {".macro", &Assembler::dir_unsupported_yet},
    {".noaltmacro", &Assembler::dir_unsupported_yet},
    {".org", &Assembler::dir_org},
    {".p2align", &Assembler::dir_align},
    {".private_extern", &Assembler::dir_symbol_binding},
    {".quad", &Assembler::dir_data_value},
    {".rept", &Assembler::dir_unsupported_yet},
    {".section", &Assembler::dir_section},
    {".set", &Assembler::dir_set},
    {".short", &Assembler::dir_data_value},
    {".skip", &Assembler::dir_space},
    {".sleb128", &Assembler::dir_leb},
    {".space", &Assembler::dir_space},
    {".string", &Assembler::dir_ascii},
    {".subsections_via_symbols", &Assembler::dir_ignore_line},
    {".text", &Assembler::dir_builtin_section},
    {".uleb128", &Assembler::dir_leb},
    {".weak_definition", &Assembler::dir_symbol_binding},
    {".word", &Assembler::dir_data_value},
    {".xword", &Assembler::dir_data_value},
    {".zero", &Assembler::dir_space},
    {".zerofill", &Assembler::dir_zerofill},
    }};
    auto it = std::lower_bound(
        directive_table.begin(), directive_table.end(), name,
        [](const DirectiveEntry& entry, std::string_view lookup) {
            return entry.name < lookup;
        });
    if (it != directive_table.end() && it->name == name) {
        return it->handler;
    }
    return nullptr;
}

static bool take_name_operand(Lexer& lexer, std::string_view& out) {
    const Token& token = lexer.peek();
    if (token.kind == TokKind::Ident || token.kind == TokKind::String) {
        out = token.text;
        lexer.take();
        return true;
    }
    return false;
}

void Assembler::dir_section(const Token& directive) {
    std::string_view segname;
    if (!take_name_operand(lexer_, segname)) {
        error(directive, "expected a section name after '.section'");
        lexer_.skip_to_statement_end();
        return;
    }
    if (asm_target_is_elf(*options_.target)) {
        set_current_section(find_or_add_section("", segname, 0, false));
        lexer_.skip_to_statement_end();
        return;
    }
    if (!segname.empty() && segname[0] == '.') {
        error(directive, "expected the Mach-O 'segment,section' form");
        lexer_.skip_to_statement_end();
        return;
    }
    if (!take_comma()) {
        error(directive, "expected ',' after the segment name");
        lexer_.skip_to_statement_end();
        return;
    }
    std::string_view sectname;
    if (!take_name_operand(lexer_, sectname)) {
        error(directive, "expected a section name");
        lexer_.skip_to_statement_end();
        return;
    }

    uint32_t flags = 0;
    while (take_comma()) {
        std::string_view attribute;
        if (!take_name_operand(lexer_, attribute)) {
            error(directive, "expected a section type or attribute");
            lexer_.skip_to_statement_end();
            return;
        }
        if (!backend::apply_macho_section_attribute(std::string(attribute),
                                                    flags)) {
            error(directive, "unknown section type or attribute '" +
                                 std::string(attribute) + "'");
            lexer_.skip_to_statement_end();
            return;
        }
    }
    set_current_section(
        find_or_add_section(segname, sectname, flags, false));
    expect_statement_end();
}

void Assembler::dir_builtin_section(const Token& directive) {
    if (asm_target_is_elf(*options_.target)) {
        set_current_section(
            find_or_add_section("", directive.text, 0,
                                directive.text == ".bss"));
        expect_statement_end();
        return;
    }
    if (directive.text == ".text") {
        set_current_section(find_or_add_section(
            "__TEXT", "__text",
            S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS, false));
    } else if (directive.text == ".data") {
        set_current_section(
            find_or_add_section("__DATA", "__data", 0, false));
    } else if (directive.text == ".bss") {
        set_current_section(
            find_or_add_section("__DATA", "__bss", 0, true));
    } else if (directive.text == ".const") {
        set_current_section(
            find_or_add_section("__TEXT", "__const", 0, false));
    } else {
        set_current_section(find_or_add_section(
            "__TEXT", "__cstring", S_CSTRING_LITERALS, false));
    }
    expect_statement_end();
}

void Assembler::dir_symbol_binding(const Token& directive) {
    for (;;) {
        const Token& name = lexer_.peek();
        if (name.kind != TokKind::Ident) {
            error(name, "expected a symbol name after '" +
                            std::string(directive.text) + "'");
            lexer_.skip_to_statement_end();
            return;
        }
        SymId id = unit_.symbols.intern(name.text);
        AsmSymbol& symbol = unit_.symbols.sym(id);
        if (directive.text == ".weak_definition") {
            symbol.weak = true;
        } else if (directive.text == ".private_extern") {
            symbol.global = true;
            symbol.hidden = true;
        } else {
            symbol.global = true;
        }
        lexer_.take();
        if (!take_comma()) {
            break;
        }
    }
    expect_statement_end();
}

void Assembler::dir_align(const Token& directive) {
    int64_t amount = 0;
    if (!parse_absolute(amount, directive, "the alignment")) {
        lexer_.skip_to_statement_end();
        return;
    }
    uint8_t fill = 0;
    bool fill_given = false;
    int64_t max_bytes = -1;
    if (take_comma()) {
        const Token& next = lexer_.peek();
        bool fill_omitted =
            next.kind == TokKind::Punct && next.punct == ',';
        if (!fill_omitted) {
            int64_t fill_value = 0;
            if (!parse_absolute(fill_value, directive, "the fill byte")) {
                lexer_.skip_to_statement_end();
                return;
            }
            fill = static_cast<uint8_t>(fill_value);
            fill_given = true;
        }
        if (take_comma()) {
            if (!parse_absolute(max_bytes, directive,
                                "the alignment limit")) {
                lexer_.skip_to_statement_end();
                return;
            }
        }
    }

    uint32_t align_log2 = 0;
    if (directive.text == ".balign") {
        if (amount <= 0 || (amount & (amount - 1)) != 0) {
            error(directive, "'.balign' requires a power-of-two byte count");
            lexer_.skip_to_statement_end();
            return;
        }
        while ((1ll << align_log2) < amount) {
            ++align_log2;
        }
    } else {
        if (amount < 0 || amount > 30) {
            error(directive, "alignment exponent is out of range");
            lexer_.skip_to_statement_end();
            return;
        }
        align_log2 = static_cast<uint32_t>(amount);
    }
    align_current(align_log2, fill, fill_given, max_bytes, directive);
    expect_statement_end();
}

void Assembler::dir_data_value(const Token& directive) {
    FixupKind kind = data_width_for(directive.text);
    for (;;) {
        const Token& name = lexer_.peek();
        const Token& at_sign = lexer_.peek_second();
        if (kind == FixupKind::Abs32 &&
            (name.kind == TokKind::Ident || name.kind == TokKind::String) &&
            at_sign.kind == TokKind::Punct && at_sign.punct == '@') {
            Token name_token = lexer_.take();
            lexer_.take();
            const Token& suffix = lexer_.peek();
            if (suffix.kind != TokKind::Ident ||
                (suffix.text != "GOT" && suffix.text != "GOTPCREL")) {
                error(suffix, "unsupported relocation suffix in a data "
                              "directive");
                lexer_.skip_to_statement_end();
                return;
            }
            bool gotpcrel = suffix.text == "GOTPCREL";
            lexer_.take();
            if (gotpcrel) {
                int64_t addend = 0;
                const Token& sign = lexer_.peek();
                if (sign.kind == TokKind::Punct &&
                    (sign.punct == '+' || sign.punct == '-')) {
                    bool negative = sign.punct == '-';
                    lexer_.take();
                    if (!parse_absolute(addend, directive, "the addend")) {
                        lexer_.skip_to_statement_end();
                        return;
                    }
                    if (negative) {
                        addend = -addend;
                    }
                }
                if (!check_not_zerofill(directive)) {
                    lexer_.skip_to_statement_end();
                    return;
                }
                AsmSection& section = cur();
                PendingFixup fixup;
                fixup.offset = section.bytes.size();
                fixup.kind = FixupKind::PcRel32;
                fixup.flavor = backend::SymFlavor::GotPcRel;
                fixup.constant = addend;
                fixup.pos_sym = expr_symbol(name_token.text);
                fixup.deferred_seq =
                    static_cast<uint32_t>(section.deferred.size());
                fixup.line = directive.line;
                fixup.col = directive.col;
                section.fixups.push_back(fixup);
                section.bytes.insert(section.bytes.end(), 4, 0);
                if (!take_comma()) {
                    break;
                }
                continue;
            }
            const Token& minus = lexer_.peek();
            const Token& label = lexer_.peek_second();
            if (minus.kind != TokKind::Punct || minus.punct != '-' ||
                label.kind != TokKind::Ident) {
                error(minus, "expected '- label' after '@GOT'");
                lexer_.skip_to_statement_end();
                return;
            }
            lexer_.take();
            Token label_token = lexer_.take();
            if (!check_not_zerofill(directive)) {
                lexer_.skip_to_statement_end();
                return;
            }
            AsmSection& section = cur();
            PendingFixup fixup;
            fixup.offset = section.bytes.size();
            fixup.kind = FixupKind::GotDelta32;
            fixup.pos_sym = expr_symbol(name_token.text);
            fixup.neg_sym = expr_symbol(label_token.text);
            fixup.deferred_seq =
                static_cast<uint32_t>(section.deferred.size());
            fixup.line = directive.line;
            fixup.col = directive.col;
            section.fixups.push_back(fixup);
            section.bytes.insert(section.bytes.end(), 4, 0);
        } else {
            ExprValue value = parse_expression(lexer_, *this);
            if (!value.ok) {
                lexer_.skip_to_statement_end();
                return;
            }
            append_data_value(kind, value, directive);
        }
        if (!take_comma()) {
            break;
        }
    }
    expect_statement_end();
}

void Assembler::dir_ascii(const Token& directive) {
    bool terminate = directive.text != ".ascii";
    if (!check_not_zerofill(directive)) {
        lexer_.skip_to_statement_end();
        return;
    }
    for (;;) {
        const Token& token = lexer_.peek();
        if (token.kind != TokKind::String) {
            error(token, "expected a string literal");
            lexer_.skip_to_statement_end();
            return;
        }
        Token literal = lexer_.take();
        append_bytes(reinterpret_cast<const uint8_t*>(literal.text.data()),
                     literal.text.size());
        if (terminate) {
            uint8_t nul = 0;
            append_bytes(&nul, 1);
        }
        if (!take_comma()) {
            break;
        }
    }
    expect_statement_end();
}

void Assembler::dir_space(const Token& directive) {
    int64_t size = 0;
    if (!parse_absolute(size, directive, "the size")) {
        lexer_.skip_to_statement_end();
        return;
    }
    if (size < 0) {
        error(directive, "the size must not be negative");
        lexer_.skip_to_statement_end();
        return;
    }
    int64_t fill = 0;
    if (take_comma()) {
        if (!parse_absolute(fill, directive, "the fill byte")) {
            lexer_.skip_to_statement_end();
            return;
        }
    }
    append_space(static_cast<uint64_t>(size), static_cast<uint8_t>(fill),
                 directive);
    expect_statement_end();
}

void Assembler::dir_comm(const Token& directive) {
    const Token& name = lexer_.peek();
    if (name.kind != TokKind::Ident) {
        error(name, "expected a symbol name after '.comm'");
        lexer_.skip_to_statement_end();
        return;
    }
    Token name_token = lexer_.take();
    if (!take_comma()) {
        error(directive, "expected ',' after the symbol name");
        lexer_.skip_to_statement_end();
        return;
    }
    int64_t size = 0;
    if (!parse_absolute(size, directive, "the common size")) {
        lexer_.skip_to_statement_end();
        return;
    }
    int64_t align_log2 = 0;
    if (take_comma()) {
        if (!parse_absolute(align_log2, directive, "the alignment")) {
            lexer_.skip_to_statement_end();
            return;
        }
    }
    if (size < 0 || align_log2 < 0 || align_log2 > 15) {
        error(directive, "'.comm' size or alignment is out of range");
        lexer_.skip_to_statement_end();
        return;
    }
    CommonSymbol common;
    common.name = std::string(name_token.text);
    common.size = static_cast<uint64_t>(size);
    common.align_log2 = static_cast<uint32_t>(align_log2);
    unit_.commons.push_back(std::move(common));
    expect_statement_end();
}

void Assembler::dir_zerofill(const Token& directive) {
    std::string_view segname;
    std::string_view sectname;
    if (!take_name_operand(lexer_, segname) || !take_comma() ||
        !take_name_operand(lexer_, sectname)) {
        error(directive,
              "expected '.zerofill segment,section[,symbol,size[,align]]'");
        lexer_.skip_to_statement_end();
        return;
    }
    int section = find_or_add_section(segname, sectname, 0, true);
    if (!unit_.sections[static_cast<size_t>(section)].zerofill) {
        error(directive, "section '" + std::string(sectname) +
                             "' already holds initialized data");
        lexer_.skip_to_statement_end();
        return;
    }
    if (!take_comma()) {
        expect_statement_end();
        return;
    }

    const Token& name = lexer_.peek();
    if (name.kind != TokKind::Ident) {
        error(name, "expected a symbol name");
        lexer_.skip_to_statement_end();
        return;
    }
    Token name_token = lexer_.take();
    if (!take_comma()) {
        error(directive, "expected ',' after the symbol name");
        lexer_.skip_to_statement_end();
        return;
    }
    int64_t size = 0;
    if (!parse_absolute(size, directive, "the zerofill size")) {
        lexer_.skip_to_statement_end();
        return;
    }
    int64_t align_log2 = 0;
    if (take_comma()) {
        if (!parse_absolute(align_log2, directive, "the alignment")) {
            lexer_.skip_to_statement_end();
            return;
        }
    }
    if (size < 0 || align_log2 < 0 || align_log2 > 30) {
        error(directive, "'.zerofill' size or alignment is out of range");
        lexer_.skip_to_statement_end();
        return;
    }

    int saved_section = current_section_;
    set_current_section(section);
    align_current(static_cast<uint32_t>(align_log2), 0, true, -1,
                  directive);
    SymId id = unit_.symbols.intern(name_token.text);
    bind_symbol_to_location(id, name_token);
    cur().zerofill_size += static_cast<uint64_t>(size);
    set_current_section(saved_section);
    expect_statement_end();
}

void Assembler::dir_set(const Token& directive) {
    const Token& name = lexer_.peek();
    if (name.kind != TokKind::Ident) {
        error(name, "expected a symbol name after '" +
                        std::string(directive.text) + "'");
        lexer_.skip_to_statement_end();
        return;
    }
    Token name_token = lexer_.take();
    if (!take_comma()) {
        error(directive, "expected ',' after the symbol name");
        lexer_.skip_to_statement_end();
        return;
    }
    ExprValue value = parse_expression(lexer_, *this);
    if (!value.ok) {
        lexer_.skip_to_statement_end();
        return;
    }
    SymId id = unit_.symbols.intern(name_token.text);
    if (directive.text == ".equiv" &&
        unit_.symbols.sym(id).state != SymState::Undefined) {
        error(name_token, "'.equiv' symbol '" +
                              std::string(name_token.text) +
                              "' is already defined");
        lexer_.skip_to_statement_end();
        return;
    }
    apply_set(id, value, name_token);
    expect_statement_end();
}

void Assembler::dir_org(const Token& directive) {
    int64_t target = 0;
    if (!parse_absolute(target, directive, "the '.org' offset")) {
        lexer_.skip_to_statement_end();
        return;
    }
    int64_t fill = 0;
    if (take_comma()) {
        if (!parse_absolute(fill, directive, "the fill byte")) {
            lexer_.skip_to_statement_end();
            return;
        }
    }
    AsmSection& section = cur();
    if (target < 0 || static_cast<uint64_t>(target) < section.size()) {
        error(directive, "'.org' cannot move the location counter backwards");
        lexer_.skip_to_statement_end();
        return;
    }
    append_space(static_cast<uint64_t>(target) - section.size(),
                 static_cast<uint8_t>(fill), directive);
    expect_statement_end();
}

void Assembler::dir_ignore_line(const Token& directive) {
    (void)directive;
    lexer_.skip_to_statement_end();
}

void Assembler::dir_unsupported_yet(const Token& directive) {
    error(directive, "directive '" + std::string(directive.text) +
                         "' is not supported yet by the integrated "
                         "assembler");
    lexer_.skip_to_statement_end();
}

}
