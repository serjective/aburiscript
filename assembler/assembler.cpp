#include "assembler.h"

#include <algorithm>

#include "../backend/aarch64/encode.h"
#include "../backend/x86/isa.h"
#include "aarch64/asm_aarch64.h"
#include "sink.h"
#include "x86/asm_x86.h"

namespace aburi::assembler {

namespace {

constexpr size_t error_limit = 20;

constexpr uint32_t S_ATTR_PURE_INSTRUCTIONS = 0x80000000u;
constexpr uint32_t S_ATTR_SOME_INSTRUCTIONS = 0x00000400u;
constexpr uint32_t S_CSTRING_LITERALS = 0x2;
bool section_is_code(const AsmSection& section) {
    if (!section.segname.empty()) {
        return (section.flags &
                (S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS)) != 0;
    }
    return section.sectname.rfind(".text", 0) == 0;
}

bool fits_width(int64_t value, uint32_t width_bytes) {
    if (width_bytes >= 8) {
        return true;
    }
    int64_t min_signed =
        -(static_cast<int64_t>(1) << (width_bytes * 8 - 1));
    int64_t max_unsigned =
        (static_cast<int64_t>(1) << (width_bytes * 8)) - 1;
    return value >= min_signed && value <= max_unsigned;
}

}

AssembleResult assemble_string_to_object(std::string_view source,
                                         const AsmOptions& options,
                                         std::ostream& object_out) {
    AssembleResult result;
    if (!options.target) {
        Diagnostic diag;
        diag.level = DiagnosticLevel::Error;
        diag.message = "assembler: no target configured";
        result.diagnostics.push_back(std::move(diag));
        return result;
    }
    bool supported = options.target->arch == TargetArch::AARCH64 ||
                     options.target->arch == TargetArch::X86_64;
    if (!supported || asm_target_is_elf(*options.target)) {
        Diagnostic diag;
        diag.level = DiagnosticLevel::Error;
        diag.message = "assembler: target '" + options.target->triple +
                       "' is not supported by the integrated assembler yet";
        result.diagnostics.push_back(std::move(diag));
        return result;
    }

    Assembler assembler(source, options);
    bool assembled = assembler.run();
    result.diagnostics = std::move(assembler.diagnostics());
    if (!assembled) {
        return result;
    }

    std::string sink_error;
    if (!write_macho_object(assembler.unit(), *options.target, object_out,
                            sink_error)) {
        Diagnostic diag;
        diag.level = DiagnosticLevel::Error;
        diag.message = "assembler: " + sink_error;
        result.diagnostics.push_back(std::move(diag));
        return result;
    }
    result.ok = true;
    return result;
}

Assembler::Assembler(std::string_view source, const AsmOptions& options)
    : lexer_(source), options_(options) {
    lexer_.set_hash_comments(options_.target->arch == TargetArch::X86_64 ||
                             options_.target->arch == TargetArch::X86);
    current_section_ = asm_target_is_elf(*options_.target)
        ? find_or_add_section("", ".text", 0, false)
        : find_or_add_section(
              "__TEXT", "__text",
              S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS, false);
}

bool Assembler::run() {
    while (error_count_ < error_limit) {
        const Token& token = lexer_.peek();
        if (token.kind == TokKind::End) {
            break;
        }
        if (token.kind == TokKind::Newline) {
            lexer_.take();
            continue;
        }
        parse_statement();
    }
    if (error_count_ >= error_limit) {
        Diagnostic diag;
        diag.level = DiagnosticLevel::Error;
        diag.message = options_.filename + ": too many errors, giving up";
        diagnostics_.push_back(std::move(diag));
        return false;
    }
    finalize_fixups();
    return error_count_ == 0;
}

void Assembler::parse_statement() {
    for (;;) {
        const Token& first = lexer_.peek();
        const Token& second = lexer_.peek_second();
        bool is_colon =
            second.kind == TokKind::Punct && second.punct == ':';
        if (first.kind == TokKind::Ident && first.text != "." && is_colon) {
            Token name = lexer_.take();
            lexer_.take();
            define_label(name);
            continue;
        }
        if (first.kind == TokKind::Integer && is_colon) {
            Token number = lexer_.take();
            lexer_.take();
            define_local_label(number);
            continue;
        }
        break;
    }

    const Token& token = lexer_.peek();
    if (token.kind == TokKind::Newline || token.kind == TokKind::End) {
        if (token.kind == TokKind::Newline) {
            lexer_.take();
        }
        return;
    }
    if (token.kind != TokKind::Ident) {
        error(token, "expected a directive, label, or instruction");
        lexer_.skip_to_statement_end();
        return;
    }

    const Token& second = lexer_.peek_second();
    if (second.kind == TokKind::Punct && second.punct == '=') {
        Token name = lexer_.take();
        lexer_.take();
        handle_assignment(name);
        return;
    }

    if (!token.text.empty() && token.text[0] == '.') {
        Token directive = lexer_.take();
        DirectiveHandler handler = find_directive(directive.text);
        if (handler == nullptr) {
            error(directive,
                  "unknown directive '" + std::string(directive.text) + "'");
            lexer_.skip_to_statement_end();
            return;
        }
        (this->*handler)(directive);
        return;
    }

    Token mnemonic = lexer_.take();
    if (options_.target->arch == TargetArch::X86_64) {
        x86::parse_instruction(*this, lexer_, mnemonic);
        return;
    }
    aarch64::parse_instruction(*this, lexer_, mnemonic);
}

void Assembler::append_inst_word(uint32_t word, const Token& at) {
    if (!check_not_zerofill(at)) {
        return;
    }
    AsmSection& section = cur();
    for (int i = 0; i < 4; ++i) {
        section.bytes.push_back(static_cast<uint8_t>(word >> (8 * i)));
    }
}

void Assembler::append_inst_fixup(uint32_t word, FixupKind kind, SymId sym,
                                  int64_t addend, backend::SymFlavor flavor,
                                  uint8_t access_bytes, const Token& at) {
    if (!check_not_zerofill(at)) {
        return;
    }
    PendingFixup fixup;
    fixup.offset = cur().bytes.size();
    fixup.kind = kind;
    fixup.constant = addend;
    fixup.pos_sym = sym;
    fixup.flavor = flavor;
    fixup.access_bytes = access_bytes;
    fixup.deferred_seq = static_cast<uint32_t>(cur().deferred.size());
    fixup.line = at.line;
    fixup.col = at.col;
    cur().fixups.push_back(fixup);
    append_inst_word(word, at);
}

void Assembler::append_inst_bytes(const uint8_t* bytes, size_t size,
                                  const Token& at) {
    if (!check_not_zerofill(at)) {
        return;
    }
    AsmSection& section = cur();
    section.bytes.insert(section.bytes.end(), bytes, bytes + size);
}

void Assembler::append_inst_bytes_fixup(const uint8_t* bytes, size_t size,
                                        FixupKind kind, size_t field_offset,
                                        SymId sym, int64_t addend,
                                        backend::SymFlavor flavor,
                                        uint8_t pcrel_extra, const Token& at) {
    if (!check_not_zerofill(at)) {
        return;
    }
    PendingFixup fixup;
    fixup.offset = cur().bytes.size() + field_offset;
    fixup.kind = kind;
    fixup.constant = addend;
    fixup.pos_sym = sym;
    fixup.flavor = flavor;
    fixup.pcrel_extra = pcrel_extra;
    fixup.deferred_seq = static_cast<uint32_t>(cur().deferred.size());
    fixup.line = at.line;
    fixup.col = at.col;
    cur().fixups.push_back(fixup);
    append_inst_bytes(bytes, size, at);
}

void Assembler::append_branch(const uint8_t* near_bytes, size_t near_size,
                              size_t rel_offset, uint8_t short_opcode,
                              SymId target, int64_t addend, const Token& at) {
    if (!check_not_zerofill(at)) {
        return;
    }
    if (near_size > sizeof(DeferredBranch::near_bytes)) {
        error(at, "branch encoding is too long");
        return;
    }
    AsmSection& section = cur();
    DeferredField field;
    field.kind = DeferredKind::Branch;
    field.raw_offset = section.bytes.size();
    field.constant = addend;
    field.pos_sym = target;
    field.line = at.line;
    field.col = at.col;
    field.branch.short_opcode = short_opcode;
    field.branch.near_size = static_cast<uint8_t>(near_size);
    field.branch.rel_offset = static_cast<uint8_t>(rel_offset);
    for (size_t i = 0; i < near_size; ++i) {
        field.branch.near_bytes[i] = near_bytes[i];
    }
    field.size = field.branch.near_size;
    section.deferred.push_back(field);
}

void Assembler::define_label(const Token& name) {
    SymId id = unit_.symbols.intern(name.text);
    bind_symbol_to_location(id, name);
}

void Assembler::define_local_label(const Token& number) {
    uint32_t value = static_cast<uint32_t>(number.value);
    LocalLabelState& state = local_labels_[value];
    SymId id =
        unit_.symbols.make_internal(std::to_string(value) + ":");
    bind_symbol_to_location(id, number);
    state.last_def = id;
    for (SymId pending : state.pending_forward) {
        bind_symbol_to_location(pending, number);
    }
    state.pending_forward.clear();
}

void Assembler::handle_assignment(const Token& name) {
    ExprValue value = parse_expression(lexer_, *this);
    if (!value.ok) {
        lexer_.skip_to_statement_end();
        return;
    }
    SymId id = unit_.symbols.intern(name.text);
    apply_set(id, value, name);
    expect_statement_end();
}

void Assembler::bind_symbol_to_location(SymId id, const Token& at) {
    AsmSymbol& symbol = unit_.symbols.sym(id);
    if (symbol.state != SymState::Undefined && !symbol.from_set) {
        error(at, "symbol '" + symbol.name + "' is already defined");
        return;
    }
    symbol.state = SymState::Label;
    symbol.from_set = false;
    symbol.section = current_section_;
    symbol.offset = cur().size();
    symbol.deferred_seq = static_cast<uint32_t>(cur().deferred.size());
}

void Assembler::apply_set(SymId id, const ExprValue& value, const Token& at) {
    AsmSymbol& symbol = unit_.symbols.sym(id);
    if (symbol.state != SymState::Undefined && !symbol.from_set) {
        error(at, "symbol '" + symbol.name + "' is already defined");
        return;
    }
    if (value.neg_sym != no_sym) {
        const AsmSymbol& neg = unit_.symbols.sym(value.neg_sym);
        const AsmSymbol& pos = value.pos_sym != no_sym
                                   ? unit_.symbols.sym(value.pos_sym)
                                   : neg;
        if (value.pos_sym == no_sym || pos.state != SymState::Label ||
            neg.state != SymState::Label || pos.section != neg.section) {
            error(at, "'.set' value is not representable");
            return;
        }
        symbol.state = SymState::Constant;
        symbol.from_set = true;
        symbol.value = value.constant +
                       static_cast<int64_t>(pos.offset) -
                       static_cast<int64_t>(neg.offset);
        return;
    }
    if (value.pos_sym != no_sym) {
        const AsmSymbol& target = unit_.symbols.sym(value.pos_sym);
        if (target.state != SymState::Label) {
            error(at, "'.set' target '" + target.name +
                          "' is not defined yet");
            return;
        }
        symbol.state = SymState::Label;
        symbol.from_set = true;
        symbol.section = target.section;
        symbol.offset =
            target.offset + static_cast<uint64_t>(value.constant);
        return;
    }
    symbol.state = SymState::Constant;
    symbol.from_set = true;
    symbol.value = value.constant;
}

SymId Assembler::expr_symbol(std::string_view name) {
    SymId id = unit_.symbols.intern(name);
    unit_.symbols.sym(id).referenced = true;
    return id;
}

SymId Assembler::expr_here() {
    SymId id = unit_.symbols.make_internal(".");
    AsmSymbol& symbol = unit_.symbols.sym(id);
    symbol.state = SymState::Label;
    symbol.section = current_section_;
    symbol.offset = cur().size();
    return id;
}

SymId Assembler::expr_local_ref(uint32_t number, bool backward, uint32_t line,
                                uint32_t col) {
    LocalLabelState& state = local_labels_[number];
    if (backward) {
        if (state.last_def == no_sym) {
            error(line, col,
                  "no preceding definition for local label '" +
                      std::to_string(number) + "b'");
            return no_sym;
        }
        return state.last_def;
    }
    SymId id =
        unit_.symbols.make_internal(std::to_string(number) + "f");
    state.pending_forward.push_back(id);
    return id;
}

bool Assembler::expr_constant_value(SymId id, int64_t& out) const {
    const AsmSymbol& symbol = unit_.symbols.sym(id);
    if (symbol.state == SymState::Constant) {
        out = symbol.value;
        return true;
    }
    return false;
}

void Assembler::expr_error(uint32_t line, uint32_t col,
                           const std::string& message) {
    error(line, col, message);
}

int Assembler::find_or_add_section(std::string_view segname,
                                   std::string_view sectname, uint32_t flags,
                                   bool zerofill) {
    for (size_t i = 0; i < unit_.sections.size(); ++i) {
        if (unit_.sections[i].segname == segname &&
            unit_.sections[i].sectname == sectname) {
            return static_cast<int>(i);
        }
    }
    AsmSection section;
    section.segname = std::string(segname);
    section.sectname = std::string(sectname);
    section.flags = flags;
    section.zerofill = zerofill;
    unit_.sections.push_back(std::move(section));
    return static_cast<int>(unit_.sections.size()) - 1;
}

AsmSection& Assembler::cur() {
    return unit_.sections[static_cast<size_t>(current_section_)];
}

void Assembler::align_current(uint32_t align_log2, uint8_t fill,
                              bool fill_given, int64_t max_bytes,
                              const Token& at) {
    if (align_log2 > 30) {
        error(at, "alignment is out of range");
        return;
    }
    AsmSection& section = cur();
    if (align_log2 > section.align_log2) {
        section.align_log2 = align_log2;
    }
    bool nop_fill = !fill_given && section_is_code(section) &&
                    options_.target->arch == TargetArch::X86_64;
    if (!section.zerofill && !section.deferred.empty()) {
        if (max_bytes >= 0) {
            error(at, "alignment limits after variable-size data are not "
                      "supported");
            return;
        }
        DeferredField field;
        field.kind = DeferredKind::Align;
        field.raw_offset = section.bytes.size();
        field.align_log2 = align_log2;
        field.fill = fill;
        field.nop_fill = nop_fill;
        field.line = at.line;
        field.col = at.col;
        section.deferred.push_back(field);
        return;
    }
    uint64_t alignment = 1ull << align_log2;
    uint64_t size = section.size();
    uint64_t aligned = (size + alignment - 1) & ~(alignment - 1);
    if (max_bytes >= 0 &&
        aligned - size > static_cast<uint64_t>(max_bytes)) {
        return;
    }
    if (section.zerofill) {
        section.zerofill_size = aligned;
        return;
    }
    if (nop_fill) {
        backend::x86::x86_append_nop_padding(section.bytes,
                                             aligned - section.bytes.size());
        return;
    }
    while (section.bytes.size() < aligned) {
        section.bytes.push_back(fill);
    }
}

void Assembler::dir_leb(const Token& directive) {
    if (!check_not_zerofill(directive)) {
        lexer_.skip_to_statement_end();
        return;
    }
    bool is_signed = directive.text == ".sleb128";
    for (;;) {
        ExprValue value = parse_expression(lexer_, *this);
        if (!value.ok) {
            lexer_.skip_to_statement_end();
            return;
        }
        AsmSection& section = cur();
        if (value.is_absolute()) {
            uint64_t bits = static_cast<uint64_t>(value.constant);
            if (is_signed) {
                int64_t rest = value.constant;
                bool more = true;
                while (more) {
                    uint8_t byte = static_cast<uint8_t>(rest & 0x7F);
                    bool sign = (byte & 0x40) != 0;
                    rest >>= 7;
                    more = !((rest == 0 && !sign) || (rest == -1 && sign));
                    section.bytes.push_back(more ? (byte | 0x80) : byte);
                }
            } else {
                do {
                    uint8_t byte = static_cast<uint8_t>(bits & 0x7F);
                    bits >>= 7;
                    section.bytes.push_back(bits != 0 ? (byte | 0x80)
                                                      : byte);
                } while (bits != 0);
            }
        } else {
            DeferredField field;
            field.kind =
                is_signed ? DeferredKind::Sleb : DeferredKind::Uleb;
            field.raw_offset = section.bytes.size();
            field.constant = value.constant;
            field.pos_sym = value.pos_sym;
            field.neg_sym = value.neg_sym;
            field.line = directive.line;
            field.col = directive.col;
            section.deferred.push_back(field);
        }
        if (!take_comma()) {
            break;
        }
    }
    expect_statement_end();
}
bool Assembler::check_not_zerofill(const Token& at) {
    if (cur().zerofill) {
        error(at, "cannot emit data into a zerofill section");
        return false;
    }
    return true;
}

void Assembler::append_bytes(const uint8_t* data, size_t size) {
    AsmSection& section = cur();
    section.bytes.insert(section.bytes.end(), data, data + size);
}

void Assembler::append_data_value(FixupKind kind, const ExprValue& value,
                                  const Token& at) {
    if (!check_not_zerofill(at)) {
        return;
    }
    AsmSection& section = cur();
    uint32_t width = fixup_width_bytes(kind);
    if (value.is_absolute()) {
        if (!fits_width(value.constant, width)) {
            error(at, "value " + std::to_string(value.constant) +
                          " is out of range for a " + std::to_string(width) +
                          "-byte field");
            return;
        }
        uint64_t bits = static_cast<uint64_t>(value.constant);
        for (uint32_t i = 0; i < width; ++i) {
            section.bytes.push_back(static_cast<uint8_t>(bits >> (8 * i)));
        }
        return;
    }
    PendingFixup fixup;
    fixup.offset = section.bytes.size();
    fixup.kind = kind;
    fixup.constant = value.constant;
    fixup.pos_sym = value.pos_sym;
    fixup.neg_sym = value.neg_sym;
    fixup.deferred_seq = static_cast<uint32_t>(section.deferred.size());
    fixup.line = at.line;
    fixup.col = at.col;
    section.fixups.push_back(fixup);
    for (uint32_t i = 0; i < width; ++i) {
        section.bytes.push_back(0);
    }
}

void Assembler::append_space(uint64_t size, uint8_t fill, const Token& at) {
    AsmSection& section = cur();
    if (section.zerofill) {
        if (fill != 0) {
            error(at, "cannot fill a zerofill section with a nonzero byte");
            return;
        }
        section.zerofill_size += size;
        return;
    }
    section.bytes.insert(section.bytes.end(), size, fill);
}
bool Assembler::expect_statement_end() {
    const Token& token = lexer_.peek();
    if (token.kind == TokKind::Newline || token.kind == TokKind::End) {
        if (token.kind == TokKind::Newline) {
            lexer_.take();
        }
        return true;
    }
    error(token, "unexpected token at end of statement");
    lexer_.skip_to_statement_end();
    return false;
}

bool Assembler::take_comma() {
    const Token& token = lexer_.peek();
    if (token.kind == TokKind::Punct && token.punct == ',') {
        lexer_.take();
        return true;
    }
    return false;
}

bool Assembler::parse_absolute(int64_t& out, const Token& at,
                               const char* what_for) {
    ExprValue value = parse_expression(lexer_, *this);
    if (!value.ok) {
        return false;
    }
    if (!value.is_absolute()) {
        error(at, std::string(what_for) + " must be an absolute expression");
        return false;
    }
    out = value.constant;
    return true;
}
namespace {

struct ResolvedSym {
    enum class Kind { Absolute, InSection, External, Failed } kind;
    int64_t value = 0;
    int section = -1;
    uint64_t offset = 0;
};

struct AtomMap {
    std::vector<std::vector<std::pair<uint64_t, SymId>>> starts;
    std::pair<SymId, int64_t> atom_at(int section, uint64_t offset) const {
        const auto& atoms = starts[static_cast<size_t>(section)];
        SymId atom = no_sym;
        uint64_t atom_offset = 0;
        for (const auto& [start, symbol] : atoms) {
            if (start > offset) {
                break;
            }
            atom = symbol;
            atom_offset = start;
        }
        return {atom, static_cast<int64_t>(offset - atom_offset)};
    }
};

bool starts_atom(const AsmSymbol& symbol, bool elf, bool x86) {
    if (elf) {
        return false;
    }
    if (symbol.internal || symbol.name.empty() || symbol.name[0] == 'L') {
        return false;
    }
    return x86 || symbol.name[0] != 'l';
}

bool can_be_reloc_target(const AsmSymbol& symbol, bool elf) {
    if (symbol.internal || symbol.name.empty()) {
        return false;
    }
    return elf ? symbol.name.rfind(".L", 0) != 0 : symbol.name[0] != 'L';
}

bool resolves_in_place(const AsmSymbol& target, SymId target_id,
                       SymId target_atom, SymId fixup_atom, bool elf,
                       bool x86) {
    if (elf || target_id == fixup_atom) {
        return true;
    }
    if (x86) {
        return !can_be_reloc_target(target, elf) && target_atom == fixup_atom;
    }
    return !starts_atom(target, elf, x86);
}

}

void Assembler::expand_deferred_fields() {
    for (size_t section_index = 0; section_index < unit_.sections.size();
         ++section_index) {
        AsmSection& section = unit_.sections[section_index];
        if (section.deferred.empty()) {
            continue;
        }
        std::vector<DeferredField>& fields = section.deferred;
        std::vector<uint64_t> prefix(fields.size() + 1, 0);

        const bool elf_atoms = asm_target_is_elf(*options_.target);
        const bool x86_atoms = options_.target->arch == TargetArch::X86_64;
        auto position_key = [](uint64_t offset, uint32_t seq) {
            return std::pair<uint64_t, uint32_t>{offset, seq};
        };
        std::vector<std::pair<std::pair<uint64_t, uint32_t>, SymId>>
            raw_atoms;
        for (SymId id = 0; id < unit_.symbols.size(); ++id) {
            const AsmSymbol& symbol = unit_.symbols.sym(id);
            if (symbol.state != SymState::Label ||
                symbol.section != static_cast<int>(section_index) ||
                !starts_atom(symbol, elf_atoms, x86_atoms)) {
                continue;
            }
            raw_atoms.push_back(
                {position_key(symbol.offset, symbol.deferred_seq), id});
        }
        std::sort(raw_atoms.begin(), raw_atoms.end());
        auto enclosing_atom = [&](uint64_t offset, uint32_t seq) -> SymId {
            SymId atom = no_sym;
            for (const auto& [key, id] : raw_atoms) {
                if (key > position_key(offset, seq)) {
                    break;
                }
                atom = id;
            }
            return atom;
        };
        for (size_t i = 0; i < fields.size(); ++i) {
            DeferredField& field = fields[i];
            if (field.kind != DeferredKind::Branch) {
                continue;
            }
            const AsmSymbol& target = unit_.symbols.sym(field.pos_sym);
            bool same_section =
                target.state == SymState::Label &&
                target.section == static_cast<int>(section_index);
            field.branch.patchable =
                same_section &&
                resolves_in_place(
                    target, field.pos_sym,
                    enclosing_atom(target.offset, target.deferred_seq),
                    enclosing_atom(field.raw_offset,
                                   static_cast<uint32_t>(i)),
                    elf_atoms, x86_atoms);
            field.size = (field.branch.patchable &&
                          field.branch.short_opcode != 0)
                             ? 2
                             : field.branch.near_size;
        }

        auto recompute_prefix = [&]() {
            for (size_t i = 0; i < fields.size(); ++i) {
                prefix[i + 1] = prefix[i] + fields[i].size;
            }
        };
        auto symbol_final = [&](SymId id, int64_t& out,
                                int& out_section) -> bool {
            const AsmSymbol& symbol = unit_.symbols.sym(id);
            if (symbol.state == SymState::Constant) {
                out = symbol.value;
                out_section = -1;
                return true;
            }
            if (symbol.state != SymState::Label) {
                return false;
            }
            out_section = symbol.section;
            if (symbol.section == static_cast<int>(section_index)) {
                uint32_t seq = symbol.deferred_seq;
                if (seq > fields.size()) {
                    seq = static_cast<uint32_t>(fields.size());
                }
                out = static_cast<int64_t>(symbol.offset + prefix[seq]);
                return true;
            }
            const AsmSection& other =
                unit_.sections[static_cast<size_t>(symbol.section)];
            if (!other.deferred.empty()) {
                return false;
            }
            out = static_cast<int64_t>(symbol.offset);
            return true;
        };
        auto leb_value = [&](const DeferredField& field,
                             int64_t& out) -> bool {
            int64_t value = field.constant;
            int pos_section = -1;
            int neg_section = -1;
            if (field.pos_sym != no_sym) {
                int64_t position = 0;
                if (!symbol_final(field.pos_sym, position, pos_section)) {
                    return false;
                }
                value += position;
            }
            if (field.neg_sym != no_sym) {
                int64_t position = 0;
                if (!symbol_final(field.neg_sym, position, neg_section)) {
                    return false;
                }
                value -= position;
            }
            if (pos_section != neg_section) {
                return false;
            }
            out = value;
            return true;
        };
        auto leb_size = [](int64_t value, bool is_signed) -> uint32_t {
            uint32_t size = 0;
            if (is_signed) {
                bool more = true;
                while (more) {
                    uint8_t byte = static_cast<uint8_t>(value & 0x7F);
                    bool sign = (byte & 0x40) != 0;
                    value >>= 7;
                    more = !((value == 0 && !sign) ||
                             (value == -1 && sign));
                    ++size;
                }
                return size;
            }
            uint64_t bits = static_cast<uint64_t>(value);
            do {
                bits >>= 7;
                ++size;
            } while (bits != 0);
            return size;
        };

        bool resolved = true;
        bool converged = false;
        size_t iteration_limit = fields.size() * 2 + 8;
        for (size_t iteration = 0; iteration < iteration_limit; ++iteration) {
            recompute_prefix();
            bool changed = false;
            for (size_t i = 0; i < fields.size(); ++i) {
                DeferredField& field = fields[i];
                uint32_t new_size = field.size;
                if (field.kind == DeferredKind::Align) {
                    uint64_t position = field.raw_offset + prefix[i];
                    uint64_t alignment = 1ull << field.align_log2;
                    new_size = static_cast<uint32_t>(
                        (alignment - (position & (alignment - 1))) &
                        (alignment - 1));
                } else if (field.kind == DeferredKind::Branch) {
                    if (field.size >= field.branch.near_size) {
                        new_size = field.branch.near_size;
                    } else {
                        int64_t target = 0;
                        int target_section = -1;
                        if (!symbol_final(field.pos_sym, target,
                                          target_section)) {
                            new_size = field.branch.near_size;
                        } else {
                            int64_t here = static_cast<int64_t>(
                                field.raw_offset + prefix[i]);
                            int64_t delta =
                                target + field.constant - (here + 2);
                            new_size = (delta >= -128 && delta <= 127)
                                           ? 2
                                           : field.branch.near_size;
                        }
                    }
                } else {
                    int64_t value = 0;
                    if (!leb_value(field, value)) {
                        error(field.line, field.col,
                              "leb128 value does not resolve within its "
                              "section");
                        resolved = false;
                        new_size = 1;
                    } else {
                        new_size = leb_size(
                            value, field.kind == DeferredKind::Sleb);
                    }
                }
                if (new_size != field.size) {
                    field.size = new_size;
                    changed = true;
                }
            }
            if (!changed || !resolved) {
                converged = true;
                break;
            }
        }
        recompute_prefix();
        if (!resolved) {
            continue;
        }
        if (!converged) {
            error(fields.front().line, fields.front().col,
                  "variable-size data in this section did not converge to a "
                  "stable layout");
            continue;
        }

        std::vector<uint8_t> expanded;
        expanded.reserve(section.bytes.size() + prefix[fields.size()]);
        std::vector<RelocRecord> branch_relocs;
        std::vector<UnresolvedFixup> branch_unresolved;
        size_t raw_cursor = 0;
        for (size_t i = 0; i < fields.size(); ++i) {
            const DeferredField& field = fields[i];
            expanded.insert(expanded.end(),
                            section.bytes.begin() + raw_cursor,
                            section.bytes.begin() + field.raw_offset);
            raw_cursor = static_cast<size_t>(field.raw_offset);
            if (field.kind == DeferredKind::Align) {
                if (field.nop_fill) {
                    backend::x86::x86_append_nop_padding(expanded, field.size);
                } else {
                    expanded.insert(expanded.end(), field.size, field.fill);
                }
                continue;
            }
            if (field.kind == DeferredKind::Branch) {
                uint64_t here = field.raw_offset + prefix[i];
                if (field.branch.patchable) {
                    int64_t target = 0;
                    int target_section = -1;
                    symbol_final(field.pos_sym, target, target_section);
                    int64_t delta = target + field.constant -
                                    static_cast<int64_t>(here + field.size);
                    if (field.size == 2) {
                        expanded.push_back(field.branch.short_opcode);
                        expanded.push_back(static_cast<uint8_t>(delta));
                    } else {
                        expanded.insert(
                            expanded.end(), field.branch.near_bytes,
                            field.branch.near_bytes + field.branch.near_size);
                        size_t hole = expanded.size() -
                                      field.branch.near_size +
                                      field.branch.rel_offset;
                        for (int byte = 0; byte < 4; ++byte) {
                            expanded[hole + byte] = static_cast<uint8_t>(
                                static_cast<uint64_t>(delta) >> (8 * byte));
                        }
                    }
                    continue;
                }
                expanded.insert(
                    expanded.end(), field.branch.near_bytes,
                    field.branch.near_bytes + field.branch.near_size);
                size_t hole = expanded.size() - field.branch.near_size +
                              field.branch.rel_offset;
                for (int byte = 0; byte < 4; ++byte) {
                    expanded[hole + byte] = static_cast<uint8_t>(
                        static_cast<uint64_t>(field.constant) >> (8 * byte));
                }
                uint64_t field_offset = here + field.branch.rel_offset;
                const AsmSymbol& target = unit_.symbols.sym(field.pos_sym);
                if (options_.fragment_mode &&
                    target.state == SymState::Undefined) {
                    UnresolvedFixup out;
                    out.offset = field_offset;
                    out.kind = FixupKind::Branch32;
                    out.symbol = field.pos_sym;
                    out.addend = field.constant;
                    out.line = field.line;
                    out.col = field.col;
                    branch_unresolved.push_back(out);
                    continue;
                }
                if (target.state == SymState::Undefined && target.internal) {
                    error(field.line, field.col,
                          "undefined local label '" + target.name + "'");
                    continue;
                }
                if (target.state == SymState::Constant) {
                    error(field.line, field.col,
                          "branch target '" + target.name +
                              "' is not addressable by a relocation");
                    continue;
                }
                SymId reloc_symbol = field.pos_sym;
                if (target.state == SymState::Label &&
                    !can_be_reloc_target(target, elf_atoms)) {
                    SymId atom =
                        enclosing_atom(target.offset, target.deferred_seq);
                    int64_t label_position = 0;
                    int64_t atom_position = 0;
                    int ignored = -1;
                    if (atom == no_sym ||
                        !symbol_final(field.pos_sym, label_position,
                                      ignored) ||
                        !symbol_final(atom, atom_position, ignored)) {
                        error(field.line, field.col,
                              "branch target '" + target.name +
                                  "' has no addressable atom symbol");
                        continue;
                    }
                    reloc_symbol = atom;
                    int64_t addend =
                        field.constant + label_position - atom_position;
                    for (int byte = 0; byte < 4; ++byte) {
                        expanded[hole + byte] = static_cast<uint8_t>(
                            static_cast<uint64_t>(addend) >> (8 * byte));
                    }
                }
                RelocRecord reloc;
                reloc.offset = field_offset;
                reloc.kind = FixupKind::Branch32;
                reloc.reloc_kind = RelocKind::Branch32;
                reloc.symbol = reloc_symbol;
                branch_relocs.push_back(reloc);
                continue;
            }
            int64_t value = 0;
            leb_value(field, value);
            if (field.kind == DeferredKind::Sleb) {
                bool more = true;
                while (more) {
                    uint8_t byte = static_cast<uint8_t>(value & 0x7F);
                    bool sign = (byte & 0x40) != 0;
                    value >>= 7;
                    more = !((value == 0 && !sign) || (value == -1 && sign));
                    expanded.push_back(more ? (byte | 0x80) : byte);
                }
            } else {
                uint64_t bits = static_cast<uint64_t>(value);
                do {
                    uint8_t byte = static_cast<uint8_t>(bits & 0x7F);
                    bits >>= 7;
                    expanded.push_back(bits != 0 ? (byte | 0x80) : byte);
                } while (bits != 0);
            }
        }
        expanded.insert(expanded.end(), section.bytes.begin() + raw_cursor,
                        section.bytes.end());
        section.bytes = std::move(expanded);

        for (SymId id = 0; id < unit_.symbols.size(); ++id) {
            AsmSymbol& symbol = unit_.symbols.sym(id);
            if (symbol.state == SymState::Label &&
                symbol.section == static_cast<int>(section_index)) {
                uint32_t seq = symbol.deferred_seq;
                if (seq > fields.size()) {
                    seq = static_cast<uint32_t>(fields.size());
                }
                symbol.offset += prefix[seq];
            }
        }
        for (PendingFixup& fixup : section.fixups) {
            uint32_t seq = fixup.deferred_seq;
            if (seq > fields.size()) {
                seq = static_cast<uint32_t>(fields.size());
            }
            fixup.offset += prefix[seq];
        }
        for (RelocRecord& reloc : branch_relocs) {
            section.relocs.push_back(reloc);
        }
        for (UnresolvedFixup& fixup : branch_unresolved) {
            section.unresolved.push_back(fixup);
        }
        fields.clear();
    }
}

void Assembler::finalize_fixups() {
    expand_deferred_fields();
    const bool elf = asm_target_is_elf(*options_.target);
    const bool x86 = options_.target->arch == TargetArch::X86_64;
    AtomMap atoms;
    atoms.starts.resize(unit_.sections.size());
    for (SymId id = 0; id < unit_.symbols.size(); ++id) {
        const AsmSymbol& symbol = unit_.symbols.sym(id);
        if (symbol.state != SymState::Label ||
            !starts_atom(symbol, elf, x86)) {
            continue;
        }
        atoms.starts[static_cast<size_t>(symbol.section)].push_back(
            {symbol.offset, id});
    }
    for (auto& section_atoms : atoms.starts) {
        std::sort(section_atoms.begin(), section_atoms.end());
    }
    auto resolve = [&](SymId id, const PendingFixup& fixup) -> ResolvedSym {
        ResolvedSym resolved;
        const AsmSymbol& symbol = unit_.symbols.sym(id);
        switch (symbol.state) {
            case SymState::Constant:
                resolved.kind = ResolvedSym::Kind::Absolute;
                resolved.value = symbol.value;
                return resolved;
            case SymState::Label:
                resolved.kind = ResolvedSym::Kind::InSection;
                resolved.section = symbol.section;
                resolved.offset = symbol.offset;
                return resolved;
            case SymState::Undefined:
                if (symbol.internal) {
                    error(fixup.line, fixup.col,
                          "undefined local label '" + symbol.name + "'");
                    resolved.kind = ResolvedSym::Kind::Failed;
                    return resolved;
                }
                resolved.kind = ResolvedSym::Kind::External;
                return resolved;
        }
        resolved.kind = ResolvedSym::Kind::Failed;
        return resolved;
    };

    auto read_inst_word = [](const AsmSection& section, uint64_t offset) {
        uint32_t word = 0;
        for (int i = 0; i < 4; ++i) {
            word |= static_cast<uint32_t>(section.bytes[offset + i])
                    << (8 * i);
        }
        return word;
    };
    auto write_inst_word = [](AsmSection& section, uint64_t offset,
                              uint32_t word) {
        for (int i = 0; i < 4; ++i) {
            section.bytes[offset + i] =
                static_cast<uint8_t>(word >> (8 * i));
        }
    };

    for (size_t section_index = 0; section_index < unit_.sections.size();
         ++section_index) {
        AsmSection& section = unit_.sections[section_index];
        for (const PendingFixup& fixup : section.fixups) {
            if (fixup.kind == FixupKind::GotDelta32) {
                ResolvedSym neg = resolve(fixup.neg_sym, fixup);
                if (neg.kind == ResolvedSym::Kind::Failed) {
                    continue;
                }
                if (neg.kind != ResolvedSym::Kind::InSection ||
                    neg.section != static_cast<int>(section_index)) {
                    error(fixup.line, fixup.col,
                          "'@GOT - label' requires a label in the same "
                          "section");
                    continue;
                }
                uint32_t hole =
                    0u - static_cast<uint32_t>(neg.offset);
                for (int i = 0; i < 4; ++i) {
                    section.bytes[fixup.offset + i] =
                        static_cast<uint8_t>(hole >> (8 * i));
                }
                RelocRecord reloc;
                reloc.offset = fixup.offset;
                reloc.kind = fixup.kind;
                reloc.reloc_kind = RelocKind::PointerToGot;
                reloc.symbol = fixup.pos_sym;
                section.relocs.push_back(reloc);
                continue;
            }
            if (fixup.kind == FixupKind::PcRel32 ||
                fixup.kind == FixupKind::Branch32) {
                if (options_.fragment_mode && fixup.pos_sym != no_sym &&
                    unit_.symbols.sym(fixup.pos_sym).state ==
                        SymState::Undefined) {
                    UnresolvedFixup out;
                    out.offset = fixup.offset;
                    out.kind = fixup.kind;
                    out.symbol = fixup.pos_sym;
                    out.addend = fixup.constant;
                    out.flavor = fixup.flavor;
                    out.pcrel_extra = fixup.pcrel_extra;
                    out.line = fixup.line;
                    out.col = fixup.col;
                    section.unresolved.push_back(out);
                    continue;
                }
                ResolvedSym pos = resolve(fixup.pos_sym, fixup);
                if (pos.kind == ResolvedSym::Kind::Failed) {
                    continue;
                }
                if (pos.kind == ResolvedSym::Kind::Absolute) {
                    error(fixup.line, fixup.col,
                          "instruction target must be a label or symbol");
                    continue;
                }
                bool indirect_flavor =
                    fixup.flavor == backend::SymFlavor::GotPcRel ||
                    fixup.flavor == backend::SymFlavor::TlvPcRel;
                if (!indirect_flavor &&
                    pos.kind == ResolvedSym::Kind::InSection &&
                    pos.section == static_cast<int>(section_index)) {
                    const AsmSymbol& target =
                        unit_.symbols.sym(fixup.pos_sym);
                    bool patchable = resolves_in_place(
                        target, fixup.pos_sym,
                        atoms.atom_at(pos.section, pos.offset).first,
                        atoms.atom_at(static_cast<int>(section_index),
                                      fixup.offset)
                            .first,
                        elf, x86);
                    if (patchable) {
                        int64_t delta =
                            static_cast<int64_t>(pos.offset) +
                            fixup.constant -
                            static_cast<int64_t>(fixup.offset + 4 +
                                                 fixup.pcrel_extra);
                        uint64_t bits = static_cast<uint64_t>(delta);
                        for (int byte = 0; byte < 4; ++byte) {
                            section.bytes[fixup.offset + byte] =
                                static_cast<uint8_t>(bits >> (8 * byte));
                        }
                        continue;
                    }
                }
                RelocRecord reloc;
                reloc.offset = fixup.offset;
                reloc.kind = fixup.kind;
                reloc.flavor = fixup.flavor;
                reloc.pcrel_extra = fixup.pcrel_extra;
                reloc.reloc_kind = fixup.kind == FixupKind::Branch32
                                       ? RelocKind::Branch32
                                       : RelocKind::PcRel32;
                int64_t hole = fixup.constant - fixup.pcrel_extra;
                if (pos.kind == ResolvedSym::Kind::External) {
                    reloc.symbol = fixup.pos_sym;
                } else {
                    const AsmSymbol& target =
                        unit_.symbols.sym(fixup.pos_sym);
                    if (can_be_reloc_target(target, elf)) {
                        reloc.symbol = fixup.pos_sym;
                    } else {
                        auto [target_atom, target_delta] =
                            atoms.atom_at(pos.section, pos.offset);
                        if (target_atom != no_sym) {
                            reloc.symbol = target_atom;
                            hole += target_delta;
                        } else {
                            reloc.section = pos.section;
                            hole += static_cast<int64_t>(pos.offset) -
                                    static_cast<int64_t>(fixup.offset + 4 +
                                                         fixup.pcrel_extra);
                        }
                    }
                }
                uint64_t bits = static_cast<uint64_t>(hole);
                for (int byte = 0; byte < 4; ++byte) {
                    section.bytes[fixup.offset + byte] =
                        static_cast<uint8_t>(bits >> (8 * byte));
                }
                section.relocs.push_back(reloc);
                continue;
            }
            if (!fixup_is_data(fixup.kind)) {
                if (options_.fragment_mode && fixup.pos_sym != no_sym &&
                    unit_.symbols.sym(fixup.pos_sym).state ==
                        SymState::Undefined) {
                    UnresolvedFixup out;
                    out.offset = fixup.offset;
                    out.kind = fixup.kind;
                    out.symbol = fixup.pos_sym;
                    out.addend = fixup.constant;
                    out.flavor = fixup.flavor;
                    out.access_bytes = fixup.access_bytes;
                    out.line = fixup.line;
                    out.col = fixup.col;
                    section.unresolved.push_back(out);
                    continue;
                }
                ResolvedSym pos = resolve(fixup.pos_sym, fixup);
                if (pos.kind == ResolvedSym::Kind::Failed) {
                    continue;
                }
                if (pos.kind == ResolvedSym::Kind::Absolute) {
                    error(fixup.line, fixup.col,
                          "instruction target must be a label or symbol");
                    continue;
                }
                if (fixup.constant != 0) {
                    error(fixup.line, fixup.col,
                          "addends on instruction relocations are not "
                          "supported yet");
                    continue;
                }
                bool is_branch = fixup.kind == FixupKind::Branch26 ||
                                 fixup.kind == FixupKind::Branch19;
                if (is_branch &&
                    pos.kind == ResolvedSym::Kind::InSection &&
                    pos.section == static_cast<int>(section_index)) {
                    const AsmSymbol& target =
                        unit_.symbols.sym(fixup.pos_sym);
                    bool patchable = resolves_in_place(
                        target, fixup.pos_sym,
                        atoms.atom_at(pos.section, pos.offset).first,
                        atoms.atom_at(static_cast<int>(section_index),
                                      fixup.offset)
                            .first,
                        elf, x86);
                    if (patchable) {
                        int64_t delta = static_cast<int64_t>(pos.offset) -
                                        static_cast<int64_t>(fixup.offset);
                        uint32_t word = read_inst_word(section, fixup.offset);
                        word = fixup.kind == FixupKind::Branch26
                                   ? backend::aarch64::patch_branch26(word,
                                                                      delta)
                                   : backend::aarch64::patch_branch19(word,
                                                                      delta);
                        write_inst_word(section, fixup.offset, word);
                        continue;
                    }
                }
                if (fixup.kind == FixupKind::Branch19) {
                    error(fixup.line, fixup.col,
                          "conditional branch target is outside the "
                          "instruction's atom");
                    continue;
                }
                RelocRecord reloc;
                reloc.offset = fixup.offset;
                reloc.kind = fixup.kind;
                reloc.flavor = fixup.flavor;
                reloc.access_bytes = fixup.access_bytes;
                reloc.reloc_kind =
                    fixup.kind == FixupKind::Branch26 ? RelocKind::Branch26
                    : fixup.kind == FixupKind::Page21 ? RelocKind::Page21
                                                      : RelocKind::PageOff12;
                if (pos.kind == ResolvedSym::Kind::External) {
                    reloc.symbol = fixup.pos_sym;
                } else {
                    const AsmSymbol& target =
                        unit_.symbols.sym(fixup.pos_sym);
                    if (can_be_reloc_target(target, elf)) {
                        reloc.symbol = fixup.pos_sym;
                    } else {
                        auto [target_atom, target_delta] =
                            atoms.atom_at(pos.section, pos.offset);
                        if (target_atom == no_sym || target_delta != 0) {
                            error(fixup.line, fixup.col,
                                  "instruction target has no addressable "
                                  "atom symbol");
                            continue;
                        }
                        reloc.symbol = target_atom;
                    }
                }
                section.relocs.push_back(reloc);
                continue;
            }
            if (options_.fragment_mode && fixup.neg_sym == no_sym &&
                fixup.pos_sym != no_sym &&
                unit_.symbols.sym(fixup.pos_sym).state ==
                    SymState::Undefined) {
                UnresolvedFixup out;
                out.offset = fixup.offset;
                out.kind = fixup.kind;
                out.symbol = fixup.pos_sym;
                out.addend = fixup.constant;
                out.flavor = fixup.flavor;
                out.line = fixup.line;
                out.col = fixup.col;
                section.unresolved.push_back(out);
                continue;
            }
            int64_t constant = fixup.constant;
            ResolvedSym pos;
            pos.kind = ResolvedSym::Kind::Absolute;
            if (fixup.pos_sym != no_sym) {
                pos = resolve(fixup.pos_sym, fixup);
                if (pos.kind == ResolvedSym::Kind::Failed) {
                    continue;
                }
                if (pos.kind == ResolvedSym::Kind::Absolute) {
                    constant += pos.value;
                }
            }

            SymId subtractor_atom = no_sym;
            if (fixup.neg_sym != no_sym) {
                ResolvedSym neg = resolve(fixup.neg_sym, fixup);
                if (neg.kind == ResolvedSym::Kind::Failed) {
                    continue;
                }
                if (neg.kind == ResolvedSym::Kind::Absolute) {
                    constant -= neg.value;
                } else if (neg.kind != ResolvedSym::Kind::InSection ||
                           pos.kind == ResolvedSym::Kind::Absolute) {
                    error(fixup.line, fixup.col,
                          "expression subtracts a symbol that is not "
                          "defined in this unit");
                    continue;
                } else {
                    auto [neg_atom, neg_delta] =
                        atoms.atom_at(neg.section, neg.offset);
                    if (pos.kind == ResolvedSym::Kind::InSection) {
                        auto [pos_atom, pos_delta] =
                            atoms.atom_at(pos.section, pos.offset);
                        if (pos.section == neg.section &&
                            pos_atom == neg_atom) {
                            constant += static_cast<int64_t>(pos.offset) -
                                        static_cast<int64_t>(neg.offset);
                            pos.kind = ResolvedSym::Kind::Absolute;
                        } else if (neg_atom == no_sym) {
                            error(fixup.line, fixup.col,
                                  "cannot subtract a symbol that has no "
                                  "enclosing atom symbol");
                            continue;
                        } else {
                            subtractor_atom = neg_atom;
                            constant -= neg_delta;
                        }
                    } else {
                        if (neg_atom == no_sym) {
                            error(fixup.line, fixup.col,
                                  "cannot subtract a symbol that has no "
                                  "enclosing atom symbol");
                            continue;
                        }
                        subtractor_atom = neg_atom;
                        constant -= neg_delta;
                    }
                }
            }

            if (pos.kind == ResolvedSym::Kind::Absolute) {
                patch_absolute(section, fixup, constant);
                continue;
            }

            uint32_t width = fixup_width_bytes(fixup.kind);
            if (width < 4) {
                error(fixup.line, fixup.col,
                      "cannot emit a " + std::to_string(width) +
                          "-byte relocation");
                continue;
            }

            RelocRecord reloc;
            reloc.offset = fixup.offset;
            reloc.kind = fixup.kind;
            if (pos.kind == ResolvedSym::Kind::External) {
                reloc.symbol = fixup.pos_sym;
            } else {
                const AsmSymbol& symbol = unit_.symbols.sym(fixup.pos_sym);
                if (can_be_reloc_target(symbol, elf)) {
                    reloc.symbol = fixup.pos_sym;
                } else {
                    auto [pos_atom, pos_delta] =
                        atoms.atom_at(pos.section, pos.offset);
                    if (pos_atom != no_sym) {
                        reloc.symbol = pos_atom;
                        constant += pos_delta;
                    } else if (subtractor_atom != no_sym) {
                        error(fixup.line, fixup.col,
                              "difference target has no enclosing atom "
                              "symbol");
                        continue;
                    } else {
                        reloc.section = pos.section;
                        constant += static_cast<int64_t>(pos.offset);
                    }
                }
            }
            if (!patch_absolute(section, fixup, constant)) {
                continue;
            }
            if (subtractor_atom != no_sym) {
                RelocRecord subtractor;
                subtractor.offset = fixup.offset;
                subtractor.kind = fixup.kind;
                subtractor.reloc_kind = RelocKind::Subtractor;
                subtractor.symbol = subtractor_atom;
                section.relocs.push_back(subtractor);
            }
            section.relocs.push_back(reloc);
        }
        section.fixups.clear();
    }

    for (const auto& [number, state] : local_labels_) {
        for (SymId pending : state.pending_forward) {
            const AsmSymbol& symbol = unit_.symbols.sym(pending);
            if (symbol.state == SymState::Undefined) {
                Diagnostic diag;
                diag.level = DiagnosticLevel::Error;
                diag.message = options_.filename +
                               ": undefined local label '" +
                               std::to_string(number) + "f'";
                diagnostics_.push_back(std::move(diag));
                ++error_count_;
                break;
            }
        }
    }
}

bool Assembler::patch_absolute(AsmSection& section, const PendingFixup& fixup,
                               int64_t value) {
    uint32_t width = fixup_width_bytes(fixup.kind);
    if (!fits_width(value, width)) {
        error(fixup.line, fixup.col,
              "value " + std::to_string(value) +
                  " is out of range for a " + std::to_string(width) +
                  "-byte field");
        return false;
    }
    uint64_t bits = static_cast<uint64_t>(value);
    for (uint32_t i = 0; i < width; ++i) {
        section.bytes[fixup.offset + i] =
            static_cast<uint8_t>(bits >> (8 * i));
    }
    return true;
}

void Assembler::error(uint32_t line, uint32_t col,
                      const std::string& message) {
    Diagnostic diag;
    diag.level = DiagnosticLevel::Error;
    diag.message = options_.filename + ":" + std::to_string(line) + ":" +
                   std::to_string(col) + ": " + message;
    diagnostics_.push_back(std::move(diag));
    ++error_count_;
}

void Assembler::error(const Token& at, const std::string& message) {
    error(at.line, at.col, message);
}

}
