#ifndef ABURI_ASSEMBLER_ASSEMBLER_H
#define ABURI_ASSEMBLER_ASSEMBLER_H

#include <cstdint>
#include <ostream>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "../diagnostics.h"
#include "asm_options.h"
#include "expr.h"
#include "lexer.h"
#include "symbols.h"
#include "unit.h"

namespace aburi::assembler {

struct AssembleResult {
    std::vector<Diagnostic> diagnostics;
    bool ok = false;
};

AssembleResult assemble_string_to_object(std::string_view source,
                                         const AsmOptions& options,
                                         std::ostream& object_out);

class Assembler final : public ExprContext {
public:
    Assembler(std::string_view source, const AsmOptions& options);

    bool run();

    AsmUnit& unit() { return unit_; }
    std::vector<Diagnostic>& diagnostics() { return diagnostics_; }

    SymId expr_symbol(std::string_view name) override;
    SymId expr_here() override;
    SymId expr_local_ref(uint32_t number, bool backward, uint32_t line,
                         uint32_t col) override;
    bool expr_constant_value(SymId id, int64_t& out) const override;
    void expr_error(uint32_t line, uint32_t col,
                    const std::string& message) override;

    void append_inst_word(uint32_t word, const Token& at);
    void append_inst_fixup(uint32_t word, FixupKind kind, SymId sym,
                           int64_t addend, backend::SymFlavor flavor,
                           uint8_t access_bytes, const Token& at);
    void append_inst_bytes(const uint8_t* bytes, size_t size, const Token& at);
    void append_inst_bytes_fixup(const uint8_t* bytes, size_t size,
                                 FixupKind kind, size_t field_offset,
                                 SymId sym, int64_t addend,
                                 backend::SymFlavor flavor,
                                 uint8_t pcrel_extra, const Token& at);
    void append_branch(const uint8_t* near_bytes, size_t near_size,
                       size_t rel_offset, uint8_t short_opcode, SymId target,
                       int64_t addend, const Token& at);

private:
    using DirectiveHandler = void (Assembler::*)(const Token& directive);

    static DirectiveHandler find_directive(std::string_view name);

    void parse_statement();
    void define_label(const Token& name);
    void define_local_label(const Token& number);
    void handle_assignment(const Token& name);

    void dir_section(const Token& directive);
    void dir_builtin_section(const Token& directive);
    void dir_symbol_binding(const Token& directive);
    void dir_align(const Token& directive);
    void dir_data_value(const Token& directive);
    void dir_ascii(const Token& directive);
    void dir_space(const Token& directive);
    void dir_comm(const Token& directive);
    void dir_zerofill(const Token& directive);
    void dir_set(const Token& directive);
    void dir_org(const Token& directive);
    void dir_leb(const Token& directive);
    void dir_ignore_line(const Token& directive);
    void dir_unsupported_yet(const Token& directive);

    int find_or_add_section(std::string_view segname, std::string_view sectname,
                            uint32_t flags, bool zerofill);
    AsmSection& cur();
    void set_current_section(int id) { current_section_ = id; }
    void align_current(uint32_t align_log2, uint8_t fill, bool fill_given,
                       int64_t max_bytes, const Token& at);

    void append_bytes(const uint8_t* data, size_t size);
    void append_data_value(FixupKind kind, const ExprValue& value,
                           const Token& at);
    void append_space(uint64_t size, uint8_t fill, const Token& at);
    bool check_not_zerofill(const Token& at);

    bool expect_statement_end();
    bool take_comma();
    bool parse_absolute(int64_t& out, const Token& at,
                        const char* what_for);

    void bind_symbol_to_location(SymId id, const Token& at);
    void apply_set(SymId id, const ExprValue& value, const Token& at);

    void expand_deferred_fields();
    void finalize_fixups();
    bool patch_absolute(AsmSection& section, const PendingFixup& fixup,
                        int64_t value);

    void error(uint32_t line, uint32_t col, const std::string& message);
    void error(const Token& at, const std::string& message);

    Lexer lexer_;
    AsmOptions options_;
    AsmUnit unit_;
    std::vector<Diagnostic> diagnostics_;
    size_t error_count_ = 0;
    int current_section_ = -1;

    struct LocalLabelState {
        SymId last_def = no_sym;
        std::vector<SymId> pending_forward;
    };
    std::unordered_map<uint32_t, LocalLabelState> local_labels_;
};

}

#endif
