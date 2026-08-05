#ifndef ABURI_BACKEND_X86_ELF_EMIT_H
#define ABURI_BACKEND_X86_ELF_EMIT_H

#include <cstdint>
#include <map>
#include <ostream>
#include <string>
#include <vector>

#include "../../diagnostics.h"
#include "../common/elf.h"
#include "../common/emitter.h"

namespace aburi::backend::x86 {

class ElfEmitter : public ModuleEmitter {
public:
    explicit ElfEmitter(std::vector<Diagnostic>& diagnostics,
                        bool emit_unwind_tables = false,
                        bool legacy32 = false);

    void begin_module(const air::Module& module) override;
    void emit_module_asm(const std::string& text) override;
    void emit_global(const air::Module& module,
                     const air::GlobalData& global) override;
    void begin_function(const MFunction& function) override;
    void emit_block_label(const MFunction& function,
                          uint32_t block_index) override;
    void emit_inst(const MFunction& function, const MInst& inst) override;
    void end_function(const MFunction& function) override;
    void emit_ctor_list(const air::Module& module) override;
    void end_module(const air::Module& module) override;

    bool write(std::ostream& out);

private:
    struct PendingLabelFixup {
        uint64_t field_offset = 0;
        uint32_t target_block = 0;
    };
    struct PendingSymBranch {
        uint64_t field_offset = 0;
        std::string symbol;
    };

    void error(const std::string& message);
    int text_section();
    int section_for_global(const air::GlobalData& global, bool has_relocs);

    std::vector<Diagnostic>& diagnostics_;
    ElfBuilder builder_;
    std::map<std::string, int> section_ids_;
    bool emit_unwind_tables_ = false;

    std::string current_function_symbol_;
    uint64_t current_function_start_ = 0;
    size_t current_function_symbol_index_ = 0;
    std::map<std::string, uint64_t> local_text_offsets_;
    std::map<uint32_t, uint64_t> block_offsets_;
    std::vector<PendingLabelFixup> pending_labels_;
    std::vector<PendingSymBranch> pending_sym_branches_;
};

} // namespace aburi::backend::x86

#endif // ABURI_BACKEND_X86_ELF_EMIT_H
