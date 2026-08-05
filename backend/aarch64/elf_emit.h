#ifndef ABURI_BACKEND_AARCH64_ELF_EMIT_H
#define ABURI_BACKEND_AARCH64_ELF_EMIT_H

#include <cstdint>
#include <map>
#include <ostream>
#include <set>
#include <string>
#include <vector>

#include "../../diagnostics.h"
#include "../common/elf.h"
#include "../../assembler/fragment.h"
#include "../common/emitter.h"

namespace aburi::backend::aarch64 {

class ElfEmitter : public ModuleEmitter {
public:
    explicit ElfEmitter(std::vector<Diagnostic>& diagnostics,
                        bool emit_unwind_tables = false);

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
        uint64_t word_offset = 0;
        bool branch26 = false;
        uint32_t target_block = 0;
    };
    struct PendingSymBranch {
        uint64_t word_offset = 0;
        std::string symbol;
    };

    void error(const std::string& message);
    int text_section();
    int section_for_global(const air::GlobalData& global, bool has_relocs);
    void splice_asm_fragment(const std::string& text, bool inside_function);
    int eh_frame_section();
    int gcc_except_section();
    std::string dw_ref_symbol(const std::string& symbol);
    uint64_t emit_lsda(const MFunction& function, uint64_t function_end);
    void emit_eh_frame_entry(const MFunction& function, uint64_t function_end,
                             uint64_t lsda_offset, bool has_lsda);

    std::vector<Diagnostic>& diagnostics_;
    std::shared_ptr<const TargetInfo> target_;
    ElfBuilder builder_;
    std::map<std::string, int> section_ids_;
    bool emit_unwind_tables_ = false;

    std::string current_function_symbol_;
    uint64_t current_function_start_ = 0;
    uint64_t frame_setup_offset_ = 0;
    bool has_frame_setup_ = false;
    std::map<uint32_t, uint64_t> eh_label_offsets_;
    std::set<std::string> dw_refs_;
    bool eh_frame_started_ = false;
    uint64_t cie_offset_ = 0;
    size_t current_function_symbol_index_ = 0;
    std::map<uint32_t, uint64_t> block_offsets_;
    std::vector<PendingLabelFixup> pending_labels_;
    std::vector<PendingSymBranch> pending_sym_branches_;
    std::map<std::string, uint64_t> local_text_offsets_;
};

} // namespace aburi::backend::aarch64

#endif // ABURI_BACKEND_AARCH64_ELF_EMIT_H
