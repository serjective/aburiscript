#ifndef ABURI_BACKEND_AARCH64_MACHO_EMIT_H
#define ABURI_BACKEND_AARCH64_MACHO_EMIT_H

#include <cstdint>
#include <map>
#include <ostream>
#include <string>
#include <vector>

#include "../../diagnostics.h"
#include "../../assembler/fragment.h"
#include "../common/emitter.h"
#include "../common/macho.h"

namespace aburi::backend::aarch64 {

class MachOEmitter : public ModuleEmitter {
public:
    explicit MachOEmitter(std::vector<Diagnostic>& diagnostics,
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
    struct PendingCompactUnwindRow {
        uint64_t function_start = 0;
        uint64_t function_end = 0;
        uint64_t lsda_offset = 0;
        uint32_t encoding = 0;
        bool has_lsda = false;
    };

    void error(const std::string& message);
    int text_section();
    int gcc_except_section();
    int compact_unwind_section();
    int section_for_global(const air::GlobalData& global, bool has_relocs);
    uint64_t emit_lsda(const MFunction& function, uint64_t function_end);
    void queue_compact_unwind(const MFunction& function, uint64_t function_end,
                              uint64_t lsda_offset, bool has_lsda);
    void emit_pending_compact_unwind();
    void splice_asm_fragment(const std::string& text, bool inside_function);

    std::vector<Diagnostic>& diagnostics_;
    MachOBuilder builder_;
    std::shared_ptr<const TargetInfo> target_;
    std::map<std::string, int> section_ids_;
    bool emit_unwind_tables_ = false;
    std::string current_function_symbol_;
    uint64_t current_function_start_ = 0;
    std::vector<uint64_t> self_call_offsets_;
    std::map<uint32_t, uint64_t> block_offsets_;
    std::map<uint32_t, uint64_t> eh_label_offsets_;
    std::vector<PendingLabelFixup> pending_labels_;
    std::vector<PendingCompactUnwindRow> compact_unwind_rows_;
};

} // namespace aburi::backend::aarch64

#endif // ABURI_BACKEND_AARCH64_MACHO_EMIT_H
