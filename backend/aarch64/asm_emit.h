#ifndef ABURI_BACKEND_AARCH64_ASM_EMIT_H
#define ABURI_BACKEND_AARCH64_ASM_EMIT_H

#include <ostream>
#include <set>
#include <string>
#include <vector>

#include "../../diagnostics.h"
#include "../common/emitter.h"

namespace aburi::backend::aarch64 {

class AsmTextEmitter final : public ModuleEmitter {
public:
    explicit AsmTextEmitter(std::ostream& out,
                            bool emit_unwind_tables = false,
                            ObjectFormat format = ObjectFormat::MachO,
                            std::vector<Diagnostic>* diagnostics = nullptr)
        : out_(out), emit_unwind_tables_(emit_unwind_tables),
          elf_(format == ObjectFormat::Elf), diagnostics_(diagnostics) {}

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

private:
    void emit_symbol_visibility(const std::string& symbol, air::Linkage linkage,
                                const air::SymbolAttrs& attrs);
    void emit_lsda(const MFunction& function);
    std::string object_symbol(const std::string& name, bool no_prefix) const;
    std::string symbol_ref(const MOperand& operand) const;
    std::string local_label(const std::string& stem) const;
    std::string block_label(const MFunction& function,
                            uint32_t block_index) const;
    std::string eh_label(const MFunction& function, uint32_t label) const;
    std::string func_begin_label(const MFunction& function) const;
    std::string func_end_label(const MFunction& function) const;
    std::string exception_label(const MFunction& function) const;
    std::string action_base_label(const MFunction& function) const;
    std::string action_next_label(const MFunction& function,
                                  uint32_t label) const;
    std::string typeinfo_entry_label(const MFunction& function,
                                     uint32_t filter) const;

    std::ostream& out_;
    bool emit_unwind_tables_ = false;
    bool elf_ = false;
    std::vector<Diagnostic>* diagnostics_ = nullptr;
    bool in_text_section_ = false;
    bool in_function_ = false;
    bool cfi_frame_emitted_ = false;
    bool current_function_has_lsda_ = false;
    std::set<std::string> dw_refs_;
};

} // namespace aburi::backend::aarch64

#endif // ABURI_BACKEND_AARCH64_ASM_EMIT_H
