#ifndef ABURI_BACKEND_OR1K_ASM_EMIT_H
#define ABURI_BACKEND_OR1K_ASM_EMIT_H

#include <ostream>
#include <set>
#include <string>
#include <vector>

#include "../../diagnostics.h"
#include "../common/emitter.h"

namespace aburi::backend::or1k {

class AsmTextEmitter final : public ModuleEmitter {
public:
    explicit AsmTextEmitter(std::ostream& out,
                            bool emit_unwind_tables = false,
                            std::vector<Diagnostic>* diagnostics = nullptr)
        : out_(out), emit_unwind_tables_(emit_unwind_tables),
          diagnostics_(diagnostics) {}

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
    std::string block_label(const MFunction& function,
                            uint32_t block_index) const;
    void emit_set_bool(const MInst& inst);
    void emit_frame_cfi(const MFunction& function);
    void emit_lsda(const MFunction& function);
    std::string func_begin_label(const MFunction& function) const;
    std::string func_end_label(const MFunction& function) const;
    std::string exception_label(const MFunction& function) const;
    std::string eh_label(const MFunction& function, uint32_t label) const;
    std::string action_base_label(const MFunction& function) const;
    std::string action_next_label(const MFunction& function,
                                  uint32_t label) const;
    std::string typeinfo_entry_label(const MFunction& function,
                                     uint32_t filter) const;

    std::ostream& out_;
    bool emit_unwind_tables_ = false;
    std::vector<Diagnostic>* diagnostics_ = nullptr;
    bool in_text_section_ = false;
    bool in_function_ = false;
    bool cfi_frame_emitted_ = false;
    bool current_function_has_lsda_ = false;
    uint32_t local_counter_ = 0;
    std::set<std::string> dw_refs_;
};

} // namespace aburi::backend::or1k

#endif // ABURI_BACKEND_OR1K_ASM_EMIT_H
