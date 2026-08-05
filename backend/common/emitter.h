#ifndef ABURI_BACKEND_COMMON_EMITTER_H
#define ABURI_BACKEND_COMMON_EMITTER_H

#include "mir.h"

#include "../../air/module.h"

namespace aburi::backend {

enum class ObjectFormat {
    MachO,
    Elf,
};

inline ObjectFormat object_format_for(const TargetInfo& target) {
    return target.os == TargetOS::MACOS ? ObjectFormat::MachO
                                        : ObjectFormat::Elf;
}

class ModuleEmitter {
public:
    virtual ~ModuleEmitter() = default;

    virtual void begin_module(const air::Module& module) = 0;
    virtual void emit_module_asm(const std::string& text) = 0;
    virtual void emit_global(const air::Module& module,
                             const air::GlobalData& global) = 0;
    virtual void begin_function(const MFunction& function) = 0;
    virtual void emit_block_label(const MFunction& function,
                                  uint32_t block_index) = 0;
    virtual void emit_inst(const MFunction& function, const MInst& inst) = 0;
    virtual void end_function(const MFunction& function) = 0;
    virtual void emit_ctor_list(const air::Module& module) = 0;
    virtual void end_module(const air::Module& module) = 0;
};

} // namespace aburi::backend

#endif // ABURI_BACKEND_COMMON_EMITTER_H
