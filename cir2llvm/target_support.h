#ifndef ABURI_CIR2LLVM_TARGET_SUPPORT_H
#define ABURI_CIR2LLVM_TARGET_SUPPORT_H

#include <memory>
#include <string>
#include <vector>

#include <llvm/Support/CodeGen.h>
#include <llvm/Target/TargetMachine.h>

#include "../abi/target_info.h"
#include "../diagnostics.h"

namespace llvm {
class Module;
}

namespace aburi::cir2llvm {

struct TargetMachineOptions {
    std::string cpu = "generic";
    std::string features;
    bool pic = true;
    llvm::CodeGenOptLevel opt_level = llvm::CodeGenOptLevel::None;
    bool disable_integrated_as = false;
};

void initialize_codegen_targets();

std::string effective_triple(const TargetInfo& target);

std::unique_ptr<llvm::TargetMachine> create_target_machine(
    const TargetInfo& target,
    const TargetMachineOptions& options,
    std::vector<Diagnostic>& diagnostics);

bool configure_module_target(llvm::Module& module,
                             const TargetInfo& target,
                             const TargetMachineOptions& options,
                             std::vector<Diagnostic>& diagnostics);

bool is_native_jit_target(const TargetInfo& target);

} // namespace aburi::cir2llvm

#endif // ABURI_CIR2LLVM_TARGET_SUPPORT_H
