#include "target_support.h"

#include <optional>
#include <string>
#include <utility>

#include <llvm/IR/Module.h>
#include <llvm/MC/TargetRegistry.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Target/TargetOptions.h>
#include <llvm/TargetParser/Host.h>
#include <llvm/TargetParser/Triple.h>

namespace aburi::cir2llvm {
namespace {

void add_error(std::vector<Diagnostic>& diagnostics, std::string message) {
    Diagnostic diag;
    diag.level = DiagnosticLevel::Error;
    diag.message = "cir2llvm: " + std::move(message);
    diagnostics.push_back(std::move(diag));
}

llvm::Reloc::Model relocation_model(const TargetMachineOptions& options) {
    return options.pic ? llvm::Reloc::PIC_ : llvm::Reloc::Static;
}

} // namespace

void initialize_codegen_targets() {
    static const bool initialized = [] {
        llvm::InitializeNativeTarget();
        llvm::InitializeNativeTargetAsmPrinter();
        llvm::InitializeNativeTargetAsmParser();

        LLVMInitializeAArch64TargetInfo();
        LLVMInitializeAArch64Target();
        LLVMInitializeAArch64TargetMC();
        LLVMInitializeAArch64AsmPrinter();
        LLVMInitializeAArch64AsmParser();
        return true;
    }();
    (void)initialized;
}

std::string effective_triple(const TargetInfo& target) {
    if (!target.triple.empty()) {
        return target.triple;
    }
    return llvm::sys::getDefaultTargetTriple();
}

std::unique_ptr<llvm::TargetMachine> create_target_machine(
    const TargetInfo& target,
    const TargetMachineOptions& options,
    std::vector<Diagnostic>& diagnostics) {
    initialize_codegen_targets();

    std::string triple_text = effective_triple(target);

    llvm::Triple triple(triple_text);
    std::string error;
    const llvm::Target* llvm_target =
        llvm::TargetRegistry::lookupTarget(triple, error);
    if (!llvm_target) {
        add_error(diagnostics,
                  "could not create target for '" + triple_text + "': " + error);
        return nullptr;
    }

    llvm::TargetOptions target_options;

    if (triple.isOSBinFormatELF()) {
        target_options.UseInitArray = true;
    }

    target_options.DisableIntegratedAS = options.disable_integrated_as;

    std::string features = options.features;
    if (features.empty() && target.arch == TargetArch::AARCH64) {
        features = "+v8a";
    }

    llvm::Reloc::Model reloc = relocation_model(options);
    std::unique_ptr<llvm::TargetMachine> machine(
        llvm_target->createTargetMachine(triple,
                                         options.cpu,
                                         features,
                                         target_options,
                                         reloc,
                                         std::nullopt,
                                         options.opt_level));
    if (!machine) {
        add_error(diagnostics,
                  "could not create target machine for '" + triple_text + "'");
        return nullptr;
    }
    return machine;
}

bool configure_module_target(llvm::Module& module,
                             const TargetInfo& target,
                             const TargetMachineOptions& options,
                             std::vector<Diagnostic>& diagnostics) {
    std::unique_ptr<llvm::TargetMachine> machine =
        create_target_machine(target, options, diagnostics);
    if (!machine) {
        return false;
    }

    module.setTargetTriple(llvm::Triple(effective_triple(target)));
    module.setDataLayout(machine->createDataLayout());
    return true;
}

bool is_native_jit_target(const TargetInfo& target) {
    std::shared_ptr<TargetInfo> host = TargetInfo::create_host();
    return host && target.arch == host->arch && target.os == host->os;
}

} // namespace aburi::cir2llvm
