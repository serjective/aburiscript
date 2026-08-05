#ifndef ABURI_CIR2LLVM_CIR2LLVM_H
#define ABURI_CIR2LLVM_CIR2LLVM_H

#include <iosfwd>
#include <memory>
#include <string>
#include <vector>

#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>

#include "../abi/target_info.h"
#include "../diagnostics.h"
#include "../cir/file.h"

namespace aburi::cir2llvm {

struct LoweringOptions {
    std::shared_ptr<TargetInfo> target;
    std::string module_name = "aburi_module";
    bool verify_llvm = true;
    bool cxx_mangling = false;
    // Objective-C compiles over the C base but its exceptions unwind through
    // the C++ ABI, so the C-mode nounwind blanket must not apply.
    bool objc = false;
    bool pic = true;
    bool branch_target_enforcement = false;
    bool sign_return_address = false;
    bool keep_frame_pointer = false;
    bool fcommon = false;
};

struct LoweringResult {
    std::unique_ptr<llvm::LLVMContext> context;
    std::unique_ptr<llvm::Module> module;
    std::vector<Diagnostic> diagnostics;

    bool ok() const;
};

enum class OutputKind {
    LLVMIR,
    Assembly,
    Object,
};

struct TargetOutputOptions {
    std::shared_ptr<TargetInfo> target;
    std::string module_name = "aburi_module";
    std::string output_path;
    OutputKind kind = OutputKind::LLVMIR;
    std::string cpu = "generic";
    std::string features;
    bool pic = true;
    bool verify_llvm = true;
    bool cxx_mangling = false;
    // Objective-C compiles over the C base but its exceptions unwind through
    // the C++ ABI, so the C-mode nounwind blanket must not apply.
    bool objc = false;
    int opt_level = 0;
    bool branch_target_enforcement = false;
    bool sign_return_address = false;
    bool keep_frame_pointer = false;
    bool fcommon = false;
    bool freestanding = false;
};

struct TargetOutputResult {
    std::vector<Diagnostic> diagnostics;

    bool ok() const;
};

struct JitOptions {
    std::shared_ptr<TargetInfo> target;
    std::string module_name = "aburi_module";
    std::string entry = "main";
    bool verify_llvm = true;
    bool cxx_mangling = false;
    // Objective-C compiles over the C base but its exceptions unwind through
    // the C++ ABI, so the C-mode nounwind blanket must not apply.
    bool objc = false;
};

struct JitResult {
    std::vector<Diagnostic> diagnostics;
    int exit_code = 0;

    bool ok() const;
};

LoweringResult lower_cir_to_llvm(const cir::File& file,
                                   LoweringOptions options = {});

bool write_llvm_ir(const cir::File& file,
                   LoweringOptions options,
                   std::ostream& out,
                   std::vector<Diagnostic>* diagnostics = nullptr);

TargetOutputResult emit_target_output(const cir::File& file,
                                      const TargetOutputOptions& options);

JitResult run_jit(const cir::File& file, JitOptions options = {});

} // namespace aburi::cir2llvm

#endif // ABURI_CIR2LLVM_CIR2LLVM_H
