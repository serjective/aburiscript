#include "cir2llvm.h"

#include "lowerer.h"
#include "target_support.h"

#include <algorithm>
#include <cstdlib>
#include <cstring>
#include <ostream>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>

#include <llvm/ExecutionEngine/Orc/ExecutionUtils.h>
#include <llvm/ExecutionEngine/Orc/LLJIT.h>
#include <llvm/ExecutionEngine/Orc/Mangling.h>
#include <llvm/ExecutionEngine/Orc/ThreadSafeModule.h>
#include <llvm/Analysis/TargetLibraryInfo.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/TargetParser/Triple.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <llvm/Transforms/Utils/Local.h>
#include <llvm/Support/FileSystem.h>

namespace aburi::cir2llvm {
namespace {

struct EmutlsControlLayout {
    std::size_t size;
    std::size_t alignment;
    void* object;
    void* init_image;
};

thread_local std::unordered_map<const void*, void*> emutls_allocations;

bool is_power_of_two(std::size_t value) {
    return value && ((value & (value - 1)) == 0);
}

std::size_t round_up_pow2(std::size_t value) {
    if (value <= 1) {
        return 1;
    }
    std::size_t out = 1;
    while (out < value) {
        out <<= 1;
    }
    return out;
}

std::size_t normalize_alignment(std::size_t alignment) {
    if (alignment == 0) {
        alignment = alignof(void*);
    }
    if (alignment < alignof(void*)) {
        alignment = alignof(void*);
    }
    if (!is_power_of_two(alignment)) {
        alignment = round_up_pow2(alignment);
    }
    return alignment;
}

std::size_t align_up(std::size_t value, std::size_t alignment) {
    return (value + alignment - 1) & ~(alignment - 1);
}

void append_error(std::vector<Diagnostic>& diagnostics, std::string message) {
    Diagnostic diag;
    diag.level = DiagnosticLevel::Error;
    diag.message = "cir2llvm: " + std::move(message);
    diagnostics.push_back(std::move(diag));
}

bool diagnostics_ok(const std::vector<Diagnostic>& diagnostics) {
    for (const Diagnostic& diag : diagnostics) {
        if (diag.level == DiagnosticLevel::Error) {
            return false;
        }
    }
    return true;
}

LoweringOptions lowering_options_from_target_options(
    const TargetOutputOptions& options) {
    LoweringOptions lowering_options;
    lowering_options.target = options.target;
    lowering_options.module_name = options.module_name;
    lowering_options.verify_llvm = options.verify_llvm;
    lowering_options.cxx_mangling = options.cxx_mangling;
    lowering_options.objc = options.objc;
    lowering_options.pic = options.pic;
    lowering_options.branch_target_enforcement = options.branch_target_enforcement;
    lowering_options.sign_return_address = options.sign_return_address;
    lowering_options.keep_frame_pointer = options.keep_frame_pointer;
    lowering_options.fcommon = options.fcommon;
    return lowering_options;
}

llvm::CodeGenFileType codegen_file_type(OutputKind kind) {
    return kind == OutputKind::Assembly
        ? llvm::CodeGenFileType::AssemblyFile
        : llvm::CodeGenFileType::ObjectFile;
}

} // namespace

extern "C" void* __emutls_get_address(void* control_addr) {
    auto cached = emutls_allocations.find(control_addr);
    if (cached != emutls_allocations.end()) {
        return cached->second;
    }

    auto* control = static_cast<EmutlsControlLayout*>(control_addr);
    if (!control) {
        return nullptr;
    }

    std::size_t alignment = normalize_alignment(control->alignment);
    std::size_t size = std::max<std::size_t>(1, control->size);
    std::size_t allocation_size = align_up(size, alignment);
    void* allocation = nullptr;
    if (posix_memalign(&allocation, alignment, allocation_size) != 0) {
        return nullptr;
    }

    if (control->init_image) {
        std::memcpy(allocation, control->init_image, size);
        if (allocation_size > size) {
            std::memset(static_cast<char*>(allocation) + size,
                        0,
                        allocation_size - size);
        }
    } else {
        std::memset(allocation, 0, allocation_size);
    }

    emutls_allocations.emplace(control_addr, allocation);
    return allocation;
}

extern "C" void __emutls_register_common(void*) {}

bool LoweringResult::ok() const {
    return diagnostics_ok(diagnostics);
}

bool TargetOutputResult::ok() const {
    return diagnostics_ok(diagnostics);
}

bool JitResult::ok() const {
    return diagnostics_ok(diagnostics);
}

namespace {

void fold_constant_branches(llvm::Module& module) {
    for (llvm::Function& function : module) {
        if (function.isDeclaration()) {
            continue;
        }
        bool changed = true;
        while (changed) {
            changed = false;
            for (llvm::BasicBlock& block : function) {
                changed |= llvm::ConstantFoldTerminator(&block);
            }
        }
        llvm::EliminateUnreachableBlocks(function);
    }
}

} // namespace

LoweringResult lower_cir_to_llvm(const cir::File& file,
                                   LoweringOptions options) {
    LoweringResult result = Lowerer(file, std::move(options)).run();
    if (result.ok() && result.module) {
        fold_constant_branches(*result.module);
    }
    return result;
}

bool write_llvm_ir(const cir::File& file,
                   LoweringOptions options,
                   std::ostream& out,
                   std::vector<Diagnostic>* diagnostics) {
    LoweringResult result = lower_cir_to_llvm(file, std::move(options));
    if (diagnostics) {
        diagnostics->insert(diagnostics->end(),
                            result.diagnostics.begin(),
                            result.diagnostics.end());
    }
    if (!result.ok()) {
        return false;
    }

    std::string text;
    llvm::raw_string_ostream stream(text);
    result.module->print(stream, nullptr);
    stream.flush();
    out << text;
    return true;
}

llvm::TargetLibraryInfoImpl make_target_library_info(const llvm::Module& module,
                                                     bool freestanding) {
    llvm::TargetLibraryInfoImpl tlii{module.getTargetTriple()};
    if (freestanding) {
        tlii.disableAllFunctions();
    }
    return tlii;
}

void run_middle_end_pipeline(llvm::Module& module,
                             llvm::TargetMachine& machine,
                             int opt_level,
                             bool freestanding) {
    llvm::PassBuilder pass_builder(&machine);
    llvm::LoopAnalysisManager lam;
    llvm::FunctionAnalysisManager fam;
    llvm::CGSCCAnalysisManager cgam;
    llvm::ModuleAnalysisManager mam;

    fam.registerPass([&] {
        return llvm::TargetLibraryAnalysis(
            make_target_library_info(module, freestanding));
    });
    pass_builder.registerModuleAnalyses(mam);
    pass_builder.registerCGSCCAnalyses(cgam);
    pass_builder.registerFunctionAnalyses(fam);
    pass_builder.registerLoopAnalyses(lam);
    pass_builder.crossRegisterProxies(lam, fam, cgam, mam);

    llvm::OptimizationLevel level = llvm::OptimizationLevel::O1;
    if (opt_level == 2) {
        level = llvm::OptimizationLevel::O2;
    } else if (opt_level >= 3) {
        level = llvm::OptimizationLevel::O3;
    }
    llvm::ModulePassManager mpm =
        pass_builder.buildPerModuleDefaultPipeline(level);
    mpm.run(module, mam);
}

TargetOutputResult emit_target_output(const cir::File& file,
                                      const TargetOutputOptions& options) {
    TargetOutputResult out;
    if (options.output_path.empty()) {
        append_error(out.diagnostics, "target output path cannot be empty");
        return out;
    }
    std::shared_ptr<TargetInfo> target =
        options.target ? options.target : TargetInfo::create_host();

    TargetOutputOptions effective_options = options;
    effective_options.target = target;
    LoweringResult lowered = lower_cir_to_llvm(
        file, lowering_options_from_target_options(effective_options));
    out.diagnostics.insert(out.diagnostics.end(),
                           lowered.diagnostics.begin(),
                           lowered.diagnostics.end());
    if (!lowered.ok()) {
        return out;
    }

    std::error_code ec;
    llvm::raw_fd_ostream dest(options.output_path, ec, llvm::sys::fs::OF_None);
    if (ec) {
        append_error(out.diagnostics,
                     "could not open output file '" + options.output_path +
                         "': " + ec.message());
        return out;
    }

    if (options.kind == OutputKind::LLVMIR) {
        lowered.module->print(dest, nullptr);
        dest.flush();
        return out;
    }

    TargetMachineOptions machine_options;
    machine_options.cpu = options.cpu;
    machine_options.features = options.features;
    machine_options.pic = options.pic;

    machine_options.disable_integrated_as = (options.kind == OutputKind::Assembly);

    switch (options.opt_level) {
        case 0:
            machine_options.opt_level = llvm::CodeGenOptLevel::None;
            break;
        case 1:
            machine_options.opt_level = llvm::CodeGenOptLevel::Less;
            break;
        case 2:
            machine_options.opt_level = llvm::CodeGenOptLevel::Default;
            break;
        default:
            machine_options.opt_level = llvm::CodeGenOptLevel::Aggressive;
            break;
    }
    std::unique_ptr<llvm::TargetMachine> machine =
        create_target_machine(*target, machine_options, out.diagnostics);
    if (!machine) {
        return out;
    }

    if (options.opt_level >= 1) {
        run_middle_end_pipeline(*lowered.module, *machine, options.opt_level,
                                options.freestanding);
    }

    llvm::legacy::PassManager pass;

    pass.add(new llvm::TargetLibraryInfoWrapperPass(
        make_target_library_info(*lowered.module, options.freestanding)));
    if (machine->addPassesToEmitFile(
            pass, dest, nullptr, codegen_file_type(options.kind))) {
        append_error(out.diagnostics,
                     "target machine cannot emit the requested output kind");
        return out;
    }

    pass.run(*lowered.module);
    dest.flush();
    return out;
}

JitResult run_jit(const cir::File& file, JitOptions options) {
    JitResult out;
    if (!options.target) {
        options.target = TargetInfo::create_host();
    }
    if (!is_native_jit_target(*options.target)) {
        append_error(out.diagnostics,
                     "JIT mode only supports the native host target");
        return out;
    }
    if (options.entry.empty()) {
        append_error(out.diagnostics, "JIT entry symbol cannot be empty");
        return out;
    }

    LoweringOptions lowering_options;
    lowering_options.target = options.target;
    lowering_options.module_name = options.module_name;
    lowering_options.verify_llvm = options.verify_llvm;
    lowering_options.cxx_mangling = options.cxx_mangling;
    LoweringResult lowered = lower_cir_to_llvm(file, std::move(lowering_options));
    out.diagnostics.insert(out.diagnostics.end(),
                           lowered.diagnostics.begin(),
                           lowered.diagnostics.end());
    if (!lowered.ok()) {
        return out;
    }

    initialize_codegen_targets();
    auto jit = llvm::orc::LLJITBuilder().create();
    if (!jit) {
        append_error(out.diagnostics,
                     "failed to create LLJIT: " +
                         llvm::toString(jit.takeError()));
        return out;
    }

    llvm::orc::JITDylib& jd = (*jit)->getMainJITDylib();
    llvm::orc::ExecutionSession& es = (*jit)->getExecutionSession();
    llvm::orc::MangleAndInterner mangle(es, (*jit)->getDataLayout());
    llvm::orc::SymbolMap runtime_symbols;
    auto add_runtime_symbol = [&](std::string_view name, auto* address) {
        runtime_symbols[mangle(llvm::StringRef(name.data(), name.size()))] =
            llvm::orc::ExecutorSymbolDef(
                llvm::orc::ExecutorAddr::fromPtr(address),
                llvm::JITSymbolFlags::Exported);
    };
    add_runtime_symbol("__emutls_get_address", &__emutls_get_address);
    add_runtime_symbol("__emutls_register_common", &__emutls_register_common);

    if (auto err = jd.define(llvm::orc::absoluteSymbols(std::move(runtime_symbols)))) {
        append_error(out.diagnostics,
                     "failed to install JIT runtime symbols: " +
                         llvm::toString(std::move(err)));
        return out;
    }

    auto generator = llvm::orc::DynamicLibrarySearchGenerator::GetForCurrentProcess(
        (*jit)->getDataLayout().getGlobalPrefix());
    if (!generator) {
        append_error(out.diagnostics,
                     "failed to create JIT process symbol generator: " +
                         llvm::toString(generator.takeError()));
        return out;
    }
    jd.addGenerator(std::move(*generator));

    std::vector<llvm::GlobalAlias*> aliases;
    for (llvm::GlobalAlias& alias : lowered.module->aliases()) {
        aliases.push_back(&alias);
    }
    for (llvm::GlobalAlias* alias : aliases) {
        alias->replaceAllUsesWith(alias->getAliasee());
        alias->eraseFromParent();
    }

    llvm::orc::ThreadSafeContext thread_safe_context(std::move(lowered.context));
    llvm::orc::ThreadSafeModule thread_safe_module(std::move(lowered.module),
                                                   thread_safe_context);
    if (auto err = (*jit)->addIRModule(std::move(thread_safe_module))) {
        append_error(out.diagnostics,
                     "failed to add IR module to JIT: " +
                         llvm::toString(std::move(err)));
        return out;
    }

    if (auto err = (*jit)->initialize(jd)) {
        append_error(out.diagnostics,
                     "failed to run JIT initializers: " +
                         llvm::toString(std::move(err)));
        return out;
    }

    auto entry_symbol = (*jit)->lookup(options.entry);
    if (!entry_symbol) {
        append_error(out.diagnostics,
                     "failed to find JIT entry '" + options.entry + "': " +
                         llvm::toString(entry_symbol.takeError()));
        return out;
    }

    auto* entry = entry_symbol->toPtr<int()>();
    out.exit_code = entry();

    if (auto err = (*jit)->deinitialize(jd)) {
        append_error(out.diagnostics,
                     "failed to run JIT deinitializers: " +
                         llvm::toString(std::move(err)));
    }
    return out;
}

} // namespace aburi::cir2llvm
