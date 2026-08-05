#include "lowerer.h"

#include "target_support.h"

#include <algorithm>
#include <utility>

#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>

namespace aburi::cir2llvm {

Lowerer::Lowerer(const cir::File& file, LoweringOptions options)
    : file_(file), options_(std::move(options)) {}

LoweringResult Lowerer::run() {
    if (!options_.target) {
        options_.target = file_.target_info_ptr();
    }
    if (!options_.target) {
        options_.target = TargetInfo::create_host();
    }

    result_.context = std::make_unique<llvm::LLVMContext>();
    result_.module = std::make_unique<llvm::Module>(
        options_.module_name.empty() ? "aburi_module" : options_.module_name,
        *result_.context);
    TargetMachineOptions target_options;
    if (!configure_module_target(*result_.module,
                                 *options_.target,
                                 target_options,
                                 result_.diagnostics)) {
        return std::move(result_);
    }

    if (options_.branch_target_enforcement) {
        result_.module->addModuleFlag(llvm::Module::Min,
                                      "branch-target-enforcement", 1);
    }
    if (options_.sign_return_address) {
        result_.module->addModuleFlag(llvm::Module::Min,
                                      "sign-return-address", 1);
    }
    builder_ = std::make_unique<llvm::IRBuilder<>>(*result_.context);

    preflight();
    if (has_errors()) {
        return std::move(result_);
    }

    for (const std::string& module_asm : file_.module_asm()) {
        module().appendModuleInlineAsm(module_asm);
    }

    declare_entities();
    for (cir::FunctionId function_id : file_.function_ids()) {
        const cir::Entity& entity = file_.entity(file_.function(function_id).entity);
        if (entity.is_deleted ||
            entity.is_template_pattern ||
            entity.result_type_only_definition ||
            entity.decl_flags.is_consteval ||
            entity.suppressed_by_explicit_instantiation_declaration ||
            entity.suppressed_as_unselected_template_candidate) {
            continue;
        }
        if (!definition_required(entity)) {
            continue;
        }
        if (entity.symbol_policy.imported_definition &&
            entity.symbol_policy.emission != cir::LinkageKind::LinkOnceODR) {

            continue;
        }
        lower_function(function_id);
        if (has_errors()) {
            return std::move(result_);
        }
    }
    emit_structor_aliases();
    merge_expression_blocks();

    replace_aggregate_copies();

    if (options_.verify_llvm) {
        std::string verifier_text;
        llvm::raw_string_ostream verifier_stream(verifier_text);
        if (llvm::verifyModule(module(), &verifier_stream)) {
            verifier_stream.flush();
            error("LLVM verifier rejected cir2llvm output: " + verifier_text);
        }
    }

    return std::move(result_);
}

void Lowerer::merge_expression_blocks() {

    for (llvm::Function& function : module()) {
        if (function.isDeclaration()) {
            continue;
        }
        bool merged_any = true;
        while (merged_any) {
            merged_any = false;

            for (auto it = std::next(function.begin()), end = function.end();
                 it != end;) {
                llvm::BasicBlock& block = *it++;
                if (llvm::MergeBlockIntoPredecessor(&block)) {
                    merged_any = true;
                }
            }
        }
    }
}

void Lowerer::replace_aggregate_copies() {

    const llvm::DataLayout& layout = module().getDataLayout();
    for (llvm::Function& function : module()) {
        std::vector<llvm::StoreInst*> copies;
        for (llvm::BasicBlock& block : function) {
            for (llvm::Instruction& instruction : block) {
                auto* store = llvm::dyn_cast<llvm::StoreInst>(&instruction);
                if (!store || store->isVolatile()) {
                    continue;
                }
                llvm::Type* type = store->getValueOperand()->getType();
                if (!type->isArrayTy() && !type->isStructTy()) {
                    continue;
                }
                auto* load = llvm::dyn_cast<llvm::LoadInst>(store->getValueOperand());
                if (!load || load->isVolatile() || !load->hasOneUse() ||
                    load->getParent() != store->getParent()) {
                    continue;
                }

                bool source_is_stable = true;
                for (llvm::Instruction* between = load->getNextNode();
                     between && between != store;
                     between = between->getNextNode()) {
                    if (between->mayWriteToMemory()) {
                        source_is_stable = false;
                        break;
                    }
                }
                if (source_is_stable) {
                    copies.push_back(store);
                }
            }
        }

        for (llvm::StoreInst* store : copies) {
            auto* load = llvm::cast<llvm::LoadInst>(store->getValueOperand());
            llvm::IRBuilder<> copy_builder(store);
            copy_builder.CreateMemCpy(
                store->getPointerOperand(), store->getAlign(),
                load->getPointerOperand(), load->getAlign(),
                layout.getTypeStoreSize(load->getType()));
            store->eraseFromParent();
            load->eraseFromParent();
        }
    }
}

llvm::LLVMContext& Lowerer::context() { return *result_.context; }

llvm::Module& Lowerer::module() { return *result_.module; }

llvm::IRBuilder<>& Lowerer::builder() { return *builder_; }

void Lowerer::error(std::string message, SrcLoc loc) {
    Diagnostic diag;
    diag.level = DiagnosticLevel::Error;
    diag.message = "cir2llvm: " + std::move(message);
    diag.location = loc;
    result_.diagnostics.push_back(std::move(diag));
}

bool Lowerer::has_errors() const {
    for (const Diagnostic& diag : result_.diagnostics) {
        if (diag.level == DiagnosticLevel::Error) {
            return true;
        }
    }
    return false;
}

uint64_t Lowerer::pointer_bytes() const {
    int width = options_.target ? options_.target->pointer_width : 64;
    return std::max<uint64_t>(1, static_cast<uint64_t>((width + 7) / 8));
}

uint64_t Lowerer::pointer_bits() const {
    return pointer_bytes() * 8;
}

} // namespace aburi::cir2llvm
