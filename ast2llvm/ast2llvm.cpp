#include "ast2llvm.h"
#include "../abi/mangle.h"
#include "../helpers/casting.h"
#include <iostream>
#include <vector>
#include <string>
#include <sstream>
#include <iomanip>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <exception>
#include <typeinfo>
#include <unordered_map>
#include <unordered_set>
#include <llvm/Support/raw_ostream.h>
#include <llvm/ExecutionEngine/Orc/LLJIT.h>
#include <llvm/ExecutionEngine/Orc/Mangling.h>
#include <llvm/ExecutionEngine/Orc/ThreadSafeModule.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/IR/Verifier.h>
#include <llvm/MC/TargetRegistry.h>
#include <llvm/Target/TargetMachine.h>
#include <llvm/Target/TargetOptions.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/TargetParser/Host.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/IR/PassManager.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Transforms/Scalar.h>
#include <llvm/Transforms/IPO.h>
#include <llvm/Transforms/Utils.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/BinaryFormat/Dwarf.h>
#include <llvm/IR/IntrinsicInst.h>

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

std::size_t align_up(std::size_t value, std::size_t alignment) {
    return (value + alignment - 1) & ~(alignment - 1);
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

llvm::CodeGenOptLevel get_codegen_opt_level(const std::string& optimization_level) {
    if (optimization_level == "0") return llvm::CodeGenOptLevel::None;
    if (optimization_level == "1") return llvm::CodeGenOptLevel::Less;
    if (optimization_level == "2") return llvm::CodeGenOptLevel::Default;
    if (optimization_level == "3") return llvm::CodeGenOptLevel::Aggressive;
    if (optimization_level == "s") return llvm::CodeGenOptLevel::Default;
    if (optimization_level == "z") return llvm::CodeGenOptLevel::Default;
    // Treat absent/unknown levels as -O0 semantics.
    return llvm::CodeGenOptLevel::None;
}

bool record_uses_byte_layout(const ObjectType* rec) {
    if (!rec) {
        return false;
    }
    if (rec->is_packed || rec->pack_alignment > 0) {
        return true;
    }
    if (rec->has_bitfields()) {
        return true;
    }
    for (const auto& field : rec->semantic_fields()) {
        if (field.forced_alignment > 0 ||
            field.is_base_subobject ||
            field.storage_size_override > 0 ||
            field.storage_alignment_override > 0) {
            return true;
        }
    }
    return false;
}

const void* record_cache_key(const ObjectType* rec) {
    if (!rec) {
        return nullptr;
    }
    if (auto* decl = rec->get_decl()) {
        return decl;
    }
    return rec;
}

bool llvm_type_contains_pointer_impl(llvm::Type* ty,
                                     std::unordered_set<llvm::Type*>& visiting) {
    if (!ty) {
        return false;
    }
    if (ty->isPointerTy()) {
        return true;
    }
    if (!visiting.insert(ty).second) {
        return false;
    }

    if (auto* st = llvm::dyn_cast<llvm::StructType>(ty)) {
        for (unsigned i = 0; i < st->getNumElements(); ++i) {
            if (llvm_type_contains_pointer_impl(st->getElementType(i), visiting)) {
                return true;
            }
        }
        return false;
    }

    if (auto* arr = llvm::dyn_cast<llvm::ArrayType>(ty)) {
        return llvm_type_contains_pointer_impl(arr->getElementType(), visiting);
    }

    if (auto* vec = llvm::dyn_cast<llvm::FixedVectorType>(ty)) {
        return llvm_type_contains_pointer_impl(vec->getElementType(), visiting);
    }

    return false;
}

bool llvm_type_contains_pointer(llvm::Type* ty) {
    std::unordered_set<llvm::Type*> visiting;
    return llvm_type_contains_pointer_impl(ty, visiting);
}

void collect_llvm_pointer_offsets_impl(
    llvm::Type* ty,
    const llvm::DataLayout& DL,
    std::size_t base_offset,
    std::unordered_set<llvm::Type*>& visiting,
    std::unordered_set<std::size_t>& offsets) {
    if (!ty) {
        return;
    }
    if (ty->isPointerTy()) {
        offsets.insert(base_offset);
        return;
    }
    if (!visiting.insert(ty).second) {
        return;
    }

    if (auto* st = llvm::dyn_cast<llvm::StructType>(ty)) {
        const llvm::StructLayout* layout = DL.getStructLayout(st);
        for (unsigned i = 0; i < st->getNumElements(); ++i) {
            collect_llvm_pointer_offsets_impl(
                st->getElementType(i),
                DL,
                base_offset + layout->getElementOffset(i),
                visiting,
                offsets);
        }
        return;
    }

    if (auto* arr = llvm::dyn_cast<llvm::ArrayType>(ty)) {
        llvm::Type* elem_ty = arr->getElementType();
        std::size_t elem_size = DL.getTypeAllocSize(elem_ty);
        for (uint64_t i = 0; i < arr->getNumElements(); ++i) {
            collect_llvm_pointer_offsets_impl(
                elem_ty, DL, base_offset + i * elem_size, visiting, offsets);
        }
        return;
    }

    if (auto* vec = llvm::dyn_cast<llvm::FixedVectorType>(ty)) {
        llvm::Type* elem_ty = vec->getElementType();
        std::size_t elem_size = DL.getTypeAllocSize(elem_ty);
        for (unsigned i = 0; i < vec->getNumElements(); ++i) {
            collect_llvm_pointer_offsets_impl(
                elem_ty, DL, base_offset + i * elem_size, visiting, offsets);
        }
    }
}

std::unordered_set<std::size_t> collect_llvm_pointer_offsets(
    llvm::Type* ty,
    const llvm::DataLayout& DL) {
    std::unordered_set<llvm::Type*> visiting;
    std::unordered_set<std::size_t> offsets;
    collect_llvm_pointer_offsets_impl(ty, DL, 0, visiting, offsets);
    return offsets;
}

bool llvm_type_covers_pointer_offsets(
    llvm::Type* storage_ty,
    const std::unordered_set<std::size_t>& required_offsets,
    const llvm::DataLayout& DL) {
    if (required_offsets.empty()) {
        return true;
    }
    auto provided_offsets = collect_llvm_pointer_offsets(storage_ty, DL);
    for (std::size_t offset : required_offsets) {
        if (!provided_offsets.count(offset)) {
            return false;
        }
    }
    return true;
}

llvm::Type* build_union_pointer_storage_type(
    llvm::LLVMContext& context,
    const llvm::DataLayout& DL,
    std::size_t size_in_bytes,
    const std::unordered_set<std::size_t>& pointer_offsets) {
    if (pointer_offsets.empty()) {
        return llvm::ArrayType::get(llvm::Type::getInt8Ty(context), size_in_bytes);
    }

    std::vector<std::size_t> sorted_offsets(pointer_offsets.begin(), pointer_offsets.end());
    std::sort(sorted_offsets.begin(), sorted_offsets.end());
    sorted_offsets.erase(std::unique(sorted_offsets.begin(), sorted_offsets.end()),
                         sorted_offsets.end());

    llvm::Type* byte_type = llvm::Type::getInt8Ty(context);
    llvm::Type* ptr_type = llvm::PointerType::getUnqual(context);
    std::size_t ptr_size = DL.getTypeAllocSize(ptr_type);
    std::vector<llvm::Type*> field_types;
    std::size_t current = 0;

    for (std::size_t offset : sorted_offsets) {
        if (offset > size_in_bytes) {
            break;
        }
        if (offset < current) {
            continue;
        }
        if (offset > current) {
            field_types.push_back(llvm::ArrayType::get(byte_type, offset - current));
            current = offset;
        }
        if (current + ptr_size > size_in_bytes) {
            break;
        }
        field_types.push_back(ptr_type);
        current += ptr_size;
    }

    if (current < size_in_bytes) {
        field_types.push_back(llvm::ArrayType::get(byte_type, size_in_bytes - current));
    }

    return llvm::StructType::get(context, field_types, /*isPacked=*/true);
}

const EhRuntimeHooks& get_active_eh_runtime_hooks(const ASTToLLVM& codegen) {
    if (codegen.ast_ctx && codegen.ast_ctx->abi_policy) {
        return codegen.ast_ctx->abi_policy->eh_runtime_hooks;
    }
    static const EhRuntimeHooks defaults =
        eh_runtime_hooks_for_kind(EhRuntimeKind::LLVM);
    return defaults;
}

BuiltinTypes normalize_darwin_hfa_builtin_kind(BuiltinTypes kind,
                                               const TargetInfo* target) {
    if (kind == BuiltinTypes::LongDouble && target &&
        target->long_double_format == LongDoubleFormat::IEEE_DOUBLE) {
        return BuiltinTypes::Double;
    }
    return kind;
}

bool is_darwin_hfa_builtin_kind(BuiltinTypes kind) {
    switch (kind) {
        case BuiltinTypes::Float16:
        case BuiltinTypes::Float:
        case BuiltinTypes::Double:
            return true;
        default:
            return false;
    }
}

bool collect_darwin_hfa_members(const QualType& type,
                                const ASTContext* ast_ctx,
                                const TargetInfo* target,
                                BuiltinTypes& element_kind,
                                unsigned& element_count) {
    auto canonical = desugar_type(type, ast_ctx);
    if (!canonical) {
        return false;
    }

    if (auto builtin = canonical.as_shared<BuiltinType>()) {
        BuiltinTypes candidate =
            normalize_darwin_hfa_builtin_kind(builtin->builtin_kind, target);
        if (!is_darwin_hfa_builtin_kind(candidate)) {
            return false;
        }
        if (element_count == 0) {
            element_kind = candidate;
        } else if (element_kind != candidate) {
            return false;
        }
        element_count += 1;
        return element_count <= 4;
    }

    if (auto array = canonical.as_shared<ArrayType>()) {
        if (array->size_kind != ArraySizeKind::Constant || !array->size.has_value()) {
            return false;
        }
        if (*array->size == 0 || *array->size > 4) {
            return false;
        }
        for (size_t i = 0; i < *array->size; ++i) {
            if (!collect_darwin_hfa_members(
                    array->element_type, ast_ctx, target, element_kind, element_count)) {
                return false;
            }
        }
        return true;
    }

    auto record = canonical.as_shared<ObjectType>();
    if (!record || record->is_union || record->isIncomplete()) {
        return false;
    }
    for (const auto& field : record->semantic_fields()) {
        if (field.is_bitfield || field.storage_size_override > 0 ||
            field.storage_alignment_override > 0) {
            return false;
        }
        if (!collect_darwin_hfa_members(
                field.type, ast_ctx, target, element_kind, element_count)) {
            return false;
        }
    }
    return element_count > 0 && element_count <= 4;
}
}

extern "C" {
void* __cxa_allocate_exception(std::size_t thrown_size);
[[noreturn]] void __cxa_throw(void* thrown_exception,
                              void* typeinfo,
                              void (*dest)(void*));
void* __cxa_begin_catch(void* exc_obj) noexcept;
void __cxa_end_catch();
[[noreturn]] void __cxa_rethrow();
void* __dynamic_cast(const void* sub,
                     const void* src,
                     const void* dst,
                     std::ptrdiff_t src2dst_offset);
[[noreturn]] void __cxa_bad_cast();
[[noreturn]] void __cxa_bad_typeid();
[[noreturn]] void _Unwind_Resume(void* exc_obj);
int __gxx_personality_v0(...);
}

extern "C" void* __emutls_get_address(void* control_addr) {
    if (!control_addr) {
        return nullptr;
    }

    auto* control = reinterpret_cast<EmutlsControlLayout*>(control_addr);
    auto it = emutls_allocations.find(control_addr);
    if (it != emutls_allocations.end()) {
        return it->second;
    }

    std::size_t alignment = normalize_alignment(control->alignment);
    std::size_t object_size = control->size == 0 ? 1 : control->size;
    std::size_t alloc_size = align_up(object_size, alignment);

    void* allocation = nullptr;
    if (posix_memalign(&allocation, alignment, alloc_size) != 0 || !allocation) {
        return nullptr;
    }

    if (control->init_image) {
        std::memcpy(allocation, control->init_image, control->size);
        if (alloc_size > control->size) {
            std::memset(static_cast<char*>(allocation) + control->size, 0, alloc_size - control->size);
        }
    } else {
        std::memset(allocation, 0, alloc_size);
    }

    emutls_allocations.emplace(control_addr, allocation);
    return allocation;
}

extern "C" void __emutls_register_common(void*) {
    // Darwin ORC JIT TLS paths currently only require __emutls_get_address.
}

// As of LLVM 18.1.8
ASTToLLVM::ASTToLLVM() : context(std::make_unique<llvm::LLVMContext>()), builder(*context) {
    module = std::make_unique<llvm::Module>("aburi_module", *context);
    target = TargetInfo::create_host();
    type_ctx = std::make_shared<TypeContext>(target);

    // Initialize target
    llvm::InitializeNativeTarget();
    llvm::InitializeNativeTargetAsmPrinter();
    llvm::InitializeNativeTargetAsmParser();

    std::string triple = target->triple.empty()
        ? llvm::sys::getDefaultTargetTriple()
        : target->triple;
    module->setTargetTriple(triple);

    std::string error;
    auto llvm_target = llvm::TargetRegistry::lookupTarget(triple, error);

    if (!llvm_target) {
        // Fallback or error
    } else {
        std::string cpu = "generic";
        std::string features = "";
        llvm::TargetOptions opt;
        auto RM = llvm::Reloc::Model::PIC_;
        auto targetMachine = llvm_target->createTargetMachine(triple, cpu, features, opt, RM);
        module->setDataLayout(targetMachine->createDataLayout());
    }
}

void ASTToLLVM::reset_entry_alloca_insertion_state() {
    last_entry_alloca = nullptr;
}

llvm::AllocaInst* ASTToLLVM::create_entry_alloca(llvm::Function* function,
                                                 llvm::Type* alloc_type,
                                                 llvm::Value* array_size,
                                                 const std::string& name) {
    if (!function || function->empty() || !alloc_type) {
        return nullptr;
    }

    llvm::BasicBlock& entry_block = function->getEntryBlock();
    llvm::Instruction* insert_before = nullptr;
    if (last_entry_alloca && last_entry_alloca->getParent() == &entry_block) {
        llvm::Instruction* cursor = last_entry_alloca->getNextNode();
        while (cursor) {
            if (auto* next_alloca = llvm::dyn_cast<llvm::AllocaInst>(cursor)) {
                last_entry_alloca = next_alloca;
                cursor = next_alloca->getNextNode();
                continue;
            }
            if (llvm::isa<llvm::DbgInfoIntrinsic>(cursor)) {
                cursor = cursor->getNextNode();
                continue;
            }
            break;
        }
        insert_before = cursor;
    } else {
        auto insert_it = entry_block.getFirstNonPHIOrDbgOrAlloca();
        if (insert_it != entry_block.end()) {
            insert_before = &*insert_it;
        }
    }

    llvm::IRBuilder<> tmp_builder(*context);
    if (insert_before) {
        tmp_builder.SetInsertPoint(insert_before);
    } else {
        tmp_builder.SetInsertPoint(&entry_block);
    }

    auto* alloca =
        tmp_builder.CreateAlloca(alloc_type, array_size, name);
    last_entry_alloca = alloca;
    return alloca;
}

void ASTToLLVM::dump() {
    module->print(llvm::outs(), nullptr);
}

void ASTToLLVM::emit(std::string filename, llvm::CodeGenFileType file_type) {
    std::string triple = module->getTargetTriple();

    std::string error;
    auto llvm_target = llvm::TargetRegistry::lookupTarget(triple, error);
    if (!llvm_target) {
        throw std::runtime_error("Could not create target: " + error);
    }

    std::string cpu = "generic";
    std::string features = "";
    llvm::TargetOptions opt;
    auto RM = llvm::Reloc::Model::PIC_;
    auto codegen_opt_level = get_codegen_opt_level(optimization_level);
    auto targetMachine = llvm_target->createTargetMachine(
        triple,
        cpu,
        features,
        opt,
        RM,
        std::nullopt,
        codegen_opt_level
    );

    std::error_code ec;
    llvm::raw_fd_ostream dest(filename, ec, llvm::sys::fs::OF_None);
    if (ec) {
        throw std::runtime_error("Could not open file: " + ec.message());
    }

    llvm::legacy::PassManager pass;
    if (targetMachine->addPassesToEmitFile(pass, dest, nullptr, file_type)) {
        throw std::runtime_error("TargetMachine can't emit a file of this type");
    }

    pass.run(*module);
    dest.flush();
}

int ASTToLLVM::run() {
    if (llvm::verifyModule(*module, &llvm::errs())) {
        std::cerr << "Module verification failed!" << std::endl;
        return -500;
    }

    auto jit = llvm::orc::LLJITBuilder().create();
    if (!jit) {
        std::cerr << "Failed to create LLJIT: "
                  << llvm::toString(jit.takeError()) << std::endl;
        return -500;
    }

    auto &jd = (*jit)->getMainJITDylib();
    auto& es = (*jit)->getExecutionSession();
    llvm::orc::MangleAndInterner mangle(es, (*jit)->getDataLayout());
    llvm::orc::SymbolMap runtime_symbols;
    auto add_runtime_symbol = [&](std::string_view name, const void* addr) {
        if (name.empty() || !addr) {
            return;
        }
        runtime_symbols[mangle(name)] = llvm::orc::ExecutorSymbolDef(
            llvm::orc::ExecutorAddr::fromPtr(const_cast<void*>(addr)),
            llvm::JITSymbolFlags::Exported);
    };
    const auto& hooks = get_active_eh_runtime_hooks(*this);

    add_runtime_symbol("__emutls_get_address",
        reinterpret_cast<const void*>(&__emutls_get_address));
    add_runtime_symbol("__emutls_register_common",
        reinterpret_cast<const void*>(&__emutls_register_common));
    add_runtime_symbol(hooks.personality,
        reinterpret_cast<const void*>(&__gxx_personality_v0));
    add_runtime_symbol(hooks.allocate_exception,
        reinterpret_cast<const void*>(&__cxa_allocate_exception));
    add_runtime_symbol(hooks.throw_exception,
        reinterpret_cast<const void*>(&__cxa_throw));
    add_runtime_symbol(hooks.rethrow_exception,
        reinterpret_cast<const void*>(&__cxa_rethrow));
    add_runtime_symbol(hooks.dynamic_cast_symbol,
        reinterpret_cast<const void*>(&__dynamic_cast));
    add_runtime_symbol(hooks.bad_cast,
        reinterpret_cast<const void*>(&__cxa_bad_cast));
    add_runtime_symbol(hooks.bad_typeid,
        reinterpret_cast<const void*>(&__cxa_bad_typeid));
    add_runtime_symbol(hooks.begin_catch,
        reinterpret_cast<const void*>(&__cxa_begin_catch));
    add_runtime_symbol(hooks.end_catch,
        reinterpret_cast<const void*>(&__cxa_end_catch));
    add_runtime_symbol(hooks.unwind_resume,
        reinterpret_cast<const void*>(&_Unwind_Resume));
    add_runtime_symbol(
        hooks.terminate,
        reinterpret_cast<const void*>(static_cast<void (*)()>(std::terminate)));

    add_runtime_symbol("_ZTIb", &typeid(bool));
    add_runtime_symbol("_ZTIc", &typeid(char));
    add_runtime_symbol("_ZTIh", &typeid(unsigned char));
    add_runtime_symbol("_ZTIs", &typeid(short));
    add_runtime_symbol("_ZTIt", &typeid(unsigned short));
    add_runtime_symbol("_ZTIi", &typeid(int));
    add_runtime_symbol("_ZTIj", &typeid(unsigned int));
    add_runtime_symbol("_ZTIl", &typeid(long));
    add_runtime_symbol("_ZTIm", &typeid(unsigned long));
    add_runtime_symbol("_ZTIx", &typeid(long long));
    add_runtime_symbol("_ZTIy", &typeid(unsigned long long));
    add_runtime_symbol("_ZTIf", &typeid(float));
    add_runtime_symbol("_ZTId", &typeid(double));
    add_runtime_symbol("_ZTIe", &typeid(long double));

    if (auto err = jd.define(llvm::orc::absoluteSymbols(std::move(runtime_symbols)))) {
        std::cerr << "Failed to install JIT runtime symbols: "
                  << llvm::toString(std::move(err)) << std::endl;
        return -500;
    }

    auto gen = llvm::orc::DynamicLibrarySearchGenerator::GetForCurrentProcess(
        (*jit)->getDataLayout().getGlobalPrefix());
    if (!gen) {
        std::cerr << "Failed to create symbol generator: "
                  << llvm::toString(gen.takeError()) << std::endl;
        return -500;
    }
    jd.addGenerator(std::move(*gen));

    auto tsc = llvm::orc::ThreadSafeContext(std::move(context));
    auto tsm = llvm::orc::ThreadSafeModule(std::move(module), tsc);

    if (auto err = (*jit)->addIRModule(std::move(tsm))) {
        std::cerr << "Failed to add IR module: "
                  << llvm::toString(std::move(err)) << std::endl;
        return -500;
    }

    auto main_sym = (*jit)->lookup("main");
    if (!main_sym) {
        std::cerr << "Failed to find main: "
                  << llvm::toString(main_sym.takeError()) << std::endl;
        return -500;
    }

    auto *main_fn = main_sym->toPtr<int()>();
    int result = main_fn();

    // Recreate context and module for potential reuse
    context = std::make_unique<llvm::LLVMContext>();
    module = std::make_unique<llvm::Module>("aburi_module", *context);
    builder.~IRBuilder();
    new (&builder) llvm::IRBuilder<>(*context);
    named_values.clear();
    struct_type_cache.clear();
    cpp_vtable_cache.clear();
    cpp_vtable_group_cache.clear();
    cpp_nonvirtual_thunk_cache.clear();
    cpp_virtual_thunk_cache.clear();
    bitfield_field_index_map.clear();
    vla_size_cache.clear();

    return result;
}

std::string ASTToLLVM::get_asm_label_name(const std::string& label) {
    return "\01" + label;
}

std::string ASTToLLVM::get_function_llvm_name(const FuncDecl& decl) const {
    if (!(ast_ctx && ast_ctx->abi_policy)) {
        if (decl.asm_label) {
            return get_asm_label_name(*decl.asm_label);
        }
        return decl.name == "main" ? "main" : decl.name;
    }
    auto resolved = resolve_function_linkage_name(decl, *ast_ctx->abi_policy);
    if (resolved.from_asm_label) {
        return get_asm_label_name(resolved.name);
    }
    return resolved.name;
}

std::string ASTToLLVM::get_function_llvm_name(const std::shared_ptr<Symbol>& sym,
                                              const std::string& fallback_spelling) const {
    if (sym && sym->kind == SymbolKind::FUNCTION && ast_ctx && ast_ctx->abi_policy) {
        auto resolved = resolve_function_linkage_name(
            *sym, *ast_ctx->abi_policy, fallback_spelling);
        if (resolved.from_asm_label) {
            return get_asm_label_name(resolved.name);
        }
        return resolved.name;
    }
    if (sym && sym->asm_label.has_value()) {
        return get_asm_label_name(sym->asm_label.value());
    }
    if (sym && sym->kind == SymbolKind::FUNCTION) {
        if (sym->name == "main") {
            return "main";
        }
        return sym->name;
    }
    return fallback_spelling;
}

std::string ASTToLLVM::get_variable_linkage_identity(const VariableDecl& decl) const {
    if (decl.sym && decl.sym->linkage == VariableLinkage::NONE && !decl.asm_label) {
        return mangleCIdentifier(decl.sym->uid);
    }
    if (ast_ctx && ast_ctx->abi_policy) {
        auto resolved = resolve_variable_linkage_name(decl, *ast_ctx->abi_policy);
        return resolved.name;
    }
    if (decl.asm_label) {
        return *decl.asm_label;
    }
    if (!decl.name.empty()) {
        return decl.name;
    }
    if (decl.sym) {
        return decl.sym->name;
    }
    return "";
}

std::string ASTToLLVM::get_variable_llvm_name(const VariableDecl& decl) const {
    if (decl.sym && decl.sym->linkage == VariableLinkage::NONE && !decl.asm_label) {
        return mangleCIdentifier(decl.sym->uid);
    }
    if (ast_ctx && ast_ctx->abi_policy) {
        auto resolved = resolve_variable_linkage_name(decl, *ast_ctx->abi_policy);
        if (resolved.from_asm_label) {
            return get_asm_label_name(resolved.name);
        }
        return resolved.name;
    }
    if (decl.asm_label) {
        return get_asm_label_name(*decl.asm_label);
    }
    if (!decl.name.empty()) {
        return decl.name;
    }
    if (decl.sym) {
        return decl.sym->name;
    }
    return "";
}

std::string ASTToLLVM::get_variable_llvm_name(const std::shared_ptr<Symbol>& sym,
                                              const std::string& fallback_spelling) const {
    if (!sym) {
        return fallback_spelling;
    }
    if (sym->linkage == VariableLinkage::NONE && !sym->asm_label.has_value()) {
        return mangleCIdentifier(sym->uid);
    }
    if (ast_ctx && ast_ctx->abi_policy) {
        auto resolved = resolve_variable_linkage_name(
            *sym, *ast_ctx->abi_policy, fallback_spelling);
        if (resolved.from_asm_label) {
            return get_asm_label_name(resolved.name);
        }
        return resolved.name;
    }
    if (sym->asm_label.has_value()) {
        return get_asm_label_name(sym->asm_label.value());
    }
    if (!sym->name.empty()) {
        return sym->name;
    }
    return fallback_spelling;
}

llvm::Function* ASTToLLVM::get_or_create_function_symbol(
    const std::shared_ptr<Symbol>& sym,
    const std::string& fallback_spelling) {
    if (!sym || sym->kind != SymbolKind::FUNCTION) {
        return nullptr;
    }

    std::string fn_name = get_function_llvm_name(sym, fallback_spelling);
    if (llvm::Function* fn = module->getFunction(fn_name)) {
        if (!sym->uid.empty()) {
            named_values[mangleCIdentifier(sym->uid)] = fn;
        }
        return fn;
    }

    auto func_ctype = dyn_cast_shared<FunctionType>(sym->type.get_shared());
    if (!func_ctype) {
        return nullptr;
    }

    std::vector<llvm::Type*> param_types;
    bool has_void_param =
        func_ctype->parameters.size() == 1 &&
        func_ctype->parameters[0]->isVoid();
    if (!has_void_param) {
        for (const auto& p : func_ctype->parameters) {
            param_types.push_back(convert_param_type(p));
        }
    }
    prepend_indirect_result_parameter(param_types, func_ctype->ret_type);

    llvm::Type* ret_type = convert_function_return_type(func_ctype->ret_type);
    llvm::FunctionType* ft = llvm::FunctionType::get(
        ret_type, param_types, func_ctype->is_variadic || !func_ctype->has_prototype);
    llvm::GlobalValue::LinkageTypes linkage =
        sym->storage_class == StorageClass::STATIC
            ? llvm::Function::InternalLinkage
            : llvm::Function::ExternalLinkage;
    llvm::Function* fn =
        llvm::Function::Create(ft, linkage, fn_name, module.get());
    apply_indirect_result_attributes(fn, 0, func_ctype->ret_type);

    if (!sym->uid.empty()) {
        named_values[mangleCIdentifier(sym->uid)] = fn;
    }
    return fn;
}

std::string ASTToLLVM::mangleCIdentifier(const std::string& original) {
    if (original.empty()) return "C.anon";

    std::stringstream mangled;
    mangled << "C."; // Namespace prefix for C identifiers

    for (size_t i = 0; i < original.length(); ++i) {
        char c = original[i];

        // LLVM identifiers allow alphanumeric, '.', '_', '$', and '-'
        // However, C identifiers only use alphanumeric and '_'
        if (std::isalnum(static_cast<unsigned char>(c)) || c == '_') {
            // Check if the first character is a digit (illegal as start of LLVM unquoted ID)
            if (i == 0 && std::isdigit(static_cast<unsigned char>(c))) {
                mangled << "_hex" << std::hex << std::setw(2) << std::setfill('0') << (int)c;
            } else {
                mangled << c;
            }
        } else {
            // Escape special characters as _XX (hex)
            mangled << "_hex" << std::hex << std::setw(2) << std::setfill('0') << (int)(unsigned char)c;
        }
    }
    mangled << ".";

    return mangled.str();
}

llvm::Type* ASTToLLVM::convert_param_type(const QualType& param) {
    auto canonical = desugar_type(param, ast_ctx.get());
    // C standard: array parameters decay to pointers in function types
    if (canonical->kind == TypeKind::Array) {
        return llvm::PointerType::get(*context, 0);
    }
    // C standard: function parameters decay to pointers to functions
    if (canonical->kind == TypeKind::Function) {
        return llvm::PointerType::get(*context, 0);
    }
    // C++ references are ABI-lowered as pointers.
    if (canonical->kind == TypeKind::Reference) {
        return llvm::PointerType::get(*context, 0);
    }
    if (llvm::Type* abi_type = get_direct_aggregate_parameter_abi_type(canonical)) {
        return abi_type;
    }
    // Very large aggregates are lowered as indirect parameters. Callers create
    // an explicit copy temporary so we avoid huge by-value IR arguments.
    if (pass_aggregate_by_reference(canonical)) {
        return llvm::PointerType::get(*context, 0);
    }
    return convert_type(canonical.get_shared());
}

bool ASTToLLVM::pass_aggregate_by_reference(const QualType& param) const {
    auto canonical = desugar_type(param, ast_ctx.get());
    if (!canonical || canonical->kind != TypeKind::Object) {
        return false;
    }
    auto rec = canonical.as_shared<ObjectType>();
    if (!rec || rec->isIncomplete()) {
        return false;
    }
    if (target && target->arch == TargetArch::AARCH64 &&
        target->os == TargetOS::MACOS) {
        return rec->getWidthBytes() > 16;
    }
    constexpr size_t kByRefAggregateThresholdBytes = 4096;
    return rec->getWidthBytes() > kByRefAggregateThresholdBytes;
}

llvm::Type* ASTToLLVM::get_direct_aggregate_parameter_abi_type(
    const QualType& param) const {
    if (!target || target->arch != TargetArch::AARCH64 ||
        target->os != TargetOS::MACOS) {
        return nullptr;
    }

    auto canonical = desugar_type(param, ast_ctx.get());
    if (!canonical || canonical->kind != TypeKind::Object) {
        return nullptr;
    }

    auto record = canonical.as_shared<ObjectType>();
    if (!record || record->isIncomplete()) {
        return nullptr;
    }

    std::size_t width_bytes =
        static_cast<std::size_t>(std::max<int64_t>(1, record->getWidthBytes()));
    if (width_bytes > 16) {
        return nullptr;
    }

    BuiltinTypes hfa_kind = BuiltinTypes::Void;
    unsigned hfa_count = 0;
    if (collect_darwin_hfa_members(canonical, ast_ctx.get(), target.get(), hfa_kind,
                                   hfa_count)) {
        llvm::Type* element_type =
            const_cast<ASTToLLVM*>(this)->convert_type(type_ctx->get_builtin(hfa_kind));
        if (element_type) {
            return llvm::ArrayType::get(element_type, hfa_count);
        }
    }

    std::size_t slot_count = (width_bytes + 7) / 8;
    if (slot_count <= 1) {
        return llvm::Type::getInt64Ty(*context);
    }
    return llvm::ArrayType::get(llvm::Type::getInt64Ty(*context), slot_count);
}

bool ASTToLLVM::has_direct_aggregate_parameter_abi(const QualType& param) const {
    return get_direct_aggregate_parameter_abi_type(param) != nullptr;
}

bool ASTToLLVM::return_aggregate_indirectly(const QualType& ret) const {
    if (!target || target->arch != TargetArch::AARCH64 ||
        target->os != TargetOS::MACOS) {
        return false;
    }

    auto canonical = desugar_type(ret, ast_ctx.get());
    if (!canonical || canonical->kind != TypeKind::Object) {
        return false;
    }

    auto object_type = canonical.as_shared<ObjectType>();
    if (!object_type || object_type->isIncomplete()) {
        return false;
    }

    return object_type->getWidthBytes() > 16;
}

llvm::Type* ASTToLLVM::convert_function_return_type(const QualType& ret) {
    if (return_aggregate_indirectly(ret)) {
        return llvm::Type::getVoidTy(*context);
    }
    return convert_type(ret.get_shared());
}

unsigned ASTToLLVM::prepend_indirect_result_parameter(
    std::vector<llvm::Type*>& param_types,
    const QualType& ret) {
    if (!return_aggregate_indirectly(ret)) {
        return 0;
    }
    param_types.insert(param_types.begin(), llvm::PointerType::get(*context, 0));
    return 1;
}

void ASTToLLVM::apply_indirect_result_attributes(llvm::Function* fn,
                                                 unsigned arg_index,
                                                 const QualType& ret) {
    if (!fn || !return_aggregate_indirectly(ret)) {
        return;
    }

    llvm::Type* result_type = convert_type(ret.get_shared());
    if (!result_type) {
        return;
    }

    fn->addParamAttr(arg_index,
                     llvm::Attribute::getWithStructRetType(*context, result_type));
    fn->addParamAttr(arg_index,
                     llvm::Attribute::getWithAlignment(
                         *context, module->getDataLayout().getABITypeAlign(result_type)));
}

void ASTToLLVM::apply_indirect_result_attributes(llvm::CallBase* call,
                                                 unsigned arg_index,
                                                 const QualType& ret) {
    if (!call || !return_aggregate_indirectly(ret)) {
        return;
    }

    llvm::Type* result_type = convert_type(ret.get_shared());
    if (!result_type) {
        return;
    }

    call->addParamAttr(arg_index,
                       llvm::Attribute::getWithStructRetType(*context, result_type));
    call->addParamAttr(arg_index,
                       llvm::Attribute::getWithAlignment(
                           *context, module->getDataLayout().getABITypeAlign(result_type)));
}

llvm::AllocaInst* ASTToLLVM::create_indirect_result_slot(llvm::Function* function,
                                                         const QualType& ret,
                                                         const char* name) {
    if (!function || !return_aggregate_indirectly(ret)) {
        return nullptr;
    }

    llvm::Type* result_type = convert_type(ret.get_shared());
    if (!result_type) {
        return nullptr;
    }

    auto* slot = create_entry_alloca(function, result_type, nullptr, name);
    if (!slot) {
        return nullptr;
    }
    slot->setAlignment(module->getDataLayout().getABITypeAlign(result_type));
    return slot;
}

llvm::Value* ASTToLLVM::load_aggregate_memory_as_abi_value(
    llvm::Value* src_addr,
    const QualType& aggregate_type,
    llvm::Type* abi_type,
    SrcLoc loc,
    const char* context_name) {
    auto canonical = desugar_type(aggregate_type, ast_ctx.get());
    auto record = canonical.as_shared<ObjectType>();
    if (!src_addr || !record || record->isIncomplete() || !abi_type) {
        error(std::string(context_name) +
                  ": invalid aggregate ABI load materialization",
              loc);
    }

    llvm::Function* function = builder.GetInsertBlock()->getParent();
    auto* abi_tmp = create_entry_alloca(function, abi_type, nullptr, "agg.abi.load.tmp");
    if (!abi_tmp) {
        error(std::string(context_name) + ": failed to allocate aggregate ABI load temporary",
              loc);
    }

    llvm::Type* aggregate_llvm_type = convert_type(canonical.get_shared());
    if (!aggregate_llvm_type) {
        error(std::string(context_name) + ": failed to lower aggregate type", loc);
    }

    llvm::Align abi_align = module->getDataLayout().getABITypeAlign(abi_type);
    abi_tmp->setAlignment(abi_align);
    builder.CreateStore(llvm::Constant::getNullValue(abi_type), abi_tmp);

    uint64_t copy_size = static_cast<uint64_t>(
        std::max<int64_t>(0, record->getWidthBytes()));
    if (copy_size > 0) {
        llvm::Align aggregate_align =
            module->getDataLayout().getABITypeAlign(aggregate_llvm_type);
        builder.CreateMemCpy(
            abi_tmp, llvm::MaybeAlign(abi_align), src_addr,
            llvm::MaybeAlign(aggregate_align), copy_size);
    }

    auto* load = builder.CreateLoad(abi_type, abi_tmp, "agg.abi");
    load->setAlignment(abi_align);
    return load;
}

void ASTToLLVM::store_abi_value_into_aggregate_memory(llvm::Value* abi_value,
                                                      llvm::Value* dest_addr,
                                                      const QualType& aggregate_type,
                                                      SrcLoc loc,
                                                      const char* context_name) {
    auto canonical = desugar_type(aggregate_type, ast_ctx.get());
    auto record = canonical.as_shared<ObjectType>();
    if (!abi_value || !dest_addr || !record || record->isIncomplete()) {
        error(std::string(context_name) +
                  ": invalid aggregate ABI store materialization",
              loc);
    }

    llvm::Type* aggregate_llvm_type = convert_type(canonical.get_shared());
    if (!aggregate_llvm_type) {
        error(std::string(context_name) + ": failed to lower aggregate type", loc);
    }

    llvm::Function* function = builder.GetInsertBlock()->getParent();
    llvm::Type* abi_type = abi_value->getType();
    auto* abi_tmp =
        create_entry_alloca(function, abi_type, nullptr, "agg.abi.store.tmp");
    if (!abi_tmp) {
        error(std::string(context_name) +
                  ": failed to allocate aggregate ABI store temporary",
              loc);
    }

    llvm::Align abi_align = module->getDataLayout().getABITypeAlign(abi_type);
    abi_tmp->setAlignment(abi_align);
    auto* store = builder.CreateStore(abi_value, abi_tmp);
    store->setAlignment(abi_align);

    uint64_t copy_size = static_cast<uint64_t>(
        std::max<int64_t>(0, record->getWidthBytes()));
    if (copy_size == 0) {
        return;
    }

    llvm::Align aggregate_align =
        module->getDataLayout().getABITypeAlign(aggregate_llvm_type);
    builder.CreateMemCpy(dest_addr, llvm::MaybeAlign(aggregate_align), abi_tmp,
                         llvm::MaybeAlign(abi_align), copy_size);
}

llvm::Type* ASTToLLVM::convert_type(std::shared_ptr<CType> ctype) {
    ctype = desugar_type(ctype, ast_ctx.get());
    if (!ctype) {
        // Default to int if no type provided (legacy behavior)
        return llvm::Type::getInt32Ty(*context);
    }

    if (auto builtin = dyn_cast_shared<BuiltinType>(ctype)) {
        switch (builtin->builtin_kind) {
            case BuiltinTypes::Void:
                return llvm::Type::getVoidTy(*context);
            case BuiltinTypes::NullPtr:
                return llvm::PointerType::get(*context, 0);
            case BuiltinTypes::Bool:
                return llvm::Type::getInt1Ty(*context);
            case BuiltinTypes::Char:
            case BuiltinTypes::UChar:
                return llvm::Type::getInt8Ty(*context);
            case BuiltinTypes::Short:
            case BuiltinTypes::UShort:
                return llvm::Type::getInt16Ty(*context);
            case BuiltinTypes::Int:
            case BuiltinTypes::UInt:
                return llvm::Type::getInt32Ty(*context);
            case BuiltinTypes::Long:
            case BuiltinTypes::ULong:
            case BuiltinTypes::LongLong:
            case BuiltinTypes::ULongLong:
                return llvm::Type::getInt64Ty(*context);
            case BuiltinTypes::Int128:
            case BuiltinTypes::UInt128:
                return llvm::Type::getInt128Ty(*context);
            case BuiltinTypes::Float16:
                return llvm::Type::getHalfTy(*context);
            case BuiltinTypes::Float:
                return llvm::Type::getFloatTy(*context);
            case BuiltinTypes::Double:
                return llvm::Type::getDoubleTy(*context);
            case BuiltinTypes::LongDouble:
                switch (target->long_double_format) {
                    case LongDoubleFormat::IEEE_DOUBLE:
                        return llvm::Type::getDoubleTy(*context);
                    case LongDoubleFormat::X87_EXTENDED:
                        return llvm::Type::getX86_FP80Ty(*context);
                    case LongDoubleFormat::IEEE_QUAD:
                        return llvm::Type::getFP128Ty(*context);
                }
            default:
                error("convert_type(): Unsupported builtin type");
                return nullptr;
        }
    }

    if (auto ptr = dyn_cast_shared<PointerType>(ctype)) {
        return llvm::PointerType::get(*context, 0);
    }

    if (auto mem_ptr = dyn_cast_shared<MemberPointerType>(ctype)) {
        auto member_type = desugar_type(mem_ptr->member_type, ast_ctx.get());
        if (member_type && member_type->kind == TypeKind::Function) {
            return llvm::StructType::get(
                *context,
                {llvm::PointerType::get(*context, 0),
                 llvm::Type::getInt64Ty(*context)},
                /*isPacked=*/false);
        }
        return llvm::Type::getInt64Ty(*context);
    }

    if (auto ref = dyn_cast_shared<ReferenceType>(ctype)) {
        (void)ref;
        return llvm::PointerType::get(*context, 0);
    }

    if (auto cpp_type_info = dyn_cast_shared<CppTypeInfoType>(ctype)) {
        (void)cpp_type_info;
        return llvm::PointerType::get(*context, 0);
    }

    if (auto blk = dyn_cast_shared<BlockPointerType>(ctype)) {
        return llvm::PointerType::get(*context, 0);
    }

    if (auto arr = dyn_cast_shared<ArrayType>(ctype)) {
        llvm::Type* elemType = convert_type(arr->element_type);
        if (arr->size_kind == ArraySizeKind::Variable) {
            // VLAs are allocated at runtime via alloca. For type purposes,
            // treat as a zero-length array (the actual size is runtime-determined).
            return llvm::ArrayType::get(elemType, 0);
        }
        size_t ret_size = 0; // for purposes of codegen, int[] and int[0] should be mostly equiv.
        if (arr->size_kind == ArraySizeKind::Constant && arr->size.has_value()) {
            ret_size = *arr->size;
        }
        return llvm::ArrayType::get(elemType, ret_size);
    }

    if (auto vec = dyn_cast_shared<VectorType>(ctype)) {
        llvm::Type* elemType = convert_type(vec->element_type);
        return llvm::FixedVectorType::get(elemType, vec->num_elements);
    }

    if (auto complex = dyn_cast_shared<ComplexType>(ctype)) {
        llvm::Type* elemType = convert_type(complex->element_type);
        return llvm::StructType::get(*context, {elemType, elemType}, /*isPacked=*/false);
    }

    if (auto rec = dyn_cast_shared<ObjectType>(ctype)) {
        // Cache by declaration identity where available.
        std::string record_tag;
        if (auto* decl = rec->get_decl()) {
            record_tag = decl->get_tag_name();
        }
        std::string llvm_name = (rec->is_union ? "union." : "struct.") + record_tag;
        const void* cache_key = record_cache_key(rec.get());
        llvm::StructType* cached_struct = nullptr;
        {
            auto it = struct_type_cache.find(cache_key);
            if (it != struct_type_cache.end()) {
                cached_struct = it->second;
            }
        }

        // Incomplete record type in declarations/prototypes: materialize an opaque LLVM struct.
        if (rec->isIncomplete()) {
            if (cached_struct) {
                return cached_struct;
            }
            auto* opaque = llvm::StructType::create(*context, llvm_name);
            struct_type_cache[cache_key] = opaque;
            return opaque;
        }

        // Build LLVM struct type from fields
        std::vector<llvm::Type*> field_types;
        const auto& rec_fields = rec->semantic_fields();
        field_types.reserve(rec_fields.size());
        llvm::StructType* struct_type = cached_struct;
        if (!struct_type) {
            struct_type = llvm::StructType::create(*context, llvm_name);
        }

        if (rec->is_union) {
            size_t size_in_bytes = rec->getWidthBytes();
            llvm::Type* byteType = llvm::Type::getInt8Ty(*context);
            llvm::Type* unionStorage = nullptr;
            const llvm::DataLayout& DL = module->getDataLayout();
            std::unordered_set<std::size_t> union_pointer_offsets;

            for (const auto& field : rec_fields) {
                llvm::Type* member_ty = convert_type(field.type.get_shared());
                if (!member_ty || !llvm_type_contains_pointer(member_ty)) {
                    continue;
                }
                auto member_offsets = collect_llvm_pointer_offsets(member_ty, DL);
                union_pointer_offsets.insert(member_offsets.begin(), member_offsets.end());
            }

            // Prefer a full-size aggregate member that contains pointer fields
            // so relocatable constants inside that member survive lowering
            // (e.g. QTAILQ heads, FFmpeg parser unions), but only when that
            // storage shape can preserve every pointer-bearing offset used by
            // the other union members.
            for (const auto& field : rec_fields) {
                llvm::Type* candidate = convert_type(field.type.get_shared());
                if (!candidate || candidate->isPointerTy()) {
                    continue;
                }
                size_t candidate_bytes = DL.getTypeAllocSize(candidate);
                if (candidate_bytes == size_in_bytes &&
                    llvm_type_contains_pointer(candidate) &&
                    llvm_type_covers_pointer_offsets(
                        candidate, union_pointer_offsets, DL)) {
                    unionStorage = candidate;
                    break;
                }
            }

            // Otherwise, prefer direct pointer storage so plain pointer union
            // members still keep relocations without byte-packing.
            if (!unionStorage) {
                for (const auto& field : rec_fields) {
                    llvm::Type* candidate = convert_type(field.type.get_shared());
                    if (candidate && candidate->isPointerTy() &&
                        llvm_type_covers_pointer_offsets(
                            candidate, union_pointer_offsets, DL)) {
                        unionStorage = candidate;
                        break;
                    }
                }
            }

            if (!unionStorage) {
                unionStorage = build_union_pointer_storage_type(
                    *context, DL, size_in_bytes, union_pointer_offsets);
            }

            field_types.push_back(unionStorage);
            size_t storage_bytes = DL.getTypeAllocSize(unionStorage);
            if (size_in_bytes > storage_bytes) {
                field_types.push_back(
                    llvm::ArrayType::get(byteType, size_in_bytes - storage_bytes));
            }

            if (struct_type->isOpaque()) {
                struct_type->setBody(field_types, /*isPacked=*/false);
            }
            struct_type_cache[cache_key] = struct_type;
            return struct_type;
        } else {
            bool uses_byte_layout = record_uses_byte_layout(rec.get());

            if (uses_byte_layout) {
                // Prefer a concrete field+padding layout for non-overlapping
                // bitfield records. This preserves relocatable pointer fields
                // in static initializers while member accesses still use byte
                // offsets. If offsets overlap (bitfield storage windows sharing
                // bytes with regular fields), fall back to raw byte storage.
                bool can_use_component_layout =
                    !rec->is_packed && rec->pack_alignment == 0;
                size_t size_in_bytes = rec->getWidthBytes();
                size_t current_offset = 0;
                std::vector<std::pair<size_t, size_t>> emitted_bitfield_windows;

                auto window_emitted = [&](size_t off, size_t sz) {
                    for (const auto& [existing_off, existing_sz] : emitted_bitfield_windows) {
                        if (existing_off == off && existing_sz == sz) {
                            return true;
                        }
                    }
                    return false;
                };

                if (can_use_component_layout) {
                    for (const auto& field : rec_fields) {
                        size_t field_offset = field.offset;
                        size_t field_size = 0;
                        llvm::Type* llvm_field_ty = nullptr;

                        if (field.is_bitfield) {
                            if (field.bit_width == 0 || field.storage_size == 0) {
                                continue;
                            }
                            field_size = field.storage_size / 8;
                            if (field_size == 0) {
                                continue;
                            }
                            if (window_emitted(field_offset, field_size)) {
                                continue;
                            }
                            llvm_field_ty = llvm::IntegerType::get(*context, field.storage_size);
                        } else if (field.is_base_subobject ||
                                   field.storage_size_override > 0) {
                            field_size = object_field_storage_size_bytes(field);
                            llvm_field_ty = llvm::ArrayType::get(
                                llvm::Type::getInt8Ty(*context),
                                field_size);
                        } else {
                            field_size = object_field_storage_size_bytes(field);
                            if (field_size == 0) {
                                field_size = 1;
                            }
                            llvm_field_ty = convert_type(field.type.get_shared());
                        }

                        if (field_offset < current_offset) {
                            can_use_component_layout = false;
                            break;
                        }
                        if (field_offset > current_offset) {
                            field_types.push_back(
                                llvm::ArrayType::get(llvm::Type::getInt8Ty(*context),
                                                     field_offset - current_offset));
                            current_offset = field_offset;
                        }
                        field_types.push_back(llvm_field_ty);
                        current_offset += field_size;

                        if (field.is_bitfield) {
                            emitted_bitfield_windows.push_back({field_offset, field_size});
                        }
                    }
                }

                if (can_use_component_layout) {
                    if (size_in_bytes > current_offset) {
                        field_types.push_back(
                            llvm::ArrayType::get(llvm::Type::getInt8Ty(*context),
                                                 size_in_bytes - current_offset));
                    }
                    if (struct_type->isOpaque()) {
                        struct_type->setBody(field_types, /*isPacked=*/false);
                    }
                } else {
                    // Raw byte-storage fallback for overlapping layouts.
                    // To preserve the correct alignment for when this struct
                    // is embedded in another struct, use an alignment-forcing
                    // first element. Also carve out naturally aligned pointer
                    // fields so static initializers can carry relocations.
                    size_t alignment = rec->getAlignment();
                    llvm::Type* byteType = llvm::Type::getInt8Ty(*context);
                    const llvm::DataLayout& DL = module->getDataLayout();
                    size_t ptr_size = DL.getPointerSize();
                    size_t ptr_align = DL.getPointerABIAlignment(0).value();

                    field_types.clear();
                    size_t prefix_bytes = 0;
                    if (alignment > 1 && size_in_bytes >= alignment) {
                        llvm::Type* alignType = nullptr;
                        switch (alignment) {
                            case 2:  alignType = llvm::Type::getInt16Ty(*context); break;
                            case 4:  alignType = llvm::Type::getInt32Ty(*context); break;
                            case 8:  alignType = llvm::Type::getInt64Ty(*context); break;
                            default: alignType = llvm::IntegerType::get(*context, alignment * 8); break;
                        }
                        field_types.push_back(alignType);
                        prefix_bytes = alignment;
                    }

                    std::vector<const ObjectType::Field*> reloc_ptr_fields;
                    for (const auto& field : rec_fields) {
                        if (field.is_bitfield || field.type->kind != TypeKind::Pointer) {
                            continue;
                        }
                        size_t off = field.offset;
                        size_t sz = static_cast<size_t>(field.type->getWidthBytes());
                        if (sz != ptr_size || off < prefix_bytes || (off + sz) > size_in_bytes) {
                            continue;
                        }
                        if (ptr_align > 0 && (off % ptr_align) != 0) {
                            continue;
                        }
                        reloc_ptr_fields.push_back(&field);
                    }
                    std::sort(reloc_ptr_fields.begin(), reloc_ptr_fields.end(),
                              [](const ObjectType::Field* lhs, const ObjectType::Field* rhs) {
                                  return lhs->offset < rhs->offset;
                              });

                    size_t cursor = prefix_bytes;
                    for (const auto* ptr_field : reloc_ptr_fields) {
                        if (ptr_field->offset < cursor) {
                            continue;
                        }
                        if (ptr_field->offset > cursor) {
                            field_types.push_back(
                                llvm::ArrayType::get(byteType, ptr_field->offset - cursor));
                            cursor = ptr_field->offset;
                        }
                        field_types.push_back(convert_type(ptr_field->type.get_shared()));
                        cursor += ptr_size;
                    }

                    if (cursor < size_in_bytes) {
                        field_types.push_back(llvm::ArrayType::get(byteType, size_in_bytes - cursor));
                    } else {
                        // No usable pointer carve-outs.
                        if (field_types.empty()) {
                            field_types.push_back(llvm::ArrayType::get(byteType, size_in_bytes));
                        } else if (cursor == prefix_bytes && size_in_bytes > prefix_bytes) {
                            field_types.push_back(llvm::ArrayType::get(byteType, size_in_bytes - prefix_bytes));
                        }
                    }

                    if (field_types.empty()) {
                        field_types.push_back(llvm::ArrayType::get(byteType, size_in_bytes));
                    }
                    if (struct_type->isOpaque()) {
                        struct_type->setBody(field_types, /*isPacked=*/false);
                    }
                }
            } else {
                // No bitfields: lower using semantic field offsets/size, so
                // explicit padding and over-alignment are preserved.
                size_t current_offset = 0;
                for (const auto& field : rec_fields) {
                    if (field.offset > current_offset) {
                        size_t pad = field.offset - current_offset;
                        field_types.push_back(
                            llvm::ArrayType::get(llvm::Type::getInt8Ty(*context), pad));
                        current_offset += pad;
                    }
                    llvm::Type* llvm_field_ty = nullptr;
                    if (field.is_base_subobject || field.storage_size_override > 0) {
                        llvm_field_ty = llvm::ArrayType::get(
                            llvm::Type::getInt8Ty(*context),
                            object_field_storage_size_bytes(field));
                    } else {
                        llvm_field_ty = convert_type(field.type);
                    }
                    field_types.push_back(llvm_field_ty);
                    current_offset += object_field_storage_size_bytes(field);
                }
                size_t total_size = rec->getWidthBytes();
                if (total_size < current_offset) {
                    total_size = current_offset;
                }
                if (total_size > current_offset) {
                    size_t tail_pad = total_size - current_offset;
                    field_types.push_back(
                        llvm::ArrayType::get(llvm::Type::getInt8Ty(*context), tail_pad));
                }
                if (struct_type->isOpaque()) {
                    struct_type->setBody(field_types, /*isPacked=*/false);
                }
            }

            struct_type_cache[cache_key] = struct_type;
            return struct_type;
        }
    }

    if (auto enm = dyn_cast_shared<EnumType>(ctype)) {
        return convert_type(enm->semantic_underlying_type());
    }

    // Bare function types should be treated as pointer-to-function
    // (e.g., function type parameters in typedef'd function types that
    // weren't decayed by sema because they're not direct function declarations).
    if (ctype->kind == TypeKind::Function) {
        return llvm::PointerType::get(*context, 0);
    }

    error("convert_type(): Unsupported type kind: " + ctype->to_string());
    return nullptr;
}
llvm::Value* ASTToLLVM::cast_llvm_type(llvm::Value * val, llvm::Type * destType, bool isUnsigned) {
    // isUnsigned with integer types - do we want to signextend val into desttype?
    // isUnsigned with floating types - do we want to convert val into a signed or unsigned integer?
    llvm::Type *srcType = val->getType();

    if (srcType == destType) return val;
    // C _Bool semantics: convert to 0/1 using "!= 0", not bit truncation.
    if (destType->isIntegerTy(1)) {
        if (srcType->isIntegerTy()) {
            return builder.CreateICmpNE(
                val, llvm::ConstantInt::get(srcType, 0), "to.bool");
        }
        if (srcType->isFloatingPointTy()) {
            return builder.CreateFCmpUNE(
                val, llvm::ConstantFP::get(srcType, 0.0), "to.bool");
        }
        if (srcType->isPointerTy()) {
            return builder.CreateIsNotNull(val, "to.bool");
        }
    }

    // Complex -> scalar: convert using the real component.
    if (srcType->isStructTy() && !destType->isStructTy()) {
        auto* srcST = llvm::cast<llvm::StructType>(srcType);
        if (srcST->getNumElements() == 2 &&
            srcST->getElementType(0) == srcST->getElementType(1)) {
            llvm::Type* elemTy = srcST->getElementType(0);
            if (elemTy->isFloatingPointTy() || elemTy->isIntegerTy()) {
                llvm::Value* realPart =
                    builder.CreateExtractValue(val, {0}, "complex.to.scalar.real");
                if (realPart->getType() == destType) return realPart;
                return cast_llvm_type(realPart, destType, isUnsigned);
            }
        }
    }

    if (srcType->isIntegerTy() && destType->isIntegerTy()) {
        unsigned srcWidth = srcType->getIntegerBitWidth();
        unsigned destWidth = destType->getIntegerBitWidth();

        if (destWidth > srcWidth) {
            if (isUnsigned) {
                return builder.CreateZExt(val, destType, "zext");
            } else {
                return builder.CreateSExt(val, destType, "sext");

            }
        } else if (destWidth < srcWidth) {
            // Truncation
            return builder.CreateTrunc(val, destType, "trunc");
        }
    }
    // Pointer to Integer
    if (srcType->isPointerTy() && destType->isIntegerTy()) {
        return builder.CreatePtrToInt(val, destType, "ptrtoint");
    }
    // Integer to Pointer
    if (srcType->isIntegerTy() && destType->isPointerTy()) {
        llvm::DataLayout dl = module->getDataLayout();
        unsigned ptr_bits = dl.getPointerSizeInBits(0);
        auto* ptr_int_ty = llvm::IntegerType::get(*context, ptr_bits);
        llvm::Value* int_val = val;
        unsigned src_bits = srcType->getIntegerBitWidth();
        if (src_bits < ptr_bits) {
            int_val = isUnsigned
                ? builder.CreateZExt(int_val, ptr_int_ty, "inttoptr.zext")
                : builder.CreateSExt(int_val, ptr_int_ty, "inttoptr.sext");
        } else if (src_bits > ptr_bits) {
            int_val = builder.CreateTrunc(int_val, ptr_int_ty, "inttoptr.trunc");
        }
        return builder.CreateIntToPtr(int_val, destType, "inttoptr");
    }
    // Pointer to Pointer (bitcast - though with opaque pointers this is a no-op usually)
    if (srcType->isPointerTy() && destType->isPointerTy()) {
        return builder.CreateBitCast(val, destType, "bitcast");
    }

    // Floating point casts
    if (srcType->isFloatingPointTy() && destType->isFloatingPointTy()) {
        if (srcType->getTypeID() > destType->getTypeID()) {
            return builder.CreateFPTrunc(val, destType, "fptrunc");
        } else {
            return builder.CreateFPExt(val, destType, "fpext");
        }
    }

    // Integer to Float
    if (srcType->isIntegerTy() && destType->isFloatingPointTy()) {
        if (isUnsigned) {
            return builder.CreateUIToFP(val, destType, "uitofp");
        } else {
            return builder.CreateSIToFP(val, destType, "sitofp");
        }
    }

    // Float to Integer
    if (srcType->isFloatingPointTy() && destType->isIntegerTy()) {
        if (isUnsigned) {
            return builder.CreateFPToUI(val, destType, "fptoui");
        } else {
            return builder.CreateFPToSI(val, destType, "fptosi");
        }
    }

    // Vector-to-vector bitcast (same total size, different element types)
    if (srcType->isVectorTy() && destType->isVectorTy()) {
        return builder.CreateBitCast(val, destType, "vec_bitcast");
    }

    // Scalar to complex: { real = val, imag = 0 }
    if (!srcType->isStructTy() && destType->isStructTy()) {
        auto* destST = llvm::cast<llvm::StructType>(destType);
        if (destST->getNumElements() == 2 && destST->getElementType(0) == destST->getElementType(1)) {
            auto* elemTy = destST->getElementType(0);
            llvm::Value* realPart = val;
            if (srcType != elemTy) {
                realPart = cast_llvm_type(val, elemTy, isUnsigned);
            }
            llvm::Value* imagZero = nullptr;
            if (elemTy->isFloatingPointTy()) {
                imagZero = llvm::ConstantFP::get(elemTy, 0.0);
            } else if (elemTy->isIntegerTy()) {
                imagZero = llvm::ConstantInt::get(elemTy, 0);
            } else {
                std::string elemStr;
                llvm::raw_string_ostream elemOS(elemStr);
                elemTy->print(elemOS);
                error("cast_llvm_type(): unsupported complex element type " + elemStr);
                return nullptr;
            }
            llvm::Value* result = llvm::UndefValue::get(destType);
            result = builder.CreateInsertValue(result, realPart, {0}, "complex.real");
            result = builder.CreateInsertValue(result, imagZero, {1}, "complex.imag");
            return result;
        }
    }

    // Struct-to-struct with identical layout (e.g. same anonymous struct via typedef)
    if (srcType->isStructTy() && destType->isStructTy()) {
        auto* srcST = llvm::cast<llvm::StructType>(srcType);
        auto* destST = llvm::cast<llvm::StructType>(destType);
        if (srcST->isLayoutIdentical(destST)) {
            // Store to a temp alloca and load back as the dest type (opaque pointers make this simple)
            llvm::Function* func = builder.GetInsertBlock()->getParent();
            llvm::IRBuilder<> tmpBuilder(&func->getEntryBlock(), func->getEntryBlock().begin());
            auto* alloca = tmpBuilder.CreateAlloca(srcType, nullptr, "struct.cast");
            builder.CreateStore(val, alloca);
            return builder.CreateLoad(destType, alloca, "struct.cast.load");
        }
        // Homogeneous 2-field struct cast (used by complex element widening/narrowing).
        if (srcST->getNumElements() == 2 && destST->getNumElements() == 2 &&
            srcST->getElementType(0) == srcST->getElementType(1) &&
            destST->getElementType(0) == destST->getElementType(1)) {
            llvm::Type* srcElemTy = srcST->getElementType(0);
            llvm::Type* dstElemTy = destST->getElementType(0);
            llvm::Value* realPart = builder.CreateExtractValue(val, {0}, "struct.cast.real");
            llvm::Value* imagPart = builder.CreateExtractValue(val, {1}, "struct.cast.imag");
            if (srcElemTy != dstElemTy) {
                realPart = cast_llvm_type(realPart, dstElemTy, isUnsigned);
                imagPart = cast_llvm_type(imagPart, dstElemTy, isUnsigned);
            }
            llvm::Value* out = llvm::UndefValue::get(destType);
            out = builder.CreateInsertValue(out, realPart, {0}, "struct.cast.out.real");
            out = builder.CreateInsertValue(out, imagPart, {1}, "struct.cast.out.imag");
            return out;
        }
    }

    // Vector to scalar: extract element 0
    if (srcType->isVectorTy() && !destType->isVectorTy()) {
        auto srcBits = module->getDataLayout().getTypeSizeInBits(srcType);
        auto destBits = module->getDataLayout().getTypeSizeInBits(destType);
        if (srcBits == destBits) {
            return builder.CreateBitCast(val, destType, "vec_to_scalar");
        }
        auto* vecTy = llvm::cast<llvm::FixedVectorType>(srcType);
        auto* elem = builder.CreateExtractElement(val, (uint64_t)0, "vec_extract");
        if (elem->getType() == destType) return elem;
        return cast_llvm_type(elem, destType, isUnsigned);
    }

    // Scalar to vector: bitcast if same size, splat for 1-element, or store/load
    if (!srcType->isVectorTy() && destType->isVectorTy()) {
        auto* vecTy = llvm::cast<llvm::FixedVectorType>(destType);
        if (vecTy->getNumElements() == 1) {
            auto* castedSrc = srcType == vecTy->getElementType() ? val
                : cast_llvm_type(val, vecTy->getElementType(), isUnsigned);
            return builder.CreateInsertElement(
                llvm::UndefValue::get(destType), castedSrc, (uint64_t)0, "vec_insert");
        }
        // Same bit size: bitcast (reinterpret bits as vector)
        auto srcBits = module->getDataLayout().getTypeSizeInBits(srcType);
        auto destBits = module->getDataLayout().getTypeSizeInBits(destType);
        if (srcBits == destBits) {
            return builder.CreateBitCast(val, destType, "scalar_to_vec");
        }
        // Different size: extend/trunc to matching integer, then bitcast
        auto* intTy = llvm::IntegerType::get(*context, destBits);
        llvm::Value* sized = nullptr;
        if (srcType->isIntegerTy()) {
            if (srcBits < destBits) {
                sized = isUnsigned ? builder.CreateZExt(val, intTy) : builder.CreateSExt(val, intTy);
            } else {
                sized = builder.CreateTrunc(val, intTy);
            }
        } else {
            sized = builder.CreateBitCast(val, intTy);
        }
        return builder.CreateBitCast(sized, destType, "scalar_to_vec");
    }

    // General fallback: store/load through alloca for same-size types
    // (e.g., pointer to union, integer to struct)
    if (srcType->isSized() && destType->isSized()) {
        auto srcBits = module->getDataLayout().getTypeSizeInBits(srcType);
        auto destBits = module->getDataLayout().getTypeSizeInBits(destType);
        if (srcBits == destBits) {
            llvm::Function* func = builder.GetInsertBlock()->getParent();
            llvm::IRBuilder<> tmpBuilder(&func->getEntryBlock(), func->getEntryBlock().begin());
            auto* alloca = tmpBuilder.CreateAlloca(srcType, nullptr, "cast.tmp");
            builder.CreateStore(val, alloca);
            return builder.CreateLoad(destType, alloca, "cast.load");
        }
    }

    std::string srcStr, destStr;
    llvm::raw_string_ostream srcOS(srcStr), destOS(destStr);
    srcType->print(srcOS); destType->print(destOS);
        error("cast_llvm_type(): unhandled cast from " + srcStr + " to " + destStr);
        return nullptr;
    }
    
    void ASTToLLVM::optimize() {
        const bool run_pipeline =
            optimization_level == "1" ||
            optimization_level == "2" ||
            optimization_level == "3" ||
            optimization_level == "s" ||
            optimization_level == "z";
        if (!run_pipeline) return;
    
        llvm::LoopAnalysisManager LAM;
        llvm::FunctionAnalysisManager FAM;
        llvm::CGSCCAnalysisManager CGAM;
        llvm::ModuleAnalysisManager MAM;
    
        llvm::PassBuilder PB;
    
        PB.registerModuleAnalyses(MAM);
        PB.registerCGSCCAnalyses(CGAM);
        PB.registerFunctionAnalyses(FAM);
        PB.registerLoopAnalyses(LAM);
        PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);
    
        llvm::OptimizationLevel level;
        if (optimization_level == "1") level = llvm::OptimizationLevel::O1;
        else if (optimization_level == "2") level = llvm::OptimizationLevel::O2;
        else if (optimization_level == "3") level = llvm::OptimizationLevel::O3;
        else if (optimization_level == "s") level = llvm::OptimizationLevel::Os;
        else if (optimization_level == "z") level = llvm::OptimizationLevel::Oz;
        else level = llvm::OptimizationLevel::O0;
    
        llvm::ModulePassManager MPM = PB.buildPerModuleDefaultPipeline(level);
        MPM.run(*module, MAM);
    }

void ASTToLLVM::create_debug_info_for_function(FuncDecl* decl, llvm::Function* func) {
    if (!emit_debug_info || !di_builder || !sm) return;

    auto loc = sm->getLogicalLocation(decl->location);
    
    llvm::DIFile* file = di_cu->getFile(); 
    if (loc.file != file->getFilename()) {
         file = di_builder->createFile(loc.file, ".");
    }

    llvm::DISubprogram* sp = di_builder->createFunction(
        file,
        decl->name,
        decl->name, // linkage name
        file,
        loc.line,
        di_builder->createSubroutineType(di_builder->getOrCreateTypeArray({})), // TODO: proper type
        loc.line,
        llvm::DINode::FlagPrototyped,
        llvm::DISubprogram::SPFlagDefinition
    );
    func->setSubprogram(sp);
    // Push the subprogram scope for subsequent instructions
    builder.SetCurrentDebugLocation(llvm::DILocation::get(*context, loc.line, loc.column, sp));
}

void ASTToLLVM::emit_debug_location(Stmt* stmt) {
    if (!emit_debug_info || !di_builder || !stmt || !sm) return;
    if (stmt->location.isInvalid()) return;

    auto loc = sm->getLogicalLocation(stmt->location);
    if (loc.line == 0) return;

    // DILocation requires a DILocalScope (DISubprogram or DILexicalBlock), not a DICompileUnit.
    // If the current function doesn't have a subprogram, skip emitting a debug location.
    auto* sp = builder.GetInsertBlock()->getParent()->getSubprogram();
    if (!sp) return;
    builder.SetCurrentDebugLocation(llvm::DILocation::get(*context, loc.line, loc.column, sp));
}

llvm::DIType* ASTToLLVM::convert_debug_type(std::shared_ptr<CType> type) {
    if (!emit_debug_info || !di_builder || !type) return nullptr;
    
    // Basic types implementation
    if (auto builtin = dyn_cast_shared<BuiltinType>(type)) {
        std::string name;
        uint64_t size = 0;
        uint32_t align = 0;
        unsigned encoding = 0;

        switch (builtin->builtin_kind) {
            case BuiltinTypes::Int:
                name = "int"; size = 32; align = 32; encoding = llvm::dwarf::DW_ATE_signed; break;
            case BuiltinTypes::NullPtr:
                name = "decltype(nullptr)";
                size = 64;
                align = 64;
                encoding = llvm::dwarf::DW_ATE_address;
                break;
            case BuiltinTypes::Void:
                return nullptr; // Void has no DWARF type usually, or unspec type
            default:
                name = "unknown"; size = 32; align = 32; encoding = llvm::dwarf::DW_ATE_signed; break;
        }
        return di_builder->createBasicType(name, size, encoding);
    }
    return nullptr;
}
