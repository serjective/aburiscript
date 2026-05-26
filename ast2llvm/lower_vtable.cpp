#include "ast2llvm.h"
#include "const_lowering.h"
#include "../helpers/casting.h"
#include "../constexpr/consteval_compat.h"
#include "../numeric_utils.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include <array>
#include <algorithm>
#include <cstdlib>
#include <functional>
#include <limits>
#include <optional>
#include <unordered_set>

const ObjectDecl* ASTToLLVM::canonical_cpp_record_decl(const ObjectDecl* decl) const {
    if (!decl) {
        return nullptr;
    }
    auto record_type = decl->get_record_type();
    if (record_type) {
        if (auto* canonical_decl = dyn_cast<ObjectDecl>(record_type->get_decl())) {
            return canonical_decl;
        }
    }
    return decl;
}

const RecordSemanticState* ASTToLLVM::lookup_cpp_record_state(
    const ObjectDecl* decl) const {
    const ObjectDecl* canonical_decl = canonical_cpp_record_decl(decl);
    if (!canonical_decl) {
        return nullptr;
    }
    return record_semantics_cache_lookup(canonical_decl);
}

bool ASTToLLVM::cpp_record_uses_vptr(const RecordSemanticState* state) const {
    return state &&
           !state->is_incomplete &&
           (state->is_polymorphic || !state->virtual_bases.empty());
}

bool ASTToLLVM::using_itanium_cxx_object_abi() const {
    if (!(ast_ctx && ast_ctx->abi_policy)) {
        return true;
    }
    return ast_ctx->abi_policy->cxx_abi == CxxAbiKind::Itanium;
}

bool ASTToLLVM::ensure_supported_cpp_vtable_abi(
    SrcLoc loc,
    const std::string& context_name) const {
    if (using_itanium_cxx_object_abi()) {
        return true;
    }
    error(context_name +
              ": C++ RTTI/vtable lowering for Microsoft ABI is not implemented yet",
          loc);
    return false;
}

size_t ASTToLLVM::cpp_vtable_header_entries_for_context(
    const RecordSemanticState* context_state) const {
    if (!context_state) {
        return 0;
    }
    if (using_itanium_cxx_object_abi()) {
        // Itanium-compatible table header: [offset-to-top, typeinfo].
        return 2;
    }
    return 0;
}

// Itanium ABI vtable memory layout:
//   [vbase_offset_N, ..., vbase_offset_1, offset_to_top, typeinfo_ptr, slot_0, slot_1, ...]
//    <-- virtual base prefix -->  <-- header -->  <-- method slots -->
//                                  ^
//                                  address point (what the vptr points to)
// The address_point_index = num_virtual_bases + num_header_entries
// Method slots are at non-negative indices from the address point;
// virtual base offsets and the header are at negative indices.
size_t ASTToLLVM::cpp_vtable_address_point_index(
    const RecordSemanticState* context_state) const {
    if (!context_state) {
        return 0;
    }
    return context_state->virtual_bases.size() +
           cpp_vtable_header_entries_for_context(context_state);
}

size_t ASTToLLVM::cpp_vtable_emitted_slot_count(
    const RecordSemanticState* context_state) const {
    if (!context_state) {
        return 0;
    }
    size_t emitted_count = context_state->virtual_slots.size();
    for (const auto& slot : context_state->virtual_slots) {
        if (slot.is_destructor) {
            ++emitted_count;
        }
    }
    return emitted_count;
}

size_t ASTToLLVM::cpp_vtable_physical_slot_index(
    const RecordSemanticState* context_state,
    size_t semantic_slot_index,
    bool use_deleting_destructor_entry) const {
    if (!context_state) {
        return semantic_slot_index;
    }

    size_t physical_index = semantic_slot_index;
    size_t limit = std::min(semantic_slot_index, context_state->virtual_slots.size());
    for (size_t idx = 0; idx < limit; ++idx) {
        if (context_state->virtual_slots[idx].is_destructor) {
            ++physical_index;
        }
    }
    if (use_deleting_destructor_entry &&
        semantic_slot_index < context_state->virtual_slots.size() &&
        context_state->virtual_slots[semantic_slot_index].is_destructor) {
        ++physical_index;
    }
    return physical_index;
}

int64_t ASTToLLVM::cpp_vtable_virtual_base_relative_index(
    const RecordSemanticState* context_state,
    size_t virtual_base_index) const {
    if (!context_state) {
        return 0;
    }

    const size_t address_point_index = cpp_vtable_address_point_index(context_state);
    if (virtual_base_index >
            static_cast<size_t>(std::numeric_limits<int64_t>::max()) ||
        address_point_index >
            static_cast<size_t>(std::numeric_limits<int64_t>::max())) {
        return 0;
    }
    return static_cast<int64_t>(virtual_base_index) -
           static_cast<int64_t>(address_point_index);
}

std::string ASTToLLVM::make_cpp_vtable_group_key(
    const ObjectDecl* record_decl,
    const ObjectDecl* context_record_decl) const {
    const ObjectDecl* canonical_decl = canonical_cpp_record_decl(record_decl);
    const ObjectDecl* canonical_context_decl = canonical_cpp_record_decl(
        context_record_decl ? context_record_decl : record_decl);
    if (!canonical_decl || !canonical_context_decl) {
        return "";
    }
    return std::to_string(reinterpret_cast<uintptr_t>(canonical_decl)) + ":" +
           std::to_string(reinterpret_cast<uintptr_t>(canonical_context_decl));
}

std::optional<size_t> ASTToLLVM::get_cpp_vtt_entry_index(
    const ObjectDecl* record_decl,
    const ObjectDecl* context_record_decl) const {
    const ObjectDecl* canonical_decl = canonical_cpp_record_decl(record_decl);
    const ObjectDecl* canonical_context_decl = canonical_cpp_record_decl(context_record_decl);
    if (!canonical_decl || !canonical_context_decl) {
        return std::nullopt;
    }

    const RecordSemanticState* state = lookup_cpp_record_state(canonical_decl);
    if (!state || state->is_incomplete || state->virtual_bases.empty()) {
        return std::nullopt;
    }

    // Keep this traversal order in sync with `get_or_create_cpp_vtt`:
    // primary context first, then direct bases, then virtual bases.
    size_t index = 0;
    std::unordered_set<std::string> seen_context_keys;
    auto visit_context = [&](const ObjectDecl* context_decl) -> std::optional<size_t> {
        const ObjectDecl* canonical_context = canonical_cpp_record_decl(context_decl);
        if (!canonical_context) {
            return std::nullopt;
        }
        std::string key = make_cpp_vtable_group_key(canonical_decl, canonical_context);
        if (!seen_context_keys.insert(key).second) {
            return std::nullopt;
        }
        if (canonical_context == canonical_context_decl) {
            return index;
        }
        ++index;
        return std::nullopt;
    };

    if (auto found = visit_context(canonical_decl)) {
        return found;
    }
    for (const auto& base : state->bases) {
        if (!base.record_decl) {
            continue;
        }
        const RecordSemanticState* base_state = lookup_cpp_record_state(base.record_decl);
        if (!cpp_record_uses_vptr(base_state)) {
            continue;
        }
        if (auto found = visit_context(base.record_decl)) {
            return found;
        }
    }
    for (const auto& virtual_base : state->virtual_bases) {
        if (!virtual_base.record_decl) {
            continue;
        }
        const RecordSemanticState* virtual_base_state =
            lookup_cpp_record_state(virtual_base.record_decl);
        if (!cpp_record_uses_vptr(virtual_base_state)) {
            continue;
        }
        if (auto found = visit_context(virtual_base.record_decl)) {
            return found;
        }
    }
    return std::nullopt;
}

// ---------------------------------------------------------------------------
// Vtable helper functions extracted from get_or_create_cpp_vtable to reduce
// nesting and eliminate thunk-generator duplication.
// ---------------------------------------------------------------------------

// Recursively find which record in the inheritance hierarchy declares a
// given method symbol.
static const ObjectDecl* find_symbol_owner_decl(
    const ASTToLLVM& lower,
    const ObjectDecl* root_decl,
    const std::shared_ptr<Symbol>& method_symbol,
    std::unordered_set<const ObjectDecl*>& visited) {
    const ObjectDecl* current_decl = lower.canonical_cpp_record_decl(root_decl);
    if (!current_decl || !method_symbol || visited.contains(current_decl)) {
        return nullptr;
    }
    visited.insert(current_decl);
    const RecordSemanticState* state = lower.lookup_cpp_record_state(current_decl);
    if (!state) {
        return nullptr;
    }
    for (const auto& method : state->methods) {
        if (method.symbol == method_symbol) {
            return current_decl;
        }
    }
    for (const auto& dtor : state->destructors) {
        if (dtor.symbol == method_symbol) {
            return current_decl;
        }
    }
    for (const auto& base : state->bases) {
        if (!base.record_decl) {
            continue;
        }
        if (const ObjectDecl* owner = find_symbol_owner_decl(
                lower, base.record_decl, method_symbol, visited)) {
            return owner;
        }
    }
    return nullptr;
}

// Covariant return analysis types and helpers.
namespace {
enum class CovariantReturnKind : uint8_t {
    Invalid, Pointer, LValueReference, RValueReference,
};
struct CovariantReturnTarget {
    CovariantReturnKind kind = CovariantReturnKind::Invalid;
    QualType object_type;
    const ObjectDecl* object_decl = nullptr;
};
struct CovariantReturnAdjustInfo {
    bool valid = true;
    bool result_is_reference = false;
    int64_t byte_adjustment = 0;
};
} // namespace

static CovariantReturnTarget extract_covariant_return_target(
    const ASTToLLVM& lower, QualType return_type) {
    CovariantReturnTarget target;
    if (!return_type) {
        return target;
    }
    auto canonical_return = desugar_type(return_type, lower.ast_ctx.get());
    if (auto ptr_type = canonical_return.as_shared<PointerType>()) {
        target.kind = CovariantReturnKind::Pointer;
        target.object_type = ptr_type->pointed_type;
    } else if (auto ref_type = canonical_return.as_shared<ReferenceType>()) {
        target.kind = ref_type->isRValueReference()
            ? CovariantReturnKind::RValueReference
            : CovariantReturnKind::LValueReference;
        target.object_type = ref_type->referred_type;
    } else {
        return target;
    }

    auto object_type =
        desugar_type(target.object_type, lower.ast_ctx.get()).as_shared<ObjectType>();
    if (!object_type) {
        target.kind = CovariantReturnKind::Invalid;
        target.object_type = QualType();
        return target;
    }
    target.object_decl = lower.canonical_cpp_record_decl(
        dyn_cast<ObjectDecl>(object_type->get_decl()));
    if (!target.object_decl) {
        target.kind = CovariantReturnKind::Invalid;
        target.object_type = QualType();
    }
    return target;
}

static CovariantReturnAdjustInfo compute_covariant_return_adjustment(
    const ASTToLLVM& lower,
    QualType context_return,
    QualType target_return) {
    CovariantReturnAdjustInfo info;
    if (!context_return || !target_return ||
        context_return.equals_unqualified(target_return)) {
        return info;
    }

    CovariantReturnTarget context_target =
        extract_covariant_return_target(lower, context_return);
    CovariantReturnTarget target_target =
        extract_covariant_return_target(lower, target_return);
    if (context_target.kind == CovariantReturnKind::Invalid ||
        target_target.kind == CovariantReturnKind::Invalid ||
        context_target.kind != target_target.kind ||
        !context_target.object_type ||
        !target_target.object_type ||
        !context_target.object_decl ||
        !target_target.object_decl) {
        info.valid = false;
        return info;
    }

    if (!context_target.object_type.has_all_qualifiers_of(
            target_target.object_type)) {
        info.valid = false;
        return info;
    }
    info.result_is_reference =
        context_target.kind != CovariantReturnKind::Pointer;

    if (context_target.object_decl == target_target.object_decl) {
        return info;
    }

    std::optional<size_t> offset = lower.find_cpp_base_subobject_offset(
        target_target.object_decl,
        context_target.object_decl);
    if (!offset.has_value() ||
        *offset > static_cast<size_t>(std::numeric_limits<int64_t>::max())) {
        info.valid = false;
        return info;
    }
    info.byte_adjustment = static_cast<int64_t>(*offset);
    return info;
}

// Unified adjusting thunk: applies constant `this` delta and optional
// covariant-return fixups before tail-calling the target implementation.
// `is_virtual` selects the cache and naming convention (nv vs. v prefix).
static llvm::Function* emit_adjusting_thunk(
    ASTToLLVM& lower,
    const std::shared_ptr<Symbol>& context_symbol,
    const std::shared_ptr<Symbol>& target_symbol,
    int64_t this_adjustment,
    bool is_virtual,
    ASTToLLVM::CppCtorDtorVariant context_variant =
        ASTToLLVM::CppCtorDtorVariant::Complete,
    ASTToLLVM::CppCtorDtorVariant target_variant =
        ASTToLLVM::CppCtorDtorVariant::Complete) {
    if (!context_symbol || !target_symbol ||
        context_symbol->kind != SymbolKind::FUNCTION ||
        target_symbol->kind != SymbolKind::FUNCTION) {
        return nullptr;
    }

    auto context_fn_type =
        desugar_type(context_symbol->type, lower.ast_ctx.get()).as_shared<FunctionType>();
    auto target_fn_type =
        desugar_type(target_symbol->type, lower.ast_ctx.get()).as_shared<FunctionType>();
    if (!context_fn_type || !target_fn_type ||
        context_fn_type->parameters.empty() || target_fn_type->parameters.empty()) {
        return nullptr;
    }

    // Select cache and naming convention based on thunk kind.
    auto& thunk_cache = is_virtual
        ? lower.cpp_virtual_thunk_cache
        : lower.cpp_nonvirtual_thunk_cache;
    const char* name_infix = is_virtual ? ".v." : ".nv.";
    const char* tag_prefix = is_virtual ? "vthunk" : "thunk";

    std::string thunk_key =
        context_symbol->uid + "->" + target_symbol->uid + "@" +
        std::to_string(this_adjustment) + ":" +
        std::to_string(static_cast<int>(context_variant)) + ":" +
        std::to_string(static_cast<int>(target_variant));
    auto thunk_cache_it = thunk_cache.find(thunk_key);
    if (thunk_cache_it != thunk_cache.end()) {
        return thunk_cache_it->second;
    }

    std::vector<llvm::Type*> context_param_types;
    context_param_types.reserve(context_fn_type->parameters.size());
    for (const auto& param : context_fn_type->parameters) {
        context_param_types.push_back(lower.convert_param_type(param));
    }
    llvm::Type* context_return_type = lower.convert_type(context_fn_type->ret_type);
    auto* context_llvm_fn_type = llvm::FunctionType::get(
        context_return_type, context_param_types, context_fn_type->is_variadic);

    std::vector<llvm::Type*> target_param_types;
    target_param_types.reserve(target_fn_type->parameters.size());
    for (const auto& param : target_fn_type->parameters) {
        target_param_types.push_back(lower.convert_param_type(param));
    }
    llvm::Type* target_return_type = lower.convert_type(target_fn_type->ret_type);
    auto* target_llvm_fn_type = llvm::FunctionType::get(
        target_return_type, target_param_types, target_fn_type->is_variadic);

    std::string context_name =
        context_variant == ASTToLLVM::CppCtorDtorVariant::Complete
            ? lower.get_function_llvm_name(context_symbol, context_symbol->name)
            : lower.get_cpp_special_member_variant_llvm_name(
                context_symbol, true, context_variant);
    std::string target_name =
        target_variant == ASTToLLVM::CppCtorDtorVariant::Complete
            ? lower.get_function_llvm_name(target_symbol, target_symbol->name)
            : lower.get_cpp_special_member_variant_llvm_name(
                target_symbol, true, target_variant);
    std::string thunk_name =
        std::string("__aburi_thunk") + name_infix +
        ASTToLLVM::mangleCIdentifier(context_name) + ".to." +
        ASTToLLVM::mangleCIdentifier(target_name) + "." +
        std::to_string(this_adjustment);

    llvm::Function* thunk_fn = lower.module->getFunction(thunk_name);
    if (!thunk_fn) {
        thunk_fn = llvm::Function::Create(
            context_llvm_fn_type,
            llvm::GlobalValue::InternalLinkage,
            thunk_name,
            lower.module.get());
    }
    thunk_cache[thunk_key] = thunk_fn;

    if (!thunk_fn->empty()) {
        return thunk_fn;
    }

    ASTToLLVM::SyntheticFunctionEmissionScope synthetic_scope(lower);

    llvm::BasicBlock* entry_bb =
        llvm::BasicBlock::Create(*lower.context, "entry", thunk_fn);
    lower.builder.SetInsertPoint(entry_bb);

    llvm::FunctionCallee target_callee =
        lower.module->getOrInsertFunction(target_name, target_llvm_fn_type);

    std::vector<llvm::Value*> target_args;
    target_args.reserve(thunk_fn->arg_size());

    std::string this_tag = std::string(tag_prefix) + ".this.adjust";
    unsigned arg_index = 0;
    for (auto& arg : thunk_fn->args()) {
        llvm::Value* arg_value = &arg;
        if (arg_index == 0 && this_adjustment != 0) {
            llvm::Value* adjust_amount = llvm::ConstantInt::get(
                llvm::Type::getInt64Ty(*lower.context),
                this_adjustment,
                true);
            arg_value = lower.builder.CreateInBoundsGEP(
                llvm::Type::getInt8Ty(*lower.context),
                arg_value,
                adjust_amount,
                this_tag);
        }

        llvm::Type* target_param_type = arg_index < target_param_types.size()
            ? target_param_types[arg_index]
            : arg_value->getType();
        if (arg_value->getType() != target_param_type) {
            bool is_unsigned = false;
            if (arg_index < context_fn_type->parameters.size() &&
                context_fn_type->parameters[arg_index]) {
                is_unsigned = context_fn_type->parameters[arg_index]->isUnsigned();
            }
            arg_value = lower.cast_llvm_type(arg_value, target_param_type, is_unsigned);
        }
        target_args.push_back(arg_value);
        ++arg_index;
    }

    llvm::CallInst* call_inst = lower.builder.CreateCall(target_callee, target_args);
    if (context_return_type->isVoidTy()) {
        lower.builder.CreateRetVoid();
    } else {
        // Covariant return adjustment in thunks:
        // If the overriding method returns a derived-class pointer where the
        // overridden method returns a base-class pointer, we must adjust the
        // returned pointer by the base subobject offset.
        // For pointer returns: null pointers must remain null (null-check first).
        // For reference returns: always adjust (references are never null).
        CovariantReturnAdjustInfo return_adjust = compute_covariant_return_adjustment(
            lower, context_fn_type->ret_type, target_fn_type->ret_type);
        llvm::Value* ret_value = call_inst;
        if (return_adjust.valid &&
            return_adjust.byte_adjustment != 0 &&
            ret_value->getType()->isPointerTy()) {
            std::string ret_tag = std::string(tag_prefix) + ".ret.adjust";
            std::string null_tag = std::string(tag_prefix) + ".ret.isnull";
            std::string sel_tag = std::string(tag_prefix) + ".ret.select";
            llvm::Value* adjust_amount = llvm::ConstantInt::get(
                llvm::Type::getInt64Ty(*lower.context),
                return_adjust.byte_adjustment,
                true);
            llvm::Value* adjusted_value = lower.builder.CreateGEP(
                llvm::Type::getInt8Ty(*lower.context),
                ret_value,
                adjust_amount,
                ret_tag);
            if (adjusted_value->getType() != ret_value->getType()) {
                adjusted_value = lower.cast_llvm_type(
                    adjusted_value, ret_value->getType(), false);
            }
            if (!return_adjust.result_is_reference) {
                llvm::Value* is_null =
                    lower.builder.CreateIsNull(ret_value, null_tag);
                ret_value = lower.builder.CreateSelect(
                    is_null, ret_value, adjusted_value, sel_tag);
            } else {
                ret_value = adjusted_value;
            }
        }
        if (ret_value->getType() != context_return_type) {
            bool is_unsigned = context_fn_type->ret_type &&
                context_fn_type->ret_type->isUnsigned();
            ret_value = lower.cast_llvm_type(ret_value, context_return_type, is_unsigned);
        }
        lower.builder.CreateRet(ret_value);
    }

    return thunk_fn;
}

llvm::GlobalVariable* ASTToLLVM::get_or_create_cpp_vtable(
    const ObjectDecl* record_decl,
    const ObjectDecl* context_record_decl) {
    const ObjectDecl* canonical_decl = canonical_cpp_record_decl(record_decl);
    const ObjectDecl* canonical_context_decl = canonical_cpp_record_decl(
        context_record_decl ? context_record_decl : canonical_decl);
    if (!canonical_decl || !canonical_context_decl) {
        return nullptr;
    }

    bool primary_context = canonical_context_decl == canonical_decl;
    // Itanium ABI: each polymorphic subobject within a most-derived class has
    // its own vtable address point. Primary context (self) uses cpp_vtable_cache;
    // secondary context (base subobject viewed from derived) uses
    // cpp_vtable_group_cache keyed by (derived, context) pair.
    if (primary_context) {
        auto cache_it = cpp_vtable_cache.find(canonical_decl);
        if (cache_it != cpp_vtable_cache.end()) {
            return cache_it->second;
        }
    }

    std::string group_cache_key =
        make_cpp_vtable_group_key(canonical_decl, canonical_context_decl);
    if (!primary_context) {
        auto group_cache_it = cpp_vtable_group_cache.find(group_cache_key);
        if (group_cache_it != cpp_vtable_group_cache.end()) {
            return group_cache_it->second;
        }
    }

    const RecordSemanticState* derived_state = lookup_cpp_record_state(canonical_decl);
    const RecordSemanticState* context_state =
        lookup_cpp_record_state(canonical_context_decl);
    if (!cpp_record_uses_vptr(derived_state) ||
        !cpp_record_uses_vptr(context_state) ||
        (context_state->virtual_slots.empty() &&
         context_state->virtual_bases.empty())) {
        return nullptr;
    }
    if (!using_itanium_cxx_object_abi()) {
        return nullptr;
    }

    std::string vtable_name = "__aburi_vtable." +
        mangleCIdentifier(canonical_decl->get_tag_name());
    if (!primary_context) {
        vtable_name += "." + mangleCIdentifier(canonical_context_decl->get_tag_name());
    }
    if (auto* existing = module->getGlobalVariable(vtable_name, true)) {
        if (primary_context) {
            cpp_vtable_cache[canonical_decl] = existing;
        } else {
            cpp_vtable_group_cache[group_cache_key] = existing;
        }
        return existing;
    }

    std::unordered_map<std::string, const RecordSemanticState::VirtualSlot*> derived_slot_map;
    derived_slot_map.reserve(derived_state->virtual_slots.size());
    // Pre-index derived slots by key so context-slot iteration can cheaply find
    // the final override selected for this most-derived type.
    for (const auto& slot : derived_state->virtual_slots) {
        derived_slot_map[slot.key] = &slot;
    }

    // Thunk generation delegates to the unified emit_adjusting_thunk helper.
    auto get_or_create_nonvirtual_thunk =
        [this](const std::shared_ptr<Symbol>& context_symbol,
            const std::shared_ptr<Symbol>& target_symbol,
            int64_t adj,
            CppCtorDtorVariant context_variant,
            CppCtorDtorVariant target_variant) -> llvm::Function* {
        return emit_adjusting_thunk(
            *this,
            context_symbol,
            target_symbol,
            adj,
            false,
            context_variant,
            target_variant);
    };
    auto get_or_create_virtual_thunk =
        [this](const std::shared_ptr<Symbol>& context_symbol,
            const std::shared_ptr<Symbol>& target_symbol,
            int64_t adj,
            CppCtorDtorVariant context_variant,
            CppCtorDtorVariant target_variant) -> llvm::Function* {
        return emit_adjusting_thunk(
            *this,
            context_symbol,
            target_symbol,
            adj,
            true,
            context_variant,
            target_variant);
    };

    auto* ptr_ty = llvm::PointerType::get(*context, 0);
    std::vector<llvm::Constant*> entries;
    const size_t header_entry_count =
        cpp_vtable_header_entries_for_context(context_state);
    size_t minimum_entry_count =
        context_state->virtual_bases.size() +
        header_entry_count +
        cpp_vtable_emitted_slot_count(context_state);
    if (using_itanium_cxx_object_abi() && context_state->virtual_slots.empty()) {
        // Keep the address point in-range even for virtual-base-only contexts.
        ++minimum_entry_count;
    }
    entries.reserve(minimum_entry_count);

    auto null_entry =
        llvm::ConstantPointerNull::get(llvm::cast<llvm::PointerType>(ptr_ty));
    std::optional<size_t> context_offset_for_vbase_entries = std::nullopt;
    if (canonical_context_decl == canonical_decl) {
        context_offset_for_vbase_entries = size_t{0};
    } else {
        context_offset_for_vbase_entries = find_cpp_base_subobject_offset(
            canonical_decl,
            canonical_context_decl);
    }

    // Itanium prefix stores per-virtual-base offsets relative to the current
    // address-point context. These are consumed by virtual-base thunks.
    for (const auto& context_virtual_base : context_state->virtual_bases) {
        int64_t relative_offset = 0;
        if (context_offset_for_vbase_entries.has_value() &&
            context_virtual_base.record_decl) {
            std::optional<size_t> target_offset = find_cpp_base_subobject_offset(
                canonical_decl,
                context_virtual_base.record_decl);
            if (target_offset.has_value()) {
                relative_offset =
                    static_cast<int64_t>(*target_offset) -
                    static_cast<int64_t>(*context_offset_for_vbase_entries);
            }
        }
        llvm::Constant* offset_value = llvm::ConstantInt::get(
            llvm::Type::getInt64Ty(*context),
            relative_offset,
            true);
        entries.push_back(llvm::ConstantExpr::getIntToPtr(offset_value, ptr_ty));
    }

    if (using_itanium_cxx_object_abi()) {
        // Header layout: [offset-to-top, typeinfo].
        int64_t offset_to_top = 0;
        if (context_offset_for_vbase_entries.has_value() &&
            *context_offset_for_vbase_entries <=
                static_cast<size_t>(std::numeric_limits<int64_t>::max())) {
            offset_to_top =
                -static_cast<int64_t>(*context_offset_for_vbase_entries);
        }
        llvm::Constant* offset_to_top_value = llvm::ConstantInt::get(
            llvm::Type::getInt64Ty(*context),
            offset_to_top,
            true);
        entries.push_back(
            llvm::ConstantExpr::getIntToPtr(offset_to_top_value, ptr_ty));
        llvm::Constant* typeinfo_entry = null_entry;
        if (auto context_record_type = canonical_context_decl->get_record_type()) {
            if (llvm::GlobalVariable* typeinfo_global =
                    get_or_create_itanium_typeinfo_global(QualType(context_record_type))) {
                typeinfo_entry =
                    llvm::ConstantExpr::getBitCast(typeinfo_global, ptr_ty);
            }
        }
        entries.push_back(typeinfo_entry);
    }

    auto append_virtual_slot_entry =
        [&](const RecordSemanticState::VirtualSlot& context_slot,
            const RecordSemanticState::VirtualSlot* derived_slot,
            bool use_deleting_destructor_entry) {
            llvm::Constant* entry = null_entry;

            bool is_pure = derived_slot ? derived_slot->is_pure : context_slot.is_pure;
            std::shared_ptr<Symbol> resolved_symbol =
                (derived_slot && derived_slot->final_symbol)
                    ? derived_slot->final_symbol
                    : context_slot.final_symbol;
            if (!resolved_symbol || resolved_symbol->kind != SymbolKind::FUNCTION || is_pure) {
                entries.push_back(entry);
                return;
            }

            std::shared_ptr<Symbol> context_symbol =
                context_slot.final_symbol ? context_slot.final_symbol : resolved_symbol;
            CppCtorDtorVariant slot_variant =
                (context_slot.is_destructor && use_deleting_destructor_entry)
                    ? CppCtorDtorVariant::Deleting
                    : CppCtorDtorVariant::Complete;
            if (slot_variant == CppCtorDtorVariant::Deleting) {
                if (!get_or_create_cpp_deleting_destructor_function(
                        resolved_symbol,
                        SrcLoc(),
                        "get_or_create_cpp_vtable(deleting destructor)")) {
                    entries.push_back(entry);
                    return;
                }
            }

            llvm::Constant* callable_entry = nullptr;
            bool needs_adjusting_thunk = false;
            bool needs_return_adjusting_thunk = false;
            int64_t this_adjustment = 0;
            if (!primary_context) {
                std::unordered_set<const ObjectDecl*> owner_visited;
                const ObjectDecl* symbol_owner_decl = find_symbol_owner_decl(
                    *this, canonical_decl, resolved_symbol, owner_visited);

                std::optional<size_t> context_offset = std::nullopt;
                if (canonical_context_decl == canonical_decl) {
                    context_offset = size_t{0};
                } else {
                    context_offset = find_cpp_base_subobject_offset(
                        canonical_decl,
                        canonical_context_decl);
                }

                std::optional<size_t> owner_offset = std::nullopt;
                if (symbol_owner_decl) {
                    if (symbol_owner_decl == canonical_decl) {
                        owner_offset = size_t{0};
                    } else {
                        owner_offset = find_cpp_base_subobject_offset(
                            canonical_decl,
                            symbol_owner_decl);
                    }
                }

                if (context_offset.has_value() &&
                    owner_offset.has_value() &&
                    *context_offset != *owner_offset) {
                    this_adjustment = static_cast<int64_t>(*owner_offset) -
                                      static_cast<int64_t>(*context_offset);
                    needs_adjusting_thunk = true;
                }
            }

            auto context_fn_type =
                desugar_type(context_symbol->type, ast_ctx.get()).as_shared<FunctionType>();
            auto resolved_fn_type =
                desugar_type(resolved_symbol->type, ast_ctx.get()).as_shared<FunctionType>();
            if (context_fn_type && resolved_fn_type &&
                !context_fn_type->ret_type.equals_unqualified(
                    resolved_fn_type->ret_type)) {
                needs_return_adjusting_thunk = true;
            }
            needs_adjusting_thunk =
                needs_adjusting_thunk || needs_return_adjusting_thunk;

            if (needs_adjusting_thunk) {
                const bool use_virtual_thunk = !context_state->virtual_bases.empty();
                llvm::Function* thunk_fn = use_virtual_thunk
                    ? get_or_create_virtual_thunk(
                        context_symbol,
                        resolved_symbol,
                        this_adjustment,
                        slot_variant,
                        slot_variant)
                    : get_or_create_nonvirtual_thunk(
                        context_symbol,
                        resolved_symbol,
                        this_adjustment,
                        slot_variant,
                        slot_variant);
                if (thunk_fn) {
                    callable_entry = llvm::ConstantExpr::getBitCast(thunk_fn, ptr_ty);
                }
            }

            if (!callable_entry && resolved_fn_type) {
                std::vector<llvm::Type*> param_types;
                param_types.reserve(resolved_fn_type->parameters.size());
                for (const auto& param : resolved_fn_type->parameters) {
                    param_types.push_back(convert_param_type(param));
                }
                llvm::Type* return_type = convert_type(resolved_fn_type->ret_type);
                auto* llvm_fn_type = llvm::FunctionType::get(
                    return_type, param_types, resolved_fn_type->is_variadic);
                std::string fn_name =
                    slot_variant == CppCtorDtorVariant::Deleting
                        ? get_cpp_special_member_variant_llvm_name(
                            resolved_symbol, true, slot_variant)
                        : get_function_llvm_name(
                            resolved_symbol, resolved_symbol->name);
                llvm::FunctionCallee callee =
                    module->getOrInsertFunction(fn_name, llvm_fn_type);
                if (auto* callee_const =
                        llvm::dyn_cast<llvm::Constant>(callee.getCallee())) {
                    callable_entry = llvm::ConstantExpr::getBitCast(callee_const, ptr_ty);
                }
            }

            entry = callable_entry ? callable_entry : null_entry;
            entries.push_back(entry);
        };

    for (const auto& context_slot : context_state->virtual_slots) {
        const RecordSemanticState::VirtualSlot* derived_slot = nullptr;
        auto derived_slot_it = derived_slot_map.find(context_slot.key);
        if (derived_slot_it != derived_slot_map.end()) {
            derived_slot = derived_slot_it->second;
        }

        append_virtual_slot_entry(
            context_slot, derived_slot, /*use_deleting_destructor_entry=*/false);
        if (context_slot.is_destructor) {
            append_virtual_slot_entry(
                context_slot, derived_slot, /*use_deleting_destructor_entry=*/true);
        }
    }

    if (using_itanium_cxx_object_abi() && context_state->virtual_slots.empty()) {
        // Keep address-point index valid even when a context has no virtual methods.
        entries.push_back(null_entry);
    }

    auto* table_ty = llvm::ArrayType::get(ptr_ty, entries.size());
    auto* table_init = llvm::ConstantArray::get(table_ty, entries);
    auto* table = new llvm::GlobalVariable(
        *module,
        table_ty,
        true,
        llvm::GlobalValue::InternalLinkage,
        table_init,
        vtable_name);
    table->setUnnamedAddr(llvm::GlobalValue::UnnamedAddr::Global);
    table->setAlignment(module->getDataLayout().getPointerABIAlignment(0));

    if (primary_context) {
        cpp_vtable_cache[canonical_decl] = table;
    } else {
        cpp_vtable_group_cache[group_cache_key] = table;
    }
    return table;
}

llvm::GlobalVariable* ASTToLLVM::get_or_create_cpp_construction_vtable(
    const ObjectDecl* record_decl,
    const ObjectDecl* context_record_decl) {
    if (!using_itanium_cxx_object_abi()) {
        return nullptr;
    }

    const ObjectDecl* canonical_decl = canonical_cpp_record_decl(record_decl);
    const ObjectDecl* canonical_context_decl = canonical_cpp_record_decl(
        context_record_decl ? context_record_decl : record_decl);
    if (!canonical_decl || !canonical_context_decl) {
        return nullptr;
    }

    std::string construction_key =
        make_cpp_vtable_group_key(canonical_decl, canonical_context_decl);
    auto construction_it = cpp_construction_vtable_cache.find(construction_key);
    if (construction_it != cpp_construction_vtable_cache.end()) {
        return construction_it->second;
    }

    llvm::GlobalVariable* context_vtable = get_or_create_cpp_vtable(
        canonical_decl, canonical_context_decl);
    if (!context_vtable || !context_vtable->hasInitializer()) {
        return nullptr;
    }

    std::string construction_name = "__aburi_construction_vtable." +
        mangleCIdentifier(canonical_decl->get_tag_name()) + "." +
        mangleCIdentifier(canonical_context_decl->get_tag_name());
    if (auto* existing = module->getGlobalVariable(construction_name, true)) {
        cpp_construction_vtable_cache[construction_key] = existing;
        return existing;
    }

    auto* construction_vtable = new llvm::GlobalVariable(
        *module,
        context_vtable->getValueType(),
        true,
        llvm::GlobalValue::InternalLinkage,
        // Construction vtable starts as a byte-for-byte clone of the context table.
        context_vtable->getInitializer(),
        construction_name);
    construction_vtable->setUnnamedAddr(llvm::GlobalValue::UnnamedAddr::Global);
    construction_vtable->setAlignment(module->getDataLayout().getPointerABIAlignment(0));
    cpp_construction_vtable_cache[construction_key] = construction_vtable;
    return construction_vtable;
}

llvm::GlobalVariable* ASTToLLVM::get_or_create_cpp_vtt(const ObjectDecl* record_decl) {
    if (!using_itanium_cxx_object_abi()) {
        return nullptr;
    }

    const ObjectDecl* canonical_decl = canonical_cpp_record_decl(record_decl);
    if (!canonical_decl) {
        return nullptr;
    }
    auto vtt_it = cpp_vtt_cache.find(canonical_decl);
    if (vtt_it != cpp_vtt_cache.end()) {
        return vtt_it->second;
    }

    const RecordSemanticState* state = lookup_cpp_record_state(canonical_decl);
    if (!state || state->is_incomplete || state->virtual_bases.empty()) {
        return nullptr;
    }

    auto* ptr_ty = llvm::PointerType::get(*context, 0);
    std::vector<llvm::Constant*> vtt_entries;
    std::unordered_set<std::string> seen_context_keys;
    auto append_construction_entry = [&](const ObjectDecl* context_decl) {
        const ObjectDecl* canonical_context_decl = canonical_cpp_record_decl(context_decl);
        if (!canonical_context_decl) {
            return;
        }
        std::string entry_key =
            make_cpp_vtable_group_key(canonical_decl, canonical_context_decl);
        if (!seen_context_keys.insert(entry_key).second) {
            return;
        }
        llvm::GlobalVariable* construction_vtable = get_or_create_cpp_construction_vtable(
            canonical_decl, canonical_context_decl);
        if (!construction_vtable) {
            return;
        }
        const RecordSemanticState* context_state =
            lookup_cpp_record_state(canonical_context_decl);
        if (!cpp_record_uses_vptr(context_state)) {
            return;
        }
        auto* table_array_ty =
            llvm::dyn_cast<llvm::ArrayType>(construction_vtable->getValueType());
        if (!table_array_ty) {
            return;
        }
        const size_t address_point_index =
            cpp_vtable_address_point_index(context_state);
        if (address_point_index >= table_array_ty->getNumElements()) {
            return;
        }
        llvm::Constant* zero_idx = llvm::ConstantInt::get(
            llvm::Type::getInt64Ty(*context), 0);
        llvm::Constant* entry_idx = llvm::ConstantInt::get(
            llvm::Type::getInt64Ty(*context),
            static_cast<uint64_t>(address_point_index));
        std::array<llvm::Constant*, 2> gep_indices = {zero_idx, entry_idx};
        llvm::Constant* address_point =
            llvm::ConstantExpr::getInBoundsGetElementPtr(
                construction_vtable->getValueType(),
                construction_vtable,
                llvm::ArrayRef<llvm::Constant*>(gep_indices));
        if (address_point->getType() != ptr_ty) {
            address_point = llvm::ConstantExpr::getBitCast(address_point, ptr_ty);
        }
        vtt_entries.push_back(address_point);
    };

    // Entry order mirrors `get_cpp_vtt_entry_index`.
    append_construction_entry(canonical_decl);
    for (const auto& base : state->bases) {
        if (!base.record_decl) {
            continue;
        }
        const RecordSemanticState* base_state = lookup_cpp_record_state(base.record_decl);
        if (!cpp_record_uses_vptr(base_state)) {
            continue;
        }
        append_construction_entry(base.record_decl);
    }
    for (const auto& virtual_base : state->virtual_bases) {
        if (!virtual_base.record_decl) {
            continue;
        }
        const RecordSemanticState* virtual_base_state =
            lookup_cpp_record_state(virtual_base.record_decl);
        if (!cpp_record_uses_vptr(virtual_base_state)) {
            continue;
        }
        append_construction_entry(virtual_base.record_decl);
    }

    if (vtt_entries.empty()) {
        return nullptr;
    }

    std::string vtt_name =
        "__aburi_vtt." + mangleCIdentifier(canonical_decl->get_tag_name());
    if (auto* existing = module->getGlobalVariable(vtt_name, true)) {
        cpp_vtt_cache[canonical_decl] = existing;
        return existing;
    }

    auto* vtt_ty = llvm::ArrayType::get(ptr_ty, vtt_entries.size());
    auto* vtt_init = llvm::ConstantArray::get(vtt_ty, vtt_entries);
    auto* vtt = new llvm::GlobalVariable(
        *module,
        vtt_ty,
        true,
        llvm::GlobalValue::InternalLinkage,
        vtt_init,
        vtt_name);
    vtt->setUnnamedAddr(llvm::GlobalValue::UnnamedAddr::Global);
    vtt->setAlignment(module->getDataLayout().getPointerABIAlignment(0));
    cpp_vtt_cache[canonical_decl] = vtt;
    return vtt;
}

bool ASTToLLVM::emit_cpp_construction_vptr_store_from_vtt(
    const ObjectDecl* record_decl,
    const ObjectDecl* context_record_decl,
    llvm::Value* object_addr,
    SrcLoc loc,
    const std::string& context_name) {
    const ObjectDecl* canonical_decl = canonical_cpp_record_decl(record_decl);
    const ObjectDecl* canonical_context_decl = canonical_cpp_record_decl(context_record_decl);
    if (!canonical_decl || !canonical_context_decl || !object_addr ||
        !object_addr->getType()->isPointerTy()) {
        return false;
    }
    if (!ensure_supported_cpp_vtable_abi(loc, context_name)) {
        return false;
    }

    const RecordSemanticState* complete_state = lookup_cpp_record_state(canonical_decl);
    const RecordSemanticState* context_state = lookup_cpp_record_state(canonical_context_decl);
    if (!complete_state || !context_state ||
        complete_state->virtual_bases.empty() ||
        !cpp_record_uses_vptr(context_state)) {
        return false;
    }

    llvm::GlobalVariable* vtt = get_or_create_cpp_vtt(canonical_decl);
    if (!vtt) {
        error(context_name + ": failed to materialize VTT", loc);
        return false;
    }

    std::optional<size_t> vtt_index = get_cpp_vtt_entry_index(
        canonical_decl, canonical_context_decl);
    if (!vtt_index.has_value()) {
        return false;
    }

    auto context_record_type = canonical_context_decl->get_record_type();
    if (!context_record_type) {
        return false;
    }
    llvm::Type* context_llvm_type = convert_type(context_record_type);
    auto* context_struct_ty = llvm::dyn_cast<llvm::StructType>(context_llvm_type);
    if (!context_struct_ty || context_struct_ty->getNumElements() == 0) {
        return false;
    }

    llvm::Value* context_addr = object_addr;
    llvm::Type* context_ptr_ty = llvm::PointerType::get(context_struct_ty, 0);
    if (context_addr->getType() != context_ptr_ty) {
        context_addr = cast_llvm_type(context_addr, context_ptr_ty, false);
    }

    llvm::Type* vptr_field_ty = context_struct_ty->getElementType(0);
    bool has_typed_vptr_field =
        vptr_field_ty && vptr_field_ty->isPointerTy();
    auto* ptr_ty = llvm::PointerType::get(*context, 0);
    llvm::Value* vptr_addr = nullptr;
    if (has_typed_vptr_field) {
        vptr_addr =
            builder.CreateStructGEP(context_struct_ty, context_addr, 0, "ctor.vptr.addr");
    } else {
        // Legacy/opaque layout fallback: treat object address as `void**`.
        llvm::Type* ptr_ptr_ty = llvm::PointerType::get(ptr_ty, 0);
        vptr_addr = context_addr;
        if (vptr_addr->getType() != ptr_ptr_ty) {
            vptr_addr = cast_llvm_type(vptr_addr, ptr_ptr_ty, false);
        }
    }

    auto* vtt_array_ty = llvm::dyn_cast<llvm::ArrayType>(vtt->getValueType());
    if (!vtt_array_ty || *vtt_index >= vtt_array_ty->getNumElements()) {
        return false;
    }
    llvm::Value* zero_idx = llvm::ConstantInt::get(
        llvm::Type::getInt64Ty(*context), 0);
    llvm::Value* vtt_idx = llvm::ConstantInt::get(
        llvm::Type::getInt64Ty(*context), static_cast<uint64_t>(*vtt_index));
    llvm::Value* entry_addr = builder.CreateInBoundsGEP(
        vtt_array_ty,
        vtt,
        {zero_idx, vtt_idx},
        "ctor.vtt.entry.addr");
    llvm::Value* raw_vtable_ptr = builder.CreateLoad(
        ptr_ty, entry_addr, "ctor.vtt.entry");
    llvm::Value* vtable_store_value = raw_vtable_ptr;
    if (has_typed_vptr_field) {
        if (vtable_store_value->getType() != vptr_field_ty) {
            vtable_store_value = cast_llvm_type(vtable_store_value, vptr_field_ty, false);
        }
    } else if (vtable_store_value->getType() != ptr_ty) {
        vtable_store_value = cast_llvm_type(vtable_store_value, ptr_ty, false);
    }
    builder.CreateStore(vtable_store_value, vptr_addr);
    return true;
}

llvm::GlobalVariable* ASTToLLVM::get_or_create_cpp_vtable_for_object_type(
    const QualType& object_type) {
    auto canonical_type = desugar_type(object_type, ast_ctx.get());
    auto record_type = canonical_type.as_shared<ObjectType>();
    if (!record_type) {
        if (auto ptr_type = canonical_type.as_shared<PointerType>()) {
            record_type =
                desugar_type(ptr_type->pointed_type, ast_ctx.get()).as_shared<ObjectType>();
        }
    }
    if (!record_type) {
        return nullptr;
    }

    const ObjectDecl* record_decl = canonical_cpp_record_decl(
        dyn_cast<ObjectDecl>(record_type->get_decl()));
    return get_or_create_cpp_vtable(record_decl);
}

bool ASTToLLVM::emit_cpp_vptr_store(const QualType& object_type,
                                    llvm::Value* object_addr,
                                    SrcLoc loc,
                                    const std::string& context_name) {
    if (!object_addr) {
        return false;
    }

    auto record_type = desugar_type(object_type, ast_ctx.get()).as_shared<ObjectType>();
    if (!record_type) {
        if (auto ptr_type =
                desugar_type(object_type, ast_ctx.get()).as_shared<PointerType>()) {
            record_type =
                desugar_type(ptr_type->pointed_type, ast_ctx.get()).as_shared<ObjectType>();
        }
    }
    if (!record_type) {
        return true;
    }

    const ObjectDecl* record_decl = canonical_cpp_record_decl(
        dyn_cast<ObjectDecl>(record_type->get_decl()));
    const RecordSemanticState* state = lookup_cpp_record_state(record_decl);
    if (!cpp_record_uses_vptr(state)) {
        return true;
    }
    if (!ensure_supported_cpp_vtable_abi(loc, context_name)) {
        return false;
    }

    llvm::GlobalVariable* primary_vtable = get_or_create_cpp_vtable(
        record_decl, record_decl);
    if (!primary_vtable) {
        error(context_name + ": failed to materialize polymorphic vtable", loc);
        return false;
    }
    if (!state->virtual_bases.empty()) {
        llvm::GlobalVariable* vtt = get_or_create_cpp_vtt(record_decl);
        if (!vtt) {
            error(context_name + ": failed to materialize construction vtable table", loc);
            return false;
        }
    }

    llvm::Type* object_llvm_type = convert_type(record_type);
    auto* object_struct_ty = llvm::dyn_cast<llvm::StructType>(object_llvm_type);
    if (!object_struct_ty || object_struct_ty->getNumElements() == 0) {
        error(context_name + ": polymorphic object has invalid LLVM layout", loc);
        return false;
    }
    if (!object_addr->getType()->isPointerTy()) {
        error(context_name + ": polymorphic object storage is not addressable", loc);
        return false;
    }

    auto store_subobject_vptr =
        [&](llvm::Value* subobject_addr,
            llvm::StructType* subobject_struct_ty,
            llvm::GlobalVariable* vtable,
            const RecordSemanticState* vtable_context_state,
            const std::string& store_name) -> bool {
        if (!subobject_addr || !subobject_struct_ty || !vtable ||
            !vtable_context_state) {
            return false;
        }
        if (!subobject_addr->getType()->isPointerTy() ||
            subobject_struct_ty->getNumElements() == 0) {
            return false;
        }
        llvm::Type* vptr_field_ty = subobject_struct_ty->getElementType(0);
        bool has_typed_vptr_field =
            vptr_field_ty && vptr_field_ty->isPointerTy();
        auto* ptr_ty = llvm::PointerType::get(*context, 0);
        llvm::Value* vptr_addr = nullptr;
        if (has_typed_vptr_field) {
            vptr_addr = builder.CreateStructGEP(
                subobject_struct_ty, subobject_addr, 0, store_name);
        } else {
            // Some lowered layouts keep the vptr in an untyped leading slot.
            llvm::Type* ptr_ptr_ty = llvm::PointerType::get(ptr_ty, 0);
            vptr_addr = subobject_addr;
            if (vptr_addr->getType() != ptr_ptr_ty) {
                vptr_addr = cast_llvm_type(vptr_addr, ptr_ptr_ty, false);
            }
        }
        auto* table_array_ty = llvm::dyn_cast<llvm::ArrayType>(vtable->getValueType());
        if (!table_array_ty) {
            return false;
        }
        const size_t address_point_index =
            cpp_vtable_address_point_index(vtable_context_state);
        if (address_point_index >= table_array_ty->getNumElements()) {
            return false;
        }
        llvm::Constant* zero_idx = llvm::ConstantInt::get(
            llvm::Type::getInt64Ty(*context), 0);
        llvm::Constant* entry_idx = llvm::ConstantInt::get(
            llvm::Type::getInt64Ty(*context),
            static_cast<uint64_t>(address_point_index));
        std::array<llvm::Constant*, 2> gep_indices = {zero_idx, entry_idx};
        llvm::Constant* address_point =
            llvm::ConstantExpr::getInBoundsGetElementPtr(
                vtable->getValueType(),
                vtable,
                llvm::ArrayRef<llvm::Constant*>(gep_indices));
        llvm::Value* vtable_ptr = address_point;
        if (has_typed_vptr_field) {
            if (vtable_ptr->getType() != vptr_field_ty) {
                vtable_ptr = llvm::ConstantExpr::getBitCast(
                    llvm::cast<llvm::Constant>(vtable_ptr),
                    vptr_field_ty);
            }
        } else if (vtable_ptr->getType() != ptr_ty) {
            vtable_ptr = llvm::ConstantExpr::getBitCast(
                llvm::cast<llvm::Constant>(vtable_ptr),
                ptr_ty);
        }
        builder.CreateStore(vtable_ptr, vptr_addr);
        return true;
    };

    if (!store_subobject_vptr(
            object_addr, object_struct_ty, primary_vtable, state, "vptr.addr")) {
        error(context_name + ": polymorphic vptr field is not pointer-typed", loc);
        return false;
    }

    for (const auto& base : state->bases) {
        // Install secondary vptrs for non-virtual base subobjects that own one.
        if (!base.record_decl ||
            base.is_virtual ||
            !base.has_non_virtual_offset ||
            base.non_virtual_offset == 0) {
            continue;
        }
        const RecordSemanticState* base_state = lookup_cpp_record_state(base.record_decl);
        if (!cpp_record_uses_vptr(base_state)) {
            continue;
        }

        auto base_record_type =
            desugar_type(base.type, ast_ctx.get()).as_shared<ObjectType>();
        if (!base_record_type) {
            continue;
        }
        llvm::Type* base_llvm_type = convert_type(base_record_type);
        auto* base_struct_ty = llvm::dyn_cast<llvm::StructType>(base_llvm_type);
        if (!base_struct_ty || base_struct_ty->getNumElements() == 0) {
            continue;
        }

        llvm::GlobalVariable* secondary_vtable = get_or_create_cpp_vtable(
            record_decl, base.record_decl);
        if (!secondary_vtable) {
            error(context_name + ": failed to materialize secondary vtable", loc);
            return false;
        }

        llvm::Value* base_offset = llvm::ConstantInt::get(
            llvm::Type::getInt64Ty(*context),
            static_cast<uint64_t>(base.non_virtual_offset));
        llvm::Value* base_addr = builder.CreateInBoundsGEP(
            llvm::Type::getInt8Ty(*context),
            object_addr,
            base_offset,
            "vptr.base.addr");
        llvm::Type* base_ptr_type = llvm::PointerType::get(base_struct_ty, 0);
        if (base_addr->getType() != base_ptr_type) {
            base_addr = cast_llvm_type(base_addr, base_ptr_type, false);
        }

        if (!store_subobject_vptr(
                base_addr,
                base_struct_ty,
                secondary_vtable,
                base_state,
                "vptr.base.field")) {
            error(context_name + ": secondary polymorphic vptr field is not pointer-typed", loc);
            return false;
        }
    }

    for (const auto& virtual_base : state->virtual_bases) {
        // Virtual bases use context-specific tables so dynamic dispatch sees the
        // correct slot layout from each virtual subobject.
        if (!virtual_base.record_decl ||
            !virtual_base.has_offset ||
            virtual_base.offset == 0) {
            continue;
        }
        const RecordSemanticState* virtual_base_state =
            lookup_cpp_record_state(virtual_base.record_decl);
        if (!cpp_record_uses_vptr(virtual_base_state)) {
            continue;
        }

        auto virtual_base_record_type =
            desugar_type(virtual_base.type, ast_ctx.get()).as_shared<ObjectType>();
        if (!virtual_base_record_type) {
            continue;
        }
        llvm::Type* virtual_base_llvm_type = convert_type(virtual_base_record_type);
        auto* virtual_base_struct_ty = llvm::dyn_cast<llvm::StructType>(virtual_base_llvm_type);
        if (!virtual_base_struct_ty || virtual_base_struct_ty->getNumElements() == 0) {
            continue;
        }

        llvm::GlobalVariable* virtual_base_vtable = get_or_create_cpp_vtable(
            record_decl, virtual_base.record_decl);
        if (!virtual_base_vtable) {
            error(context_name + ": failed to materialize virtual-base vtable", loc);
            return false;
        }

        llvm::Value* virtual_base_offset = llvm::ConstantInt::get(
            llvm::Type::getInt64Ty(*context),
            static_cast<uint64_t>(virtual_base.offset));
        llvm::Value* virtual_base_addr = builder.CreateInBoundsGEP(
            llvm::Type::getInt8Ty(*context),
            object_addr,
            virtual_base_offset,
            "vptr.vbase.addr");
        llvm::Type* virtual_base_ptr_type =
            llvm::PointerType::get(virtual_base_struct_ty, 0);
        if (virtual_base_addr->getType() != virtual_base_ptr_type) {
            virtual_base_addr = cast_llvm_type(
                virtual_base_addr, virtual_base_ptr_type, false);
        }

        if (!store_subobject_vptr(
                virtual_base_addr,
                virtual_base_struct_ty,
                virtual_base_vtable,
                virtual_base_state,
                "vptr.vbase.field")) {
            error(context_name + ": virtual-base polymorphic vptr field is not pointer-typed", loc);
            return false;
        }
    }

    return true;
}
