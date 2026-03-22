#include "ast2llvm.h"
#include "llvm/IR/Constants.h"
#include <limits>
#include <optional>
#include <string>
#include <unordered_set>

namespace {

std::optional<size_t> find_cpp_base_subobject_offset_impl(
    const ASTToLLVM& lower,
    const ObjectDecl* derived_decl,
    const ObjectDecl* base_decl,
    std::unordered_set<const ObjectDecl*>& active_stack) {
    derived_decl = lower.canonical_cpp_record_decl(derived_decl);
    base_decl = lower.canonical_cpp_record_decl(base_decl);
    if (!derived_decl || !base_decl) {
        return std::nullopt;
    }
    if (derived_decl == base_decl) {
        return size_t{0};
    }

    const RecordSemanticState* state = lower.lookup_cpp_record_state(derived_decl);
    if (!state) {
        return std::nullopt;
    }

    std::optional<size_t> found_offset;
    for (const auto& virtual_base : state->virtual_bases) {
        if (!virtual_base.record_decl || !virtual_base.has_offset) {
            continue;
        }
        const ObjectDecl* virtual_base_decl =
            lower.canonical_cpp_record_decl(virtual_base.record_decl);
        if (!virtual_base_decl || virtual_base_decl != base_decl) {
            continue;
        }
        if (!found_offset.has_value()) {
            found_offset = virtual_base.offset;
            continue;
        }
        if (*found_offset != virtual_base.offset) {
            return std::nullopt;
        }
    }
    if (found_offset.has_value()) {
        return found_offset;
    }

    for (const auto& base : state->bases) {
        if (!base.record_decl || base.is_virtual || !base.has_non_virtual_offset) {
            continue;
        }

        const ObjectDecl* base_record_decl =
            lower.canonical_cpp_record_decl(base.record_decl);
        if (!base_record_decl || active_stack.contains(base_record_decl)) {
            continue;
        }

        active_stack.insert(base_record_decl);
        std::optional<size_t> child_offset = find_cpp_base_subobject_offset_impl(
            lower,
            base_record_decl,
            base_decl,
            active_stack);
        active_stack.erase(base_record_decl);
        if (!child_offset.has_value()) {
            continue;
        }
        if (*child_offset >
            std::numeric_limits<size_t>::max() - base.non_virtual_offset) {
            continue;
        }

        size_t total_offset = base.non_virtual_offset + *child_offset;
        if (!found_offset.has_value()) {
            found_offset = total_offset;
            continue;
        }
        if (*found_offset != total_offset) {
            return std::nullopt;
        }
    }

    return found_offset;
}

llvm::Type* get_cpp_intptr_type(ASTToLLVM& lower) {
    return lower.module->getDataLayout().getIntPtrType(*lower.context);
}

llvm::Constant* get_null_pointer_constant(llvm::Type* ptr_type) {
    auto* pointer_type = llvm::dyn_cast_or_null<llvm::PointerType>(ptr_type);
    if (!pointer_type) {
        return nullptr;
    }
    return llvm::ConstantPointerNull::get(pointer_type);
}

llvm::Value* cast_pointer_if_needed(
    ASTToLLVM& lower,
    llvm::Value* ptr_value,
    llvm::Type* target_type) {
    if (!ptr_value || !target_type || ptr_value->getType() == target_type) {
        return ptr_value;
    }
    return lower.cast_llvm_type(ptr_value, target_type, false);
}

llvm::Value* adjust_pointer_with_dynamic_offset_nonnull(
    ASTToLLVM& lower,
    llvm::Value* ptr_value,
    llvm::Value* byte_offset,
    const std::string& name_prefix) {
    if (!ptr_value || !byte_offset || !ptr_value->getType()->isPointerTy()) {
        return ptr_value;
    }

    llvm::Type* intptr_ty = get_cpp_intptr_type(lower);
    llvm::Value* offset = byte_offset;
    if (!offset->getType()->isIntegerTy()) {
        lower.error(name_prefix + ": invalid dynamic byte offset type");
    }
    if (offset->getType() != intptr_ty) {
        offset = lower.cast_llvm_type(offset, intptr_ty, false);
    }

    llvm::Value* adjusted_ptr = lower.builder.CreateGEP(
        llvm::Type::getInt8Ty(*lower.context),
        ptr_value,
        offset,
        name_prefix);
    return cast_pointer_if_needed(lower, adjusted_ptr, ptr_value->getType());
}

llvm::Value* load_cpp_vtable_address_point_nonnull(
    ASTToLLVM& lower,
    llvm::Value* object_ptr,
    const ObjectDecl* object_record_decl,
    SrcLoc loc,
    const std::string& context_name,
    const std::string& name_prefix) {
    const ObjectDecl* canonical_decl =
        lower.canonical_cpp_record_decl(object_record_decl);
    if (!canonical_decl) {
        lower.error(context_name + ": missing C++ object type for vtable lookup", loc);
    }

    auto object_type = canonical_decl->get_record_type();
    if (!object_type) {
        lower.error(context_name + ": missing C++ record type for vtable lookup", loc);
    }

    llvm::Type* object_llvm_type = lower.convert_type(QualType(object_type));
    auto* object_struct_ty = llvm::dyn_cast<llvm::StructType>(object_llvm_type);
    if (!object_struct_ty || object_struct_ty->getNumElements() == 0) {
        lower.error(context_name + ": invalid polymorphic object layout for vtable lookup", loc);
    }

    auto* ptr_ty = llvm::PointerType::get(*lower.context, 0);
    llvm::Value* vptr_addr = lower.builder.CreateStructGEP(
        object_struct_ty, object_ptr, 0, name_prefix + ".vptr.addr");
    llvm::Value* raw_vptr = lower.builder.CreateLoad(
        ptr_ty, vptr_addr, name_prefix + ".vptr");
    auto* table_ptr_ty = llvm::PointerType::get(ptr_ty, 0);
    return lower.builder.CreateBitCast(
        raw_vptr, table_ptr_ty, name_prefix + ".address.point");
}

llvm::Value* load_cpp_vtable_relative_byte_offset_nonnull(
    ASTToLLVM& lower,
    llvm::Value* address_point_ptr,
    int64_t relative_index,
    const std::string& name_prefix) {
    auto* ptr_ty = llvm::PointerType::get(*lower.context, 0);
    llvm::Value* offset_index = llvm::ConstantInt::get(
        llvm::Type::getInt64Ty(*lower.context),
        relative_index,
        true);
    llvm::Value* offset_addr = lower.builder.CreateInBoundsGEP(
        ptr_ty,
        address_point_ptr,
        offset_index,
        name_prefix + ".addr");
    llvm::Value* raw_offset = lower.builder.CreateLoad(
        ptr_ty,
        offset_addr,
        name_prefix + ".raw");
    return lower.builder.CreatePtrToInt(
        raw_offset,
        get_cpp_intptr_type(lower),
        name_prefix);
}

template <typename EmitAdjusted>
llvm::Value* emit_null_checked_pointer_adjustment(
    ASTToLLVM& lower,
    llvm::Value* input_ptr,
    const std::string& name_prefix,
    EmitAdjusted&& emit_adjusted) {
    if (!input_ptr || !input_ptr->getType()->isPointerTy()) {
        return input_ptr;
    }

    auto* input_ptr_ty = llvm::dyn_cast<llvm::PointerType>(input_ptr->getType());
    if (!input_ptr_ty) {
        return input_ptr;
    }

    llvm::Constant* null_result = get_null_pointer_constant(input_ptr->getType());
    if (!null_result) {
        return input_ptr;
    }

    if (auto* null_input = llvm::dyn_cast<llvm::ConstantPointerNull>(input_ptr)) {
        return null_input;
    }

    llvm::BasicBlock* entry_bb = lower.builder.GetInsertBlock();
    if (!entry_bb) {
        lower.error(name_prefix + ": not inside a function while lowering pointer adjustment");
    }
    llvm::Function* current_fn = entry_bb->getParent();
    if (!current_fn) {
        lower.error(name_prefix + ": missing enclosing function for pointer adjustment");
    }

    llvm::Value* is_null = lower.builder.CreateICmpEQ(
        input_ptr, null_result, name_prefix + ".isnull");
    auto* nonnull_bb = llvm::BasicBlock::Create(
        *lower.context, name_prefix + ".nonnull", current_fn);
    auto* continue_bb = llvm::BasicBlock::Create(
        *lower.context, name_prefix + ".cont", current_fn);
    lower.builder.CreateCondBr(is_null, continue_bb, nonnull_bb);

    lower.builder.SetInsertPoint(nonnull_bb);
    llvm::Value* adjusted_ptr = emit_adjusted();
    if (!adjusted_ptr) {
        return nullptr;
    }
    adjusted_ptr = cast_pointer_if_needed(lower, adjusted_ptr, input_ptr->getType());
    lower.builder.CreateBr(continue_bb);
    llvm::BasicBlock* adjusted_bb = lower.builder.GetInsertBlock();

    lower.builder.SetInsertPoint(continue_bb);
    auto* result = lower.builder.CreatePHI(input_ptr->getType(), 2, name_prefix + ".result");
    result->addIncoming(null_result, entry_bb);
    result->addIncoming(adjusted_ptr, adjusted_bb);
    return result;
}

} // namespace

std::optional<size_t> ASTToLLVM::find_cpp_base_subobject_offset(
    const ObjectDecl* derived_decl,
    const ObjectDecl* base_decl) const {
    derived_decl = canonical_cpp_record_decl(derived_decl);
    base_decl = canonical_cpp_record_decl(base_decl);
    if (!derived_decl || !base_decl) {
        return std::nullopt;
    }

    std::unordered_set<const ObjectDecl*> active_stack;
    active_stack.insert(derived_decl);
    return find_cpp_base_subobject_offset_impl(
        *this,
        derived_decl,
        base_decl,
        active_stack);
}

llvm::Value* ASTToLLVM::adjust_cpp_pointer_by_static_offset(
    llvm::Value* ptr_value,
    int64_t byte_offset,
    const std::string& name_prefix) {
    if (!ptr_value || !ptr_value->getType()->isPointerTy() || byte_offset == 0) {
        return ptr_value;
    }

    llvm::Type* intptr_ty = get_cpp_intptr_type(*this);
    llvm::Constant* offset_const = llvm::ConstantInt::get(
        intptr_ty,
        byte_offset,
        true);

    if (auto* null_ptr = llvm::dyn_cast<llvm::ConstantPointerNull>(ptr_value)) {
        return null_ptr;
    }
    if (auto* const_ptr = llvm::dyn_cast<llvm::Constant>(ptr_value)) {
        llvm::Constant* adjusted_const =
            llvm::ConstantExpr::getInBoundsGetElementPtr(
                llvm::Type::getInt8Ty(*context),
                const_ptr,
                offset_const);
        if (adjusted_const->getType() != ptr_value->getType()) {
            adjusted_const = llvm::ConstantExpr::getBitCast(
                adjusted_const,
                ptr_value->getType());
        }
        return adjusted_const;
    }

    llvm::Value* adjusted_ptr = adjust_pointer_with_dynamic_offset_nonnull(
        *this,
        ptr_value,
        offset_const,
        name_prefix);
    llvm::Value* null_ptr = get_null_pointer_constant(ptr_value->getType());
    llvm::Value* is_null = builder.CreateICmpEQ(
        ptr_value, null_ptr, name_prefix + ".isnull");
    return builder.CreateSelect(
        is_null,
        ptr_value,
        adjusted_ptr,
        name_prefix + ".select");
}

llvm::Value* ASTToLLVM::recover_cpp_complete_object_address(
    llvm::Value* subobject_ptr,
    const ObjectDecl* subobject_record_decl,
    SrcLoc loc,
    const std::string& context_name,
    const ObjectDecl* active_vptr_context_decl) {
    const ObjectDecl* object_decl =
        canonical_cpp_record_decl(subobject_record_decl);
    const ObjectDecl* vptr_context_decl = canonical_cpp_record_decl(
        active_vptr_context_decl ? active_vptr_context_decl : subobject_record_decl);
    if (!subobject_ptr || !object_decl || !vptr_context_decl) {
        return subobject_ptr;
    }

    const RecordSemanticState* context_state = lookup_cpp_record_state(vptr_context_decl);
    if (!cpp_record_uses_vptr(context_state)) {
        error(context_name +
                  ": complete-object recovery requires an active polymorphic/virtual-base subobject",
              loc);
    }
    if (!ensure_supported_cpp_vtable_abi(loc, context_name)) {
        return nullptr;
    }

    return emit_null_checked_pointer_adjustment(
        *this,
        subobject_ptr,
        "cpp.complete.object",
        [&]() -> llvm::Value* {
            llvm::Value* address_point = load_cpp_vtable_address_point_nonnull(
                *this,
                subobject_ptr,
                object_decl,
                loc,
                context_name,
                "cpp.complete.object");
            llvm::Value* offset = load_cpp_vtable_relative_byte_offset_nonnull(
                *this,
                address_point,
                -2,
                "cpp.complete.object.offtop");
            return adjust_pointer_with_dynamic_offset_nonnull(
                *this,
                subobject_ptr,
                offset,
                "cpp.complete.object.adjust");
        });
}

llvm::Value* ASTToLLVM::resolve_cpp_virtual_base_subobject_address(
    llvm::Value* context_ptr,
    const ObjectDecl* context_record_decl,
    const ObjectDecl* target_virtual_base_decl,
    SrcLoc loc,
    const std::string& context_name,
    const ObjectDecl* active_vptr_context_decl) {
    const ObjectDecl* object_decl =
        canonical_cpp_record_decl(context_record_decl);
    const ObjectDecl* vptr_context_decl = canonical_cpp_record_decl(
        active_vptr_context_decl ? active_vptr_context_decl : context_record_decl);
    const ObjectDecl* target_decl =
        canonical_cpp_record_decl(target_virtual_base_decl);
    if (!context_ptr || !object_decl || !vptr_context_decl || !target_decl) {
        return nullptr;
    }

    const RecordSemanticState* context_state = lookup_cpp_record_state(vptr_context_decl);
    if (!context_state || !cpp_record_uses_vptr(context_state)) {
        return nullptr;
    }
    if (!ensure_supported_cpp_vtable_abi(loc, context_name)) {
        return nullptr;
    }

    std::optional<size_t> virtual_base_index;
    for (size_t idx = 0; idx < context_state->virtual_bases.size(); ++idx) {
        const auto& virtual_base = context_state->virtual_bases[idx];
        const ObjectDecl* virtual_base_decl =
            canonical_cpp_record_decl(virtual_base.record_decl);
        if (virtual_base_decl && virtual_base_decl == target_decl) {
            virtual_base_index = idx;
            break;
        }
    }
    if (!virtual_base_index.has_value()) {
        return nullptr;
    }

    const int64_t relative_index = cpp_vtable_virtual_base_relative_index(
        context_state,
        *virtual_base_index);
    return emit_null_checked_pointer_adjustment(
        *this,
        context_ptr,
        "cpp.virtual.base",
        [&]() -> llvm::Value* {
            llvm::Value* address_point = load_cpp_vtable_address_point_nonnull(
                *this,
                context_ptr,
                object_decl,
                loc,
                context_name,
                "cpp.virtual.base");
            llvm::Value* offset = load_cpp_vtable_relative_byte_offset_nonnull(
                *this,
                address_point,
                relative_index,
                "cpp.virtual.base.offset");
            return adjust_pointer_with_dynamic_offset_nonnull(
                *this,
                context_ptr,
                offset,
                "cpp.virtual.base.adjust");
        });
}
