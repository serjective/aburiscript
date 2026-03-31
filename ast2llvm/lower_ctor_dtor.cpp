#include "ast2llvm.h"
#include "const_lowering.h"
#include "../helpers/casting.h"
#include "../ast/special_members.h"
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

std::shared_ptr<Symbol> ASTToLLVM::select_record_destructor_symbol(
    const RecordSemanticState* state,
    bool require_public_access) const {
    if (!state) {
        return nullptr;
    }
    for (const auto& dtor : state->destructors) {
        if (dtor.is_deleted || !dtor.symbol ||
            dtor.symbol->kind != SymbolKind::FUNCTION) {
            continue;
        }
        if (require_public_access &&
            dtor.declared_access != RecordMemberAccess::Public) {
            continue;
        }
        return dtor.symbol;
    }
    return nullptr;
}

std::shared_ptr<Symbol> ASTToLLVM::select_record_deallocation_symbol(
    const RecordSemanticState* state,
    bool is_array_form) const {
    const std::string operator_name =
        is_array_form ? "operatordelete[]" : "operatordelete";

    std::function<std::shared_ptr<Symbol>(
        const RecordSemanticState*,
        std::unordered_set<const RecordSemanticState*>&)> select_impl =
        [&](const RecordSemanticState* current_state,
            std::unordered_set<const RecordSemanticState*>& visited)
            -> std::shared_ptr<Symbol> {
            if (!current_state || !visited.insert(current_state).second) {
                return nullptr;
            }

            for (const auto& method : current_state->methods) {
                if (!method.is_static ||
                    method.name != operator_name ||
                    !method.symbol ||
                    method.symbol->kind != SymbolKind::FUNCTION) {
                    continue;
                }
                auto method_type =
                    desugar_type(method.symbol->type, ast_ctx.get())
                        .as_shared<FunctionType>();
                if (!method_type || method_type->parameters.size() != 1) {
                    continue;
                }
                if (canonical_type_kind(method_type->parameters.front(), ast_ctx.get()) !=
                    TypeKind::Pointer) {
                    continue;
                }
                return method.symbol;
            }

            for (const auto& base : current_state->bases) {
                if (!base.record_decl) {
                    continue;
                }
                if (auto base_symbol = select_impl(
                        lookup_cpp_record_state(base.record_decl),
                        visited)) {
                    return base_symbol;
                }
            }
            return nullptr;
        };

    std::unordered_set<const RecordSemanticState*> visited;
    if (auto selected = select_impl(state, visited)) {
        return selected;
    }

    if (!type_ctx) {
        return nullptr;
    }

    auto fn_type = std::make_shared<FunctionType>();
    fn_type->has_prototype = true;
    fn_type->is_variadic = false;
    fn_type->ret_type = QualType(type_ctx->get_builtin(BuiltinTypes::Void));
    fn_type->parameters.push_back(QualType(
        std::make_shared<PointerType>(
            QualType(type_ctx->get_builtin(BuiltinTypes::Void)))));

    auto sym = std::make_shared<Symbol>(
        operator_name,
        SymbolKind::FUNCTION,
        QualType(fn_type));
    sym->storage_class = StorageClass::EXTERN;
    sym->linkage = VariableLinkage::EXTERNAL;
    sym->set_language_linkage(LanguageLinkage::CXX);
    return sym;
}

std::shared_ptr<Symbol> ASTToLLVM::select_record_default_constructor_symbol(
    const RecordSemanticState* state,
    bool require_public_access) const {
    if (!state) {
        return nullptr;
    }

    bool allow_protected_access = !require_public_access;
    for (const auto& ctor : state->constructors) {
        if (!ctor.symbol || ctor.symbol->kind != SymbolKind::FUNCTION) {
            continue;
        }
        if (!cpp_constructor_is_viable_default_candidate(
                ctor, allow_protected_access)) {
            continue;
        }
        return ctor.symbol;
    }
    return nullptr;
}

bool ASTToLLVM::emit_cpp_object_default_construction_recursive(
    const QualType& object_type,
    llvm::Value* object_addr,
    SrcLoc loc,
    const std::string& construction_context,
    CppCtorDtorVariant ctor_variant,
    const ObjectDecl* construction_complete_decl) {
    auto object_record =
        desugar_type(object_type, ast_ctx.get()).as_shared<ObjectType>();
    if (!object_record || !object_addr) {
        return true;
    }

    const ObjectDecl* object_decl = canonical_cpp_record_decl(
        dyn_cast<ObjectDecl>(object_record->get_decl()));
    const RecordSemanticState* object_state = lookup_cpp_record_state(object_decl);
    if (!object_state || object_state->constructors.empty()) {
        return true;
    }
    construction_complete_decl = canonical_cpp_record_decl(
        construction_complete_decl ? construction_complete_decl : object_decl);
    const RecordSemanticState* construction_complete_state =
        lookup_cpp_record_state(construction_complete_decl);

    std::shared_ptr<Symbol> object_ctor_sym =
        select_record_default_constructor_symbol(
            object_state,
            /*require_public_access=*/false);
    if (object_ctor_sym && object_ctor_sym->kind == SymbolKind::FUNCTION) {
        std::vector<std::unique_ptr<Expr>> no_ctor_args;
        return emit_cpp_construct_call(
            object_ctor_sym,
            no_ctor_args,
            object_addr,
            loc,
            construction_context,
            ctor_variant);
    }

    if (object_record->is_union) {
        if (object_decl && cpp_record_uses_vptr(object_state)) {
            bool wrote_construction_vptr = false;
            if (construction_complete_decl &&
                construction_complete_state &&
                !construction_complete_state->virtual_bases.empty()) {
                wrote_construction_vptr =
                    emit_cpp_construction_vptr_store_from_vtt(
                        construction_complete_decl,
                        object_decl,
                        object_addr,
                        loc,
                        construction_context);
            }
            if (!wrote_construction_vptr) {
                emit_cpp_vptr_store(object_type, object_addr, loc, construction_context);
            }
        }
        return true;
    }

    bool has_virtual_base_work = false;
    if (ctor_variant == CppCtorDtorVariant::Complete) {
        for (const auto& virtual_base : object_state->virtual_bases) {
            if (!virtual_base.record_decl || !virtual_base.has_offset) {
                continue;
            }
            has_virtual_base_work = true;
            break;
        }
    }
    bool has_nonvirtual_base_work = false;
    for (const auto& base : object_state->bases) {
        if (base.is_virtual || !base.record_decl || !base.has_non_virtual_offset) {
            continue;
        }
        has_nonvirtual_base_work = true;
        break;
    }
    bool has_record_field_work = false;
    for (const auto& field : object_state->fields) {
        if (field.is_bitfield || field.is_base_subobject ||
            field.is_virtual_base_storage) {
            continue;
        }
        if (canonical_type_kind(field.type, ast_ctx.get()) != TypeKind::Object) {
            continue;
        }
        has_record_field_work = true;
        break;
    }
    bool has_vptr_work = object_decl && cpp_record_uses_vptr(object_state);
    if (!has_virtual_base_work &&
        !has_nonvirtual_base_work &&
        !has_record_field_work &&
        !has_vptr_work) {
        return true;
    }

    auto subobject_addr_with_offset =
        [&](uint64_t offset, const char* ir_name) -> llvm::Value* {
            if (offset == 0) {
                return object_addr;
            }
            return builder.CreateInBoundsGEP(
                llvm::Type::getInt8Ty(*context),
                object_addr,
                llvm::ConstantInt::get(
                    llvm::Type::getInt64Ty(*context),
                    offset),
                ir_name);
        };

    if (ctor_variant == CppCtorDtorVariant::Complete) {
        for (const auto& virtual_base : object_state->virtual_bases) {
            if (!virtual_base.record_decl || !virtual_base.has_offset) {
                continue;
            }
            llvm::Value* virtual_base_addr =
                subobject_addr_with_offset(
                    static_cast<uint64_t>(virtual_base.offset),
                    "implicit.ctor.vbase.addr");
            if (!emit_cpp_object_default_construction_recursive(
                    virtual_base.type,
                    virtual_base_addr,
                    loc,
                    construction_context,
                    CppCtorDtorVariant::Base,
                    construction_complete_decl)) {
                return false;
            }
        }
    }

    for (const auto& base : object_state->bases) {
        if (base.is_virtual || !base.record_decl || !base.has_non_virtual_offset) {
            continue;
        }
        llvm::Value* base_addr =
            subobject_addr_with_offset(
                static_cast<uint64_t>(base.non_virtual_offset),
                "implicit.ctor.base.addr");
        if (!emit_cpp_object_default_construction_recursive(
                base.type,
                base_addr,
                loc,
                construction_context,
                CppCtorDtorVariant::Base,
                construction_complete_decl)) {
            return false;
        }
    }

    if (object_decl && cpp_record_uses_vptr(object_state)) {
        bool wrote_construction_vptr = false;
        if (construction_complete_decl &&
            construction_complete_state &&
            !construction_complete_state->virtual_bases.empty()) {
            wrote_construction_vptr =
                emit_cpp_construction_vptr_store_from_vtt(
                    construction_complete_decl,
                    object_decl,
                    object_addr,
                    loc,
                    construction_context);
        }
        if (!wrote_construction_vptr) {
            emit_cpp_vptr_store(object_type, object_addr, loc, construction_context);
        }
    }

    for (const auto& field : object_state->fields) {
        if (field.is_bitfield || field.is_base_subobject ||
            field.is_virtual_base_storage) {
            continue;
        }
        auto field_record =
            desugar_type(field.type, ast_ctx.get()).as_shared<ObjectType>();
        if (!field_record) {
            continue;
        }

        llvm::Value* field_addr =
            subobject_addr_with_offset(
                static_cast<uint64_t>(field.offset),
                "implicit.ctor.field.addr");
        if (!emit_cpp_object_default_construction_recursive(
                field.type,
                field_addr,
                loc,
                construction_context,
                CppCtorDtorVariant::Complete,
                nullptr)) {
            return false;
        }
    }

    return true;
}

void ASTToLLVM::emit_cpp_object_teardown_recursive(
    const QualType& object_type,
    llvm::Value* object_addr,
    std::shared_ptr<Symbol> object_dtor_sym,
    SrcLoc loc,
    const std::string& teardown_context,
    CppCtorDtorVariant dtor_variant) {
    auto object_record =
        desugar_type(object_type, ast_ctx.get()).as_shared<ObjectType>();
    if (!object_record || !object_addr) {
        return;
    }

    const TagDecl* tag_decl = object_record->get_decl();
    const ObjectDecl* object_decl =
        (tag_decl && tag_decl->is_record_decl())
            ? static_cast<const ObjectDecl*>(tag_decl)
            : nullptr;
    const RecordSemanticState* object_state =
        object_decl ? record_semantics_cache_lookup(object_decl)
                    : nullptr;

    if (!object_dtor_sym) {
        object_dtor_sym = select_record_destructor_symbol(object_state, false);
    }
    if (object_dtor_sym &&
        object_dtor_sym->kind == SymbolKind::FUNCTION) {
        emit_cpp_destruct_call(
            object_dtor_sym,
            object_addr,
            loc,
            teardown_context,
            dtor_variant);
    }

    if (!object_state || object_record->is_union) {
        return;
    }

    bool has_nonvirtual_base_work = false;
    for (const auto& base : object_state->bases) {
        if (base.is_virtual || !base.record_decl || !base.has_non_virtual_offset) {
            continue;
        }
        has_nonvirtual_base_work = true;
        break;
    }
    bool has_virtual_base_work = false;
    if (dtor_variant == CppCtorDtorVariant::Complete) {
        for (const auto& virtual_base : object_state->virtual_bases) {
            if (!virtual_base.record_decl || !virtual_base.has_offset) {
                continue;
            }
            has_virtual_base_work = true;
            break;
        }
    }
    bool has_record_field_work = false;
    for (const auto& field : object_state->fields) {
        if (field.is_bitfield || field.is_base_subobject ||
            field.is_virtual_base_storage) {
            continue;
        }
        if (canonical_type_kind(field.type, ast_ctx.get()) != TypeKind::Object) {
            continue;
        }
        has_record_field_work = true;
        break;
    }
    if (!object_dtor_sym &&
        !has_nonvirtual_base_work &&
        !has_virtual_base_work &&
        !has_record_field_work) {
        return;
    }

    for (auto field_it = object_state->fields.rbegin();
         field_it != object_state->fields.rend();
         ++field_it) {
        const auto& field = *field_it;
        if (field.is_bitfield || field.is_base_subobject ||
            field.is_virtual_base_storage) {
            continue;
        }
        auto field_record =
            desugar_type(field.type, ast_ctx.get()).as_shared<ObjectType>();
        if (!field_record) {
            continue;
        }

        llvm::Value* field_addr = object_addr;
        if (field.offset != 0) {
            llvm::Type* i8_type = llvm::Type::getInt8Ty(*context);
            llvm::Value* field_offset = llvm::ConstantInt::get(
                llvm::Type::getInt64Ty(*context),
                static_cast<uint64_t>(field.offset));
            field_addr = builder.CreateInBoundsGEP(
                i8_type,
                object_addr,
                field_offset,
                "global.dtor.field.addr");
        }

        const TagDecl* field_tag_decl = field_record->get_decl();
        const ObjectDecl* field_decl =
            (field_tag_decl && field_tag_decl->is_record_decl())
                ? static_cast<const ObjectDecl*>(field_tag_decl)
                : nullptr;
        const RecordSemanticState* field_state =
            field_decl ? record_semantics_cache_lookup(field_decl)
                       : nullptr;
        std::shared_ptr<Symbol> field_dtor_sym =
            select_record_destructor_symbol(field_state, false);

        emit_cpp_object_teardown_recursive(
            field.type,
            field_addr,
            field_dtor_sym,
            loc,
            teardown_context,
            CppCtorDtorVariant::Base);
    }

    for (auto base_it = object_state->bases.rbegin();
         base_it != object_state->bases.rend();
         ++base_it) {
        const auto& base = *base_it;
        if (base.is_virtual || !base.record_decl || !base.has_non_virtual_offset) {
            continue;
        }

        llvm::Value* base_addr = object_addr;
        if (base.non_virtual_offset != 0) {
            llvm::Type* i8_type = llvm::Type::getInt8Ty(*context);
            llvm::Value* base_offset = llvm::ConstantInt::get(
                llvm::Type::getInt64Ty(*context),
                static_cast<uint64_t>(base.non_virtual_offset));
            base_addr = builder.CreateInBoundsGEP(
                i8_type,
                object_addr,
                base_offset,
                "global.dtor.base.addr");
        }

        const RecordSemanticState* base_state =
            record_semantics_cache_lookup(base.record_decl);
        std::shared_ptr<Symbol> base_dtor_sym =
            select_record_destructor_symbol(base_state, false);
        emit_cpp_object_teardown_recursive(
            base.type,
            base_addr,
            base_dtor_sym,
            loc,
            teardown_context,
            CppCtorDtorVariant::Base);
    }

    if (dtor_variant == CppCtorDtorVariant::Complete) {
        for (auto vbase_it = object_state->virtual_bases.rbegin();
             vbase_it != object_state->virtual_bases.rend();
             ++vbase_it) {
            const auto& virtual_base = *vbase_it;
            if (!virtual_base.record_decl || !virtual_base.has_offset) {
                continue;
            }

            llvm::Value* virtual_base_addr = object_addr;
            if (virtual_base.offset != 0) {
                llvm::Type* i8_type = llvm::Type::getInt8Ty(*context);
                llvm::Value* virtual_base_offset = llvm::ConstantInt::get(
                    llvm::Type::getInt64Ty(*context),
                    static_cast<uint64_t>(virtual_base.offset));
                virtual_base_addr = builder.CreateInBoundsGEP(
                    i8_type,
                    object_addr,
                    virtual_base_offset,
                    "global.dtor.vbase.addr");
            }

            const RecordSemanticState* virtual_base_state =
                record_semantics_cache_lookup(virtual_base.record_decl);
            std::shared_ptr<Symbol> virtual_base_dtor_sym =
                select_record_destructor_symbol(virtual_base_state, false);
            emit_cpp_object_teardown_recursive(
                virtual_base.type,
                virtual_base_addr,
                virtual_base_dtor_sym,
                loc,
                teardown_context,
                CppCtorDtorVariant::Base);
        }
    }
}

void ASTToLLVM::emit_cpp_global_object_dtor_thunk(
    const std::string& thunk_name,
    const QualType& object_type,
    llvm::Value* object_addr,
    std::shared_ptr<Symbol> selected_dtor_sym,
    SrcLoc loc,
    const std::string& teardown_context,
    llvm::GlobalValue::LinkageTypes thunk_linkage,
    llvm::Constant* comdat_association) {
    if (!object_addr) {
        return;
    }
    if (selected_dtor_sym &&
        selected_dtor_sym->kind != SymbolKind::FUNCTION) {
        return;
    }

    auto object_record =
        desugar_type(object_type, ast_ctx.get()).as_shared<ObjectType>();
    const ObjectDecl* object_decl = object_record
        ? canonical_cpp_record_decl(dyn_cast<ObjectDecl>(object_record->get_decl()))
        : nullptr;
    const RecordSemanticState* object_state = lookup_cpp_record_state(object_decl);
    if (!selected_dtor_sym) {
        selected_dtor_sym = select_record_destructor_symbol(object_state, false);
    }

    bool has_recursive_teardown_work = false;
    if (object_state) {
        if (!object_state->bases.empty() ||
            !object_state->virtual_bases.empty()) {
            has_recursive_teardown_work = true;
        } else {
            for (const auto& field : object_state->fields) {
                if (field.is_bitfield || field.is_base_subobject ||
                    field.is_virtual_base_storage) {
                    continue;
                }
                if (canonical_type_kind(field.type, ast_ctx.get()) == TypeKind::Object) {
                    has_recursive_teardown_work = true;
                    break;
                }
            }
        }
    }
    if (!selected_dtor_sym && !has_recursive_teardown_work) {
        return;
    }

    llvm::Function* dtor_thunk = module->getFunction(thunk_name);
    if (!dtor_thunk) {
        auto* thunk_type = llvm::FunctionType::get(
            llvm::Type::getVoidTy(*context), false);
        dtor_thunk = llvm::Function::Create(
            thunk_type,
            thunk_linkage,
            thunk_name,
            module.get());
        if (auto* associated_global =
                llvm::dyn_cast_or_null<llvm::GlobalObject>(comdat_association);
            associated_global && associated_global->hasComdat()) {
            dtor_thunk->setComdat(associated_global->getComdat());
        }
        llvm::appendToGlobalDtors(
            *module, dtor_thunk, 65535, comdat_association);
    }

    if (!dtor_thunk->empty()) {
        return;
    }

    llvm::BasicBlock* saved_block = builder.GetInsertBlock();
    auto saved_ip = builder.saveIP();

    llvm::BasicBlock* entry_bb =
        llvm::BasicBlock::Create(*context, "entry", dtor_thunk);
    builder.SetInsertPoint(entry_bb);

    emit_cpp_object_teardown_recursive(
        object_type,
        object_addr,
        selected_dtor_sym,
        loc,
        teardown_context,
        CppCtorDtorVariant::Complete);
    builder.CreateRetVoid();

    if (saved_block) {
        builder.restoreIP(saved_ip);
    } else {
        builder.ClearInsertionPoint();
    }
}

llvm::Function* ASTToLLVM::get_or_create_cpp_deleting_destructor_function(
    const std::shared_ptr<Symbol>& dtor_sym,
    SrcLoc loc,
    const std::string& context_name) {
    if (!dtor_sym || dtor_sym->kind != SymbolKind::FUNCTION) {
        error(context_name + ": invalid deleting-destructor symbol", loc);
    }

    auto dtor_type =
        desugar_type(dtor_sym->type, ast_ctx.get()).as_shared<FunctionType>();
    if (!dtor_type || dtor_type->parameters.empty()) {
        error(context_name + ": deleting destructor requires implicit object parameter",
              loc);
    }

    auto this_ptr_type =
        desugar_type(dtor_type->parameters.front(), ast_ctx.get())
            .as_shared<PointerType>();
    auto object_type =
        this_ptr_type
            ? desugar_type(this_ptr_type->pointed_type, ast_ctx.get())
                  .as_shared<ObjectType>()
            : nullptr;
    const ObjectDecl* object_decl = object_type
        ? canonical_cpp_record_decl(dyn_cast<ObjectDecl>(object_type->get_decl()))
        : nullptr;
    if (!object_decl || !object_decl->get_record_type()) {
        error(context_name + ": deleting destructor requires class object parameter", loc);
    }

    const RecordSemanticState* object_state = lookup_cpp_record_state(object_decl);
    std::shared_ptr<Symbol> deallocator_sym =
        select_record_deallocation_symbol(object_state, /*is_array_form=*/false);
    if (!deallocator_sym || deallocator_sym->kind != SymbolKind::FUNCTION) {
        error(context_name + ": failed to select scalar deallocation function", loc);
    }

    std::vector<llvm::Type*> param_types;
    param_types.reserve(dtor_type->parameters.size());
    for (const auto& param : dtor_type->parameters) {
        param_types.push_back(convert_param_type(param));
    }
    llvm::Type* return_type = convert_type(dtor_type->ret_type);
    auto* llvm_fn_type = llvm::FunctionType::get(
        return_type,
        param_types,
        dtor_type->is_variadic);

    std::string deleting_name = get_cpp_special_member_variant_llvm_name(
        dtor_sym, true, CppCtorDtorVariant::Deleting);
    llvm::Function* deleting_fn = module->getFunction(deleting_name);
    if (!deleting_fn) {
        deleting_fn = llvm::Function::Create(
            llvm_fn_type,
            llvm::Function::ExternalLinkage,
            deleting_name,
            module.get());
    }
    if (!deleting_fn->empty()) {
        return deleting_fn;
    }

    llvm::BasicBlock* saved_block = builder.GetInsertBlock();
    auto saved_ip = builder.saveIP();

    llvm::BasicBlock* entry_bb =
        llvm::BasicBlock::Create(*context, "entry", deleting_fn);
    builder.SetInsertPoint(entry_bb);

    llvm::Value* this_addr = deleting_fn->getArg(0);
    llvm::Value* deallocation_addr = recover_cpp_complete_object_address(
        this_addr,
        object_decl,
        loc,
        context_name,
        object_decl);
    emit_cpp_object_teardown_recursive(
        QualType(object_decl->get_record_type()),
        this_addr,
        dtor_sym,
        loc,
        context_name,
        CppCtorDtorVariant::Complete);

    if (!type_ctx) {
        error(context_name + ": deleting destructor requires builtin type context", loc);
    }
    QualType void_ptr_type(std::make_shared<PointerType>(
        QualType(type_ctx->get_builtin(BuiltinTypes::Void))));
    std::vector<std::pair<llvm::Value*, QualType>> deallocator_args;
    deallocator_args.emplace_back(deallocation_addr, void_ptr_type);
    if (!emit_cpp_operator_call(
            deallocator_sym,
            deallocator_args,
            loc,
            context_name)) {
        if (saved_block) {
            builder.restoreIP(saved_ip);
        } else {
            builder.ClearInsertionPoint();
        }
        return nullptr;
    }

    if (return_type->isVoidTy()) {
        builder.CreateRetVoid();
    } else if (return_type == this_addr->getType()) {
        builder.CreateRet(this_addr);
    } else {
        builder.CreateRet(llvm::Constant::getNullValue(return_type));
    }

    if (saved_block) {
        builder.restoreIP(saved_ip);
    } else {
        builder.ClearInsertionPoint();
    }
    return deleting_fn;
}

std::string ASTToLLVM::get_cpp_special_member_variant_llvm_name(
    const std::string& complete_name,
    bool is_destructor,
    CppCtorDtorVariant variant) const {
    if (variant == CppCtorDtorVariant::Complete) {
        return complete_name;
    }

    const std::string from_code = is_destructor ? "D1" : "C1";
    std::string to_code;
    if (variant == CppCtorDtorVariant::Base) {
        to_code = is_destructor ? "D2" : "C2";
    } else {
        to_code = is_destructor ? "D0" : "C1";
    }
    size_t code_pos = complete_name.rfind(from_code);
    if (code_pos == std::string::npos) {
        // Non-ABI test/JIT mode uses simple source spellings (e.g. "Derived"),
        // so C1/D1 markers may not be present. Keep complete naming unchanged
        // and synthesize stable internal sibling names for each variant.
        if (variant == CppCtorDtorVariant::Base) {
            return complete_name + ".cxx.base";
        }
        return complete_name + ".cxx.deleting";
    }
    std::string variant_name = complete_name;
    variant_name.replace(code_pos, from_code.size(), to_code);
    return variant_name;
}

std::string ASTToLLVM::get_cpp_special_member_variant_llvm_name(
    const std::shared_ptr<Symbol>& sym,
    bool is_destructor,
    CppCtorDtorVariant variant) const {
    if (!sym || sym->kind != SymbolKind::FUNCTION) {
        return "";
    }
    std::string complete_name = get_function_llvm_name(sym, sym->name);
    return get_cpp_special_member_variant_llvm_name(
        complete_name, is_destructor, variant);
}
