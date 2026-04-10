#include "ast2llvm.h"
#include "lower_helpers.h"
#include "const_lowering.h"
#include "../abi/darwin_blocks.h"
#include "../helpers/casting.h"
#include "../constexpr/consteval_compat.h"
#include "../numeric_utils.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include <llvm/TargetParser/Triple.h>
#include <algorithm>
#include <cstdlib>
#include <functional>
#include <limits>
#include <optional>
#include <unordered_set>

namespace {

std::shared_ptr<Expr> recover_record_field_initializer_expr(
    InitListExpr* init_list,
    size_t field_idx,
    const std::shared_ptr<ObjectType>& record_type) {
    if (!init_list) {
        return nullptr;
    }

    auto mapping_it = init_list->mappings.find(field_idx);
    if (mapping_it != init_list->mappings.end()) {
        return mapping_it->second;
    }

    std::shared_ptr<InitListExpr> recovered_nested;
    std::shared_ptr<Expr> recovered_direct;

    auto assign_nested_path = [&](const std::shared_ptr<InitListExpr>& root,
                                  const std::vector<size_t>& path,
                                  const std::shared_ptr<Expr>& value,
                                  SrcLoc loc) {
        if (!root || path.empty() || !value) {
            return;
        }
        InitListExpr* cur = root.get();
        for (size_t depth = 0; depth + 1 < path.size(); ++depth) {
            size_t idx = path[depth];
            auto it = cur->mappings.find(idx);
            if (it == cur->mappings.end() || !isa<InitListExpr>(it->second.get())) {
                auto next = std::make_shared<InitListExpr>(loc);
                cur->mappings[idx] = next;
                cur = next.get();
            } else {
                cur = static_cast<InitListExpr*>(it->second.get());
            }
        }
        cur->mappings[path.back()] = value;
    };

    for (const auto& action : init_list->actions) {
        for (const auto& path : action.paths) {
            if (path.empty() || path[0] != field_idx || !action.value) {
                continue;
            }
            if (path.size() == 1) {
                recovered_direct = action.value;
                continue;
            }
            if (!recovered_nested) {
                recovered_nested = std::make_shared<InitListExpr>(action.loc);
                if (record_type && field_idx < record_type->semantic_fields().size()) {
                    recovered_nested->type =
                        record_type->semantic_fields()[field_idx].type;
                }
            }
            std::vector<size_t> subpath(path.begin() + 1, path.end());
            assign_nested_path(recovered_nested, subpath, action.value, action.loc);
        }
    }

    if (recovered_nested) {
        return recovered_nested;
    }
    return recovered_direct;
}

std::optional<size_t> get_flexible_array_initializer_count(
    ASTToLLVM& lower,
    const std::shared_ptr<ObjectType>& record_type,
    InitListExpr* init_list) {
    if (!record_type || !init_list || record_type->is_union ||
        !record_type->semantic_has_flexible_array_member()) {
        return std::nullopt;
    }

    const auto& fields = record_type->semantic_fields();
    if (fields.empty()) {
        return std::nullopt;
    }

    size_t field_idx = fields.size() - 1;
    auto fam_type = dyn_cast_shared<ArrayType>(
        desugar_type(fields.back().type, lower.ast_ctx.get()).get_shared());
    if (!fam_type || fam_type->size_kind != ArraySizeKind::Incomplete) {
        return std::nullopt;
    }

    auto field_expr =
        recover_record_field_initializer_expr(init_list, field_idx, record_type);
    if (!field_expr) {
        return size_t{0};
    }

    if (auto* nested = unwrap_init_list_expr(field_expr.get())) {
        if (nested->mappings.empty()) {
            return size_t{0};
        }
        return nested->mappings.rbegin()->first + 1;
    }

    if (auto* str_lit = unwrap_string_literal_expr(field_expr.get())) {
        auto str_lit_type = str_lit->ctype.as_shared<ArrayType>();
        if (str_lit_type && str_lit_type->size_kind == ArraySizeKind::Constant &&
            str_lit_type->size.has_value()) {
            return str_lit_type->size.value();
        }
    }

    return std::nullopt;
}

llvm::Type* build_flexible_array_storage_type(
    ASTToLLVM& lower,
    const std::shared_ptr<ObjectType>& record_type,
    size_t fam_count) {
    if (!record_type || record_type->is_union ||
        !record_type->semantic_has_flexible_array_member() ||
        record_uses_byte_layout(record_type.get())) {
        return nullptr;
    }

    const auto& fields = record_type->semantic_fields();
    if (fields.empty()) {
        return nullptr;
    }

    auto fam_type = dyn_cast_shared<ArrayType>(
        desugar_type(fields.back().type, lower.ast_ctx.get()).get_shared());
    if (!fam_type || fam_type->size_kind != ArraySizeKind::Incomplete) {
        return nullptr;
    }

    llvm::Type* fam_elem_type = lower.convert_type(fam_type->element_type.get_shared());
    if (!fam_elem_type) {
        return nullptr;
    }

    std::vector<llvm::Type*> field_types;
    size_t current_offset = 0;
    for (size_t field_idx = 0; field_idx < fields.size(); ++field_idx) {
        const auto& field = fields[field_idx];
        if (field.offset > current_offset) {
            field_types.push_back(
                llvm::ArrayType::get(llvm::Type::getInt8Ty(*lower.context),
                                     field.offset - current_offset));
            current_offset = field.offset;
        }

        llvm::Type* llvm_field_ty = nullptr;
        size_t field_size = 0;
        bool is_last_field = (field_idx + 1 == fields.size());
        if (is_last_field) {
            llvm_field_ty = llvm::ArrayType::get(fam_elem_type, fam_count);
            field_size = lower.module->getDataLayout().getTypeAllocSize(llvm_field_ty);
        } else if (field.is_base_subobject || field.storage_size_override > 0) {
            field_size = object_field_storage_size_bytes(field);
            llvm_field_ty = llvm::ArrayType::get(
                llvm::Type::getInt8Ty(*lower.context), field_size);
        } else {
            llvm_field_ty = lower.convert_type(field.type.get_shared());
            field_size = object_field_storage_size_bytes(field);
        }

        field_types.push_back(llvm_field_ty);
        current_offset += field_size;
    }

    size_t alignment = record_type->getAlignment();
    if (alignment == 0) {
        alignment = 1;
    }
    if (current_offset % alignment != 0) {
        field_types.push_back(
            llvm::ArrayType::get(llvm::Type::getInt8Ty(*lower.context),
                                 alignment - (current_offset % alignment)));
    }

    return llvm::StructType::get(*lower.context, field_types, /*isPacked=*/false);
}

llvm::Type* convert_global_storage_type(ASTToLLVM& lower,
                                        QualType type,
                                        Expr* init_expr) {
    auto record_type =
        desugar_type(type, lower.ast_ctx.get()).as_shared<ObjectType>();
    auto* init_list = unwrap_init_list_expr(init_expr);
    if (!record_type || !init_list) {
        return lower.convert_type(type);
    }

    auto fam_count =
        get_flexible_array_initializer_count(lower, record_type, init_list);
    if (!fam_count.has_value()) {
        return lower.convert_type(type);
    }
    if (*fam_count == 0) {
        return lower.convert_type(type);
    }

    if (auto* storage_type =
            build_flexible_array_storage_type(lower, record_type, *fam_count)) {
        return storage_type;
    }
    return lower.convert_type(type);
}

llvm::Value* materialize_indirect_aggregate_ctor_argument(
    ASTToLLVM& lower,
    const QualType& param_type,
    Expr* arg_expr,
    SrcLoc loc,
    const std::string& context) {
    auto param_canonical = desugar_type(param_type, lower.ast_ctx.get());
    auto record_type = param_canonical.as_shared<ObjectType>();
    if (!record_type || record_type->isIncomplete()) {
        lower.error(context + ": invalid aggregate constructor parameter", loc);
        return nullptr;
    }

    llvm::Type* agg_ty = lower.convert_type(param_canonical.get_shared());
    if (!agg_ty) {
        lower.error(context + ": failed to lower aggregate constructor type", loc);
        return nullptr;
    }

    llvm::Function* function = lower.builder.GetInsertBlock()->getParent();
    auto* tmp = lower.create_entry_alloca(function, agg_ty, nullptr, "ctor.byref.tmp");
    if (!tmp) {
        lower.error(context + ": failed to allocate aggregate constructor temporary",
                    loc);
        return nullptr;
    }

    llvm::Align agg_align = lower.module->getDataLayout().getABITypeAlign(agg_ty);
    tmp->setAlignment(agg_align);

    Expr* lvalue_base = arg_expr;
    while (auto* cast = dyn_cast<ImplicitCast>(lvalue_base)) {
        lvalue_base = cast->expr.get();
    }

    llvm::Value* src_ptr = lower.get_lvalue(lvalue_base).address;
    if (src_ptr) {
        uint64_t size_bytes =
            static_cast<uint64_t>(std::max<int64_t>(0, record_type->getWidthBytes()));
        if (size_bytes > 0) {
            lower.builder.CreateMemCpy(
                tmp, llvm::MaybeAlign(agg_align), src_ptr, llvm::MaybeAlign(1), size_bytes);
        }
        return tmp;
    }

    llvm::Value* arg_val = lower.convert_expression(arg_expr);
    if (!arg_val) {
        lower.error(context + ": invalid aggregate constructor argument", loc);
        return nullptr;
    }
    if (arg_val->getType() != agg_ty) {
        lower.error(context + ": aggregate constructor argument type mismatch", loc);
        return nullptr;
    }

    auto* store = lower.builder.CreateStore(arg_val, tmp);
    store->setAlignment(agg_align);
    return tmp;
}

llvm::Value* materialize_direct_aggregate_ctor_argument(
    ASTToLLVM& lower,
    const QualType& param_type,
    Expr* arg_expr,
    SrcLoc loc,
    const std::string& context) {
    llvm::Type* abi_type = lower.get_direct_aggregate_parameter_abi_type(param_type);
    auto param_canonical = desugar_type(param_type, lower.ast_ctx.get());
    auto record_type = param_canonical.as_shared<ObjectType>();
    if (!abi_type || !record_type || record_type->isIncomplete()) {
        lower.error(context + ": invalid aggregate constructor ABI parameter", loc);
        return nullptr;
    }

    llvm::Type* agg_ty = lower.convert_type(param_canonical.get_shared());
    if (!agg_ty) {
        lower.error(context + ": failed to lower aggregate constructor type", loc);
        return nullptr;
    }

    Expr* lvalue_base = arg_expr;
    while (auto* cast = dyn_cast<ImplicitCast>(lvalue_base)) {
        lvalue_base = cast->expr.get();
    }

    llvm::Value* src_ptr = lower.get_lvalue(lvalue_base).address;
    if (!src_ptr) {
        llvm::Value* arg_val = lower.convert_expression(arg_expr);
        if (!arg_val) {
            lower.error(context + ": invalid aggregate constructor argument", loc);
            return nullptr;
        }
        if (arg_val->getType() != agg_ty) {
            lower.error(context + ": aggregate constructor argument type mismatch", loc);
            return nullptr;
        }

        llvm::Function* function = lower.builder.GetInsertBlock()->getParent();
        auto* tmp = lower.create_entry_alloca(function, agg_ty, nullptr, "ctor.coerce.tmp");
        if (!tmp) {
            lower.error(context + ": failed to allocate aggregate constructor temporary",
                        loc);
            return nullptr;
        }
        llvm::Align agg_align =
            lower.module->getDataLayout().getABITypeAlign(agg_ty);
        tmp->setAlignment(agg_align);
        auto* store = lower.builder.CreateStore(arg_val, tmp);
        store->setAlignment(agg_align);
        src_ptr = tmp;
    }

    return lower.load_aggregate_memory_as_abi_value(
        src_ptr, param_type, abi_type, loc, "materialize_direct_aggregate_ctor_argument()");
}

std::string block_byref_helper_suffix(const VariableDecl* var_decl) {
    if (!var_decl) {
        return "invalid";
    }
    if (var_decl->sym) {
        return ASTToLLVM::mangleCIdentifier(var_decl->sym->uid);
    }
    if (var_decl->node_id != 0) {
        return std::to_string(var_decl->node_id);
    }
    if (!var_decl->location.isInvalid()) {
        return std::to_string(var_decl->location.offset);
    }
    return "invalid";
}

llvm::StructType* build_block_byref_cell_type(ASTToLLVM& lower,
                                              QualType value_type,
                                              bool has_copy_dispose_helpers) {
    llvm::Type* ptr_ty = llvm::PointerType::get(*lower.context, 0);
    llvm::Type* i32_ty = llvm::Type::getInt32Ty(*lower.context);
    llvm::Type* payload_ty = lower.convert_type(
        remove_reference(value_type, lower.ast_ctx.get()).get_shared());
    if (!payload_ty) {
        return nullptr;
    }

    std::vector<llvm::Type*> fields = {ptr_ty, ptr_ty, i32_ty, i32_ty};
    if (has_copy_dispose_helpers) {
        fields.push_back(ptr_ty);
        fields.push_back(ptr_ty);
    }
    fields.push_back(payload_ty);
    return llvm::StructType::get(*lower.context, fields, /*isPacked=*/false);
}

llvm::Function* get_or_create_block_byref_keep_helper(ASTToLLVM& lower,
                                                      const VariableDecl* var_decl) {
    if (!var_decl ||
        !lower.block_byref_requires_copy_dispose_helpers(var_decl->type)) {
        return nullptr;
    }

    std::string name =
        "__block_byref_keep_" + block_byref_helper_suffix(var_decl);
    if (auto* existing = lower.module->getFunction(name)) {
        return existing;
    }

    llvm::Type* ptr_ty = llvm::PointerType::get(*lower.context, 0);
    auto* fn_ty = llvm::FunctionType::get(
        llvm::Type::getVoidTy(*lower.context),
        {ptr_ty, ptr_ty},
        false);
    auto* fn = llvm::Function::Create(
        fn_ty,
        llvm::Function::InternalLinkage,
        name,
        lower.module.get());

    llvm::IRBuilderBase::InsertPointGuard guard(lower.builder);
    auto* entry_bb = llvm::BasicBlock::Create(*lower.context, "entry", fn);
    lower.builder.SetInsertPoint(entry_bb);

    auto arg_it = fn->arg_begin();
    llvm::Value* dst_cell = &*arg_it++;
    llvm::Value* src_cell = &*arg_it;
    llvm::Value* dst_payload_addr = lower.get_block_byref_payload_address(
        dst_cell,
        var_decl->type,
        var_decl->location,
        "block byref keep helper");
    llvm::Value* src_payload_addr = lower.get_block_byref_payload_address(
        src_cell,
        var_decl->type,
        var_decl->location,
        "block byref keep helper");
    llvm::Type* payload_ty = lower.convert_type(
        remove_reference(var_decl->type, lower.ast_ctx.get()).get_shared());
    llvm::Value* src_payload = lower.builder.CreateLoad(
        payload_ty,
        src_payload_addr,
        "block.byref.keep.payload");
    if (src_payload->getType() != ptr_ty) {
        src_payload = lower.builder.CreatePointerCast(
            src_payload,
            ptr_ty,
            "block.byref.keep.cast");
    }

    uint32_t object_flags =
        lower.block_object_field_flags_for_type(var_decl->type, true);
    lower.builder.CreateCall(
        lower.get_or_create_block_object_assign(),
        {dst_payload_addr,
         src_payload,
         llvm::ConstantInt::get(
             llvm::Type::getInt32Ty(*lower.context),
             object_flags)});
    lower.builder.CreateRetVoid();
    return fn;
}

llvm::Function* get_or_create_block_byref_destroy_helper(ASTToLLVM& lower,
                                                         const VariableDecl* var_decl) {
    if (!var_decl ||
        !lower.block_byref_requires_copy_dispose_helpers(var_decl->type)) {
        return nullptr;
    }

    std::string name =
        "__block_byref_destroy_" + block_byref_helper_suffix(var_decl);
    if (auto* existing = lower.module->getFunction(name)) {
        return existing;
    }

    llvm::Type* ptr_ty = llvm::PointerType::get(*lower.context, 0);
    auto* fn_ty = llvm::FunctionType::get(
        llvm::Type::getVoidTy(*lower.context),
        {ptr_ty},
        false);
    auto* fn = llvm::Function::Create(
        fn_ty,
        llvm::Function::InternalLinkage,
        name,
        lower.module.get());

    llvm::IRBuilderBase::InsertPointGuard guard(lower.builder);
    auto* entry_bb = llvm::BasicBlock::Create(*lower.context, "entry", fn);
    lower.builder.SetInsertPoint(entry_bb);

    llvm::Value* cell = &*fn->arg_begin();
    llvm::Value* payload_addr = lower.get_block_byref_payload_address(
        cell,
        var_decl->type,
        var_decl->location,
        "block byref destroy helper");
    llvm::Type* payload_ty = lower.convert_type(
        remove_reference(var_decl->type, lower.ast_ctx.get()).get_shared());
    llvm::Value* payload = lower.builder.CreateLoad(
        payload_ty,
        payload_addr,
        "block.byref.destroy.payload");
    if (payload->getType() != ptr_ty) {
        payload = lower.builder.CreatePointerCast(
            payload,
            ptr_ty,
            "block.byref.destroy.cast");
    }

    uint32_t object_flags =
        lower.block_object_field_flags_for_type(var_decl->type, true);
    lower.builder.CreateCall(
        lower.get_or_create_block_object_dispose(),
        {payload,
         llvm::ConstantInt::get(
             llvm::Type::getInt32Ty(*lower.context),
             object_flags)});
    lower.builder.CreateRetVoid();
    return fn;
}

bool variable_decl_is_static_data_member(ASTToLLVM& lower,
                                         const VariableDecl* var_decl) {
    if (!var_decl || !lower.ast_ctx) {
        return false;
    }
    const auto* member_info =
        lower.ast_ctx->get_cpp_member_decl_info(var_decl->node_id);
    return member_info && !member_info->is_method && member_info->is_static;
}

std::optional<std::string> variable_decl_weakref_target(
    ASTToLLVM& lower,
    const VariableDecl* var_decl) {
    if (!var_decl || !lower.ast_ctx) {
        return std::nullopt;
    }
    for (const auto& attr : lower.ast_ctx->get_attrs(var_decl->node_id).attrs) {
        if (attr.canonical_name() != "weakref" ||
            attr.args.empty() ||
            attr.args[0].kind != AttributeArg::Kind::STRING ||
            attr.args[0].str_value.empty()) {
            continue;
        }
        return attr.args[0].str_value;
    }
    return std::nullopt;
}

std::string weakref_alias_llvm_name(ASTToLLVM& lower,
                                    const VariableDecl& decl) {
    if (decl.sym &&
        (decl.sym->linkage == VariableLinkage::INTERNAL ||
         decl.sym->linkage == VariableLinkage::NONE ||
         decl.storage_class == StorageClass::STATIC)) {
        return ASTToLLVM::mangleCIdentifier(decl.sym->uid);
    }
    if (decl.sym) {
        return lower.get_variable_llvm_name(decl.sym, decl.name);
    }
    if (!decl.name.empty()) {
        return decl.name;
    }
    return "";
}

llvm::GlobalValue::LinkageTypes weakref_alias_linkage(
    const VariableDecl* var_decl) {
    if (!var_decl || !var_decl->sym) {
        return llvm::GlobalValue::ExternalLinkage;
    }
    if (var_decl->sym->linkage == VariableLinkage::INTERNAL ||
        var_decl->storage_class == StorageClass::STATIC) {
        return llvm::GlobalValue::InternalLinkage;
    }
    return llvm::GlobalValue::ExternalLinkage;
}

llvm::GlobalValue* get_or_create_variable_weakref_alias(
    ASTToLLVM& lower,
    const VariableDecl* var_decl,
    llvm::Type* var_type) {
    auto weakref_target = variable_decl_weakref_target(lower, var_decl);
    if (!weakref_target || !var_decl || !var_decl->sym || !var_type) {
        return nullptr;
    }

    std::string alias_name = weakref_alias_llvm_name(lower, *var_decl);
    if (alias_name.empty()) {
        return nullptr;
    }

    if (auto* alias = lower.module->getNamedAlias(alias_name)) {
        return alias;
    }
    if (auto* existing = lower.module->getGlobalVariable(alias_name, true)) {
        return existing;
    }

    llvm::GlobalVariable* aliasee =
        lower.module->getGlobalVariable(*weakref_target, true);
    if (!aliasee) {
        aliasee = lower.module->getGlobalVariable(
            ASTToLLVM::get_asm_label_name(*weakref_target),
            true);
    }
    if (!aliasee) {
        aliasee = new llvm::GlobalVariable(
            *lower.module,
            var_type,
            var_decl->type.is_const(),
            llvm::GlobalValue::ExternalWeakLinkage,
            nullptr,
            *weakref_target);
    }

    return llvm::GlobalAlias::create(
        var_type,
        aliasee->getAddressSpace(),
        weakref_alias_linkage(var_decl),
        alias_name,
        aliasee,
        lower.module.get());
}

bool variable_decl_is_definition_bearing(ASTToLLVM& lower,
                                         const VariableDecl* var_decl) {
    if (!var_decl) {
        return false;
    }
    if (variable_decl_is_static_data_member(lower, var_decl)) {
        return var_decl->is_inline || var_decl->init != nullptr;
    }
    return var_decl->storage_class != StorageClass::EXTERN ||
           var_decl->init != nullptr;
}

bool variable_decl_is_inline_equivalent_external_definition(
    ASTToLLVM& lower,
    const VariableDecl* var_decl) {
    if (!var_decl || !var_decl->sym ||
        var_decl->sym->linkage != VariableLinkage::EXTERNAL ||
        !variable_decl_is_definition_bearing(lower, var_decl)) {
        return false;
    }
    if (var_decl->is_inline) {
        return true;
    }
    return variable_decl_is_static_data_member(lower, var_decl) &&
           var_decl->is_constexpr &&
           var_decl->init != nullptr;
}

llvm::GlobalValue::LinkageTypes variable_global_linkage(ASTToLLVM& lower,
                                                        const VariableDecl* var_decl) {
    if (!var_decl || !var_decl->sym) {
        return llvm::GlobalValue::ExternalLinkage;
    }
    if (var_decl->sym->linkage == VariableLinkage::INTERNAL ||
        (var_decl->sym->linkage == VariableLinkage::NONE &&
         var_decl->storage_class == StorageClass::STATIC)) {
        return llvm::GlobalValue::InternalLinkage;
    }
    if (variable_decl_is_inline_equivalent_external_definition(lower, var_decl)) {
        return llvm::GlobalValue::LinkOnceODRLinkage;
    }
    return llvm::GlobalValue::ExternalLinkage;
}

void configure_variable_global_linkage(ASTToLLVM& lower,
                                       const VariableDecl* var_decl,
                                       llvm::GlobalVariable* gvar) {
    if (!var_decl || !gvar) {
        return;
    }
    llvm::GlobalValue::LinkageTypes linkage =
        variable_global_linkage(lower, var_decl);
    if (gvar->getLinkage() == llvm::GlobalValue::LinkOnceODRLinkage &&
        linkage != llvm::GlobalValue::LinkOnceODRLinkage) {
        return;
    }
    gvar->setLinkage(linkage);
    if (linkage != llvm::GlobalValue::LinkOnceODRLinkage) {
        return;
    }
    llvm::Triple triple(lower.module->getTargetTriple());
    if (!triple.supportsCOMDAT()) {
        return;
    }
    std::string comdat_key = lower.get_variable_linkage_identity(*var_decl);
    if (comdat_key.empty()) {
        return;
    }
    gvar->setComdat(lower.module->getOrInsertComdat(comdat_key));
}

} // namespace

void ASTToLLVM::deal_global_variable_declaration(Decl *decl) {
    if (auto* cpp_record = dyn_cast<CppRecordDecl>(decl)) {
        for (const auto& member : cpp_record->members) {
            if (!member) {
                continue;
            }
            if (auto* static_member = dyn_cast<VariableDecl>(member.get())) {
                if (static_member->storage_class == StorageClass::STATIC &&
                    variable_decl_is_definition_bearing(*this, static_member)) {
                    deal_global_variable_declaration(static_member);
                }
                continue;
            }
            if (isa<CppRecordDecl>(member.get())) {
                deal_global_variable_declaration(member.get());
            }
        }
        return;
    }
    auto* varDecl = dyn_cast<VariableDecl>(decl);
    if (!varDecl) return;
    auto sym = varDecl->sym;
    if (sym == nullptr) {
        error("deal_global_variable_declaration(): variable not in scope during ast2llvm", decl->location);
        return;
    }
    if (sym->linkage != VariableLinkage::EXTERNAL && sym->linkage != VariableLinkage::INTERNAL) {
        error("deal_global_variable_declaration(): Invalid declaration linkage", decl->location);
        return;
    }
    std::string mangled = mangleCIdentifier(sym->uid);
    std::string linkage_identity = get_variable_linkage_identity(*varDecl);
    // Global variable
    // Check if it already exists (e.g. extern declaration)
    llvm::Type* varType = convert_global_storage_type(*this, varDecl->type, varDecl->init.get());
    auto coerce_global_initializer_constant =
        [&](llvm::Constant* constant) -> llvm::Constant* {
            if (!constant || !varType || constant->getType() == varType) {
                return constant;
            }
            bool src_unsigned =
                varDecl->init && varDecl->init->get_type() &&
                varDecl->init->get_type()->isUnsigned();
            bool dst_unsigned = varDecl->type && varDecl->type->isUnsigned();
            return fold_constant_cast(
                constant,
                varType,
                src_unsigned,
                dst_unsigned,
                module->getDataLayout());
        };
    if (llvm::GlobalValue* weak_alias =
            get_or_create_variable_weakref_alias(*this, varDecl, varType)) {
        named_values[mangled] = weak_alias;
        return;
    }
    std::string var_name_get = get_variable_llvm_name(*varDecl);
    llvm::GlobalVariable* gVar = module->getGlobalVariable(var_name_get, true);

    // Create the global variable first (before evaluating initializer) so that
    // self-referential initializers like LIST_HEAD can take the address of the
    // variable being defined.
    if (!gVar) {
        gVar = new llvm::GlobalVariable(
            *module,
            varType,
            varDecl->type.is_const(), // isConstant
            variable_global_linkage(*this, varDecl),
            nullptr, // initializer set below
            var_name_get
        );
        if (varDecl->is_thread_local) {
            gVar->setThreadLocalMode(llvm::GlobalVariable::GeneralDynamicTLSModel);
        }
    } else if (varDecl->init && gVar->getValueType() != varType) {
        // Definition has a different (more complete) type than the existing
        // declaration (e.g., extern T[] followed by T[] = {...}).
        // Replace the old GlobalVariable with a new one of the correct type.
        auto* oldGVar = gVar;
        gVar = new llvm::GlobalVariable(
            *module,
            varType,
            varDecl->type.is_const(),
            variable_global_linkage(*this, varDecl),
            nullptr,
            var_name_get + ".new"
        );
        oldGVar->replaceAllUsesWith(gVar);
        gVar->takeName(oldGVar);
        oldGVar->eraseFromParent();
    }
    configure_variable_global_linkage(*this, varDecl, gVar);
    named_values[mangled] = gVar;

    // Now evaluate the initializer (the variable is already in named_values)
    llvm::Constant* initVal = nullptr;
    if (varDecl->init) {
        if (is_global_defined.contains(varDecl->name)) {
            error("re-defining global variable", varDecl->location);
        } else {
            llvm::Value* val = nullptr;
            if (canonical_type_kind(varDecl->type, ast_ctx.get()) ==
                TypeKind::Reference) {
                auto ref_type =
                    desugar_type(varDecl->type, ast_ctx.get())
                        .as_shared<ReferenceType>();
                if (!ref_type || !ref_type->referred_type) {
                    error("deal_global_variable_declaration(): invalid reference type",
                          varDecl->location);
                    return;
                }

                Expr* binding_expr = unwrap_lvalue_to_rvalue_casts(varDecl->init.get());

                llvm::Value* bound_addr = get_lvalue(binding_expr).address;
                if (!bound_addr) {
                    // const T& global_ref = <constant-prvalue>;
                    llvm::Type* referred_llvm_type = convert_type(ref_type->referred_type.get_shared());
                    if (!referred_llvm_type) {
                        error("deal_global_variable_declaration(): failed to lower reference target type",
                              varDecl->location);
                        return;
                    }
                    auto* referred_init = emit_constant_initializer(varDecl->init.get());
                    if (!referred_init) {
                        error("deal_global_variable_declaration(): global reference initializer must bind to a global lvalue or constant temporary",
                              varDecl->location);
                        return;
                    }
                    if (referred_init->getType() != referred_llvm_type) {
                        bool src_uns = varDecl->init->get_type() && varDecl->init->get_type()->isUnsigned();
                        bool dst_uns = ref_type->referred_type && ref_type->referred_type->isUnsigned();
                        referred_init = fold_constant_cast(
                            referred_init,
                            referred_llvm_type,
                            src_uns,
                            dst_uns,
                            module->getDataLayout());
                        if (!referred_init || referred_init->getType() != referred_llvm_type) {
                            error("deal_global_variable_declaration(): failed to fold global reference temporary initializer",
                                  varDecl->location);
                            return;
                        }
                    }

                    static uint64_t global_ref_temp_counter = 0;
                    std::string temp_name =
                        mangleCIdentifier(sym->uid) + ".ref.tmp." +
                        std::to_string(global_ref_temp_counter++);
                    auto* temp_global = new llvm::GlobalVariable(
                        *module,
                        referred_llvm_type,
                        ref_type->referred_type.is_const(),
                        llvm::GlobalValue::InternalLinkage,
                        referred_init,
                        temp_name);
                    bound_addr = temp_global;
                }
                auto* bound_const = llvm::dyn_cast<llvm::Constant>(bound_addr);
                if (!bound_const) {
                    error("deal_global_variable_declaration(): reference initializer must be a constant address",
                          varDecl->location);
                    return;
                }
                initVal = bound_const;
            } else if (auto* initList = dyn_cast<InitListExpr>(varDecl->init.get())) {
                val = convert_init_list(initList, varType);
            } else if (auto *strLit = dyn_cast<StringLiteral>(varDecl->init.get())) {
                // For global char[] = "string", set the string data as the
                // initializer of the GlobalVariable (not a separate anonymous string)
                auto arr_type_s = strLit->ctype.as_shared<ArrayType>();
                if (arr_type_s && arr_type_s->size_kind == ArraySizeKind::Constant && arr_type_s->size.has_value()) {
                    size_t len = arr_type_s->size.value();
                    initVal = build_string_literal_array_constant(strLit, len);
                    if (!initVal) {
                        error("deal_global_variable_declaration(): unsupported string literal initializer type",
                              varDecl->location);
                    }
                } else {
                    val = convert_string_literal(strLit);
                    named_values[mangled] = val;
                    return;
                }
            } else {
                // Try constant evaluator first (avoids crash when no basic block)
                auto* constVal = emit_constant_initializer(varDecl->init.get());
                if (constVal) {
                    val = constVal;
                } else {
                    val = convert_expression(varDecl->init.get());
                }
            }
            if (!initVal) {
                auto* constant = llvm::dyn_cast<llvm::Constant>(val);
                if (constant == nullptr) {
                    error("deal_global_variable_declaration(): "
                          "init to global variable was not a constant", decl->location); // should be caught by sema
                    return;
                }
                constant = coerce_global_initializer_constant(constant);
                if (!constant) {
                    error("deal_global_variable_declaration(): failed to coerce global initializer to variable type",
                          decl->location);
                    return;
                }
                initVal = constant;
            }
        }
    }

    if (!initVal &&
        variable_decl_is_definition_bearing(*this, varDecl)
        && !gVar->hasInitializer()) {
        // Tentative definition or definition without initializer: initialize to zero
        if (varType->isArrayTy()) {
            initVal = llvm::ConstantAggregateZero::get(varType);
        } else {
            initVal = llvm::Constant::getNullValue(varType);
        }
    }
    if (initVal) {
        gVar->setInitializer(initVal);
    }
    // Apply variable attributes
    for (const auto& attr : ast_ctx->get_attrs(varDecl->node_id).attrs) {
        switch (attr.resolved_kind) {
            case AttributeKind::ALIGNED:
                if (!attr.args.empty() && attr.args[0].kind == AttributeArg::Kind::INTEGER) {
                    int64_t raw_align = attr.args[0].int_value;
                    if (raw_align > 0) {
                        uint64_t align = static_cast<uint64_t>(raw_align);
                        if ((align & (align - 1)) == 0) {
                            gVar->setAlignment(llvm::Align(align));
                        }
                    }
                }
                break;
            case AttributeKind::SECTION:
                if (!attr.args.empty() && attr.args[0].kind == AttributeArg::Kind::STRING) {
                    gVar->setSection(attr.args[0].str_value);
                }
                break;
            case AttributeKind::WEAK:
                gVar->setLinkage(llvm::GlobalValue::WeakAnyLinkage);
                break;
            case AttributeKind::COMMON_ATTR:
                gVar->setLinkage(llvm::GlobalValue::CommonLinkage);
                if (!gVar->hasInitializer()) {
                    gVar->setInitializer(llvm::Constant::getNullValue(varType));
                }
                gVar->setConstant(false);
                break;
            case AttributeKind::VISIBILITY: {
                if (!attr.args.empty() && attr.args[0].kind == AttributeArg::Kind::STRING) {
                    const auto& vis = attr.args[0].str_value;
                    if (vis == "default") gVar->setVisibility(llvm::GlobalValue::DefaultVisibility);
                    else if (vis == "hidden") gVar->setVisibility(llvm::GlobalValue::HiddenVisibility);
                    else if (vis == "protected") gVar->setVisibility(llvm::GlobalValue::ProtectedVisibility);
                }
                break;
            }
            case AttributeKind::USED:
                llvm::appendToCompilerUsed(*module, {gVar});
                break;
            default:
                break;
        }
    }

    if (ast_ctx &&
        !varDecl->is_thread_local &&
        canonical_type_kind(varDecl->type, ast_ctx.get()) == TypeKind::Object &&
        variable_decl_is_definition_bearing(*this, varDecl)) {
        auto* selected_dtor_sym_ptr =
            ast_ctx->get_cpp_variable_destructor_symbol(varDecl->node_id);
        std::shared_ptr<Symbol> selected_dtor_sym =
            selected_dtor_sym_ptr ? *selected_dtor_sym_ptr : nullptr;
        bool mergeable_dtor_thunk =
            variable_decl_is_inline_equivalent_external_definition(*this, varDecl);
        std::string dtor_thunk_name = linkage_identity + ".cxx.global.dtor";
        emit_cpp_global_object_dtor_thunk(
            dtor_thunk_name,
            varDecl->type,
            gVar,
            selected_dtor_sym,
            varDecl->location,
            "deal_global_variable_declaration() global dtor thunk",
            mergeable_dtor_thunk
                ? llvm::GlobalValue::LinkOnceODRLinkage
                : llvm::GlobalValue::InternalLinkage,
            mergeable_dtor_thunk
                ? static_cast<llvm::Constant*>(gVar)
                : nullptr);
    }
}

bool ASTToLLVM::emit_cpp_construct_call(const CppConstructExpr* ctor_init,
                                        llvm::Value* object_addr,
                                        SrcLoc loc,
                                        const std::string& context,
                                        CppCtorDtorVariant variant) {
    if (!ctor_init) {
        return false;
    }
    return emit_cpp_construct_call(
        ctor_init->ctor_sym,
        ctor_init->args,
        object_addr,
        loc,
        context,
        variant);
}

bool ASTToLLVM::emit_cpp_construct_call(const std::shared_ptr<Symbol>& ctor_sym,
                                        const std::vector<std::unique_ptr<Expr>>& ctor_args,
                                        llvm::Value* object_addr,
                                        SrcLoc loc,
                                        const std::string& context,
                                        CppCtorDtorVariant variant) {
    if (!object_addr) {
        return false;
    }
    if (!ctor_sym || ctor_sym->kind != SymbolKind::FUNCTION) {
        error(context + ": selected constructor symbol is invalid", loc);
        return false;
    }
    auto ctor_type = ctor_sym->type.as_shared<FunctionType>();
    if (!ctor_type) {
        error(context + ": selected constructor has non-function type", loc);
        return false;
    }
    if (ctor_type->parameters.empty()) {
        error(context + ": selected constructor is missing implicit object parameter", loc);
        return false;
    }

    std::vector<llvm::Type*> param_types;
    param_types.reserve(ctor_type->parameters.size());
    for (const auto& param : ctor_type->parameters) {
        param_types.push_back(convert_param_type(param));
    }
    llvm::Type* return_type = convert_type(ctor_type->ret_type);
    auto* llvm_fn_type = llvm::FunctionType::get(
        return_type,
        param_types,
        ctor_type->is_variadic);

    std::string complete_ctor_name = get_cpp_special_member_variant_llvm_name(
        ctor_sym, false, CppCtorDtorVariant::Complete);
    std::string ctor_name = get_cpp_special_member_variant_llvm_name(
        ctor_sym, false, variant);
    if (variant == CppCtorDtorVariant::Base &&
        ctor_name != complete_ctor_name &&
        module->getFunction(ctor_name) == nullptr &&
        module->getFunction(complete_ctor_name) != nullptr) {
        ctor_name = complete_ctor_name;
    }
    llvm::FunctionCallee ctor_callee =
        module->getOrInsertFunction(ctor_name, llvm_fn_type);
    llvm::Value* ctor_callee_value = ctor_callee.getCallee();

    std::vector<llvm::Value*> call_args;
    call_args.reserve(ctor_type->parameters.size());
    llvm::Value* this_arg = object_addr;
    if (this_arg->getType() != param_types.front()) {
        this_arg = builder.CreateBitCast(this_arg, param_types.front(), "ctor.this.cast");
    }
    call_args.push_back(this_arg);

    size_t expected_ctor_arg_count = ctor_type->parameters.size() - 1;
    if (ctor_args.size() != expected_ctor_arg_count) {
        error(context + ": constructor argument count mismatch after sema", loc);
        return false;
    }

    for (size_t arg_idx = 0; arg_idx < ctor_args.size(); ++arg_idx) {
        auto* arg_expr = ctor_args[arg_idx].get();
        QualType param_semantic_type = ctor_type->parameters[arg_idx + 1];
        llvm::Value* arg_val = nullptr;
        if (canonical_type_kind(param_semantic_type, ast_ctx.get()) ==
            TypeKind::Reference) {
            Expr* lvalue_base = unwrap_reference_binding_expr(arg_expr);
            arg_val = get_lvalue(lvalue_base).address;
            if (!arg_val) {
                auto ref_type =
                    desugar_type(param_semantic_type, ast_ctx.get())
                        .as_shared<ReferenceType>();
                if (!ref_type || !ref_type->referred_type) {
                    error(context + ": invalid constructor reference parameter", loc);
                    return false;
                }
                llvm::Value* tmp_val = convert_expression(arg_expr);
                if (!tmp_val) {
                    error(context + ": failed to lower constructor argument", loc);
                    return false;
                }
                llvm::Type* referred_llvm_type = convert_type(ref_type->referred_type.get_shared());
                if (!referred_llvm_type) {
                    error(context + ": failed to lower constructor reference target type", loc);
                    return false;
                }
                if (tmp_val->getType() != referred_llvm_type) {
                    bool src_unsigned =
                        arg_expr && arg_expr->get_type() && arg_expr->get_type()->isUnsigned();
                    tmp_val = cast_llvm_type(tmp_val, referred_llvm_type, src_unsigned);
                }
                llvm::Function* function =
                    builder.GetInsertBlock() ? builder.GetInsertBlock()->getParent() : nullptr;
                if (!function) {
                    error(context + ": constructor reference argument outside function", loc);
                    return false;
                }
                llvm::Value* tmp_slot =
                    create_entry_alloca(function, referred_llvm_type, nullptr, "ctor.ref.arg.tmp");
                if (!tmp_slot) {
                    error(context + ": failed to allocate constructor reference temporary", loc);
                    return false;
                }
                builder.CreateStore(tmp_val, tmp_slot);
                arg_val = tmp_slot;
            }
        } else if (pass_aggregate_by_reference(param_semantic_type)) {
            arg_val = materialize_indirect_aggregate_ctor_argument(
                *this, param_semantic_type, arg_expr, loc, context);
            if (!arg_val) {
                return false;
            }
        } else if (has_direct_aggregate_parameter_abi(param_semantic_type)) {
            arg_val = materialize_direct_aggregate_ctor_argument(
                *this, param_semantic_type, arg_expr, loc, context);
            if (!arg_val) {
                return false;
            }
        } else {
            arg_val = convert_expression(arg_expr);
            if (!arg_val) {
                error(context + ": failed to lower constructor argument", loc);
                return false;
            }
        }
        llvm::Type* expected_type = param_types[arg_idx + 1];
        if (arg_val->getType() != expected_type) {
            bool src_unsigned =
                arg_expr && arg_expr->get_type() && arg_expr->get_type()->isUnsigned();
            arg_val = cast_llvm_type(arg_val, expected_type, src_unsigned);
        }
        if (!arg_val) {
            error(context + ": failed to cast constructor argument", loc);
            return false;
        }
        call_args.push_back(arg_val);
    }

    bool ctor_non_throwing =
        ctor_type->exception_spec == FunctionExceptionSpecKind::NonThrowing;
    bool callee_has_nounwind = false;
    llvm::Value* ctor_stripped = ctor_callee_value->stripPointerCasts();
    if (auto* fn = llvm::dyn_cast<llvm::Function>(ctor_stripped)) {
        callee_has_nounwind = fn->hasFnAttribute(llvm::Attribute::NoUnwind);
    }
    bool eh_active =
        !eh_region_stack.empty() && eh_region_stack.back().landing_pad_block != nullptr;
    bool emit_invoke = eh_active && !callee_has_nounwind;
    llvm::CallBase* call_inst = nullptr;
    if (emit_invoke) {
        llvm::Function* function =
            builder.GetInsertBlock() ? builder.GetInsertBlock()->getParent() : nullptr;
        llvm::BasicBlock* unwind_bb =
            eh_region_stack.empty() ? nullptr : eh_region_stack.back().landing_pad_block;
        if (!function || !unwind_bb) {
            error(context + ": constructor invoke lowering missing EH context", loc);
            return false;
        }
        auto* continue_bb = llvm::BasicBlock::Create(*this->context, "invoke.cont", function);
        if (llvm_fn_type->getReturnType()->isVoidTy()) {
            call_inst = builder.CreateInvoke(
                llvm_fn_type, ctor_callee_value, continue_bb, unwind_bb, call_args);
        } else {
            call_inst = builder.CreateInvoke(
                llvm_fn_type, ctor_callee_value, continue_bb, unwind_bb, call_args, "ctor.calltmp");
        }
        builder.SetInsertPoint(continue_bb);
    } else {
        if (llvm_fn_type->getReturnType()->isVoidTy()) {
            call_inst = builder.CreateCall(llvm_fn_type, ctor_callee_value, call_args);
        } else {
            call_inst = builder.CreateCall(llvm_fn_type, ctor_callee_value, call_args, "ctor.calltmp");
        }
    }
    if (!emit_invoke && call_inst) {
        if (ctor_non_throwing || callee_has_nounwind) {
            call_inst->setDoesNotThrow();
        }
    }
    return true;
}

bool ASTToLLVM::emit_cpp_destruct_call(const std::shared_ptr<Symbol>& dtor_sym,
                                       llvm::Value* object_addr,
                                       SrcLoc loc,
                                       const std::string& context,
                                       CppCtorDtorVariant variant) {
    if (!dtor_sym || !object_addr) {
        return false;
    }
    if (dtor_sym->kind != SymbolKind::FUNCTION) {
        error(context + ": selected destructor symbol is invalid", loc);
        return false;
    }

    auto dtor_type = dtor_sym->type.as_shared<FunctionType>();
    if (!dtor_type) {
        error(context + ": selected destructor has non-function type", loc);
        return false;
    }
    if (dtor_type->parameters.empty()) {
        error(context + ": selected destructor is missing implicit object parameter", loc);
        return false;
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

    std::string complete_dtor_name = get_cpp_special_member_variant_llvm_name(
        dtor_sym, true, CppCtorDtorVariant::Complete);
    std::string dtor_name = get_cpp_special_member_variant_llvm_name(
        dtor_sym, true, variant);
    if (variant == CppCtorDtorVariant::Base &&
        dtor_name != complete_dtor_name &&
        module->getFunction(dtor_name) == nullptr &&
        module->getFunction(complete_dtor_name) != nullptr) {
        dtor_name = complete_dtor_name;
    }
    llvm::FunctionCallee dtor_callee =
        module->getOrInsertFunction(dtor_name, llvm_fn_type);
    llvm::Value* dtor_callee_value = dtor_callee.getCallee();

    llvm::Value* this_arg = object_addr;
    if (this_arg->getType() != param_types.front()) {
        this_arg = builder.CreateBitCast(this_arg, param_types.front(), "dtor.this.cast");
    }

    size_t expected_dtor_arg_count = dtor_type->parameters.size() - 1;
    if (expected_dtor_arg_count != 0) {
        error(context + ": destructor argument count mismatch after sema", loc);
        return false;
    }

    bool dtor_non_throwing =
        dtor_type->exception_spec == FunctionExceptionSpecKind::NonThrowing;
    bool callee_has_nounwind = false;
    llvm::Value* dtor_stripped = dtor_callee_value->stripPointerCasts();
    if (auto* fn = llvm::dyn_cast<llvm::Function>(dtor_stripped)) {
        callee_has_nounwind = fn->hasFnAttribute(llvm::Attribute::NoUnwind);
    }
    std::vector<llvm::Value*> dtor_args{this_arg};
    bool eh_active =
        !eh_region_stack.empty() && eh_region_stack.back().landing_pad_block != nullptr;
    bool emit_invoke = eh_active && !callee_has_nounwind;
    llvm::CallBase* call_inst = nullptr;
    if (emit_invoke) {
        llvm::Function* function =
            builder.GetInsertBlock() ? builder.GetInsertBlock()->getParent() : nullptr;
        llvm::BasicBlock* unwind_bb =
            eh_region_stack.empty() ? nullptr : eh_region_stack.back().landing_pad_block;
        if (!function || !unwind_bb) {
            error(context + ": destructor invoke lowering missing EH context", loc);
            return false;
        }
        auto* continue_bb = llvm::BasicBlock::Create(*this->context, "invoke.cont", function);
        if (llvm_fn_type->getReturnType()->isVoidTy()) {
            call_inst = builder.CreateInvoke(
                llvm_fn_type, dtor_callee_value, continue_bb, unwind_bb, dtor_args);
        } else {
            call_inst = builder.CreateInvoke(
                llvm_fn_type, dtor_callee_value, continue_bb, unwind_bb, dtor_args, "dtor.calltmp");
        }
        builder.SetInsertPoint(continue_bb);
    } else {
        if (llvm_fn_type->getReturnType()->isVoidTy()) {
            call_inst = builder.CreateCall(llvm_fn_type, dtor_callee_value, dtor_args);
        } else {
            call_inst = builder.CreateCall(llvm_fn_type, dtor_callee_value, dtor_args, "dtor.calltmp");
        }
    }
    if (!emit_invoke && call_inst) {
        if (dtor_non_throwing || callee_has_nounwind) {
            call_inst->setDoesNotThrow();
        }
    }
    return true;
}

void ASTToLLVM::convert_variable_declaration(VariableDecl *varDecl) {
    if (builder.GetInsertBlock() == nullptr) {
        return; // we already processed this
    }
    auto sym = varDecl->sym;
    if (sym == nullptr) {
        error("convert_variable_declaration(): variable sym missing (internal error)", varDecl->location);
        return;
    }
    std::string mangled = mangleCIdentifier(sym->uid);
    if (named_values.count(mangled) && sym->linkage == VariableLinkage::NONE) {
        // any variable with no variabloe linkage will have a static or extern
        // unless for gloal variables, but we handle those already
        error("convert_variable_declaration(): "
              "already declared this mangled variable: " + mangled, varDecl->location);
        return;
    }
    auto arr_type = varDecl->type.as_shared<ArrayType>();
    bool has_vla = type_contains_vla(varDecl->type.get_shared());
    bool is_vla_array = arr_type && has_vla;
    llvm::Type* varType = nullptr;
    if (!is_vla_array) {
        varType = convert_type(varDecl->type);
    }

    // Determine if this is a local variable (not static/extern, inside a function)
    bool isLocal = varDecl->storage_class != StorageClass::STATIC &&
                   varDecl->storage_class != StorageClass::EXTERN &&
                   builder.GetInsertBlock() != nullptr;
    bool is_block_byref = varDecl->is_block_byref != 0;
    bool has_constructor_call = varDecl->has_cxx_constructor_call();
    bool used_recursive_default_construction = false;
    std::shared_ptr<Symbol> selected_destructor_sym = nullptr;
    if (ast_ctx) {
        if (auto* dtor_sym = ast_ctx->get_cpp_variable_destructor_symbol(varDecl->node_id)) {
            selected_destructor_sym = *dtor_sym;
        }
    }

    if (has_constructor_call && !isLocal) {
        error("convert_variable_declaration(): constructor initialization for non-local storage is not supported",
              varDecl->location);
        return;
    }

    if (isLocal &&
        canonical_type_kind(varDecl->type, ast_ctx.get()) == TypeKind::Reference) {
        auto ref_type =
            desugar_type(varDecl->type, ast_ctx.get()).as_shared<ReferenceType>();
        if (!ref_type || !ref_type->referred_type) {
            error("convert_variable_declaration(): invalid reference type", varDecl->location);
            return;
        }
        if (!varDecl->init) {
            error("convert_variable_declaration(): reference declaration requires initializer",
                  varDecl->location);
            return;
        }

        Expr* binding_expr = unwrap_reference_binding_expr(varDecl->init.get());

        llvm::Value* bound_addr = get_lvalue(binding_expr).address;
        if (!bound_addr) {
            // Temporary materialization for local reference binding.
            llvm::Value* init_val = convert_expression(varDecl->init.get());
            if (!init_val) {
                error("convert_variable_declaration(): invalid reference initializer",
                      varDecl->location);
                return;
            }

            if (init_val->getType()->isPointerTy()) {
                bound_addr = init_val;
            } else {
                llvm::Type* referred_llvm_type = convert_type(ref_type->referred_type.get_shared());
                if (!referred_llvm_type) {
                    error("convert_variable_declaration(): failed to lower reference target type",
                          varDecl->location);
                    return;
                }
                if (init_val->getType() != referred_llvm_type) {
                    bool src_unsigned =
                        varDecl->init->get_type() && varDecl->init->get_type()->isUnsigned();
                    init_val = cast_llvm_type(init_val, referred_llvm_type, src_unsigned);
                }

                llvm::Function* function = builder.GetInsertBlock()->getParent();
                llvm::Value* tmp =
                    create_entry_alloca(function, referred_llvm_type, nullptr, mangled + ".ref.tmp");
                if (!tmp) {
                    error("convert_variable_declaration(): failed to allocate reference temporary",
                          varDecl->location);
                    return;
                }
                builder.CreateStore(init_val, tmp);
                bound_addr = tmp;
            }
        }

        if (!bound_addr || !bound_addr->getType()->isPointerTy()) {
            error("convert_variable_declaration(): reference initializer did not produce address",
                  varDecl->location);
            return;
        }
        named_values[mangled] = bound_addr;
        return;
    }

    if (has_vla && !isLocal) {
        error("convert_variable_declaration(): VLA with non-local storage is not supported", varDecl->location);
        return;
    }
    if (has_vla) {
        cache_vla_sizes_for_type(varDecl->type.get_shared());
    }

    auto coerce_global_initializer_constant =
        [&](llvm::Constant* constant) -> llvm::Constant* {
            if (!constant || !varType || constant->getType() == varType) {
                return constant;
            }
            bool src_unsigned =
                varDecl->init && varDecl->init->get_type() &&
                varDecl->init->get_type()->isUnsigned();
            bool dst_unsigned = varDecl->type && varDecl->type->isUnsigned();
            return fold_constant_cast(
                constant,
                varType,
                src_unsigned,
                dst_unsigned,
                module->getDataLayout());
        };
    if (llvm::GlobalValue* weak_alias =
            get_or_create_variable_weakref_alias(*this, varDecl, varType)) {
        named_values[mangled] = weak_alias;
        return;
    }

    std::string linkage_identity = get_variable_linkage_identity(*varDecl);
    auto get_global_var_name = [&]() -> std::string {
        return get_variable_llvm_name(*varDecl);
    };

    // Local static initializers can reference the variable itself (e.g. &x).
    // Materialize and register the backing global before folding the initializer.
    if (varDecl->storage_class == StorageClass::STATIC &&
        builder.GetInsertBlock() != nullptr &&
        !is_vla_array) {
        std::string var_name_get = get_global_var_name();
        llvm::GlobalVariable* gVar = module->getGlobalVariable(var_name_get, true);
        if (!gVar) {
            llvm::Constant* zero_init = nullptr;
            if (varType->isArrayTy()) {
                zero_init = llvm::ConstantAggregateZero::get(varType);
            } else {
                zero_init = llvm::Constant::getNullValue(varType);
            }
            gVar = new llvm::GlobalVariable(
                *module,
                varType,
                varDecl->type.is_const(),
                variable_global_linkage(*this, varDecl),
                zero_init,
                var_name_get
            );
        }
        configure_variable_global_linkage(*this, varDecl, gVar);
        if (varDecl->is_thread_local) {
            gVar->setThreadLocalMode(llvm::GlobalVariable::GeneralDynamicTLSModel);
        }
        named_values[mangled] = gVar;
    }

    // For local variables, allocate BEFORE evaluating the initializer so the variable
    // is in scope during its own initializer (C allows `int a = a = 5;`)
    llvm::AllocaInst* localAlloca = nullptr;
    llvm::StructType* block_byref_cell_type = nullptr;
    bool block_byref_has_helpers = false;
    if (isLocal) {
        if (is_vla_array) {
            if (!cleanup_stack.empty()) {
                llvm::Type* ptr_ty = llvm::PointerType::get(*context, 0);
                llvm::Function* stacksave_fn = llvm::Intrinsic::getDeclaration(
                    module.get(), llvm::Intrinsic::stacksave, {ptr_ty});
                llvm::Value* saved_sp = builder.CreateCall(stacksave_fn, {}, "vla.stacksave");
                CleanupEntry cleanup_entry{};
                cleanup_entry.var_addr = saved_sp;
                cleanup_entry.kind = CleanupEntry::Kind::StackRestore;
                cleanup_entry.location = varDecl->location;
                cleanup_stack.back().push_back(cleanup_entry);
            }
            auto [flat_elem_type, total_count] = get_vla_flat_element_and_count(arr_type);
            if (!flat_elem_type || !total_count) {
                error("convert_variable_declaration(): Failed to compute VLA flat allocation", varDecl->location);
                return;
            }
            localAlloca = builder.CreateAlloca(flat_elem_type, total_count, mangled);
        } else {
            llvm::Function* function = builder.GetInsertBlock()->getParent();
            llvm::Type* storage_type = varType;
            if (is_block_byref) {
                block_byref_has_helpers =
                    block_byref_requires_copy_dispose_helpers(varDecl->type);
                block_byref_cell_type = build_block_byref_cell_type(
                    *this,
                    varDecl->type,
                    block_byref_has_helpers);
                if (!block_byref_cell_type) {
                    error("convert_variable_declaration(): failed to lower __block cell type",
                          varDecl->location);
                    return;
                }
                storage_type = block_byref_cell_type;
            }
            // Preserve source declaration order for entry allocas by appending
            // after any existing static allocas in the entry block.
            localAlloca = create_entry_alloca(function, storage_type, nullptr, mangled);
            if (!localAlloca) {
                error("convert_variable_declaration(): failed to allocate local variable",
                      varDecl->location);
                return;
            }
        }
        // Apply aligned attribute to local alloca
        for (const auto& attr : ast_ctx->get_attrs(varDecl->node_id).attrs) {
            if (attr.resolved_kind == AttributeKind::ALIGNED &&
                !attr.args.empty() && attr.args[0].kind == AttributeArg::Kind::INTEGER) {
                int64_t raw_align = attr.args[0].int_value;
                if (raw_align > 0) {
                    uint64_t align = static_cast<uint64_t>(raw_align);
                    if ((align & (align - 1)) == 0) {
                        localAlloca->setAlignment(llvm::Align(align));
                    }
                }
            }
        }
        if (is_block_byref && block_byref_cell_type) {
            auto store_cell_field =
                [&](unsigned field_index, llvm::Value* value, const char* name) {
                    llvm::Value* slot = builder.CreateStructGEP(
                        block_byref_cell_type,
                        localAlloca,
                        field_index,
                        name);
                    llvm::Type* slot_type = block_byref_cell_type->getElementType(field_index);
                    if (value->getType() != slot_type) {
                        if (value->getType()->isPointerTy() && slot_type->isPointerTy()) {
                            value = builder.CreatePointerCast(value, slot_type);
                        } else {
                            value = cast_llvm_type(value, slot_type, false);
                        }
                    }
                    builder.CreateStore(value, slot);
                };

            llvm::Type* ptr_ty = llvm::PointerType::get(*context, 0);
            auto* i32_ty = llvm::Type::getInt32Ty(*context);
            llvm::Value* cell_ptr =
                builder.CreatePointerCast(localAlloca, ptr_ty, "block.byref.cell.addr");
            store_cell_field(
                0,
                llvm::ConstantPointerNull::get(llvm::cast<llvm::PointerType>(ptr_ty)),
                "block.byref.isa");
            store_cell_field(1, cell_ptr, "block.byref.forwarding");
            store_cell_field(
                2,
                llvm::ConstantInt::get(
                    i32_ty,
                    block_byref_has_helpers
                        ? darwin_blocks::BLOCK_HAS_COPY_DISPOSE
                        : 0),
                "block.byref.flags");
            store_cell_field(
                3,
                llvm::ConstantInt::get(
                    i32_ty,
                    module->getDataLayout().getTypeAllocSize(block_byref_cell_type)),
                "block.byref.size");
            if (block_byref_has_helpers) {
                store_cell_field(
                    4,
                    get_or_create_block_byref_keep_helper(*this, varDecl),
                    "block.byref.keep");
                store_cell_field(
                    5,
                    get_or_create_block_byref_destroy_helper(*this, varDecl),
                    "block.byref.destroy");
            }
        }
        named_values[mangled] = localAlloca;
    }

    llvm::Value* localStorageAddr = localAlloca;
    if (isLocal && is_block_byref && localAlloca) {
        localStorageAddr = get_block_byref_payload_address(
            localAlloca,
            varDecl->type,
            varDecl->location,
            "convert_variable_declaration()");
        if (!localStorageAddr) {
            return;
        }
    }

    const auto* ctor_init = has_constructor_call ? varDecl->get_cpp_construct_init() : nullptr;

    llvm::Value* initVal = nullptr;
    InitListExpr* initListExpr = nullptr;
    if (varDecl->init && !has_constructor_call) {
        if (is_vla_array) {
            error("convert_variable_declaration(): Initializers for VLAs are not supported", varDecl->location);
            return;
        }
        if (canonical_type_kind(varDecl->type, ast_ctx.get()) ==
            TypeKind::Reference) {
            auto ref_type =
                desugar_type(varDecl->type, ast_ctx.get())
                    .as_shared<ReferenceType>();
            if (!ref_type || !ref_type->referred_type) {
                error("convert_variable_declaration(): invalid reference type", varDecl->location);
                return;
            }

            Expr* binding_expr = unwrap_reference_binding_expr(varDecl->init.get());

            llvm::Value* bound_addr = get_lvalue(binding_expr).address;
            bool is_global_storage = varDecl->storage_class == StorageClass::STATIC ||
                                     varDecl->storage_class == StorageClass::EXTERN ||
                                     builder.GetInsertBlock() == nullptr;
            if (!bound_addr) {
                if (!is_global_storage) {
                    error("convert_variable_declaration(): local reference initializer did not produce address",
                          varDecl->location);
                    return;
                }

                llvm::Type* referred_llvm_type = convert_type(ref_type->referred_type.get_shared());
                if (!referred_llvm_type) {
                    error("convert_variable_declaration(): failed to lower reference target type",
                          varDecl->location);
                    return;
                }
                auto* referred_init = emit_constant_initializer(varDecl->init.get());
                if (!referred_init) {
                    error("convert_variable_declaration(): static/global reference initializer must bind to a global lvalue or constant temporary",
                          varDecl->location);
                    return;
                }
                if (referred_init->getType() != referred_llvm_type) {
                    bool src_uns = varDecl->init->get_type() && varDecl->init->get_type()->isUnsigned();
                    bool dst_uns = ref_type->referred_type && ref_type->referred_type->isUnsigned();
                    referred_init = fold_constant_cast(
                        referred_init,
                        referred_llvm_type,
                        src_uns,
                        dst_uns,
                        module->getDataLayout());
                    if (!referred_init || referred_init->getType() != referred_llvm_type) {
                        error("convert_variable_declaration(): failed to fold static/global reference temporary initializer",
                              varDecl->location);
                        return;
                    }
                }
                static uint64_t static_ref_temp_counter = 0;
                std::string temp_name =
                    mangled + ".ref.tmp." + std::to_string(static_ref_temp_counter++);
                auto* temp_global = new llvm::GlobalVariable(
                    *module,
                    referred_llvm_type,
                    ref_type->referred_type.is_const(),
                    llvm::GlobalValue::InternalLinkage,
                    referred_init,
                    temp_name);
                bound_addr = temp_global;
            }

            auto* bound_const = llvm::dyn_cast<llvm::Constant>(bound_addr);
            if (!bound_const) {
                error("convert_variable_declaration(): static/global reference initializer must be constant address",
                      varDecl->location);
                return;
            }
            initVal = bound_const;
        } else if (auto* initList = dyn_cast<InitListExpr>(varDecl->init.get())) {
            initListExpr = initList;
            if (!isLocal) {
                initVal = convert_init_list(initList, varType);
            }
        } else if (auto *strLit = dyn_cast<StringLiteral>(varDecl->init.get())) {
            auto arr_type_s = strLit->ctype.as_shared<ArrayType>();
            if (arr_type_s && arr_type_s->size_kind == ArraySizeKind::Constant && arr_type_s->size.has_value()) {
                // For char arr[] = "string", create a ConstantDataArray.
                // Local arrays: stored into the stack alloca below.
                // Static/global arrays: used as the initializer by the global-variable path.
                size_t len = arr_type_s->size.value();
                initVal = build_string_literal_array_constant(strLit, len);
                if (!initVal) {
                    error("convert_variable_declaration(): unsupported string literal initializer type",
                          varDecl->location);
                }
            } else {
                // String literal used as pointer (e.g. char *p = "str")
                initVal = convert_string_literal(strLit);
                if (!isLocal) {
                    named_values[mangled] = initVal;
                    return;
                }
            }
        }
        else {
            // For static/global variables, prefer constant lowering first.
            bool is_global = varDecl->storage_class == StorageClass::STATIC ||
                             varDecl->storage_class == StorageClass::EXTERN ||
                             builder.GetInsertBlock() == nullptr;
            if (is_global) {
                auto* cst = emit_constant_initializer(varDecl->init.get());
                if (cst) {
                    initVal = cst;
                } else {
                    initVal = convert_expression(varDecl->init.get());
                }
            } else {
                initVal = convert_expression(varDecl->init.get());
            }
        }
    }

    // Global variable
    // a varaible with no linkage can still be global
    if (varDecl->storage_class == StorageClass::STATIC ||varDecl->storage_class == StorageClass::EXTERN ||
        builder.GetInsertBlock() == nullptr) {
        if (has_vla) {
            error("convert_variable_declaration(): VLA with non-local storage is not supported", varDecl->location);
            return;
        }
        // Global variable
        // Check if it already exists (e.g. extern declaration)
        // todo: we can have nested static's, call mangled on vardecl->name when child is tatic
        std::string var_name_get = get_global_var_name();
        llvm::GlobalVariable* gVar = module->getGlobalVariable(var_name_get, true);

        if (!gVar) {
            // For all global (top level defined) variables,
            // we should never reach here as we delt with this in deal_global
            // This means that if we are here the variable has linkage but limited "scope"

            llvm::Constant* initConst = nullptr;
            if (initVal) {
                if (auto* constant = llvm::dyn_cast<llvm::Constant>(initVal)) {
                    constant = coerce_global_initializer_constant(constant);
                    if (!constant) {
                        error("convert_variable_declaration(): failed to coerce global initializer to variable type",
                              varDecl->location);
                        return;
                    }
                    initConst = constant;
                } else {
                    error("convert_variable_declaration(): initializer must be constant", varDecl->location);
                    return;
                }
            } else if (variable_decl_is_definition_bearing(*this, varDecl)) {
                // Tentative definition or definition without initializer: initialize to zero
                if (varType->isArrayTy()) {
                    initConst = llvm::ConstantAggregateZero::get(varType);
                } else {
                    initConst = llvm::Constant::getNullValue(varType);
                }
            }

            gVar = new llvm::GlobalVariable(
                *module,
                varType,
                varDecl->type.is_const(), // isConstant
                variable_global_linkage(*this, varDecl),
                initConst,
                var_name_get
            );
        } else {
            if (initVal) {
                if (auto* constant = llvm::dyn_cast<llvm::Constant>(initVal)) {
                    constant = coerce_global_initializer_constant(constant);
                    if (!constant) {
                        error("convert_variable_declaration(): failed to coerce global initializer to variable type",
                              varDecl->location);
                        return;
                    }
                    gVar->setInitializer(constant);
                } else {
                    error("convert_variable_declaration(): initializer must be constant", varDecl->location);
                    return;
                }
            } else if (!gVar->hasInitializer() &&
                       variable_decl_is_definition_bearing(*this, varDecl)) {
                llvm::Constant* zero_init = varType->isArrayTy()
                    ? static_cast<llvm::Constant*>(llvm::ConstantAggregateZero::get(varType))
                    : static_cast<llvm::Constant*>(llvm::Constant::getNullValue(varType));
                gVar->setInitializer(zero_init);
            }
        }
        configure_variable_global_linkage(*this, varDecl, gVar);
        if (varDecl->is_thread_local) {
            gVar->setThreadLocalMode(llvm::GlobalVariable::GeneralDynamicTLSModel);
        }

        // Apply variable attributes to static/extern globals
        for (const auto& attr : ast_ctx->get_attrs(varDecl->node_id).attrs) {
            switch (attr.resolved_kind) {
                case AttributeKind::ALIGNED:
                    if (!attr.args.empty() && attr.args[0].kind == AttributeArg::Kind::INTEGER) {
                        int64_t raw_align = attr.args[0].int_value;
                        if (raw_align > 0) {
                            uint64_t align = static_cast<uint64_t>(raw_align);
                            if ((align & (align - 1)) == 0) {
                                gVar->setAlignment(llvm::Align(align));
                            }
                        }
                    }
                    break;
                case AttributeKind::SECTION:
                    if (!attr.args.empty() && attr.args[0].kind == AttributeArg::Kind::STRING) {
                        gVar->setSection(attr.args[0].str_value);
                    }
                    break;
                case AttributeKind::WEAK:
                    gVar->setLinkage(llvm::GlobalValue::WeakAnyLinkage);
                    break;
                case AttributeKind::COMMON_ATTR:
                    gVar->setLinkage(llvm::GlobalValue::CommonLinkage);
                    if (!gVar->hasInitializer()) {
                        gVar->setInitializer(llvm::Constant::getNullValue(varType));
                    }
                    gVar->setConstant(false);
                    break;
                case AttributeKind::VISIBILITY: {
                    if (!attr.args.empty() && attr.args[0].kind == AttributeArg::Kind::STRING) {
                        const auto& vis = attr.args[0].str_value;
                        if (vis == "default") gVar->setVisibility(llvm::GlobalValue::DefaultVisibility);
                        else if (vis == "hidden") gVar->setVisibility(llvm::GlobalValue::HiddenVisibility);
                        else if (vis == "protected") gVar->setVisibility(llvm::GlobalValue::ProtectedVisibility);
                    }
                    break;
                }
                case AttributeKind::USED:
                    llvm::appendToCompilerUsed(*module, {gVar});
                    break;
                default:
                    break;
            }
        }
        // We map the UID to the global variable
        named_values[mangled] = gVar;

        if (!varDecl->is_thread_local &&
            canonical_type_kind(varDecl->type, ast_ctx.get()) == TypeKind::Object &&
            variable_decl_is_definition_bearing(*this, varDecl) &&
            ast_ctx) {
            bool mergeable_dtor_thunk =
                variable_decl_is_inline_equivalent_external_definition(*this, varDecl);
            std::string dtor_thunk_name = linkage_identity + ".cxx.global.dtor";
            emit_cpp_global_object_dtor_thunk(
                dtor_thunk_name,
                varDecl->type,
                gVar,
                selected_destructor_sym,
                varDecl->location,
                "convert_variable_declaration() global dtor thunk",
                mergeable_dtor_thunk
                    ? llvm::GlobalValue::LinkOnceODRLinkage
                    : llvm::GlobalValue::InternalLinkage,
                mergeable_dtor_thunk
                    ? static_cast<llvm::Constant*>(gVar)
                    : nullptr);
        }

    } else {
        // Local variable - already allocated above
        if (is_block_byref && !cleanup_stack.empty()) {
            CleanupEntry cleanup_entry{};
            cleanup_entry.var_addr = localAlloca;
            cleanup_entry.location = varDecl->location;
            cleanup_entry.kind = CleanupEntry::Kind::BlockByrefDispose;
            cleanup_stack.back().push_back(std::move(cleanup_entry));
        }
        if (has_constructor_call) {
            if (!emit_cpp_construct_call(ctor_init,
                                         localStorageAddr,
                                         varDecl->location,
                                         "convert_variable_declaration()")) {
                return;
            }
        } else if (initListExpr) {
            emit_init_list_store(initListExpr, localStorageAddr, varDecl->type.get_shared(),
                                 varDecl->type.is_volatile(), varDecl->type.is_atomic());
        } else if (initVal) {
            // If initVal is a pointer (e.g. from compound literal) but we need the value, load it
            if (initVal->getType()->isPointerTy() && !varType->isPointerTy()) {
                initVal = builder.CreateLoad(varType, initVal, "compoundlit.load");
            }
            if (initVal && initVal->getType() != varType) {
                bool src_unsigned =
                    varDecl->init && varDecl->init->get_type() &&
                    varDecl->init->get_type()->isUnsigned();
                initVal = cast_llvm_type(initVal, varType, src_unsigned);
            }
            if (!initVal) {
                error("convert_variable_declaration(): failed to convert initializer to declared type",
                      varDecl->location);
                return;
            }
            auto *store = builder.CreateStore(initVal, localStorageAddr);
            apply_store_qualifiers(store, varDecl->type, module->getDataLayout());
        } else if (canonical_type_kind(varDecl->type, ast_ctx.get()) ==
                       TypeKind::Object &&
                   localStorageAddr &&
                   !varDecl->init) {
            if (!emit_cpp_object_default_construction_recursive(
                    varDecl->type,
                    localStorageAddr,
                    varDecl->location,
                    "convert_variable_declaration() implicit default construction")) {
                return;
            }
            used_recursive_default_construction = true;
        }
        if (!has_constructor_call &&
            !used_recursive_default_construction &&
            canonical_type_kind(varDecl->type, ast_ctx.get()) == TypeKind::Object &&
            localStorageAddr) {
            emit_cpp_vptr_store(
                varDecl->type,
                localStorageAddr,
                varDecl->location,
                "convert_variable_declaration()");
        }
        // Register cleanup attribute if present
        if (!cleanup_stack.empty()) {
            auto* cleanup_attr = ast_ctx->get_attrs(varDecl->node_id).find(AttributeKind::CLEANUP);
            if (cleanup_attr && !cleanup_attr->args.empty() &&
                cleanup_attr->args[0].kind == AttributeArg::Kind::IDENTIFIER) {
                CleanupEntry cleanup_entry{};
                cleanup_entry.var_addr = localStorageAddr;
                cleanup_entry.cleanup_func = cleanup_attr->args[0].str_value;
                cleanup_entry.location = varDecl->location;
                cleanup_entry.kind = CleanupEntry::Kind::Call;
                cleanup_stack.back().push_back(std::move(cleanup_entry));
            }
        }
        if (canonical_type_kind(varDecl->type, ast_ctx.get()) == TypeKind::Object &&
            !cleanup_stack.empty()) {
            auto select_record_destructor_symbol =
                [&](const RecordSemanticState* state,
                    bool require_public_access) -> std::shared_ptr<Symbol> {
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
            };

            auto append_object_cleanup =
                [&](const QualType& object_type,
                    llvm::Value* object_addr,
                    std::shared_ptr<Symbol> object_dtor_sym) {
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
                    object_decl ? record_semantics_cache_lookup(object_decl) : nullptr;

                if (!object_dtor_sym) {
                    object_dtor_sym = select_record_destructor_symbol(
                        object_state, false);
                }
                if (object_dtor_sym &&
                    object_dtor_sym->kind != SymbolKind::FUNCTION) {
                    return;
                }

                bool has_recursive_teardown_work =
                    object_state &&
                    (!object_state->fields.empty() ||
                     !object_state->bases.empty() ||
                     !object_state->virtual_bases.empty());
                if (!object_dtor_sym && !has_recursive_teardown_work) {
                    return;
                }

                CleanupEntry cleanup_entry{};
                cleanup_entry.var_addr = object_addr;
                cleanup_entry.cxx_destructor_sym = object_dtor_sym;
                cleanup_entry.cxx_destructor_object_type = object_type;
                cleanup_entry.location = varDecl->location;
                cleanup_entry.kind = CleanupEntry::Kind::CppDestructor;
                cleanup_stack.back().push_back(std::move(cleanup_entry));
            };

            append_object_cleanup(
                varDecl->type,
                localStorageAddr,
                selected_destructor_sym);
        }
    }
}
