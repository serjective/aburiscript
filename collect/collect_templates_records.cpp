#include "collect_templates_internal.h"
#include "../ast/ast_clone.h"

namespace template_sema_internal {

QualType replace_record_decl_in_type(QualType type,
                                     const ObjectDecl* pattern_decl,
                                     QualType replacement_type,
                                     const ASTContext* ast_ctx) {
    if (!type || !pattern_decl || !replacement_type) {
        return type;
    }

    auto raw = type.get_shared();
    uint8_t quals = type.get_qualifiers();
    if (!raw) {
        return type;
    }

    if (auto object = dyn_cast_shared<ObjectType>(raw)) {
        if (object->get_decl() == pattern_decl) {
            return QualType(
                replacement_type.get_shared(),
                static_cast<uint8_t>(replacement_type.get_qualifiers() | quals));
        }
        return type;
    }
    if (auto typedef_type = dyn_cast_shared<TypedefType>(raw)) {
        auto rewritten_underlying = replace_record_decl_in_type(
            typedef_type->underlying_type,
            pattern_decl,
            replacement_type,
            ast_ctx);
        if (rewritten_underlying.equals_qualified(typedef_type->underlying_type)) {
            return type;
        }
        return QualType(
            std::make_shared<TypedefType>(
                typedef_type->name,
                rewritten_underlying,
                typedef_type->typedef_decl),
            quals);
    }
    if (auto dependent_name = dyn_cast_shared<DependentNameType>(raw)) {
        auto rewritten_qualifier = replace_record_decl_in_type(
            dependent_name->qualifier_type,
            pattern_decl,
            replacement_type,
            ast_ctx);
        bool changed =
            !rewritten_qualifier.equals_qualified(dependent_name->qualifier_type);
        std::vector<TemplateArgument> rewritten_arguments;
        rewritten_arguments.reserve(dependent_name->template_arguments.size());
        for (const auto& argument : dependent_name->template_arguments) {
            TemplateArgument rewritten_argument = argument;
            if (argument.kind == TemplateArgumentKind::Type) {
                rewritten_argument.type = replace_record_decl_in_type(
                    argument.type,
                    pattern_decl,
                    replacement_type,
                    ast_ctx);
                changed = changed ||
                    !rewritten_argument.type.equals_qualified(argument.type);
            } else {
                rewritten_argument.value_type = replace_record_decl_in_type(
                    argument.value_type,
                    pattern_decl,
                    replacement_type,
                    ast_ctx);
                changed = changed ||
                    !rewritten_argument.value_type.equals_qualified(
                        argument.value_type);
            }
            rewritten_arguments.push_back(std::move(rewritten_argument));
        }
        if (!changed) {
            return type;
        }
        auto rewritten = std::make_shared<DependentNameType>(
            rewritten_qualifier,
            dependent_name->member_name,
            std::move(rewritten_arguments),
            dependent_name->is_current_instantiation,
            dependent_name->requires_typename_keyword,
            dependent_name->requires_template_keyword);
        return QualType(rewritten, quals);
    }
    if (auto ptr = dyn_cast_shared<PointerType>(raw)) {
        auto rewritten = replace_record_decl_in_type(
            ptr->pointed_type,
            pattern_decl,
            replacement_type,
            ast_ctx);
        if (rewritten.equals_qualified(ptr->pointed_type)) {
            return type;
        }
        return QualType(std::make_shared<PointerType>(rewritten), quals);
    }
    if (auto ref = dyn_cast_shared<ReferenceType>(raw)) {
        auto rewritten = replace_record_decl_in_type(
            ref->referred_type,
            pattern_decl,
            replacement_type,
            ast_ctx);
        if (rewritten.equals_qualified(ref->referred_type)) {
            return type;
        }
        return QualType(
            std::make_shared<ReferenceType>(rewritten, ref->reference_kind),
            quals);
    }
    if (auto transform = dyn_cast_shared<BuiltinTypeTransformType>(raw)) {
        auto rewritten = replace_record_decl_in_type(
            transform->operand_type,
            pattern_decl,
            replacement_type,
            ast_ctx);
        if (rewritten.equals_qualified(transform->operand_type)) {
            return type;
        }
        return QualType(
            std::make_shared<BuiltinTypeTransformType>(
                transform->transform_kind,
                rewritten),
            quals);
    }
    if (auto mem_ptr = dyn_cast_shared<MemberPointerType>(raw)) {
        auto rewritten_class = replace_record_decl_in_type(
            mem_ptr->class_type,
            pattern_decl,
            replacement_type,
            ast_ctx);
        auto rewritten_member = replace_record_decl_in_type(
            mem_ptr->member_type,
            pattern_decl,
            replacement_type,
            ast_ctx);
        if (rewritten_class.equals_qualified(mem_ptr->class_type) &&
            rewritten_member.equals_qualified(mem_ptr->member_type)) {
            return type;
        }
        return QualType(
            std::make_shared<MemberPointerType>(
                rewritten_class,
                rewritten_member),
            quals);
    }
    if (auto blk = dyn_cast_shared<BlockPointerType>(raw)) {
        auto rewritten = replace_record_decl_in_type(
            blk->pointed_type,
            pattern_decl,
            replacement_type,
            ast_ctx);
        if (rewritten.equals_qualified(blk->pointed_type)) {
            return type;
        }
        return QualType(std::make_shared<BlockPointerType>(rewritten), quals);
    }
    if (auto arr = dyn_cast_shared<ArrayType>(raw)) {
        auto rewritten = replace_record_decl_in_type(
            arr->element_type,
            pattern_decl,
            replacement_type,
            ast_ctx);
        if (rewritten.equals_qualified(arr->element_type)) {
            return type;
        }
        if (arr->size.has_value()) {
            return QualType(
                std::make_shared<ArrayType>(rewritten, arr->size),
                quals);
        }
        auto rebuilt = std::make_shared<ArrayType>(rewritten, arr->size_expr);
        rebuilt->size_kind = arr->size_kind;
        rebuilt->size = arr->size;
        return QualType(rebuilt, quals);
    }
    if (auto func = dyn_cast_shared<FunctionType>(raw)) {
        auto rewritten_ret = replace_record_decl_in_type(
            func->ret_type,
            pattern_decl,
            replacement_type,
            ast_ctx);
        bool changed = !rewritten_ret.equals_qualified(func->ret_type);
        auto rebuilt = std::make_shared<FunctionType>(*func);
        rebuilt->ret_type = rewritten_ret;
        for (size_t index = 0; index < rebuilt->parameters.size(); ++index) {
            auto rewritten_param = replace_record_decl_in_type(
                rebuilt->parameters[index],
                pattern_decl,
                replacement_type,
                ast_ctx);
            changed = changed ||
                !rewritten_param.equals_qualified(rebuilt->parameters[index]);
            rebuilt->parameters[index] = rewritten_param;
        }
        if (!changed) {
            return type;
        }
        return QualType(rebuilt, quals);
    }
    if (auto vec = dyn_cast_shared<VectorType>(raw)) {
        auto rewritten = replace_record_decl_in_type(
            vec->element_type,
            pattern_decl,
            replacement_type,
            ast_ctx);
        if (rewritten.equals_qualified(vec->element_type)) {
            return type;
        }
        return QualType(
            std::make_shared<VectorType>(rewritten, vec->total_bytes),
            quals);
    }

    return type;
}

const ObjectDecl* canonical_record_decl(const ObjectDecl* decl) {
    if (!decl) {
        return nullptr;
    }
    if (auto record_type = decl->get_record_type()) {
        if (auto* canonical = dyn_cast<ObjectDecl>(record_type->get_decl())) {
            return canonical;
        }
    }
    return decl;
}

std::shared_ptr<Symbol> clone_symbol_shallow_for_specialization(
    const std::shared_ptr<Symbol>& sym,
    QualType cloned_type) {
    if (!sym) {
        return nullptr;
    }
    auto cloned = std::make_shared<Symbol>(
        sym->name,
        sym->kind,
        std::move(cloned_type),
        sym->storage_class,
        sym->linkage,
        sym->is_inline != 0);
    cloned->is_defined = sym->is_defined;
    cloned->is_constexpr = sym->is_constexpr;
    cloned->had_non_inline_declaration = sym->had_non_inline_declaration;
    cloned->is_block_byref = sym->is_block_byref;
    cloned->is_deprecated = sym->is_deprecated;
    cloned->deprecated_message = sym->deprecated_message;
    cloned->sym_attrs = sym->sym_attrs;
    cloned->enum_val = sym->enum_val;
    cloned->asm_label = sym->asm_label;
    cloned->set_language_linkage(sym->get_language_linkage());
    return cloned;
}

void rebind_specialized_function_owner(FuncDecl* decl,
                                       QualType specialized_owner_type,
                                       const ASTContext* ast_ctx) {
    if (!decl || !specialized_owner_type || !ast_ctx) {
        return;
    }

    QualType current_owner_type = get_func_decl_owner_record_type(decl);
    if (!current_owner_type) {
        set_func_decl_owner_record_type(decl, specialized_owner_type);
        return;
    }

    auto current_owner_object =
        desugar_type(current_owner_type, ast_ctx).as_shared<ObjectType>();
    auto specialized_owner_object =
        desugar_type(specialized_owner_type, ast_ctx).as_shared<ObjectType>();
    const auto* current_owner_decl = current_owner_object
        ? dyn_cast<ObjectDecl>(current_owner_object->get_decl())
        : nullptr;
    const auto* specialized_owner_decl = specialized_owner_object
        ? dyn_cast<ObjectDecl>(specialized_owner_object->get_decl())
        : nullptr;

    if (!current_owner_decl || !specialized_owner_decl ||
        current_owner_decl == specialized_owner_decl) {
        set_func_decl_owner_record_type(decl, specialized_owner_type);
        return;
    }

    auto rewritten_function_type = replace_record_decl_in_type(
        QualType(decl->type),
        current_owner_decl,
        specialized_owner_type,
        ast_ctx);
    auto canonical_function_type = desugar_type(rewritten_function_type, ast_ctx);
    if (canonical_function_type) {
        decl->type = canonical_function_type.get_shared();
    }

    for (auto& parameter_decl : decl->parameters) {
        auto* param = dyn_cast<ParamDecl>(parameter_decl.get());
        if (!param) {
            continue;
        }
        param->type = replace_record_decl_in_type(
            param->type,
            current_owner_decl,
            specialized_owner_type,
            ast_ctx);
        if (param->original_type) {
            param->original_type =
                replace_record_decl_in_type(
                    QualType(param->original_type),
                    current_owner_decl,
                    specialized_owner_type,
                    ast_ctx)
                    .get_shared();
        }
        if (param->sym) {
            param->sym->type = param->type;
        }
    }

    set_func_decl_owner_record_type(decl, specialized_owner_type);
}

void copy_cpp_member_decl_info(ASTContext* ast_ctx,
                               uint32_t from_node_id,
                               uint32_t to_node_id) {
    if (!ast_ctx) {
        return;
    }
    if (const auto* info = ast_ctx->get_cpp_member_decl_info(from_node_id)) {
        ast_ctx->set_cpp_member_decl_info(to_node_id, *info);
    }
}

std::shared_ptr<Symbol> lookup_symbol_remap_in_clone_context(
    const std::shared_ptr<Symbol>& sym,
    ASTCloneContext& clone_ctx) {
    if (!sym) {
        return nullptr;
    }
    auto remapped = clone_ctx.symbol_remap.find(sym.get());
    if (remapped == clone_ctx.symbol_remap.end()) {
        return nullptr;
    }
    return remapped->second;
}

} // namespace template_sema_internal
