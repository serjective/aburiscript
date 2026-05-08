#include "expr_clone.h"

#include "ast_clone.h"
#include "ast_context.h"

#include <cassert>
#include <limits>

namespace {
template <typename NodeType>
void assign_node_id(NodeType* node, ASTContext* ast_ctx) {
    if (node && ast_ctx) {
        node->node_id = ast_ctx->next_node_id();
    }
}

std::unique_ptr<Expr> fail_clone(std::string* error_out,
                                 const std::string& message) {
    if (error_out && error_out->empty()) {
        *error_out = message;
    }
    return nullptr;
}

std::unique_ptr<Expr> clone_expr_impl(const Expr* expr,
                                      ASTContext* ast_ctx,
                                      std::string* error_out);

std::shared_ptr<Expr> clone_shared_expr_impl(const std::shared_ptr<Expr>& expr,
                                             ASTContext* ast_ctx,
                                             std::string* error_out) {
    if (!expr) {
        return nullptr;
    }
    auto cloned = clone_expr_impl(expr.get(), ast_ctx, error_out);
    if (!cloned) {
        return nullptr;
    }
    return std::shared_ptr<Expr>(cloned.release());
}

std::vector<std::unique_ptr<Expr>> clone_expr_vector_impl(
    const std::vector<std::unique_ptr<Expr>>& input,
    ASTContext* ast_ctx,
    std::string* error_out) {
    std::vector<std::unique_ptr<Expr>> result;
    result.reserve(input.size());
    for (const auto& expr : input) {
        if (!expr) {
            result.push_back(nullptr);
            continue;
        }
        auto cloned = clone_expr_impl(expr.get(), ast_ctx, error_out);
        if (!cloned) {
            return {};
        }
        result.push_back(std::move(cloned));
    }
    return result;
}

std::vector<std::unique_ptr<ParamDecl>> clone_requires_param_list(
    const std::vector<std::unique_ptr<ParamDecl>>& input,
    ASTContext* ast_ctx,
    std::string* error_out) {
    ASTCloneContext clone_ctx;
    clone_ctx.ast_ctx = ast_ctx;
    std::vector<std::unique_ptr<ParamDecl>> result;
    result.reserve(input.size());
    for (const auto& parameter : input) {
        if (!parameter) {
            result.push_back(nullptr);
            continue;
        }
        auto cloned_decl =
            clone_decl_tree(parameter.get(), clone_ctx, error_out);
        auto* cloned_param = dyn_cast<ParamDecl>(cloned_decl.release());
        if (!cloned_param) {
            return {};
        }
        result.emplace_back(cloned_param);
    }
    return result;
}

bool clone_constraint_requirement_impl(const ConstraintRequirement& input,
                                       ConstraintRequirement& output,
                                       ASTContext* ast_ctx,
                                       std::string* error_out) {
    output.kind = input.kind;
    output.type_requirement = input.type_requirement;
    output.is_noexcept = input.is_noexcept;
    output.location = input.location;

    if (input.expr) {
        output.expr = clone_expr_impl(input.expr.get(), ast_ctx, error_out);
        if (!output.expr) {
            return false;
        }
    }
    if (input.return_constraint) {
        output.return_constraint =
            clone_expr_impl(input.return_constraint.get(), ast_ctx, error_out);
        if (!output.return_constraint) {
            return false;
        }
    }
    return true;
}

bool clone_designator_impl(const Designator& input,
                           Designator& output,
                           ASTContext* ast_ctx,
                           std::string* error_out) {
    output.kind = input.kind;
    output.field_name = input.field_name;
    output.loc = input.loc;
    if (input.index) {
        output.index = clone_expr_impl(input.index.get(), ast_ctx, error_out);
        if (!output.index) {
            return false;
        }
    }
    if (input.range_end) {
        output.range_end = clone_expr_impl(input.range_end.get(), ast_ctx, error_out);
        if (!output.range_end) {
            return false;
        }
    }
    return true;
}

bool clone_offsetof_component_impl(const OffsetOfComponent& input,
                                   OffsetOfComponent& output,
                                   ASTContext* ast_ctx,
                                   std::string* error_out) {
    output.field_name = input.field_name;
    output.array_index = input.array_index;
    if (input.array_index_expr) {
        output.array_index_expr =
            clone_expr_impl(input.array_index_expr.get(), ast_ctx, error_out);
        if (!output.array_index_expr) {
            return false;
        }
    }
    return true;
}

TemplateArgument remap_lambda_template_argument(
    TemplateArgument argument,
    const std::unordered_map<const TemplateParameterDecl*,
                             const TemplateParameterDecl*>& parameter_rebinds);

QualType remap_lambda_template_parameter_types(
    QualType type,
    const std::unordered_map<const TemplateParameterDecl*,
                             const TemplateParameterDecl*>& parameter_rebinds) {
    if (!type) {
        return type;
    }

    auto raw = type.get_shared();
    uint8_t quals = type.get_qualifiers();

    if (auto parm_type = dyn_cast_shared<TemplateTypeParmType>(raw)) {
        if (!parm_type->parameter_decl) {
            return type;
        }
        auto it = parameter_rebinds.find(parm_type->parameter_decl);
        if (it == parameter_rebinds.end() || !it->second) {
            return type;
        }
        auto* rebound =
            dyn_cast<TemplateTypeParmDecl>(
                const_cast<TemplateParameterDecl*>(it->second));
        if (!rebound) {
            return type;
        }
        return QualType(rebound->type, quals);
    }

    if (auto pointer = dyn_cast_shared<PointerType>(raw)) {
        auto rewritten =
            remap_lambda_template_parameter_types(
                pointer->pointed_type,
                parameter_rebinds);
        if (rewritten.equals_qualified(pointer->pointed_type)) {
            return type;
        }
        return QualType(
            std::make_shared<PointerType>(rewritten),
            quals);
    }

    if (auto reference = dyn_cast_shared<ReferenceType>(raw)) {
        auto rewritten =
            remap_lambda_template_parameter_types(
                reference->referred_type,
                parameter_rebinds);
        if (rewritten.equals_qualified(reference->referred_type)) {
            return type;
        }
        return QualType(
            std::make_shared<ReferenceType>(
                rewritten,
                reference->reference_kind),
            quals);
    }

    if (auto transform = dyn_cast_shared<BuiltinTypeTransformType>(raw)) {
        auto rewritten =
            remap_lambda_template_parameter_types(
                transform->operand_type,
                parameter_rebinds);
        if (rewritten.equals_qualified(transform->operand_type)) {
            return type;
        }
        return QualType(
            std::make_shared<BuiltinTypeTransformType>(
                transform->transform_kind,
                rewritten),
            quals);
    }

    if (auto member_pointer = dyn_cast_shared<MemberPointerType>(raw)) {
        auto rewritten_class =
            remap_lambda_template_parameter_types(
                member_pointer->class_type,
                parameter_rebinds);
        auto rewritten_member =
            remap_lambda_template_parameter_types(
                member_pointer->member_type,
                parameter_rebinds);
        if (rewritten_class.equals_qualified(member_pointer->class_type) &&
            rewritten_member.equals_qualified(member_pointer->member_type)) {
            return type;
        }
        return QualType(
            std::make_shared<MemberPointerType>(
                rewritten_class,
                rewritten_member),
            quals);
    }

    if (auto array = dyn_cast_shared<ArrayType>(raw)) {
        auto rewritten_element =
            remap_lambda_template_parameter_types(
                array->element_type,
                parameter_rebinds);
        if (rewritten_element.equals_qualified(array->element_type)) {
            return type;
        }
        auto rebuilt = std::make_shared<ArrayType>(*array);
        rebuilt->element_type = rewritten_element;
        return QualType(rebuilt, quals);
    }

    if (auto function = dyn_cast_shared<FunctionType>(raw)) {
        auto rewritten_ret =
            remap_lambda_template_parameter_types(
                function->ret_type,
                parameter_rebinds);
        bool changed = !rewritten_ret.equals_qualified(function->ret_type);
        std::vector<QualType> rewritten_params;
        rewritten_params.reserve(function->parameters.size());
        for (const auto& param_type : function->parameters) {
            auto rewritten_param =
                remap_lambda_template_parameter_types(
                    param_type,
                    parameter_rebinds);
            changed = changed ||
                !rewritten_param.equals_qualified(param_type);
            rewritten_params.push_back(std::move(rewritten_param));
        }
        if (!changed) {
            return type;
        }
        auto rebuilt = std::make_shared<FunctionType>(*function);
        rebuilt->ret_type = rewritten_ret;
        rebuilt->parameters = std::move(rewritten_params);
        return QualType(rebuilt, quals);
    }

    if (auto typedef_type = dyn_cast_shared<TypedefType>(raw)) {
        auto rewritten =
            remap_lambda_template_parameter_types(
                typedef_type->underlying_type,
                parameter_rebinds);
        if (rewritten.equals_qualified(typedef_type->underlying_type)) {
            return type;
        }
        return QualType(
            std::make_shared<TypedefType>(
                typedef_type->name,
                rewritten,
                typedef_type->typedef_decl),
            quals);
    }

    if (auto block_ptr = dyn_cast_shared<BlockPointerType>(raw)) {
        auto rewritten =
            remap_lambda_template_parameter_types(
                block_ptr->pointed_type,
                parameter_rebinds);
        if (rewritten.equals_qualified(block_ptr->pointed_type)) {
            return type;
        }
        return QualType(
            std::make_shared<BlockPointerType>(rewritten),
            quals);
    }

    if (auto spec = dyn_cast_shared<TemplateSpecializationType>(raw)) {
        bool changed = false;
        std::vector<TemplateArgument> rewritten_args;
        rewritten_args.reserve(spec->arguments.size());
        for (const auto& arg : spec->arguments) {
            auto rewritten = remap_lambda_template_argument(arg, parameter_rebinds);
            if (rewritten.type && arg.type &&
                !rewritten.type.equals_qualified(arg.type)) {
                changed = true;
            }
            if (rewritten.value_type && arg.value_type &&
                !rewritten.value_type.equals_qualified(arg.value_type)) {
                changed = true;
            }
            rewritten_args.push_back(std::move(rewritten));
        }
        if (!changed) {
            return type;
        }
        return QualType(
            std::make_shared<TemplateSpecializationType>(
                spec->template_name,
                spec->primary_template,
                std::move(rewritten_args),
                spec->is_dependent),
            quals);
    }

    // Leaf types that cannot contain template parameter references (Builtin,
    // Object, Enum, Auto, etc.) pass through unchanged.  If a new composite
    // type kind is added that can embed template parameters, it must be
    // handled above — this assertion catches the omission early.
    assert(raw->kind == TypeKind::Builtin ||
           raw->kind == TypeKind::Object ||
           raw->kind == TypeKind::Enum ||
           raw->kind == TypeKind::CppTypeInfo ||
           raw->kind == TypeKind::Auto ||
           raw->kind == TypeKind::Complex ||
           raw->kind == TypeKind::Vector ||
           raw->kind == TypeKind::Placeholder ||
           raw->kind == TypeKind::Other ||
           raw->kind == TypeKind::DependentName ||
           raw->kind == TypeKind::TypeofExpr ||
           raw->kind == TypeKind::DecltypeExpr ||
           "remap_lambda_template_parameter_types: unhandled composite type kind");
    return type;
}

TemplateArgument remap_lambda_template_argument(
    TemplateArgument argument,
    const std::unordered_map<const TemplateParameterDecl*,
                             const TemplateParameterDecl*>& parameter_rebinds) {
    if (argument.kind == TemplateArgumentKind::Type) {
        argument.type =
            remap_lambda_template_parameter_types(
                argument.type,
                parameter_rebinds);
        return argument;
    }
    if (argument.kind == TemplateArgumentKind::Value) {
        argument.value_type =
            remap_lambda_template_parameter_types(
                argument.value_type,
                parameter_rebinds);
        if (argument.referenced_parameter) {
            auto it = parameter_rebinds.find(argument.referenced_parameter);
            if (it != parameter_rebinds.end() && it->second) {
                argument.referenced_parameter = it->second;
            }
        }
    }
    return argument;
}

TemplateParameterList clone_lambda_template_parameter_list(
    const TemplateParameterList& parameters,
    ASTContext* ast_ctx,
    std::unordered_map<const TemplateParameterDecl*,
                       const TemplateParameterDecl*>& parameter_rebinds,
    std::string* error_out) {
    TemplateParameterList result;
    result.reserve(parameters.size());
    for (const auto& parameter : parameters) {
        if (!parameter) {
            result.push_back(nullptr);
            continue;
        }

        switch (parameter->get_kind()) {
            case DeclKind::TemplateTypeParmDecl: {
                const auto* type_param =
                    static_cast<const TemplateTypeParmDecl*>(parameter.get());
                auto cloned_type = std::make_shared<TemplateTypeParmType>(
                    type_param->name,
                    type_param->depth,
                    type_param->index,
                    type_param->is_parameter_pack,
                    nullptr);
                auto cloned_param = std::make_unique<TemplateTypeParmDecl>(
                    type_param->name,
                    type_param->depth,
                    type_param->index,
                    cloned_type,
                    type_param->is_parameter_pack,
                    type_param->location);
                cloned_type->parameter_decl = cloned_param.get();
                parameter_rebinds.emplace(parameter.get(), cloned_param.get());
                result.push_back(std::move(cloned_param));
                continue;
            }
            default:
                return {};
        }
    }
    return result;
}

std::unique_ptr<Expr> clone_expr_impl(const Expr* expr,
                                      ASTContext* ast_ctx,
                                      std::string* error_out) {
    if (!expr) {
        return nullptr;
    }

    switch (expr->get_kind()) {
        case StmtKind::IntegerLiteral: {
            const auto* literal = static_cast<const IntegerLiteral*>(expr);
            const std::string* value_ptr = literal->get_value_ptr();
            if (value_ptr && ast_ctx) {
                value_ptr = ast_ctx->intern_identifier(*value_ptr);
            }
            std::unique_ptr<IntegerLiteral> result;
            if (value_ptr) {
                result = std::make_unique<IntegerLiteral>(
                    value_ptr, literal->ctype, literal->location);
            } else {
                result = std::make_unique<IntegerLiteral>(
                    literal->get_value(), literal->ctype, literal->location);
            }
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::FloatingLiteral: {
            const auto* literal = static_cast<const FloatingLiteral*>(expr);
            auto result = std::make_unique<FloatingLiteral>(
                literal->value,
                literal->ctype,
                literal->is_imaginary != 0,
                literal->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::CharacterLiteral: {
            const auto* literal = static_cast<const CharacterLiteral*>(expr);
            auto result = std::make_unique<CharacterLiteral>(
                literal->value, literal->int_value, literal->ctype, literal->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::StringLiteral: {
            const auto* literal = static_cast<const StringLiteral*>(expr);
            auto result = std::make_unique<StringLiteral>(
                literal->value, literal->ctype, literal->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::PredefinedExpr: {
            const auto* predefined = static_cast<const PredefinedExpr*>(expr);
            auto result = std::make_unique<PredefinedExpr>(
                predefined->ident_kind,
                predefined->func_name,
                predefined->ctype,
                predefined->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::CppThisExpr: {
            const auto* this_expr = static_cast<const CppThisExpr*>(expr);
            auto result = std::make_unique<CppThisExpr>(
                this_expr->this_type, this_expr->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::VarRef:
        case StmtKind::QualifiedVarRef: {
            const auto* var_ref = static_cast<const VarRef*>(expr);
            const std::string* spelled_name = var_ref->get_spelled_name_ptr();
            if (spelled_name && ast_ctx) {
                spelled_name = ast_ctx->intern_identifier(*spelled_name);
            }
            std::unique_ptr<Expr> result;
            if (const auto* qualified_info = var_ref->get_cpp_qualified_info()) {
                result = std::make_unique<QualifiedVarRef>(
                    spelled_name,
                    var_ref->symref,
                    *qualified_info,
                    var_ref->location);
            } else if (spelled_name || !var_ref->symref) {
                result = std::make_unique<VarRef>(
                    spelled_name, var_ref->symref, var_ref->location);
            } else {
                result = std::make_unique<VarRef>(var_ref->symref, var_ref->location);
            }
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::UnresolvedLookupExpr: {
            const auto* lookup = static_cast<const UnresolvedLookupExpr*>(expr);
            auto result = std::make_unique<UnresolvedLookupExpr>(
                lookup->name,
                lookup->qualifier,
                lookup->explicit_template_arguments,
                lookup->requires_template_keyword,
                lookup->is_dependent,
                lookup->ctype,
                lookup->location,
                lookup->lexical_lookup_scope,
                lookup->lexical_lookup_context);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::LabelAddressExpr: {
            const auto* label = static_cast<const LabelAddressExpr*>(expr);
            auto result = std::make_unique<LabelAddressExpr>(
                label->label, label->ctype, label->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::FuncCall: {
            const auto* call = static_cast<const FuncCall*>(expr);
            auto cloned_callee = clone_expr_impl(call->func.get(), ast_ctx, error_out);
            if (!cloned_callee) {
                return {};
            }
            auto cloned_args = clone_expr_vector_impl(call->args, ast_ctx, error_out);
            if (call->args.size() != cloned_args.size()) {
                return {};
            }
            auto result = std::make_unique<FuncCall>(
                std::move(cloned_callee), std::move(cloned_args), call->location);
            assign_node_id(result.get(), ast_ctx);
            result->ctype = call->ctype;
            return result;
        }
        case StmtKind::DependentCallExpr: {
            const auto* call = static_cast<const DependentCallExpr*>(expr);
            auto cloned_callee =
                clone_expr_impl(call->callee.get(), ast_ctx, error_out);
            if (call->callee && !cloned_callee) {
                return {};
            }
            auto cloned_args =
                clone_expr_vector_impl(call->args, ast_ctx, error_out);
            if (call->args.size() != cloned_args.size()) {
                return {};
            }
            auto result = std::make_unique<DependentCallExpr>(
                std::move(cloned_callee),
                std::move(cloned_args),
                call->ctype,
                call->known_function_type,
                call->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::DependentArraySubscriptExpr: {
            const auto* subscript =
                static_cast<const DependentArraySubscriptExpr*>(expr);
            auto cloned_array =
                clone_expr_impl(subscript->array.get(), ast_ctx, error_out);
            auto cloned_index =
                clone_expr_impl(subscript->index.get(), ast_ctx, error_out);
            if ((subscript->array && !cloned_array) ||
                (subscript->index && !cloned_index)) {
                return {};
            }
            auto result = std::make_unique<DependentArraySubscriptExpr>(
                std::move(cloned_array),
                std::move(cloned_index),
                subscript->ctype,
                subscript->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::DependentUnaryExpr: {
            const auto* unary = static_cast<const DependentUnaryExpr*>(expr);
            auto cloned_operand =
                clone_expr_impl(unary->operand.get(), ast_ctx, error_out);
            if (unary->operand && !cloned_operand) {
                return {};
            }
            auto result = std::make_unique<DependentUnaryExpr>(
                unary->uop,
                std::move(cloned_operand),
                unary->ctype,
                unary->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::DependentBinaryExpr: {
            const auto* binary = static_cast<const DependentBinaryExpr*>(expr);
            auto cloned_left =
                clone_expr_impl(binary->left.get(), ast_ctx, error_out);
            auto cloned_right =
                clone_expr_impl(binary->right.get(), ast_ctx, error_out);
            if ((binary->left && !cloned_left) ||
                (binary->right && !cloned_right)) {
                return {};
            }
            auto result = std::make_unique<DependentBinaryExpr>(
                std::move(cloned_left),
                std::move(cloned_right),
                binary->bop,
                binary->ctype,
                binary->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::DependentMemberPointerAccessExpr: {
            const auto* access =
                static_cast<const DependentMemberPointerAccessExpr*>(expr);
            auto cloned_base =
                clone_expr_impl(access->base.get(), ast_ctx, error_out);
            auto cloned_member_pointer =
                clone_expr_impl(access->member_pointer.get(), ast_ctx, error_out);
            if ((access->base && !cloned_base) ||
                (access->member_pointer && !cloned_member_pointer)) {
                return {};
            }
            auto result = std::make_unique<DependentMemberPointerAccessExpr>(
                std::move(cloned_base),
                std::move(cloned_member_pointer),
                access->ctype,
                access->is_arrow != 0,
                access->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::PackExpansionExpr: {
            const auto* pack = static_cast<const PackExpansionExpr*>(expr);
            auto cloned_pattern =
                clone_expr_impl(pack->pattern.get(), ast_ctx, error_out);
            if (pack->pattern && !cloned_pattern) {
                return {};
            }
            auto result = std::make_unique<PackExpansionExpr>(
                std::move(cloned_pattern),
                pack->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::FoldExpr: {
            const auto* fold = static_cast<const FoldExpr*>(expr);
            auto cloned_pattern =
                clone_expr_impl(fold->pattern.get(), ast_ctx, error_out);
            auto cloned_init =
                clone_expr_impl(fold->init.get(), ast_ctx, error_out);
            if ((fold->pattern && !cloned_pattern) ||
                (fold->init && !cloned_init)) {
                return {};
            }
            auto result = std::make_unique<FoldExpr>(
                fold->op,
                fold->direction,
                std::move(cloned_pattern),
                std::move(cloned_init),
                fold->result_type,
                fold->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::CppMemberCallExpr: {
            const auto* member_call = static_cast<const CppMemberCallExpr*>(expr);
            std::unique_ptr<FuncCall> lowered_call = nullptr;
            if (member_call->lowered_call) {
                auto cloned_lowered = clone_expr_impl(
                    member_call->lowered_call.get(), ast_ctx, error_out);
                if (!cloned_lowered) {
                    return {};
                }
                lowered_call = std::unique_ptr<FuncCall>(
                    dyn_cast<FuncCall>(cloned_lowered.release()));
                if (!lowered_call) {
                    return fail_clone(
                        error_out,
                        "internal error: failed to clone lowered member call");
                }
            }
            auto result = std::make_unique<CppMemberCallExpr>(
                std::move(lowered_call),
                member_call->member_name,
                member_call->isArrow != 0,
                member_call->suppress_virtual_dispatch != 0,
                member_call->has_implicit_object_argument != 0,
                member_call->location);
            assign_node_id(result.get(), ast_ctx);
            result->ctype = member_call->ctype;
            if (ast_ctx) {
                if (const auto* call_info =
                        ast_ctx->get_cpp_virtual_call_info(member_call->node_id)) {
                    ast_ctx->set_cpp_virtual_call_info(result->node_id, *call_info);
                }
            }
            return result;
        }
        case StmtKind::CppConstructExpr: {
            const auto* construct_expr = static_cast<const CppConstructExpr*>(expr);
            auto cloned_args =
                clone_expr_vector_impl(construct_expr->args, ast_ctx, error_out);
            if (construct_expr->args.size() != cloned_args.size()) {
                return {};
            }
            auto result = std::make_unique<CppConstructExpr>(
                construct_expr->ctor_sym,
                std::move(cloned_args),
                construct_expr->ctype,
                construct_expr->is_list_init,
                construct_expr->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::CppImmediateInvocationExpr: {
            const auto* immediate =
                static_cast<const CppImmediateInvocationExpr*>(expr);
            auto cloned_invocation = clone_expr_impl(
                immediate->invocation.get(), ast_ctx, error_out);
            if (immediate->invocation && !cloned_invocation) {
                return {};
            }
            auto result = std::make_unique<CppImmediateInvocationExpr>(
                std::move(cloned_invocation),
                immediate->value,
                immediate->ctype,
                immediate->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::CppThrowExpr: {
            const auto* throw_expr = static_cast<const CppThrowExpr*>(expr);
            auto cloned_thrown_expr = clone_expr_impl(
                throw_expr->thrown_expr.get(), ast_ctx, error_out);
            if (throw_expr->thrown_expr && !cloned_thrown_expr) {
                return {};
            }
            auto result = std::make_unique<CppThrowExpr>(
                std::move(cloned_thrown_expr),
                throw_expr->ctype,
                throw_expr->is_rethrow,
                throw_expr->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::CppNewExpr: {
            const auto* new_expr = static_cast<const CppNewExpr*>(expr);
            auto cloned_placement_args =
                clone_expr_vector_impl(new_expr->placement_args, ast_ctx, error_out);
            if (new_expr->placement_args.size() != cloned_placement_args.size()) {
                return {};
            }
            auto cloned_initializer = clone_expr_impl(
                new_expr->initializer.get(), ast_ctx, error_out);
            if (new_expr->initializer && !cloned_initializer) {
                return {};
            }
            auto cloned_ctor_args =
                clone_expr_vector_impl(new_expr->constructor_args, ast_ctx, error_out);
            if (new_expr->constructor_args.size() != cloned_ctor_args.size()) {
                return {};
            }
            auto result = std::make_unique<CppNewExpr>(
                new_expr->allocated_type,
                new_expr->result_type,
                std::move(cloned_placement_args),
                std::move(cloned_initializer),
                std::move(cloned_ctor_args),
                new_expr->allocator_sym,
                new_expr->deallocator_sym,
                new_expr->ctor_sym,
                new_expr->is_array_form != 0,
                new_expr->is_global_allocation != 0,
                new_expr->is_list_init != 0,
                new_expr->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::CppDeleteExpr: {
            const auto* delete_expr = static_cast<const CppDeleteExpr*>(expr);
            auto cloned_operand =
                clone_expr_impl(delete_expr->operand.get(), ast_ctx, error_out);
            if (delete_expr->operand && !cloned_operand) {
                return {};
            }
            auto result = std::make_unique<CppDeleteExpr>(
                std::move(cloned_operand),
                delete_expr->ctype,
                delete_expr->destroyed_type,
                delete_expr->deallocator_sym,
                delete_expr->destructor_sym,
                delete_expr->destruction_kind,
                delete_expr->is_array_form != 0,
                delete_expr->is_global_delete != 0,
                delete_expr->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::CppPseudoDestructorExpr: {
            const auto* pseudo_dtor =
                static_cast<const CppPseudoDestructorExpr*>(expr);
            auto cloned_base =
                clone_expr_impl(pseudo_dtor->base.get(), ast_ctx, error_out);
            if (pseudo_dtor->base && !cloned_base) {
                return {};
            }
            auto result = std::make_unique<CppPseudoDestructorExpr>(
                std::move(cloned_base),
                pseudo_dtor->destroyed_type,
                pseudo_dtor->ctype,
                pseudo_dtor->destructor_sym,
                pseudo_dtor->is_arrow != 0,
                pseudo_dtor->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::BlockByrefAccessExpr: {
            const auto* byref_expr = static_cast<const BlockByrefAccessExpr*>(expr);
            auto cloned_cell_expr =
                clone_expr_impl(byref_expr->cell_expr.get(), ast_ctx, error_out);
            if (byref_expr->cell_expr && !cloned_cell_expr) {
                return {};
            }
            auto result = std::make_unique<BlockByrefAccessExpr>(
                std::move(cloned_cell_expr),
                byref_expr->symbol,
                byref_expr->ctype,
                byref_expr->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::BlockExpr: {
            if (!ast_ctx) {
                return fail_clone(
                    error_out,
                    "block cloning requires an ASTContext");
            }

            const auto* block = static_cast<const BlockExpr*>(expr);
            ASTCloneContext bare_clone_ctx;
            bare_clone_ctx.ast_ctx = ast_ctx;

            std::vector<std::unique_ptr<Decl>> cloned_parameters;
            cloned_parameters.reserve(block->parameters.size());
            for (const auto& parameter : block->parameters) {
                auto cloned_parameter = clone_decl_tree(
                    parameter.get(),
                    bare_clone_ctx,
                    error_out);
                if (parameter && !cloned_parameter) {
                    return {};
                }
                cloned_parameters.push_back(std::move(cloned_parameter));
            }

            std::unique_ptr<Stmt> cloned_body_stmt = clone_stmt_tree(
                block->body.get(),
                bare_clone_ctx,
                error_out);
            if (block->body && !cloned_body_stmt) {
                return {};
            }
            if (block->body &&
                !dyn_cast<CompoundStmt>(cloned_body_stmt.get())) {
                return fail_clone(
                    error_out,
                    "failed to clone block body");
            }

            auto cloned_body = std::unique_ptr<CompoundStmt>(
                dyn_cast<CompoundStmt>(cloned_body_stmt.release()));
            auto cloned_semantic_info =
                make_block_semantic_info(*ast_ctx, block->location);
            auto result = std::make_unique<BlockExpr>(
                std::move(cloned_semantic_info),
                block->block_type,
                std::move(cloned_parameters),
                std::move(cloned_body),
                block->stmt_labels,
                block->explicit_return_type,
                block->has_parameter_clause != 0,
                block->has_explicit_return_type != 0,
                block->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::CppLambdaExpr: {
            if (!ast_ctx) {
                return fail_clone(
                    error_out,
                    "lambda cloning requires an ASTContext");
            }

            const auto* lambda = static_cast<const CppLambdaExpr*>(expr);
            std::unordered_map<const TemplateParameterDecl*,
                               const TemplateParameterDecl*> parameter_rebinds;
            auto cloned_template_parameters =
                clone_lambda_template_parameter_list(
                    lambda->call_operator_template_parameters,
                    ast_ctx,
                    parameter_rebinds,
                    error_out);
            if (lambda->call_operator_template_parameters.size() !=
                cloned_template_parameters.size()) {
                return fail_clone(
                    error_out,
                    "lambda template-parameter cloning is not supported");
            }

            ASTCloneContext bare_clone_ctx;
            bare_clone_ctx.ast_ctx = ast_ctx;

            LambdaClosureInfo cloned_closure_info;
            cloned_closure_info.default_capture =
                lambda->closure_info.default_capture;
            cloned_closure_info.captures.reserve(
                lambda->closure_info.captures.size());
            for (const auto& capture : lambda->closure_info.captures) {
                CppLambdaCapture cloned_capture;
                cloned_capture.name = capture.name;
                cloned_capture.symbol = capture.symbol;
                cloned_capture.by_reference = capture.by_reference;
                cloned_capture.captures_this = capture.captures_this;
                cloned_capture.is_init_capture = capture.is_init_capture;
                cloned_capture.location = capture.location;
                if (capture.initializer) {
                    auto cloned_initializer = clone_expr_tree(
                        capture.initializer.get(),
                        ast_ctx,
                        error_out);
                    if (!cloned_initializer) {
                        return {};
                    }
                    cloned_capture.initializer = std::shared_ptr<Expr>(
                        cloned_initializer.release());
                }
                cloned_closure_info.captures.push_back(
                    std::move(cloned_capture));
            }

            std::vector<std::unique_ptr<Decl>> cloned_parameters;
            cloned_parameters.reserve(lambda->parameters.size());
            for (const auto& parameter : lambda->parameters) {
                auto cloned_parameter = clone_decl_tree(
                    parameter.get(),
                    bare_clone_ctx,
                    error_out);
                if (parameter && !cloned_parameter) {
                    return {};
                }
                cloned_parameters.push_back(std::move(cloned_parameter));
            }

            std::unique_ptr<Stmt> cloned_body_stmt = clone_stmt_tree(
                lambda->body.get(),
                bare_clone_ctx,
                error_out);
            if (lambda->body && !cloned_body_stmt) {
                return {};
            }
            if (lambda->body &&
                !dyn_cast<CompoundStmt>(cloned_body_stmt.get())) {
                return fail_clone(
                    error_out,
                    "failed to clone lambda body");
            }

            QualType cloned_written_type =
                remap_lambda_template_parameter_types(
                    lambda->written_call_operator_type,
                    parameter_rebinds);
            QualType cloned_explicit_return_type =
                remap_lambda_template_parameter_types(
                    lambda->explicit_return_type,
                    parameter_rebinds);

            if (!parameter_rebinds.empty()) {
                ASTCloneContext rebind_ctx;
                rebind_ctx.ast_ctx = ast_ctx;
                rebind_ctx.rewrite_type =
                    [&parameter_rebinds](QualType type) -> QualType {
                    return remap_lambda_template_parameter_types(
                        type,
                        parameter_rebinds);
                    };
                rebind_ctx.rewrite_template_arguments =
                    [&parameter_rebinds](
                        const std::vector<TemplateArgument>& arguments,
                        ASTCloneContext&,
                        std::string*) -> std::vector<TemplateArgument> {
                        std::vector<TemplateArgument> rewritten;
                        rewritten.reserve(arguments.size());
                        for (const auto& argument : arguments) {
                            rewritten.push_back(
                                remap_lambda_template_argument(
                                    argument,
                                    parameter_rebinds));
                        }
                        return rewritten;
                    };

                for (auto& parameter : cloned_parameters) {
                    if (parameter &&
                        !rewrite_decl_tree_in_place(
                            parameter,
                            rebind_ctx,
                            error_out)) {
                        return {};
                    }
                }
                if (cloned_body_stmt &&
                    !rewrite_stmt_tree_in_place(
                        cloned_body_stmt,
                        rebind_ctx,
                        error_out)) {
                    return {};
                }
                for (auto& capture : cloned_closure_info.captures) {
                    if (!capture.initializer) {
                        continue;
                    }
                    auto owned_initializer = clone_expr_tree(
                        capture.initializer.get(),
                        ast_ctx,
                        error_out);
                    if (!owned_initializer) {
                        return {};
                    }
                    if (!rewrite_expr_tree_in_place(
                            owned_initializer,
                            rebind_ctx,
                            error_out)) {
                        return {};
                    }
                    capture.initializer = std::shared_ptr<Expr>(
                        owned_initializer.release());
                }
            }

            auto cloned_body = std::unique_ptr<CompoundStmt>(
                dyn_cast<CompoundStmt>(cloned_body_stmt.release()));

            auto cloned_semantic_info =
                make_lambda_semantic_info(*ast_ctx, lambda->location);
            cloned_semantic_info.lexical_this_context =
                lambda->semantic_info.lexical_this_context;
            auto result = std::make_unique<CppLambdaExpr>(
                std::move(cloned_closure_info),
                std::move(cloned_semantic_info),
                std::move(cloned_written_type),
                std::move(cloned_template_parameters),
                std::move(cloned_parameters),
                std::move(cloned_body),
                lambda->stmt_labels,
                std::move(cloned_explicit_return_type),
                lambda->has_parameter_clause != 0,
                lambda->is_mutable != 0,
                lambda->has_noexcept != 0,
                lambda->has_trailing_return != 0,
                lambda->is_generic != 0,
                lambda->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::CppTypeIdExpr: {
            const auto* typeid_expr = static_cast<const CppTypeIdExpr*>(expr);
            std::unique_ptr<Expr> result;
            if (typeid_expr->is_type_operand) {
                result = std::make_unique<CppTypeIdExpr>(
                    typeid_expr->type_operand,
                    typeid_expr->ctype,
                    typeid_expr->location);
            } else {
                auto cloned_operand =
                    clone_expr_impl(typeid_expr->expr_operand.get(), ast_ctx, error_out);
                if (typeid_expr->expr_operand && !cloned_operand) {
                    return {};
                }
                result = std::make_unique<CppTypeIdExpr>(
                    std::move(cloned_operand),
                    typeid_expr->ctype,
                    typeid_expr->location);
            }
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::CppDynamicCastExpr: {
            const auto* dynamic_cast_expr = static_cast<const CppDynamicCastExpr*>(expr);
            auto cloned_operand =
                clone_expr_impl(dynamic_cast_expr->expr.get(), ast_ctx, error_out);
            if (dynamic_cast_expr->expr && !cloned_operand) {
                return {};
            }
            auto result = std::make_unique<CppDynamicCastExpr>(
                std::move(cloned_operand),
                dynamic_cast_expr->target_type,
                dynamic_cast_expr->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::CondExpr: {
            const auto* cond_expr = static_cast<const CondExpr*>(expr);
            auto cloned_condition =
                clone_expr_impl(cond_expr->condition.get(), ast_ctx, error_out);
            auto cloned_true_expr =
                clone_expr_impl(cond_expr->true_expr.get(), ast_ctx, error_out);
            auto cloned_false_expr =
                clone_expr_impl(cond_expr->false_expr.get(), ast_ctx, error_out);
            if (!cloned_condition || !cloned_true_expr || !cloned_false_expr) {
                return {};
            }
            auto result = std::make_unique<CondExpr>(
                std::move(cloned_condition),
                std::move(cloned_true_expr),
                std::move(cloned_false_expr),
                cond_expr->type);
            assign_node_id(result.get(), ast_ctx);
            result->location = cond_expr->location;
            return result;
        }
        case StmtKind::UnaryOperation: {
            const auto* unary = static_cast<const UnaryOperation*>(expr);
            auto cloned_operand = clone_expr_impl(unary->exp.get(), ast_ctx, error_out);
            if (unary->exp && !cloned_operand) {
                return {};
            }
            auto result = std::make_unique<UnaryOperation>(
                unary->uop, std::move(cloned_operand), unary->location);
            assign_node_id(result.get(), ast_ctx);
            result->ctype = unary->ctype;
            return result;
        }
        case StmtKind::ImplicitCast: {
            const auto* implicit_cast = static_cast<const ImplicitCast*>(expr);
            auto cloned_expr = clone_expr_impl(
                implicit_cast->expr.get(), ast_ctx, error_out);
            if (implicit_cast->expr && !cloned_expr) {
                return {};
            }
            auto result = std::make_unique<ImplicitCast>(
                implicit_cast->kind, std::move(cloned_expr), implicit_cast->ctype);
            assign_node_id(result.get(), ast_ctx);
            result->location = implicit_cast->location;
            return result;
        }
        case StmtKind::ExplicitCast: {
            const auto* explicit_cast = static_cast<const ExplicitCast*>(expr);
            auto cloned_expr = clone_expr_impl(
                explicit_cast->expr.get(), ast_ctx, error_out);
            if (explicit_cast->expr && !cloned_expr) {
                return {};
            }
            auto result = std::make_unique<ExplicitCast>(
                std::move(cloned_expr), explicit_cast->ctype, explicit_cast->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::CompoundAssignOperation: {
            const auto* compound_assign =
                static_cast<const CompoundAssignOperation*>(expr);
            auto cloned_lhs = clone_expr_impl(
                compound_assign->left.get(), ast_ctx, error_out);
            auto cloned_rhs = clone_expr_impl(
                compound_assign->right.get(), ast_ctx, error_out);
            if (!cloned_lhs || !cloned_rhs) {
                return {};
            }
            auto result = std::make_unique<CompoundAssignOperation>(
                std::move(cloned_lhs),
                std::move(cloned_rhs),
                compound_assign->bop,
                compound_assign->ctype);
            assign_node_id(result.get(), ast_ctx);
            result->location = compound_assign->location;
            return result;
        }
        case StmtKind::BinaryOperation: {
            const auto* binary = static_cast<const BinaryOperation*>(expr);
            auto cloned_lhs = clone_expr_impl(binary->left.get(), ast_ctx, error_out);
            auto cloned_rhs = clone_expr_impl(binary->right.get(), ast_ctx, error_out);
            if (!cloned_lhs || !cloned_rhs) {
                return {};
            }
            auto result = std::make_unique<BinaryOperation>(
                std::move(cloned_lhs), std::move(cloned_rhs), binary->bop);
            assign_node_id(result.get(), ast_ctx);
            result->location = binary->location;
            result->ctype = binary->ctype;
            return result;
        }
        case StmtKind::ArraySubscriptExpr: {
            const auto* subscript = static_cast<const ArraySubscriptExpr*>(expr);
            auto cloned_array =
                clone_expr_impl(subscript->array.get(), ast_ctx, error_out);
            auto cloned_index =
                clone_expr_impl(subscript->index.get(), ast_ctx, error_out);
            if (!cloned_array || !cloned_index) {
                return {};
            }
            auto result = std::make_unique<ArraySubscriptExpr>(
                std::move(cloned_array),
                std::move(cloned_index),
                subscript->ctype,
                subscript->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::MemberExpr: {
            const auto* member_expr = static_cast<const MemberExpr*>(expr);
            auto cloned_base = clone_expr_impl(member_expr->base.get(), ast_ctx, error_out);
            if (member_expr->base && !cloned_base) {
                return {};
            }
            const std::string* member_name = member_expr->get_member_name_ptr();
            if (member_name && ast_ctx) {
                member_name = ast_ctx->intern_identifier(*member_name);
            }
            auto result = std::make_unique<MemberExpr>(
                std::move(cloned_base),
                member_name,
                member_expr->isArrow != 0,
                member_expr->suppress_virtual_dispatch != 0,
                member_expr->location);
            assign_node_id(result.get(), ast_ctx);
            result->member_type = member_expr->member_type;
            result->virtual_base_record_decl =
                member_expr->virtual_base_record_decl;
            result->field_index = member_expr->field_index;
            result->field_path = member_expr->field_path;
            result->byte_offset = member_expr->byte_offset;
            result->is_bitfield = member_expr->is_bitfield;
            if (ast_ctx && member_expr->is_bitfield) {
                if (const auto* bitfield_info =
                        ast_ctx->get_bitfield_info(member_expr->node_id)) {
                    ast_ctx->set_bitfield_info(result->node_id, *bitfield_info);
                }
            }
            return result;
        }
        case StmtKind::UnresolvedMemberExpr: {
            const auto* member_expr =
                static_cast<const UnresolvedMemberExpr*>(expr);
            auto cloned_base =
                clone_expr_impl(member_expr->base.get(), ast_ctx, error_out);
            if (member_expr->base && !cloned_base) {
                return {};
            }
            auto result = std::make_unique<UnresolvedMemberExpr>(
                std::move(cloned_base),
                member_expr->member_name,
                member_expr->member_type,
                member_expr->explicit_template_arguments,
                member_expr->isArrow != 0,
                member_expr->is_current_instantiation != 0,
                member_expr->names_dependent_base != 0,
                member_expr->requires_template_keyword != 0,
                member_expr->suppress_virtual_dispatch != 0,
                member_expr->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::MemberPointerLiteralExpr: {
            const auto* member_ptr_lit =
                static_cast<const MemberPointerLiteralExpr*>(expr);
            auto result = std::make_unique<MemberPointerLiteralExpr>(
                member_ptr_lit->ctype,
                member_ptr_lit->byte_offset,
                member_ptr_lit->is_function_member != 0,
                member_ptr_lit->method_symbol,
                member_ptr_lit->virtual_slot_index,
                member_ptr_lit->member_name,
                member_ptr_lit->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::MemberPointerAccessExpr: {
            const auto* member_ptr_access =
                static_cast<const MemberPointerAccessExpr*>(expr);
            auto cloned_base =
                clone_expr_impl(member_ptr_access->base.get(), ast_ctx, error_out);
            auto cloned_member_pointer = clone_expr_impl(
                member_ptr_access->member_pointer.get(), ast_ctx, error_out);
            if (!cloned_base || !cloned_member_pointer) {
                return {};
            }
            auto result = std::make_unique<MemberPointerAccessExpr>(
                std::move(cloned_base),
                std::move(cloned_member_pointer),
                member_ptr_access->result_type,
                member_ptr_access->is_arrow != 0,
                member_ptr_access->is_function_member != 0,
                member_ptr_access->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::InitListExpr: {
            const auto* init_list = static_cast<const InitListExpr*>(expr);
            auto result = std::make_unique<InitListExpr>(init_list->location);
            assign_node_id(result.get(), ast_ctx);
            result->is_paren_init = init_list->is_paren_init;
            result->type = init_list->type;

            result->elements.reserve(init_list->elements.size());
            for (const auto& element : init_list->elements) {
                InitElement new_element;
                new_element.loc = element.loc;
                new_element.designators.reserve(element.designators.size());
                for (const auto& designator : element.designators) {
                    Designator cloned_designator;
                    if (!clone_designator_impl(
                            designator, cloned_designator, ast_ctx, error_out)) {
                        return {};
                    }
                    new_element.designators.push_back(std::move(cloned_designator));
                }
                if (element.value) {
                    new_element.value =
                        clone_expr_impl(element.value.get(), ast_ctx, error_out);
                    if (!new_element.value) {
                        return {};
                    }
                }
                result->elements.push_back(std::move(new_element));
            }

            result->actions.reserve(init_list->actions.size());
            for (const auto& action : init_list->actions) {
                InitAction new_action;
                new_action.paths = action.paths;
                new_action.loc = action.loc;
                if (action.value) {
                    new_action.value =
                        clone_shared_expr_impl(action.value, ast_ctx, error_out);
                    if (!new_action.value) {
                        return {};
                    }
                }
                result->actions.push_back(std::move(new_action));
            }

            for (const auto& [index, value] : init_list->mappings) {
                auto cloned_value = clone_shared_expr_impl(value, ast_ctx, error_out);
                if (value && !cloned_value) {
                    return {};
                }
                result->mappings[index] = std::move(cloned_value);
            }
            return result;
        }
        case StmtKind::SizeOfExpr: {
            const auto* sizeof_expr = static_cast<const SizeOfExpr*>(expr);
            std::unique_ptr<Expr> result;
            if (sizeof_expr->expr_operand) {
                auto cloned_operand =
                    clone_expr_impl(sizeof_expr->expr_operand.get(), ast_ctx, error_out);
                if (!cloned_operand) {
                    return {};
                }
                result = std::make_unique<SizeOfExpr>(
                    std::move(cloned_operand), sizeof_expr->location);
            } else {
                result = std::make_unique<SizeOfExpr>(
                    sizeof_expr->type_operand, sizeof_expr->location);
            }
            assign_node_id(result.get(), ast_ctx);
            auto* cloned_sizeof = static_cast<SizeOfExpr*>(result.get());
            cloned_sizeof->result_type = sizeof_expr->result_type;
            cloned_sizeof->is_runtime_sizeof = sizeof_expr->is_runtime_sizeof;
            return result;
        }
        case StmtKind::SizeOfPackExpr: {
            const auto* sizeof_pack = static_cast<const SizeOfPackExpr*>(expr);
            auto result = std::make_unique<SizeOfPackExpr>(
                sizeof_pack->pack_name,
                sizeof_pack->parameter_decl,
                sizeof_pack->location);
            assign_node_id(result.get(), ast_ctx);
            result->parameter_kind = sizeof_pack->parameter_kind;
            result->parameter_depth = sizeof_pack->parameter_depth;
            result->parameter_index = sizeof_pack->parameter_index;
            result->result_type = sizeof_pack->result_type;
            return result;
        }
        case StmtKind::CompoundLiteralExpr: {
            const auto* compound_literal = static_cast<const CompoundLiteralExpr*>(expr);
            auto cloned_init =
                clone_expr_impl(compound_literal->init.get(), ast_ctx, error_out);
            if (compound_literal->init && !cloned_init) {
                return {};
            }
            auto result = std::make_unique<CompoundLiteralExpr>(
                compound_literal->type,
                std::move(cloned_init),
                compound_literal->location);
            assign_node_id(result.get(), ast_ctx);
            result->has_static_storage = compound_literal->has_static_storage;
            return result;
        }
        case StmtKind::StmtExpr:
            return fail_clone(
                error_out,
                "statement-expression cloning is not supported");
        case StmtKind::VaArgExpr: {
            const auto* va_arg_expr = static_cast<const VaArgExpr*>(expr);
            auto cloned_list_expr =
                clone_expr_impl(va_arg_expr->va_list_expr.get(), ast_ctx, error_out);
            if (va_arg_expr->va_list_expr && !cloned_list_expr) {
                return {};
            }
            auto result = std::make_unique<VaArgExpr>(
                std::move(cloned_list_expr),
                va_arg_expr->arg_type,
                va_arg_expr->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::VaStartExpr: {
            const auto* va_start_expr = static_cast<const VaStartExpr*>(expr);
            auto cloned_list_expr =
                clone_expr_impl(va_start_expr->va_list_expr.get(), ast_ctx, error_out);
            auto cloned_last_param =
                clone_expr_impl(va_start_expr->last_param.get(), ast_ctx, error_out);
            if (!cloned_list_expr || !cloned_last_param) {
                return {};
            }
            auto result = std::make_unique<VaStartExpr>(
                std::move(cloned_list_expr),
                std::move(cloned_last_param),
                va_start_expr->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::VaEndExpr: {
            const auto* va_end_expr = static_cast<const VaEndExpr*>(expr);
            auto cloned_list_expr =
                clone_expr_impl(va_end_expr->va_list_expr.get(), ast_ctx, error_out);
            if (va_end_expr->va_list_expr && !cloned_list_expr) {
                return {};
            }
            auto result = std::make_unique<VaEndExpr>(
                std::move(cloned_list_expr), va_end_expr->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::VaCopyExpr: {
            const auto* va_copy_expr = static_cast<const VaCopyExpr*>(expr);
            auto cloned_dest = clone_expr_impl(va_copy_expr->dest.get(), ast_ctx, error_out);
            auto cloned_src = clone_expr_impl(va_copy_expr->src.get(), ast_ctx, error_out);
            if (!cloned_dest || !cloned_src) {
                return {};
            }
            auto result = std::make_unique<VaCopyExpr>(
                std::move(cloned_dest), std::move(cloned_src), va_copy_expr->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::AlignOfExpr: {
            const auto* alignof_expr = static_cast<const AlignOfExpr*>(expr);
            std::unique_ptr<Expr> result;
            if (alignof_expr->expr_operand) {
                auto cloned_operand =
                    clone_expr_impl(alignof_expr->expr_operand.get(), ast_ctx, error_out);
                if (!cloned_operand) {
                    return {};
                }
                result = std::make_unique<AlignOfExpr>(
                    std::move(cloned_operand), alignof_expr->location);
            } else {
                result = std::make_unique<AlignOfExpr>(
                    alignof_expr->type_operand, alignof_expr->location);
            }
            assign_node_id(result.get(), ast_ctx);
            auto* cloned_alignof = static_cast<AlignOfExpr*>(result.get());
            cloned_alignof->result_type = alignof_expr->result_type;
            return result;
        }
        case StmtKind::CppNoexceptExpr: {
            const auto* noexcept_expr =
                static_cast<const CppNoexceptExpr*>(expr);
            auto cloned_operand =
                clone_expr_impl(noexcept_expr->operand.get(), ast_ctx, error_out);
            if (noexcept_expr->operand && !cloned_operand) {
                return {};
            }
            auto result = std::make_unique<CppNoexceptExpr>(
                std::move(cloned_operand),
                noexcept_expr->ctype,
                noexcept_expr->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        case StmtKind::GenericExpr: {
            const auto* generic_expr = static_cast<const GenericExpr*>(expr);
            auto cloned_controlling_expr = clone_expr_impl(
                generic_expr->controlling_expr.get(), ast_ctx, error_out);
            if (!cloned_controlling_expr) {
                return {};
            }
            auto result = std::make_unique<GenericExpr>(
                std::move(cloned_controlling_expr), generic_expr->location);
            assign_node_id(result.get(), ast_ctx);
            result->result_index = generic_expr->result_index;
            result->result_type = generic_expr->result_type;
            result->associations.reserve(generic_expr->associations.size());
            for (const auto& assoc : generic_expr->associations) {
                GenericAssociation new_assoc;
                new_assoc.type = assoc.type;
                new_assoc.is_default = assoc.is_default;
                new_assoc.loc = assoc.loc;
                if (assoc.expr) {
                    new_assoc.expr = clone_expr_impl(assoc.expr.get(), ast_ctx, error_out);
                    if (!new_assoc.expr) {
                        return {};
                    }
                }
                result->associations.push_back(std::move(new_assoc));
            }
            return result;
        }
        case StmtKind::OffsetOfExpr: {
            const auto* offsetof_expr = static_cast<const OffsetOfExpr*>(expr);
            auto result = std::make_unique<OffsetOfExpr>(
                offsetof_expr->type_operand,
                offsetof_expr->member_name,
                offsetof_expr->location);
            assign_node_id(result.get(), ast_ctx);
            result->designator_path.reserve(offsetof_expr->designator_path.size());
            for (const auto& component : offsetof_expr->designator_path) {
                OffsetOfComponent cloned_component;
                if (!clone_offsetof_component_impl(
                        component, cloned_component, ast_ctx, error_out)) {
                    return {};
                }
                result->designator_path.push_back(std::move(cloned_component));
            }
            result->result_type = offsetof_expr->result_type;
            result->computed_offset = offsetof_expr->computed_offset;
            return result;
        }
        case StmtKind::BuiltinCallExpr: {
            const auto* builtin_expr = static_cast<const BuiltinCallExpr*>(expr);
            auto cloned_args = clone_expr_vector_impl(builtin_expr->args, ast_ctx, error_out);
            if (builtin_expr->args.size() != cloned_args.size()) {
                return {};
            }
            std::unique_ptr<BuiltinCallExpr> result;
            if (builtin_expr->type_args.empty()) {
                result = std::make_unique<BuiltinCallExpr>(
                    builtin_expr->kind,
                    std::move(cloned_args),
                    builtin_expr->result_type,
                    builtin_expr->location);
            } else {
                result = std::make_unique<BuiltinCallExpr>(
                    builtin_expr->kind,
                    std::move(cloned_args),
                    builtin_expr->type_args,
                    builtin_expr->result_type,
                    builtin_expr->location);
            }
            assign_node_id(result.get(), ast_ctx);
            result->const_value = builtin_expr->const_value;
            return result;
        }
        case StmtKind::ConceptSpecializationExpr: {
            const auto* concept_expr =
                static_cast<const ConceptSpecializationExpr*>(expr);
            auto result = std::make_unique<ConceptSpecializationExpr>(
                concept_expr->concept_decl,
                concept_expr->concept_name,
                concept_expr->arguments,
                concept_expr->result_type,
                concept_expr->location);
            assign_node_id(result.get(), ast_ctx);
            result->satisfaction = concept_expr->satisfaction;
            return result;
        }
        case StmtKind::RequiresExpr: {
            const auto* requires_expr = static_cast<const RequiresExpr*>(expr);
            auto cloned_parameters = clone_requires_param_list(
                requires_expr->parameters,
                ast_ctx,
                error_out);
            if (cloned_parameters.size() != requires_expr->parameters.size()) {
                return {};
            }
            std::vector<ConstraintRequirement> cloned_requirements;
            cloned_requirements.reserve(requires_expr->requirements.size());
            for (const auto& requirement : requires_expr->requirements) {
                ConstraintRequirement cloned_requirement;
                if (!clone_constraint_requirement_impl(
                        requirement,
                        cloned_requirement,
                        ast_ctx,
                        error_out)) {
                    return {};
                }
                cloned_requirements.push_back(std::move(cloned_requirement));
            }
            auto result = std::make_unique<RequiresExpr>(
                std::move(cloned_parameters),
                std::move(cloned_requirements),
                requires_expr->result_type,
                requires_expr->location);
            assign_node_id(result.get(), ast_ctx);
            result->satisfaction = requires_expr->satisfaction;
            return result;
        }
        case StmtKind::ErrorExpr: {
            const auto* error_expr = static_cast<const ErrorExpr*>(expr);
            auto result = std::make_unique<ErrorExpr>(
                error_expr->error_message, error_expr->location);
            assign_node_id(result.get(), ast_ctx);
            return result;
        }
        default:
            break;
    }

    int kind_value = static_cast<int>(expr->get_kind());
    return fail_clone(
        error_out,
        "unsupported expression clone kind " + std::to_string(kind_value));
}
} // namespace

std::unique_ptr<Expr> clone_expr_tree(const Expr* expr,
                                      ASTContext* ast_ctx,
                                      std::string* error_out) {
    std::string local_error;
    if (!error_out) {
        error_out = &local_error;
    } else {
        error_out->clear();
    }
    return clone_expr_impl(expr, ast_ctx, error_out);
}
