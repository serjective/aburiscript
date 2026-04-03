#include "ast_clone.h"

#include "ast_context.h"
#include "expr_clone.h"

#include <type_traits>

namespace {
template <typename NodeType>
void assign_node_id(NodeType* node, ASTContext* ast_ctx) {
    if (node && ast_ctx) {
        node->node_id = ast_ctx->next_node_id();
    }
}

std::unique_ptr<Stmt> fail_stmt_clone(std::string* error_out,
                                      const std::string& message) {
    if (error_out && error_out->empty()) {
        *error_out = message;
    }
    return nullptr;
}

std::unique_ptr<Decl> fail_decl_clone(std::string* error_out,
                                      const std::string& message) {
    if (error_out && error_out->empty()) {
        *error_out = message;
    }
    return nullptr;
}

bool set_expr_error(std::string* error_out, const std::string& message) {
    if (error_out && error_out->empty()) {
        *error_out = message;
    }
    return false;
}

QualType get_sizeof_result_type(ASTContext* ast_ctx) {
    if (ast_ctx && ast_ctx->type_ctx) {
        if (auto size_t_type =
                ast_ctx->type_ctx->get_builtin(BuiltinTypes::ULong)) {
            return QualType(size_t_type);
        }
        if (auto int_type = ast_ctx->type_ctx->get_builtin(BuiltinTypes::Int)) {
            return QualType(int_type);
        }
    }
    return nullptr;
}

std::unique_ptr<Expr> make_pack_size_integer_literal(size_t pack_size,
                                                     ASTContext* ast_ctx,
                                                     SrcLoc loc) {
    auto value = std::to_string(pack_size);
    const std::string* interned_value =
        ast_ctx ? ast_ctx->intern_identifier(value) : nullptr;
    auto result_type = get_sizeof_result_type(ast_ctx);
    std::unique_ptr<Expr> literal;
    if (interned_value) {
        literal =
            std::make_unique<IntegerLiteral>(interned_value, result_type, loc);
    } else {
        literal = std::make_unique<IntegerLiteral>(
            std::move(value),
            result_type,
            loc);
    }
    assign_node_id(literal.get(), ast_ctx);
    return literal;
}

QualType rewrite_type(QualType type, ASTCloneContext& ctx) {
    if (!ctx.rewrite_type) {
        return type;
    }
    return ctx.rewrite_type(type);
}

bool clone_attribute_list(const AttributeList& source,
                          AttributeList& destination,
                          ASTCloneContext& ctx,
                          std::string* error_out) {
    destination.attrs.reserve(source.attrs.size());
    for (const auto& attr : source.attrs) {
        ParsedAttribute cloned_attr;
        cloned_attr.ns = attr.ns;
        cloned_attr.name = attr.name;
        cloned_attr.loc = attr.loc;
        cloned_attr.resolved_kind = attr.resolved_kind;
        cloned_attr.args.reserve(attr.args.size());
        for (const auto& arg : attr.args) {
            AttributeArg cloned_arg;
            cloned_arg.kind = arg.kind;
            cloned_arg.str_value = arg.str_value;
            cloned_arg.key = arg.key;
            cloned_arg.int_value = arg.int_value;
            cloned_arg.float_value = arg.float_value;
            cloned_arg.loc = arg.loc;
            if (arg.expr_value) {
                auto cloned_expr = clone_expr_with_substitution(
                    arg.expr_value.get(),
                    ctx,
                    error_out);
                if (!cloned_expr) {
                    return false;
                }
                cloned_arg.expr_value =
                    std::shared_ptr<Expr>(cloned_expr.release());
            }
            cloned_attr.args.push_back(std::move(cloned_arg));
        }
        destination.attrs.push_back(std::move(cloned_attr));
    }
    return true;
}

bool rewrite_attribute_list_in_place(AttributeList& attrs,
                                     ASTCloneContext& ctx,
                                     std::string* error_out) {
    for (auto& attr : attrs.attrs) {
        for (auto& arg : attr.args) {
            if (!arg.expr_value) {
                continue;
            }
            auto rewritten_expr = clone_expr_with_substitution(
                arg.expr_value.get(),
                ctx,
                error_out);
            if (!rewritten_expr) {
                return false;
            }
            arg.expr_value = std::shared_ptr<Expr>(rewritten_expr.release());
        }
    }
    return true;
}

bool copy_decl_side_tables(const Decl* source,
                           Decl* destination,
                           ASTCloneContext& ctx,
                           std::string* error_out) {
    if (!source || !destination || !ctx.ast_ctx ||
        !ctx.ast_ctx->has_attrs(source->node_id)) {
        return true;
    }
    AttributeList cloned_attrs;
    if (!clone_attribute_list(
            ctx.ast_ctx->get_attrs(source->node_id),
            cloned_attrs,
            ctx,
            error_out)) {
        return false;
    }
    ctx.ast_ctx->set_attrs(destination->node_id, std::move(cloned_attrs));
    return true;
}

std::vector<TemplateArgument> rewrite_template_arguments(
    const std::vector<TemplateArgument>& arguments,
    ASTCloneContext& ctx,
    std::string* error_out) {
    if (!ctx.rewrite_template_arguments) {
        return arguments;
    }
    return ctx.rewrite_template_arguments(arguments, ctx, error_out);
}

bool rewrite_optional_template_arguments(
    std::optional<std::vector<TemplateArgument>>& arguments,
    ASTCloneContext& ctx,
    std::string* error_out) {
    if (!arguments.has_value()) {
        return true;
    }
    auto rewritten = rewrite_template_arguments(*arguments, ctx, error_out);
    if (rewritten.empty() && !arguments->empty() &&
        error_out && !error_out->empty()) {
        return false;
    }
    arguments = std::move(rewritten);
    return true;
}

std::shared_ptr<Symbol> remap_symbol(const std::shared_ptr<Symbol>& sym,
                                     ASTCloneContext& ctx);
bool rewrite_expr_tree(std::unique_ptr<Expr>& expr,
                       ASTCloneContext& ctx,
                       std::string* error_out);

bool rewrite_param_decl_in_place(ParamDecl* param,
                                 ASTCloneContext& ctx,
                                 std::string* error_out) {
    if (!param) {
        return true;
    }
    param->type = rewrite_type(param->type, ctx);
    param->original_type =
        rewrite_type(QualType(param->original_type), ctx).get_shared();
    param->sym = remap_symbol(param->sym, ctx);
    if (param->sym) {
        param->sym->type = rewrite_type(param->sym->type, ctx);
    }
    if (const Expr* default_arg = get_param_decl_default_argument(param)) {
        auto cloned_default = clone_expr_with_substitution(
            default_arg,
            ctx,
            error_out);
        if (!cloned_default) {
            return false;
        }
        set_param_decl_default_argument(param, std::move(cloned_default));
    }
    return true;
}

bool rewrite_constraint_requirements_in_place(
    std::vector<ConstraintRequirement>& requirements,
    ASTCloneContext& ctx,
    std::string* error_out) {
    for (auto& requirement : requirements) {
        if (requirement.expr &&
            !rewrite_expr_tree(requirement.expr, ctx, error_out)) {
            return false;
        }
        requirement.type_requirement =
            rewrite_type(requirement.type_requirement, ctx);
        if (requirement.return_constraint &&
            !rewrite_expr_tree(requirement.return_constraint, ctx, error_out)) {
            return false;
        }
    }
    return true;
}

std::shared_ptr<Symbol> remap_symbol(const std::shared_ptr<Symbol>& sym,
                                     ASTCloneContext& ctx) {
    if (!sym) {
        return nullptr;
    }
    auto it = ctx.symbol_remap.find(sym.get());
    if (it != ctx.symbol_remap.end()) {
        return it->second;
    }
    if (ctx.rewrite_symbol) {
        return ctx.rewrite_symbol(sym);
    }
    return sym;
}

void register_symbol(const std::shared_ptr<Symbol>& sym, ASTCloneContext& ctx) {
    if (sym && ctx.register_symbol) {
        ctx.register_symbol(sym);
    }
}

std::shared_ptr<Scope> clone_scope(const std::shared_ptr<Scope>& scope,
                                   ASTCloneContext& ctx) {
    if (!scope) {
        return nullptr;
    }
    auto it = ctx.scope_remap.find(scope.get());
    if (it != ctx.scope_remap.end()) {
        return it->second;
    }

    auto cloned = std::make_shared<Scope>();
    ctx.scope_remap.emplace(scope.get(), cloned);
    cloned->flags = scope->flags;
    cloned->cxx_namespace_path = scope->cxx_namespace_path;
    cloned->parent = clone_scope(scope->parent, ctx);
    return cloned;
}

bool rewrite_expr_tree(std::unique_ptr<Expr>& expr,
                       ASTCloneContext& ctx,
                       std::string* error_out);
bool rewrite_stmt_tree_in_place_impl(std::unique_ptr<Stmt>& stmt,
                                     ASTCloneContext& ctx,
                                     std::string* error_out);
bool rewrite_decl_tree_in_place_impl(std::unique_ptr<Decl>& decl,
                                     ASTCloneContext& ctx,
                                     std::string* error_out);

template <typename ExprT>
bool rewrite_expr_tree(std::unique_ptr<ExprT>& expr,
                       ASTCloneContext& ctx,
                       std::string* error_out) {
    static_assert(std::is_base_of_v<Expr, ExprT>);
    if (!expr) {
        return true;
    }
    std::unique_ptr<Expr> erased(expr.release());
    bool ok = rewrite_expr_tree(erased, ctx, error_out);
    if (!ok) {
        return false;
    }
    expr.reset(static_cast<ExprT*>(erased.release()));
    return true;
}

template <typename ExprPtrVec>
bool rewrite_expr_vector(ExprPtrVec& exprs,
                         ASTCloneContext& ctx,
                         std::string* error_out) {
    ExprPtrVec rewritten_exprs;
    rewritten_exprs.reserve(exprs.size());
    for (auto& expr : exprs) {
        if (!expr) {
            rewritten_exprs.push_back(nullptr);
            continue;
        }
        if (auto* pack = dyn_cast<PackExpansionExpr>(expr.get())) {
            if (!ctx.expand_pack_expansion) {
                return set_expr_error(
                    error_out,
                    "pack expansion requires template specialization context");
            }
            std::vector<std::unique_ptr<Expr>> expanded_exprs;
            if (!ctx.expand_pack_expansion(
                    pack->pattern.get(),
                    expanded_exprs,
                    error_out)) {
                return false;
            }
            for (auto& expanded_expr : expanded_exprs) {
                rewritten_exprs.push_back(std::move(expanded_expr));
            }
            continue;
        }
        if (!rewrite_expr_tree(expr, ctx, error_out)) {
            return false;
        }
        rewritten_exprs.push_back(std::move(expr));
    }
    exprs = std::move(rewritten_exprs);
    return true;
}

template <typename DeclPtrVec>
bool rewrite_decl_vector(DeclPtrVec& decls,
                         ASTCloneContext& ctx,
                         std::string* error_out) {
    for (auto& decl : decls) {
        if (decl && !rewrite_decl_tree_in_place_impl(decl, ctx, error_out)) {
            return false;
        }
    }
    return true;
}

bool rewrite_call_argument_vector(std::vector<std::unique_ptr<Expr>>& args,
                                  ASTCloneContext& ctx,
                                  std::string* error_out) {
    return rewrite_expr_vector(args, ctx, error_out);
}

bool rewrite_init_element_vector(std::vector<InitElement>& elements,
                                 ASTCloneContext& ctx,
                                 std::string* error_out) {
    std::vector<InitElement> rewritten_elements;
    rewritten_elements.reserve(elements.size());
    for (auto& element : elements) {
        for (auto& designator : element.designators) {
            if ((designator.index &&
                 !rewrite_expr_tree(designator.index, ctx, error_out)) ||
                (designator.range_end &&
                 !rewrite_expr_tree(designator.range_end, ctx, error_out))) {
                return false;
            }
        }
        if (!element.value) {
            rewritten_elements.push_back(std::move(element));
            continue;
        }
        if (auto* pack = dyn_cast<PackExpansionExpr>(element.value.get())) {
            if (!ctx.expand_pack_expansion) {
                return set_expr_error(
                    error_out,
                    "pack expansion requires template specialization context");
            }
            if (!element.designators.empty()) {
                return set_expr_error(
                    error_out,
                    "designated initializer pack expansion is not supported");
            }
            std::vector<std::unique_ptr<Expr>> expanded_values;
            if (!ctx.expand_pack_expansion(
                    pack->pattern.get(),
                    expanded_values,
                    error_out)) {
                return false;
            }
            for (auto& expanded_value : expanded_values) {
                InitElement expanded_element;
                expanded_element.value = std::move(expanded_value);
                expanded_element.loc = element.loc;
                rewritten_elements.push_back(std::move(expanded_element));
            }
            continue;
        }
        if (!rewrite_expr_tree(element.value, ctx, error_out)) {
            return false;
        }
        rewritten_elements.push_back(std::move(element));
    }
    elements = std::move(rewritten_elements);
    return true;
}

bool rewrite_init_action_vector(std::vector<InitAction>& actions,
                                ASTCloneContext& ctx,
                                std::string* error_out) {
    std::vector<InitAction> rewritten_actions;
    rewritten_actions.reserve(actions.size());
    for (auto& action : actions) {
        if (!action.value) {
            rewritten_actions.push_back(std::move(action));
            continue;
        }
        if (auto* pack = dyn_cast<PackExpansionExpr>(action.value.get())) {
            if (!ctx.expand_pack_expansion) {
                return set_expr_error(
                    error_out,
                    "pack expansion requires template specialization context");
            }
            if (action.paths.size() != 1 || action.paths.front().empty()) {
                return set_expr_error(
                    error_out,
                    "processed initializer pack expansion is only supported for single target paths");
            }
            std::vector<std::unique_ptr<Expr>> expanded_values;
            if (!ctx.expand_pack_expansion(
                    pack->pattern.get(),
                    expanded_values,
                    error_out)) {
                return false;
            }
            const auto base_path = action.paths.front();
            const size_t start_index = base_path.back();
            for (size_t idx = 0; idx < expanded_values.size(); ++idx) {
                InitAction expanded_action;
                auto path = base_path;
                path.back() = start_index + idx;
                expanded_action.paths.push_back(std::move(path));
                expanded_action.value = std::shared_ptr<Expr>(
                    expanded_values[idx].release());
                expanded_action.loc = action.loc;
                rewritten_actions.push_back(std::move(expanded_action));
            }
            continue;
        }

        auto rewritten_value = clone_expr_with_substitution(
            action.value.get(),
            ctx,
            error_out);
        if (!rewritten_value) {
            return false;
        }
        action.value = std::shared_ptr<Expr>(rewritten_value.release());
        rewritten_actions.push_back(std::move(action));
    }
    actions = std::move(rewritten_actions);
    return true;
}

bool rewrite_init_mapping_map(std::map<size_t, std::shared_ptr<Expr>>& mappings,
                              ASTCloneContext& ctx,
                              std::string* error_out) {
    std::map<size_t, std::shared_ptr<Expr>> rewritten_mappings;
    for (auto& [index, mapped_expr] : mappings) {
        if (!mapped_expr) {
            rewritten_mappings[index] = nullptr;
            continue;
        }
        if (auto* pack = dyn_cast<PackExpansionExpr>(mapped_expr.get())) {
            if (!ctx.expand_pack_expansion) {
                return set_expr_error(
                    error_out,
                    "pack expansion requires template specialization context");
            }
            std::vector<std::unique_ptr<Expr>> expanded_values;
            if (!ctx.expand_pack_expansion(
                    pack->pattern.get(),
                    expanded_values,
                    error_out)) {
                return false;
            }
            for (size_t idx = 0; idx < expanded_values.size(); ++idx) {
                rewritten_mappings[index + idx] =
                    std::shared_ptr<Expr>(expanded_values[idx].release());
            }
            continue;
        }

        auto rewritten_mapping = clone_expr_with_substitution(
            mapped_expr.get(),
            ctx,
            error_out);
        if (!rewritten_mapping) {
            return false;
        }
        rewritten_mappings[index] =
            std::shared_ptr<Expr>(rewritten_mapping.release());
    }
    mappings = std::move(rewritten_mappings);
    return true;
}

bool rewrite_expr_tree(std::unique_ptr<Expr>& expr,
                       ASTCloneContext& ctx,
                       std::string* error_out) {
    if (!expr) {
        return true;
    }
    if (ctx.rewrite_var_ref) {
        if (auto* var_ref = dyn_cast<VarRef>(expr.get())) {
            auto replacement = ctx.rewrite_var_ref(var_ref, error_out);
            if (!replacement && error_out && !error_out->empty()) {
                return false;
            }
            if (replacement) {
                expr = std::move(replacement);
            }
        }
    }

    bool ok = [&]() -> bool {
    switch (expr->get_kind()) {
        case StmtKind::IntegerLiteral: {
            auto* literal = static_cast<IntegerLiteral*>(expr.get());
            literal->ctype = rewrite_type(literal->ctype, ctx);
            return true;
        }
        case StmtKind::FloatingLiteral: {
            auto* literal = static_cast<FloatingLiteral*>(expr.get());
            literal->ctype = rewrite_type(literal->ctype, ctx);
            return true;
        }
        case StmtKind::CharacterLiteral: {
            auto* literal = static_cast<CharacterLiteral*>(expr.get());
            literal->ctype = rewrite_type(literal->ctype, ctx);
            return true;
        }
        case StmtKind::StringLiteral: {
            auto* literal = static_cast<StringLiteral*>(expr.get());
            literal->ctype = rewrite_type(literal->ctype, ctx);
            return true;
        }
        case StmtKind::PredefinedExpr: {
            auto* predefined = static_cast<PredefinedExpr*>(expr.get());
            predefined->ctype = rewrite_type(predefined->ctype, ctx);
            return true;
        }
        case StmtKind::CppThisExpr: {
            auto* this_expr = static_cast<CppThisExpr*>(expr.get());
            this_expr->this_type = rewrite_type(this_expr->this_type, ctx);
            return true;
        }
        case StmtKind::VarRef:
        case StmtKind::QualifiedVarRef: {
            auto* var_ref = static_cast<VarRef*>(expr.get());
            var_ref->symref = remap_symbol(var_ref->symref, ctx);
            if (auto* qualified_info = var_ref->get_cpp_qualified_info()) {
                qualified_info->qualifier_type =
                    rewrite_type(qualified_info->qualifier_type, ctx);
            }
            return true;
        }
        case StmtKind::UnresolvedLookupExpr: {
            auto* lookup = static_cast<UnresolvedLookupExpr*>(expr.get());
            lookup->qualifier.qualifier_type =
                rewrite_type(lookup->qualifier.qualifier_type, ctx);
            if (!rewrite_optional_template_arguments(
                    lookup->explicit_template_arguments,
                    ctx,
                    error_out)) {
                return false;
            }
            lookup->ctype = rewrite_type(lookup->ctype, ctx);
            return true;
        }
        case StmtKind::LabelAddressExpr: {
            auto* label = static_cast<LabelAddressExpr*>(expr.get());
            label->ctype = rewrite_type(label->ctype, ctx);
            return true;
        }
        case StmtKind::FuncCall: {
            auto* call = static_cast<FuncCall*>(expr.get());
            if (call->func && !rewrite_expr_tree(call->func, ctx, error_out)) {
                return false;
            }
            if (!rewrite_call_argument_vector(call->args, ctx, error_out)) {
                return false;
            }
            call->ctype = rewrite_type(call->ctype, ctx);
            return true;
        }
        case StmtKind::DependentCallExpr: {
            auto* call = static_cast<DependentCallExpr*>(expr.get());
            if (call->callee &&
                !rewrite_expr_tree(call->callee, ctx, error_out)) {
                return false;
            }
            if (!rewrite_call_argument_vector(call->args, ctx, error_out)) {
                return false;
            }
            call->ctype = rewrite_type(call->ctype, ctx);
            call->known_function_type =
                rewrite_type(call->known_function_type, ctx);
            return true;
        }
        case StmtKind::DependentArraySubscriptExpr: {
            auto* subscript =
                static_cast<DependentArraySubscriptExpr*>(expr.get());
            if (subscript->array &&
                !rewrite_expr_tree(subscript->array, ctx, error_out)) {
                return false;
            }
            if (subscript->index &&
                !rewrite_expr_tree(subscript->index, ctx, error_out)) {
                return false;
            }
            subscript->ctype = rewrite_type(subscript->ctype, ctx);
            return true;
        }
        case StmtKind::DependentUnaryExpr: {
            auto* unary = static_cast<DependentUnaryExpr*>(expr.get());
            if (unary->operand &&
                !rewrite_expr_tree(unary->operand, ctx, error_out)) {
                return false;
            }
            unary->ctype = rewrite_type(unary->ctype, ctx);
            return true;
        }
        case StmtKind::DependentBinaryExpr: {
            auto* binary = static_cast<DependentBinaryExpr*>(expr.get());
            if (binary->left &&
                !rewrite_expr_tree(binary->left, ctx, error_out)) {
                return false;
            }
            if (binary->right &&
                !rewrite_expr_tree(binary->right, ctx, error_out)) {
                return false;
            }
            binary->ctype = rewrite_type(binary->ctype, ctx);
            return true;
        }
        case StmtKind::DependentMemberPointerAccessExpr: {
            auto* access =
                static_cast<DependentMemberPointerAccessExpr*>(expr.get());
            if (access->base &&
                !rewrite_expr_tree(access->base, ctx, error_out)) {
                return false;
            }
            if (access->member_pointer &&
                !rewrite_expr_tree(access->member_pointer, ctx, error_out)) {
                return false;
            }
            access->ctype = rewrite_type(access->ctype, ctx);
            return true;
        }
        case StmtKind::PackExpansionExpr: {
            auto* pack = static_cast<PackExpansionExpr*>(expr.get());
            if (pack->pattern &&
                !rewrite_expr_tree(pack->pattern, ctx, error_out)) {
                return false;
            }
            return true;
        }
        case StmtKind::FoldExpr: {
            auto* fold = static_cast<FoldExpr*>(expr.get());
            if ((fold->pattern &&
                 !rewrite_expr_tree(fold->pattern, ctx, error_out)) ||
                (fold->init &&
                 !rewrite_expr_tree(fold->init, ctx, error_out))) {
                return false;
            }
            fold->result_type = rewrite_type(fold->result_type, ctx);
            return true;
        }
        case StmtKind::CppMemberCallExpr: {
            auto* member_call = static_cast<CppMemberCallExpr*>(expr.get());
            if (member_call->lowered_call &&
                !rewrite_expr_tree(member_call->lowered_call, ctx, error_out)) {
                return false;
            }
            member_call->ctype = rewrite_type(member_call->ctype, ctx);
            return true;
        }
        case StmtKind::CppConstructExpr: {
            auto* construct = static_cast<CppConstructExpr*>(expr.get());
            if (!rewrite_expr_vector(construct->args, ctx, error_out)) {
                return false;
            }
            construct->ctor_sym = remap_symbol(construct->ctor_sym, ctx);
            construct->ctype = rewrite_type(construct->ctype, ctx);
            return true;
        }
        case StmtKind::CppThrowExpr: {
            auto* throw_expr = static_cast<CppThrowExpr*>(expr.get());
            if (throw_expr->thrown_expr &&
                !rewrite_expr_tree(throw_expr->thrown_expr, ctx, error_out)) {
                return false;
            }
            throw_expr->ctype = rewrite_type(throw_expr->ctype, ctx);
            return true;
        }
        case StmtKind::CppNewExpr: {
            auto* new_expr = static_cast<CppNewExpr*>(expr.get());
            if (!rewrite_expr_vector(new_expr->placement_args, ctx, error_out)) {
                return false;
            }
            if (new_expr->initializer &&
                !rewrite_expr_tree(new_expr->initializer, ctx, error_out)) {
                return false;
            }
            if (!rewrite_expr_vector(new_expr->constructor_args, ctx, error_out)) {
                return false;
            }
            new_expr->allocated_type = rewrite_type(new_expr->allocated_type, ctx);
            new_expr->result_type = rewrite_type(new_expr->result_type, ctx);
            new_expr->allocator_sym = remap_symbol(new_expr->allocator_sym, ctx);
            new_expr->deallocator_sym = remap_symbol(new_expr->deallocator_sym, ctx);
            new_expr->ctor_sym = remap_symbol(new_expr->ctor_sym, ctx);
            return true;
        }
        case StmtKind::CppDeleteExpr: {
            auto* delete_expr = static_cast<CppDeleteExpr*>(expr.get());
            if (delete_expr->operand &&
                !rewrite_expr_tree(delete_expr->operand, ctx, error_out)) {
                return false;
            }
            delete_expr->ctype = rewrite_type(delete_expr->ctype, ctx);
            delete_expr->destroyed_type =
                rewrite_type(delete_expr->destroyed_type, ctx);
            delete_expr->deallocator_sym =
                remap_symbol(delete_expr->deallocator_sym, ctx);
            delete_expr->destructor_sym =
                remap_symbol(delete_expr->destructor_sym, ctx);
            return true;
        }
        case StmtKind::BlockByrefAccessExpr: {
            auto* byref_expr = static_cast<BlockByrefAccessExpr*>(expr.get());
            if (byref_expr->cell_expr &&
                !rewrite_expr_tree(byref_expr->cell_expr, ctx, error_out)) {
                return false;
            }
            byref_expr->symbol = remap_symbol(byref_expr->symbol, ctx);
            byref_expr->ctype = rewrite_type(byref_expr->ctype, ctx);
            return true;
        }
        case StmtKind::BlockExpr: {
            auto* block = static_cast<BlockExpr*>(expr.get());
            block->block_type = rewrite_type(block->block_type, ctx);
            block->explicit_return_type =
                rewrite_type(block->explicit_return_type, ctx);
            if (!rewrite_decl_vector(
                    block->parameters,
                    ctx,
                    error_out)) {
                return false;
            }
            if (block->body) {
                std::unique_ptr<Stmt> body_stmt(block->body.release());
                if (!rewrite_stmt_tree_in_place_impl(
                        body_stmt,
                        ctx,
                        error_out)) {
                    return false;
                }
                block->body.reset(
                    static_cast<CompoundStmt*>(body_stmt.release()));
            }
            if (ctx.finalize_block_expr &&
                !ctx.finalize_block_expr(*block, error_out)) {
                return false;
            }
            return true;
        }
        case StmtKind::CppLambdaExpr: {
            auto* lambda = static_cast<CppLambdaExpr*>(expr.get());
            lambda->written_call_operator_type =
                rewrite_type(lambda->written_call_operator_type, ctx);
            lambda->explicit_return_type =
                rewrite_type(lambda->explicit_return_type, ctx);
            lambda->semantic_info.lexical_this_context.this_type =
                rewrite_type(
                    lambda->semantic_info.lexical_this_context.this_type,
                    ctx);
            for (auto& capture : lambda->closure_info.captures) {
                capture.symbol = remap_symbol(capture.symbol, ctx);
                if (!capture.initializer) {
                    continue;
                }
                auto rewritten_initializer = clone_expr_with_substitution(
                    capture.initializer.get(),
                    ctx,
                    error_out);
                if (!rewritten_initializer) {
                    return false;
                }
                capture.initializer = std::shared_ptr<Expr>(
                    rewritten_initializer.release());
            }
            if (!rewrite_decl_vector(
                    lambda->parameters,
                    ctx,
                    error_out)) {
                return false;
            }
            if (lambda->body) {
                std::unique_ptr<Stmt> body_stmt(lambda->body.release());
                if (!rewrite_stmt_tree_in_place_impl(
                        body_stmt,
                        ctx,
                        error_out)) {
                    return false;
                }
                lambda->body.reset(
                    static_cast<CompoundStmt*>(body_stmt.release()));
            }
            if (ctx.finalize_lambda_expr &&
                !ctx.finalize_lambda_expr(*lambda, error_out)) {
                return false;
            }
            return true;
        }
        case StmtKind::CppTypeIdExpr: {
            auto* typeid_expr = static_cast<CppTypeIdExpr*>(expr.get());
            if (typeid_expr->is_type_operand) {
                typeid_expr->type_operand =
                    rewrite_type(typeid_expr->type_operand, ctx);
            } else if (typeid_expr->expr_operand &&
                       !rewrite_expr_tree(typeid_expr->expr_operand, ctx, error_out)) {
                return false;
            }
            typeid_expr->ctype = rewrite_type(typeid_expr->ctype, ctx);
            return true;
        }
        case StmtKind::CppDynamicCastExpr: {
            auto* cast_expr = static_cast<CppDynamicCastExpr*>(expr.get());
            if (cast_expr->expr &&
                !rewrite_expr_tree(cast_expr->expr, ctx, error_out)) {
                return false;
            }
            cast_expr->target_type = rewrite_type(cast_expr->target_type, ctx);
            return true;
        }
        case StmtKind::CondExpr: {
            auto* cond = static_cast<CondExpr*>(expr.get());
            if (cond->condition &&
                !rewrite_expr_tree(cond->condition, ctx, error_out)) {
                return false;
            }
            if (cond->true_expr &&
                !rewrite_expr_tree(cond->true_expr, ctx, error_out)) {
                return false;
            }
            if (cond->false_expr &&
                !rewrite_expr_tree(cond->false_expr, ctx, error_out)) {
                return false;
            }
            cond->type = rewrite_type(cond->type, ctx);
            return true;
        }
        case StmtKind::UnaryOperation: {
            auto* unary = static_cast<UnaryOperation*>(expr.get());
            if (unary->exp && !rewrite_expr_tree(unary->exp, ctx, error_out)) {
                return false;
            }
            unary->ctype = rewrite_type(unary->ctype, ctx);
            return true;
        }
        case StmtKind::BinaryOperation: {
            auto* binary = static_cast<BinaryOperation*>(expr.get());
            if (binary->left &&
                !rewrite_expr_tree(binary->left, ctx, error_out)) {
                return false;
            }
            if (binary->right &&
                !rewrite_expr_tree(binary->right, ctx, error_out)) {
                return false;
            }
            binary->ctype = rewrite_type(binary->ctype, ctx);
            return true;
        }
        case StmtKind::CompoundAssignOperation: {
            auto* compound = static_cast<CompoundAssignOperation*>(expr.get());
            if (compound->left &&
                !rewrite_expr_tree(compound->left, ctx, error_out)) {
                return false;
            }
            if (compound->right &&
                !rewrite_expr_tree(compound->right, ctx, error_out)) {
                return false;
            }
            compound->ctype = rewrite_type(compound->ctype, ctx);
            return true;
        }
        case StmtKind::ImplicitCast: {
            auto* cast = static_cast<ImplicitCast*>(expr.get());
            if (cast->expr && !rewrite_expr_tree(cast->expr, ctx, error_out)) {
                return false;
            }
            cast->ctype = rewrite_type(cast->ctype, ctx);
            return true;
        }
        case StmtKind::ExplicitCast: {
            auto* cast = static_cast<ExplicitCast*>(expr.get());
            if (cast->expr && !rewrite_expr_tree(cast->expr, ctx, error_out)) {
                return false;
            }
            cast->ctype = rewrite_type(cast->ctype, ctx);
            return true;
        }
        case StmtKind::ArraySubscriptExpr: {
            auto* subscript = static_cast<ArraySubscriptExpr*>(expr.get());
            if (subscript->array &&
                !rewrite_expr_tree(subscript->array, ctx, error_out)) {
                return false;
            }
            if (subscript->index &&
                !rewrite_expr_tree(subscript->index, ctx, error_out)) {
                return false;
            }
            subscript->ctype = rewrite_type(subscript->ctype, ctx);
            return true;
        }
        case StmtKind::MemberExpr: {
            auto* member = static_cast<MemberExpr*>(expr.get());
            if (member->base && !rewrite_expr_tree(member->base, ctx, error_out)) {
                return false;
            }
            member->member_type = rewrite_type(member->member_type, ctx);
            if (ctx.rewrite_member_expr &&
                !ctx.rewrite_member_expr(member, error_out)) {
                return false;
            }
            return true;
        }
        case StmtKind::UnresolvedMemberExpr: {
            auto* member = static_cast<UnresolvedMemberExpr*>(expr.get());
            if (member->base &&
                !rewrite_expr_tree(member->base, ctx, error_out)) {
                return false;
            }
            member->member_type = rewrite_type(member->member_type, ctx);
            if (!rewrite_optional_template_arguments(
                    member->explicit_template_arguments,
                    ctx,
                    error_out)) {
                return false;
            }
            return true;
        }
        case StmtKind::MemberPointerLiteralExpr: {
            auto* literal = static_cast<MemberPointerLiteralExpr*>(expr.get());
            literal->ctype = rewrite_type(literal->ctype, ctx);
            literal->method_symbol = remap_symbol(literal->method_symbol, ctx);
            return true;
        }
        case StmtKind::MemberPointerAccessExpr: {
            auto* access = static_cast<MemberPointerAccessExpr*>(expr.get());
            if (access->base && !rewrite_expr_tree(access->base, ctx, error_out)) {
                return false;
            }
            if (access->member_pointer &&
                !rewrite_expr_tree(access->member_pointer, ctx, error_out)) {
                return false;
            }
            access->result_type = rewrite_type(access->result_type, ctx);
            return true;
        }
        case StmtKind::InitListExpr: {
            auto* init_list = static_cast<InitListExpr*>(expr.get());
            if (!rewrite_init_element_vector(
                    init_list->elements,
                    ctx,
                    error_out)) {
                return false;
            }
            if (!rewrite_init_action_vector(
                    init_list->actions,
                    ctx,
                    error_out)) {
                return false;
            }
            if (!rewrite_init_mapping_map(
                    init_list->mappings,
                    ctx,
                    error_out)) {
                return false;
            }
            init_list->type = rewrite_type(init_list->type, ctx);
            return true;
        }
        case StmtKind::CompoundLiteralExpr: {
            auto* compound_literal = static_cast<CompoundLiteralExpr*>(expr.get());
            if (compound_literal->init &&
                !rewrite_expr_tree(compound_literal->init, ctx, error_out)) {
                return false;
            }
            compound_literal->type = rewrite_type(compound_literal->type, ctx);
            return true;
        }
        case StmtKind::SizeOfExpr: {
            auto* sizeof_expr = static_cast<SizeOfExpr*>(expr.get());
            if (sizeof_expr->expr_operand &&
                !rewrite_expr_tree(sizeof_expr->expr_operand, ctx, error_out)) {
                return false;
            }
            sizeof_expr->type_operand =
                rewrite_type(sizeof_expr->type_operand, ctx);
            sizeof_expr->result_type =
                rewrite_type(sizeof_expr->result_type, ctx);
            return true;
        }
        case StmtKind::SizeOfPackExpr: {
            auto* sizeof_pack = static_cast<SizeOfPackExpr*>(expr.get());
            if (ctx.lookup_pack_size) {
                auto pack_size = ctx.lookup_pack_size(sizeof_pack, error_out);
                if (error_out && !error_out->empty()) {
                    return false;
                }
                if (pack_size.has_value()) {
                    expr = make_pack_size_integer_literal(
                        *pack_size,
                        ctx.ast_ctx,
                        sizeof_pack->location);
                    return rewrite_expr_tree(expr, ctx, error_out);
                }
            }
            sizeof_pack->result_type =
                rewrite_type(sizeof_pack->result_type, ctx);
            return true;
        }
        case StmtKind::StmtExpr:
            return set_expr_error(
                error_out,
                "statement-expression cloning is not supported");
        case StmtKind::VaArgExpr: {
            auto* va_arg = static_cast<VaArgExpr*>(expr.get());
            if (va_arg->va_list_expr &&
                !rewrite_expr_tree(va_arg->va_list_expr, ctx, error_out)) {
                return false;
            }
            va_arg->arg_type = rewrite_type(va_arg->arg_type, ctx);
            return true;
        }
        case StmtKind::VaStartExpr: {
            auto* va_start = static_cast<VaStartExpr*>(expr.get());
            if (va_start->va_list_expr &&
                !rewrite_expr_tree(va_start->va_list_expr, ctx, error_out)) {
                return false;
            }
            if (va_start->last_param &&
                !rewrite_expr_tree(va_start->last_param, ctx, error_out)) {
                return false;
            }
            return true;
        }
        case StmtKind::VaEndExpr: {
            auto* va_end = static_cast<VaEndExpr*>(expr.get());
            return !va_end->va_list_expr ||
                rewrite_expr_tree(va_end->va_list_expr, ctx, error_out);
        }
        case StmtKind::VaCopyExpr: {
            auto* va_copy = static_cast<VaCopyExpr*>(expr.get());
            if (va_copy->dest &&
                !rewrite_expr_tree(va_copy->dest, ctx, error_out)) {
                return false;
            }
            if (va_copy->src &&
                !rewrite_expr_tree(va_copy->src, ctx, error_out)) {
                return false;
            }
            return true;
        }
        case StmtKind::AlignOfExpr: {
            auto* alignof_expr = static_cast<AlignOfExpr*>(expr.get());
            if (alignof_expr->expr_operand &&
                !rewrite_expr_tree(alignof_expr->expr_operand, ctx, error_out)) {
                return false;
            }
            alignof_expr->type_operand =
                rewrite_type(alignof_expr->type_operand, ctx);
            alignof_expr->result_type =
                rewrite_type(alignof_expr->result_type, ctx);
            return true;
        }
        case StmtKind::GenericExpr: {
            auto* generic_expr = static_cast<GenericExpr*>(expr.get());
            if (generic_expr->controlling_expr &&
                !rewrite_expr_tree(generic_expr->controlling_expr, ctx, error_out)) {
                return false;
            }
            for (auto& assoc : generic_expr->associations) {
                assoc.type = rewrite_type(assoc.type, ctx);
                if (assoc.expr &&
                    !rewrite_expr_tree(assoc.expr, ctx, error_out)) {
                    return false;
                }
            }
            generic_expr->result_type =
                rewrite_type(generic_expr->result_type, ctx);
            return true;
        }
        case StmtKind::OffsetOfExpr: {
            auto* offsetof_expr = static_cast<OffsetOfExpr*>(expr.get());
            offsetof_expr->type_operand =
                rewrite_type(offsetof_expr->type_operand, ctx);
            offsetof_expr->result_type =
                rewrite_type(offsetof_expr->result_type, ctx);
            return true;
        }
        case StmtKind::BuiltinCallExpr: {
            auto* builtin = static_cast<BuiltinCallExpr*>(expr.get());
            if (!rewrite_expr_vector(builtin->args, ctx, error_out)) {
                return false;
            }
            for (auto& type_arg : builtin->type_args) {
                type_arg = rewrite_type(type_arg, ctx);
            }
            builtin->result_type = rewrite_type(builtin->result_type, ctx);
            return true;
        }
        case StmtKind::ConceptSpecializationExpr: {
            auto* concept_expr =
                static_cast<ConceptSpecializationExpr*>(expr.get());
            concept_expr->arguments = rewrite_template_arguments(
                concept_expr->arguments,
                ctx,
                error_out);
            concept_expr->result_type =
                rewrite_type(concept_expr->result_type, ctx);
            concept_expr->satisfaction.reset();
            return true;
        }
        case StmtKind::RequiresExpr: {
            auto* requires_expr = static_cast<RequiresExpr*>(expr.get());
            for (auto& parameter : requires_expr->parameters) {
                if (!rewrite_param_decl_in_place(
                        parameter.get(),
                        ctx,
                        error_out)) {
                    return false;
                }
            }
            if (!rewrite_constraint_requirements_in_place(
                    requires_expr->requirements,
                    ctx,
                    error_out)) {
                return false;
            }
            requires_expr->result_type =
                rewrite_type(requires_expr->result_type, ctx);
            requires_expr->satisfaction.reset();
            return true;
        }
        case StmtKind::ErrorExpr:
            return true;
        default:
            return set_expr_error(
                error_out,
                "unsupported expression substitution kind " +
                    std::to_string(static_cast<int>(expr->get_kind())));
    }
    }();
    if (!ok) {
        return false;
    }
    if (ctx.rewrite_expr && !ctx.rewrite_expr(expr, error_out)) {
        return false;
    }
    return true;
}

bool rewrite_decl_tree_in_place_impl(std::unique_ptr<Decl>& decl,
                                     ASTCloneContext& ctx,
                                     std::string* error_out) {
    if (!decl) {
        return true;
    }

    switch (decl->get_kind()) {
        case DeclKind::NopDecl:
        case DeclKind::NamespaceDecl:
        case DeclKind::ErrorDecl:
            return true;
        case DeclKind::FieldDecl: {
            auto* field_decl = static_cast<FieldDecl*>(decl.get());
            field_decl->type = rewrite_type(field_decl->type, ctx);
            if (ctx.ast_ctx && ctx.ast_ctx->has_attrs(field_decl->node_id) &&
                !rewrite_attribute_list_in_place(
                    ctx.ast_ctx->get_attrs_mut(field_decl->node_id),
                    ctx,
                    error_out)) {
                return false;
            }
            return true;
        }
        case DeclKind::CppAccessSpecDecl:
            return true;
        case DeclKind::CppRecordDecl: {
            auto* record_decl = static_cast<CppRecordDecl*>(decl.get());
            for (auto& base : record_decl->bases) {
                base.type = rewrite_type(base.type, ctx);
            }
            if (!rewrite_decl_vector(record_decl->members, ctx, error_out)) {
                return false;
            }
            if (ctx.ast_ctx && ctx.ast_ctx->has_attrs(record_decl->node_id) &&
                !rewrite_attribute_list_in_place(
                    ctx.ast_ctx->get_attrs_mut(record_decl->node_id),
                    ctx,
                    error_out)) {
                return false;
            }
            return true;
        }
        case DeclKind::TypedefDecl: {
            auto* typedef_decl = static_cast<TypedefDecl*>(decl.get());
            typedef_decl->type = rewrite_type(typedef_decl->type, ctx);
            typedef_decl->sym = remap_symbol(typedef_decl->sym, ctx);
            if (typedef_decl->sym) {
                typedef_decl->sym->type = rewrite_type(typedef_decl->sym->type, ctx);
            }
            return true;
        }
        case DeclKind::VariableDecl: {
            auto* variable = static_cast<VariableDecl*>(decl.get());
            variable->type = rewrite_type(variable->type, ctx);
            variable->original_type = rewrite_type(variable->original_type, ctx);
            variable->sym = remap_symbol(variable->sym, ctx);
            if (variable->sym) {
                variable->sym->type = rewrite_type(variable->sym->type, ctx);
            }
            if (variable->init &&
                !rewrite_expr_tree(variable->init, ctx, error_out)) {
                return false;
            }
            return true;
        }
        case DeclKind::ParamDecl: {
            auto* param = static_cast<ParamDecl*>(decl.get());
            param->type = rewrite_type(param->type, ctx);
            param->sym = remap_symbol(param->sym, ctx);
            if (param->sym) {
                param->sym->type = rewrite_type(param->sym->type, ctx);
            }
            param->original_type =
                rewrite_type(QualType(param->original_type), ctx).get_shared();
            if (const Expr* default_arg = get_param_decl_default_argument(param)) {
                auto rewritten_default = clone_expr_with_substitution(
                    default_arg,
                    ctx,
                    error_out);
                if (!rewritten_default) {
                    return false;
                }
                set_param_decl_default_argument(
                    param,
                    std::move(rewritten_default));
            }
            return true;
        }
        case DeclKind::StaticAssertDecl: {
            auto* static_assert_decl = static_cast<StaticAssertDecl*>(decl.get());
            if (static_assert_decl->condition &&
                !rewrite_expr_tree(
                    static_assert_decl->condition,
                    ctx,
                    error_out)) {
                return false;
            }
            return true;
        }
        default:
            return set_expr_error(
                error_out,
                "unsupported declaration rewrite kind " +
                    std::to_string(static_cast<int>(decl->get_kind())));
    }
}

bool rewrite_stmt_tree_in_place_impl(std::unique_ptr<Stmt>& stmt,
                                     ASTCloneContext& ctx,
                                     std::string* error_out) {
    if (!stmt) {
        return true;
    }

    if (Expr::classof(stmt.get())) {
        std::unique_ptr<Expr> expr(static_cast<Expr*>(stmt.release()));
        if (!rewrite_expr_tree(expr, ctx, error_out)) {
            return false;
        }
        stmt.reset(expr.release());
        return true;
    }

    switch (stmt->get_kind()) {
        case StmtKind::CompoundStmt: {
            auto* compound = static_cast<CompoundStmt*>(stmt.get());
            for (auto& child : compound->statements) {
                if (child &&
                    !rewrite_stmt_tree_in_place_impl(child, ctx, error_out)) {
                    return false;
                }
            }
            return true;
        }
        case StmtKind::Decl2Stmt: {
            auto* decl_stmt = static_cast<Decl2Stmt*>(stmt.get());
            return rewrite_decl_vector(decl_stmt->decls, ctx, error_out);
        }
        case StmtKind::ReturnStmt: {
            auto* ret = static_cast<ReturnStmt*>(stmt.get());
            return !ret->expression ||
                   rewrite_expr_tree(ret->expression, ctx, error_out);
        }
        case StmtKind::IfStmt: {
            auto* if_stmt = static_cast<IfStmt*>(stmt.get());
            return (!if_stmt->condition ||
                    rewrite_expr_tree(if_stmt->condition, ctx, error_out)) &&
                   (!if_stmt->then_stmt ||
                    rewrite_stmt_tree_in_place_impl(
                        if_stmt->then_stmt,
                        ctx,
                        error_out)) &&
                   (!if_stmt->else_stmt ||
                    rewrite_stmt_tree_in_place_impl(
                        if_stmt->else_stmt,
                        ctx,
                        error_out));
        }
        case StmtKind::CaseStmt: {
            auto* case_stmt = static_cast<CaseStmt*>(stmt.get());
            return (!case_stmt->const_expr ||
                    rewrite_expr_tree(case_stmt->const_expr, ctx, error_out)) &&
                   (!case_stmt->range_end ||
                    rewrite_expr_tree(case_stmt->range_end, ctx, error_out)) &&
                   (!case_stmt->stmt ||
                    rewrite_stmt_tree_in_place_impl(
                        case_stmt->stmt,
                        ctx,
                        error_out));
        }
        case StmtKind::DefaultStmt: {
            auto* default_stmt = static_cast<DefaultStmt*>(stmt.get());
            return !default_stmt->stmt ||
                   rewrite_stmt_tree_in_place_impl(
                       default_stmt->stmt,
                       ctx,
                       error_out);
        }
        case StmtKind::LabeledStmt: {
            auto* labeled = static_cast<LabeledStmt*>(stmt.get());
            return !labeled->stmt ||
                   rewrite_stmt_tree_in_place_impl(
                       labeled->stmt,
                       ctx,
                       error_out);
        }
        case StmtKind::GoToStmt:
        case StmtKind::ContinueStmt:
        case StmtKind::BreakStmt:
        case StmtKind::EmptyStmt:
        case StmtKind::ErrorStmt:
            return true;
        case StmtKind::ComputedGotoStmt: {
            auto* goto_stmt = static_cast<ComputedGotoStmt*>(stmt.get());
            return !goto_stmt->target ||
                   rewrite_expr_tree(goto_stmt->target, ctx, error_out);
        }
        case StmtKind::SwitchStmt: {
            auto* switch_stmt = static_cast<SwitchStmt*>(stmt.get());
            return (!switch_stmt->condition ||
                    rewrite_expr_tree(
                        switch_stmt->condition,
                        ctx,
                        error_out)) &&
                   (!switch_stmt->stmt ||
                    rewrite_stmt_tree_in_place_impl(
                        switch_stmt->stmt,
                        ctx,
                        error_out));
        }
        case StmtKind::WhileStmt: {
            auto* while_stmt = static_cast<WhileStmt*>(stmt.get());
            return (!while_stmt->condition ||
                    rewrite_expr_tree(while_stmt->condition, ctx, error_out)) &&
                   (!while_stmt->body_stmt ||
                    rewrite_stmt_tree_in_place_impl(
                        while_stmt->body_stmt,
                        ctx,
                        error_out));
        }
        case StmtKind::DoWhileStmt: {
            auto* while_stmt = static_cast<DoWhileStmt*>(stmt.get());
            return (!while_stmt->condition ||
                    rewrite_expr_tree(while_stmt->condition, ctx, error_out)) &&
                   (!while_stmt->body_stmt ||
                    rewrite_stmt_tree_in_place_impl(
                        while_stmt->body_stmt,
                        ctx,
                        error_out));
        }
        case StmtKind::ForStmt: {
            auto* for_stmt = static_cast<ForStmt*>(stmt.get());
            return (!for_stmt->init ||
                    rewrite_stmt_tree_in_place_impl(
                        for_stmt->init,
                        ctx,
                        error_out)) &&
                   (!for_stmt->cond ||
                    rewrite_expr_tree(for_stmt->cond, ctx, error_out)) &&
                   (!for_stmt->action ||
                    rewrite_expr_tree(for_stmt->action, ctx, error_out)) &&
                   (!for_stmt->body_stmt ||
                    rewrite_stmt_tree_in_place_impl(
                        for_stmt->body_stmt,
                        ctx,
                        error_out));
        }
        case StmtKind::AsmStmt: {
            auto* asm_stmt = static_cast<AsmStmt*>(stmt.get());
            auto rewrite_operand_vec =
                [&](std::vector<AsmOperand>& operands) -> bool {
                    for (auto& operand : operands) {
                        if (operand.expr &&
                            !rewrite_expr_tree(operand.expr, ctx, error_out)) {
                            return false;
                        }
                    }
                    return true;
                };
            return rewrite_operand_vec(asm_stmt->output_operands) &&
                   rewrite_operand_vec(asm_stmt->input_operands);
        }
        case StmtKind::CppTryStmt: {
            auto* try_stmt = static_cast<CppTryStmt*>(stmt.get());
            if (try_stmt->try_block &&
                !rewrite_stmt_tree_in_place_impl(
                    try_stmt->try_block,
                    ctx,
                    error_out)) {
                return false;
            }
            for (auto& handler : try_stmt->handlers) {
                if (handler.handler &&
                    !rewrite_stmt_tree_in_place_impl(
                        handler.handler,
                        ctx,
                        error_out)) {
                    return false;
                }
            }
            return true;
        }
        default:
            return set_expr_error(
                error_out,
                "unsupported statement rewrite kind " +
                    std::to_string(static_cast<int>(stmt->get_kind())));
    }
}

std::unique_ptr<Decl> clone_decl_impl(const Decl* decl,
                                      ASTCloneContext& ctx,
                                      std::string* error_out);

std::unique_ptr<Stmt> clone_stmt_impl(const Stmt* stmt,
                                      ASTCloneContext& ctx,
                                      std::string* error_out) {
    if (!stmt) {
        return nullptr;
    }

    if (Expr::classof(stmt)) {
        auto cloned = clone_expr_with_substitution(
            static_cast<const Expr*>(stmt),
            ctx,
            error_out);
        return std::unique_ptr<Stmt>(cloned.release());
    }

    switch (stmt->get_kind()) {
        case StmtKind::CompoundStmt: {
            const auto* compound = static_cast<const CompoundStmt*>(stmt);
            std::vector<std::unique_ptr<Stmt>> cloned_statements;
            cloned_statements.reserve(compound->statements.size());
            for (const auto& child : compound->statements) {
                auto cloned_child = clone_stmt_impl(child.get(), ctx, error_out);
                if (child && !cloned_child) {
                    return nullptr;
                }
                cloned_statements.push_back(std::move(cloned_child));
            }
            auto result = std::make_unique<CompoundStmt>(
                std::move(cloned_statements),
                clone_scope(compound->scope, ctx),
                compound->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::Decl2Stmt: {
            const auto* decl_stmt = static_cast<const Decl2Stmt*>(stmt);
            std::vector<std::unique_ptr<Decl>> cloned_decls;
            cloned_decls.reserve(decl_stmt->decls.size());
            for (const auto& decl : decl_stmt->decls) {
                auto cloned_decl = clone_decl_impl(decl.get(), ctx, error_out);
                if (decl && !cloned_decl) {
                    return nullptr;
                }
                cloned_decls.push_back(std::move(cloned_decl));
            }
            auto result = std::make_unique<Decl2Stmt>(
                std::move(cloned_decls), decl_stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::ReturnStmt: {
            const auto* ret = static_cast<const ReturnStmt*>(stmt);
            auto expr =
                clone_expr_with_substitution(ret->expression.get(), ctx, error_out);
            if (ret->expression && !expr) {
                return nullptr;
            }
            auto result = std::make_unique<ReturnStmt>(
                std::move(expr), ret->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::IfStmt: {
            const auto* if_stmt = static_cast<const IfStmt*>(stmt);
            auto condition = clone_expr_with_substitution(
                if_stmt->condition.get(), ctx, error_out);
            auto then_stmt = clone_stmt_impl(if_stmt->then_stmt.get(), ctx, error_out);
            auto else_stmt = clone_stmt_impl(if_stmt->else_stmt.get(), ctx, error_out);
            if ((if_stmt->condition && !condition) ||
                (if_stmt->then_stmt && !then_stmt) ||
                (if_stmt->else_stmt && !else_stmt)) {
                return nullptr;
            }
            auto result = std::make_unique<IfStmt>(
                std::move(condition),
                std::move(then_stmt),
                std::move(else_stmt),
                if_stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::CaseStmt: {
            const auto* case_stmt = static_cast<const CaseStmt*>(stmt);
            auto const_expr = clone_expr_with_substitution(
                case_stmt->const_expr.get(), ctx, error_out);
            auto range_end = clone_expr_with_substitution(
                case_stmt->range_end.get(), ctx, error_out);
            auto nested_stmt = clone_stmt_impl(case_stmt->stmt.get(), ctx, error_out);
            if ((case_stmt->const_expr && !const_expr) ||
                (case_stmt->range_end && !range_end) ||
                (case_stmt->stmt && !nested_stmt)) {
                return nullptr;
            }
            std::unique_ptr<CaseStmt> result;
            if (range_end) {
                result = std::make_unique<CaseStmt>(
                    std::move(const_expr),
                    std::move(range_end),
                    std::move(nested_stmt),
                    case_stmt->location);
            } else {
                result = std::make_unique<CaseStmt>(
                    std::move(const_expr),
                    std::move(nested_stmt),
                    case_stmt->location);
            }
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::DefaultStmt: {
            const auto* default_stmt = static_cast<const DefaultStmt*>(stmt);
            auto nested_stmt =
                clone_stmt_impl(default_stmt->stmt.get(), ctx, error_out);
            if (default_stmt->stmt && !nested_stmt) {
                return nullptr;
            }
            auto result = std::make_unique<DefaultStmt>(
                std::move(nested_stmt),
                default_stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::LabeledStmt: {
            const auto* labeled = static_cast<const LabeledStmt*>(stmt);
            auto nested_stmt = clone_stmt_impl(labeled->stmt.get(), ctx, error_out);
            if (labeled->stmt && !nested_stmt) {
                return nullptr;
            }
            auto result = std::make_unique<LabeledStmt>(
                labeled->name,
                std::move(nested_stmt),
                labeled->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::GoToStmt: {
            const auto* goto_stmt = static_cast<const GoToStmt*>(stmt);
            auto result = std::make_unique<GoToStmt>(
                goto_stmt->name,
                goto_stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::ComputedGotoStmt: {
            const auto* goto_stmt = static_cast<const ComputedGotoStmt*>(stmt);
            auto target = clone_expr_with_substitution(
                goto_stmt->target.get(), ctx, error_out);
            if (goto_stmt->target && !target) {
                return nullptr;
            }
            auto result = std::make_unique<ComputedGotoStmt>(
                std::move(target),
                goto_stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::SwitchStmt: {
            const auto* switch_stmt = static_cast<const SwitchStmt*>(stmt);
            auto condition = clone_expr_with_substitution(
                switch_stmt->condition.get(), ctx, error_out);
            auto nested_stmt = clone_stmt_impl(switch_stmt->stmt.get(), ctx, error_out);
            if ((switch_stmt->condition && !condition) ||
                (switch_stmt->stmt && !nested_stmt)) {
                return nullptr;
            }
            auto result = std::make_unique<SwitchStmt>(
                std::move(condition),
                std::move(nested_stmt),
                switch_stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::WhileStmt: {
            const auto* while_stmt = static_cast<const WhileStmt*>(stmt);
            auto condition = clone_expr_with_substitution(
                while_stmt->condition.get(), ctx, error_out);
            auto body_stmt = clone_stmt_impl(while_stmt->body_stmt.get(), ctx, error_out);
            if ((while_stmt->condition && !condition) ||
                (while_stmt->body_stmt && !body_stmt)) {
                return nullptr;
            }
            auto result = std::make_unique<WhileStmt>(
                std::move(condition),
                std::move(body_stmt),
                while_stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::DoWhileStmt: {
            const auto* while_stmt = static_cast<const DoWhileStmt*>(stmt);
            auto condition = clone_expr_with_substitution(
                while_stmt->condition.get(), ctx, error_out);
            auto body_stmt = clone_stmt_impl(while_stmt->body_stmt.get(), ctx, error_out);
            if ((while_stmt->condition && !condition) ||
                (while_stmt->body_stmt && !body_stmt)) {
                return nullptr;
            }
            auto result = std::make_unique<DoWhileStmt>(
                std::move(condition),
                std::move(body_stmt),
                while_stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::ForStmt: {
            const auto* for_stmt = static_cast<const ForStmt*>(stmt);
            auto init = clone_stmt_impl(for_stmt->init.get(), ctx, error_out);
            auto cond = clone_expr_with_substitution(
                for_stmt->cond.get(), ctx, error_out);
            auto action = clone_expr_with_substitution(
                for_stmt->action.get(), ctx, error_out);
            auto body_stmt = clone_stmt_impl(for_stmt->body_stmt.get(), ctx, error_out);
            if ((for_stmt->init && !init) ||
                (for_stmt->cond && !cond) ||
                (for_stmt->action && !action) ||
                (for_stmt->body_stmt && !body_stmt)) {
                return nullptr;
            }
            auto result = std::make_unique<ForStmt>(
                std::move(init),
                std::move(cond),
                std::move(action),
                std::move(body_stmt),
                clone_scope(for_stmt->scope, ctx),
                for_stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::ContinueStmt: {
            auto result = std::make_unique<ContinueStmt>(stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::BreakStmt: {
            auto result = std::make_unique<BreakStmt>(stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::EmptyStmt: {
            auto result = std::make_unique<EmptyStmt>(stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::ErrorStmt: {
            const auto* error_stmt = static_cast<const ErrorStmt*>(stmt);
            auto result = std::make_unique<ErrorStmt>(
                error_stmt->error_message,
                error_stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::AsmStmt: {
            const auto* asm_stmt = static_cast<const AsmStmt*>(stmt);
            auto result = std::make_unique<AsmStmt>(
                asm_stmt->asm_template,
                asm_stmt->is_volatile != 0,
                asm_stmt->is_inline != 0,
                asm_stmt->is_goto != 0,
                asm_stmt->has_colon_syntax != 0,
                asm_stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            auto clone_operand_vec = [&](const std::vector<AsmOperand>& input,
                                         std::vector<AsmOperand>& output) -> bool {
                output.reserve(input.size());
                for (const auto& operand : input) {
                    AsmOperand cloned_operand;
                    cloned_operand.symbolic_name = operand.symbolic_name;
                    cloned_operand.constraint = operand.constraint;
                    cloned_operand.loc = operand.loc;
                    cloned_operand.expr = clone_expr_with_substitution(
                        operand.expr.get(), ctx, error_out);
                    if (operand.expr && !cloned_operand.expr) {
                        return false;
                    }
                    output.push_back(std::move(cloned_operand));
                }
                return true;
            };
            if (!clone_operand_vec(asm_stmt->output_operands, result->output_operands) ||
                !clone_operand_vec(asm_stmt->input_operands, result->input_operands)) {
                return nullptr;
            }
            result->clobbers = asm_stmt->clobbers;
            result->goto_labels = asm_stmt->goto_labels;
            return result;
        }
        case StmtKind::CppTryStmt:
            return fail_stmt_clone(
                error_out,
                "C++ try/catch statement cloning is not supported");
        default:
            return fail_stmt_clone(
                error_out,
                "unsupported statement clone kind " +
                    std::to_string(static_cast<int>(stmt->get_kind())));
    }
}

std::shared_ptr<Symbol> clone_symbol_shallow(const std::shared_ptr<Symbol>& sym,
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
    cloned->uid = sym->uid;
    cloned->asm_label = sym->asm_label;
    cloned->set_language_linkage(sym->get_language_linkage());
    return cloned;
}

std::unique_ptr<Decl> clone_decl_impl(const Decl* decl,
                                      ASTCloneContext& ctx,
                                      std::string* error_out) {
    if (!decl) {
        return nullptr;
    }

    switch (decl->get_kind()) {
        case DeclKind::NopDecl: {
            auto result = std::make_unique<NopDecl>(decl->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            if (!copy_decl_side_tables(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::NamespaceDecl: {
            const auto* namespace_decl = static_cast<const NamespaceDecl*>(decl);
            auto result = std::make_unique<NamespaceDecl>(
                namespace_decl->name,
                std::vector<Decl*>{},
                namespace_decl->semantic_context,
                namespace_decl->is_anonymous,
                namespace_decl->is_inline,
                namespace_decl->location);
            result->canonical_decl = result.get();
            assign_node_id(result.get(), ctx.ast_ctx);
            if (!copy_decl_side_tables(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::FieldDecl: {
            const auto* field_decl = static_cast<const FieldDecl*>(decl);
            auto cloned_type = rewrite_type(field_decl->type, ctx);
            std::unique_ptr<FieldDecl> result;
            if (field_decl->is_bitfield()) {
                result = std::make_unique<FieldDecl>(
                    cloned_type,
                    field_decl->name,
                    field_decl->bitfield_width,
                    field_decl->location);
            } else {
                result = std::make_unique<FieldDecl>(
                    cloned_type,
                    field_decl->name,
                    field_decl->location);
            }
            assign_node_id(result.get(), ctx.ast_ctx);
            if (!copy_decl_side_tables(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::CppAccessSpecDecl: {
            const auto* access_spec_decl =
                static_cast<const CppAccessSpecDecl*>(decl);
            auto result = std::make_unique<CppAccessSpecDecl>(
                access_spec_decl->access,
                access_spec_decl->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            if (!copy_decl_side_tables(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::CppRecordDecl: {
            const auto* record_decl = static_cast<const CppRecordDecl*>(decl);
            std::vector<CppBaseSpecifier> cloned_bases;
            cloned_bases.reserve(record_decl->bases.size());
            for (const auto& base : record_decl->bases) {
                CppBaseSpecifier cloned_base;
                cloned_base.type_name = base.type_name;
                cloned_base.type = rewrite_type(base.type, ctx);
                cloned_base.access = base.access;
                cloned_base.is_virtual_base = base.is_virtual_base;
                cloned_base.is_pack_expansion = base.is_pack_expansion;
                cloned_base.location = base.location;
                cloned_bases.push_back(std::move(cloned_base));
            }
            std::vector<std::unique_ptr<Decl>> cloned_members;
            cloned_members.reserve(record_decl->members.size());
            for (const auto& member : record_decl->members) {
                auto cloned_member = clone_decl_impl(member.get(), ctx, error_out);
                if (member && !cloned_member) {
                    return nullptr;
                }
                cloned_members.push_back(std::move(cloned_member));
            }
            auto result = std::make_unique<CppRecordDecl>(
                record_decl->record_kind,
                record_decl->name,
                std::move(cloned_bases),
                std::move(cloned_members),
                record_decl->is_definition != 0,
                record_decl->location);
            result->default_access = record_decl->default_access;
            result->definition_data = record_decl->definition_data;
            assign_node_id(result.get(), ctx.ast_ctx);
            if (!copy_decl_side_tables(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::TypedefDecl: {
            const auto* typedef_decl = static_cast<const TypedefDecl*>(decl);
            auto cloned_type = rewrite_type(typedef_decl->type, ctx);
            std::shared_ptr<Symbol> cloned_sym = nullptr;
            if (typedef_decl->sym) {
                cloned_sym = clone_symbol_shallow(
                    typedef_decl->sym,
                    rewrite_type(typedef_decl->sym->type, ctx));
                register_symbol(cloned_sym, ctx);
            }
            auto result = std::make_unique<TypedefDecl>(
                typedef_decl->name,
                cloned_type,
                std::move(cloned_sym),
                typedef_decl->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            if (!copy_decl_side_tables(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::VariableDecl: {
            const auto* variable = static_cast<const VariableDecl*>(decl);
            auto cloned_type = rewrite_type(variable->type, ctx);
            auto cloned_original_type = rewrite_type(variable->original_type, ctx);
            std::shared_ptr<Symbol> cloned_sym = nullptr;
            if (variable->sym) {
                cloned_sym = clone_symbol_shallow(
                    variable->sym,
                    rewrite_type(variable->sym->type, ctx));
                ctx.symbol_remap[variable->sym.get()] = cloned_sym;
                register_symbol(cloned_sym, ctx);
            }
            auto cloned_init =
                clone_expr_with_substitution(variable->init.get(), ctx, error_out);
            if (variable->init && !cloned_init) {
                return nullptr;
            }
            auto result = std::make_unique<VariableDecl>(
                cloned_type,
                variable->name,
                std::move(cloned_init),
                cloned_sym,
                variable->storage_class,
                variable->is_inline != 0,
                variable->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            result->is_constexpr = variable->is_constexpr;
            result->is_thread_local = variable->is_thread_local;
            result->is_block_byref = variable->is_block_byref;
            result->original_type = cloned_original_type;
            result->explicit_specialization_arguments =
                rewrite_template_arguments(
                    variable->explicit_specialization_arguments,
                    ctx,
                    error_out);
            result->has_explicit_specialization_argument_list =
                variable->has_explicit_specialization_argument_list;
            result->set_language_linkage(variable->get_language_linkage());
            if (variable->asm_label) {
                result->set_asm_label(*variable->asm_label);
            }
            if (result->sym) {
                result->sym->variable_definition = result.get();
            }
            if (!copy_decl_side_tables(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::ParamDecl: {
            const auto* param = static_cast<const ParamDecl*>(decl);
            auto cloned_type = rewrite_type(param->type, ctx);
            std::shared_ptr<Symbol> cloned_sym = nullptr;
            if (param->sym) {
                cloned_sym = clone_symbol_shallow(
                    param->sym,
                    rewrite_type(param->sym->type, ctx));
                ctx.symbol_remap[param->sym.get()] = cloned_sym;
                register_symbol(cloned_sym, ctx);
            }
            auto result = std::make_unique<ParamDecl>(
                cloned_type,
                param->get_name(),
                cloned_sym,
                param->storage_class,
                param->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            result->is_constexpr = param->is_constexpr;
            result->is_parameter_pack = param->is_parameter_pack;
            result->original_type =
                rewrite_type(QualType(param->original_type), ctx).get_shared();
            if (const Expr* default_arg = get_param_decl_default_argument(param)) {
                auto cloned_default = clone_expr_with_substitution(
                    default_arg,
                    ctx,
                    error_out);
                if (!cloned_default) {
                    return nullptr;
                }
                set_param_decl_default_argument(
                    result.get(),
                    std::move(cloned_default));
            }
            if (!copy_decl_side_tables(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::StaticAssertDecl: {
            const auto* static_assert_decl = static_cast<const StaticAssertDecl*>(decl);
            auto condition = clone_expr_with_substitution(
                static_assert_decl->condition.get(), ctx, error_out);
            if (static_assert_decl->condition && !condition) {
                return nullptr;
            }
            auto result = std::make_unique<StaticAssertDecl>(
                std::move(condition),
                static_assert_decl->message,
                static_assert_decl->has_message != 0,
                static_assert_decl->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            if (!copy_decl_side_tables(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::ErrorDecl: {
            const auto* error_decl = static_cast<const ErrorDecl*>(decl);
            auto result = std::make_unique<ErrorDecl>(
                error_decl->error_message,
                error_decl->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            if (!copy_decl_side_tables(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        default:
            return fail_decl_clone(
                error_out,
                "unsupported declaration clone kind " +
                    std::to_string(static_cast<int>(decl->get_kind())));
    }
}
} // namespace

std::unique_ptr<Expr> clone_expr_with_substitution(
    const Expr* expr,
    ASTCloneContext& ctx,
    std::string* error_out) {
    auto cloned = clone_expr_tree(expr, ctx.ast_ctx, error_out);
    if (!cloned) {
        return nullptr;
    }
    auto saved_rewrite_expr = std::move(ctx.rewrite_expr);
    ctx.rewrite_expr = nullptr;
    if (!rewrite_expr_tree(cloned, ctx, error_out)) {
        ctx.rewrite_expr = std::move(saved_rewrite_expr);
        return nullptr;
    }
    ctx.rewrite_expr = std::move(saved_rewrite_expr);
    return cloned;
}

bool rewrite_expr_tree_in_place(std::unique_ptr<Expr>& expr,
                                ASTCloneContext& ctx,
                                std::string* error_out) {
    std::string local_error;
    if (!error_out) {
        error_out = &local_error;
    } else {
        error_out->clear();
    }
    return rewrite_expr_tree(expr, ctx, error_out);
}

std::unique_ptr<Stmt> clone_stmt_tree(const Stmt* stmt,
                                      ASTCloneContext& ctx,
                                      std::string* error_out) {
    std::string local_error;
    if (!error_out) {
        error_out = &local_error;
    } else {
        error_out->clear();
    }
    return clone_stmt_impl(stmt, ctx, error_out);
}

bool rewrite_stmt_tree_in_place(std::unique_ptr<Stmt>& stmt,
                                ASTCloneContext& ctx,
                                std::string* error_out) {
    std::string local_error;
    if (!error_out) {
        error_out = &local_error;
    } else {
        error_out->clear();
    }
    return rewrite_stmt_tree_in_place_impl(stmt, ctx, error_out);
}

std::unique_ptr<Decl> clone_decl_tree(const Decl* decl,
                                      ASTCloneContext& ctx,
                                      std::string* error_out) {
    std::string local_error;
    if (!error_out) {
        error_out = &local_error;
    } else {
        error_out->clear();
    }
    return clone_decl_impl(decl, ctx, error_out);
}

bool rewrite_decl_tree_in_place(std::unique_ptr<Decl>& decl,
                                ASTCloneContext& ctx,
                                std::string* error_out) {
    std::string local_error;
    if (!error_out) {
        error_out = &local_error;
    } else {
        error_out->clear();
    }
    return rewrite_decl_tree_in_place_impl(decl, ctx, error_out);
}
