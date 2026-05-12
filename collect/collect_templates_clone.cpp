#include "collect_templates_internal.h"
#include "../helpers/auto_type_utils.h"

#include <sstream>

namespace template_sema_internal {

TemplateSubstitutionPass::TemplateSubstitutionPass() = default;

TemplateSubstitutionPass::TemplateSubstitutionPass(
    const TemplateSubstitutionPass& other)
    : ctx(other.ctx),
      rewrite_template_arguments_callback(
          other.rewrite_template_arguments_callback),
      rewrite_symbol_callback(other.rewrite_symbol_callback) {
    refresh_callbacks();
}

TemplateSubstitutionPass::TemplateSubstitutionPass(
    TemplateSubstitutionPass&& other) noexcept
    : ctx(std::move(other.ctx)),
      rewrite_template_arguments_callback(
          std::move(other.rewrite_template_arguments_callback)),
      rewrite_symbol_callback(std::move(other.rewrite_symbol_callback)) {
    refresh_callbacks();
}

TemplateSubstitutionPass& TemplateSubstitutionPass::operator=(
    const TemplateSubstitutionPass& other) {
    if (this == &other) {
        return *this;
    }
    ctx = other.ctx;
    rewrite_template_arguments_callback = other.rewrite_template_arguments_callback;
    rewrite_symbol_callback = other.rewrite_symbol_callback;
    refresh_callbacks();
    return *this;
}

TemplateSubstitutionPass& TemplateSubstitutionPass::operator=(
    TemplateSubstitutionPass&& other) noexcept {
    if (this == &other) {
        return *this;
    }
    ctx = std::move(other.ctx);
    rewrite_template_arguments_callback =
        std::move(other.rewrite_template_arguments_callback);
    rewrite_symbol_callback = std::move(other.rewrite_symbol_callback);
    refresh_callbacks();
    return *this;
}

ASTCloneContext& TemplateSubstitutionPass::context() { return ctx; }

const ASTCloneContext& TemplateSubstitutionPass::context() const { return ctx; }

void TemplateSubstitutionPass::refresh_callbacks() {
    auto* self = this;
    ctx.rewrite_template_arguments =
        [self](const std::vector<TemplateArgument>& template_arguments,
               ASTCloneContext&,
               std::string* error_out) -> std::vector<TemplateArgument> {
        if (!self->rewrite_template_arguments_callback) {
            return template_arguments;
        }
        return self->rewrite_template_arguments_callback(
            template_arguments,
            self->ctx,
            error_out);
    };
    ctx.rewrite_symbol =
        [self](const std::shared_ptr<Symbol>& sym) -> std::shared_ptr<Symbol> {
        if (self->rewrite_symbol_callback) {
            return self->rewrite_symbol_callback(sym, self->ctx);
        }
        if (auto remapped = lookup_symbol_remap_in_clone_context(sym, self->ctx)) {
            return remapped;
        }
        return sym;
    };
}

QualType TemplateSubstitutionPass::rewrite_type(QualType type) const {
    return ctx.rewrite_type ? ctx.rewrite_type(type) : type;
}

std::unique_ptr<Expr> TemplateSubstitutionPass::clone_expr(const Expr* expr,
                                                            std::string* error_out) {
    return clone_expr_with_substitution(expr, ctx, error_out);
}

std::unique_ptr<Stmt> TemplateSubstitutionPass::clone_stmt(const Stmt* stmt,
                                                            std::string* error_out) {
    return clone_stmt_tree(stmt, ctx, error_out);
}

std::unique_ptr<Decl> TemplateSubstitutionPass::clone_decl(const Decl* decl,
                                                            std::string* error_out) {
    return clone_decl_tree(decl, ctx, error_out);
}

ASTCloneContext& TemplateDependentResolutionPass::context() { return ctx; }

const ASTCloneContext& TemplateDependentResolutionPass::context() const {
    return ctx;
}

void TemplateDependentResolutionPass::sync_from_substitution_pass(
    const TemplateSubstitutionPass& substitution_pass) {
    ctx.rewrite_type = substitution_pass.context().rewrite_type;
    ctx.rewrite_template_arguments =
        substitution_pass.context().rewrite_template_arguments;
    ctx.rewrite_var_ref = substitution_pass.context().rewrite_var_ref;
    ctx.rewrite_symbol = substitution_pass.context().rewrite_symbol;
    ctx.register_symbol = substitution_pass.context().register_symbol;
    ctx.rewrite_member_expr = substitution_pass.context().rewrite_member_expr;
    ctx.expand_pack_expansion = substitution_pass.context().expand_pack_expansion;
    ctx.lookup_pack_size = substitution_pass.context().lookup_pack_size;
    ctx.symbol_remap = substitution_pass.context().symbol_remap;
    ctx.scope_remap = substitution_pass.context().scope_remap;
}

bool TemplateDependentResolutionPass::resolve_expr_in_place(
    std::unique_ptr<Expr>& expr,
    std::string* error_out) {
    return rewrite_expr_tree_in_place(expr, ctx, error_out);
}

bool TemplateDependentResolutionPass::resolve_stmt_in_place(
    std::unique_ptr<Stmt>& stmt,
    std::string* error_out) {
    return rewrite_stmt_tree_in_place(stmt, ctx, error_out);
}

bool TemplateDependentResolutionPass::resolve_decl_in_place(
    std::unique_ptr<Decl>& decl,
    std::string* error_out) {
    return rewrite_decl_tree_in_place(decl, ctx, error_out);
}

TemplateSubstitutionPass TemplateClonePassBuilder::build_substitution_pass() const {
    TemplateSubstitutionPass pass;
    pass.ctx.ast_ctx = ast_ctx;
    pass.ctx.rewrite_type = rewrite_type;
    pass.rewrite_template_arguments_callback = rewrite_template_arguments;
    pass.ctx.rewrite_var_ref = rewrite_var_ref;
    pass.ctx.register_symbol = register_symbol;
    pass.ctx.rewrite_member_expr = rewrite_member_expr;
    pass.ctx.expand_pack_expansion = expand_pack_expansion;
    pass.ctx.lookup_pack_size = lookup_pack_size;
    pass.ctx.symbol_remap = symbol_remap;
    pass.ctx.scope_remap = scope_remap;
    pass.rewrite_symbol_callback = rewrite_symbol;
    pass.refresh_callbacks();
    return pass;
}

TemplateDependentResolutionPass
TemplateClonePassBuilder::build_dependent_resolution_pass(
    const std::function<bool(std::unique_ptr<Expr>&, std::string*)>& resolve_expr) const {
    TemplateDependentResolutionPass pass;
    pass.ctx.ast_ctx = ast_ctx;
    pass.ctx.rewrite_type = rewrite_type;
    pass.ctx.rewrite_template_arguments = rewrite_template_arguments;
    pass.ctx.rewrite_var_ref = rewrite_var_ref;
    pass.ctx.register_symbol = register_symbol;
    pass.ctx.rewrite_member_expr = rewrite_member_expr;
    pass.ctx.rewrite_expr = resolve_expr;
    pass.ctx.expand_pack_expansion = expand_pack_expansion;
    pass.ctx.lookup_pack_size = lookup_pack_size;
    pass.ctx.symbol_remap = symbol_remap;
    pass.ctx.scope_remap = scope_remap;
    return pass;
}

TemplateDependentResolutionPass
TemplateClonePassBuilder::build_dependent_resolution_pass(
    const TemplateSubstitutionPass& substitution_pass,
    const std::function<bool(std::unique_ptr<Expr>&, std::string*)>& resolve_expr) const {
    auto pass = build_dependent_resolution_pass(resolve_expr);
    pass.ctx.rewrite_type = substitution_pass.context().rewrite_type;
    pass.ctx.rewrite_template_arguments =
        substitution_pass.context().rewrite_template_arguments;
    pass.ctx.rewrite_var_ref = substitution_pass.context().rewrite_var_ref;
    pass.ctx.rewrite_symbol = substitution_pass.context().rewrite_symbol;
    pass.ctx.register_symbol = substitution_pass.context().register_symbol;
    pass.ctx.rewrite_member_expr = substitution_pass.context().rewrite_member_expr;
    pass.ctx.expand_pack_expansion = substitution_pass.context().expand_pack_expansion;
    pass.ctx.lookup_pack_size = substitution_pass.context().lookup_pack_size;
    pass.ctx.symbol_remap = substitution_pass.context().symbol_remap;
    pass.ctx.scope_remap = substitution_pass.context().scope_remap;
    return pass;
}

bool materialize_specialized_fold_expression(
    Collect& collect,
    std::unique_ptr<Expr>& expr,
    QualType implicit_this_type,
    std::shared_ptr<CType> bool_type,
    const TemplateParameterList& parameters,
    const TemplateArgumentBindings& specialization_bindings,
    const std::function<std::unique_ptr<Expr>(size_t, const Expr*, std::string*)>&
        clone_pattern_element,
    std::string* error_out) {
    auto* fold = dyn_cast<FoldExpr>(expr.get());
    if (!fold) {
        return true;
    }

    TemplatePackExpansionShape shape;
    if (!collect_pack_expansion_shape_in_expr(
            fold->pattern.get(),
            parameters,
            shape)) {
        if (shape.has_unsupported_dependency) {
            return true;
        }
        if (error_out && error_out->empty()) {
            *error_out = "failed to collect fold-expression pack shape";
        }
        return false;
    }
    if (shape.has_unsupported_dependency) {
        return true;
    }
    if (shape.referenced_parameters.empty()) {
        if (error_out && error_out->empty()) {
            *error_out =
                "fold expression pattern does not reference a template parameter pack";
        }
        return false;
    }

    std::string arity_error;
    auto expansion_arity = find_pack_expansion_arity_for_bindings(
        shape,
        parameters,
        specialization_bindings,
        &arity_error);
    if (!expansion_arity.has_value()) {
        if (arity_error.empty()) {
            return true;
        }
        if (error_out && error_out->empty()) {
            *error_out = arity_error;
        }
        return false;
    }

    auto owned_fold = std::unique_ptr<FoldExpr>(
        static_cast<FoldExpr*>(expr.release()));
    if (*expansion_arity == 0) {
        if (owned_fold->init) {
            expr = std::move(owned_fold->init);
            return true;
        }
        if (owned_fold->op == BinOpTypes::LOGICAL_AND) {
            expr = collect.collect_integer_literal(
                "1",
                std::move(bool_type),
                owned_fold->location);
            return expr != nullptr;
        }
        if (owned_fold->op == BinOpTypes::LOGICAL_OR) {
            expr = collect.collect_integer_literal(
                "0",
                std::move(bool_type),
                owned_fold->location);
            return expr != nullptr;
        }
        if (error_out && error_out->empty()) {
            *error_out =
                "empty unary fold expression is not supported for this operator";
        }
        return false;
    }

    std::vector<std::unique_ptr<Expr>> pattern_elements;
    pattern_elements.reserve(*expansion_arity);
    for (size_t element_index = 0;
         element_index < *expansion_arity;
         ++element_index) {
        auto element_expr =
            clone_pattern_element(
                element_index,
                owned_fold->pattern.get(),
                error_out);
        if (!element_expr) {
            return false;
        }
        pattern_elements.push_back(std::move(element_expr));
    }

    auto combine =
        [&](std::unique_ptr<Expr> lhs,
            std::unique_ptr<Expr> rhs) -> std::unique_ptr<Expr> {
            auto combined = collect.collect_binary_operation(
                std::move(lhs),
                std::move(rhs),
                owned_fold->op,
                owned_fold->location);
            if (!combined) {
                if (error_out && error_out->empty()) {
                    *error_out =
                        "failed to materialize fold-expression binary operation";
                }
                return nullptr;
            }
            if (!collect.resolve_dependent_expr_after_substitution(
                    combined,
                    implicit_this_type,
                    error_out)) {
                return nullptr;
            }
            return combined;
        };

    auto resolve_accumulator = [&](std::unique_ptr<Expr>& candidate) -> bool {
        return !candidate ||
               collect.resolve_dependent_expr_after_substitution(
                   candidate,
                   implicit_this_type,
                   error_out);
    };

    std::unique_ptr<Expr> result;
    if (owned_fold->is_binary_fold()) {
        result = std::move(owned_fold->init);
        if (!resolve_accumulator(result)) {
            return false;
        }
        if (owned_fold->direction == FoldDirection::Left) {
            for (auto& element : pattern_elements) {
                result = combine(std::move(result), std::move(element));
                if (!result) {
                    return false;
                }
            }
        } else {
            for (size_t index = pattern_elements.size(); index-- > 0;) {
                result = combine(
                    std::move(pattern_elements[index]),
                    std::move(result));
                if (!result) {
                    return false;
                }
            }
        }
    } else if (owned_fold->direction == FoldDirection::Left) {
        result = std::move(pattern_elements.front());
        for (size_t index = 1; index < pattern_elements.size(); ++index) {
            result = combine(
                std::move(result),
                std::move(pattern_elements[index]));
            if (!result) {
                return false;
            }
        }
    } else {
        result = std::move(pattern_elements.back());
        for (size_t index = pattern_elements.size() - 1; index-- > 0;) {
            result = combine(
                std::move(pattern_elements[index]),
                std::move(result));
            if (!result) {
                return false;
            }
        }
    }

    expr = std::move(result);
    return true;
}

TemplateClonePassBuilder make_template_binding_clone_pass_builder(
    ASTContext* ast_ctx,
    Collect* collect,
    const TemplateParameterList& parameters,
    const TemplateArgumentBindings& argument_bindings,
    SrcLoc loc,
    std::string value_error_message,
    const std::function<QualType(QualType)>& rewrite_type,
    const std::function<std::vector<TemplateArgument>(
        const std::vector<TemplateArgument>&)>& rewrite_template_arguments,
    const std::function<void(const std::shared_ptr<Symbol>&)>& register_symbol,
    const std::function<bool(MemberExpr*, std::string*)>& rewrite_member_expr) {
    TemplateClonePassBuilder builder;
    builder.ast_ctx = ast_ctx;
    builder.rewrite_type = rewrite_type;
    builder.rewrite_template_arguments =
        [rewrite_template_arguments](
            const std::vector<TemplateArgument>& template_arguments,
            ASTCloneContext&,
            std::string*) -> std::vector<TemplateArgument> {
        return rewrite_template_arguments
                   ? rewrite_template_arguments(template_arguments)
                   : template_arguments;
    };
    const auto* parameters_ptr = &parameters;
    const auto* argument_bindings_ptr = &argument_bindings;
    ASTContext* clone_ast_ctx = ast_ctx;
    SrcLoc fallback_loc = loc;
    builder.rewrite_var_ref =
        [parameters_ptr,
         collect,
         argument_bindings_ptr,
         clone_ast_ctx,
         fallback_loc,
         rewrite_template_arguments_fn = rewrite_template_arguments,
         rewrite_type_fn = rewrite_type,
         value_error_message = std::move(value_error_message)](
            const VarRef* var_ref,
            std::string* error_out) -> std::unique_ptr<Expr> {
        const TemplateArgument* replacement =
            find_template_argument_for_non_type_parameter_symbol(
                var_ref ? var_ref->symref.get() : nullptr,
                *parameters_ptr,
                *argument_bindings_ptr);
        if (!replacement) {
            return nullptr;
        }
        auto literal = make_constant_expr_for_template_argument(
            *replacement,
            clone_ast_ctx,
            var_ref ? var_ref->location : fallback_loc);
        if (literal && rewrite_type_fn) {
            ASTCloneContext rewrite_ctx;
            rewrite_ctx.ast_ctx = clone_ast_ctx;
            rewrite_ctx.rewrite_type = rewrite_type_fn;
            std::string rewrite_error;
            if (!rewrite_expr_tree_in_place(
                    literal,
                    rewrite_ctx,
                    &rewrite_error)) {
                literal.reset();
                if (error_out && error_out->empty()) {
                    *error_out = rewrite_error.empty()
                        ? value_error_message
                        : rewrite_error;
                }
                return nullptr;
            }
        }
        if (!literal && error_out && error_out->empty()) {
            *error_out = value_error_message;
        }
        if (literal) {
            return literal;
        }
        if (collect && var_ref && var_ref->symref) {
            if (const auto* specialization_info =
                    get_symbol_variable_template_specialization(
                        var_ref->symref.get())) {
                std::vector<TemplateArgument> rewritten_arguments =
                    rewrite_template_arguments_fn
                        ? rewrite_template_arguments_fn(
                              specialization_info->arguments)
                        : specialization_info->arguments;
                std::shared_ptr<Symbol> specialization_symbol = nullptr;
                auto* specialization_decl =
                    collect->instantiate_variable_template_specialization_for_clone(
                        specialization_info->primary_template,
                        rewritten_arguments,
                        var_ref->location,
                        &specialization_symbol);
                if (!specialization_decl || !specialization_symbol) {
                    if (error_out && error_out->empty()) {
                        *error_out =
                            "failed to rewrite variable template specialization reference";
                    }
                    return nullptr;
                }
                auto rewritten_ref = collect->collect_identifier_reference(
                    var_ref->get_name(),
                    std::move(specialization_symbol),
                    var_ref->location);
                if (const auto* qualified_info =
                        var_ref->get_cpp_qualified_info()) {
                    rewritten_ref = attach_cpp_qualified_info_to_expr(
                        std::move(rewritten_ref),
                        *qualified_info);
                }
                return rewritten_ref;
            }
        }
        return nullptr;
    };
    builder.rewrite_symbol =
        [collect,
         fallback_loc,
         rewrite_template_arguments_fn = rewrite_template_arguments,
         register_symbol_fn = register_symbol](
            const std::shared_ptr<Symbol>& sym,
            ASTCloneContext& clone_ctx) -> std::shared_ptr<Symbol> {
        if (!sym) {
            return nullptr;
        }
        if (auto remapped = lookup_symbol_remap_in_clone_context(sym, clone_ctx)) {
            return remapped;
        }
        if (!collect) {
            return sym;
        }
        const auto* specialization_info =
            get_symbol_variable_template_specialization(sym.get());
        if (!specialization_info || !specialization_info->primary_template) {
            return sym;
        }

        std::vector<TemplateArgument> rewritten_arguments =
            rewrite_template_arguments_fn
                ? rewrite_template_arguments_fn(specialization_info->arguments)
                : specialization_info->arguments;
        std::shared_ptr<Symbol> specialization_symbol = nullptr;
        auto* specialization_decl =
            collect->instantiate_variable_template_specialization_for_clone(
                specialization_info->primary_template,
                rewritten_arguments,
                fallback_loc,
                &specialization_symbol);
        if (!specialization_decl || !specialization_symbol) {
            return sym;
        }
        clone_ctx.symbol_remap[sym.get()] = specialization_symbol;
        if (register_symbol_fn) {
            register_symbol_fn(specialization_symbol);
        }
        return specialization_symbol;
    };
    builder.register_symbol = register_symbol;
    builder.rewrite_member_expr = rewrite_member_expr;
    builder.lookup_pack_size =
        [parameters_ptr, argument_bindings_ptr](
            const SizeOfPackExpr* expr,
            std::string* error_out) -> std::optional<size_t> {
        return find_pack_binding_size_for_sizeof_expr(
            expr,
            *parameters_ptr,
            *argument_bindings_ptr,
            error_out);
    };
    return builder;
}

bool remap_template_argument_after_outer_substitution(
    TemplateArgument& argument,
    const std::unordered_map<const TemplateParameterDecl*,
                             const TemplateParameterDecl*>& parameter_rebinds,
    ASTCloneContext& clone_ctx,
    std::string* error_out) {
    if (argument.kind != TemplateArgumentKind::Value) {
        return true;
    }

    if (argument.referenced_parameter) {
        auto parameter_it = parameter_rebinds.find(argument.referenced_parameter);
        if (parameter_it != parameter_rebinds.end() && parameter_it->second) {
            argument.referenced_parameter = parameter_it->second;
        }
    }
    if (argument.value.kind == ConstValueKind::Address &&
        argument.value.address_value.symbol) {
        if (auto remapped = lookup_symbol_remap_in_clone_context(
                argument.value.address_value.symbol,
                clone_ctx)) {
            argument.value.address_value.symbol = remapped;
        }
    } else if (argument.value.kind == ConstValueKind::MemberPointer &&
               argument.value.member_pointer_value.method_symbol) {
        if (auto remapped = lookup_symbol_remap_in_clone_context(
                argument.value.member_pointer_value.method_symbol,
                clone_ctx)) {
            argument.value.member_pointer_value.method_symbol = remapped;
        }
    }
    if (!argument.value_expr) {
        return true;
    }

    std::string clone_error;
    auto cloned_expr = clone_expr_with_substitution(
        argument.value_expr.get(),
        clone_ctx,
        &clone_error);
    if (!cloned_expr) {
        if (error_out && error_out->empty()) {
            *error_out =
                clone_error.empty()
                    ? "member template default argument expression is not supported"
                    : clone_error;
        }
        return false;
    }

    argument.value_expr = std::shared_ptr<Expr>(cloned_expr.release());
    return true;
}

// Recursively rewrite a type, replacing template parameter references
// using the parameter_rebinds map (old parameter_decl → new parameter_decl).
// To avoid spurious allocations in deeply nested template types, each
// variant checks whether the rewritten children differ from the originals
// before constructing a new type node.  This is performance-critical:
// template types are compared frequently and allocation is expensive.
// If the remapping logic changes, both the type switch AND the
// remap_template_argument helper lambda must be updated in sync.
QualType remap_template_parameter_types_in_type(
    QualType type,
    const std::unordered_map<const TemplateParameterDecl*,
                             const TemplateParameterDecl*>& parameter_rebinds,
    ASTCloneContext* clone_ctx) {
    if (!type) {
        return type;
    }

    auto raw = type.get_shared();
    uint8_t quals = type.get_qualifiers();

    if (auto parm_type = dyn_cast_shared<TemplateTypeParmType>(raw)) {
        if (parm_type->parameter_decl) {
            auto it = parameter_rebinds.find(parm_type->parameter_decl);
            if (it != parameter_rebinds.end() && it->second) {
                if (auto* rebound =
                        dyn_cast<TemplateTypeParmDecl>(
                            const_cast<TemplateParameterDecl*>(it->second))) {
                    return QualType(rebound->type, quals);
                }
            }
        }
        return type;
    }

    auto remap_template_argument =
        [&](const TemplateArgument& argument) -> TemplateArgument {
        TemplateArgument remapped = argument;
        switch (argument.kind) {
            case TemplateArgumentKind::Type:
                remapped.type = remap_template_parameter_types_in_type(
                    argument.type,
                    parameter_rebinds,
                    clone_ctx);
                break;
            case TemplateArgumentKind::Template:
                if (argument.referenced_parameter) {
                    auto it = parameter_rebinds.find(argument.referenced_parameter);
                    if (it != parameter_rebinds.end()) {
                        remapped.referenced_parameter = it->second;
                    }
                }
                break;
            case TemplateArgumentKind::Value:
                remapped.value_type = remap_template_parameter_types_in_type(
                    argument.value_type,
                    parameter_rebinds,
                    clone_ctx);
                if (argument.referenced_parameter) {
                    auto it = parameter_rebinds.find(argument.referenced_parameter);
                    if (it != parameter_rebinds.end()) {
                        remapped.referenced_parameter = it->second;
                    }
                }
                if (clone_ctx) {
                    remap_template_argument_after_outer_substitution(
                        remapped,
                        parameter_rebinds,
                        *clone_ctx,
                        nullptr);
                }
                break;
        }
        remapped.is_dependent = template_argument_depends_on_template_parameters(
            remapped,
            clone_ctx ? clone_ctx->ast_ctx : nullptr);
        if (remapped.kind == TemplateArgumentKind::Value &&
            !remapped.is_dependent &&
            remapped.value_type) {
            std::string ignored_error;
            normalize_concrete_template_value_argument(
                remapped,
                remapped.value_type,
                &ignored_error);
        }
        return remapped;
    };

    if (auto typedef_type = dyn_cast_shared<TypedefType>(raw)) {
        auto remapped_underlying = remap_template_parameter_types_in_type(
            typedef_type->underlying_type,
            parameter_rebinds,
            clone_ctx);
        if (remapped_underlying.equals_qualified(typedef_type->underlying_type)) {
            return type;
        }
        return QualType(
            std::make_shared<TypedefType>(
                typedef_type->name,
                remapped_underlying,
                typedef_type->typedef_decl),
            quals);
    }

    if (auto specialization = dyn_cast_shared<TemplateSpecializationType>(raw)) {
        std::vector<TemplateArgument> remapped_arguments;
        remapped_arguments.reserve(specialization->arguments.size());
        bool changed = false;
        for (const auto& argument : specialization->arguments) {
            auto remapped_argument = remap_template_argument(argument);
            changed |= !remapped_argument.equals(argument);
            remapped_arguments.push_back(std::move(remapped_argument));
        }
        if (!changed) {
            return type;
        }
        return QualType(
            std::make_shared<TemplateSpecializationType>(
                specialization->template_name,
                specialization->primary_template,
                std::move(remapped_arguments),
                specialization->is_dependent),
            quals);
    }

    if (auto pack_element =
            dyn_cast_shared<BuiltinTypePackElementType>(raw)) {
        std::vector<TemplateArgument> remapped_arguments;
        remapped_arguments.reserve(pack_element->arguments.size());
        bool changed = false;
        for (const auto& argument : pack_element->arguments) {
            auto remapped_argument = remap_template_argument(argument);
            changed |= !remapped_argument.equals(argument);
            remapped_arguments.push_back(std::move(remapped_argument));
        }
        if (!changed) {
            return type;
        }
        return QualType(
            std::make_shared<BuiltinTypePackElementType>(
                std::move(remapped_arguments)),
            quals);
    }

    if (auto dependent_name = dyn_cast_shared<DependentNameType>(raw)) {
        auto remapped_qualifier = remap_template_parameter_types_in_type(
            dependent_name->qualifier_type,
            parameter_rebinds,
            clone_ctx);
        std::vector<TemplateArgument> remapped_arguments;
        remapped_arguments.reserve(dependent_name->template_arguments.size());
        bool changed =
            !remapped_qualifier.equals_qualified(dependent_name->qualifier_type);
        for (const auto& argument : dependent_name->template_arguments) {
            auto remapped_argument = remap_template_argument(argument);
            changed |= !remapped_argument.equals(argument);
            remapped_arguments.push_back(std::move(remapped_argument));
        }
        if (!changed) {
            return type;
        }
        return QualType(
            std::make_shared<DependentNameType>(
                remapped_qualifier,
                dependent_name->member_name,
                std::move(remapped_arguments),
                dependent_name->is_current_instantiation,
                dependent_name->requires_typename_keyword,
                dependent_name->requires_template_keyword),
            quals);
    }

    if (auto ptr = dyn_cast_shared<PointerType>(raw)) {
        auto remapped_pointed = remap_template_parameter_types_in_type(
            ptr->pointed_type,
            parameter_rebinds,
            clone_ctx);
        if (remapped_pointed.equals_qualified(ptr->pointed_type)) {
            return type;
        }
        return QualType(std::make_shared<PointerType>(remapped_pointed), quals);
    }

    if (auto ref = dyn_cast_shared<ReferenceType>(raw)) {
        auto remapped_referred = remap_template_parameter_types_in_type(
            ref->referred_type,
            parameter_rebinds,
            clone_ctx);
        if (remapped_referred.equals_qualified(ref->referred_type)) {
            return type;
        }
        auto collapsed = make_reference_type(
            remapped_referred,
            ref->reference_kind);
        return QualType(collapsed.get_shared(), quals);
    }

    if (auto transform = dyn_cast_shared<BuiltinTypeTransformType>(raw)) {
        auto remapped_operand = remap_template_parameter_types_in_type(
            transform->operand_type,
            parameter_rebinds,
            clone_ctx);
        if (remapped_operand.equals_qualified(transform->operand_type)) {
            return type;
        }
        return QualType(
            std::make_shared<BuiltinTypeTransformType>(
                transform->transform_kind,
                remapped_operand),
            quals);
    }

    if (auto mem_ptr = dyn_cast_shared<MemberPointerType>(raw)) {
        auto remapped_class = remap_template_parameter_types_in_type(
            mem_ptr->class_type,
            parameter_rebinds,
            clone_ctx);
        auto remapped_member = remap_template_parameter_types_in_type(
            mem_ptr->member_type,
            parameter_rebinds,
            clone_ctx);
        if (remapped_class.equals_qualified(mem_ptr->class_type) &&
            remapped_member.equals_qualified(mem_ptr->member_type)) {
            return type;
        }
        return QualType(
            std::make_shared<MemberPointerType>(
                remapped_class,
                remapped_member),
            quals);
    }

    if (auto blk = dyn_cast_shared<BlockPointerType>(raw)) {
        auto remapped_pointed = remap_template_parameter_types_in_type(
            blk->pointed_type,
            parameter_rebinds,
            clone_ctx);
        if (remapped_pointed.equals_qualified(blk->pointed_type)) {
            return type;
        }
        return QualType(
            std::make_shared<BlockPointerType>(remapped_pointed),
            quals);
    }

    if (auto arr = dyn_cast_shared<ArrayType>(raw)) {
        auto remapped_element = remap_template_parameter_types_in_type(
            arr->element_type,
            parameter_rebinds,
            clone_ctx);
        if (remapped_element.equals_qualified(arr->element_type)) {
            return type;
        }
        if (arr->size_kind == ArraySizeKind::Variable && arr->size_expr) {
            return QualType(
                std::make_shared<ArrayType>(
                    remapped_element,
                    arr->size_expr),
                quals);
        }
        return QualType(
            std::make_shared<ArrayType>(
                remapped_element,
                arr->size),
            quals);
    }

    if (auto func = dyn_cast_shared<FunctionType>(raw)) {
        auto remapped_ret = remap_template_parameter_types_in_type(
            func->ret_type,
            parameter_rebinds,
            clone_ctx);
        bool changed = !remapped_ret.equals_qualified(func->ret_type);
        std::vector<QualType> remapped_parameters;
        remapped_parameters.reserve(func->parameters.size());
        for (const auto& parameter : func->parameters) {
            auto remapped_parameter = remap_template_parameter_types_in_type(
                parameter,
                parameter_rebinds,
                clone_ctx);
            changed |= !remapped_parameter.equals_qualified(parameter);
            remapped_parameters.push_back(std::move(remapped_parameter));
        }
        if (!changed) {
            return type;
        }
        auto rewritten = std::make_shared<FunctionType>();
        rewritten->ret_type = remapped_ret;
        rewritten->parameters = std::move(remapped_parameters);
        rewritten->parameter_pack_flags = func->parameter_pack_flags;
        rewritten->normalize_parameter_pack_flags();
        rewritten->is_variadic = func->is_variadic;
        rewritten->has_prototype = func->has_prototype;
        rewritten->member_ref_qualifier = func->member_ref_qualifier;
        rewritten->has_explicit_exception_spec =
            func->has_explicit_exception_spec;
        rewritten->exception_spec = func->exception_spec;
        rewritten->exception_spec_expr = func->exception_spec_expr;
        return QualType(rewritten, quals);
    }

    if (auto vec = dyn_cast_shared<VectorType>(raw)) {
        auto remapped_element = remap_template_parameter_types_in_type(
            vec->element_type,
            parameter_rebinds,
            clone_ctx);
        if (remapped_element.equals_qualified(vec->element_type)) {
            return type;
        }
        return QualType(
            std::make_shared<VectorType>(
                remapped_element,
                vec->total_bytes),
            quals);
    }

    return type;
}

std::vector<TemplateArgument> remap_template_parameter_types_in_arguments(
    const std::vector<TemplateArgument>& arguments,
    const std::unordered_map<const TemplateParameterDecl*,
                             const TemplateParameterDecl*>& parameter_rebinds,
    ASTCloneContext* clone_ctx) {
    std::vector<TemplateArgument> remapped;
    remapped.reserve(arguments.size());
    for (const auto& argument : arguments) {
        TemplateArgument rewritten = argument;
        switch (argument.kind) {
            case TemplateArgumentKind::Type:
                rewritten.type = remap_template_parameter_types_in_type(
                    argument.type,
                    parameter_rebinds,
                    clone_ctx);
                break;
            case TemplateArgumentKind::Template:
                if (argument.referenced_parameter) {
                    auto it = parameter_rebinds.find(argument.referenced_parameter);
                    if (it != parameter_rebinds.end()) {
                        rewritten.referenced_parameter = it->second;
                    }
                }
                break;
            case TemplateArgumentKind::Value:
                rewritten.value_type = remap_template_parameter_types_in_type(
                    argument.value_type,
                    parameter_rebinds,
                    clone_ctx);
                if (argument.referenced_parameter) {
                    auto it = parameter_rebinds.find(argument.referenced_parameter);
                    if (it != parameter_rebinds.end()) {
                        rewritten.referenced_parameter = it->second;
                    }
                }
                if (clone_ctx) {
                    remap_template_argument_after_outer_substitution(
                        rewritten,
                        parameter_rebinds,
                        *clone_ctx,
                        nullptr);
                }
                break;
        }
        rewritten.is_dependent = template_argument_depends_on_template_parameters(
            rewritten,
            clone_ctx ? clone_ctx->ast_ctx : nullptr);
        if (rewritten.kind == TemplateArgumentKind::Value &&
            !rewritten.is_dependent &&
            rewritten.value_type) {
            std::string ignored_error;
            normalize_concrete_template_value_argument(
                rewritten,
                rewritten.value_type,
                &ignored_error);
        }
        remapped.push_back(std::move(rewritten));
    }
    return remapped;
}

// The rewrite_type closure composes two transformations in strict order:
// 1. Outer-pass substitution (e.g., concrete template arguments from the
//    enclosing instantiation)
// 2. Parameter rebinding (remaps parameter pointers to match the nested
//    template's own parameter list)
// This order is critical: outer bindings must be resolved first so they
// don't accidentally shadow nested parameters.  parameter_rebinds must
// remain valid for the lifetime of the returned builder.
TemplateClonePassBuilder make_nested_template_clone_pass_builder(
    const TemplateClonePassBuilder& outer_builder,
    const TemplateSubstitutionPass& outer_pass,
    const std::function<std::vector<TemplateArgument>(
        const std::vector<TemplateArgument>&)>& rewrite_outer_template_arguments,
    const std::unordered_map<const TemplateParameterDecl*,
                             const TemplateParameterDecl*>& parameter_rebinds,
    const std::unordered_map<const Symbol*, std::shared_ptr<Symbol>>&
        extra_symbol_remap) {
    auto builder = outer_builder;
    auto outer_rewrite_type = builder.rewrite_type;
    builder.rewrite_type =
        [outer_rewrite_type,
         &parameter_rebinds](QualType type) -> QualType {
        auto rewritten =
            outer_rewrite_type ? outer_rewrite_type(type) : type;
        return remap_template_parameter_types_in_type(
            rewritten,
            parameter_rebinds);
    };
    builder.symbol_remap = outer_pass.context().symbol_remap;
    builder.scope_remap = outer_pass.context().scope_remap;
    for (const auto& [pattern_symbol, remapped_symbol] : extra_symbol_remap) {
        builder.symbol_remap[pattern_symbol] = remapped_symbol;
    }
    builder.rewrite_symbol =
        [](const std::shared_ptr<Symbol>& sym,
           ASTCloneContext& clone_ctx) -> std::shared_ptr<Symbol> {
        if (!sym) {
            return nullptr;
        }
        if (auto remapped =
                lookup_symbol_remap_in_clone_context(sym, clone_ctx)) {
            return remapped;
        }
        return sym;
    };
    builder.rewrite_template_arguments =
        [rewrite_outer_template_arguments,
         &parameter_rebinds](const std::vector<TemplateArgument>& template_arguments,
                             ASTCloneContext& clone_ctx,
                             std::string* error_out)
            -> std::vector<TemplateArgument> {
        auto rewritten =
            rewrite_outer_template_arguments
                ? rewrite_outer_template_arguments(template_arguments)
                : template_arguments;
        for (auto& rewritten_argument : rewritten) {
            if (!remap_template_argument_after_outer_substitution(
                    rewritten_argument,
                    parameter_rebinds,
                    clone_ctx,
                    error_out)) {
                return {};
            }
        }
        return rewritten;
    };
    return builder;
}

size_t method_user_param_start(const std::shared_ptr<FunctionType>& fn_type) {
    if (!fn_type || fn_type->parameters.empty()) {
        return 0;
    }
    auto first_param =
        desugar_type(fn_type->parameters.front()).as_shared<PointerType>();
    if (!first_param) {
        return 0;
    }
    if (canonical_type_kind(first_param->pointed_type) != TypeKind::Object) {
        return 0;
    }
    return 1;
}

std::string make_method_virtual_slot_key(const std::string& method_name,
                                         QualType method_type) {
    auto fn_type = desugar_type(method_type).as_shared<FunctionType>();
    if (!fn_type) {
        return method_name + "(<invalid>)";
    }
    std::ostringstream os;
    os << method_name << "{cv=";
    if (!fn_type->parameters.empty()) {
        auto this_ptr =
            desugar_type(fn_type->parameters.front()).as_shared<PointerType>();
        if (this_ptr &&
            canonical_type_kind(this_ptr->pointed_type) == TypeKind::Object) {
            uint8_t this_cv = static_cast<uint8_t>(
                this_ptr->pointed_type.get_qualifiers() &
                static_cast<uint8_t>(QUAL_CONST | QUAL_VOLATILE));
            if (this_cv & QUAL_CONST) {
                os << "c";
            }
            if (this_cv & QUAL_VOLATILE) {
                os << "v";
            }
        }
    }
    os << ",ref=";
    if (fn_type->member_ref_qualifier == FunctionRefQualifierKind::LValue) {
        os << "&";
    } else if (fn_type->member_ref_qualifier == FunctionRefQualifierKind::RValue) {
        os << "&&";
    } else {
        os << "-";
    }
    os << "}(";
    bool wrote_param = false;
    size_t param_start = method_user_param_start(fn_type);
    for (size_t idx = param_start; idx < fn_type->parameters.size(); ++idx) {
        QualType param_type = fn_type->parameters[idx];
        if (param_type && param_type->isVoid() &&
            fn_type->parameters.size() == param_start + 1) {
            break;
        }
        if (wrote_param) {
            os << ",";
        }
        os << param_type.to_string();
        wrote_param = true;
    }
    if (fn_type->is_variadic) {
        if (wrote_param) {
            os << ",";
        }
        os << "...";
    }
    os << ")";
    return os.str();
}

bool rebind_member_expr_for_specialized_record(MemberExpr* member,
                                               ASTContext* ast_ctx,
                                               std::string* error_out) {
    if (!member || !member->base) {
        return true;
    }

    QualType base_type = member->base->get_type();
    if (!base_type) {
        return true;
    }

    std::shared_ptr<ObjectType> record_type = nullptr;
    if (member->isArrow) {
        auto ptr_type =
            remove_reference(desugar_type(base_type)).as_shared<PointerType>();
        if (!ptr_type) {
            return true;
        }
        record_type = desugar_type(ptr_type->pointed_type).as_shared<ObjectType>();
    } else {
        record_type =
            remove_reference(desugar_type(base_type)).as_shared<ObjectType>();
    }
    if (!record_type) {
        return true;
    }

    const auto* record_decl =
        canonical_record_decl(dyn_cast<ObjectDecl>(record_type->get_decl()));
    if (!record_decl) {
        return true;
    }
    const RecordSemanticState* state =
        record_semantics_cache_lookup(record_decl, ast_ctx);
    if (!state) {
        return true;
    }

    const auto& member_name = member->get_member_name();
    for (size_t idx = 0; idx < state->fields.size(); ++idx) {
        const auto& field = state->fields[idx];
        if (field.is_base_subobject || field.is_virtual_base_storage ||
            field.name != member_name) {
            continue;
        }

        member->member_type = field.type;
        member->virtual_base_record_decl = nullptr;
        member->field_index = static_cast<uint32_t>(idx);
        member->field_path.clear();
        member->byte_offset = static_cast<uint32_t>(field.offset);
        member->is_bitfield = field.is_bitfield;
        if (field.is_bitfield && ast_ctx) {
            ast_ctx->set_bitfield_info(
                member->node_id,
                BitfieldInfo{
                    field.bit_offset,
                    field.bit_width,
                    field.storage_size});
        }

        uint8_t base_quals = QUAL_NONE;
        if (member->isArrow) {
            auto ptr_type =
                remove_reference(desugar_type(base_type)).as_shared<PointerType>();
            if (ptr_type) {
                base_quals = ptr_type->pointed_type.get_qualifiers();
            }
        } else {
            base_quals = remove_reference(base_type).get_qualifiers();
        }
        if (base_quals != QUAL_NONE && member->member_type) {
            member->member_type = member->member_type.with_qualifiers(base_quals);
        }
        return true;
    }

    return true;
}

// Some expression-bearing function types have already been cloned once before
// the final parameter-symbol remap exists. Repair only stale dependent
// parameter references by matching them to the specialization parameters.
void rewrite_stale_parameter_refs_by_name(
    Expr* expr,
    const std::unordered_map<std::string, std::shared_ptr<Symbol>>&
        parameter_symbols,
    const ASTContext* ast_ctx) {
    if (!expr || parameter_symbols.empty()) {
        return;
    }

    auto visit = [&](auto&& self, Expr* candidate) -> void {
        if (!candidate) {
            return;
        }
        if (auto* var_ref = dyn_cast<VarRef>(candidate)) {
            auto replacement_it = parameter_symbols.find(var_ref->get_name());
            if (replacement_it != parameter_symbols.end() &&
                replacement_it->second &&
                (!var_ref->symref ||
                 (var_ref->symref->kind == SymbolKind::VARIABLE &&
                  type_depends_on_template_parameters(
                      var_ref->symref->type,
                      ast_ctx)))) {
                var_ref->symref = replacement_it->second;
            }
            return;
        }

        auto visit_unique = [&](const std::unique_ptr<Expr>& child) {
            self(self, child.get());
        };
        auto visit_vector =
            [&](const std::vector<std::unique_ptr<Expr>>& children) {
            for (const auto& child : children) {
                self(self, child.get());
            }
        };

        switch (candidate->get_kind()) {
            case StmtKind::FuncCall: {
                auto* call = static_cast<FuncCall*>(candidate);
                visit_unique(call->func);
                visit_vector(call->args);
                return;
            }
            case StmtKind::DependentCallExpr: {
                auto* call = static_cast<DependentCallExpr*>(candidate);
                visit_unique(call->callee);
                visit_vector(call->args);
                return;
            }
            case StmtKind::ImplicitCast: {
                visit_unique(static_cast<ImplicitCast*>(candidate)->expr);
                return;
            }
            case StmtKind::ExplicitCast: {
                visit_unique(static_cast<ExplicitCast*>(candidate)->expr);
                return;
            }
            case StmtKind::UnaryOperation: {
                visit_unique(static_cast<UnaryOperation*>(candidate)->exp);
                return;
            }
            case StmtKind::DependentUnaryExpr: {
                visit_unique(static_cast<DependentUnaryExpr*>(candidate)->operand);
                return;
            }
            case StmtKind::BinaryOperation: {
                auto* binary = static_cast<BinaryOperation*>(candidate);
                visit_unique(binary->left);
                visit_unique(binary->right);
                return;
            }
            case StmtKind::DependentBinaryExpr: {
                auto* binary = static_cast<DependentBinaryExpr*>(candidate);
                visit_unique(binary->left);
                visit_unique(binary->right);
                return;
            }
            case StmtKind::ArraySubscriptExpr: {
                auto* subscript = static_cast<ArraySubscriptExpr*>(candidate);
                visit_unique(subscript->array);
                visit_unique(subscript->index);
                return;
            }
            case StmtKind::DependentArraySubscriptExpr: {
                auto* subscript =
                    static_cast<DependentArraySubscriptExpr*>(candidate);
                visit_unique(subscript->array);
                visit_unique(subscript->index);
                return;
            }
            case StmtKind::MemberExpr: {
                visit_unique(static_cast<MemberExpr*>(candidate)->base);
                return;
            }
            case StmtKind::UnresolvedMemberExpr: {
                visit_unique(static_cast<UnresolvedMemberExpr*>(candidate)->base);
                return;
            }
            case StmtKind::CppFunctionStyleCastExpr: {
                visit_vector(
                    static_cast<CppFunctionStyleCastExpr*>(candidate)->args);
                return;
            }
            case StmtKind::CppConstructExpr: {
                visit_vector(static_cast<CppConstructExpr*>(candidate)->args);
                return;
            }
            case StmtKind::CppValueInitExpr:
                return;
            default:
                return;
        }
    };

    visit(visit, expr);
}

bool clone_function_parameters_for_specialization(
    Collect& collect,
    const FuncDecl* pattern,
    const TemplateParameterList& template_parameters,
    const TemplateArgumentBindings& specialization_bindings,
    FuncDecl* specialization,
    TemplateSubstitutionPass& substitution_pass,
    TemplateDependentResolutionPass& resolution_pass,
    SrcLoc loc,
    const std::string& failure_context,
    const std::function<QualType(QualType, size_t, std::string*)>&
        rewrite_pack_element_type,
    std::unordered_map<const Symbol*, std::vector<std::shared_ptr<Symbol>>>*
        pack_param_symbol_remap_out,
    std::vector<const Expr*>& default_arguments_out,
    std::string* error_out) {
    if (!pattern || !specialization) {
        return false;
    }

    specialization->parameters.reserve(pattern->parameters.size());
    default_arguments_out.clear();
    for (size_t index = 0; index < pattern->parameters.size(); ++index) {
        auto* pattern_param = dyn_cast<ParamDecl>(pattern->parameters[index].get());
        if (!pattern_param) {
            if (error_out) {
                *error_out =
                    "internal error: expected ParamDecl while cloning " +
                    failure_context;
            }
            return false;
        }

        if (!pattern_param->is_parameter_pack) {
            auto pick_parameter_substitution_pattern =
                [](const ParamDecl* param_decl) -> QualType {
                    if (!param_decl) {
                        return QualType();
                    }
                    QualType original_type(param_decl->original_type);
                    if (original_type &&
                        !auto_type_utils::has_cxx_auto_type(
                            original_type.get_shared())) {
                        return original_type;
                    }
                    return param_decl->type;
                };
            QualType spelled_param_type =
                pick_parameter_substitution_pattern(pattern_param);
            auto substituted_param_type =
                substitution_pass.rewrite_type(spelled_param_type);
            if (auto_type_utils::auto_type_flavors_in(
                    substituted_param_type.get_shared()) != 0) {
                if (error_out) {
                    *error_out =
                        failure_context +
                        " parameter substitution left an unresolved auto placeholder of type '" +
                        substituted_param_type.to_string() + "'";
                }
                return false;
            }
            std::shared_ptr<Symbol> cloned_param_symbol = nullptr;
            if (pattern_param->sym) {
                cloned_param_symbol = clone_symbol_shallow_for_specialization(
                    pattern_param->sym,
                    substituted_param_type);
                collect.collect_add_global_symbol(cloned_param_symbol);
                substitution_pass.context().symbol_remap.emplace(
                    pattern_param->sym.get(),
                    cloned_param_symbol);
            }

            auto cloned_param_decl = collect.collect_make<ParamDecl>(
                substituted_param_type,
                pattern_param->get_name(),
                cloned_param_symbol,
                pattern_param->storage_class,
                pattern_param->location);
            cloned_param_decl->is_constexpr = pattern_param->is_constexpr;
            cloned_param_decl->original_type =
                substitution_pass.rewrite_type(
                    pick_parameter_substitution_pattern(pattern_param)).get_shared();

            if (const Expr* default_expr =
                    get_param_decl_default_argument(pattern_param)) {
                std::string clone_error;
                auto cloned_default =
                    substitution_pass.clone_expr(default_expr, &clone_error);
                if (!cloned_default) {
                    if (error_out) {
                        *error_out =
                            failure_context + " default argument expression is not supported" +
                            (clone_error.empty() ? std::string()
                                                 : ": " + clone_error);
                    }
                    return false;
                }
                if (!resolution_pass.resolve_expr_in_place(
                        cloned_default,
                        &clone_error)) {
                    if (error_out) {
                        *error_out =
                            failure_context +
                            " default argument dependent resolution is not supported" +
                            (clone_error.empty() ? std::string()
                                                 : ": " + clone_error);
                    }
                    return false;
                }
                set_param_decl_default_argument(
                    cloned_param_decl.get(),
                    std::move(cloned_default));
            }

            default_arguments_out.push_back(
                get_param_decl_default_argument(cloned_param_decl.get()));
            specialization->parameters.push_back(std::move(cloned_param_decl));
            continue;
        }

        std::optional<size_t> pack_index;
        if (!find_unique_parameter_pack_index_in_type(
                pattern_param->type,
                template_parameters,
                pack_index)) {
            if (error_out) {
                *error_out =
                    failure_context +
                    " parameter pack substitution currently supports only one pack per parameter type";
            }
            return false;
        }
        if (!pack_index.has_value() || *pack_index >= specialization_bindings.size()) {
            if (error_out) {
                *error_out =
                    "internal error: missing template pack binding while cloning " +
                    failure_context;
            }
            return false;
        }
        const auto& pack_binding = specialization_bindings[*pack_index];
        if (!pack_binding.is_pack()) {
            if (error_out) {
                *error_out =
                    "internal error: template pack binding was not stored as a pack";
            }
            return false;
        }
        if (const Expr* default_expr = get_param_decl_default_argument(pattern_param)) {
            (void)default_expr;
            if (error_out) {
                *error_out =
                    failure_context +
                    " default arguments on function parameter packs are not supported yet";
            }
            return false;
        }

        std::vector<std::shared_ptr<Symbol>> cloned_pack_symbols;
        cloned_pack_symbols.reserve(pack_binding.arguments.size());
        for (size_t element_index = 0;
             element_index < pack_binding.arguments.size();
             ++element_index) {
            if (!rewrite_pack_element_type) {
                if (error_out) {
                    *error_out =
                        failure_context +
                        " parameter pack cloning requires an element-wise type rewriter";
                }
                return false;
            }

            std::string element_error;
            auto substituted_param_type = rewrite_pack_element_type(
                pattern_param->type,
                element_index,
                &element_error);
            if (!substituted_param_type) {
                if (error_out) {
                    *error_out =
                        element_error.empty()
                            ? failure_context + " parameter pack element type rewrite failed"
                            : element_error;
                }
                return false;
            }

            std::shared_ptr<Symbol> cloned_param_symbol = nullptr;
            std::string specialized_name = make_parameter_pack_element_name(
                pattern_param->get_name(),
                element_index);
            if (pattern_param->sym) {
                std::string symbol_type_error;
                cloned_param_symbol = clone_symbol_shallow_for_specialization(
                    pattern_param->sym,
                    rewrite_pack_element_type(
                        pattern_param->sym->type,
                        element_index,
                        &symbol_type_error));
                if (!cloned_param_symbol || !cloned_param_symbol->type) {
                    if (error_out) {
                        *error_out =
                            symbol_type_error.empty()
                                ? failure_context + " parameter-pack symbol type rewrite failed"
                                : symbol_type_error;
                    }
                    return false;
                }
                cloned_param_symbol->name = specialized_name;
                collect.collect_add_global_symbol(cloned_param_symbol);
                cloned_pack_symbols.push_back(cloned_param_symbol);
            }

            auto cloned_param_decl = collect.collect_make<ParamDecl>(
                substituted_param_type,
                specialized_name,
                cloned_param_symbol,
                pattern_param->storage_class,
                pattern_param->location);
            cloned_param_decl->is_constexpr = pattern_param->is_constexpr;
            std::string original_type_error;
            cloned_param_decl->original_type = rewrite_pack_element_type(
                QualType(pattern_param->original_type),
                element_index,
                &original_type_error)
                    .get_shared();
            if (!cloned_param_decl->original_type) {
                if (error_out) {
                    *error_out =
                        original_type_error.empty()
                            ? failure_context + " parameter-pack original type rewrite failed"
                            : original_type_error;
                }
                return false;
            }

            default_arguments_out.push_back(nullptr);
            specialization->parameters.push_back(std::move(cloned_param_decl));
        }
        if (pack_param_symbol_remap_out && pattern_param->sym) {
            (*pack_param_symbol_remap_out)[pattern_param->sym.get()] =
                std::move(cloned_pack_symbols);
        }
    }

    resolution_pass.sync_from_substitution_pass(substitution_pass);

    std::unordered_map<std::string, std::shared_ptr<Symbol>>
        specialized_parameter_symbols_by_name;
    for (const auto& parameter_decl : specialization->parameters) {
        auto* param_decl = dyn_cast<ParamDecl>(parameter_decl.get());
        if (!param_decl || !param_decl->sym || param_decl->get_name().empty()) {
            continue;
        }
        specialized_parameter_symbols_by_name.emplace(
            param_decl->get_name(),
            param_decl->sym);
    }

    auto rebuilt_function_type =
        desugar_type(
            substitution_pass.rewrite_type(QualType(pattern->type)),
            substitution_pass.context().ast_ctx)
            .as_shared<FunctionType>();
    if (!rebuilt_function_type) {
        if (error_out) {
            *error_out =
                "internal error: expected function type while rebuilding " +
                failure_context;
        }
        return false;
    }
    auto specialized_function_type =
        std::make_shared<FunctionType>(*rebuilt_function_type);
    rebuilt_function_type = specialized_function_type;

    auto pattern_function_type =
        desugar_type(QualType(pattern->type), substitution_pass.context().ast_ctx)
            .as_shared<FunctionType>();
    if (pattern_function_type) {
        auto rewritten_decltype =
            rebuilt_function_type->ret_type.as_shared<DecltypeExprType>();
        if (rewritten_decltype) {
            const auto* source_decltype = rewritten_decltype.get();
            if (auto pattern_decltype =
                    pattern_function_type->ret_type.as_shared<DecltypeExprType>()) {
                source_decltype = pattern_decltype.get();
            }

            if (source_decltype && source_decltype->expr) {
                std::string clone_error;
                auto cloned_expr = substitution_pass.clone_expr(
                    source_decltype->expr.get(),
                    &clone_error);
                if (!cloned_expr) {
                    if (error_out) {
                        *error_out =
                            failure_context +
                            " decltype return expression cloning is not supported" +
                            (clone_error.empty() ? std::string()
                                                 : ": " + clone_error);
                    }
                    return false;
                }
                rewrite_stale_parameter_refs_by_name(
                    cloned_expr.get(),
                    specialized_parameter_symbols_by_name,
                    substitution_pass.context().ast_ctx);

                QualType realized_return_type;
                constexpr unsigned kMaxDecltypeReturnResolutionPasses = 8;
                // The decltype operand was collected as unevaluated already;
                // this loop only completes staged overload/dependent-call
                // resolution now that specialization parameters are concrete.
                for (unsigned pass = 0;
                     pass < kMaxDecltypeReturnResolutionPasses;
                     ++pass) {
                    if (!resolution_pass.resolve_expr_in_place(
                            cloned_expr,
                            &clone_error) ||
                        !cloned_expr) {
                        if (error_out) {
                            *error_out =
                                failure_context +
                                " decltype return dependent resolution is not supported" +
                                (clone_error.empty() ? std::string()
                                                     : ": " + clone_error);
                        }
                        return false;
                    }

                    auto probe_expr = std::shared_ptr<Expr>(
                        cloned_expr.get(),
                        [](Expr*) {});
                    auto probe_decltype = QualType(
                        std::make_shared<DecltypeExprType>(
                            std::move(probe_expr),
                            source_decltype->use_declared_type_rule),
                        rebuilt_function_type->ret_type.get_qualifiers());
                    auto realized_decltype =
                        collect.collect_try_realize_deferred_semantic_type(
                            probe_decltype);
                    if (realized_decltype &&
                        !isa<DecltypeExprType>(realized_decltype.get())) {
                        realized_return_type = realized_decltype;
                        break;
                    }
                }

                if (realized_return_type) {
                    rebuilt_function_type->ret_type = realized_return_type;
                } else {
                    auto resolved_decltype = QualType(
                        std::make_shared<DecltypeExprType>(
                            std::shared_ptr<Expr>(cloned_expr.release()),
                            source_decltype->use_declared_type_rule),
                        rebuilt_function_type->ret_type.get_qualifiers());
                    auto realized_decltype =
                        collect.collect_try_realize_deferred_semantic_type(
                            resolved_decltype);
                    if (realized_decltype) {
                        rebuilt_function_type->ret_type = realized_decltype;
                    } else {
                        rebuilt_function_type->ret_type = resolved_decltype;
                    }
                }
            }
        }
    }

    rebuilt_function_type->clear_parameters();
    rebuilt_function_type->parameters.reserve(specialization->parameters.size());
    rebuilt_function_type->parameter_pack_flags.reserve(
        specialization->parameters.size());
    for (const auto& parameter_decl : specialization->parameters) {
        auto* param_decl = dyn_cast<ParamDecl>(parameter_decl.get());
        if (!param_decl) {
            continue;
        }
        rebuilt_function_type->push_parameter(
            param_decl->type,
            param_decl->is_parameter_pack);
    }
    specialization->type = rebuilt_function_type;

    return true;
}

bool clone_function_body_for_specialization(Collect& collect,
                                            const FuncDecl* pattern,
                                            FuncDecl* specialization,
                                            TemplateSubstitutionPass& substitution_pass,
                                            TemplateDependentResolutionPass& resolution_pass,
                                            const std::string& failure_context,
                                            bool finalize_body_semantics,
                                            std::string* error_out) {
    if (!pattern || !specialization) {
        return false;
    }
    if (!pattern->body) {
        specialization->stmt_labels = pattern->stmt_labels;
        return true;
    }

    std::string clone_error;
    auto cloned_body =
        substitution_pass.clone_stmt(pattern->body.get(), &clone_error);
    if (!cloned_body) {
        if (error_out) {
            *error_out =
                failure_context + " body cloning is not supported" +
                (clone_error.empty() ? std::string() : ": " + clone_error);
        }
        return false;
    }
    enum class BodyCloneFailurePhase {
        None,
        DependentResolution,
        SemanticFinalization,
    };
    BodyCloneFailurePhase failure_phase = BodyCloneFailurePhase::None;
    if (!collect.with_function_definition_state(
            specialization,
            [&]() {
                if (!resolution_pass.resolve_stmt_in_place(
                        cloned_body,
                        &clone_error)) {
                    failure_phase = BodyCloneFailurePhase::DependentResolution;
                    return false;
                }
                if (finalize_body_semantics &&
                    !finalize_specialized_stmt_semantics(
                        collect,
                        cloned_body,
                        QualType(specialization->type),
                        &clone_error)) {
                    failure_phase = BodyCloneFailurePhase::SemanticFinalization;
                    return false;
                }
                return true;
            })) {
        if (error_out) {
            const char* phase_message =
                failure_phase == BodyCloneFailurePhase::DependentResolution
                    ? " dependent body resolution is not supported"
                    : " body semantic finalization is not supported";
            *error_out =
                failure_context + phase_message +
                (clone_error.empty() ? std::string() : ": " + clone_error);
        }
        return false;
    }
    specialization->body = std::move(cloned_body);
    specialization->stmt_labels = pattern->stmt_labels;
    if (pattern->scope) {
        auto scope_it =
            substitution_pass.context().scope_remap.find(pattern->scope.get());
        if (scope_it != substitution_pass.context().scope_remap.end()) {
            specialization->scope = scope_it->second;
        }
    }
    return true;
}

bool clone_ctor_initializers_for_specialization(
    const CppConstructorDecl* pattern,
    CppConstructorDecl* specialization,
    TemplateSubstitutionPass& substitution_pass,
    TemplateDependentResolutionPass& resolution_pass,
    std::string* error_out) {
    if (!pattern || !specialization) {
        return false;
    }
    specialization->ctor_initializers.reserve(pattern->ctor_initializers.size());
    for (const auto& initializer : pattern->ctor_initializers) {
        CppCtorInitializer cloned_initializer;
        cloned_initializer.member_name = initializer.member_name;
        cloned_initializer.is_base_initializer = initializer.is_base_initializer;
        cloned_initializer.is_delegating_initializer =
            initializer.is_delegating_initializer;
        cloned_initializer.is_list_init = initializer.is_list_init;
        cloned_initializer.location = initializer.location;

        if (initializer.member_expr) {
            std::string clone_error;
            cloned_initializer.member_expr = substitution_pass.clone_expr(
                initializer.member_expr.get(),
                &clone_error);
            if (!cloned_initializer.member_expr) {
                if (error_out) {
                    *error_out =
                        "constructor member initializer clone is not supported" +
                        (clone_error.empty() ? std::string()
                                             : ": " + clone_error);
                }
                return false;
            }
            if (!resolution_pass.resolve_expr_in_place(
                    cloned_initializer.member_expr,
                    &clone_error)) {
                if (error_out) {
                    *error_out =
                        "constructor member initializer dependent resolution is not supported" +
                        (clone_error.empty() ? std::string()
                                             : ": " + clone_error);
                }
                return false;
            }
        }
        if (initializer.init_expr) {
            std::string clone_error;
            cloned_initializer.init_expr = substitution_pass.clone_expr(
                initializer.init_expr.get(),
                &clone_error);
            if (!cloned_initializer.init_expr) {
                if (error_out) {
                    *error_out =
                        "constructor member initializer expression clone is not supported" +
                        (clone_error.empty() ? std::string()
                                             : ": " + clone_error);
                }
                return false;
            }
            if (!resolution_pass.resolve_expr_in_place(
                    cloned_initializer.init_expr,
                    &clone_error)) {
                if (error_out) {
                    *error_out =
                        "constructor member initializer expression dependent resolution is not supported" +
                        (clone_error.empty() ? std::string()
                                             : ": " + clone_error);
                }
                return false;
            }
        }
        specialization->ctor_initializers.push_back(std::move(cloned_initializer));
    }
    return true;
}

bool substitute_cpp_explicit_specifier_for_specialization(
    Collect& collect,
    const CppExplicitSpecifier& pattern,
    CppExplicitSpecifier& specialization,
    TemplateSubstitutionPass& substitution_pass,
    TemplateDependentResolutionPass& resolution_pass,
    SrcLoc loc,
    std::string* error_out) {
    specialization = pattern;
    if (!pattern.is_present) {
        return true;
    }
    if (!pattern.is_conditional || !pattern.condition) {
        specialization.is_dependent = false;
        specialization.effective_value = true;
        return true;
    }

    std::string clone_error;
    auto cloned_condition =
        substitution_pass.clone_expr(pattern.condition.get(), &clone_error);
    if (!cloned_condition) {
        if (error_out) {
            *error_out =
                clone_error.empty()
                    ? "failed to substitute explicit specifier expression"
                    : clone_error;
        }
        return false;
    }
    if (!resolution_pass.resolve_expr_in_place(cloned_condition, &clone_error)) {
        if (error_out) {
            *error_out =
                clone_error.empty()
                    ? "failed to resolve explicit specifier expression after substitution"
                    : clone_error;
        }
        return false;
    }

    bool is_dependent =
        collect.expression_depends_on_template_parameters(
            cloned_condition.get()) ||
        type_depends_on_template_parameters(
            cloned_condition ? cloned_condition->get_type() : QualType());
    specialization.condition = std::shared_ptr<Expr>(cloned_condition.release());
    specialization.is_dependent = is_dependent;
    if (is_dependent) {
        specialization.effective_value = true;
        return true;
    }

    auto eval = try_evaluate_with_consteval_compat(
        specialization.condition.get(),
        ConstEvalMode::cpp_core_constant_expression());
    if (!eval.has_value()) {
        if (error_out) {
            *error_out =
                "explicit specifier expression must be an integer constant expression";
        }
        (void)loc;
        return false;
    }
    specialization.effective_value = *eval != 0;
    return true;
}

} // namespace template_sema_internal
