#include "collect.h"
#include "collect_templates_internal.h"
#include "../helpers/auto_type_utils.h"

#include <optional>

using template_sema_internal::build_pack_element_argument_bindings;
using template_sema_internal::build_pack_element_argument_bindings_for_shape;
using template_sema_internal::classify_parameter_pack_reference_in_type;
using template_sema_internal::collect_pack_expansion_shape_in_expr;
using template_sema_internal::collect_pack_expansion_shape_in_template_argument;
using template_sema_internal::find_pack_expansion_arity_for_bindings;
using template_sema_internal::find_template_parameter_index_by_identity;
using template_sema_internal::find_template_parameter_index_by_decl;
using template_sema_internal::make_template_binding_clone_pass_builder;
using template_sema_internal::materialize_specialized_fold_expression;
using template_sema_internal::normalize_concrete_template_value_argument;
using template_sema_internal::TemplateClonePassBuilder;
using template_sema_internal::TemplatePackReferenceResolutionKind;
using template_sema_internal::template_arguments_depend_on_template_parameters;
using template_sema_internal::TemplateSubstitutionPass;

namespace {

// Looks up a template argument binding for a given parameter.
// allow_index_fallback controls whether raw-index lookup is permitted:
//   true  — normal substitution; index fallback is safe
//   false — partial-specialization owner substitution; index fallback
//           would let outer bindings cross-bind inner member-template
//           parameters that happen to share the same index
// When allow_index_fallback is false and identity match fails, nullptr
// is returned (not an error).  The caller interprets this as "this
// parameter is not substitutable in this context" and preserves it.
const TemplateArgument* find_template_argument_for_parameter(
    const TemplateTypeParmType* parm_type,
    const TemplateParameterList& parameters,
    const TemplateArgumentBindings& specialization_bindings,
    bool allow_index_fallback) {
    if (!parm_type) {
        return nullptr;
    }
    if (parm_type->parameter_decl) {
        for (size_t idx = 0; idx < parameters.size(); ++idx) {
            if (parameters[idx].get() == parm_type->parameter_decl) {
                if (idx >= specialization_bindings.size()) {
                    return nullptr;
                }
                return specialization_bindings[idx].single_argument();
            }
        }
        if (!allow_index_fallback) {
            // Partial owner substitution must not fall back by raw index,
            // otherwise outer bindings can cross-bind nested template
            // parameter lists (for example owner `T` substitution rewriting
            // inner member-template `U`).
            return nullptr;
        }
    }
    if (allow_index_fallback && parm_type->index < specialization_bindings.size()) {
        return specialization_bindings[parm_type->index].single_argument();
    }
    return nullptr;
}

const TemplateArgument* find_template_argument_for_non_type_parameter_symbol(
    const Symbol* sym,
    const TemplateParameterList& parameters,
    const TemplateArgumentBindings& specialization_bindings) {
    if (!sym) {
        return nullptr;
    }
    for (size_t idx = 0; idx < parameters.size() &&
                         idx < specialization_bindings.size();
         ++idx) {
        const auto* non_type_parameter =
            dyn_cast<TemplateNonTypeParmDecl>(parameters[idx].get());
        if (!non_type_parameter) {
            continue;
        }
        if (non_type_parameter->sym.get() == sym) {
            return specialization_bindings[idx].single_argument();
        }
        if (!non_type_parameter->sym || !sym->is_constexpr) {
            continue;
        }
        if (non_type_parameter->name != sym->name) {
            continue;
        }
        if (!non_type_parameter->type.equals_qualified(sym->type)) {
            continue;
        }
        return specialization_bindings[idx].single_argument();
    }
    return nullptr;
}

using FinishSubstitutedPackPatternElement =
    std::function<bool(std::unique_ptr<Expr>&,
                       const TemplateArgumentBindings&,
                       const TemplateClonePassBuilder&,
                       const TemplateSubstitutionPass&,
                       std::string*)>;
using RewriteSubstitutedPackElementType =
    std::function<QualType(QualType, const TemplateArgumentBindings&)>;
using RewriteSubstitutedPackElementArguments =
    std::function<std::vector<TemplateArgument>(
        const std::vector<TemplateArgument>&,
        const TemplateArgumentBindings&)>;

// Shared setup for substitution paths that materialize pack-driven patterns:
// bind the selected pack element, clone the pattern under those bindings, then let
// the caller run its path-specific resolution.
std::unique_ptr<Expr> clone_substituted_pack_pattern_element(
    Collect& collect,
    ASTContext* ast_ctx,
    const TemplateParameterList& parameters,
    const TemplateArgumentBindings& active_bindings,
    const template_sema_internal::TemplatePackExpansionShape* expansion_shape,
    ASTCloneContext* clone_context,
    size_t element_index,
    const Expr* pattern_expr,
    SrcLoc loc,
    const char* binding_error_message,
    const char* value_error_message,
    const char* clone_error_message,
    const RewriteSubstitutedPackElementType& rewrite_type_for_bindings,
    const RewriteSubstitutedPackElementArguments&
        rewrite_arguments_for_bindings,
    const FinishSubstitutedPackPatternElement& finish_element,
    std::string* error_out) {
    TemplateArgumentBindings element_bindings;
    std::string binding_error;
    bool built_bindings = expansion_shape
        ? build_pack_element_argument_bindings_for_shape(
              parameters,
              active_bindings,
              *expansion_shape,
              element_index,
              element_bindings,
              &binding_error)
        : build_pack_element_argument_bindings(
              parameters,
              active_bindings,
              element_index,
              element_bindings,
              &binding_error);
    if (!built_bindings) {
        if (error_out && error_out->empty()) {
            *error_out =
                binding_error.empty() ? binding_error_message : binding_error;
        }
        return nullptr;
    }

    auto rewrite_element_type =
        [&](QualType nested_type) -> QualType {
            return rewrite_type_for_bindings(
                nested_type,
                element_bindings);
        };
    auto rewrite_element_arguments =
        [&](const std::vector<TemplateArgument>& template_arguments)
        -> std::vector<TemplateArgument> {
            return rewrite_arguments_for_bindings(
                template_arguments,
                element_bindings);
        };
    auto element_builder =
        make_template_binding_clone_pass_builder(
            ast_ctx,
            &collect,
            parameters,
            element_bindings,
            loc,
            value_error_message,
            rewrite_element_type,
            rewrite_element_arguments,
            {},
            {});
    if (clone_context) {
        element_builder.symbol_remap = clone_context->symbol_remap;
        element_builder.scope_remap = clone_context->scope_remap;
    }
    auto element_clone_pass = element_builder.build_substitution_pass();

    std::string clone_error;
    auto element_expr = element_clone_pass.clone_expr(
        pattern_expr,
        &clone_error);
    if (!element_expr) {
        if (error_out && error_out->empty()) {
            *error_out = clone_error.empty() ? clone_error_message
                                             : clone_error;
        }
        return nullptr;
    }

    if (!finish_element(
            element_expr,
            element_bindings,
            element_builder,
            element_clone_pass,
            error_out)) {
        return nullptr;
    }
    return element_expr;
}

void inherit_clone_context_symbol_remaps(TemplateClonePassBuilder& builder,
                                         ASTCloneContext* clone_context);

std::unique_ptr<Expr> clone_preserved_substituted_pack_expansion(
    Collect& collect,
    ASTContext* ast_ctx,
    const TemplateParameterList& parameters,
    const TemplateArgumentBindings& active_bindings,
    ASTCloneContext* clone_context,
    SrcLoc loc,
    const Expr* pattern_expr,
    const char* value_error_message,
    const char* preserve_error_message,
    const RewriteSubstitutedPackElementType& rewrite_type_for_bindings,
    const RewriteSubstitutedPackElementArguments&
        rewrite_arguments_for_bindings,
    std::string* error_out) {
    auto preserve_builder =
        make_template_binding_clone_pass_builder(
            ast_ctx,
            &collect,
            parameters,
            active_bindings,
            loc,
            value_error_message,
            [&](QualType type) -> QualType {
                return rewrite_type_for_bindings(type, active_bindings);
            },
            [&](const std::vector<TemplateArgument>& template_arguments)
                -> std::vector<TemplateArgument> {
                return rewrite_arguments_for_bindings(
                    template_arguments,
                    active_bindings);
            },
            {},
            {});
    inherit_clone_context_symbol_remaps(preserve_builder, clone_context);
    auto preserve_pass = preserve_builder.build_substitution_pass();
    preserve_pass.context().preserve_unexpanded_pack_expansions = true;

    std::string clone_error;
    auto cloned_pattern = preserve_pass.clone_expr(pattern_expr, &clone_error);
    if (!cloned_pattern) {
        if (error_out && error_out->empty()) {
            *error_out =
                clone_error.empty() ? preserve_error_message : clone_error;
        }
        return nullptr;
    }
    return std::make_unique<PackExpansionExpr>(
        std::move(cloned_pattern),
        pattern_expr ? pattern_expr->location : loc);
}

bool expand_substituted_pack_expression(
    Collect& collect,
    ASTContext* ast_ctx,
    const TemplateParameterList& parameters,
    const TemplateArgumentBindings& active_bindings,
    ASTCloneContext* clone_context,
    SrcLoc loc,
    const Expr* pattern_expr,
    std::vector<std::unique_ptr<Expr>>& expanded_out,
    const char* shape_error_message,
    const char* empty_shape_error_message,
    const char* binding_error_message,
    const char* value_error_message,
    const char* clone_error_message,
    const char* preserve_error_message,
    const RewriteSubstitutedPackElementType& rewrite_type_for_bindings,
    const RewriteSubstitutedPackElementArguments&
        rewrite_arguments_for_bindings,
    const FinishSubstitutedPackPatternElement& finish_element,
    std::string* error_out) {
    auto preserve = [&]() -> bool {
        auto preserved =
            clone_preserved_substituted_pack_expansion(
                collect,
                ast_ctx,
                parameters,
                active_bindings,
                clone_context,
                loc,
                pattern_expr,
                value_error_message,
                preserve_error_message,
                rewrite_type_for_bindings,
                rewrite_arguments_for_bindings,
                error_out);
        if (!preserved) {
            return false;
        }
        expanded_out.clear();
        expanded_out.push_back(std::move(preserved));
        return true;
    };

    template_sema_internal::TemplatePackExpansionShape shape;
    if (!collect_pack_expansion_shape_in_expr(
            pattern_expr,
            parameters,
            shape)) {
        if (shape.has_unsupported_dependency) {
            return preserve();
        }
        if (error_out && error_out->empty()) {
            *error_out = shape_error_message;
        }
        return false;
    }
    if (shape.has_unsupported_dependency) {
        return preserve();
    }
    if (shape.referenced_parameters.empty()) {
        if (error_out && error_out->empty()) {
            *error_out = empty_shape_error_message;
        }
        return false;
    }

    std::string arity_error;
    auto expansion_arity =
        find_pack_expansion_arity_for_bindings(
            shape,
            parameters,
            active_bindings,
            &arity_error);
    if (!expansion_arity.has_value()) {
        if (arity_error.empty()) {
            return preserve();
        }
        if (error_out && error_out->empty()) {
            *error_out = arity_error;
        }
        return false;
    }

    expanded_out.clear();
    expanded_out.reserve(*expansion_arity);
    for (size_t element_index = 0;
         element_index < *expansion_arity;
         ++element_index) {
        auto element_expr =
            clone_substituted_pack_pattern_element(
                collect,
                ast_ctx,
                parameters,
                active_bindings,
                &shape,
                clone_context,
                element_index,
                pattern_expr,
                loc,
                binding_error_message,
                value_error_message,
                clone_error_message,
                rewrite_type_for_bindings,
                rewrite_arguments_for_bindings,
                finish_element,
                error_out);
        if (!element_expr) {
            return false;
        }
        expanded_out.push_back(std::move(element_expr));
    }
    return true;
}

const Expr* integer_pack_size_operand_from_expr(const Expr* expr) {
    auto strip_implicit_casts_and_parens = [](const Expr* candidate) -> Expr* {
        auto* stripped =
            Collect::strip_implicit_casts(const_cast<Expr*>(candidate));
        while (auto* paren = dyn_cast<ParenExpr>(stripped)) {
            stripped = Collect::strip_implicit_casts(paren->subexpr.get());
        }
        return stripped;
    };

    auto* stripped = strip_implicit_casts_and_parens(expr);
    if (const auto* builtin = dyn_cast<BuiltinCallExpr>(stripped);
        builtin && builtin->kind == BuiltinKind::INTEGER_PACK &&
        builtin->args.size() == 1) {
        return builtin->args.front().get();
    }
    if (const auto* dependent_call = dyn_cast<DependentCallExpr>(stripped)) {
        const auto* callee_ref = dyn_cast<VarRef>(
            strip_implicit_casts_and_parens(dependent_call->callee.get()));
        if (callee_ref && callee_ref->get_name() == "__integer_pack" &&
            dependent_call->args.size() == 1) {
            return dependent_call->args.front().get();
        }
    }
    if (const auto* call = dyn_cast<FuncCall>(stripped)) {
        const auto* callee_ref = dyn_cast<VarRef>(
            strip_implicit_casts_and_parens(call->func.get()));
        if (callee_ref && callee_ref->get_name() == "__integer_pack" &&
            call->args.size() == 1) {
            return call->args.front().get();
        }
    }
    return nullptr;
}

bool is_integer_pack_template_argument(const TemplateArgument& argument) {
    if (argument.kind != TemplateArgumentKind::Value ||
        !argument.expands_parameter_pack ||
        !argument.value_expr) {
        return false;
    }
    return integer_pack_size_operand_from_expr(argument.value_expr.get()) != nullptr;
}

void inherit_clone_context_symbol_remaps(TemplateClonePassBuilder& builder,
                                         ASTCloneContext* clone_context) {
    if (!clone_context) {
        return;
    }
    builder.symbol_remap = clone_context->symbol_remap;
    builder.scope_remap = clone_context->scope_remap;
}

void remap_template_argument_symbols_for_substitution(
    TemplateArgument& argument,
    ASTCloneContext* clone_context) {
    if (!clone_context) {
        return;
    }
    template_sema_internal::remap_template_argument_symbol_references(
        argument,
        *clone_context);
}

bool substituted_value_argument_depends_on_template_parameters(
    const Collect& collect,
    const TemplateArgument& argument,
    const ASTContext* ast_ctx) {
    if (argument.kind != TemplateArgumentKind::Value) {
        return false;
    }
    if (template_argument_depends_on_template_parameters(argument, ast_ctx)) {
        return true;
    }
    return argument.value_expr &&
           collect.expression_depends_on_template_parameters(
               argument.value_expr.get());
}

bool append_integer_pack_template_arguments(
    Collect& collect,
    ASTContext* ast_ctx,
    const TemplateArgument& argument,
    const TemplateParameterList& parameters,
    const TemplateArgumentBindings& active_bindings,
    ASTCloneContext* clone_context,
    SrcLoc loc,
    bool allow_unsubstituted_parameters,
    const std::function<QualType(QualType)>& rewrite_type,
    const std::function<std::vector<TemplateArgument>(
        const std::vector<TemplateArgument>&)>& rewrite_template_arguments,
    const std::function<void(const std::string&, SrcLoc)>& report_error,
    QualType fallback_value_type,
    std::vector<TemplateArgument>& rewritten) {
    auto clone_pass_builder =
        make_template_binding_clone_pass_builder(
            ast_ctx,
            &collect,
            parameters,
            active_bindings,
            loc,
            "__integer_pack argument requires a concrete integral value",
            rewrite_type,
            rewrite_template_arguments,
            {},
            {});
    inherit_clone_context_symbol_remaps(clone_pass_builder, clone_context);
    auto clone_pass = clone_pass_builder.build_substitution_pass();

    std::string clone_error;
    auto cloned_expr = clone_pass.clone_expr(
        argument.value_expr.get(),
        &clone_error);
    if (!cloned_expr) {
        if (allow_unsubstituted_parameters) {
            rewritten.push_back(argument);
            return true;
        }
        report_error(
            clone_error.empty()
                ? "failed to substitute __integer_pack expression"
                : clone_error,
            loc);
        return false;
    }

    std::string resolve_error;
    if (!collect.resolve_dependent_expr_after_substitution(
            cloned_expr,
            QualType(),
            &resolve_error)) {
        if (allow_unsubstituted_parameters) {
            rewritten.push_back(argument);
            return true;
        }
        report_error(
            resolve_error.empty()
                ? "failed to resolve __integer_pack expression after substitution"
                : resolve_error,
            loc);
        return false;
    }

    const Expr* size_operand =
        integer_pack_size_operand_from_expr(cloned_expr.get());
    if (!size_operand) {
        report_error("invalid __integer_pack expression", loc);
        return false;
    }

    ConstEvalResult eval = evaluate_with_consteval_compat(
        const_cast<Expr*>(size_operand),
        ConstEvalMode::cpp_non_type_template_argument());
    if (eval.status != ConstEvalStatus::Constant ||
        !eval.value.has_value() ||
        eval.value->kind != ConstValueKind::Integer) {
        if (allow_unsubstituted_parameters) {
            rewritten.push_back(argument);
            return true;
        }
        report_error(
            "__integer_pack argument must be an integral constant expression",
            loc);
        return false;
    }

    const auto& size_value = eval.value->int_value;
    if (!size_value.is_unsigned && size_value.to_signed_i64() < 0) {
        report_error(
            "__integer_pack argument must be non-negative",
            loc);
        return false;
    }

    uint64_t pack_size = size_value.to_unsigned_u64();
    QualType element_value_type = rewrite_type(argument.value_type);
    if (!element_value_type) {
        element_value_type = fallback_value_type;
    }

    for (uint64_t idx = 0; idx < pack_size; ++idx) {
        rewritten.push_back(TemplateArgument::value_argument(
            element_value_type,
            ConstValue::integer(ConstIntValue::from_unsigned(idx, 64)),
            std::to_string(idx)));
    }
    return true;
}

} // namespace

QualType Collect::substitute_template_type(
    QualType type,
    const TemplateParameterList& parameters,
    const std::vector<TemplateArgument>& specialization_arguments,
    SrcLoc loc) {
    TemplateArgumentBindings argument_bindings;
    std::string binding_error;
    if (!bind_template_arguments_to_parameters(
            parameters,
            specialization_arguments,
            argument_bindings,
            &binding_error)) {
        report_error(
            binding_error.empty()
                ? "internal error: failed to align template arguments with parameters"
                : binding_error,
            loc);
        return type;
    }
    return substitute_template_type_with_bindings(
        type,
        parameters,
        argument_bindings,
        loc);
}

QualType Collect::partially_substitute_template_type(
    QualType type,
    const TemplateParameterList& parameters,
    const std::vector<TemplateArgument>& specialization_arguments,
    SrcLoc loc) {
    TemplateArgumentBindings argument_bindings;
    std::string binding_error;
    if (!bind_template_arguments_to_parameters(
            parameters,
            specialization_arguments,
            argument_bindings,
            &binding_error)) {
        report_error(
            binding_error.empty()
                ? "internal error: failed to align template arguments with parameters"
                : binding_error,
            loc);
        return type;
    }
    return substitute_template_type_with_bindings(
        type,
        parameters,
        argument_bindings,
        loc,
        true);
}

QualType Collect::substitute_template_type_with_bindings(
    QualType type,
    const TemplateParameterList& parameters,
    const TemplateArgumentBindings& argument_bindings,
    SrcLoc loc,
    bool allow_unsubstituted_parameters,
    ASTCloneContext* clone_context) {
    if (!type) {
        return type;
    }

    auto raw = type.get_shared();
    uint8_t quals = type.get_qualifiers();
    auto clone_expr_for_expression_type_substitution =
        [&](const std::shared_ptr<Expr>& expr) -> std::shared_ptr<Expr> {
            if (!expr) {
                return nullptr;
            }

            auto rewrite_bound_template_type =
                [&](QualType nested_type) -> QualType {
                    return substitute_template_type_with_bindings(
                        nested_type,
                        parameters,
                        argument_bindings,
                        loc,
                        allow_unsubstituted_parameters,
                        clone_context);
                };
            auto rewrite_bound_template_arguments =
                [&](const std::vector<TemplateArgument>& template_arguments)
                -> std::vector<TemplateArgument> {
                    auto rewritten = substitute_template_arguments_with_bindings(
                        template_arguments,
                        parameters,
                        argument_bindings,
                        loc,
                        allow_unsubstituted_parameters,
                        clone_context);
                    for (auto& argument : rewritten) {
                        if (argument.kind == TemplateArgumentKind::Type) {
                            if (auto realized =
                                    try_realize_deferred_semantic_type(
                                        argument.type)) {
                                argument.type = realized;
                                argument.is_dependent =
                                    type_depends_on_template_parameters(
                                        argument.type,
                                        ast_ctx_.get());
                            }
                        } else if (argument.kind == TemplateArgumentKind::Value) {
                            if (auto realized =
                                    try_realize_deferred_semantic_type(
                                        argument.value_type)) {
                                argument.value_type = realized;
                                argument.is_dependent =
                                    argument.is_dependent ||
                                    type_depends_on_template_parameters(
                                        argument.value_type,
                                        ast_ctx_.get());
                            }
                        }
                    }
                    return rewritten;
                };

            auto clone_pass_builder = make_template_binding_clone_pass_builder(
                ast_ctx_.get(),
                this,
                parameters,
                argument_bindings,
                loc,
                "failed to substitute expression-bearing deferred type",
                rewrite_bound_template_type,
                rewrite_bound_template_arguments,
                {},
                {});
            inherit_clone_context_symbol_remaps(clone_pass_builder, clone_context);
            std::function<bool(std::unique_ptr<Expr>&,
                               const TemplateArgumentBindings&,
                               std::string*)>
                resolve_specialized_expr;
            auto materialize_substituted_type_value_initializer =
                [&](std::unique_ptr<Expr>& candidate,
                    const TemplateArgumentBindings& active_bindings,
                    std::string* error_out) -> bool {
                    if (!candidate) {
                        return true;
                    }

                    if (auto* dependent_call =
                            dyn_cast<DependentCallExpr>(candidate.get())) {
                        auto* callee_ref = dyn_cast<VarRef>(
                            strip_implicit_casts(dependent_call->callee.get()));
                        auto parm_type = callee_ref && callee_ref->symref &&
                                         callee_ref->symref->kind ==
                                             SymbolKind::TYPE
                            ? callee_ref->symref->type
                                  .as_shared<TemplateTypeParmType>()
                            : nullptr;
                        const TemplateArgument* replacement = parm_type
                            ? find_template_argument_for_parameter(
                                  parm_type.get(),
                                  parameters,
                                  active_bindings,
                                  !allow_unsubstituted_parameters)
                            : nullptr;
                        if (replacement &&
                            replacement->kind == TemplateArgumentKind::Type &&
                            !replacement->type.is_null() &&
                            !type_depends_on_template_parameters(
                                replacement->type,
                                ast_ctx_.get())) {
                            candidate = collect_cpp_function_style_cast(
                                replacement->type,
                                std::move(dependent_call->args),
                                dependent_call->location);
                            return candidate != nullptr;
                        }
                    }
                    if (auto* function_style_cast =
                            dyn_cast<CppFunctionStyleCastExpr>(
                                candidate.get())) {
                        bool still_dependent =
                            type_depends_on_template_parameters(
                                function_style_cast->target_type,
                                ast_ctx_.get());
                        for (const auto& arg : function_style_cast->args) {
                            if (!arg) {
                                continue;
                            }
                            if (expression_depends_on_template_parameters(
                                    arg.get()) ||
                                type_depends_on_template_parameters(
                                    arg->get_type(),
                                    ast_ctx_.get())) {
                                still_dependent = true;
                                break;
                            }
                        }
                        if (!still_dependent) {
                            if (function_style_cast->is_list_init) {
                                auto init_list = collect_make<InitListExpr>(
                                    function_style_cast->location);
                                init_list->elements.reserve(
                                    function_style_cast->args.size());
                                for (auto& arg : function_style_cast->args) {
                                    InitElement element;
                                    element.value = std::move(arg);
                                    element.loc = element.value
                                        ? element.value->location
                                        : function_style_cast->location;
                                    init_list->elements.push_back(
                                        std::move(element));
                                }
                                candidate =
                                    collect_cpp_type_list_initialization_expression(
                                        function_style_cast->target_type,
                                        std::move(init_list),
                                        function_style_cast->location);
                            } else {
                                candidate = collect_cpp_function_style_cast(
                                    function_style_cast->target_type,
                                    std::move(function_style_cast->args),
                                    function_style_cast->location);
                            }
                            return true;
                        }
                        if (function_style_cast->is_list_init &&
                            !type_depends_on_template_parameters(
                                function_style_cast->target_type,
                                ast_ctx_.get())) {
                            auto init_list = collect_make<InitListExpr>(
                                function_style_cast->location);
                            init_list->elements.reserve(
                                function_style_cast->args.size());
                            for (auto& arg : function_style_cast->args) {
                                InitElement element;
                                element.value = std::move(arg);
                                element.loc = element.value
                                    ? element.value->location
                                    : function_style_cast->location;
                                init_list->elements.push_back(
                                    std::move(element));
                            }
                            candidate =
                                collect_cpp_type_list_initialization_expression(
                                    function_style_cast->target_type,
                                    std::move(init_list),
                                    function_style_cast->location);
                            return true;
                        }
                    }
                    return true;
                };
            auto rewrite_substituted_pack_element_type =
                [&](QualType nested_type,
                    const TemplateArgumentBindings& element_bindings)
                -> QualType {
                    auto rewritten_type =
                        substitute_template_type_with_bindings(
                            nested_type,
                            parameters,
                            element_bindings,
                            loc,
                            allow_unsubstituted_parameters,
                            clone_context);
                    return finalize_deferred_semantic_type(
                        rewritten_type,
                        loc);
                };
            auto rewrite_substituted_pack_element_arguments =
                [&](const std::vector<TemplateArgument>& template_arguments,
                    const TemplateArgumentBindings& element_bindings)
                -> std::vector<TemplateArgument> {
                    return substitute_template_arguments_with_bindings(
                        template_arguments,
                        parameters,
                        element_bindings,
                        loc,
                        allow_unsubstituted_parameters,
                        clone_context);
                };
            clone_pass_builder.expand_pack_expansion =
                [&](const Expr* pattern_expr,
                    std::vector<std::unique_ptr<Expr>>& expanded_out,
                    std::string* error_out) -> bool {
                    return expand_substituted_pack_expression(
                        *this,
                        ast_ctx_.get(),
                        parameters,
                        argument_bindings,
                        clone_context,
                        loc,
                        pattern_expr,
                        expanded_out,
                        "failed to collect expression type pack expansion shape",
                        "pack expansion expression does not reference a template parameter pack",
                        "failed to materialize expression type pack expansion bindings",
                        "failed to substitute expression type pack expansion pattern",
                        "expression type pack expansion pattern cloning is not supported",
                        "failed to preserve unexpanded pack expansion",
                        rewrite_substituted_pack_element_type,
                        rewrite_substituted_pack_element_arguments,
                        [&](std::unique_ptr<Expr>& element_expr,
                            const TemplateArgumentBindings& element_bindings,
                            const TemplateClonePassBuilder& element_builder,
                            const TemplateSubstitutionPass& element_clone_pass,
                            std::string* nested_error_out) -> bool {
                            auto element_resolution_pass =
                                element_builder.build_dependent_resolution_pass(
                                    element_clone_pass,
                                    [&](std::unique_ptr<Expr>& nested_expr,
                                        std::string* resolution_error_out)
                                        -> bool {
                                        if (!resolve_specialized_expr(
                                                nested_expr,
                                                element_bindings,
                                                resolution_error_out)) {
                                            return false;
                                        }
                                        return resolve_dependent_expr_after_substitution(
                                            nested_expr,
                                            QualType(nullptr),
                                            resolution_error_out);
                                    });
                            return element_resolution_pass.resolve_expr_in_place(
                                element_expr,
                                nested_error_out);
                        },
                        error_out);
                };
            resolve_specialized_expr =
                [&](std::unique_ptr<Expr>& rewritten_expr,
                    const TemplateArgumentBindings& active_bindings,
                    std::string* error_out) -> bool {
                    if (!materialize_substituted_type_value_initializer(
                            rewritten_expr,
                            active_bindings,
                            error_out)) {
                        return false;
                    }
                    auto clone_fold_pattern_element =
                        [&](size_t element_index,
                            const Expr* pattern_expr,
                            std::string* element_error_out)
                            -> std::unique_ptr<Expr> {
                            return clone_substituted_pack_pattern_element(
                                *this,
                                ast_ctx_.get(),
                                parameters,
                                active_bindings,
                                nullptr,
                                clone_context,
                                element_index,
                                pattern_expr,
                                loc,
                                "failed to materialize fold-expression bindings",
                                "failed to substitute fold-expression pattern",
                                "fold-expression pattern cloning is not supported",
                                rewrite_substituted_pack_element_type,
                                rewrite_substituted_pack_element_arguments,
                                [&](std::unique_ptr<Expr>& element_expr,
                                    const TemplateArgumentBindings&
                                        element_bindings,
                                    const TemplateClonePassBuilder&
                                        element_builder,
                                    const TemplateSubstitutionPass&
                                        element_clone_pass,
                                    std::string* nested_error_out) -> bool {
                                    auto element_resolution_pass =
                                        element_builder
                                            .build_dependent_resolution_pass(
                                                element_clone_pass,
                                                [&](std::unique_ptr<Expr>&
                                                        nested_expr,
                                                    std::string*
                                                        resolution_error_out)
                                                    -> bool {
                                                    if (!resolve_specialized_expr(
                                                            nested_expr,
                                                            element_bindings,
                                                            resolution_error_out)) {
                                                        return false;
                                                    }
                                                    return resolve_dependent_expr_after_substitution(
                                                        nested_expr,
                                                        QualType(nullptr),
                                                        resolution_error_out);
                                                });
                                    return element_resolution_pass
                                        .resolve_expr_in_place(
                                            element_expr,
                                            nested_error_out);
                                },
                                element_error_out);
                        };

                    if (!materialize_specialized_fold_expression(
                            *this,
                            rewritten_expr,
                            QualType(nullptr),
                            QualType(get_builtin_bool()).get_shared(),
                            parameters,
                            active_bindings,
                            clone_fold_pattern_element,
                            error_out)) {
                        return false;
                    }
                    return true;
                };
            auto clone_pass = clone_pass_builder.build_substitution_pass();
            auto resolution_pass =
                clone_pass_builder.build_dependent_resolution_pass(
                    clone_pass,
                    [&](std::unique_ptr<Expr>& rewritten_expr,
                        std::string* error_out) -> bool {
                        if (!resolve_specialized_expr(
                                rewritten_expr,
                                argument_bindings,
                                error_out)) {
                            return false;
                        }
                        return resolve_dependent_expr_after_substitution(
                            rewritten_expr,
                            QualType(nullptr),
                            error_out);
                    });

            std::string clone_error;
            auto cloned_expr = clone_pass.clone_expr(expr.get(), &clone_error);
            if (!cloned_expr) {
                return nullptr;
            }
            auto rewrite_lingering_template_ids =
                [&](auto&& self, Expr* candidate) -> void {
                    if (!candidate) {
                        return;
                    }

                    switch (candidate->get_kind()) {
                        case StmtKind::UnresolvedLookupExpr: {
                            auto* lookup =
                                static_cast<UnresolvedLookupExpr*>(candidate);
                            if (lookup->explicit_template_arguments) {
                                lookup->explicit_template_arguments =
                                    rewrite_bound_template_arguments(
                                        *lookup->explicit_template_arguments);
                            }
                            return;
                        }
                        case StmtKind::UnresolvedMemberExpr: {
                            auto* member =
                                static_cast<UnresolvedMemberExpr*>(candidate);
                            if (member->explicit_template_arguments) {
                                member->explicit_template_arguments =
                                    rewrite_bound_template_arguments(
                                        *member->explicit_template_arguments);
                            }
                            self(self, member->base.get());
                            return;
                        }
                        case StmtKind::FuncCall: {
                            auto* call = static_cast<FuncCall*>(candidate);
                            self(self, call->func.get());
                            for (const auto& arg : call->args) {
                                self(self, arg.get());
                            }
                            return;
                        }
                        case StmtKind::DependentCallExpr: {
                            auto* call =
                                static_cast<DependentCallExpr*>(candidate);
                            self(self, call->callee.get());
                            for (const auto& arg : call->args) {
                                self(self, arg.get());
                            }
                            return;
                        }
                        case StmtKind::CppFunctionStyleCastExpr: {
                            auto* cast =
                                static_cast<CppFunctionStyleCastExpr*>(
                                    candidate);
                            for (const auto& arg : cast->args) {
                                self(self, arg.get());
                            }
                            return;
                        }
                        case StmtKind::CppValueInitExpr:
                            return;
                        case StmtKind::ImplicitCast: {
                            auto* cast = static_cast<ImplicitCast*>(candidate);
                            self(self, cast->expr.get());
                            return;
                        }
                        case StmtKind::ExplicitCast: {
                            auto* cast = static_cast<ExplicitCast*>(candidate);
                            self(self, cast->expr.get());
                            return;
                        }
                        case StmtKind::ParenExpr: {
                            auto* paren = static_cast<ParenExpr*>(candidate);
                            self(self, paren->subexpr.get());
                            return;
                        }
                        case StmtKind::CondExpr: {
                            auto* cond = static_cast<CondExpr*>(candidate);
                            self(self, cond->condition.get());
                            self(self, cond->true_expr.get());
                            self(self, cond->false_expr.get());
                            return;
                        }
                        case StmtKind::UnaryOperation: {
                            auto* unary =
                                static_cast<UnaryOperation*>(candidate);
                            self(self, unary->exp.get());
                            return;
                        }
                        case StmtKind::DependentUnaryExpr: {
                            auto* unary =
                                static_cast<DependentUnaryExpr*>(candidate);
                            self(self, unary->operand.get());
                            return;
                        }
                        case StmtKind::BinaryOperation: {
                            auto* binary =
                                static_cast<BinaryOperation*>(candidate);
                            self(self, binary->left.get());
                            self(self, binary->right.get());
                            return;
                        }
                        case StmtKind::CppBuiltinThreeWayCompareExpr: {
                            auto* compare =
                                static_cast<CppBuiltinThreeWayCompareExpr*>(
                                    candidate);
                            self(self, compare->left.get());
                            self(self, compare->right.get());
                            return;
                        }
                        case StmtKind::CompoundAssignOperation: {
                            auto* binary =
                                static_cast<CompoundAssignOperation*>(candidate);
                            self(self, binary->left.get());
                            self(self, binary->right.get());
                            return;
                        }
                        case StmtKind::DependentBinaryExpr: {
                            auto* binary =
                                static_cast<DependentBinaryExpr*>(candidate);
                            self(self, binary->left.get());
                            self(self, binary->right.get());
                            return;
                        }
                        case StmtKind::ArraySubscriptExpr: {
                            auto* subscript =
                                static_cast<ArraySubscriptExpr*>(candidate);
                            self(self, subscript->array.get());
                            self(self, subscript->index.get());
                            return;
                        }
                        case StmtKind::DependentArraySubscriptExpr: {
                            auto* subscript =
                                static_cast<DependentArraySubscriptExpr*>(
                                    candidate);
                            self(self, subscript->array.get());
                            self(self, subscript->index.get());
                            return;
                        }
                        case StmtKind::MemberExpr: {
                            auto* member =
                                static_cast<MemberExpr*>(candidate);
                            self(self, member->base.get());
                            return;
                        }
                        case StmtKind::MemberPointerAccessExpr: {
                            auto* access =
                                static_cast<MemberPointerAccessExpr*>(candidate);
                            self(self, access->base.get());
                            self(self, access->member_pointer.get());
                            return;
                        }
                        case StmtKind::DependentMemberPointerAccessExpr: {
                            auto* access =
                                static_cast<DependentMemberPointerAccessExpr*>(
                                    candidate);
                            self(self, access->base.get());
                            self(self, access->member_pointer.get());
                            return;
                        }
                        case StmtKind::CppNoexceptExpr: {
                            auto* noexcept_expr =
                                static_cast<CppNoexceptExpr*>(candidate);
                            self(self, noexcept_expr->operand.get());
                            return;
                        }
                        case StmtKind::CppPseudoDestructorExpr: {
                            auto* pseudo_dtor =
                                static_cast<CppPseudoDestructorExpr*>(candidate);
                            self(self, pseudo_dtor->base.get());
                            return;
                        }
                        default:
                            return;
                    }
                };
            rewrite_lingering_template_ids(
                rewrite_lingering_template_ids,
                cloned_expr.get());
            {
                Collect::UnevaluatedContextScope unevaluated_scope(
                    this,
                    "template expression-bearing type substitution");
                constexpr unsigned kMaxExprResolutionPasses = 8;
                // resolution can happen in stages, 8 is just an arbitary number to detect infinite loops/something gone wrong
                for (unsigned pass = 0; pass < kMaxExprResolutionPasses; ++pass) {
                    if (!decltype_expression_requires_deferred_resolution(
                            cloned_expr.get())) {
                        break;
                    }
                    if (!resolution_pass.resolve_expr_in_place(
                            cloned_expr,
                            &clone_error)) {
                        return nullptr;
                    }
                }
            }
            return std::shared_ptr<Expr>(cloned_expr.release());
        };
    auto substitute_declared_decltype_from_non_type_parameter =
        [&](const DecltypeExprType& decltype_type) -> std::optional<QualType> {
            if (!decltype_type.use_declared_type_rule || !decltype_type.expr) {
                return std::nullopt;
            }
            auto* stripped_expr =
                Collect::strip_implicit_casts(decltype_type.expr.get());
            auto* var_ref = dyn_cast<VarRef>(stripped_expr);
            if (!var_ref || !var_ref->symref) {
                return std::nullopt;
            }
            const TemplateArgument* replacement =
                find_template_argument_for_non_type_parameter_symbol(
                    var_ref->symref.get(),
                    parameters,
                    argument_bindings);
            if (!replacement || replacement->kind != TemplateArgumentKind::Value ||
                replacement->is_dependent || !replacement->value_type) {
                return std::nullopt;
            }
            return QualType(replacement->value_type.get_shared(), quals);
        };

    if (auto parm_type = dyn_cast_shared<TemplateTypeParmType>(raw)) {
        if (const auto* replacement = find_template_argument_for_parameter(
                parm_type.get(),
                parameters,
                argument_bindings,
                !allow_unsubstituted_parameters)) {
            if (replacement->kind == TemplateArgumentKind::Type) {
                return QualType(
                    replacement->type.get_shared(),
                    static_cast<uint8_t>(
                        replacement->type.get_qualifiers() | quals));
            }
        }
        auto parameter_index = find_template_parameter_index_by_identity(
            parm_type.get(),
            parameters);
        if (parm_type->is_parameter_pack &&
            parameter_index &&
            *parameter_index < argument_bindings.size() &&
            argument_bindings[*parameter_index].is_pack()) {
            // Keep the pack pattern intact here. Expression-bearing type
            // substitution materializes concrete pack elements separately when
            // it expands the surrounding fold/pack context.
            return type;
        }
        if (allow_unsubstituted_parameters) {
            return type;
        }
        report_error(
            "internal error: failed to substitute template type parameter '" +
                parm_type->to_string() + "'",
            loc);
        return type;
    }

    if (auto typedef_type = dyn_cast_shared<TypedefType>(raw)) {
        auto substituted_underlying = substitute_template_type_with_bindings(
            typedef_type->underlying_type,
            parameters,
            argument_bindings,
            loc,
            allow_unsubstituted_parameters,
            clone_context);
        if (substituted_underlying.equals_qualified(typedef_type->underlying_type)) {
            return type;
        }
        return QualType(
            std::make_shared<TypedefType>(
                typedef_type->name,
                substituted_underlying,
                typedef_type->typedef_decl),
            quals);
    }

    if (auto typeof_type = dyn_cast_shared<TypeofExprType>(raw)) {
        auto cloned_expr =
            clone_expr_for_expression_type_substitution(typeof_type->expr);
        if (!cloned_expr) {
            if (allow_unsubstituted_parameters) {
                return type;
            }
            report_error(
                "internal error: failed to substitute expression in typeof",
                loc);
            return type;
        }
        return QualType(
            std::make_shared<TypeofExprType>(std::move(cloned_expr)),
            quals);
    }

    if (auto decltype_type = dyn_cast_shared<DecltypeExprType>(raw)) {
        if (auto direct_rewrite =
                substitute_declared_decltype_from_non_type_parameter(
                    *decltype_type)) {
            return *direct_rewrite;
        }
        auto cloned_expr =
            clone_expr_for_expression_type_substitution(decltype_type->expr);
        if (!cloned_expr) {
            if (allow_unsubstituted_parameters) {
                return type;
            }
            report_error(
                "internal error: failed to substitute expression in decltype",
                loc);
            return type;
        }
        return QualType(
            std::make_shared<DecltypeExprType>(
                std::move(cloned_expr),
                decltype_type->use_declared_type_rule),
            quals);
    }

    if (auto transform_type = dyn_cast_shared<BuiltinTypeTransformType>(raw)) {
        auto substituted_operand = substitute_template_type_with_bindings(
            transform_type->operand_type,
            parameters,
            argument_bindings,
            loc,
            allow_unsubstituted_parameters,
            clone_context);
        if (substituted_operand.equals_qualified(transform_type->operand_type)) {
            return type;
        }
        return QualType(
            std::make_shared<BuiltinTypeTransformType>(
                transform_type->transform_kind,
                substituted_operand),
            quals);
    }

    if (auto pack_element_type =
            dyn_cast_shared<BuiltinTypePackElementType>(raw)) {
        auto substituted_arguments = substitute_template_arguments_with_bindings(
            pack_element_type->arguments,
            parameters,
            argument_bindings,
            loc,
            allow_unsubstituted_parameters,
            clone_context);
        if (auto selected_type = apply_builtin_type_pack_element(
                substituted_arguments,
                ast_ctx_.get())) {
            return QualType(
                selected_type.get_shared(),
                static_cast<uint8_t>(
                    selected_type.get_qualifiers() | quals));
        }

        bool changed = substituted_arguments.size() !=
            pack_element_type->arguments.size();
        if (!changed) {
            for (size_t idx = 0; idx < substituted_arguments.size(); ++idx) {
                if (!substituted_arguments[idx].equals(
                        pack_element_type->arguments[idx])) {
                    changed = true;
                    break;
                }
            }
        }
        if (!changed) {
            return type;
        }
        return QualType(
            std::make_shared<BuiltinTypePackElementType>(
                std::move(substituted_arguments)),
            quals);
    }

    if (auto specialization = dyn_cast_shared<TemplateSpecializationType>(raw)) {
        const Decl* rewritten_primary = specialization->primary_template;
        std::string rewritten_name = specialization->template_name;
        if (auto* template_parameter = dyn_cast<TemplateTemplateParmDecl>(
                const_cast<Decl*>(specialization->primary_template))) {
            auto parameter_index = find_template_parameter_index_by_decl(
                template_parameter,
                parameters);
            if (parameter_index && *parameter_index < argument_bindings.size()) {
                if (const auto* replacement =
                        argument_bindings[*parameter_index].single_argument()) {
                    if (replacement->kind == TemplateArgumentKind::Template) {
                        rewritten_primary = replacement->template_decl
                            ? static_cast<const Decl*>(replacement->template_decl)
                            : static_cast<const Decl*>(replacement->referenced_parameter);
                        rewritten_name = replacement->to_string();
                    } else if (!allow_unsubstituted_parameters) {
                        report_error(
                            "internal error: failed to substitute template-template parameter '" +
                                template_parameter->get_name() + "'",
                            loc);
                    }
                } else if (!allow_unsubstituted_parameters) {
                    report_error(
                        "internal error: failed to substitute template-template parameter '" +
                            template_parameter->get_name() + "'",
                        loc);
                }
            } else if (!allow_unsubstituted_parameters) {
                report_error(
                    "internal error: failed to substitute template-template parameter '" +
                        template_parameter->get_name() + "'",
                    loc);
            }
        }

        auto substituted_arguments = substitute_template_arguments_with_bindings(
            specialization->arguments,
            parameters,
            argument_bindings,
            loc,
            allow_unsubstituted_parameters,
            clone_context);
        bool dependent = template_specialization_components_are_dependent(
            rewritten_primary,
            substituted_arguments,
            /*explicitly_dependent=*/false,
            ast_ctx_.get());
        auto rewritten = std::make_shared<TemplateSpecializationType>(
            rewritten_name,
            rewritten_primary,
            std::move(substituted_arguments),
            dependent,
            specialization->is_class_template_placeholder);
        QualType rewritten_type(rewritten, quals);
        cache_existing_class_template_specialization_resolved_type(
            ast_ctx_.get(),
            rewritten_type,
            clone_context &&
                clone_context->publish_type_resolution_to_persistent_store);
        return rewritten_type;
    }

    if (auto dependent_name = dyn_cast_shared<DependentNameType>(raw)) {
        auto substituted_qualifier = substitute_template_type_with_bindings(
            dependent_name->qualifier_type,
            parameters,
            argument_bindings,
            loc,
            allow_unsubstituted_parameters,
            clone_context);
        auto substituted_arguments = substitute_template_arguments_with_bindings(
            dependent_name->template_arguments,
            parameters,
            argument_bindings,
            loc,
            allow_unsubstituted_parameters,
            clone_context);
        auto rewritten = std::make_shared<DependentNameType>(
            substituted_qualifier,
            dependent_name->member_name,
            std::move(substituted_arguments),
            dependent_name->is_current_instantiation,
            dependent_name->requires_typename_keyword,
            dependent_name->requires_template_keyword);
        return QualType(rewritten, quals);
    }

    if (auto ptr = dyn_cast_shared<PointerType>(raw)) {
        auto substituted_pointed = substitute_template_type_with_bindings(
            ptr->pointed_type,
            parameters,
            argument_bindings,
            loc,
            allow_unsubstituted_parameters,
            clone_context);
        if (substituted_pointed.equals_qualified(ptr->pointed_type)) {
            return type;
        }
        return QualType(
            std::make_shared<PointerType>(substituted_pointed),
            quals);
    }

    if (auto ref = dyn_cast_shared<ReferenceType>(raw)) {
        auto substituted_referred = substitute_template_type_with_bindings(
            ref->referred_type,
            parameters,
            argument_bindings,
            loc,
            allow_unsubstituted_parameters,
            clone_context);
        if (substituted_referred.equals_qualified(ref->referred_type)) {
            return type;
        }
        auto collapsed_reference =
            make_reference_type(substituted_referred, ref->reference_kind);
        return QualType(collapsed_reference.get_shared(), quals);
    }

    if (auto mem_ptr = dyn_cast_shared<MemberPointerType>(raw)) {
        auto substituted_class = substitute_template_type_with_bindings(
            mem_ptr->class_type,
            parameters,
            argument_bindings,
            loc,
            allow_unsubstituted_parameters,
            clone_context);
        auto substituted_member = substitute_template_type_with_bindings(
            mem_ptr->member_type,
            parameters,
            argument_bindings,
            loc,
            allow_unsubstituted_parameters,
            clone_context);
        if (substituted_class.equals_qualified(mem_ptr->class_type) &&
            substituted_member.equals_qualified(mem_ptr->member_type)) {
            return type;
        }
        return QualType(
            std::make_shared<MemberPointerType>(
                substituted_class,
                substituted_member),
            quals);
    }

    if (auto blk = dyn_cast_shared<BlockPointerType>(raw)) {
        auto substituted_pointed = substitute_template_type_with_bindings(
            blk->pointed_type,
            parameters,
            argument_bindings,
            loc,
            allow_unsubstituted_parameters,
            clone_context);
        if (substituted_pointed.equals_qualified(blk->pointed_type)) {
            return type;
        }
        return QualType(
            std::make_shared<BlockPointerType>(substituted_pointed),
            quals);
    }

    if (auto arr = dyn_cast_shared<ArrayType>(raw)) {
        auto substituted_element = substitute_template_type_with_bindings(
            arr->element_type,
            parameters,
            argument_bindings,
            loc,
            allow_unsubstituted_parameters,
            clone_context);
        bool needs_bound_rewrite =
            arr->size_kind == ArraySizeKind::Variable && arr->size_expr;
        if (substituted_element.equals_qualified(arr->element_type) &&
            !needs_bound_rewrite) {
            return type;
        }
        if (needs_bound_rewrite) {
            auto rewrite_bound_template_type =
                [&](QualType type) -> QualType {
                    auto rewritten_type =
                        substitute_template_type_with_bindings(
                            type,
                            parameters,
                            argument_bindings,
                            loc,
                            allow_unsubstituted_parameters,
                            clone_context);
                    return finalize_deferred_semantic_type(
                        rewritten_type,
                        loc);
                };
            auto rewrite_bound_template_arguments =
                [&](const std::vector<TemplateArgument>& template_arguments)
                -> std::vector<TemplateArgument> {
                    return substitute_template_arguments_with_bindings(
                        template_arguments,
                        parameters,
                        argument_bindings,
                        loc,
                        allow_unsubstituted_parameters,
                        clone_context);
                };
            auto clone_pass_builder = make_template_binding_clone_pass_builder(
                ast_ctx_.get(),
                this,
                parameters,
                argument_bindings,
                loc,
                "failed to substitute array bound expression",
                rewrite_bound_template_type,
                rewrite_bound_template_arguments,
                {},
                {});
            inherit_clone_context_symbol_remaps(clone_pass_builder, clone_context);
            auto clone_pass = clone_pass_builder.build_substitution_pass();

            std::string clone_error;
            auto cloned_size_expr = clone_pass.clone_expr(
                arr->size_expr.get(),
                &clone_error);
            if (!cloned_size_expr) {
                if (allow_unsubstituted_parameters) {
                    return type;
                }
                report_error(
                    clone_error.empty()
                        ? "internal error: failed to substitute array bound expression"
                        : clone_error,
                    loc);
                return type;
            }

            std::string resolve_error;
            if (!resolve_dependent_expr_after_substitution(
                    cloned_size_expr,
                    QualType(),
                    &resolve_error)) {
                if (allow_unsubstituted_parameters) {
                    return type;
                }
                report_error(
                    resolve_error.empty()
                        ? "internal error: failed to resolve substituted array bound expression"
                        : resolve_error,
                    loc);
                return type;
            }

            auto bound = collect_array_bound_expression(std::move(cloned_size_expr));
            if (bound.constant_size.has_value()) {
                return QualType(
                    std::make_shared<ArrayType>(
                        substituted_element,
                        *bound.constant_size),
                    quals);
            }
            return QualType(
                std::make_shared<ArrayType>(
                    substituted_element,
                    bound.variable_size_expr),
                quals);
        }
        return QualType(
            std::make_shared<ArrayType>(
                substituted_element,
                arr->size),
            quals);
    }

    if (auto func = dyn_cast_shared<FunctionType>(raw)) {
        auto substituted_ret = substitute_template_type_with_bindings(
            func->ret_type,
            parameters,
            argument_bindings,
            loc,
            allow_unsubstituted_parameters,
            clone_context);
        bool changed = !substituted_ret.equals_qualified(func->ret_type);
        std::vector<QualType> substituted_parameters;
        substituted_parameters.reserve(func->parameters.size());
        std::vector<uint8_t> substituted_parameter_pack_flags;
        substituted_parameter_pack_flags.reserve(func->parameters.size());
        // A function parameter expands only when the declarator wrote a
        // syntactic parameter pack. Nested expansions such as tuple<Args...>
        // still substitute inside the parameter type but remain one parameter.
        for (size_t parameter_index = 0;
             parameter_index < func->parameters.size();
             ++parameter_index) {
            const auto& parameter = func->parameters[parameter_index];
            if (!func->parameter_is_pack(parameter_index)) {
                auto substituted_parameter = substitute_template_type_with_bindings(
                    parameter,
                    parameters,
                    argument_bindings,
                    loc,
                    allow_unsubstituted_parameters,
                    clone_context);
                changed |= !substituted_parameter.equals_qualified(parameter);
                substituted_parameters.push_back(std::move(substituted_parameter));
                substituted_parameter_pack_flags.push_back(0);
                continue;
            }

            changed = true;
            auto pack_resolution =
                classify_parameter_pack_reference_in_type(
                    parameter,
                    parameters,
                    allow_unsubstituted_parameters);
            if (pack_resolution.kind ==
                TemplatePackReferenceResolutionKind::PreserveUnsubstituted) {
                auto substituted_parameter = substitute_template_type_with_bindings(
                    parameter,
                    parameters,
                    argument_bindings,
                    loc,
                    allow_unsubstituted_parameters,
                    clone_context);
                changed |= !substituted_parameter.equals_qualified(parameter);
                substituted_parameters.push_back(std::move(substituted_parameter));
                substituted_parameter_pack_flags.push_back(1);
                continue;
            }
            if (pack_resolution.kind ==
                TemplatePackReferenceResolutionKind::Unsupported) {
                report_error(
                    "function type substitution currently supports only one pack per parameter type",
                    loc);
                return type;
            }
            if (pack_resolution.kind == TemplatePackReferenceResolutionKind::None ||
                !pack_resolution.parameter_index.has_value()) {
                auto substituted_parameter = substitute_template_type_with_bindings(
                    parameter,
                    parameters,
                    argument_bindings,
                    loc,
                    allow_unsubstituted_parameters,
                    clone_context);
                changed |= !substituted_parameter.equals_qualified(parameter);
                substituted_parameters.push_back(std::move(substituted_parameter));
                substituted_parameter_pack_flags.push_back(0);
                continue;
            }

            size_t pack_index = *pack_resolution.parameter_index;
            if (pack_index >= argument_bindings.size()) {
                report_error(
                    "internal error: missing function type parameter-pack binding",
                    loc);
                return type;
            }
            const auto& pack_binding = argument_bindings[pack_index];
            if (!pack_binding.is_pack()) {
                auto substituted_parameter = substitute_template_type_with_bindings(
                    parameter,
                    parameters,
                    argument_bindings,
                    loc,
                    allow_unsubstituted_parameters,
                    clone_context);
                changed |= !substituted_parameter.equals_qualified(parameter);
                substituted_parameters.push_back(std::move(substituted_parameter));
                substituted_parameter_pack_flags.push_back(0);
                continue;
            }
            for (size_t element_index = 0;
                 element_index < pack_binding.arguments.size();
                 ++element_index) {
                TemplateArgumentBindings element_bindings;
                std::string binding_error;
                if (!build_pack_element_argument_bindings(
                        parameters,
                        argument_bindings,
                        element_index,
                        element_bindings,
                        &binding_error)) {
                    report_error(
                        binding_error.empty()
                            ? "internal error: failed to materialize function type pack expansion"
                            : binding_error,
                        loc);
                    return type;
                }
                auto substituted_parameter = substitute_template_type_with_bindings(
                    parameter,
                    parameters,
                    element_bindings,
                    loc,
                    allow_unsubstituted_parameters,
                    clone_context);
                substituted_parameters.push_back(std::move(substituted_parameter));
                substituted_parameter_pack_flags.push_back(0);
            }
        }
        FunctionExceptionSpecKind substituted_exception_spec =
            func->exception_spec;
        std::shared_ptr<Expr> substituted_exception_spec_expr =
            func->exception_spec_expr;
        if (func->exception_spec_expr) {
            auto rewrite_bound_template_type =
                [&](QualType bound_type) -> QualType {
                    return substitute_template_type_with_bindings(
                        bound_type,
                        parameters,
                        argument_bindings,
                        loc,
                        allow_unsubstituted_parameters,
                        clone_context);
                };
            auto rewrite_bound_template_arguments =
                [&](const std::vector<TemplateArgument>& template_arguments)
                -> std::vector<TemplateArgument> {
                    return substitute_template_arguments_with_bindings(
                        template_arguments,
                        parameters,
                        argument_bindings,
                        loc,
                        allow_unsubstituted_parameters,
                        clone_context);
                };
            auto clone_pass_builder = make_template_binding_clone_pass_builder(
                ast_ctx_.get(),
                this,
                parameters,
                argument_bindings,
                loc,
                "failed to substitute function noexcept expression",
                rewrite_bound_template_type,
                rewrite_bound_template_arguments,
                {},
                {});
            inherit_clone_context_symbol_remaps(clone_pass_builder, clone_context);
            auto rewrite_noexcept_pack_element_type =
                [&](QualType nested_type,
                    const TemplateArgumentBindings& element_bindings)
                -> QualType {
                    auto rewritten_type =
                        substitute_template_type_with_bindings(
                            nested_type,
                            parameters,
                            element_bindings,
                            loc,
                            allow_unsubstituted_parameters,
                            clone_context);
                    return finalize_deferred_semantic_type(
                        rewritten_type,
                        loc);
                };
            auto rewrite_noexcept_pack_element_arguments =
                [&](const std::vector<TemplateArgument>& template_arguments,
                    const TemplateArgumentBindings& element_bindings)
                -> std::vector<TemplateArgument> {
                    return substitute_template_arguments_with_bindings(
                        template_arguments,
                        parameters,
                        element_bindings,
                        loc,
                        allow_unsubstituted_parameters,
                        clone_context);
                };
            clone_pass_builder.expand_pack_expansion =
                [&](const Expr* pattern_expr,
                    std::vector<std::unique_ptr<Expr>>& expanded_out,
                    std::string* error_out) -> bool {
                    return expand_substituted_pack_expression(
                        *this,
                        ast_ctx_.get(),
                        parameters,
                        argument_bindings,
                        clone_context,
                        loc,
                        pattern_expr,
                        expanded_out,
                        "failed to collect function noexcept pack expansion shape",
                        "function noexcept pack expansion does not reference a template parameter pack",
                        "failed to materialize function noexcept pack expansion bindings",
                        "failed to substitute function noexcept pack expansion pattern",
                        "function noexcept pack expansion pattern cloning is not supported",
                        "failed to preserve unexpanded function noexcept pack expansion",
                        rewrite_noexcept_pack_element_type,
                        rewrite_noexcept_pack_element_arguments,
                        [&](std::unique_ptr<Expr>& element_expr,
                            const TemplateArgumentBindings&,
                            const TemplateClonePassBuilder&,
                            const TemplateSubstitutionPass&,
                            std::string* nested_error_out) -> bool {
                            return resolve_dependent_expr_after_substitution(
                                element_expr,
                                QualType(),
                                nested_error_out);
                        },
                        error_out);
                };
            auto clone_pass = clone_pass_builder.build_substitution_pass();
            std::string clone_error;
            auto cloned_exception_expr =
                clone_pass.clone_expr(func->exception_spec_expr.get(), &clone_error);
            if (!cloned_exception_expr) {
                report_error(
                    clone_error.empty()
                        ? "failed to substitute function noexcept expression"
                        : clone_error,
                    loc);
                return type;
            }
            std::string resolve_error;
            bool needs_dependent_resolution =
                expression_depends_on_template_parameters(
                    cloned_exception_expr.get());
            if (needs_dependent_resolution &&
                !resolve_dependent_expr_after_substitution(
                    cloned_exception_expr,
                    QualType(),
                    &resolve_error)) {
                report_error(
                    resolve_error.empty()
                        ? "failed to resolve function noexcept expression after substitution"
                        : resolve_error,
                    loc);
                return type;
            }
            changed = true;
            substituted_exception_spec_expr =
                std::shared_ptr<Expr>(cloned_exception_expr.release());
            bool known_exception_spec = false;
            bool is_non_throwing = false;
            bool expression_is_dependent =
                expression_is_value_dependent_for_constant_evaluation(
                    substituted_exception_spec_expr.get(),
                    true);
            if (!expression_is_dependent) {
                ConstEvalResult eval = evaluate_constant_expression_demand(
                    substituted_exception_spec_expr.get(),
                    ConstEvalMode::cpp_core_constant_expression(),
                    loc);
                if (eval.status == ConstEvalStatus::Constant &&
                    eval.value.has_value()) {
                    switch (eval.value->kind) {
                        case ConstValueKind::Boolean:
                            is_non_throwing = eval.value->bool_value;
                            known_exception_spec = true;
                            break;
                        case ConstValueKind::Integer:
                            is_non_throwing =
                                eval.value->int_value.to_unsigned_u64() != 0;
                            known_exception_spec = true;
                            break;
                        default:
                            break;
                    }
                }
            }
            if (known_exception_spec) {
                substituted_exception_spec = is_non_throwing
                    ? FunctionExceptionSpecKind::NonThrowing
                    : FunctionExceptionSpecKind::PotentiallyThrowing;
                substituted_exception_spec_expr = nullptr;
            } else {
                substituted_exception_spec =
                    FunctionExceptionSpecKind::Dependent;
            }
        }
        if (!changed) {
            return type;
        }
        auto rewritten = std::make_shared<FunctionType>();
        rewritten->ret_type = substituted_ret;
        rewritten->parameters = std::move(substituted_parameters);
        rewritten->parameter_pack_flags =
            std::move(substituted_parameter_pack_flags);
        rewritten->normalize_parameter_pack_flags();
        rewritten->is_variadic = func->is_variadic;
        rewritten->has_prototype = func->has_prototype;
        rewritten->member_ref_qualifier = func->member_ref_qualifier;
        rewritten->has_explicit_exception_spec =
            func->has_explicit_exception_spec;
        rewritten->exception_spec = substituted_exception_spec;
        rewritten->exception_spec_expr = substituted_exception_spec_expr;
        return QualType(rewritten, quals);
    }

    if (auto vec = dyn_cast_shared<VectorType>(raw)) {
        auto substituted_element = substitute_template_type_with_bindings(
            vec->element_type,
            parameters,
            argument_bindings,
            loc,
            allow_unsubstituted_parameters,
            clone_context);
        if (substituted_element.equals_qualified(vec->element_type)) {
            return type;
        }
        return QualType(
            std::make_shared<VectorType>(
                substituted_element,
                vec->total_bytes),
            quals);
    }

    return type;
}

std::vector<TemplateArgument> Collect::substitute_template_arguments(
    const std::vector<TemplateArgument>& arguments,
    const TemplateParameterList& parameters,
    const std::vector<TemplateArgument>& specialization_arguments,
    SrcLoc loc) {
    TemplateArgumentBindings argument_bindings;
    std::string binding_error;
    if (!bind_template_arguments_to_parameters(
            parameters,
            specialization_arguments,
            argument_bindings,
            &binding_error)) {
        report_error(
            binding_error.empty()
                ? "internal error: failed to align template arguments with parameters"
                : binding_error,
            loc);
        return arguments;
    }
    return substitute_template_arguments_with_bindings(
        arguments,
        parameters,
        argument_bindings,
        loc);
}

std::vector<TemplateArgument> Collect::substitute_template_arguments_with_bindings(
    const std::vector<TemplateArgument>& arguments,
    const TemplateParameterList& parameters,
    const TemplateArgumentBindings& argument_bindings,
    SrcLoc loc,
    bool allow_unsubstituted_parameters,
    ASTCloneContext* clone_context) {
    std::vector<TemplateArgument> rewritten;
    rewritten.reserve(arguments.size());
    // append_rewritten_argument handles pack expansion inline via recursion.
    // When argument.expands_parameter_pack is true:
    //   1. Collect the pack shape (which parameters are referenced)
    //   2. Compute expected arity from bindings (must agree across all packs)
    //   3. For each element index 0..arity-1:
    //      - Build fresh element_bindings by extracting [index] from each pack
    //      - Recursively call with the single-element argument
    // The active_bindings map is NEVER modified; element_bindings is a fresh
    // copy per iteration.  If we encounter unsupported dependencies and
    // allow_unsubstituted is true, the original pack expansion is kept as-is.
    std::function<bool(const TemplateArgument&, const TemplateArgumentBindings&)>
        append_rewritten_argument =
            [&](const TemplateArgument& argument,
                const TemplateArgumentBindings& active_bindings) -> bool {
        if (is_integer_pack_template_argument(argument)) {
            auto rewrite_integer_pack_type =
                [&](QualType type) -> QualType {
                    auto rewritten_type =
                        substitute_template_type_with_bindings(
                            type,
                            parameters,
                            active_bindings,
                            loc,
                            allow_unsubstituted_parameters,
                            clone_context);
                    return finalize_deferred_semantic_type(
                        rewritten_type,
                        loc);
                };
            auto rewrite_integer_pack_arguments =
                [&](const std::vector<TemplateArgument>& template_arguments)
                -> std::vector<TemplateArgument> {
                    return substitute_template_arguments_with_bindings(
                        template_arguments,
                        parameters,
                        active_bindings,
                        loc,
                        allow_unsubstituted_parameters,
                        clone_context);
                };
            return append_integer_pack_template_arguments(
                *this,
                ast_ctx_.get(),
                argument,
                parameters,
                active_bindings,
                clone_context,
                loc,
                allow_unsubstituted_parameters,
                rewrite_integer_pack_type,
                rewrite_integer_pack_arguments,
                [&](const std::string& message, SrcLoc error_loc) {
                    report_error(message, error_loc);
                },
                QualType(get_builtin_ulong()),
                rewritten);
        }

        if (argument.expands_parameter_pack) {
            template_sema_internal::TemplatePackExpansionShape shape;
            if (!collect_pack_expansion_shape_in_template_argument(
                    argument,
                    parameters,
                    shape)) {
                if (allow_unsubstituted_parameters &&
                    shape.has_unsupported_dependency) {
                    rewritten.push_back(argument);
                    return true;
                }
                report_error(
                    "failed to collect template argument pack expansion shape",
                    loc);
                return false;
            }
            std::string arity_error;
            auto expansion_arity = find_pack_expansion_arity_for_bindings(
                shape,
                parameters,
                active_bindings,
                &arity_error);
            if (!expansion_arity.has_value()) {
                if (allow_unsubstituted_parameters && arity_error.empty()) {
                    rewritten.push_back(argument);
                    return true;
                }
                report_error(
                    arity_error.empty()
                        ? "failed to determine template argument pack expansion arity"
                        : arity_error,
                    loc);
                return false;
            }

            for (size_t element_index = 0;
                 element_index < *expansion_arity;
                 ++element_index) {
                TemplateArgumentBindings element_bindings;
                std::string element_binding_error;
                if (!build_pack_element_argument_bindings_for_shape(
                        parameters,
                        active_bindings,
                        shape,
                        element_index,
                        element_bindings,
                        &element_binding_error)) {
                    report_error(
                        element_binding_error.empty()
                            ? "failed to materialize template argument pack expansion bindings"
                            : element_binding_error,
                        loc);
                    return false;
                }
                TemplateArgument element_argument = argument;
                element_argument.expands_parameter_pack = false;
                element_argument.pack_expansion_parameters.clear();
                if (!append_rewritten_argument(
                        element_argument,
                        element_bindings)) {
                    return false;
                }
            }
            return true;
        }

        TemplateArgument new_argument = argument;
        switch (argument.kind) {
            case TemplateArgumentKind::Type:
                new_argument.type = substitute_template_type_with_bindings(
                    argument.type,
                    parameters,
                    active_bindings,
                    loc,
                    allow_unsubstituted_parameters,
                    clone_context);
                break;
            case TemplateArgumentKind::Template:
                if (argument.referenced_parameter) {
                    if (auto parameter_index = find_template_parameter_index_by_decl(
                            argument.referenced_parameter,
                            parameters)) {
                        if (*parameter_index < active_bindings.size()) {
                            if (const auto* replacement =
                                    active_bindings[*parameter_index]
                                        .single_argument()) {
                                auto substituted = *replacement;
                                remap_template_argument_symbols_for_substitution(
                                    substituted,
                                    clone_context);
                                rewritten.push_back(std::move(substituted));
                                return true;
                            }
                        }
                    }
                }
                if (!argument.dependent_template_member_name.empty()) {
                    new_argument.dependent_template_qualifier_type =
                        substitute_template_type_with_bindings(
                            argument.dependent_template_qualifier_type,
                            parameters,
                            active_bindings,
                            loc,
                            allow_unsubstituted_parameters,
                            clone_context);
                    new_argument.is_dependent =
                        type_depends_on_template_parameters(
                            new_argument.dependent_template_qualifier_type,
                            ast_ctx_.get());

                    if (!new_argument.is_dependent) {
                        QualType concrete_owner =
                            collect_try_realize_deferred_semantic_type(
                                new_argument.dependent_template_qualifier_type);
                        if (concrete_owner &&
                            !type_depends_on_template_parameters(
                                concrete_owner,
                                ast_ctx_.get())) {
                            new_argument.dependent_template_qualifier_type =
                                concrete_owner;
                        }

                        const auto* nested_template =
                            collect_lookup_record_nested_template(
                                new_argument.dependent_template_qualifier_type,
                                argument.dependent_template_member_name);
                        auto* resolved_template =
                            nested_template
                                ? nested_template->decl
                                : nullptr;
                        if (!resolved_template) {
                            if (allow_unsubstituted_parameters) {
                                break;
                            }
                            report_error(
                                "'" +
                                    new_argument
                                        .dependent_template_qualifier_type
                                        .to_string() +
                                    "::" +
                                    argument.dependent_template_member_name +
                                    "' does not name a template",
                                loc);
                            return false;
                        }

                        std::string resolved_name =
                            new_argument.dependent_template_qualifier_type
                                .to_string();
                        resolved_name += "::";
                        resolved_name += argument.dependent_template_member_name;
                        new_argument = TemplateArgument::template_argument(
                            resolved_template,
                            std::move(resolved_name));
                    } else {
                        new_argument.template_name =
                            new_argument.dependent_template_qualifier_type
                                .to_string();
                        new_argument.template_name += "::template ";
                        new_argument.template_name +=
                            argument.dependent_template_member_name;
                    }
                }
                break;
            case TemplateArgumentKind::Value:
                if (argument.referenced_parameter) {
                    if (auto parameter_index = find_template_parameter_index_by_decl(
                            argument.referenced_parameter,
                            parameters)) {
                        if (*parameter_index < active_bindings.size()) {
                            if (const auto* replacement =
                                    active_bindings[*parameter_index]
                                        .single_argument()) {
                                auto substituted = *replacement;
                                remap_template_argument_symbols_for_substitution(
                                    substituted,
                                    clone_context);
                                rewritten.push_back(std::move(substituted));
                                return true;
                            }
                        }
                    }
                }

                new_argument.value_type = substitute_template_type_with_bindings(
                    argument.value_type,
                    parameters,
                    active_bindings,
                    loc,
                    allow_unsubstituted_parameters,
                    clone_context);
                new_argument.value_type =
                    finalize_deferred_semantic_type(new_argument.value_type, loc);

                if (argument.value_expr) {
                    auto rewrite_bound_template_type =
                        [&](QualType type) -> QualType {
                            auto rewritten_type =
                                substitute_template_type_with_bindings(
                                    type,
                                    parameters,
                                    active_bindings,
                                    loc,
                                    allow_unsubstituted_parameters,
                                    clone_context);
                            return finalize_deferred_semantic_type(
                                rewritten_type,
                                loc);
                        };
                    auto rewrite_bound_template_arguments =
                        [&](const std::vector<TemplateArgument>& template_arguments)
                        -> std::vector<TemplateArgument> {
                            return substitute_template_arguments_with_bindings(
                                template_arguments,
                                parameters,
                                active_bindings,
                                loc,
                                allow_unsubstituted_parameters,
                                clone_context);
                        };
                    auto clone_pass_builder =
                        make_template_binding_clone_pass_builder(
                            ast_ctx_.get(),
                            this,
                            parameters,
                            active_bindings,
                            loc,
                            "non-type template argument substitution requires a concrete integral value",
                            rewrite_bound_template_type,
                            rewrite_bound_template_arguments,
                            {},
                            {});
                    inherit_clone_context_symbol_remaps(
                        clone_pass_builder,
                        clone_context);
                    auto clone_pass = clone_pass_builder.build_substitution_pass();

                    std::string clone_error;
                    auto cloned_expr = clone_pass.clone_expr(
                        argument.value_expr.get(),
                        &clone_error);
                    if (!cloned_expr) {
                        report_error(
                            clone_error.empty()
                                ? "failed to substitute non-type template argument expression"
                                : clone_error,
                            loc);
                        rewritten.push_back(std::move(new_argument));
                        return true;
                    }

                    std::string resolve_error;
                    auto rewrite_fold_element_type =
                        [&](QualType type,
                            const TemplateArgumentBindings& element_bindings)
                        -> QualType {
                            auto rewritten_type =
                                substitute_template_type_with_bindings(
                                    type,
                                    parameters,
                                    element_bindings,
                                    loc,
                                    allow_unsubstituted_parameters,
                                    clone_context);
                            return finalize_deferred_semantic_type(
                                rewritten_type,
                                loc);
                        };
                    auto rewrite_fold_element_arguments =
                        [&](const std::vector<TemplateArgument>& template_arguments,
                            const TemplateArgumentBindings& element_bindings)
                        -> std::vector<TemplateArgument> {
                            return substitute_template_arguments_with_bindings(
                                template_arguments,
                                parameters,
                                element_bindings,
                                loc,
                                allow_unsubstituted_parameters,
                                clone_context);
                        };
                    std::function<std::unique_ptr<Expr>(
                        size_t,
                        const Expr*,
                        std::string*)>
                        clone_fold_pattern_element;
                    clone_fold_pattern_element =
                        [&](size_t element_index,
                            const Expr* pattern_expr,
                            std::string* element_error_out)
                            -> std::unique_ptr<Expr> {
                            return clone_substituted_pack_pattern_element(
                                *this,
                                ast_ctx_.get(),
                                parameters,
                                active_bindings,
                                nullptr,
                                clone_context,
                                element_index,
                                pattern_expr,
                                loc,
                                "failed to materialize non-type template argument fold bindings",
                                "failed to substitute non-type template argument fold element",
                                "non-type template argument fold element cloning is not supported",
                                rewrite_fold_element_type,
                                rewrite_fold_element_arguments,
                                [&](std::unique_ptr<Expr>& element_expr,
                                    const TemplateArgumentBindings&
                                        element_bindings,
                                    const TemplateClonePassBuilder&,
                                    const TemplateSubstitutionPass&,
                                    std::string* nested_error_out) -> bool {
                                    if (!materialize_specialized_fold_expression(
                                            *this,
                                            element_expr,
                                            QualType(),
                                            QualType(get_builtin_bool()).get_shared(),
                                            parameters,
                                            element_bindings,
                                            clone_fold_pattern_element,
                                            nested_error_out)) {
                                        return false;
                                    }
                                    return resolve_dependent_expr_after_substitution(
                                        element_expr,
                                        QualType(),
                                        nested_error_out);
                                },
                                element_error_out);
                    };
                    if (!materialize_specialized_fold_expression(
                            *this,
                            cloned_expr,
                            QualType(),
                            QualType(get_builtin_bool()).get_shared(),
                            parameters,
                            active_bindings,
                            clone_fold_pattern_element,
                            &resolve_error) ||
                        !resolve_dependent_expr_after_substitution(
                            cloned_expr,
                            QualType(),
                            &resolve_error)) {
                        report_error(
                            resolve_error.empty()
                                ? "failed to resolve non-type template argument expression after substitution"
                                : resolve_error,
                            loc);
                        rewritten.push_back(std::move(new_argument));
                        return true;
                    }

                    QualType resolved_value_type =
                        finalize_deferred_semantic_type(
                            cloned_expr->get_type(),
                            loc);
                    if (resolved_value_type) {
                        new_argument.value_type = resolved_value_type;
                    }

                    bool cloned_expr_is_dependent =
                        expression_depends_on_template_parameters(
                            cloned_expr.get()) ||
                        type_depends_on_template_parameters(
                            cloned_expr->get_type(),
                            ast_ctx_.get());
                    if (cloned_expr_is_dependent) {
                        new_argument.value_expr =
                            std::shared_ptr<Expr>(cloned_expr.release());
                        new_argument.referenced_parameter = nullptr;
                        new_argument.is_dependent = true;
                    } else {
                        ConstEvalResult eval = evaluate_with_consteval_compat(
                            cloned_expr.get(),
                            ConstEvalMode::cpp_non_type_template_argument());
                        if (eval.status == ConstEvalStatus::Constant &&
                            eval.value.has_value() &&
                            eval.value->kind != ConstValueKind::Invalid) {
                            std::shared_ptr<Expr> concrete_expr = nullptr;
                            if (eval.value->kind == ConstValueKind::Object) {
                                concrete_expr = std::shared_ptr<Expr>(
                                    cloned_expr.release());
                            }
                            new_argument = TemplateArgument::value_argument(
                                new_argument.value_type,
                                *eval.value,
                                {},
                                std::move(concrete_expr));
                        } else {
                            new_argument.value_expr =
                                std::shared_ptr<Expr>(cloned_expr.release());
                            new_argument.referenced_parameter = nullptr;
                            new_argument.is_dependent =
                                substituted_value_argument_depends_on_template_parameters(
                                    *this,
                                    new_argument,
                                    ast_ctx_.get());
                        }
                    }
                }

                if (!new_argument.is_dependent &&
                    new_argument.value_type &&
                    auto_type_utils::auto_type_flavors_in(
                        new_argument.value_type.get_shared()) == 0) {
                    remap_template_argument_symbols_for_substitution(
                        new_argument,
                        clone_context);
                    std::string normalize_error;
                    if (!normalize_concrete_template_value_argument(
                            new_argument,
                            new_argument.value_type,
                            &normalize_error)) {
                        report_error(
                            normalize_error.empty()
                                ? "failed to normalize template value argument"
                                : normalize_error,
                            loc);
                    }
                }
                break;
        }
        rewritten.push_back(std::move(new_argument));
        return true;
    };

    for (const auto& argument : arguments) {
        if (!append_rewritten_argument(argument, argument_bindings)) {
            return rewritten;
        }
    }
    return rewritten;
}
