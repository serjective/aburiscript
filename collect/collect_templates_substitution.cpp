#include "collect.h"
#include "collect_templates_internal.h"
#include "../helpers/auto_type_utils.h"

#include <optional>

using template_sema_internal::build_pack_element_argument_bindings;
using template_sema_internal::collect_pack_expansion_shape_in_template_argument;
using template_sema_internal::find_template_parameter_index_by_decl;
using template_sema_internal::find_pack_expansion_arity_for_bindings;
using template_sema_internal::find_unique_parameter_pack_index_in_type;
using template_sema_internal::make_template_binding_clone_pass_builder;
using template_sema_internal::normalize_concrete_template_value_argument;
using template_sema_internal::template_arguments_depend_on_template_parameters;

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
    bool allow_unsubstituted_parameters) {
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
                        allow_unsubstituted_parameters);
                };
            auto rewrite_bound_template_arguments =
                [&](const std::vector<TemplateArgument>& template_arguments)
                -> std::vector<TemplateArgument> {
                    return substitute_template_arguments_with_bindings(
                        template_arguments,
                        parameters,
                        argument_bindings,
                        loc,
                        allow_unsubstituted_parameters);
                };

            auto clone_pass_builder = make_template_binding_clone_pass_builder(
                ast_ctx_.get(),
                parameters,
                argument_bindings,
                loc,
                "failed to substitute expression-bearing deferred type",
                rewrite_bound_template_type,
                rewrite_bound_template_arguments,
                {},
                {});
            auto clone_pass = clone_pass_builder.build_substitution_pass();

            std::string clone_error;
            auto cloned_expr = clone_pass.clone_expr(expr.get(), &clone_error);
            if (!cloned_expr) {
                return nullptr;
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
                return QualType(replacement->type.get_shared(), quals);
            }
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
            allow_unsubstituted_parameters);
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
            allow_unsubstituted_parameters);
        if (substituted_operand.equals_qualified(transform_type->operand_type)) {
            return type;
        }
        return QualType(
            std::make_shared<BuiltinTypeTransformType>(
                transform_type->transform_kind,
                substituted_operand),
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
            allow_unsubstituted_parameters);
        bool dependent = isa<TemplateTemplateParmDecl>(rewritten_primary);
        for (const auto& argument : substituted_arguments) {
            if (template_argument_depends_on_template_parameters(
                    argument,
                ast_ctx_.get())) {
                dependent = true;
                break;
            }
        }
        auto rewritten = std::make_shared<TemplateSpecializationType>(
            rewritten_name,
            rewritten_primary,
            std::move(substituted_arguments),
            dependent);
        return QualType(rewritten, quals);
    }

    if (auto dependent_name = dyn_cast_shared<DependentNameType>(raw)) {
        auto substituted_qualifier = substitute_template_type_with_bindings(
            dependent_name->qualifier_type,
            parameters,
            argument_bindings,
            loc,
            allow_unsubstituted_parameters);
        auto substituted_arguments = substitute_template_arguments_with_bindings(
            dependent_name->template_arguments,
            parameters,
            argument_bindings,
            loc,
            allow_unsubstituted_parameters);
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
            allow_unsubstituted_parameters);
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
            allow_unsubstituted_parameters);
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
            allow_unsubstituted_parameters);
        auto substituted_member = substitute_template_type_with_bindings(
            mem_ptr->member_type,
            parameters,
            argument_bindings,
            loc,
            allow_unsubstituted_parameters);
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
            allow_unsubstituted_parameters);
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
            allow_unsubstituted_parameters);
        if (substituted_element.equals_qualified(arr->element_type)) {
            return type;
        }
        if (arr->size_kind == ArraySizeKind::Variable && arr->size_expr) {
            return QualType(
                std::make_shared<ArrayType>(
                    substituted_element,
                    arr->size_expr),
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
            allow_unsubstituted_parameters);
        bool changed = !substituted_ret.equals_qualified(func->ret_type);
        std::vector<QualType> substituted_parameters;
        substituted_parameters.reserve(func->parameters.size());
        // For each FunctionType parameter, check for pack expansion references.
        // find_unique_parameter_pack_index_in_type returns:
        //   false → multiple distinct packs in one parameter type (unsupported)
        //   true, pack_index has value → single pack at that parameter list index
        //   true, pack_index empty → no packs in this parameter type
        // When a pack is found and its binding is_pack(), we expand element-by-
        // element: for arity N, this parameter produces N output parameters.
        // When the binding is NOT a pack (single element), we substitute normally.
        for (const auto& parameter : func->parameters) {
            std::optional<size_t> pack_index;
            if (!find_unique_parameter_pack_index_in_type(
                    parameter,
                    parameters,
                    pack_index)) {
                report_error(
                    "function type substitution currently supports only one pack per parameter type",
                    loc);
                return type;
            }
            if (!pack_index.has_value()) {
                auto substituted_parameter = substitute_template_type_with_bindings(
                    parameter,
                    parameters,
                    argument_bindings,
                    loc,
                    allow_unsubstituted_parameters);
                changed |= !substituted_parameter.equals_qualified(parameter);
                substituted_parameters.push_back(std::move(substituted_parameter));
                continue;
            }

            if (*pack_index >= argument_bindings.size()) {
                report_error(
                    "internal error: missing function type parameter-pack binding",
                    loc);
                return type;
            }
            const auto& pack_binding = argument_bindings[*pack_index];
            if (!pack_binding.is_pack()) {
                auto substituted_parameter = substitute_template_type_with_bindings(
                    parameter,
                    parameters,
                    argument_bindings,
                    loc,
                    allow_unsubstituted_parameters);
                changed |= !substituted_parameter.equals_qualified(parameter);
                substituted_parameters.push_back(std::move(substituted_parameter));
                continue;
            }
            changed = true;
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
                    allow_unsubstituted_parameters);
                substituted_parameters.push_back(std::move(substituted_parameter));
            }
        }
        if (!changed) {
            return type;
        }
        auto rewritten = std::make_shared<FunctionType>();
        rewritten->ret_type = substituted_ret;
        rewritten->parameters = std::move(substituted_parameters);
        rewritten->is_variadic = func->is_variadic;
        rewritten->has_prototype = func->has_prototype;
        rewritten->member_ref_qualifier = func->member_ref_qualifier;
        rewritten->has_explicit_exception_spec =
            func->has_explicit_exception_spec;
        rewritten->exception_spec = func->exception_spec;
        return QualType(rewritten, quals);
    }

    if (auto vec = dyn_cast_shared<VectorType>(raw)) {
        auto substituted_element = substitute_template_type_with_bindings(
            vec->element_type,
            parameters,
            argument_bindings,
            loc,
            allow_unsubstituted_parameters);
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
    bool allow_unsubstituted_parameters) {
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
                if (!build_pack_element_argument_bindings(
                        parameters,
                        active_bindings,
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
                    allow_unsubstituted_parameters);
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
                                rewritten.push_back(*replacement);
                                return true;
                            }
                        }
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
                                rewritten.push_back(*replacement);
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
                    allow_unsubstituted_parameters);
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
                                    allow_unsubstituted_parameters);
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
                                allow_unsubstituted_parameters);
                        };
                    auto clone_pass_builder =
                        make_template_binding_clone_pass_builder(
                            ast_ctx_.get(),
                            parameters,
                            active_bindings,
                            loc,
                            "non-type template argument substitution requires a concrete integral value",
                            rewrite_bound_template_type,
                            rewrite_bound_template_arguments,
                            {},
                            {});
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
                    if (!resolve_dependent_expr_after_substitution(
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

                    ConstEvalResult eval = evaluate_with_consteval_compat(
                        cloned_expr.get(),
                        ConstEvalMode::cpp_non_type_template_argument());
                    if (eval.status == ConstEvalStatus::Constant &&
                        eval.value.has_value()) {
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
                        new_argument.is_dependent =
                            template_arguments_depend_on_template_parameters(
                                std::vector<TemplateArgument>{new_argument});
                        new_argument.value_expr =
                            std::shared_ptr<Expr>(cloned_expr.release());
                        new_argument.referenced_parameter = nullptr;
                    }
                }

                if (!new_argument.is_dependent &&
                    new_argument.value_type &&
                    auto_type_utils::auto_type_flavors_in(
                        new_argument.value_type.get_shared()) == 0) {
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
