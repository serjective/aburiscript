#include "collect.h"
#include "collect_templates_internal.h"

using template_sema_internal::build_pack_element_argument_bindings;
using template_sema_internal::clone_function_body_for_specialization;
using template_sema_internal::clone_function_parameters_for_specialization;
using template_sema_internal::collect_pack_expansion_shape_in_expr;
using template_sema_internal::copy_cpp_member_decl_info;
using template_sema_internal::find_pack_expansion_arity_for_bindings;
using template_sema_internal::lookup_symbol_remap_in_clone_context;
using template_sema_internal::make_template_binding_clone_pass_builder;
using template_sema_internal::normalize_concrete_template_value_argument;
using template_sema_internal::rebind_member_expr_for_specialized_record;
using template_sema_internal::rebind_specialized_function_owner;
using template_sema_internal::template_argument_has_known_payload;
using template_sema_internal::template_arguments_depend_on_template_parameters;
using template_sema_internal::TemplateSubstitutionPass;

namespace {

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

    template_sema_internal::TemplatePackExpansionShape shape;
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

} // namespace

FuncDecl* Collect::instantiate_function_template_specialization(
    const FunctionTemplateDecl* function_template,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc,
    std::shared_ptr<Symbol>* specialization_symbol_out,
    bool instantiate_definition) {
    if (specialization_symbol_out) {
        *specialization_symbol_out = nullptr;
    }
    if (!function_template || !ast_ctx_) {
        return nullptr;
    }

    const auto* pattern = function_template->function_decl();
    if (!pattern) {
        report_error("internal error: missing function template pattern", loc);
        return nullptr;
    }

    TemplateArgumentBindings specialization_bindings;
    std::string binding_error;
    if (!bind_template_arguments_for_specialization(
            function_template,
            arguments,
            specialization_bindings,
            loc,
            &binding_error)) {
        report_error(
            "function template '" + pattern->name +
                "' template arguments do not match the parameter list" +
                (binding_error.empty() ? std::string() : ": " + binding_error),
            loc);
        return nullptr;
    }

    for (const auto& argument : arguments) {
        if (!template_argument_has_known_payload(argument)) {
            report_error("function template argument has unknown type", loc);
            return nullptr;
        }
    }
    for (size_t idx = 0; idx < function_template->parameters.size(); ++idx) {
        auto* non_type_parameter =
            dyn_cast<TemplateNonTypeParmDecl>(function_template->parameters[idx].get());
        if (!non_type_parameter || idx >= specialization_bindings.size()) {
            continue;
        }
        if (specialization_bindings[idx].arguments.empty()) {
            continue;
        }
        QualType expected_type = substitute_template_type_with_bindings(
            non_type_parameter->type,
            function_template->parameters,
            specialization_bindings,
            loc);
        expected_type = finalize_deferred_semantic_type(expected_type, loc);
        for (auto& bound_argument : specialization_bindings[idx].arguments) {
            std::string normalize_error;
            if (!normalize_concrete_template_value_argument(
                    bound_argument,
                    expected_type,
                    &normalize_error)) {
                report_error(
                    normalize_error.empty()
                        ? "failed to normalize function template value argument"
                        : normalize_error,
                    loc);
                return nullptr;
            }
        }
    }
    auto normalized_arguments =
        flatten_template_argument_bindings(specialization_bindings);
    bool specialization_is_dependent =
        template_arguments_depend_on_template_parameters(normalized_arguments);

    auto same_owner_type =
        [&](QualType lhs, QualType rhs) -> bool {
            if (!lhs || !rhs) {
                return !lhs && !rhs;
            }
            return desugar_type(lhs, ast_ctx_.get())
                .equals_unqualified(desugar_type(rhs, ast_ctx_.get()));
        };
    auto same_qualifier_prefix =
        [](const std::string* lhs, const std::string* rhs) -> bool {
            if (lhs == rhs) {
                return true;
            }
            if (!lhs || !rhs) {
                return false;
            }
            return *lhs == *rhs;
        };
    auto lookup_existing_function_symbol_for_decl =
        [&](const FuncDecl* decl) -> std::shared_ptr<Symbol> {
            if (!decl || !session_.current_global_scope_ || decl->name.empty()) {
                if (!decl || decl->name.empty()) {
                    return nullptr;
                }
            }
            std::function<std::shared_ptr<Symbol>(const DeclContext*)>
                lookup_in_decl_context =
                    [&](const DeclContext* context) -> std::shared_ptr<Symbol> {
                        if (!context) {
                            return nullptr;
                        }
                        for (const auto& binding : context->declarations()) {
                            if (!binding.symbol ||
                                binding.symbol->kind != SymbolKind::FUNCTION) {
                                continue;
                            }
                            if (binding.ast_decl == decl) {
                                return binding.symbol;
                            }
                        }
                        for (const auto& child : context->lexical_children()) {
                            if (auto symbol = lookup_in_decl_context(child.get())) {
                                return symbol;
                            }
                        }
                        return nullptr;
                    };
            if (session_.translation_unit_decl_context_) {
                if (auto symbol =
                        lookup_in_decl_context(session_.translation_unit_decl_context_.get())) {
                    return symbol;
                }
            }
            if (!session_.current_global_scope_) {
                return nullptr;
            }
            auto it = session_.current_global_scope_->all_variables.find(decl->name);
            if (it == session_.current_global_scope_->all_variables.end()) {
                return nullptr;
            }
            QualType decl_owner_type = get_func_decl_owner_record_type(decl);
            const auto* decl_qualifier_prefix =
                get_func_decl_cxx_qualifier_prefix(decl);
            for (const auto& symbol : it->second) {
                if (!symbol || symbol->kind != SymbolKind::FUNCTION) {
                    continue;
                }
                if (symbol->function_definition == decl) {
                    return symbol;
                }
                if (!symbol->type ||
                    !desugar_type(symbol->type, ast_ctx_.get())
                         .equals_unqualified(
                             desugar_type(QualType(decl->type), ast_ctx_.get()))) {
                    continue;
                }
                if (decl_owner_type &&
                    !same_owner_type(
                        get_symbol_owner_record_type(symbol.get()),
                        decl_owner_type)) {
                    continue;
                }
                if (decl_qualifier_prefix &&
                    !same_qualifier_prefix(
                        get_symbol_cxx_qualifier_prefix(symbol.get()),
                        decl_qualifier_prefix)) {
                    continue;
                }
                return symbol;
            }
            return nullptr;
        };
    auto lookup_explicit_specialization =
        [&]() -> const TemplateExplicitSpecializationDecl* {
            const auto* lookup_pattern =
                dyn_cast<FunctionTemplateDecl>(
                    const_cast<TemplateDecl*>(
                        function_template->get_pattern_template_decl()));
            if (!lookup_pattern) {
                lookup_pattern = function_template;
            }
            const auto* canonical_template =
                dyn_cast<FunctionTemplateDecl>(
                    const_cast<TemplateDecl*>(
                        get_template_decl_canonical_decl(lookup_pattern)));
            if (!canonical_template) {
                canonical_template = lookup_pattern;
            }

            std::vector<TemplateArgument> owner_specialization_arguments;
            const Decl* primary_member_decl = nullptr;
            if (canonical_template->function_decl() &&
                get_func_decl_owner_record_type(canonical_template->function_decl())) {
                primary_member_decl = canonical_template->function_decl();
                QualType owner_type =
                    get_func_decl_owner_record_type(function_template->function_decl());
                auto owner_object_type =
                    desugar_type(owner_type, ast_ctx_.get())
                        .as_shared<ObjectType>();
                if (owner_object_type &&
                    owner_object_type->is_class_template_specialization()) {
                    owner_specialization_arguments =
                        owner_object_type->get_template_specialization_arguments();
                }
            }

            return canonical_template->find_explicit_specialization(
                normalized_arguments,
                owner_specialization_arguments,
                primary_member_decl);
        };
    if (const auto* explicit_specialization = lookup_explicit_specialization()) {
        auto* explicit_decl = dyn_cast<FuncDecl>(
            const_cast<Decl*>(explicit_specialization->get_specialized_decl()));
        if (!explicit_decl) {
            report_error(
                "internal error: explicit function specialization did not preserve a function declaration",
                loc);
            return nullptr;
        }
        if (QualType owner_type =
                get_func_decl_owner_record_type(function_template->function_decl())) {
            rebind_specialized_function_owner(
                explicit_decl,
                owner_type,
                ast_ctx_.get());
        }
        if (specialization_symbol_out) {
            *specialization_symbol_out =
                lookup_existing_function_symbol_for_decl(explicit_decl);
            if (!*specialization_symbol_out) {
                VariableLinkage linkage =
                    explicit_decl->storage_class == StorageClass::STATIC
                        ? VariableLinkage::INTERNAL
                        : VariableLinkage::EXTERNAL;
                auto synthesized_symbol = std::make_shared<Symbol>(
                    explicit_decl->name,
                    SymbolKind::FUNCTION,
                    QualType(explicit_decl->type),
                    explicit_decl->storage_class,
                    linkage,
                    explicit_decl->is_inline != 0);
                synthesized_symbol->is_defined =
                    explicit_specialization->is_definition();
                synthesized_symbol->is_constexpr = explicit_decl->is_constexpr;
                synthesized_symbol->set_language_linkage(
                    explicit_decl->get_language_linkage());
                synthesized_symbol->function_definition = explicit_decl;
                if (explicit_decl->asm_label) {
                    synthesized_symbol->asm_label = *explicit_decl->asm_label;
                }
                if (const auto* qualifier_prefix =
                        get_func_decl_cxx_qualifier_prefix(explicit_decl)) {
                    set_symbol_cxx_qualifier_prefix(
                        synthesized_symbol.get(), *qualifier_prefix);
                }
                if (QualType owner_type =
                        get_func_decl_owner_record_type(explicit_decl)) {
                    set_symbol_owner_record_type(
                        synthesized_symbol.get(), owner_type);
                }
                *specialization_symbol_out = std::move(synthesized_symbol);
            }
        }
        return explicit_decl;
    }

    auto* entry = ast_ctx_->lookup_function_template_specialization(
        function_template,
        normalized_arguments);
    if (!entry) {
        auto substituted_function_type = substitute_template_type(
            QualType(pattern->type),
            function_template->parameters,
            normalized_arguments,
            loc);
        substituted_function_type =
            finalize_deferred_semantic_type(substituted_function_type, loc);
        auto canonical_function_type =
            desugar_type(substituted_function_type, ast_ctx_.get())
                .as_shared<FunctionType>();
        if (!canonical_function_type) {
            report_error(
                "internal error: function template specialization did not produce a function type",
                loc);
            return nullptr;
        }

        std::unique_ptr<FuncDecl> specialization_decl;
        if (auto* pattern_method = dyn_cast<CppMethodDecl>(pattern)) {
            auto specialized_method = collect_make<CppMethodDecl>();
            specialized_method->location = pattern_method->location;
            specialized_method->name = pattern_method->name;
            specialized_method->type = canonical_function_type;
            specialized_method->storage_class = pattern_method->storage_class;
            specialized_method->is_inline = pattern_method->is_inline;
            specialized_method->is_constexpr = pattern_method->is_constexpr;
            specialized_method->set_language_linkage(
                pattern_method->get_language_linkage());
            specialized_method->is_virtual = pattern_method->is_virtual;
            specialized_method->is_override = pattern_method->is_override;
            specialized_method->is_final = pattern_method->is_final;
            specialized_method->is_pure = pattern_method->is_pure;
            specialized_method->is_conversion_function =
                pattern_method->is_conversion_function;
            specialized_method->is_explicit_conversion =
                pattern_method->is_explicit_conversion;
            if (pattern_method->conversion_target_type) {
                specialized_method->conversion_target_type =
                    finalize_deferred_semantic_type(
                        substitute_template_type(
                            pattern_method->conversion_target_type,
                            function_template->parameters,
                            normalized_arguments,
                            loc),
                        loc);
            }
            if (pattern_method->asm_label) {
                specialized_method->set_asm_label(*pattern_method->asm_label);
            }
            copy_cpp_member_decl_info(
                ast_ctx_.get(),
                pattern_method->node_id,
                specialized_method->node_id);
            specialization_decl = std::move(specialized_method);
        } else {
            auto specialized_function = collect_make<FuncDecl>();
            specialized_function->location = pattern->location;
            specialized_function->name = pattern->name;
            specialized_function->type = canonical_function_type;
            specialized_function->storage_class = pattern->storage_class;
            specialized_function->is_inline = pattern->is_inline;
            specialized_function->is_constexpr = pattern->is_constexpr;
            specialized_function->set_language_linkage(pattern->get_language_linkage());
            if (pattern->asm_label) {
                specialized_function->set_asm_label(*pattern->asm_label);
            }
            specialization_decl = std::move(specialized_function);
        }
        if (const auto* qualifier_prefix =
                get_func_decl_cxx_qualifier_prefix(pattern)) {
            set_func_decl_cxx_qualifier_prefix(
                specialization_decl.get(), std::string(*qualifier_prefix));
        }
        if (QualType owner_type = get_func_decl_owner_record_type(pattern)) {
            set_func_decl_owner_record_type(specialization_decl.get(), owner_type);
        }
        set_func_decl_function_template_specialization(
            specialization_decl.get(),
            FunctionTemplateSpecializationInfo{
                function_template,
                normalized_arguments});

        VariableLinkage linkage =
            pattern->storage_class == StorageClass::STATIC
                ? VariableLinkage::INTERNAL
                : VariableLinkage::EXTERNAL;
        auto specialization_symbol = std::make_shared<Symbol>(
            pattern->name,
            SymbolKind::FUNCTION,
            QualType(canonical_function_type),
            pattern->storage_class,
            linkage,
            pattern->is_inline != 0);
        specialization_symbol->is_defined =
            !specialization_is_dependent && pattern->body != nullptr;
        specialization_symbol->is_constexpr = pattern->is_constexpr;
        specialization_symbol->set_language_linkage(pattern->get_language_linkage());
        if (pattern->asm_label) {
            specialization_symbol->asm_label = *pattern->asm_label;
        }
        if (const auto* qualifier_prefix =
                get_func_decl_cxx_qualifier_prefix(pattern)) {
            set_symbol_cxx_qualifier_prefix(
                specialization_symbol.get(), std::string(*qualifier_prefix));
        }
        if (QualType owner_type = get_func_decl_owner_record_type(pattern)) {
            set_symbol_owner_record_type(specialization_symbol.get(), owner_type);
        }
        set_symbol_function_template_specialization(
            specialization_symbol.get(),
            FunctionTemplateSpecializationInfo{
                function_template,
                normalized_arguments});

        entry = &ast_ctx_->get_or_create_function_template_specialization(
            function_template,
            normalized_arguments,
            std::move(specialization_decl),
            specialization_symbol);
    }

    if (!entry || !entry->specialization_decl || !entry->specialization_symbol) {
        return nullptr;
    }
    if (specialization_symbol_out) {
        *specialization_symbol_out = entry->specialization_symbol;
    }
    if (entry->instantiation_failed) {
        return nullptr;
    }
    specialization_is_dependent =
        template_arguments_depend_on_template_parameters(entry->arguments);
    if (entry->is_instantiated || !instantiate_definition || entry->is_instantiating ||
        specialization_is_dependent) {
        return entry->specialization_decl.get();
    }

    if (!ast_ctx_->push_template_instantiation_frame()) {
        report_error(
            "template instantiation depth exceeded while instantiating function template '" +
                pattern->name + "'",
            loc);
        entry->instantiation_failed = true;
        return nullptr;
    }

    if (specialization_symbol_out) {
        *specialization_symbol_out = entry->specialization_symbol;
    }

    auto* specialization_decl_ptr = entry->specialization_decl.get();
    auto specialization_symbol_ptr = entry->specialization_symbol;
    specialization_symbol_ptr->function_definition = specialization_decl_ptr;
    if (!specialization_is_dependent) {
        collect_add_global_symbol(specialization_symbol_ptr);
    }

    entry->is_instantiating = true;
    struct InstantiationGuard {
        FunctionTemplateSpecializationEntry& entry;
        ~InstantiationGuard() { entry.is_instantiating = false; }
    } instantiation_guard{*entry};
    struct DepthGuard {
        ASTContext* ast_ctx = nullptr;
        ~DepthGuard() {
            if (ast_ctx) {
                ast_ctx->pop_template_instantiation_frame();
            }
        }
    } depth_guard{ast_ctx_.get()};

    std::unordered_map<const Symbol*, std::vector<std::shared_ptr<Symbol>>>
        pack_param_symbol_remap;
    auto rewrite_template_specialization_symbol_for_bindings =
        [&](const std::shared_ptr<Symbol>& sym,
            const TemplateArgumentBindings& active_bindings)
            -> std::shared_ptr<Symbol> {
            if (!sym) {
                return nullptr;
            }
            const auto* specialization_info =
                get_symbol_function_template_specialization(sym.get());
            if (!specialization_info || !specialization_info->primary_template) {
                return nullptr;
            }
            auto rewritten_arguments = substitute_template_arguments_with_bindings(
                specialization_info->arguments,
                function_template->parameters,
                active_bindings,
                loc);
            std::shared_ptr<Symbol> rewritten_symbol = nullptr;
            auto* rewritten_decl = instantiate_function_template_specialization(
                specialization_info->primary_template,
                rewritten_arguments,
                loc,
                &rewritten_symbol,
                /*instantiate_definition=*/true);
            if (!rewritten_decl || !rewritten_symbol) {
                return nullptr;
            }
            return rewritten_symbol;
        };
    auto rewrite_function_template_type =
        [&](QualType type) -> QualType {
            auto rewritten = substitute_template_type_with_bindings(
                type,
                function_template->parameters,
                specialization_bindings,
                loc);
            return finalize_deferred_semantic_type(rewritten, loc);
        };
    auto rewrite_function_template_arguments =
        [&](const std::vector<TemplateArgument>& template_arguments)
            -> std::vector<TemplateArgument> {
            return substitute_template_arguments_with_bindings(
                template_arguments,
                function_template->parameters,
                specialization_bindings,
                loc);
        };
    auto register_specialization_symbol =
        [&](const std::shared_ptr<Symbol>& sym) {
            collect_add_global_symbol(sym);
        };
    auto rewrite_specialized_member_expr =
        [&](MemberExpr* member_expr, std::string* error_out) -> bool {
            return rebind_member_expr_for_specialized_record(
                member_expr,
                ast_ctx_.get(),
                error_out);
        };

    auto clone_pass_builder = make_template_binding_clone_pass_builder(
        ast_ctx_.get(),
        function_template->parameters,
        specialization_bindings,
        loc,
        "function template non-type parameter requires a concrete integral value",
        rewrite_function_template_type,
        rewrite_function_template_arguments,
        register_specialization_symbol,
        rewrite_specialized_member_expr);
    TemplateSubstitutionPass* clone_pass_ptr = nullptr;
    clone_pass_builder.rewrite_symbol =
        [&](const std::shared_ptr<Symbol>& sym,
            ASTCloneContext& clone_ctx) -> std::shared_ptr<Symbol> {
            if (!sym) {
                return nullptr;
            }
            if (auto remapped =
                    lookup_symbol_remap_in_clone_context(sym, clone_ctx)) {
                return remapped;
            }
            if (sym->kind == SymbolKind::FUNCTION &&
                sym->function_definition == pattern) {
                return specialization_symbol_ptr;
            }
            if (auto rewritten_template_symbol =
                    rewrite_template_specialization_symbol_for_bindings(
                        sym,
                        specialization_bindings)) {
                return rewritten_template_symbol;
            }
            return sym;
        };
    QualType specialization_this_type =
        template_sema_internal::implicit_this_type_for_specialized_function(
            specialization_decl_ptr);
    clone_pass_builder.expand_pack_expansion =
        [&](const Expr* pattern_expr,
            std::vector<std::unique_ptr<Expr>>& expanded_out,
            std::string* error_out) -> bool {
            template_sema_internal::TemplatePackExpansionShape shape;
            if (!collect_pack_expansion_shape_in_expr(
                    pattern_expr,
                    function_template->parameters,
                    shape)) {
                if (error_out && error_out->empty()) {
                    *error_out =
                        shape.has_unsupported_dependency
                            ? "pack expansion expression depends on unsupported template parameters"
                            : "failed to collect function template pack expansion shape";
                }
                return false;
            }
            if (shape.has_unsupported_dependency) {
                if (error_out && error_out->empty()) {
                    *error_out =
                        "pack expansion expression depends on unsupported template parameters";
                }
                return false;
            }
            std::string arity_error;
            auto expansion_arity = find_pack_expansion_arity_for_bindings(
                shape,
                function_template->parameters,
                specialization_bindings,
                &arity_error);
            if (!expansion_arity.has_value()) {
                if (error_out) {
                    *error_out =
                        arity_error.empty()
                            ? "failed to determine function template pack expansion arity"
                            : arity_error;
                }
                return false;
            }
            expanded_out.clear();
            expanded_out.reserve(*expansion_arity);
            for (size_t element_index = 0;
                 element_index < *expansion_arity;
                 ++element_index) {
                TemplateArgumentBindings element_bindings;
                std::string element_binding_error;
                if (!build_pack_element_argument_bindings(
                        function_template->parameters,
                        specialization_bindings,
                        element_index,
                        element_bindings,
                        &element_binding_error)) {
                    if (error_out) {
                        *error_out =
                            element_binding_error.empty()
                                ? "failed to materialize pack expansion bindings"
                                : element_binding_error;
                    }
                    return false;
                }

                auto element_builder = make_template_binding_clone_pass_builder(
                    ast_ctx_.get(),
                    function_template->parameters,
                    element_bindings,
                    loc,
                    "function template non-type parameter requires a concrete integral value",
                    [&](QualType type) -> QualType {
                        auto rewritten = substitute_template_type_with_bindings(
                            type,
                            function_template->parameters,
                            element_bindings,
                            loc);
                        return finalize_deferred_semantic_type(rewritten, loc);
                    },
                    [&](const std::vector<TemplateArgument>& template_arguments)
                        -> std::vector<TemplateArgument> {
                        return substitute_template_arguments_with_bindings(
                            template_arguments,
                            function_template->parameters,
                            element_bindings,
                            loc);
                    },
                    register_specialization_symbol,
                    rewrite_specialized_member_expr);
                element_builder.lookup_pack_size =
                    clone_pass_builder.lookup_pack_size;
                if (clone_pass_ptr) {
                    element_builder.symbol_remap =
                        clone_pass_ptr->context().symbol_remap;
                }
                element_builder.rewrite_symbol =
                    [&](const std::shared_ptr<Symbol>& sym,
                        ASTCloneContext& element_ctx) -> std::shared_ptr<Symbol> {
                        if (!sym) {
                            return nullptr;
                        }
                        if (auto remapped =
                                lookup_symbol_remap_in_clone_context(
                                    sym,
                                    element_ctx)) {
                            return remapped;
                        }
                        auto pack_symbol_it = pack_param_symbol_remap.find(sym.get());
                        if (pack_symbol_it != pack_param_symbol_remap.end()) {
                            if (element_index < pack_symbol_it->second.size()) {
                                return pack_symbol_it->second[element_index];
                            }
                            return nullptr;
                        }
                        if (sym->kind == SymbolKind::FUNCTION &&
                            sym->function_definition == pattern) {
                            return specialization_symbol_ptr;
                        }
                        if (auto rewritten_template_symbol =
                                rewrite_template_specialization_symbol_for_bindings(
                                    sym,
                                    element_bindings)) {
                            return rewritten_template_symbol;
                        }
                        return sym;
                    };
                auto element_pass = element_builder.build_substitution_pass();

                std::string element_clone_error;
                auto expanded_expr =
                    element_pass.clone_expr(pattern_expr, &element_clone_error);
                if (!expanded_expr) {
                    if (error_out) {
                        *error_out =
                            element_clone_error.empty()
                                ? "pack expansion expression cloning is not supported"
                                : element_clone_error;
                    }
                    return false;
                }
                expanded_out.push_back(std::move(expanded_expr));
            }
            return true;
        };
    auto clone_fold_pattern_element =
        [&](size_t element_index,
            const Expr* pattern_expr,
            std::string* error_out) -> std::unique_ptr<Expr> {
            TemplateArgumentBindings element_bindings;
            std::string element_binding_error;
            if (!build_pack_element_argument_bindings(
                    function_template->parameters,
                    specialization_bindings,
                    element_index,
                    element_bindings,
                    &element_binding_error)) {
                if (error_out && error_out->empty()) {
                    *error_out =
                        element_binding_error.empty()
                            ? "failed to materialize fold-expression bindings"
                            : element_binding_error;
                }
                return nullptr;
            }

            auto element_builder = make_template_binding_clone_pass_builder(
                ast_ctx_.get(),
                function_template->parameters,
                element_bindings,
                loc,
                "function template non-type parameter requires a concrete integral value",
                [&](QualType type) -> QualType {
                    auto rewritten = substitute_template_type_with_bindings(
                        type,
                        function_template->parameters,
                        element_bindings,
                        loc);
                    return finalize_deferred_semantic_type(rewritten, loc);
                },
                [&](const std::vector<TemplateArgument>& template_arguments)
                    -> std::vector<TemplateArgument> {
                    return substitute_template_arguments_with_bindings(
                        template_arguments,
                        function_template->parameters,
                        element_bindings,
                        loc);
                },
                register_specialization_symbol,
                rewrite_specialized_member_expr);
            element_builder.lookup_pack_size =
                clone_pass_builder.lookup_pack_size;
            if (clone_pass_ptr) {
                element_builder.symbol_remap =
                    clone_pass_ptr->context().symbol_remap;
            }
            element_builder.rewrite_symbol =
                [&](const std::shared_ptr<Symbol>& sym,
                    ASTCloneContext& element_ctx) -> std::shared_ptr<Symbol> {
                    if (!sym) {
                        return nullptr;
                    }
                    if (auto remapped =
                            lookup_symbol_remap_in_clone_context(
                                sym,
                                element_ctx)) {
                        return remapped;
                    }
                    auto pack_symbol_it = pack_param_symbol_remap.find(sym.get());
                    if (pack_symbol_it != pack_param_symbol_remap.end()) {
                        if (element_index < pack_symbol_it->second.size()) {
                            return pack_symbol_it->second[element_index];
                        }
                        return nullptr;
                    }
                    if (sym->kind == SymbolKind::FUNCTION &&
                        sym->function_definition == pattern) {
                        return specialization_symbol_ptr;
                    }
                    if (auto rewritten_template_symbol =
                            rewrite_template_specialization_symbol_for_bindings(
                                sym,
                                element_bindings)) {
                        return rewritten_template_symbol;
                    }
                    return sym;
                };
            auto element_pass = element_builder.build_substitution_pass();

            std::string element_clone_error;
            auto element_expr =
                element_pass.clone_expr(pattern_expr, &element_clone_error);
            if (!element_expr) {
                if (error_out && error_out->empty()) {
                    *error_out =
                        element_clone_error.empty()
                            ? "fold-expression pattern cloning is not supported"
                            : element_clone_error;
                }
                return nullptr;
            }
            if (!resolve_dependent_expr_after_substitution(
                    element_expr,
                    specialization_this_type,
                    error_out)) {
                return nullptr;
            }
            return element_expr;
        };
    auto clone_pass = clone_pass_builder.build_substitution_pass();
    clone_pass_ptr = &clone_pass;
    auto resolution_pass =
        clone_pass_builder.build_dependent_resolution_pass(
            clone_pass,
            [&](std::unique_ptr<Expr>& expr, std::string* error_out) -> bool {
                return materialize_specialized_fold_expression(
                    *this,
                    expr,
                    specialization_this_type,
                    get_builtin_bool(),
                    function_template->parameters,
                    specialization_bindings,
                    clone_fold_pattern_element,
                    error_out) &&
                    resolve_dependent_expr_after_substitution(
                    expr,
                    specialization_this_type,
                    error_out);
            });

    auto rewrite_pack_element_type =
        [&](QualType type,
            size_t element_index,
            std::string* error_out) -> QualType {
            TemplateArgumentBindings element_bindings;
            std::string binding_error;
            if (!build_pack_element_argument_bindings(
                    function_template->parameters,
                    specialization_bindings,
                    element_index,
                    element_bindings,
                    &binding_error)) {
                if (error_out && error_out->empty()) {
                    *error_out =
                        binding_error.empty()
                            ? "failed to materialize function-template pack element bindings"
                            : binding_error;
                }
                return QualType();
            }
            auto rewritten = substitute_template_type_with_bindings(
                type,
                function_template->parameters,
                element_bindings,
                loc);
            return finalize_deferred_semantic_type(rewritten, loc);
        };

    specialization_decl_ptr->parameters.clear();
    std::vector<const Expr*> default_arguments;
    std::string clone_error;
    if (!clone_function_parameters_for_specialization(
            *this,
            pattern,
            function_template->parameters,
            specialization_bindings,
            specialization_decl_ptr,
            clone_pass,
            resolution_pass,
            loc,
            "function template",
            rewrite_pack_element_type,
            &pack_param_symbol_remap,
            default_arguments,
            &clone_error)) {
        report_error(
            clone_error.empty()
                ? "internal error: function template parameter clone failed"
                : clone_error,
            pattern->location);
        entry->instantiation_failed = true;
        return nullptr;
    }
    specialization_symbol_ptr->type = QualType(specialization_decl_ptr->type);
    merge_symbol_cpp_default_arguments(
        specialization_symbol_ptr.get(),
        default_arguments,
        nullptr);
    resolution_pass.sync_from_substitution_pass(clone_pass);

    specialization_decl_ptr->body.reset();
    if (!clone_function_body_for_specialization(
            *this,
            pattern,
            specialization_decl_ptr,
            clone_pass,
            resolution_pass,
            "function template",
            true,
            &clone_error)) {
        report_error(
            clone_error.empty()
                ? "function template body cloning is not supported"
                : clone_error,
            pattern->body ? pattern->body->location : pattern->location);
        entry->instantiation_failed = true;
        return nullptr;
    }
    specialization_symbol_ptr->is_defined = specialization_decl_ptr->body != nullptr;

    entry->is_instantiated = true;
    return specialization_decl_ptr;
}
