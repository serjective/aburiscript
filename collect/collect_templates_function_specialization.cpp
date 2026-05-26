#include "collect.h"
#include "collect_templates_internal.h"

using template_sema_internal::build_pack_element_argument_bindings;
using template_sema_internal::clone_and_finalize_ctor_initializers_for_specialization;
using template_sema_internal::clone_function_body_for_specialization;
using template_sema_internal::clone_function_parameters_for_specialization;
using template_sema_internal::copy_cpp_member_decl_info;
using template_sema_internal::lookup_symbol_remap_in_clone_context;
using template_sema_internal::make_template_binding_clone_pass_builder;
using template_sema_internal::materialize_specialized_fold_expression;
using template_sema_internal::normalize_concrete_template_value_argument;
using template_sema_internal::rebind_member_expr_for_specialized_record;
using template_sema_internal::rebind_specialized_function_owner;
using template_sema_internal::substitute_cpp_explicit_specifier_for_specialization;
using template_sema_internal::template_argument_has_known_payload;
using template_sema_internal::template_arguments_depend_on_template_parameters;
using template_sema_internal::TemplateSubstitutionPass;

struct Collect::FunctionTemplateSpecializationInstantiator {
    Collect& collect;
    const FunctionTemplateDecl* function_template = nullptr;
    const std::vector<TemplateArgument>& arguments;
    SrcLoc loc;
    std::shared_ptr<Symbol>* specialization_symbol_out = nullptr;
    bool instantiate_definition = true;

    const FuncDecl* pattern = nullptr;
    TemplateArgumentBindings specialization_bindings;
    std::vector<TemplateArgument> normalized_arguments;
    bool specialization_is_dependent = false;
    FunctionTemplateSpecializationEntry* entry = nullptr;
    TemplateSubstitutionPass* active_clone_pass = nullptr;

    FunctionTemplateSpecializationInstantiator(
        Collect& collect,
        const FunctionTemplateDecl* function_template,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc,
        std::shared_ptr<Symbol>* specialization_symbol_out,
        bool instantiate_definition)
        : collect(collect),
          function_template(function_template),
          arguments(arguments),
          loc(loc),
          specialization_symbol_out(specialization_symbol_out),
          instantiate_definition(instantiate_definition) {}

    ASTContext* ast_ctx() const { return collect.ast_ctx_.get(); }

    bool fail(const std::string& message, SrcLoc error_loc) {
        collect.report_error(message, error_loc);
        return false;
    }

    bool fail_instantiation(const std::string& message, SrcLoc error_loc) {
        collect.report_error(message, error_loc);
        if (entry) {
            entry->instantiation_failed = true;
        }
        return false;
    }

    struct ScopedActiveClonePass {
        FunctionTemplateSpecializationInstantiator& instantiator;
        TemplateSubstitutionPass* saved = nullptr;

        ScopedActiveClonePass(
            FunctionTemplateSpecializationInstantiator& instantiator,
            TemplateSubstitutionPass* active)
            : instantiator(instantiator),
              saved(instantiator.active_clone_pass) {
            instantiator.active_clone_pass = active;
        }

        ~ScopedActiveClonePass() {
            instantiator.active_clone_pass = saved;
        }
    };

    ASTCloneContext* active_clone_context() const {
        return active_clone_pass ? &active_clone_pass->context() : nullptr;
    }

    QualType rewrite_function_template_type_for_bindings(
        QualType type,
        const TemplateArgumentBindings& bindings) {
        auto rewritten = collect.substitute_template_type_with_bindings(
            type,
            function_template->parameters,
            bindings,
            loc,
            false,
            active_clone_context());
        return collect.finalize_deferred_semantic_type(rewritten, loc);
    }

    std::vector<TemplateArgument>
    rewrite_function_template_arguments_for_bindings(
        const std::vector<TemplateArgument>& template_arguments,
        const TemplateArgumentBindings& bindings) {
        return collect.substitute_template_arguments_with_bindings(
            template_arguments,
            function_template->parameters,
            bindings,
            loc,
            false,
            active_clone_context());
    }

    static std::vector<std::string> split_qualifier_prefix(
        const std::string& qualifier_prefix) {
        std::vector<std::string> qualifiers;
        size_t start = 0;
        while (start < qualifier_prefix.size()) {
            size_t end = qualifier_prefix.find("::", start);
            if (end == std::string::npos) {
                end = qualifier_prefix.size();
            }
            if (end > start) {
                qualifiers.push_back(qualifier_prefix.substr(start, end - start));
            }
            start = end + 2;
        }
        return qualifiers;
    }

    const FunctionTemplateDecl* preferred_function_template_redeclaration(
        const FunctionTemplateDecl* candidate) const {
        if (!candidate || !candidate->function_decl()) {
            return candidate;
        }
        const auto* function_decl = candidate->function_decl();
        if (get_func_decl_owner_record_type(function_decl)) {
            return candidate;
        }
        if (function_decl->name.empty() ||
            !collect.session_.translation_unit_decl_context_) {
            return candidate;
        }

        LookupEngine::QualifiedLookupResult lookup;
        if (const auto* qualifier_prefix =
                get_func_decl_cxx_qualifier_prefix(function_decl)) {
            LookupEngine::QualifiedNameSpec name_spec;
            name_spec.qualifiers = split_qualifier_prefix(*qualifier_prefix);
            name_spec.terminal_name = function_decl->name;
            lookup = LookupEngine::lookup_qualified_name(
                name_spec,
                collect.session_.translation_unit_decl_context_.get(),
                LookupNamespace::Ordinary);
        } else {
            lookup = LookupEngine::lookup_qualified(
                function_decl->name,
                collect.session_.translation_unit_decl_context_.get(),
                LookupNamespace::Ordinary);
        }
        if (lookup.status != LookupEngine::QualifiedLookupStatus::Found ||
            !lookup.binding) {
            return candidate;
        }

        const FunctionTemplateDecl* best = candidate;
        auto consider = [&](const Decl* decl) {
            auto* function_template =
                dyn_cast<FunctionTemplateDecl>(const_cast<Decl*>(decl));
            if (!function_template ||
                !template_decls_share_lookup_identity(candidate, function_template)) {
                return;
            }
            if (!best ||
                template_decl_is_preferred_lookup_representative(
                    best,
                    function_template)) {
                best = function_template;
            }
        };
        consider(lookup.binding->template_decl);
        for (const auto* template_candidate :
             lookup.binding->template_overload_candidates) {
            consider(template_candidate);
        }
        return best ? best : candidate;
    }

    FuncDecl* run() {
        if (specialization_symbol_out) {
            *specialization_symbol_out = nullptr;
        }
        if (!function_template || !ast_ctx()) {
            return nullptr;
        }

        function_template =
            preferred_function_template_redeclaration(function_template);
        pattern = function_template->function_decl();
        if (!pattern) {
            fail("internal error: missing function template pattern", loc);
            return nullptr;
        }

        if (!bind_and_normalize_arguments()) {
            return nullptr;
        }
        if (auto* explicit_decl = try_explicit_specialization()) {
            return explicit_decl;
        }
        if (!prepare_entry()) {
            return nullptr;
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
        if (entry->is_instantiated || !instantiate_definition ||
            entry->is_instantiating || specialization_is_dependent) {
            return entry->specialization_decl.get();
        }
        return instantiate_entry_definition();
    }

    bool bind_and_normalize_arguments() {
        std::string binding_error;
        if (!collect.bind_template_arguments_for_specialization(
                function_template,
                arguments,
                specialization_bindings,
                loc,
                &binding_error)) {
            return fail(
                "function template '" + pattern->name +
                    "' template arguments do not match the parameter list" +
                    (binding_error.empty() ? std::string() : ": " + binding_error),
                loc);
        }

        for (const auto& argument : arguments) {
            if (!template_argument_has_known_payload(argument)) {
                return fail("function template argument has unknown type", loc);
            }
        }
        if (!normalize_non_type_arguments()) {
            return false;
        }

        normalized_arguments =
            flatten_template_argument_bindings(specialization_bindings);
        specialization_is_dependent =
            template_arguments_depend_on_template_parameters(normalized_arguments);
        if (!specialization_is_dependent &&
            !collect.are_template_constraints_satisfied_with_bindings(
                function_template,
                specialization_bindings,
                loc)) {
            return fail(
                "constraints not satisfied for function template '" +
                    pattern->name + "'",
                loc);
        }
        return true;
    }

    bool normalize_non_type_arguments() {
        for (size_t idx = 0; idx < function_template->parameters.size(); ++idx) {
            auto* non_type_parameter = dyn_cast<TemplateNonTypeParmDecl>(
                function_template->parameters[idx].get());
            if (!non_type_parameter || idx >= specialization_bindings.size()) {
                continue;
            }
            if (specialization_bindings[idx].arguments.empty()) {
                continue;
            }

            QualType expected_type = collect.substitute_template_type_with_bindings(
                non_type_parameter->type,
                function_template->parameters,
                specialization_bindings,
                loc);
            expected_type =
                collect.finalize_deferred_semantic_type(expected_type, loc);
            for (auto& bound_argument : specialization_bindings[idx].arguments) {
                std::string normalize_error;
                if (!normalize_concrete_template_value_argument(
                        bound_argument,
                        expected_type,
                        &normalize_error)) {
                    return fail(
                        normalize_error.empty()
                            ? "failed to normalize function template value argument"
                            : normalize_error,
                        loc);
                }
            }
        }
        return true;
    }

    bool same_owner_type(QualType lhs, QualType rhs) const {
        if (!lhs || !rhs) {
            return !lhs && !rhs;
        }
        return desugar_type(lhs, ast_ctx())
            .equals_unqualified(desugar_type(rhs, ast_ctx()));
    }

    static bool same_qualifier_prefix(
        const std::string* lhs,
        const std::string* rhs) {
        if (lhs == rhs) {
            return true;
        }
        if (!lhs || !rhs) {
            return false;
        }
        return *lhs == *rhs;
    }

    std::shared_ptr<Symbol> lookup_existing_function_symbol_for_decl(
        const FuncDecl* decl) const {
        if (!decl || !collect.session_.current_global_scope_ || decl->name.empty()) {
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

        if (collect.session_.translation_unit_decl_context_) {
            if (auto symbol = lookup_in_decl_context(
                    collect.session_.translation_unit_decl_context_.get())) {
                return symbol;
            }
        }
        if (!collect.session_.current_global_scope_) {
            return nullptr;
        }

        auto it =
            collect.session_.current_global_scope_->all_variables.find(decl->name);
        if (it == collect.session_.current_global_scope_->all_variables.end()) {
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
                !desugar_type(symbol->type, ast_ctx())
                     .equals_unqualified(
                         desugar_type(QualType(decl->type), ast_ctx()))) {
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
    }

    const TemplateExplicitSpecializationDecl* lookup_explicit_specialization() const {
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
                desugar_type(owner_type, ast_ctx()).as_shared<ObjectType>();
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
    }

    void copy_function_symbol_metadata(
        const FuncDecl* source_decl,
        Symbol* symbol) const {
        if (!source_decl || !symbol) {
            return;
        }
        symbol->is_constexpr = source_decl->is_constexpr;
        symbol->is_consteval = source_decl->is_consteval;
        symbol->is_deleted = source_decl->is_deleted;
        symbol->is_defaulted = source_decl->is_defaulted;
        symbol->set_language_linkage(source_decl->get_language_linkage());
        if (source_decl->asm_label) {
            symbol->asm_label = *source_decl->asm_label;
        }
        auto source_symbol = lookup_existing_function_symbol_for_decl(source_decl);
        if (const auto* qualifier_prefix =
                get_func_decl_cxx_qualifier_prefix(source_decl)) {
            set_symbol_cxx_qualifier_prefix(
                symbol,
                std::string(*qualifier_prefix));
        } else if (source_symbol) {
            if (const auto* qualifier_prefix =
                    get_symbol_cxx_qualifier_prefix(source_symbol.get())) {
                set_symbol_cxx_qualifier_prefix(
                    symbol,
                    std::string(*qualifier_prefix));
            }
        }
        if (QualType owner_type = get_func_decl_owner_record_type(source_decl)) {
            set_symbol_owner_record_type(symbol, owner_type);
        } else if (source_symbol) {
            if (QualType owner_type =
                    get_symbol_owner_record_type(source_symbol.get())) {
                set_symbol_owner_record_type(symbol, owner_type);
            }
        }
    }

    std::shared_ptr<Symbol> synthesize_explicit_specialization_symbol(
        FuncDecl* explicit_decl,
        bool is_definition) const {
        VariableLinkage linkage =
            function_symbol_linkage_for_storage(
                explicit_decl->storage_class,
                static_cast<bool>(
                    get_func_decl_owner_record_type(explicit_decl)));
        auto synthesized_symbol = std::make_shared<Symbol>(
            explicit_decl->name,
            SymbolKind::FUNCTION,
            QualType(explicit_decl->type),
            explicit_decl->storage_class,
            linkage,
            explicit_decl->is_inline != 0);
        synthesized_symbol->is_defined = is_definition;
        synthesized_symbol->function_definition = explicit_decl;
        copy_function_symbol_metadata(explicit_decl, synthesized_symbol.get());
        return synthesized_symbol;
    }

    FuncDecl* try_explicit_specialization() {
        const auto* explicit_specialization = lookup_explicit_specialization();
        if (!explicit_specialization) {
            return nullptr;
        }

        auto* explicit_decl = dyn_cast<FuncDecl>(
            const_cast<Decl*>(explicit_specialization->get_specialized_decl()));
        if (!explicit_decl) {
            fail(
                "internal error: explicit function specialization did not preserve a function declaration",
                loc);
            return nullptr;
        }
        if (QualType owner_type =
                get_func_decl_owner_record_type(function_template->function_decl())) {
            rebind_specialized_function_owner(
                explicit_decl,
                owner_type,
                ast_ctx());
        }
        if (specialization_symbol_out) {
            *specialization_symbol_out =
                lookup_existing_function_symbol_for_decl(explicit_decl);
            if (!*specialization_symbol_out) {
                *specialization_symbol_out =
                    synthesize_explicit_specialization_symbol(
                        explicit_decl,
                        explicit_specialization->is_definition());
            }
        }
        return explicit_decl;
    }

    std::shared_ptr<FunctionType> build_specialization_function_type() {
        auto substituted_function_type = collect.substitute_template_type(
            QualType(pattern->type),
            function_template->parameters,
            normalized_arguments,
            loc);
        substituted_function_type =
            collect.finalize_template_semantic_type_for_storage(
                substituted_function_type,
                loc);
        auto canonical_function_type =
            substituted_function_type.as_shared<FunctionType>();
        if (!canonical_function_type) {
            fail(
                "internal error: function template specialization did not produce a function type",
                loc);
            return nullptr;
        }
        return canonical_function_type;
    }

    void apply_specialization_decl_metadata(FuncDecl* specialization_decl) const {
        if (!specialization_decl) {
            return;
        }
        if (const auto* qualifier_prefix =
                get_func_decl_cxx_qualifier_prefix(pattern)) {
            set_func_decl_cxx_qualifier_prefix(
                specialization_decl,
                std::string(*qualifier_prefix));
        }
        if (QualType owner_type = get_func_decl_owner_record_type(pattern)) {
            set_func_decl_owner_record_type(specialization_decl, owner_type);
        }
        set_func_decl_function_template_specialization(
            specialization_decl,
            FunctionTemplateSpecializationInfo{
                function_template,
                normalized_arguments});
    }

    std::unique_ptr<FuncDecl> create_specialization_decl(
        const std::shared_ptr<FunctionType>& canonical_function_type) {
        std::unique_ptr<FuncDecl> specialization_decl;
        auto substitute_explicit_specifier =
            [&](const CppExplicitSpecifier& pattern_specifier,
                FuncDecl* specialized_decl,
                CppExplicitSpecifier& specialized_specifier,
                bool& effective_value_out) -> bool {
            auto rewrite_function_template_type =
                [&](QualType type) -> QualType {
                return rewrite_function_template_type_for_bindings(
                    type,
                    specialization_bindings);
            };
            auto rewrite_function_template_arguments =
                [&](const std::vector<TemplateArgument>& template_arguments)
                    -> std::vector<TemplateArgument> {
                return rewrite_function_template_arguments_for_bindings(
                    template_arguments,
                    specialization_bindings);
            };
            auto clone_pass_builder = make_template_binding_clone_pass_builder(
                ast_ctx(),
                &collect,
                function_template->parameters,
                specialization_bindings,
                loc,
                "function template non-type parameter requires a concrete integral value",
                rewrite_function_template_type,
                rewrite_function_template_arguments,
                {},
                {});
            auto clone_pass = clone_pass_builder.build_substitution_pass();
            ScopedActiveClonePass scoped_active_clone_pass(*this, &clone_pass);
            QualType specialization_this_type =
                template_sema_internal::implicit_this_type_for_specialized_function(
                    specialized_decl);
            auto resolution_pass =
                clone_pass_builder.build_dependent_resolution_pass(
                    clone_pass,
                    [&](std::unique_ptr<Expr>& expr,
                        std::string* error_out) -> bool {
                        return collect.resolve_dependent_expr_after_substitution(
                            expr,
                            specialization_this_type,
                            error_out);
                    });
            std::string explicit_error;
            if (!substitute_cpp_explicit_specifier_for_specialization(
                    collect,
                    pattern_specifier,
                    specialized_specifier,
                    clone_pass,
                    resolution_pass,
                    loc,
                    &explicit_error)) {
                fail(
                    explicit_error.empty()
                        ? "failed to substitute explicit specifier expression"
                        : explicit_error,
                    pattern_specifier.location.isInvalid()
                        ? loc
                        : pattern_specifier.location);
                return false;
            }
            effective_value_out = specialized_specifier.effective_value;
            return true;
        };

        if (auto* pattern_ctor = dyn_cast<CppConstructorDecl>(pattern)) {
            auto specialized_ctor = collect.collect_make<CppConstructorDecl>();
            specialized_ctor->location = pattern_ctor->location;
            specialized_ctor->name = pattern_ctor->name;
            specialized_ctor->type = canonical_function_type;
            specialized_ctor->storage_class = pattern_ctor->storage_class;
            specialized_ctor->is_inline = pattern_ctor->is_inline;
            specialized_ctor->is_constexpr = pattern_ctor->is_constexpr;
            specialized_ctor->is_consteval = pattern_ctor->is_consteval;
            specialized_ctor->is_deleted = pattern_ctor->is_deleted;
            specialized_ctor->is_defaulted = pattern_ctor->is_defaulted;
            specialized_ctor->is_defaulted_on_first_declaration =
                pattern_ctor->is_defaulted_on_first_declaration;
            specialized_ctor->has_deferred_defaulted_body =
                pattern_ctor->has_deferred_defaulted_body;
            specialized_ctor->set_language_linkage(
                pattern_ctor->get_language_linkage());
            specialized_ctor->is_explicit = pattern_ctor->is_explicit;
            bool specialized_ctor_is_explicit = specialized_ctor->is_explicit;
            if (!substitute_explicit_specifier(
                    pattern_ctor->explicit_specifier,
                    specialized_ctor.get(),
                    specialized_ctor->explicit_specifier,
                    specialized_ctor_is_explicit)) {
                return nullptr;
            }
            specialized_ctor->is_explicit = specialized_ctor_is_explicit;
            if (pattern_ctor->asm_label) {
                specialized_ctor->set_asm_label(*pattern_ctor->asm_label);
            }
            copy_cpp_member_decl_info(
                ast_ctx(),
                pattern_ctor->node_id,
                specialized_ctor->node_id);
            if (auto* member_info =
                    ast_ctx()->get_cpp_member_decl_info(
                        specialized_ctor->node_id)) {
                member_info->is_explicit = specialized_ctor->is_explicit;
            }
            specialization_decl = std::move(specialized_ctor);
        } else if (auto* pattern_method = dyn_cast<CppMethodDecl>(pattern)) {
            auto specialized_method = collect.collect_make<CppMethodDecl>();
            specialized_method->location = pattern_method->location;
            specialized_method->name = pattern_method->name;
            specialized_method->type = canonical_function_type;
            specialized_method->storage_class = pattern_method->storage_class;
            specialized_method->is_inline = pattern_method->is_inline;
            specialized_method->is_constexpr = pattern_method->is_constexpr;
            specialized_method->is_consteval = pattern_method->is_consteval;
            specialized_method->is_deleted = pattern_method->is_deleted;
            specialized_method->is_defaulted = pattern_method->is_defaulted;
            specialized_method->is_defaulted_on_first_declaration =
                pattern_method->is_defaulted_on_first_declaration;
            specialized_method->has_deferred_defaulted_body =
                pattern_method->has_deferred_defaulted_body;
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
            bool specialized_method_is_explicit =
                specialized_method->is_explicit_conversion;
            if (!substitute_explicit_specifier(
                    pattern_method->explicit_specifier,
                    specialized_method.get(),
                    specialized_method->explicit_specifier,
                    specialized_method_is_explicit)) {
                return nullptr;
            }
            specialized_method->is_explicit_conversion =
                specialized_method_is_explicit;
            if (pattern_method->conversion_target_type) {
                specialized_method->conversion_target_type =
                    collect.finalize_deferred_semantic_type(
                        collect.substitute_template_type(
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
                ast_ctx(),
                pattern_method->node_id,
                specialized_method->node_id);
            if (auto* member_info =
                    ast_ctx()->get_cpp_member_decl_info(
                        specialized_method->node_id)) {
                member_info->is_explicit =
                    specialized_method->is_explicit_conversion;
            }
            specialization_decl = std::move(specialized_method);
        } else {
            auto specialized_function = collect.collect_make<FuncDecl>();
            specialized_function->location = pattern->location;
            specialized_function->name = pattern->name;
            specialized_function->type = canonical_function_type;
            specialized_function->storage_class = pattern->storage_class;
            specialized_function->is_inline = pattern->is_inline;
            specialized_function->is_constexpr = pattern->is_constexpr;
            specialized_function->is_consteval = pattern->is_consteval;
            specialized_function->is_deleted = pattern->is_deleted;
            specialized_function->is_defaulted = pattern->is_defaulted;
            specialized_function->is_defaulted_on_first_declaration =
                pattern->is_defaulted_on_first_declaration;
            specialized_function->has_deferred_defaulted_body =
                pattern->has_deferred_defaulted_body;
            specialized_function->set_language_linkage(
                pattern->get_language_linkage());
            if (pattern->asm_label) {
                specialized_function->set_asm_label(*pattern->asm_label);
            }
            specialization_decl = std::move(specialized_function);
        }

        if (specialization_decl) {
            QualType friend_access_type = pattern->friend_access_type;
            if (friend_access_type) {
                friend_access_type = collect.substitute_template_type(
                    friend_access_type,
                    function_template->parameters,
                    normalized_arguments,
                    loc);
                friend_access_type =
                    collect.finalize_deferred_semantic_type(
                        friend_access_type,
                        loc);
            }
            specialization_decl->friend_access_type = friend_access_type;
        }
        apply_specialization_decl_metadata(specialization_decl.get());
        return specialization_decl;
    }

    std::shared_ptr<Symbol> create_specialization_symbol(
        const std::shared_ptr<FunctionType>& canonical_function_type) const {
        VariableLinkage linkage =
            function_symbol_linkage_for_storage(
                pattern->storage_class,
                static_cast<bool>(get_func_decl_owner_record_type(pattern)));
        auto specialization_symbol = std::make_shared<Symbol>(
            pattern->name,
            SymbolKind::FUNCTION,
            QualType(canonical_function_type),
            pattern->storage_class,
            linkage,
            pattern->is_inline != 0);
        specialization_symbol->is_defined =
            !specialization_is_dependent && function_decl_defines_entity(pattern);
        copy_function_symbol_metadata(pattern, specialization_symbol.get());
        set_symbol_function_template_specialization(
            specialization_symbol.get(),
            FunctionTemplateSpecializationInfo{
                function_template,
                normalized_arguments});
        return specialization_symbol;
    }

    bool prepare_entry() {
        entry = ast_ctx()->lookup_function_template_specialization(
            function_template,
            normalized_arguments);
        if (entry) {
            return true;
        }

        auto canonical_function_type = build_specialization_function_type();
        if (!canonical_function_type) {
            return false;
        }
        auto specialization_decl =
            create_specialization_decl(canonical_function_type);
        auto specialization_symbol =
            create_specialization_symbol(canonical_function_type);
        entry = &ast_ctx()->get_or_create_function_template_specialization(
            function_template,
            normalized_arguments,
            std::move(specialization_decl),
            specialization_symbol);
        return true;
    }

    FuncDecl* instantiate_entry_definition() {
        if (!ast_ctx()->push_template_instantiation_frame()) {
            fail_instantiation(
                "template instantiation depth exceeded while instantiating function template '" +
                    pattern->name + "'",
                loc);
            return nullptr;
        }

        if (specialization_symbol_out) {
            *specialization_symbol_out = entry->specialization_symbol;
        }

        auto* specialization_decl_ptr = entry->specialization_decl.get();
        auto specialization_symbol_ptr = entry->specialization_symbol;
        specialization_symbol_ptr->function_definition = specialization_decl_ptr;
        if (!specialization_is_dependent) {
            collect.collect_add_global_symbol(specialization_symbol_ptr);
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
        } depth_guard{ast_ctx()};

        if (specialization_decl_ptr->is_deleted ||
            specialization_decl_ptr->is_defaulted) {
            entry->is_instantiated = true;
            specialization_symbol_ptr->is_defined = true;
            return specialization_decl_ptr;
        }

        if (!clone_specialization_definition(
                specialization_decl_ptr,
                specialization_symbol_ptr)) {
            return nullptr;
        }

        entry->is_instantiated = true;
        return specialization_decl_ptr;
    }

    bool clone_specialization_definition(
        FuncDecl* specialization_decl_ptr,
        const std::shared_ptr<Symbol>& specialization_symbol_ptr) {
        std::unordered_map<const Symbol*, std::vector<std::shared_ptr<Symbol>>>
            pack_param_symbol_remap;
        auto rewrite_template_specialization_symbol_for_bindings =
            [&](const std::shared_ptr<Symbol>& sym,
                const TemplateArgumentBindings& active_bindings)
                -> std::shared_ptr<Symbol> {
                if (!sym) {
                    return nullptr;
                }
                const auto* function_specialization_info =
                    get_symbol_function_template_specialization(sym.get());
                if (function_specialization_info &&
                    function_specialization_info->primary_template) {
                    auto rewritten_arguments =
                        rewrite_function_template_arguments_for_bindings(
                            function_specialization_info->arguments,
                            active_bindings);
                    std::shared_ptr<Symbol> rewritten_symbol = nullptr;
                    auto* rewritten_decl =
                        collect.instantiate_function_template_specialization(
                            function_specialization_info->primary_template,
                            rewritten_arguments,
                            loc,
                            &rewritten_symbol,
                            /*instantiate_definition=*/true);
                    if (!rewritten_decl || !rewritten_symbol) {
                        return nullptr;
                    }
                    return rewritten_symbol;
                }

                const auto* variable_specialization_info =
                    get_symbol_variable_template_specialization(sym.get());
                if (!variable_specialization_info ||
                    !variable_specialization_info->primary_template) {
                    return nullptr;
                }

                auto rewritten_arguments =
                    rewrite_function_template_arguments_for_bindings(
                        variable_specialization_info->arguments,
                        active_bindings);
                std::shared_ptr<Symbol> rewritten_symbol = nullptr;
                auto* rewritten_decl =
                    collect.instantiate_variable_template_specialization(
                        variable_specialization_info->primary_template,
                        rewritten_arguments,
                        loc,
                        &rewritten_symbol);
                if (!rewritten_decl || !rewritten_symbol) {
                    return nullptr;
                }
                return rewritten_symbol;
            };
        auto rewrite_function_template_type =
            [&](QualType type) -> QualType {
                return rewrite_function_template_type_for_bindings(
                    type,
                    specialization_bindings);
            };
        auto rewrite_function_template_arguments =
            [&](const std::vector<TemplateArgument>& template_arguments)
                -> std::vector<TemplateArgument> {
                return rewrite_function_template_arguments_for_bindings(
                    template_arguments,
                    specialization_bindings);
            };
        auto register_specialization_symbol =
            [&](const std::shared_ptr<Symbol>& sym) {
                collect.collect_add_global_symbol(sym);
            };
        auto rewrite_specialized_member_expr =
            [&](MemberExpr* member_expr, std::string* error_out) -> bool {
                return rebind_member_expr_for_specialized_record(
                    member_expr,
                    ast_ctx(),
                    error_out);
            };

        auto clone_pass_builder = make_template_binding_clone_pass_builder(
            ast_ctx(),
            &collect,
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

                    auto element_builder =
                        make_template_binding_clone_pass_builder(
                            ast_ctx(),
                            &collect,
                            function_template->parameters,
                            element_bindings,
                            loc,
                            "function template non-type parameter requires a concrete integral value",
                            [&](QualType type) -> QualType {
                                return rewrite_function_template_type_for_bindings(
                                    type,
                                    element_bindings);
                            },
                            [&](const std::vector<TemplateArgument>& template_arguments)
                                -> std::vector<TemplateArgument> {
                                return rewrite_function_template_arguments_for_bindings(
                                    template_arguments,
                                    element_bindings);
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
                            ASTCloneContext& element_ctx)
                            -> std::shared_ptr<Symbol> {
                            if (!sym) {
                                return nullptr;
                            }
                            if (auto remapped =
                                    lookup_symbol_remap_in_clone_context(
                                        sym,
                                        element_ctx)) {
                                return remapped;
                            }
                            auto pack_symbol_it =
                                pack_param_symbol_remap.find(sym.get());
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
                    auto element_pass =
                        element_builder.build_substitution_pass();

                    std::string element_clone_error;
                    auto expanded_expr =
                        element_pass.clone_expr(
                            pattern_expr,
                            &element_clone_error);
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
                    ast_ctx(),
                    &collect,
                    function_template->parameters,
                    element_bindings,
                    loc,
                    "function template non-type parameter requires a concrete integral value",
                    [&](QualType type) -> QualType {
                        return rewrite_function_template_type_for_bindings(
                            type,
                            element_bindings);
                    },
                    [&](const std::vector<TemplateArgument>& template_arguments)
                        -> std::vector<TemplateArgument> {
                        return rewrite_function_template_arguments_for_bindings(
                            template_arguments,
                            element_bindings);
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
                        ASTCloneContext& element_ctx)
                        -> std::shared_ptr<Symbol> {
                        if (!sym) {
                            return nullptr;
                        }
                        if (auto remapped =
                                lookup_symbol_remap_in_clone_context(
                                    sym,
                                    element_ctx)) {
                            return remapped;
                        }
                        auto pack_symbol_it =
                            pack_param_symbol_remap.find(sym.get());
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
                if (!collect.resolve_dependent_expr_after_substitution(
                        element_expr,
                        specialization_this_type,
                        error_out)) {
                    return nullptr;
                }
                return element_expr;
            };
        auto clone_pass = clone_pass_builder.build_substitution_pass();
        clone_pass_ptr = &clone_pass;
        ScopedActiveClonePass scoped_active_clone_pass(*this, &clone_pass);
        auto resolution_pass =
            clone_pass_builder.build_dependent_resolution_pass(
                clone_pass,
                [&](std::unique_ptr<Expr>& expr, std::string* error_out) -> bool {
                    return materialize_specialized_fold_expression(
                        collect,
                        expr,
                        specialization_this_type,
                        collect.get_builtin_bool(),
                        function_template->parameters,
                        specialization_bindings,
                        clone_fold_pattern_element,
                        error_out) &&
                        collect.resolve_dependent_expr_after_substitution(
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
                return rewrite_function_template_type_for_bindings(
                    type,
                    element_bindings);
            };

        specialization_decl_ptr->parameters.clear();
        std::vector<const Expr*> default_arguments;
        std::string clone_error;
        if (!clone_function_parameters_for_specialization(
                collect,
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
            return fail_instantiation(
                clone_error.empty()
                    ? "internal error: function template parameter clone failed"
                    : clone_error,
                pattern->location);
        }
        specialization_symbol_ptr->type = QualType(specialization_decl_ptr->type);
        merge_symbol_cpp_default_arguments(
            specialization_symbol_ptr.get(),
            default_arguments,
            nullptr);
        resolution_pass.sync_from_substitution_pass(clone_pass);

        if (auto* pattern_ctor = dyn_cast<CppConstructorDecl>(pattern)) {
            auto* specialization_ctor =
                dyn_cast<CppConstructorDecl>(specialization_decl_ptr);
            if (!specialization_ctor) {
                return fail_instantiation(
                    "internal error: function template constructor specialization did not preserve a constructor declaration",
                    pattern->location);
            }
            if (!clone_and_finalize_ctor_initializers_for_specialization(
                    collect,
                    pattern_ctor,
                    specialization_ctor,
                    clone_pass,
                    resolution_pass,
                    &clone_error)) {
                return fail_instantiation(
                    clone_error.empty()
                        ? "constructor template initializer specialization failed"
                        : clone_error,
                    pattern_ctor->location);
            }
        }

        specialization_decl_ptr->body.reset();
        if (!clone_function_body_for_specialization(
                collect,
                pattern,
                specialization_decl_ptr,
                clone_pass,
                resolution_pass,
                "function template",
                true,
                &clone_error)) {
            return fail_instantiation(
                clone_error.empty()
                    ? "function template body cloning is not supported"
                    : clone_error,
                pattern->body ? pattern->body->location : pattern->location);
        }
        specialization_symbol_ptr->type = QualType(specialization_decl_ptr->type);
        specialization_symbol_ptr->is_defined =
            function_decl_defines_entity(specialization_decl_ptr);
        return true;
    }
};

FuncDecl* Collect::instantiate_function_template_specialization(
    const FunctionTemplateDecl* function_template,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc,
    std::shared_ptr<Symbol>* specialization_symbol_out,
    bool instantiate_definition) {
    return FunctionTemplateSpecializationInstantiator(
               *this,
               function_template,
               arguments,
               loc,
               specialization_symbol_out,
               instantiate_definition)
        .run();
}

void Collect::note_function_template_specialization_required(
    const FunctionTemplateSpecializationInfo& specialization_info,
    SrcLoc loc) {
    if (!ast_ctx_ ||
        !specialization_info.primary_template ||
        function_template_requirement_notes_suppressed()) {
        return;
    }
    auto* entry = ast_ctx_->lookup_function_template_specialization(
        specialization_info.primary_template,
        specialization_info.arguments);
    if (entry) {
        entry->note_first_required_loc(loc);
    }
}

void Collect::instantiate_pending_required_function_template_specializations() {
    if (!ast_ctx_) {
        return;
    }

    bool progressed = false;
    do {
        progressed = false;
        const auto& entries = ast_ctx_->function_template_specializations();
        const size_t entry_count = entries.size();
        for (size_t idx = 0; idx < entry_count; ++idx) {
            auto* entry = entries[idx].get();
            if (!entry ||
                !entry->primary_template ||
                entry->is_instantiated ||
                entry->is_instantiating ||
                entry->instantiation_failed ||
                entry->first_required_loc.isInvalid()) {
                continue;
            }
            const auto* pattern = entry->primary_template->function_decl();
            if (pattern && pattern->name == "declval") {
                continue;
            }
            std::shared_ptr<Symbol> ignored_symbol;
            auto* instantiated = instantiate_function_template_specialization(
                entry->primary_template,
                entry->arguments,
                entry->first_required_loc,
                &ignored_symbol,
                /*instantiate_definition=*/true);
            if (instantiated && entry->is_instantiated) {
                progressed = true;
            }
        }
    } while (progressed);
}
