#include "parser.h"

#include "../collect/lookup_engine.h"
#include "../helpers/qualified_name_utils.h"

// Parser-owned C++ qualified-name and dependent-name classification helpers.
// Keep semantic construction in Collect; keep grammar ownership and ambiguity
// decisions here so declaration and expression parsing share one seam.

const Decl* Parser::lookup_cpp_unqualified_type_template_decl(
    const std::string& component_name,
    const std::shared_ptr<Scope>& start_scope,
    bool allow_enclosing_lookup) const {
    if (!collect_ || !start_scope || component_name.empty()) {
        return nullptr;
    }

    auto select_template_decl =
        [](const DeclBinding* binding,
           LookupNamespace lookup_namespace) -> const Decl* {
            if (!binding) {
                return nullptr;
            }

            const Decl* primary_template = binding->template_decl;
            if (!primary_template &&
                binding->template_overload_candidates.size() == 1) {
                primary_template =
                    binding->template_overload_candidates.front();
            }

            if (lookup_namespace == LookupNamespace::Ordinary) {
                if (isa<AliasTemplateDecl>(primary_template) ||
                    isa<TemplateTemplateParmDecl>(primary_template)) {
                    return primary_template;
                }
                return nullptr;
            }

            if (isa<ClassTemplateDecl>(primary_template)) {
                return primary_template;
            }
            return nullptr;
        };

    auto lookup_from_scope =
        [&](const std::shared_ptr<Scope>& scope) -> const Decl* {
            if (!scope) {
                return nullptr;
            }

            if (const Decl* ordinary_template =
                    select_template_decl(
                        LookupEngine::lookup_unqualified_template_binding(
                            component_name,
                            scope,
                            allow_enclosing_lookup,
                            LookupNamespace::Ordinary),
                        LookupNamespace::Ordinary)) {
                return ordinary_template;
            }

            return select_template_decl(
                LookupEngine::lookup_unqualified_template_binding(
                    component_name,
                    scope,
                    allow_enclosing_lookup,
                    LookupNamespace::Tag),
                LookupNamespace::Tag);
        };

    if (const Decl* primary_template = lookup_from_scope(start_scope)) {
        return primary_template;
    }

    if (cxx_record_parse_stack_.empty() ||
        cxx_record_parse_stack_.back().name != component_name) {
        return nullptr;
    }

    if (cxx_record_parse_stack_.back().primary_class_template) {
        return cxx_record_parse_stack_.back().primary_class_template;
    }

    for (auto scope = start_scope; scope; scope = scope->parent) {
        const DeclContext* context = scope->associated_decl_context;
        if (!context || context->kind() != DeclContextKind::Record) {
            continue;
        }

        return lookup_from_scope(scope->parent);
    }

    return nullptr;
}

QualType Parser::lookup_cpp_current_record_nested_type(
    const std::string& component_name) const {
    if (!collect_ || component_name.empty()) {
        return QualType();
    }

    QualType current_record_lookup_type =
        collect_->collect_current_cpp_record_lookup_type();
    if (!current_record_lookup_type) {
        return QualType();
    }

    return collect_->collect_lookup_record_nested_type(
        current_record_lookup_type,
        component_name);
}

QualType Parser::prepare_cpp_qualified_type_owner(
    QualType owner_type,
    bool is_current_instantiation) {
    if (!owner_type) {
        return QualType();
    }
    if (!collect_) {
        return QualType();
    }

    if (is_current_instantiation) {
        return owner_type;
    }

    QualType realized_owner =
        collect_->collect_try_realize_deferred_semantic_type(owner_type);
    if (!realized_owner) {
        return QualType();
    }

    if (type_depends_on_template_parameters(realized_owner, ast_ctx.get())) {
        return realized_owner;
    }

    QualType lookup_owner = desugar_type(realized_owner, ast_ctx.get());
    if (!lookup_owner.as_shared<ObjectType>()) {
        return QualType();
    }

    return lookup_owner;
}

std::optional<std::vector<TemplateArgument>>
Parser::build_cpp_current_instantiation_arguments(
    const ClassTemplateDecl* class_template,
    SrcLoc loc) {
    if (!class_template) {
        return std::nullopt;
    }

    const std::vector<const TemplateParameterDecl*>* active_parameters = nullptr;
    for (auto stack_it = active_template_parameter_stack_.rbegin();
         stack_it != active_template_parameter_stack_.rend();
         ++stack_it) {
        if (stack_it->size() != class_template->parameters.size()) {
            continue;
        }
        bool compatible = true;
        for (size_t idx = 0; idx < class_template->parameters.size(); ++idx) {
            const auto* active_parameter = (*stack_it)[idx];
            const auto* canonical_parameter =
                class_template->parameters[idx].get();
            if (!active_parameter || !canonical_parameter ||
                active_parameter->get_kind() != canonical_parameter->get_kind() ||
                active_parameter->name != canonical_parameter->name ||
                active_parameter->is_parameter_pack !=
                    canonical_parameter->is_parameter_pack) {
                compatible = false;
                break;
            }
        }
        if (compatible) {
            active_parameters = &(*stack_it);
            break;
        }
    }

    std::vector<TemplateArgument> arguments;
    arguments.reserve(active_parameters ? active_parameters->size()
                                        : class_template->parameters.size());
    auto append_argument = [&](const TemplateParameterDecl* active_parameter)
        -> bool {
        if (auto* type_parameter =
                dyn_cast<TemplateTypeParmDecl>(
                    const_cast<TemplateParameterDecl*>(active_parameter))) {
            arguments.emplace_back(QualType(type_parameter->type));
            return true;
        }
        if (auto* non_type_parameter =
                dyn_cast<TemplateNonTypeParmDecl>(
                    const_cast<TemplateParameterDecl*>(active_parameter))) {
            if (!non_type_parameter->sym &&
                non_type_parameter->name.empty() &&
                get_template_parameter_default_argument(non_type_parameter)) {
                arguments.push_back(
                    *get_template_parameter_default_argument(non_type_parameter));
                return true;
            }
            if (!collect_ || !non_type_parameter->sym) {
                return false;
            }
            auto expr = collect_->collect_identifier_reference(
                non_type_parameter->name,
                non_type_parameter->sym,
                loc);
            std::shared_ptr<Expr> shared_expr(expr.release());
            arguments.push_back(
                TemplateArgument::dependent_value_argument(
                    non_type_parameter->type,
                    std::move(shared_expr),
                    non_type_parameter->name,
                    non_type_parameter));
            return true;
        }
        if (auto* template_parameter =
                dyn_cast<TemplateTemplateParmDecl>(
                    const_cast<TemplateParameterDecl*>(active_parameter))) {
            arguments.push_back(
                TemplateArgument::dependent_template_argument(
                    template_parameter->name,
                    template_parameter));
            return true;
        }
        return false;
    };

    if (active_parameters) {
        for (const auto* active_parameter : *active_parameters) {
            if (!append_argument(active_parameter)) {
                return std::nullopt;
            }
        }
    } else {
        for (const auto& parameter : class_template->parameters) {
            if (!append_argument(parameter.get())) {
                return std::nullopt;
            }
        }
    }
    return arguments;
}

QualType Parser::build_cpp_current_instantiation_type(
    const ClassTemplateDecl* primary_template,
    std::string_view type_name,
    const std::vector<TemplateArgument>& arguments) const {
    if (!primary_template || type_name.empty()) {
        return QualType();
    }
    return QualType(std::make_shared<TemplateSpecializationType>(
        std::string(type_name),
        primary_template,
        arguments,
        /*is_dependent=*/true));
}

QualType Parser::build_cpp_primary_current_instantiation_type(
    const ClassTemplateDecl* class_template,
    std::string_view type_name,
    SrcLoc loc) {
    auto current_arguments =
        build_cpp_current_instantiation_arguments(class_template, loc);
    if (!current_arguments) {
        return QualType();
    }
    return build_cpp_current_instantiation_type(
        class_template,
        type_name,
        *current_arguments);
}

QualType Parser::try_build_cpp_injected_current_instantiation_type(
    std::string_view type_name,
    SrcLoc loc) {
    if (!is_in_template_pattern_context() ||
        cxx_record_parse_stack_.empty() ||
        type_name.empty()) {
        return QualType();
    }

    const auto& current_record = cxx_record_parse_stack_.back();
    if (current_record.name != type_name) {
        return QualType();
    }
    if (current_record.current_instantiation_type) {
        return current_record.current_instantiation_type;
    }

    return build_cpp_primary_current_instantiation_type(
        current_record.primary_class_template,
        type_name,
        loc);
}

Parser::CppTypeComponentResolution Parser::resolve_cpp_unqualified_type_component(
    const std::string& component_name,
    const std::vector<TemplateArgument>& component_arguments,
    bool component_has_template_argument_list,
    SrcLoc component_loc) {
    CppTypeComponentResolution result;
    if (!component_has_template_argument_list) {
        auto current_scope =
            collect_ ? collect_->collect_current_scope() : nullptr;
        if (current_scope) {
            auto typedef_lookup =
                LookupEngine::lookup_unqualified_ordinary_result(
                    component_name,
                    current_scope,
                    /*look_parents=*/true,
                    LookupEngine::OrdinaryFilter::TypedefOnly);
            if (typedef_lookup.symbol &&
                typedef_lookup.symbol->kind == SymbolKind::TYPE) {
                result.type = typedef_lookup.symbol->type;
                result.typedef_symbol = typedef_lookup.symbol;
                result.names_current_instantiation_member =
                    cpp_type_lookup_names_current_instantiation_member(
                        typedef_lookup.owner_context,
                        result.type,
                        component_name);
                return result;
            }
        }
        if (auto current_instantiation =
                try_build_cpp_injected_current_instantiation_type(
                    component_name,
                    component_loc)) {
            result.type = current_instantiation;
            return result;
        }
        if (auto tag_type =
                collect_->collect_lookup_tag_type(component_name, true)) {
            result.type = QualType(tag_type);
            return result;
        }
        if (auto named_type =
                collect_->collect_lookup_type_name(component_name, true, true)) {
            result.type = named_type;
            return result;
        }
        result.type = lookup_cpp_current_record_nested_type(component_name);
        return result;
    }

    auto current_scope = collect_->collect_current_scope();
    if (!current_scope) {
        return result;
    }

    const Decl* primary_template =
        lookup_cpp_unqualified_type_template_decl(
            component_name,
            current_scope,
            true);
    if (!isa<AliasTemplateDecl>(primary_template) &&
        !isa<ClassTemplateDecl>(primary_template) &&
        !isa<TemplateTemplateParmDecl>(primary_template)) {
        return result;
    }

    bool is_dependent = isa<TemplateTemplateParmDecl>(primary_template);
    for (const auto& argument : component_arguments) {
        if (template_argument_depends_on_template_parameters(
                argument,
                ast_ctx.get())) {
            is_dependent = true;
            break;
        }
    }

    QualType specialization_type =
        QualType(std::make_shared<TemplateSpecializationType>(
            component_name,
            primary_template,
            component_arguments,
            is_dependent));
    if (is_dependent) {
        result.type = specialization_type;
        return result;
    }
    result.type = collect_->collect_try_realize_deferred_semantic_type(
        specialization_type);
    return result;
}

std::optional<Parser::CppDependentOwnerAnalysis>
Parser::analyze_cpp_qualified_type_owner(
    std::string_view qualifier_name,
    const std::vector<TemplateArgument>& qualifier_arguments,
    bool qualifier_has_template_argument_list,
    SrcLoc qualifier_loc) {
    auto qualifier_resolution =
        resolve_cpp_unqualified_type_component(
            std::string(qualifier_name),
            qualifier_arguments,
            qualifier_has_template_argument_list,
            qualifier_loc);
    if (!qualifier_resolution || !qualifier_resolution.type) {
        return std::nullopt;
    }
    QualType qualifier_type = qualifier_resolution.type;

    CppDependentOwnerAnalysis analysis;
    analysis.owner_type = qualifier_type;
    analysis.is_current_instantiation =
        qualifier_resolution.names_current_instantiation_member ||
        cpp_qualifier_is_current_instantiation(
            qualifier_name,
            qualifier_type);
    analysis.is_dependent =
        type_depends_on_template_parameters(
            qualifier_type,
            ast_ctx.get());
    if (!analysis.is_dependent_context()) {
        qualifier_type = prepare_cpp_qualified_type_owner(
            qualifier_type,
            analysis.is_current_instantiation);
        if (!qualifier_type) {
            return std::nullopt;
        }
        analysis.owner_type = qualifier_type;
    }
    return analysis;
}

Parser::CppQualifiedOwnerChainResolution
Parser::resolve_cpp_qualified_owner_chain(
    const std::vector<CppQualifiedNameComponent>& qualifiers,
    bool has_global_qualifier,
    SrcLoc start_loc,
    bool diagnose_dependent_names,
    std::optional<CppQualifiedOwnerSeed> initial_owner) {
    CppQualifiedOwnerChainResolution resolution;

    auto current_scope = collect_->collect_current_scope();
    auto tu_context = collect_->get_translation_unit_decl_context();
    auto current_context = collect_->get_current_decl_context();
    if (!current_scope || !tu_context || !current_context) {
        if (diagnose_dependent_names) {
            error_custloc(
                "internal error: missing scope context for qualified lookup",
                start_loc);
        }
        resolution.lookup_failed = true;
        return resolution;
    }

    auto global_scope = current_scope;
    while (global_scope && global_scope->parent) {
        global_scope = global_scope->parent;
    }
    if (!global_scope) {
        if (diagnose_dependent_names) {
            error_custloc("internal error: missing global scope", start_loc);
        }
        resolution.lookup_failed = true;
        return resolution;
    }

    resolution.lookup_scope = has_global_qualifier ? global_scope : current_scope;
    resolution.lookup_context =
        has_global_qualifier ? tu_context.get() : current_context.get();

    auto typed_owner_names_class_or_enum =
        [&](QualType owner_type) -> bool {
            auto semantic_owner = desugar_type(owner_type, ast_ctx.get());
            return static_cast<bool>(semantic_owner.as_shared<ObjectType>()) ||
                   static_cast<bool>(semantic_owner.as_shared<EnumType>());
        };

    if (initial_owner && initial_owner->owner_type) {
        resolution.owner_type = initial_owner->owner_type;
        resolution.is_current_instantiation =
            initial_owner->is_current_instantiation;
        resolution.is_dependent =
            initial_owner->is_dependent ||
            type_depends_on_template_parameters(
                resolution.owner_type,
                ast_ctx.get());

        if (!resolution.is_dependent_context()) {
            if (auto realized_owner =
                    collect_->collect_try_realize_deferred_semantic_type(
                        resolution.owner_type)) {
                resolution.owner_type = realized_owner;
            }
            resolution.is_dependent =
                type_depends_on_template_parameters(
                    resolution.owner_type,
                    ast_ctx.get());
        }

        if (!initial_owner->spelling.empty()) {
            resolution.qualifier_spellings.push_back(initial_owner->spelling);
            resolution.qualifier_chain_spelling = initial_owner->spelling;
        }

        if (initial_owner->requires_class_or_enum &&
            !resolution.is_dependent_context() &&
            !typed_owner_names_class_or_enum(resolution.owner_type)) {
            if (diagnose_dependent_names) {
                error_custloc(
                    "decltype-specifier in nested-name-specifier must name a class or enumeration type",
                    initial_owner->loc);
            }
            resolution.lookup_failed = true;
            resolution.failed_prefix_spelling = initial_owner->spelling;
            return resolution;
        }
    }

    auto template_arguments_are_dependent =
        [&](const std::vector<TemplateArgument>& arguments) {
            for (const auto& argument : arguments) {
                if (template_argument_depends_on_template_parameters(
                        argument,
                        ast_ctx.get())) {
                    return true;
                }
            }
            return false;
        };

    auto lookup_type_in_scope =
        [&](const std::shared_ptr<Scope>& scope,
            bool allow_enclosing_lookup,
            const std::string& name) -> CppTypeComponentResolution {
            CppTypeComponentResolution result;
            auto typedef_lookup =
                LookupEngine::lookup_unqualified_ordinary_result(
                    name,
                    scope,
                    allow_enclosing_lookup,
                    LookupEngine::OrdinaryFilter::TypedefOnly);
            if (typedef_lookup.symbol &&
                typedef_lookup.symbol->kind == SymbolKind::TYPE) {
                result.type = typedef_lookup.symbol->type;
                result.typedef_symbol = typedef_lookup.symbol;
                result.names_current_instantiation_member =
                    cpp_type_lookup_names_current_instantiation_member(
                        typedef_lookup.owner_context,
                        result.type,
                        name);
                return result;
            }
            if (auto tag_type = LookupEngine::lookup_tag_type(
                    name,
                    scope,
                    allow_enclosing_lookup)) {
                result.type = QualType(tag_type);
                return result;
            }
            return result;
        };

    auto lookup_record_type_in_context =
        [&](const DeclContext* start_context,
            const std::string& name,
            bool allow_enclosing_lookup) -> QualType {
            if (!start_context || name.empty()) {
                return QualType();
            }
            auto try_ctx = [&](const DeclContext* ctx) -> QualType {
                if (!ctx) {
                    return QualType();
                }
                auto* tag_binding = ctx->lookup_local(name, LookupNamespace::Tag);
                if (!tag_binding) {
                    return QualType();
                }
                return tag_binding->type;
            };

            if (!allow_enclosing_lookup) {
                return try_ctx(start_context);
            }
            for (auto* ctx = start_context; ctx; ctx = ctx->semantic_parent()) {
                if (auto record_type = try_ctx(ctx)) {
                    return record_type;
                }
            }
            return QualType();
        };

    auto lookup_type_template_in_scope =
        [&](const std::shared_ptr<Scope>& scope,
            bool allow_enclosing_lookup,
            const std::string& name) -> const Decl* {
            return lookup_cpp_unqualified_type_template_decl(
                name,
                scope,
                allow_enclosing_lookup);
        };

    auto current_record_owner_decl =
        [&](std::string_view record_name) -> const ObjectDecl* {
            if (!record_name.empty() &&
                !cxx_record_parse_stack_.empty() &&
                cxx_record_parse_stack_.back().name == record_name) {
                return cxx_record_parse_stack_.back().semantic_owner;
            }
            for (const DeclContext* ctx = current_context.get();
                 ctx;
                 ctx = ctx->semantic_parent()) {
                if (ctx->kind() != DeclContextKind::Record) {
                    continue;
                }
                if (const auto* owner_decl = dyn_cast<ObjectDecl>(ctx->owner_decl())) {
                    if (owner_decl->tag == record_name) {
                        return owner_decl;
                    }
                }
                if (ctx->lookup_name() == record_name) {
                    return dyn_cast<ObjectDecl>(ctx->owner_decl());
                }
            }
            return nullptr;
        };

    auto current_function_owner_type =
        [&]() -> QualType {
            auto fn_type = dyn_cast_shared<FunctionType>(func_type);
            if (!fn_type || fn_type->parameters.empty()) {
                return QualType();
            }
            auto this_ptr_type =
                desugar_type(fn_type->parameters.front(), ast_ctx.get())
                    .as_shared<PointerType>();
            if (!this_ptr_type) {
                return QualType();
            }
            return this_ptr_type->pointed_type;
        };

    auto current_record_matches =
        [&](std::string_view record_name) -> bool {
            if (!record_name.empty() &&
                !cxx_record_parse_stack_.empty() &&
                cxx_record_parse_stack_.back().name == record_name) {
                return true;
            }
            for (const DeclContext* ctx = current_context.get();
                 ctx;
                 ctx = ctx->semantic_parent()) {
                if (ctx->kind() != DeclContextKind::Record) {
                    continue;
                }
                if (ctx->lookup_name() == record_name) {
                    return true;
                }
                if (const auto* owner_decl = dyn_cast<ObjectDecl>(ctx->owner_decl())) {
                    if (owner_decl->tag == record_name) {
                        return true;
                    }
                }
            }
            QualType function_owner_type = current_function_owner_type();
            if (function_owner_type) {
                auto semantic_owner_type =
                    desugar_type(function_owner_type, ast_ctx.get());
                if (auto owner_record =
                        semantic_owner_type.as_shared<ObjectType>()) {
                    if (const auto* owner_decl =
                            dyn_cast<ObjectDecl>(owner_record->get_decl())) {
                        if (owner_decl->tag == record_name) {
                            return true;
                        }
                    }
                }
                if (auto owner_specialization =
                        semantic_owner_type.as<TemplateSpecializationType>()) {
                    if (owner_specialization->template_name == record_name) {
                        return true;
                    }
                }
            }
            return false;
        };

    auto append_qualifier_component =
        [&](const CppQualifiedNameComponent& component) {
            std::string component_spelling = component.spelling();
            resolution.qualifier_spellings.push_back(component_spelling);
            if (resolution.qualifier_chain_spelling.empty()) {
                resolution.qualifier_chain_spelling = component_spelling;
            } else {
                resolution.qualifier_chain_spelling += "::";
                resolution.qualifier_chain_spelling += component_spelling;
            }
        };

    auto fail_lookup =
        [&](const CppQualifiedNameComponent& component) {
            resolution.lookup_failed = true;
            std::string component_spelling = component.spelling();
            if (resolution.qualifier_chain_spelling.empty()) {
                resolution.failed_prefix_spelling = component_spelling;
            } else {
                resolution.failed_prefix_spelling =
                    resolution.qualifier_chain_spelling + "::" + component_spelling;
            }
        };

    for (size_t idx = 0; idx < qualifiers.size(); ++idx) {
        bool allow_enclosing_lookup = !has_global_qualifier && idx == 0;
        const auto& component = qualifiers[idx];

        if (component.preceded_by_template_keyword &&
            !component.has_template_argument_list) {
            if (diagnose_dependent_names) {
                error_custloc(
                    "expected template-id after 'template' keyword",
                    component.loc);
            }
            resolution.lookup_failed = true;
            return resolution;
        }

        if (!resolution.owner_type) {
            if (!component.has_template_argument_list) {
                auto namespace_scope = resolve_named_namespace_scope(
                    resolution.lookup_context,
                    component.name,
                    allow_enclosing_lookup);
                if (namespace_scope && namespace_scope->associated_decl_context) {
                    resolution.lookup_scope = namespace_scope;
                    resolution.lookup_context =
                        namespace_scope->associated_decl_context;
                    append_qualifier_component(component);
                    continue;
                }

                auto type_lookup = lookup_type_in_scope(
                    resolution.lookup_scope,
                    allow_enclosing_lookup,
                    component.name);
                resolution.owner_type = type_lookup.type;
                if (!resolution.owner_type) {
                    resolution.owner_type = lookup_record_type_in_context(
                        resolution.lookup_context,
                        component.name,
                        allow_enclosing_lookup);
                }
                if (!resolution.owner_type && allow_enclosing_lookup) {
                    resolution.owner_type =
                        lookup_cpp_current_record_nested_type(component.name);
                }
                if (!resolution.owner_type) {
                    QualType function_owner_type = current_function_owner_type();
                    if (function_owner_type) {
                        auto semantic_owner_type =
                            desugar_type(function_owner_type, ast_ctx.get());
                        bool owner_matches = false;
                        if (auto owner_record =
                                semantic_owner_type.as_shared<ObjectType>()) {
                            if (const auto* owner_decl =
                                    dyn_cast<ObjectDecl>(owner_record->get_decl())) {
                                owner_matches = owner_decl->tag == component.name;
                            }
                        } else if (auto owner_specialization =
                                       semantic_owner_type
                                           .as<TemplateSpecializationType>()) {
                            owner_matches =
                                owner_specialization->template_name == component.name;
                        }
                        if (owner_matches) {
                            resolution.owner_type = function_owner_type;
                        }
                    }
                }
                if (!resolution.owner_type &&
                    current_record_matches(component.name)) {
                    if (auto* current_class_template =
                            dyn_cast<ClassTemplateDecl>(
                                const_cast<Decl*>(
                                    lookup_type_template_in_scope(
                                        resolution.lookup_scope,
                                        allow_enclosing_lookup,
                                        component.name)))) {
                        if (auto current_arguments =
                                build_cpp_current_instantiation_arguments(
                                    current_class_template,
                                    component.loc)) {
                            resolution.owner_type =
                                QualType(std::make_shared<TemplateSpecializationType>(
                                    component.name,
                                    current_class_template,
                                    *current_arguments,
                                    /*is_dependent=*/true));
                        }
                    }
                    if (!resolution.owner_type) {
                        const auto* record_owner =
                            current_record_owner_decl(component.name);
                        QualType injected_owner_type =
                            record_owner
                                ? QualType(record_owner->get_record_type())
                                : QualType();
                        if (!injected_owner_type) {
                            injected_owner_type = current_function_owner_type();
                        }
                        if (!injected_owner_type) {
                            injected_owner_type =
                                collect_->collect_lookup_tag_type(
                                    component.name,
                                    true);
                        }
                        if (injected_owner_type) {
                            resolution.owner_type = injected_owner_type;
                        }
                    }
                }
                if (!resolution.owner_type) {
                    fail_lookup(component);
                    return resolution;
                }
                resolution.is_current_instantiation =
                    type_lookup.names_current_instantiation_member ||
                    cpp_qualifier_is_current_instantiation(
                        component.name,
                        resolution.owner_type);
                if (resolution.is_current_instantiation) {
                    auto* current_class_template =
                        dyn_cast<ClassTemplateDecl>(
                            const_cast<Decl*>(
                                lookup_type_template_in_scope(
                                    resolution.lookup_scope,
                                    allow_enclosing_lookup,
                                    component.name)));
                    if (auto current_arguments =
                            build_cpp_current_instantiation_arguments(
                                current_class_template,
                                component.loc)) {
                        resolution.owner_type =
                            QualType(std::make_shared<TemplateSpecializationType>(
                                component.name,
                                current_class_template,
                                *current_arguments,
                                /*is_dependent=*/true));
                    }
                }
                resolution.is_dependent =
                    type_depends_on_template_parameters(
                        resolution.owner_type,
                        ast_ctx.get());
                append_qualifier_component(component);
                continue;
            }

            const Decl* primary_template = lookup_type_template_in_scope(
                resolution.lookup_scope,
                allow_enclosing_lookup,
                component.name);
            if (!primary_template && allow_enclosing_lookup && collect_) {
                QualType owner_lookup_type =
                    collect_->collect_current_cpp_record_lookup_type();
                const auto* nested_template =
                    collect_->collect_lookup_record_nested_template(
                        owner_lookup_type,
                        component.name);
                if (nested_template && nested_template->decl) {
                    bool is_dependent =
                        type_depends_on_template_parameters(
                            owner_lookup_type,
                            ast_ctx.get()) ||
                        template_arguments_are_dependent(
                            component.template_arguments);
                    if (nested_template->kind ==
                            RecordSemanticState::NestedTemplateKind::Class &&
                        is_dependent) {
                        resolution.owner_type = QualType(
                            std::make_shared<TemplateSpecializationType>(
                                component.name,
                                nested_template->decl,
                                component.template_arguments,
                                true));
                    } else {
                        resolution.owner_type =
                            collect_->collect_lookup_record_nested_template_type(
                                owner_lookup_type,
                                component.name,
                                component.template_arguments,
                                component.loc);
                    }
                    if (resolution.owner_type) {
                        resolution.is_current_instantiation = false;
                        resolution.is_dependent =
                            is_dependent ||
                            type_depends_on_template_parameters(
                                resolution.owner_type,
                                ast_ctx.get());
                        append_qualifier_component(component);
                        continue;
                    }
                }
            }
            if (!primary_template) {
                fail_lookup(component);
                return resolution;
            }

            bool is_dependent =
                isa<TemplateTemplateParmDecl>(primary_template) ||
                template_arguments_are_dependent(component.template_arguments);
            QualType specialization_type(
                std::make_shared<TemplateSpecializationType>(
                    qualified_name_utils::format_cpp_qualified_name(
                        has_global_qualifier,
                        resolution.qualifier_spellings,
                        component.name),
                    primary_template,
                    component.template_arguments,
                    is_dependent));
            if (!is_dependent) {
                auto concrete_specialization =
                    collect_->collect_try_realize_deferred_semantic_type(
                        specialization_type);
                if (concrete_specialization &&
                    !type_depends_on_template_parameters(
                        concrete_specialization,
                        ast_ctx.get())) {
                    resolution.owner_type = concrete_specialization;
                } else {
                    resolution.owner_type = specialization_type;
                    is_dependent = true;
                }
            } else {
                resolution.owner_type = specialization_type;
            }
            resolution.is_current_instantiation =
                cpp_qualifier_is_current_instantiation(
                    component.name,
                    resolution.owner_type);
            resolution.is_dependent =
                is_dependent ||
                type_depends_on_template_parameters(
                    resolution.owner_type,
                    ast_ctx.get());
            append_qualifier_component(component);
            continue;
        }

        if (component.has_template_argument_list) {
            if (resolution.requires_template_keyword() &&
                !component.preceded_by_template_keyword &&
                diagnose_dependent_names) {
                diagnose_missing_cpp_template_keyword(
                    resolution.qualifier_chain_spelling,
                    component.name,
                    component.loc);
            }

            if (resolution.is_dependent_context()) {
                resolution.owner_type =
                    QualType(std::make_shared<DependentNameType>(
                        resolution.owner_type,
                        component.name,
                        component.template_arguments,
                        resolution.is_current_instantiation,
                        /*requires_typename=*/false,
                        /*is_template_id=*/true));
                resolution.is_dependent = true;
                resolution.is_current_instantiation = false;
            } else {
                auto nested_template_type =
                    collect_->collect_lookup_record_nested_template_type(
                        resolution.owner_type,
                        component.name,
                        component.template_arguments,
                        component.loc);
                if (!nested_template_type) {
                    fail_lookup(component);
                    return resolution;
                }
                resolution.owner_type = nested_template_type;
                resolution.is_dependent =
                    type_depends_on_template_parameters(
                        nested_template_type,
                        ast_ctx.get());
                resolution.is_current_instantiation = false;
            }
            append_qualifier_component(component);
            continue;
        }

        if (resolution.is_dependent_context()) {
            resolution.owner_type = QualType(std::make_shared<DependentNameType>(
                resolution.owner_type,
                component.name,
                std::vector<TemplateArgument>{},
                resolution.is_current_instantiation,
                /*requires_typename=*/false,
                /*is_template_id=*/false));
            resolution.is_dependent = true;
            resolution.is_current_instantiation = false;
        } else {
            auto nested_type =
                collect_->collect_lookup_record_nested_type(
                    resolution.owner_type,
                    component.name);
            if (!nested_type) {
                fail_lookup(component);
                return resolution;
            }
            resolution.owner_type = nested_type;
            resolution.is_dependent =
                type_depends_on_template_parameters(
                    nested_type,
                    ast_ctx.get());
            resolution.is_current_instantiation = false;
        }
        append_qualifier_component(component);
    }

    return resolution;
}

Parser::CppDependentOwnerAnalysis Parser::analyze_cpp_member_access_base(
    QualType base_type,
    bool is_arrow) const {
    CppDependentOwnerAnalysis analysis;
    if (!base_type) {
        return analysis;
    }

    QualType object_type = remove_reference(base_type, ast_ctx.get());
    if (is_arrow) {
        auto ptr_type = desugar_type(object_type, ast_ctx.get())
            .as_shared<PointerType>();
        if (!ptr_type) {
            return analysis;
        }
        object_type = ptr_type->pointed_type;
    }

    analysis.owner_type = object_type;
    analysis.is_dependent =
        type_depends_on_template_parameters(object_type, ast_ctx.get());

    if (is_in_template_pattern_context() && !cxx_record_parse_stack_.empty()) {
        const std::string& current_record_name = cxx_record_parse_stack_.back().name;
        auto object =
            desugar_type(object_type, ast_ctx.get()).as_shared<ObjectType>();
        auto* object_decl =
            object ? dyn_cast<ObjectDecl>(object->get_decl()) : nullptr;
        analysis.is_current_instantiation =
            object_decl && object_decl->tag == current_record_name;
    }

    return analysis;
}

bool Parser::starts_with_cpp_dependent_qualified_call_expression() {
    if (current_token().type != TokenType::IDENTIFIER &&
        current_token().type != TokenType::SCOPE_RESOLUTION &&
        !(current_token().type == TokenType::COLON &&
          peek_token().type == TokenType::COLON)) {
        return false;
    }

    RevertingTentativeParsingAction tentative(*this);
    bool has_global_qualifier = consume_cpp_scope_resolution();
    if (!gentle_check(TokenType::IDENTIFIER)) {
        return false;
    }

    auto parse_component = [&](bool preceded_by_template_keyword)
        -> CppQualifiedNameComponent {
        if (!gentle_check(TokenType::IDENTIFIER)) {
            return {};
        }
        CppQualifiedNameComponent component;
        component.name = current_token().value;
        component.loc = current_token().loc;
        component.preceded_by_template_keyword = preceded_by_template_keyword;
        advance();
        if (gentle_check(TokenType::LESS_THAN)) {
            RevertingTentativeParsingAction template_args(*this);
            try {
                auto parsed_arguments = parse_cpp_template_argument_list();
                if (is_cpp_scope_resolution_here()) {
                    template_args.commit();
                    component.has_template_argument_list = true;
                    component.template_arguments = std::move(parsed_arguments);
                }
            } catch (const ParseError&) {
            } catch (const FatalErrorLimitReached&) {
                throw;
            }
        }
        return component;
    };

    std::vector<CppQualifiedNameComponent> components;
    components.push_back(parse_component(false));
    while (is_cpp_scope_resolution_here()) {
        consume_cpp_scope_resolution();
        bool preceded_by_template_keyword =
            gentle_check_and_consume(TokenType::TEMPLATE);
        if (!gentle_check(TokenType::IDENTIFIER)) {
            return false;
        }
        components.push_back(parse_component(preceded_by_template_keyword));
    }

    if (components.size() < 2) {
        return false;
    }

    std::vector<CppQualifiedNameComponent> qualifiers(
        components.begin(),
        components.end() - 1);
    const auto& terminal_component = components.back();
    auto owner_chain = resolve_cpp_qualified_owner_chain(
        qualifiers,
        has_global_qualifier,
        current_token().loc,
        /*diagnose_dependent_names=*/false);
    if (!owner_chain.is_dependent_context()) {
        return false;
    }

    if (terminal_component.preceded_by_template_keyword) {
        if (!gentle_check(TokenType::LESS_THAN)) {
            return false;
        }
        parse_cpp_template_argument_list();
    } else if (gentle_check(TokenType::LESS_THAN)) {
        if (owner_chain.requires_template_keyword()) {
            return false;
        }
        parse_cpp_template_argument_list();
    }

    return gentle_check(TokenType::LEFT_PAREN);
}

std::string Parser::format_cpp_dependent_name_for_diagnostic(
    std::string_view terminal_name,
    std::string_view qualifier_name) const {
    std::string name;
    if (!qualifier_name.empty()) {
        name += qualifier_name;
        name += "::";
    }
    name += terminal_name;
    return name;
}

void Parser::diagnose_missing_cpp_template_keyword(std::string_view terminal_name,
                                                   SrcLoc loc) {
    error_custloc(
        "missing 'template' keyword prior to dependent template name '" +
            format_cpp_dependent_name_for_diagnostic(terminal_name) + "'",
        loc);
}

void Parser::diagnose_missing_cpp_template_keyword(
    std::string_view qualifier_name,
    std::string_view terminal_name,
    SrcLoc loc) {
    error_custloc(
        "missing 'template' keyword prior to dependent template name '" +
            format_cpp_dependent_name_for_diagnostic(
                terminal_name,
                qualifier_name) + "'",
        loc);
}

void Parser::diagnose_missing_cpp_typename_keyword(
    std::string_view qualifier_name,
    std::string_view terminal_name,
    SrcLoc loc) {
    error_custloc(
        "missing 'typename' prior to dependent type name '" +
            format_cpp_dependent_name_for_diagnostic(
                terminal_name,
                qualifier_name) + "'",
        loc);
}

bool Parser::cpp_qualifier_is_current_instantiation(
    std::string_view qualifier_name,
    QualType qualifier_type) const {
    if (!is_in_template_pattern_context() || cxx_record_parse_stack_.empty()) {
        return false;
    }

    const auto& current_record = cxx_record_parse_stack_.back();
    const std::string& current_record_name = current_record.name;
    if (current_record_name.empty()) {
        return false;
    }

    if (qualifier_type && current_record.current_instantiation_type) {
        QualType qualifier_canonical =
            desugar_type(qualifier_type, ast_ctx.get());
        QualType current_canonical =
            desugar_type(current_record.current_instantiation_type,
                         ast_ctx.get());
        if (qualifier_canonical &&
            current_canonical &&
            qualifier_canonical.equals_unqualified(current_canonical)) {
            return true;
        }
    }

    if (qualifier_name != current_record_name) {
        return false;
    }
    if (qualifier_type.as<ObjectType>()) {
        return true;
    }
    auto specialization = qualifier_type.as<TemplateSpecializationType>();
    return specialization && specialization->template_name == current_record_name;
}

bool Parser::cpp_type_lookup_names_current_instantiation_member(
    const DeclContext* owner_context,
    QualType type,
    std::string_view) const {
    if (!is_in_template_pattern_context() ||
        cxx_record_parse_stack_.empty() ||
        !owner_context ||
        owner_context->kind() != DeclContextKind::Record ||
        !type ||
        !type_depends_on_template_parameters(type, ast_ctx.get())) {
        return false;
    }

    const auto& current_record = cxx_record_parse_stack_.back();
    if (current_record.name.empty()) {
        return false;
    }

    if (collect_) {
        auto current_context = collect_->get_current_decl_context();
        const DeclContext* nearest_record_context = nullptr;
        for (auto* ctx = current_context.get(); ctx; ctx = ctx->semantic_parent()) {
            if (ctx->kind() == DeclContextKind::Record) {
                nearest_record_context = ctx;
                break;
            }
        }
        if (nearest_record_context == owner_context) {
            return true;
        }
    }

    const Decl* owner_decl = owner_context->owner_decl();
    if (current_record.semantic_owner && owner_decl == current_record.semantic_owner) {
        return true;
    }

    if (owner_context->lookup_name() == current_record.name) {
        return true;
    }

    if (const auto* owner_record = dyn_cast<ObjectDecl>(owner_decl)) {
        return owner_record->tag == current_record.name;
    }

    return false;
}
