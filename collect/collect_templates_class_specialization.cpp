#include "collect.h"
#include "collect_templates_internal.h"

#include <optional>

using namespace template_sema_internal;

namespace {

RecordMemberAccess record_member_access_for(CppAccessSpecifier access) {
    switch (access) {
        case CppAccessSpecifier::Public:
            return RecordMemberAccess::Public;
        case CppAccessSpecifier::Protected:
            return RecordMemberAccess::Protected;
        case CppAccessSpecifier::Private:
            return RecordMemberAccess::Private;
        case CppAccessSpecifier::None:
            break;
    }
    return RecordMemberAccess::Public;
}

std::optional<std::string> namespace_prefix_from_member_qualifier(
    const std::string* qualifier_prefix) {
    if (!qualifier_prefix || qualifier_prefix->empty()) {
        return std::nullopt;
    }
    size_t pos = qualifier_prefix->rfind("::");
    if (pos == std::string::npos) {
        return std::nullopt;
    }
    if (pos == 0) {
        return std::nullopt;
    }
    return qualifier_prefix->substr(0, pos);
}

struct ClassTemplatePartialSpecializationMatch {
    const ClassTemplatePartialSpecializationDecl* partial_specialization = nullptr;
    TemplateArgumentBindings bindings;
};

bool same_owner_type(QualType lhs, QualType rhs, const ASTContext* ast_ctx) {
    if (!lhs && !rhs) {
        return true;
    }
    if (!lhs || !rhs) {
        return false;
    }
    return desugar_type(lhs, ast_ctx).equals_unqualified(
        desugar_type(rhs, ast_ctx));
}

bool same_qualifier_prefix(const std::string* lhs, const std::string* rhs) {
    if (!lhs && !rhs) {
        return true;
    }
    if (!lhs || !rhs) {
        return false;
    }
    return *lhs == *rhs;
}

} // namespace

struct Collect::ClassTemplateSpecializationInstantiator {
    struct PendingMethodTemplateClone {
        const FunctionTemplateDecl* pattern_template = nullptr;
        const FuncDecl* pattern_function = nullptr;
        FunctionTemplateDecl* specialized_template = nullptr;
        std::unordered_map<const TemplateParameterDecl*,
                           const TemplateParameterDecl*> parameter_rebinds;
        std::unordered_map<const Symbol*, std::shared_ptr<Symbol>> symbol_remap;
    };

    const Collect& collect;
    const ClassTemplateDecl* class_template = nullptr;
    const std::vector<TemplateArgument>& arguments;
    SrcLoc loc;

    const CppRecordDecl* primary_pattern = nullptr;
    const CppRecordDecl* pattern = nullptr;
    const TemplateParameterList* selected_parameters = nullptr;
    const ObjectDecl* pattern_semantic_decl = nullptr;
    TemplateArgumentBindings specialization_bindings;
    std::vector<TemplateArgument> normalized_arguments;

    std::string cache_key;
    std::string specialization_name;
    bool is_union = false;
    ClassTemplateSpecializationEntry* entry = nullptr;

    const RecordSemanticState* pattern_state = nullptr;
    std::unordered_map<const CppMethodDecl*, std::shared_ptr<Symbol>>
        pattern_method_symbols;
    std::unordered_map<const CppConstructorDecl*, std::shared_ptr<Symbol>>
        pattern_constructor_symbols;
    std::unordered_map<const CppDestructorDecl*, std::shared_ptr<Symbol>>
        pattern_destructor_symbols;
    std::unordered_map<const VariableDecl*, std::shared_ptr<Symbol>>
        pattern_static_member_symbols;

    TemplateClonePassBuilder clone_pass_builder;
    TemplateSubstitutionPass clone_pass;
    TemplateSubstitutionPass* clone_pass_ptr = nullptr;

    QualType owner_type;
    std::vector<ObjectType::Field> user_fields;
    std::vector<RecordSemanticState::Method> methods;
    std::vector<RecordSemanticState::MethodTemplate> method_templates;
    std::vector<RecordSemanticState::Constructor> constructors;
    std::vector<RecordSemanticState::Destructor> destructors;
    std::vector<RecordSemanticState::StaticDataMember> static_data_members;
    std::vector<RecordSemanticState::NestedType> nested_types;
    std::vector<RecordSemanticState::NestedTemplate> nested_templates;
    std::unordered_map<const FuncDecl*, std::shared_ptr<Symbol>>
        specialized_member_symbols;
    std::vector<PendingMethodTemplateClone> pending_method_template_clones;
    std::vector<std::pair<const FuncDecl*, FuncDecl*>> pending_body_clones;
    std::vector<std::pair<const CppConstructorDecl*, CppConstructorDecl*>>
        pending_ctor_init_clones;
    RecordSemanticState semantic_state;

    ObjectDecl* run() {
        if (!class_template || !ast_ctx()) {
            return nullptr;
        }

        primary_pattern = class_template->record_decl();
        if (!primary_pattern) {
            collect.report_error("internal error: missing class template pattern", loc);
            return nullptr;
        }

        if (!bind_and_select_pattern()) {
            return nullptr;
        }
        if (auto* explicit_decl = try_explicit_specialization()) {
            return explicit_decl;
        }
        if (!prepare_entry()) {
            return nullptr;
        }
        if (!entry || !entry->specialization_decl) {
            return nullptr;
        }
        if (!entry->specialization_type) {
            entry->specialization_type = entry->specialization_decl->get_record_type();
        }
        if (entry->is_instantiated || entry->is_instantiating ||
            entry->instantiation_failed) {
            return entry->specialization_decl.get();
        }
        if (!ast_ctx()->push_template_instantiation_frame()) {
            collect.report_error(
                "template instantiation depth exceeded while instantiating class template '" +
                    specialization_name + "'",
                loc);
            entry->instantiation_failed = true;
            return entry->specialization_decl.get();
        }

        entry->is_instantiating = true;
        struct InstantiationGuard {
            ClassTemplateSpecializationEntry& entry;
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

        if (!pattern->bases.empty()) {
            fail_instantiation(
                "class template instantiation with base classes is not supported yet",
                loc);
            return entry->specialization_decl.get();
        }

        build_pattern_symbol_maps();
        owner_type = QualType(entry->specialization_type);
        if (!initialize_clone_pass() || !instantiate_members()) {
            return entry->specialization_decl.get();
        }

        build_semantic_state();
        record_semantics_cache_set(entry->specialization_decl.get(), semantic_state);
        if (!resolve_static_data_members() ||
            !clone_pending_member_templates() ||
            !clone_pending_member_bodies()) {
            return entry->specialization_decl.get();
        }

        record_semantics_cache_set(
            entry->specialization_decl.get(),
            std::move(semantic_state));
        entry->is_instantiated = pattern->is_definition;
        return entry->specialization_decl.get();
    }

    ASTContext* ast_ctx() const { return collect.ast_ctx_.get(); }

    bool fail_instantiation(const std::string& message, SrcLoc error_loc) {
        collect.report_error(message, error_loc);
        if (entry) {
            entry->instantiation_failed = true;
        }
        return false;
    }

    bool bind_and_select_pattern() {
        std::string binding_error;
        if (!collect.bind_template_arguments_for_specialization(
                class_template,
                arguments,
                specialization_bindings,
                loc,
                &binding_error)) {
            collect.report_error(
                "class template '" + primary_pattern->name +
                    "' template arguments do not match the parameter list" +
                    (binding_error.empty() ? std::string() : ": " + binding_error),
                loc);
            return false;
        }

        for (const auto& argument : arguments) {
            if (!template_argument_has_known_payload(argument)) {
                collect.report_error("class template argument has unknown type", loc);
                return false;
            }
        }
        for (size_t idx = 0; idx < class_template->parameters.size(); ++idx) {
            auto* non_type_parameter = dyn_cast<TemplateNonTypeParmDecl>(
                class_template->parameters[idx].get());
            if (!non_type_parameter || idx >= specialization_bindings.size()) {
                continue;
            }
            if (specialization_bindings[idx].arguments.empty()) {
                continue;
            }
            QualType expected_type = collect.substitute_template_type_with_bindings(
                non_type_parameter->type,
                class_template->parameters,
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
                    collect.report_error(
                        normalize_error.empty()
                            ? "failed to normalize class template value argument"
                            : normalize_error,
                        loc);
                    return false;
                }
            }
        }

        normalized_arguments =
            flatten_template_argument_bindings(specialization_bindings);
        pattern = primary_pattern;
        selected_parameters = &class_template->parameters;
        pattern_semantic_decl = class_template->pattern_semantic_decl();

        std::vector<ClassTemplatePartialSpecializationMatch> matching_partials;
        matching_partials.reserve(class_template->partial_specializations().size());
        for (const auto* partial_specialization :
             class_template->partial_specializations()) {
            if (!partial_specialization) {
                continue;
            }
            TemplateArgumentBindings partial_bindings;
            if (!deduce_class_template_partial_specialization_bindings(
                    partial_specialization,
                    normalized_arguments,
                    partial_bindings)) {
                continue;
            }
            matching_partials.push_back(ClassTemplatePartialSpecializationMatch{
                partial_specialization,
                std::move(partial_bindings)});
        }
        if (!matching_partials.empty()) {
            std::vector<size_t> maximal_matches;
            for (size_t idx = 0; idx < matching_partials.size(); ++idx) {
                bool is_less_specialized = false;
                for (size_t other_idx = 0; other_idx < matching_partials.size();
                     ++other_idx) {
                    if (idx == other_idx) {
                        continue;
                    }
                    if (is_class_template_partial_specialization_more_specialized(
                            matching_partials[other_idx].partial_specialization,
                            matching_partials[idx].partial_specialization)) {
                        is_less_specialized = true;
                        break;
                    }
                }
                if (!is_less_specialized) {
                    maximal_matches.push_back(idx);
                }
            }
            if (maximal_matches.size() != 1) {
                collect.report_error(
                    "ambiguous partial specialization for class template '" +
                        primary_pattern->name + "'",
                    loc);
                return false;
            }
            auto& selected_partial_match =
                matching_partials[maximal_matches.front()];
            pattern = selected_partial_match.partial_specialization->record_decl();
            selected_parameters =
                &selected_partial_match.partial_specialization->parameters;
            pattern_semantic_decl =
                selected_partial_match.partial_specialization
                    ->pattern_semantic_decl();
            specialization_bindings = std::move(selected_partial_match.bindings);
        }

        if (!pattern) {
            collect.report_error(
                "internal error: missing selected class template pattern",
                loc);
            return false;
        }
        return true;
    }

    ObjectDecl* try_explicit_specialization() const {
        if (const auto* explicit_specialization =
                class_template->find_explicit_specialization(
                    normalized_arguments)) {
            if (auto* explicit_decl =
                    explicit_specialization->specialized_record_semantic_decl()) {
                return const_cast<ObjectDecl*>(explicit_decl);
            }
            collect.report_error(
                "internal error: explicit class specialization is missing its semantic declaration",
                loc);
        }
        return nullptr;
    }

    bool prepare_entry() {
        cache_key = make_class_template_specialization_cache_key(
            class_template,
            normalized_arguments);
        specialization_name = make_class_template_specialization_name(
            class_template,
            normalized_arguments);
        is_union = pattern->record_kind == CppRecordKind::Union;

        if (auto* existing =
                ast_ctx()->lookup_class_template_specialization(cache_key);
            existing && existing->specialization_decl) {
            existing->note_first_required_loc(loc);
            entry = existing;
            return true;
        }

        auto specialization_type = std::make_shared<ObjectType>(
            specialization_name,
            is_union,
            !pattern->is_definition);
        specialization_type->set_class_template_specialization_info(
            class_template,
            normalized_arguments);
        auto specialization_decl = collect.collect_make<ObjectDecl>(
            specialization_name,
            specialization_type,
            is_union,
            loc);

        RecordSemanticState placeholder_state;
        placeholder_state.is_incomplete = true;
        record_semantics_cache_set(
            specialization_decl.get(),
            placeholder_state);

        auto& specialization_entry =
            ast_ctx()->get_or_create_class_template_specialization(
                cache_key,
                class_template,
                normalized_arguments,
                specialization_type,
                std::move(specialization_decl));
        specialization_entry.note_first_required_loc(loc);
        entry = &specialization_entry;
        return true;
    }

    void build_pattern_symbol_maps() {
        pattern_state = pattern_semantic_decl
            ? record_semantics_cache_lookup(pattern_semantic_decl)
            : nullptr;
        pattern_method_symbols.clear();
        pattern_constructor_symbols.clear();
        pattern_destructor_symbols.clear();
        pattern_static_member_symbols.clear();
        if (!pattern_state) {
            return;
        }
        for (const auto& method : pattern_state->methods) {
            if (method.decl && method.symbol) {
                pattern_method_symbols.emplace(method.decl, method.symbol);
            }
        }
        for (const auto& ctor : pattern_state->constructors) {
            if (ctor.decl && ctor.symbol) {
                pattern_constructor_symbols.emplace(ctor.decl, ctor.symbol);
            }
        }
        for (const auto& dtor : pattern_state->destructors) {
            if (dtor.decl && dtor.symbol) {
                pattern_destructor_symbols.emplace(dtor.decl, dtor.symbol);
            }
        }
        for (const auto& static_member : pattern_state->static_data_members) {
            if (static_member.decl && static_member.symbol) {
                pattern_static_member_symbols.emplace(
                    static_member.decl,
                    static_member.symbol);
            }
        }
    }

    QualType rewrite_class_template_type(
        QualType type,
        const TemplateArgumentBindings& active_bindings) const {
        auto rewritten = collect.substitute_template_type_with_bindings(
            type,
            *selected_parameters,
            active_bindings,
            loc,
            true);
        rewritten = replace_record_decl_in_type(
            rewritten,
            pattern_semantic_decl,
            QualType(entry->specialization_type),
            ast_ctx());
        return collect.finalize_deferred_semantic_type(rewritten, loc);
    }

    std::vector<TemplateArgument> rewrite_class_template_arguments(
        const std::vector<TemplateArgument>& template_arguments,
        const TemplateArgumentBindings& active_bindings) const {
        return collect.substitute_template_arguments_with_bindings(
            template_arguments,
            *selected_parameters,
            active_bindings,
            loc,
            true);
    }

    bool build_pack_element_bindings(
        size_t element_index,
        TemplateArgumentBindings& element_bindings,
        std::string* error_out) const {
        return build_pack_element_argument_bindings(
            *selected_parameters,
            specialization_bindings,
            element_index,
            element_bindings,
            error_out);
    }

    bool initialize_clone_pass() {
        auto register_specialized_member_symbol =
            [this](const std::shared_ptr<Symbol>& sym) {
                collect.collect_add_global_symbol(sym);
            };
        auto rewrite_specialized_record_member_expr =
            [this](MemberExpr* member_expr, std::string* error_out) -> bool {
                return rebind_member_expr_for_specialized_record(
                    member_expr,
                    ast_ctx(),
                    error_out);
            };

        clone_pass_builder = make_template_binding_clone_pass_builder(
            ast_ctx(),
            *selected_parameters,
            specialization_bindings,
            loc,
            "class template non-type parameter requires a concrete integral value",
            [this](QualType type) -> QualType {
                return rewrite_class_template_type(type, specialization_bindings);
            },
            [this](const std::vector<TemplateArgument>& template_arguments)
                -> std::vector<TemplateArgument> {
                return rewrite_class_template_arguments(
                    template_arguments,
                    specialization_bindings);
            },
            register_specialized_member_symbol,
            rewrite_specialized_record_member_expr);
        clone_pass_builder.rewrite_symbol =
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
        clone_pass_ptr = nullptr;
        clone_pass_builder.expand_pack_expansion =
            [this](const Expr* pattern_expr,
                   std::vector<std::unique_ptr<Expr>>& expanded_out,
                   std::string* error_out) -> bool {
                return expand_class_pack_expansion(
                    pattern_expr,
                    expanded_out,
                    error_out);
            };
        clone_pass = clone_pass_builder.build_substitution_pass();
        clone_pass_ptr = &clone_pass;
        return true;
    }

    bool expand_class_pack_expansion(
        const Expr* pattern_expr,
        std::vector<std::unique_ptr<Expr>>& expanded_out,
        std::string* error_out) {
        template_sema_internal::TemplatePackExpansionShape shape;
        if (!collect_pack_expansion_shape_in_expr(
                pattern_expr,
                *selected_parameters,
                shape)) {
            if (error_out && error_out->empty()) {
                *error_out =
                    shape.has_unsupported_dependency
                        ? "class template pack expansion depends on unsupported template parameters"
                        : "failed to collect class template pack expansion shape";
            }
            return false;
        }
        if (shape.has_unsupported_dependency) {
            if (error_out && error_out->empty()) {
                *error_out =
                    "class template pack expansion depends on unsupported template parameters";
            }
            return false;
        }

        std::string arity_error;
        auto expansion_arity = find_pack_expansion_arity_for_bindings(
            shape,
            *selected_parameters,
            specialization_bindings,
            &arity_error);
        if (!expansion_arity.has_value()) {
            if (error_out) {
                *error_out =
                    arity_error.empty()
                        ? "failed to determine class template pack expansion arity"
                        : arity_error;
            }
            return false;
        }

        auto register_specialized_member_symbol =
            [this](const std::shared_ptr<Symbol>& sym) {
                collect.collect_add_global_symbol(sym);
            };
        auto rewrite_specialized_record_member_expr =
            [this](MemberExpr* member_expr, std::string* error_out) -> bool {
                return rebind_member_expr_for_specialized_record(
                    member_expr,
                    ast_ctx(),
                    error_out);
            };

        expanded_out.clear();
        expanded_out.reserve(*expansion_arity);
        for (size_t element_index = 0;
             element_index < *expansion_arity;
             ++element_index) {
            TemplateArgumentBindings element_bindings;
            std::string element_binding_error;
            if (!build_pack_element_bindings(
                    element_index,
                    element_bindings,
                    &element_binding_error)) {
                if (error_out) {
                    *error_out =
                        element_binding_error.empty()
                            ? "failed to materialize class template pack expansion bindings"
                            : element_binding_error;
                }
                return false;
            }

            auto element_builder = make_template_binding_clone_pass_builder(
                ast_ctx(),
                *selected_parameters,
                element_bindings,
                loc,
                "class template non-type parameter requires a concrete integral value",
                [this, &element_bindings](QualType type) -> QualType {
                    return rewrite_class_template_type(type, element_bindings);
                },
                [this, &element_bindings](
                    const std::vector<TemplateArgument>& template_arguments)
                    -> std::vector<TemplateArgument> {
                    return rewrite_class_template_arguments(
                        template_arguments,
                        element_bindings);
                },
                register_specialized_member_symbol,
                rewrite_specialized_record_member_expr);
            element_builder.lookup_pack_size = clone_pass_builder.lookup_pack_size;
            if (clone_pass_ptr) {
                element_builder.symbol_remap =
                    clone_pass_ptr->context().symbol_remap;
            }
            element_builder.rewrite_symbol = clone_pass_builder.rewrite_symbol;

            auto element_pass = element_builder.build_substitution_pass();
            std::string element_clone_error;
            auto expanded_expr =
                element_pass.clone_expr(pattern_expr, &element_clone_error);
            if (!expanded_expr) {
                if (error_out) {
                    *error_out =
                        element_clone_error.empty()
                            ? "class template pack expansion expression cloning is not supported"
                            : element_clone_error;
                }
                return false;
            }
            expanded_out.push_back(std::move(expanded_expr));
        }
        return true;
    }

    QualType rewrite_class_pack_element_type(
        QualType type,
        size_t element_index,
        std::string* error_out) const {
        TemplateArgumentBindings element_bindings;
        std::string binding_error;
        if (!build_pack_element_bindings(
                element_index,
                element_bindings,
                &binding_error)) {
            if (error_out && error_out->empty()) {
                *error_out =
                    binding_error.empty()
                        ? "failed to materialize class-template pack element bindings"
                        : binding_error;
            }
            return QualType();
        }
        return rewrite_class_template_type(type, element_bindings);
    }

    std::shared_ptr<Symbol> lookup_existing_function_symbol_for_decl(
        const FuncDecl* decl) const {
        if (!decl) {
            return nullptr;
        }

        QualType decl_owner_type = get_func_decl_owner_record_type(decl);
        const auto* decl_qualifier_prefix =
            get_func_decl_cxx_qualifier_prefix(decl);
        std::function<std::shared_ptr<Symbol>(const DeclContext*)>
            lookup_in_decl_context =
                [&](const DeclContext* decl_context) -> std::shared_ptr<Symbol> {
                    if (!decl_context) {
                        return nullptr;
                    }
                    for (const auto& binding : decl_context->declarations()) {
                        if (!binding.symbol ||
                            binding.symbol->kind != SymbolKind::FUNCTION) {
                            continue;
                        }
                        auto& symbol = binding.symbol;
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
                                decl_owner_type,
                                ast_ctx())) {
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
                    for (const auto& child : decl_context->lexical_children()) {
                        if (auto symbol = lookup_in_decl_context(child.get())) {
                            return symbol;
                        }
                    }
                    return nullptr;
                };

        if (collect.translation_unit_decl_context_) {
            if (auto symbol = lookup_in_decl_context(
                    collect.translation_unit_decl_context_.get())) {
                return symbol;
            }
        }
        if (!collect.current_global_scope_) {
            return nullptr;
        }
        auto it =
            collect.current_global_scope_->all_variables.find(decl->name);
        if (it == collect.current_global_scope_->all_variables.end()) {
            return nullptr;
        }
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
                    decl_owner_type,
                    ast_ctx())) {
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

    std::shared_ptr<Symbol> ensure_explicit_member_function_symbol(
        const FuncDecl* decl,
        bool is_definition) const {
        auto symbol = lookup_existing_function_symbol_for_decl(decl);
        if (symbol) {
            if (QualType explicit_owner_type =
                    get_func_decl_owner_record_type(decl)) {
                set_symbol_owner_record_type(symbol.get(), explicit_owner_type);
            }
            if (const auto* qualifier_prefix =
                    get_func_decl_cxx_qualifier_prefix(decl)) {
                set_symbol_cxx_qualifier_prefix(symbol.get(), *qualifier_prefix);
            }
            symbol->type = QualType(decl->type);
            symbol->is_constexpr = decl->is_constexpr;
            symbol->is_defined = is_definition;
            symbol->set_language_linkage(decl->get_language_linkage());
            if (is_definition) {
                symbol->function_definition = const_cast<FuncDecl*>(decl);
            }
            return symbol;
        }

        VariableLinkage linkage =
            decl->storage_class == StorageClass::STATIC
                ? VariableLinkage::INTERNAL
                : VariableLinkage::EXTERNAL;
        auto synthesized_symbol = std::make_shared<Symbol>(
            decl->name,
            SymbolKind::FUNCTION,
            QualType(decl->type),
            decl->storage_class,
            linkage,
            decl->is_inline != 0);
        synthesized_symbol->is_defined = is_definition;
        synthesized_symbol->is_constexpr = decl->is_constexpr;
        synthesized_symbol->set_language_linkage(
            decl->get_language_linkage());
        synthesized_symbol->function_definition =
            is_definition ? const_cast<FuncDecl*>(decl) : nullptr;
        if (decl->asm_label) {
            synthesized_symbol->asm_label = *decl->asm_label;
        }
        if (const auto* qualifier_prefix =
                get_func_decl_cxx_qualifier_prefix(decl)) {
            set_symbol_cxx_qualifier_prefix(
                synthesized_symbol.get(),
                *qualifier_prefix);
        }
        if (QualType explicit_owner_type = get_func_decl_owner_record_type(decl)) {
            set_symbol_owner_record_type(
                synthesized_symbol.get(),
                explicit_owner_type);
        }
        collect.collect_add_global_symbol(synthesized_symbol);
        return synthesized_symbol;
    }

    const TemplateExplicitSpecializationDecl* find_explicit_member_specialization(
        const Decl* primary_member_decl) const {
        if (!primary_member_decl) {
            return nullptr;
        }
        return class_template->find_explicit_specialization(
            normalized_arguments,
            {},
            primary_member_decl);
    }

    void reserve_member_storage() {
        user_fields.clear();
        methods.clear();
        method_templates.clear();
        constructors.clear();
        destructors.clear();
        static_data_members.clear();
        nested_types.clear();
        nested_templates.clear();
        specialized_member_symbols.clear();
        pending_method_template_clones.clear();
        pending_body_clones.clear();
        pending_ctor_init_clones.clear();

        user_fields.reserve(pattern->members.size());
        methods.reserve(pattern->members.size());
        method_templates.reserve(pattern->members.size());
        constructors.reserve(pattern->members.size());
        destructors.reserve(pattern->members.size());
        static_data_members.reserve(pattern->members.size());
        nested_types.reserve(pattern->members.size());
        nested_templates.reserve(pattern->members.size());
        specialized_member_symbols.reserve(pattern->members.size());
        pending_method_template_clones.reserve(pattern->members.size());
        pending_body_clones.reserve(pattern->members.size());
        pending_ctor_init_clones.reserve(pattern->members.size());
        entry->member_decls.clear();
        entry->member_decls.reserve(pattern->members.size());
    }

    std::shared_ptr<Symbol> clone_member_symbol(
        const std::shared_ptr<Symbol>& pattern_symbol,
        QualType rewritten_type,
        const std::string* qualifier_prefix,
        bool register_global_symbol) {
        std::shared_ptr<Symbol> cloned_symbol = pattern_symbol
            ? clone_symbol_shallow_for_specialization(pattern_symbol, rewritten_type)
            : std::make_shared<Symbol>("", SymbolKind::FUNCTION, rewritten_type);
        if (qualifier_prefix && !qualifier_prefix->empty()) {
            set_symbol_cxx_qualifier_prefix(cloned_symbol.get(), *qualifier_prefix);
        }
        set_symbol_owner_record_type(cloned_symbol.get(), owner_type);
        if (register_global_symbol) {
            collect.collect_add_global_symbol(cloned_symbol);
        }
        if (pattern_symbol) {
            clone_pass.context().symbol_remap.emplace(
                pattern_symbol.get(),
                cloned_symbol);
        }
        return cloned_symbol;
    }

    void publish_provisional_nested_members() {
        RecordSemanticState provisional_state;
        if (const auto* existing_state =
                record_semantics_cache_lookup(entry->specialization_decl.get())) {
            provisional_state = *existing_state;
        }
        provisional_state.is_incomplete = true;
        provisional_state.nested_types = nested_types;
        provisional_state.nested_templates = nested_templates;
        record_semantics_cache_set(entry->specialization_decl.get(), provisional_state);
    }

    bool instantiate_members() {
        reserve_member_storage();

        CppAccessSpecifier current_access = pattern->default_access;
        for (const auto& member : pattern->members) {
            if (!member) {
                continue;
            }
            if (auto* access_decl = dyn_cast<CppAccessSpecDecl>(member.get())) {
                current_access = access_decl->access;
                continue;
            }
            if (!instantiate_member(
                    member.get(),
                    record_member_access_for(current_access))) {
                return false;
            }
        }
        return true;
    }

    bool instantiate_member(const Decl* member, RecordMemberAccess declared_access) {
        if (auto* field_decl = dyn_cast<FieldDecl>(member)) {
            return handle_field_member(field_decl, declared_access);
        }
        if (auto* static_member = dyn_cast<VariableDecl>(member)) {
            return handle_static_member(static_member, declared_access);
        }
        if (auto* typedef_decl = dyn_cast<TypedefDecl>(member)) {
            return handle_typedef_member(typedef_decl, declared_access);
        }
        if (auto* alias_template_decl = dyn_cast<AliasTemplateDecl>(member)) {
            return handle_alias_template_member(alias_template_decl, declared_access);
        }
        if (auto* method_template_decl = dyn_cast<FunctionTemplateDecl>(member)) {
            return handle_method_template_member(
                method_template_decl,
                declared_access);
        }
        if (auto* method_decl = dyn_cast<CppMethodDecl>(member)) {
            return handle_method_member(method_decl, declared_access);
        }
        if (auto* ctor_decl = dyn_cast<CppConstructorDecl>(member)) {
            return handle_constructor_member(ctor_decl, declared_access);
        }
        if (auto* dtor_decl = dyn_cast<CppDestructorDecl>(member)) {
            return handle_destructor_member(dtor_decl, declared_access);
        }
        return fail_instantiation(
            "class template instantiation for this member kind is not supported yet",
            member ? member->location : loc);
    }

    bool handle_field_member(
        const FieldDecl* field_decl,
        RecordMemberAccess declared_access) {
        auto substituted_type = collect.substitute_template_type_with_bindings(
            field_decl->type,
            *selected_parameters,
            specialization_bindings,
            field_decl->location);
        substituted_type = collect.finalize_deferred_semantic_type(
            substituted_type,
            field_decl->location);

        auto canonical_field_type = desugar_type(substituted_type);
        auto* field_object_type = canonical_field_type.as<ObjectType>();
        if (field_object_type && field_object_type->isIncomplete()) {
            return fail_instantiation(
                "field has incomplete type '" + substituted_type.to_string() + "'",
                field_decl->location);
        }

        if (field_decl->is_bitfield()) {
            user_fields.emplace_back(field_decl->name,
                                     substituted_type,
                                     0,
                                     0,
                                     field_decl->bitfield_width,
                                     0,
                                     declared_access);
        } else {
            user_fields.emplace_back(
                field_decl->name,
                substituted_type,
                0,
                declared_access);
        }
        return true;
    }

    bool handle_static_member(
        const VariableDecl* static_member,
        RecordMemberAccess declared_access) {
        std::string clone_error;
        auto cloned_decl_base = clone_pass.clone_decl(static_member, &clone_error);
        auto* cloned_decl = dyn_cast<VariableDecl>(cloned_decl_base.get());
        if (!cloned_decl_base || !cloned_decl) {
            return fail_instantiation(
                clone_error.empty()
                    ? "internal error: failed to clone class template static data member"
                    : clone_error,
                static_member->location);
        }

        auto pattern_symbol_it = pattern_static_member_symbols.find(static_member);
        std::shared_ptr<Symbol> cloned_symbol = cloned_decl->sym;
        if (!cloned_symbol &&
            pattern_symbol_it != pattern_static_member_symbols.end() &&
            pattern_symbol_it->second) {
            cloned_symbol = clone_symbol_shallow_for_specialization(
                pattern_symbol_it->second,
                desugar_type(cloned_decl->type));
            clone_pass.context().symbol_remap.emplace(
                pattern_symbol_it->second.get(),
                cloned_symbol);
            collect.collect_add_global_symbol(cloned_symbol);
            cloned_decl->sym = cloned_symbol;
        }

        auto namespace_prefix = namespace_prefix_from_member_qualifier(
            cloned_symbol
                ? get_symbol_cxx_qualifier_prefix(cloned_symbol.get())
                : nullptr);
        if (namespace_prefix.has_value() && cloned_symbol) {
            set_symbol_cxx_qualifier_prefix(
                cloned_symbol.get(),
                *namespace_prefix);
        }
        if (cloned_symbol) {
            set_symbol_owner_record_type(cloned_symbol.get(), owner_type);
            cloned_symbol->type = desugar_type(cloned_decl->type);
            cloned_symbol->storage_class = StorageClass::STATIC;
            cloned_symbol->is_constexpr = cloned_decl->is_constexpr;
            cloned_symbol->variable_definition = cloned_decl;
        }

        RecordSemanticState::StaticDataMember semantic_member;
        semantic_member.name = cloned_decl->name;
        semantic_member.type = cloned_decl->type;
        semantic_member.declared_access = declared_access;
        semantic_member.decl = cloned_decl;
        semantic_member.symbol = cloned_symbol;
        static_data_members.push_back(std::move(semantic_member));

        entry->member_decls.push_back(std::move(cloned_decl_base));
        return true;
    }

    bool handle_typedef_member(
        const TypedefDecl* typedef_decl,
        RecordMemberAccess declared_access) {
        auto rewritten_type = clone_pass.rewrite_type(typedef_decl->type);
        std::shared_ptr<Symbol> cloned_symbol = nullptr;
        if (typedef_decl->sym) {
            cloned_symbol = clone_symbol_shallow_for_specialization(
                typedef_decl->sym,
                rewritten_type);
            clone_pass.context().symbol_remap.emplace(
                typedef_decl->sym.get(),
                cloned_symbol);
        }

        auto cloned_decl = collect.collect_make<TypedefDecl>(
            typedef_decl->name,
            rewritten_type,
            cloned_symbol,
            typedef_decl->location);

        RecordSemanticState::NestedType nested_type;
        nested_type.name = cloned_decl->name;
        nested_type.type = cloned_decl->type;
        nested_type.declared_access = declared_access;
        nested_type.decl = cloned_decl.get();
        nested_type.symbol = cloned_symbol;
        nested_types.push_back(std::move(nested_type));
        publish_provisional_nested_members();

        entry->member_decls.push_back(std::move(cloned_decl));
        return true;
    }

    bool handle_alias_template_member(
        const AliasTemplateDecl* alias_template_decl,
        RecordMemberAccess declared_access) {
        auto* alias_decl = alias_template_decl->alias_decl();
        if (!alias_decl) {
            return fail_instantiation(
                "internal error: missing class template nested alias template pattern",
                alias_template_decl->location);
        }

        auto cloned_alias_decl = collect.collect_make<TypedefDecl>(
            alias_decl->name,
            QualType(),
            nullptr,
            alias_decl->location);
        auto cloned_template_decl = collect.collect_make<AliasTemplateDecl>(
            TemplateParameterList{},
            std::move(cloned_alias_decl),
            alias_template_decl->location);
        set_template_decl_canonical_decl(
            cloned_template_decl.get(),
            cloned_template_decl.get());
        cloned_template_decl->set_pattern_template_decl(alias_template_decl);

        std::unordered_map<const TemplateParameterDecl*, const TemplateParameterDecl*>
            parameter_rebinds;
        parameter_rebinds.reserve(alias_template_decl->parameters.size());

        auto alias_template_builder = make_nested_template_clone_pass_builder(
            clone_pass_builder,
            clone_pass,
            [this](const std::vector<TemplateArgument>& template_arguments)
                -> std::vector<TemplateArgument> {
                return rewrite_class_template_arguments(
                    template_arguments,
                    specialization_bindings);
            },
            parameter_rebinds,
            {});
        auto alias_template_clone_pass =
            alias_template_builder.build_substitution_pass();

        for (const auto& parameter : alias_template_decl->parameters) {
            if (!parameter) {
                return fail_instantiation(
                    "internal error: missing class template nested alias template parameter",
                    alias_template_decl->location);
            }

            if (auto* type_parameter =
                    dyn_cast<TemplateTypeParmDecl>(parameter.get())) {
                auto cloned_parameter_type =
                    std::make_shared<TemplateTypeParmType>(
                        type_parameter->name,
                        type_parameter->depth,
                        type_parameter->index,
                        type_parameter->is_parameter_pack);
                auto cloned_parameter =
                    collect.collect_make<TemplateTypeParmDecl>(
                        type_parameter->name,
                        type_parameter->depth,
                        type_parameter->index,
                        cloned_parameter_type,
                        type_parameter->is_parameter_pack,
                        type_parameter->location);
                cloned_parameter_type->parameter_decl = cloned_parameter.get();
                parameter_rebinds.emplace(type_parameter, cloned_parameter.get());
                cloned_template_decl->parameters.push_back(
                    std::move(cloned_parameter));
                continue;
            }

            if (auto* non_type_parameter =
                    dyn_cast<TemplateNonTypeParmDecl>(parameter.get())) {
                auto rewritten_parameter_type =
                    remap_template_parameter_types_in_type(
                        alias_template_clone_pass.rewrite_type(
                            non_type_parameter->type),
                        parameter_rebinds);
                std::shared_ptr<Symbol> cloned_parameter_symbol = nullptr;
                if (non_type_parameter->sym) {
                    cloned_parameter_symbol =
                        clone_symbol_shallow_for_specialization(
                            non_type_parameter->sym,
                            remap_template_parameter_types_in_type(
                                alias_template_clone_pass.rewrite_type(
                                    non_type_parameter->sym->type),
                                parameter_rebinds));
                    alias_template_clone_pass.context().symbol_remap.emplace(
                        non_type_parameter->sym.get(),
                        cloned_parameter_symbol);
                }

                auto cloned_parameter =
                    collect.collect_make<TemplateNonTypeParmDecl>(
                        non_type_parameter->name,
                        non_type_parameter->depth,
                        non_type_parameter->index,
                        rewritten_parameter_type,
                        cloned_parameter_symbol,
                        non_type_parameter->is_parameter_pack,
                        non_type_parameter->location);
                parameter_rebinds.emplace(non_type_parameter, cloned_parameter.get());
                cloned_template_decl->parameters.push_back(
                    std::move(cloned_parameter));
                continue;
            }

            return fail_instantiation(
                "class template nested alias template instantiation for this template parameter kind is not supported yet",
                parameter->location);
        }

        auto rewritten_alias_type = remap_template_parameter_types_in_type(
            alias_template_clone_pass.rewrite_type(alias_decl->type),
            parameter_rebinds);
        std::shared_ptr<Symbol> cloned_alias_symbol = nullptr;
        if (alias_decl->sym) {
            cloned_alias_symbol = clone_symbol_shallow_for_specialization(
                alias_decl->sym,
                rewritten_alias_type);
            clone_pass.context().symbol_remap.emplace(
                alias_decl->sym.get(),
                cloned_alias_symbol);
        }
        auto* rewritten_alias_decl = cloned_template_decl->alias_decl();
        if (!rewritten_alias_decl) {
            return fail_instantiation(
                "internal error: missing cloned class template nested alias declaration",
                alias_template_decl->location);
        }
        rewritten_alias_decl->type = rewritten_alias_type;
        rewritten_alias_decl->underlying = desugar_type(rewritten_alias_type);
        rewritten_alias_decl->sym = cloned_alias_symbol;

        for (size_t index = 0;
             index < alias_template_decl->parameters.size() &&
             index < cloned_template_decl->parameters.size();
             ++index) {
            const auto* default_argument = get_template_parameter_default_argument(
                alias_template_decl->parameters[index].get());
            if (!default_argument) {
                continue;
            }

            auto rewritten_defaults = collect.substitute_template_arguments_with_bindings(
                {*default_argument},
                *selected_parameters,
                specialization_bindings,
                loc);
            if (rewritten_defaults.size() != 1) {
                return fail_instantiation(
                    "internal error: failed to rewrite class template nested alias template default argument",
                    alias_template_decl->location);
            }

            auto rewritten_default = std::move(rewritten_defaults.front());
            std::string default_error;
            if (!remap_template_argument_after_outer_substitution(
                    rewritten_default,
                    parameter_rebinds,
                    alias_template_clone_pass.context(),
                    &default_error)) {
                return fail_instantiation(
                    default_error.empty()
                        ? "class template nested alias template default argument cloning is not supported"
                        : default_error,
                    alias_template_decl->location);
            }
            set_template_parameter_default_argument(
                cloned_template_decl->parameters[index].get(),
                std::move(rewritten_default));
        }

        if (!merge_template_decl_default_arguments(
                cloned_template_decl.get(),
                nullptr)) {
            return fail_instantiation(
                "internal error: failed to register class template nested alias template defaults",
                alias_template_decl->location);
        }

        RecordSemanticState::NestedTemplate nested_template;
        nested_template.name = alias_decl->name;
        nested_template.declared_access = declared_access;
        nested_template.kind = RecordSemanticState::NestedTemplateKind::Alias;
        nested_template.decl = cloned_template_decl.get();
        nested_templates.push_back(std::move(nested_template));
        publish_provisional_nested_members();

        entry->member_decls.push_back(std::move(cloned_template_decl));
        return true;
    }

    bool handle_method_template_member(
        const FunctionTemplateDecl* method_template_decl,
        RecordMemberAccess declared_access) {
        auto* function_decl = method_template_decl->function_decl();
        if (!function_decl) {
            return fail_instantiation(
                "internal error: missing class template member template pattern",
                method_template_decl->location);
        }
        auto* method_decl = dyn_cast<CppMethodDecl>(function_decl);

        auto rewritten_type = clone_pass.rewrite_type(QualType(function_decl->type));
        auto canonical_type =
            desugar_type(rewritten_type, ast_ctx()).as_shared<FunctionType>();
        if (!canonical_type) {
            return fail_instantiation(
                "internal error: class template member template specialization did not produce a function type",
                function_decl->location);
        }

        auto cloned_method_decl = collect.collect_make<CppMethodDecl>();
        cloned_method_decl->location = function_decl->location;
        cloned_method_decl->name = function_decl->name;
        cloned_method_decl->type = canonical_type;
        cloned_method_decl->storage_class = function_decl->storage_class;
        cloned_method_decl->is_inline = function_decl->is_inline;
        cloned_method_decl->is_constexpr = function_decl->is_constexpr;
        cloned_method_decl->set_language_linkage(
            function_decl->get_language_linkage());
        cloned_method_decl->is_virtual =
            method_decl ? method_decl->is_virtual : false;
        cloned_method_decl->is_override =
            method_decl ? method_decl->is_override : false;
        cloned_method_decl->is_final =
            method_decl ? method_decl->is_final : false;
        cloned_method_decl->is_pure =
            method_decl ? method_decl->is_pure : false;
        if (function_decl->asm_label) {
            cloned_method_decl->set_asm_label(*function_decl->asm_label);
        }

        auto namespace_prefix = namespace_prefix_from_member_qualifier(
            get_func_decl_cxx_qualifier_prefix(function_decl));
        if (namespace_prefix.has_value()) {
            set_func_decl_cxx_qualifier_prefix(
                cloned_method_decl.get(),
                *namespace_prefix);
        }
        set_func_decl_owner_record_type(cloned_method_decl.get(), owner_type);
        if (method_decl) {
            copy_cpp_member_decl_info(
                ast_ctx(),
                method_decl->node_id,
                cloned_method_decl->node_id);
        }

        auto cloned_template_decl = collect.collect_make<FunctionTemplateDecl>(
            TemplateParameterList{},
            std::move(cloned_method_decl),
            method_template_decl->location);
        set_template_decl_canonical_decl(
            cloned_template_decl.get(),
            cloned_template_decl.get());
        cloned_template_decl->set_pattern_template_decl(method_template_decl);

        PendingMethodTemplateClone pending_method_template;
        pending_method_template.pattern_template = method_template_decl;
        pending_method_template.pattern_function = function_decl;
        pending_method_template.specialized_template = cloned_template_decl.get();
        pending_method_template.parameter_rebinds.reserve(
            method_template_decl->parameters.size());
        pending_method_template.symbol_remap.reserve(
            method_template_decl->parameters.size());

        for (const auto& parameter : method_template_decl->parameters) {
            if (!parameter) {
                return fail_instantiation(
                    "internal error: missing class template member template parameter",
                    method_template_decl->location);
            }

            if (auto* type_parameter =
                    dyn_cast<TemplateTypeParmDecl>(parameter.get())) {
                auto cloned_parameter_type =
                    std::make_shared<TemplateTypeParmType>(
                        type_parameter->name,
                        type_parameter->depth,
                        type_parameter->index,
                        type_parameter->is_parameter_pack);
                auto cloned_parameter =
                    collect.collect_make<TemplateTypeParmDecl>(
                        type_parameter->name,
                        type_parameter->depth,
                        type_parameter->index,
                        cloned_parameter_type,
                        type_parameter->is_parameter_pack,
                        type_parameter->location);
                cloned_parameter_type->parameter_decl = cloned_parameter.get();
                pending_method_template.parameter_rebinds.emplace(
                    type_parameter,
                    cloned_parameter.get());
                cloned_template_decl->parameters.push_back(
                    std::move(cloned_parameter));
                continue;
            }

            if (auto* non_type_parameter =
                    dyn_cast<TemplateNonTypeParmDecl>(parameter.get())) {
                auto rewritten_parameter_type =
                    remap_template_parameter_types_in_type(
                        clone_pass.rewrite_type(non_type_parameter->type),
                        pending_method_template.parameter_rebinds);
                std::shared_ptr<Symbol> cloned_parameter_symbol = nullptr;
                if (non_type_parameter->sym) {
                    cloned_parameter_symbol =
                        clone_symbol_shallow_for_specialization(
                            non_type_parameter->sym,
                            remap_template_parameter_types_in_type(
                                clone_pass.rewrite_type(
                                    non_type_parameter->sym->type),
                                pending_method_template.parameter_rebinds));
                    pending_method_template.symbol_remap.emplace(
                        non_type_parameter->sym.get(),
                        cloned_parameter_symbol);
                }

                auto cloned_parameter =
                    collect.collect_make<TemplateNonTypeParmDecl>(
                        non_type_parameter->name,
                        non_type_parameter->depth,
                        non_type_parameter->index,
                        rewritten_parameter_type,
                        cloned_parameter_symbol,
                        non_type_parameter->is_parameter_pack,
                        non_type_parameter->location);
                pending_method_template.parameter_rebinds.emplace(
                    non_type_parameter,
                    cloned_parameter.get());
                cloned_template_decl->parameters.push_back(
                    std::move(cloned_parameter));
                continue;
            }

            return fail_instantiation(
                "class template member template instantiation for this template parameter kind is not supported yet",
                parameter->location);
        }

        RecordSemanticState::MethodTemplate semantic_method_template;
        semantic_method_template.name = function_decl->name;
        semantic_method_template.declared_access = declared_access;
        semantic_method_template.is_static =
            function_decl->storage_class == StorageClass::STATIC;
        semantic_method_template.decl = cloned_template_decl.get();
        method_templates.push_back(std::move(semantic_method_template));

        pending_method_template_clones.push_back(std::move(pending_method_template));
        entry->map_owner_specialized_member_template(
            function_decl,
            cloned_template_decl.get());
        entry->member_decls.push_back(std::move(cloned_template_decl));
        return true;
    }

    bool handle_method_member(
        const CppMethodDecl* method_decl,
        RecordMemberAccess declared_access) {
        if (const auto* explicit_specialization =
                find_explicit_member_specialization(method_decl)) {
            auto* specialized_decl = dyn_cast<CppMethodDecl>(
                const_cast<Decl*>(explicit_specialization->get_specialized_decl()));
            if (!specialized_decl) {
                return fail_instantiation(
                    "internal error: explicit member specialization did not preserve a method declaration",
                    method_decl->location);
            }

            rebind_specialized_function_owner(
                specialized_decl,
                owner_type,
                ast_ctx());
            auto specialized_symbol = ensure_explicit_member_function_symbol(
                specialized_decl,
                explicit_specialization->is_definition());

            RecordSemanticState::Method semantic_method;
            semantic_method.name = specialized_decl->name;
            semantic_method.type = QualType(specialized_decl->type);
            semantic_method.declared_access = declared_access;
            semantic_method.is_static =
                specialized_decl->storage_class == StorageClass::STATIC;
            semantic_method.is_virtual = specialized_decl->is_virtual;
            semantic_method.is_override = specialized_decl->is_override;
            semantic_method.is_final = specialized_decl->is_final;
            semantic_method.is_pure = specialized_decl->is_pure;
            semantic_method.decl = specialized_decl;
            semantic_method.symbol = specialized_symbol;
            methods.push_back(std::move(semantic_method));
            if (specialized_symbol) {
                specialized_member_symbols.emplace(
                    specialized_decl,
                    specialized_symbol);
            }
            return true;
        }

        auto rewritten_type = clone_pass.rewrite_type(QualType(method_decl->type));
        auto canonical_type =
            desugar_type(rewritten_type, ast_ctx()).as_shared<FunctionType>();
        if (!canonical_type) {
            return fail_instantiation(
                "internal error: class template method specialization did not produce a function type",
                method_decl->location);
        }

        auto cloned_decl = collect.collect_make<CppMethodDecl>();
        cloned_decl->location = method_decl->location;
        cloned_decl->name = method_decl->name;
        cloned_decl->type = canonical_type;
        cloned_decl->storage_class = method_decl->storage_class;
        cloned_decl->is_inline = method_decl->is_inline;
        cloned_decl->is_constexpr = method_decl->is_constexpr;
        cloned_decl->set_language_linkage(method_decl->get_language_linkage());
        cloned_decl->is_virtual = method_decl->is_virtual;
        cloned_decl->is_override = method_decl->is_override;
        cloned_decl->is_final = method_decl->is_final;
        cloned_decl->is_pure = method_decl->is_pure;
        if (method_decl->asm_label) {
            cloned_decl->set_asm_label(*method_decl->asm_label);
        }

        auto namespace_prefix = namespace_prefix_from_member_qualifier(
            get_func_decl_cxx_qualifier_prefix(method_decl));
        if (namespace_prefix.has_value()) {
            set_func_decl_cxx_qualifier_prefix(
                cloned_decl.get(),
                *namespace_prefix);
        }
        set_func_decl_owner_record_type(cloned_decl.get(), owner_type);
        copy_cpp_member_decl_info(
            ast_ctx(),
            method_decl->node_id,
            cloned_decl->node_id);

        auto pattern_symbol_it = pattern_method_symbols.find(method_decl);
        auto cloned_symbol = clone_member_symbol(
            pattern_symbol_it != pattern_method_symbols.end()
                ? pattern_symbol_it->second
                : nullptr,
            QualType(canonical_type),
            namespace_prefix ? &*namespace_prefix : nullptr,
            true);

        RecordSemanticState::Method semantic_method;
        semantic_method.name = cloned_decl->name;
        semantic_method.type = QualType(canonical_type);
        semantic_method.declared_access = declared_access;
        semantic_method.is_static =
            cloned_decl->storage_class == StorageClass::STATIC;
        semantic_method.is_virtual = cloned_decl->is_virtual;
        semantic_method.is_override = cloned_decl->is_override;
        semantic_method.is_final = cloned_decl->is_final;
        semantic_method.is_pure = cloned_decl->is_pure;
        semantic_method.decl = cloned_decl.get();
        semantic_method.symbol = cloned_symbol;
        methods.push_back(std::move(semantic_method));
        if (cloned_symbol) {
            specialized_member_symbols.emplace(cloned_decl.get(), cloned_symbol);
            entry->map_specialized_member_symbol_to_primary_member(
                cloned_symbol.get(),
                method_decl);
        }
        entry->map_specialized_member_to_primary_member(
            cloned_decl.get(),
            method_decl);

        pending_body_clones.emplace_back(method_decl, cloned_decl.get());
        entry->member_decls.push_back(std::move(cloned_decl));
        return true;
    }

    bool handle_constructor_member(
        const CppConstructorDecl* ctor_decl,
        RecordMemberAccess declared_access) {
        auto rewritten_type = clone_pass.rewrite_type(QualType(ctor_decl->type));
        auto canonical_type =
            desugar_type(rewritten_type, ast_ctx()).as_shared<FunctionType>();
        if (!canonical_type) {
            return fail_instantiation(
                "internal error: class template constructor specialization did not produce a function type",
                ctor_decl->location);
        }

        auto cloned_decl = collect.collect_make<CppConstructorDecl>();
        cloned_decl->location = ctor_decl->location;
        cloned_decl->name = ctor_decl->name;
        cloned_decl->type = canonical_type;
        cloned_decl->storage_class = ctor_decl->storage_class;
        cloned_decl->is_inline = ctor_decl->is_inline;
        cloned_decl->is_constexpr = ctor_decl->is_constexpr;
        cloned_decl->set_language_linkage(ctor_decl->get_language_linkage());
        cloned_decl->is_explicit = ctor_decl->is_explicit;
        cloned_decl->is_deleted = ctor_decl->is_deleted;
        cloned_decl->is_defaulted = ctor_decl->is_defaulted;
        if (ctor_decl->asm_label) {
            cloned_decl->set_asm_label(*ctor_decl->asm_label);
        }

        auto namespace_prefix = namespace_prefix_from_member_qualifier(
            get_func_decl_cxx_qualifier_prefix(ctor_decl));
        if (namespace_prefix.has_value()) {
            set_func_decl_cxx_qualifier_prefix(
                cloned_decl.get(),
                *namespace_prefix);
        }
        set_func_decl_owner_record_type(cloned_decl.get(), owner_type);
        copy_cpp_member_decl_info(
            ast_ctx(),
            ctor_decl->node_id,
            cloned_decl->node_id);

        auto pattern_symbol_it = pattern_constructor_symbols.find(ctor_decl);
        auto cloned_symbol = clone_member_symbol(
            pattern_symbol_it != pattern_constructor_symbols.end()
                ? pattern_symbol_it->second
                : nullptr,
            QualType(canonical_type),
            namespace_prefix ? &*namespace_prefix : nullptr,
            true);

        RecordSemanticState::Constructor semantic_ctor;
        semantic_ctor.name = cloned_decl->name;
        semantic_ctor.type = QualType(canonical_type);
        semantic_ctor.declared_access = declared_access;
        semantic_ctor.is_implicit = false;
        semantic_ctor.is_explicit = cloned_decl->is_explicit;
        semantic_ctor.is_deleted = cloned_decl->is_deleted;
        semantic_ctor.decl = cloned_decl.get();
        semantic_ctor.symbol = cloned_symbol;
        constructors.push_back(std::move(semantic_ctor));
        if (cloned_symbol) {
            specialized_member_symbols.emplace(cloned_decl.get(), cloned_symbol);
            entry->map_specialized_member_symbol_to_primary_member(
                cloned_symbol.get(),
                ctor_decl);
        }
        entry->map_specialized_member_to_primary_member(
            cloned_decl.get(),
            ctor_decl);

        pending_body_clones.emplace_back(ctor_decl, cloned_decl.get());
        pending_ctor_init_clones.emplace_back(ctor_decl, cloned_decl.get());
        entry->member_decls.push_back(std::move(cloned_decl));
        return true;
    }

    bool handle_destructor_member(
        const CppDestructorDecl* dtor_decl,
        RecordMemberAccess declared_access) {
        auto rewritten_type = clone_pass.rewrite_type(QualType(dtor_decl->type));
        auto canonical_type =
            desugar_type(rewritten_type, ast_ctx()).as_shared<FunctionType>();
        if (!canonical_type) {
            return fail_instantiation(
                "internal error: class template destructor specialization did not produce a function type",
                dtor_decl->location);
        }

        auto cloned_decl = collect.collect_make<CppDestructorDecl>();
        cloned_decl->location = dtor_decl->location;
        cloned_decl->name = dtor_decl->name;
        cloned_decl->type = canonical_type;
        cloned_decl->storage_class = dtor_decl->storage_class;
        cloned_decl->is_inline = dtor_decl->is_inline;
        cloned_decl->is_constexpr = dtor_decl->is_constexpr;
        cloned_decl->set_language_linkage(dtor_decl->get_language_linkage());
        cloned_decl->is_deleted = dtor_decl->is_deleted;
        cloned_decl->is_defaulted = dtor_decl->is_defaulted;
        cloned_decl->is_virtual = dtor_decl->is_virtual;
        cloned_decl->is_override = dtor_decl->is_override;
        cloned_decl->is_final = dtor_decl->is_final;
        cloned_decl->is_pure = dtor_decl->is_pure;
        if (dtor_decl->asm_label) {
            cloned_decl->set_asm_label(*dtor_decl->asm_label);
        }

        auto namespace_prefix = namespace_prefix_from_member_qualifier(
            get_func_decl_cxx_qualifier_prefix(dtor_decl));
        if (namespace_prefix.has_value()) {
            set_func_decl_cxx_qualifier_prefix(
                cloned_decl.get(),
                *namespace_prefix);
        }
        set_func_decl_owner_record_type(cloned_decl.get(), owner_type);
        copy_cpp_member_decl_info(
            ast_ctx(),
            dtor_decl->node_id,
            cloned_decl->node_id);

        auto pattern_symbol_it = pattern_destructor_symbols.find(dtor_decl);
        auto cloned_symbol = clone_member_symbol(
            pattern_symbol_it != pattern_destructor_symbols.end()
                ? pattern_symbol_it->second
                : nullptr,
            QualType(canonical_type),
            namespace_prefix ? &*namespace_prefix : nullptr,
            true);

        RecordSemanticState::Destructor semantic_dtor;
        semantic_dtor.name = cloned_decl->name;
        semantic_dtor.type = QualType(canonical_type);
        semantic_dtor.declared_access = declared_access;
        semantic_dtor.is_deleted = cloned_decl->is_deleted;
        semantic_dtor.is_virtual = cloned_decl->is_virtual;
        semantic_dtor.is_override = cloned_decl->is_override;
        semantic_dtor.is_final = cloned_decl->is_final;
        semantic_dtor.is_pure = cloned_decl->is_pure;
        semantic_dtor.decl = cloned_decl.get();
        semantic_dtor.symbol = cloned_symbol;
        destructors.push_back(std::move(semantic_dtor));
        if (cloned_symbol) {
            specialized_member_symbols.emplace(cloned_decl.get(), cloned_symbol);
            entry->map_specialized_member_symbol_to_primary_member(
                cloned_symbol.get(),
                dtor_decl);
        }
        entry->map_specialized_member_to_primary_member(
            cloned_decl.get(),
            dtor_decl);

        pending_body_clones.emplace_back(dtor_decl, cloned_decl.get());
        entry->member_decls.push_back(std::move(cloned_decl));
        return true;
    }

    void assign_virtual_slots(
        RecordSemanticState& state,
        std::vector<RecordSemanticState::Method>& state_methods,
        std::vector<RecordSemanticState::Destructor>& state_destructors) const {
        state.virtual_slots.clear();
        state.is_polymorphic = false;
        state.has_virtual_destructor = false;
        state.is_abstract = false;

        size_t next_virtual_slot = 0;
        for (auto& method : state_methods) {
            if (!method.is_virtual || method.is_static) {
                method.virtual_slot_index = -1;
                continue;
            }
            state.is_polymorphic = true;
            method.virtual_slot_index = static_cast<int32_t>(next_virtual_slot++);
            RecordSemanticState::VirtualSlot slot;
            slot.key = make_method_virtual_slot_key(method.name, method.type);
            slot.name = method.name;
            slot.is_pure = method.is_pure;
            slot.is_final = method.is_final;
            slot.final_symbol = method.symbol;
            state.virtual_slots.push_back(std::move(slot));
        }
        for (auto& dtor : state_destructors) {
            if (!dtor.is_virtual) {
                dtor.virtual_slot_index = -1;
                continue;
            }
            state.is_polymorphic = true;
            state.has_virtual_destructor = true;
            dtor.virtual_slot_index = static_cast<int32_t>(next_virtual_slot++);
            RecordSemanticState::VirtualSlot slot;
            slot.key = "<destructor>";
            slot.name = dtor.name;
            slot.is_destructor = true;
            slot.is_pure = dtor.is_pure;
            slot.is_final = dtor.is_final;
            slot.final_symbol = dtor.symbol;
            state.virtual_slots.push_back(std::move(slot));
        }
        for (const auto& slot : state.virtual_slots) {
            if (slot.is_pure) {
                state.is_abstract = true;
                break;
            }
        }
    }

    void build_semantic_state() {
        RecordSemanticState layout_state;
        layout_state.is_incomplete = !pattern->is_definition;
        if (pattern->get_definition_data()) {
            layout_state.definition_data = *pattern->get_definition_data();
        }
        assign_virtual_slots(layout_state, methods, destructors);

        std::vector<ObjectType::Field> layout_fields;
        layout_fields.reserve(
            user_fields.size() +
            (layout_state.is_polymorphic && !is_union ? 1 : 0));
        if (layout_state.is_polymorphic && !is_union) {
            auto void_type =
                ast_ctx() && ast_ctx()->type_ctx
                    ? ast_ctx()->type_ctx->get_builtin(BuiltinTypes::Void)
                    : nullptr;
            if (void_type) {
                QualType vptr_type(
                    std::make_shared<PointerType>(QualType(void_type)));
                layout_fields.emplace_back(
                    "",
                    vptr_type,
                    0,
                    RecordMemberAccess::Private);
            }
        }
        for (const auto& field : user_fields) {
            layout_fields.push_back(field);
        }

        semantic_state = compute_record_semantics(
            std::move(layout_fields),
            is_union,
            false,
            0,
            0,
            !pattern->is_definition,
            ast_ctx()->abi_policy.get());
        semantic_state.is_incomplete = !pattern->is_definition;
        semantic_state.non_virtual_size_bits = semantic_state.size_bits;
        semantic_state.non_virtual_alignment = semantic_state.alignment;
        if (pattern->get_definition_data()) {
            semantic_state.definition_data = *pattern->get_definition_data();
        }
        semantic_state.methods = std::move(methods);
        semantic_state.method_templates = std::move(method_templates);
        semantic_state.constructors = std::move(constructors);
        semantic_state.destructors = std::move(destructors);
        semantic_state.static_data_members = std::move(static_data_members);
        semantic_state.nested_types = std::move(nested_types);
        semantic_state.nested_templates = std::move(nested_templates);
        assign_virtual_slots(
            semantic_state,
            semantic_state.methods,
            semantic_state.destructors);
    }

    bool resolve_static_data_members() {
        auto static_member_resolution_pass =
            clone_pass_builder.build_dependent_resolution_pass(
                clone_pass,
                [this](std::unique_ptr<Expr>& expr, std::string* error_out)
                    -> bool {
                    return collect.resolve_dependent_expr_after_substitution(
                        expr,
                        QualType(),
                        error_out);
                });
        for (auto& member_decl : entry->member_decls) {
            if (!isa<VariableDecl>(member_decl.get())) {
                continue;
            }
            std::string clone_error;
            if (!static_member_resolution_pass.resolve_decl_in_place(
                    member_decl,
                    &clone_error) ||
                !template_sema_internal::finalize_specialized_decl_semantics(
                    collect,
                    member_decl,
                    &clone_error)) {
                return fail_instantiation(
                    clone_error.empty()
                        ? "class template static data member dependent resolution is not supported"
                        : clone_error,
                    member_decl ? member_decl->location : loc);
            }
        }
        return true;
    }

    bool clone_pending_member_templates() {
        auto register_specialized_member_symbol =
            [this](const std::shared_ptr<Symbol>& sym) {
                collect.collect_add_global_symbol(sym);
            };
        auto rewrite_specialized_record_member_expr =
            [this](MemberExpr* member_expr, std::string* error_out) -> bool {
                return rebind_member_expr_for_specialized_record(
                    member_expr,
                    ast_ctx(),
                    error_out);
            };

        for (const auto& pending_method_template : pending_method_template_clones) {
            auto* pattern_template = pending_method_template.pattern_template;
            auto* pattern_method = pending_method_template.pattern_function;
            auto* specialized_template =
                pending_method_template.specialized_template;
            auto* specialized_method =
                specialized_template
                    ? dyn_cast<CppMethodDecl>(specialized_template->function_decl())
                    : nullptr;
            if (!pattern_template || !specialized_template || !pattern_method ||
                !specialized_method) {
                return fail_instantiation(
                    "internal error: missing class template member template clone state",
                    loc);
            }

            auto member_template_builder =
                make_nested_template_clone_pass_builder(
                    clone_pass_builder,
                    clone_pass,
                    [this](const std::vector<TemplateArgument>& template_arguments)
                        -> std::vector<TemplateArgument> {
                        return rewrite_class_template_arguments(
                            template_arguments,
                            specialization_bindings);
                    },
                    pending_method_template.parameter_rebinds,
                    pending_method_template.symbol_remap);
            TemplateSubstitutionPass* member_template_clone_pass_ptr = nullptr;
            auto clone_preserved_member_template_pack_pattern =
                [&](TemplateClonePassBuilder preserve_builder,
                    const TemplateSubstitutionPass* remap_pass,
                    const Expr* pack_pattern,
                    std::string* error_out) -> std::unique_ptr<Expr> {
                    if (remap_pass) {
                        preserve_builder.symbol_remap =
                            remap_pass->context().symbol_remap;
                        preserve_builder.scope_remap =
                            remap_pass->context().scope_remap;
                    }
                    preserve_builder.expand_pack_expansion = nullptr;

                    std::string clone_error;
                    auto preserve_pass =
                        preserve_builder.build_substitution_pass();
                    auto cloned_pattern =
                        preserve_pass.clone_expr(pack_pattern, &clone_error);
                    if (!cloned_pattern) {
                        if (error_out && error_out->empty()) {
                            *error_out =
                                clone_error.empty()
                                    ? "class template member template pack expansion pattern cloning is not supported"
                                    : clone_error;
                        }
                        return nullptr;
                    }

                    return collect.collect_make<PackExpansionExpr>(
                        std::move(cloned_pattern),
                        pack_pattern ? pack_pattern->location : SrcLoc());
                };
            member_template_builder.expand_pack_expansion =
                [&](const Expr* pattern_expr,
                    std::vector<std::unique_ptr<Expr>>& expanded_out,
                    std::string* error_out) -> bool {
                    template_sema_internal::TemplatePackExpansionShape outer_shape;
                    if (!collect_pack_expansion_shape_in_expr(
                            pattern_expr,
                            *selected_parameters,
                            outer_shape) ||
                        outer_shape.has_unsupported_dependency ||
                        outer_shape.referenced_parameters.empty()) {
                        auto preserved_pack =
                            clone_preserved_member_template_pack_pattern(
                                member_template_builder,
                                member_template_clone_pass_ptr,
                                pattern_expr,
                                error_out);
                        if (!preserved_pack) {
                            return false;
                        }
                        expanded_out.clear();
                        expanded_out.push_back(std::move(preserved_pack));
                        return true;
                    }

                    std::string arity_error;
                    auto expansion_arity = find_pack_expansion_arity_for_bindings(
                        outer_shape,
                        *selected_parameters,
                        specialization_bindings,
                        &arity_error);
                    if (!expansion_arity.has_value()) {
                        if (error_out && error_out->empty()) {
                            *error_out =
                                arity_error.empty()
                                    ? "failed to determine class template member template pack expansion arity"
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
                        if (!build_pack_element_bindings(
                                element_index,
                                element_bindings,
                                &element_binding_error)) {
                            if (error_out && error_out->empty()) {
                                *error_out =
                                    element_binding_error.empty()
                                        ? "failed to materialize class template member template pack expansion bindings"
                                        : element_binding_error;
                            }
                            return false;
                        }

                        auto outer_element_builder =
                            make_template_binding_clone_pass_builder(
                                ast_ctx(),
                                *selected_parameters,
                                element_bindings,
                                loc,
                                "class template non-type parameter requires a concrete integral value",
                                [this, &element_bindings](QualType type) -> QualType {
                                    return rewrite_class_template_type(
                                        type,
                                        element_bindings);
                                },
                                [this, &element_bindings](
                                    const std::vector<TemplateArgument>&
                                        template_arguments)
                                    -> std::vector<TemplateArgument> {
                                    return rewrite_class_template_arguments(
                                        template_arguments,
                                        element_bindings);
                                },
                                register_specialized_member_symbol,
                                rewrite_specialized_record_member_expr);
                        outer_element_builder.rewrite_symbol =
                            clone_pass_builder.rewrite_symbol;
                        if (member_template_clone_pass_ptr) {
                            outer_element_builder.symbol_remap =
                                member_template_clone_pass_ptr->context()
                                    .symbol_remap;
                            outer_element_builder.scope_remap =
                                member_template_clone_pass_ptr->context()
                                    .scope_remap;
                        } else if (clone_pass_ptr) {
                            outer_element_builder.symbol_remap =
                                clone_pass_ptr->context().symbol_remap;
                            outer_element_builder.scope_remap =
                                clone_pass_ptr->context().scope_remap;
                        }

                        auto nested_element_builder =
                            make_nested_template_clone_pass_builder(
                                outer_element_builder,
                                member_template_clone_pass_ptr
                                    ? *member_template_clone_pass_ptr
                                    : clone_pass,
                                [this, &element_bindings](
                                    const std::vector<TemplateArgument>&
                                        template_arguments)
                                    -> std::vector<TemplateArgument> {
                                    return rewrite_class_template_arguments(
                                        template_arguments,
                                        element_bindings);
                                },
                                pending_method_template.parameter_rebinds,
                                pending_method_template.symbol_remap);
                        auto preserved_pack =
                            clone_preserved_member_template_pack_pattern(
                                nested_element_builder,
                                nullptr,
                                pattern_expr,
                                error_out);
                        if (!preserved_pack) {
                            return false;
                        }
                        expanded_out.push_back(std::move(preserved_pack));
                    }
                    return true;
                };
            auto member_template_clone_pass =
                member_template_builder.build_substitution_pass();
            member_template_clone_pass_ptr = &member_template_clone_pass;
            auto rewritten_member_template_type =
                remap_template_parameter_types_in_type(
                    member_template_clone_pass.rewrite_type(
                        QualType(pattern_method->type)),
                    pending_method_template.parameter_rebinds);
            auto canonical_member_template_type =
                desugar_type(rewritten_member_template_type, ast_ctx())
                    .as_shared<FunctionType>();
            if (!canonical_member_template_type) {
                return fail_instantiation(
                    "internal error: class template member template specialization did not produce a function type",
                    pattern_method->location);
            }
            specialized_method->type = canonical_member_template_type;

            for (size_t index = 0;
                 index < pattern_template->parameters.size() &&
                 index < specialized_template->parameters.size();
                 ++index) {
                const auto* default_argument =
                    get_template_parameter_default_argument(
                        pattern_template->parameters[index].get());
                if (!default_argument) {
                    continue;
                }

                auto rewritten_defaults =
                    collect.substitute_template_arguments_with_bindings(
                        {*default_argument},
                        *selected_parameters,
                        specialization_bindings,
                        loc);
                if (rewritten_defaults.size() != 1) {
                    return fail_instantiation(
                        "internal error: failed to rewrite class template member template default argument",
                        pattern_template->location);
                }

                auto rewritten_default = std::move(rewritten_defaults.front());
                std::string default_error;
                if (!remap_template_argument_after_outer_substitution(
                        rewritten_default,
                        pending_method_template.parameter_rebinds,
                        member_template_clone_pass.context(),
                        &default_error)) {
                    return fail_instantiation(
                        default_error.empty()
                            ? "class template member template default argument cloning is not supported"
                            : default_error,
                        pattern_template->location);
                }
                set_template_parameter_default_argument(
                    specialized_template->parameters[index].get(),
                    std::move(rewritten_default));
            }
            if (!merge_template_decl_default_arguments(
                    specialized_template,
                    nullptr)) {
                return fail_instantiation(
                    "internal error: failed to register class template member template defaults",
                    pattern_template->location);
            }

            specialized_method->parameters.clear();
            QualType member_template_this_type =
                template_sema_internal::implicit_this_type_for_specialized_function(
                    specialized_method);
            auto member_template_resolution_pass =
                member_template_builder.build_dependent_resolution_pass(
                    member_template_clone_pass,
                    [&](std::unique_ptr<Expr>& expr,
                        std::string* error_out) -> bool {
                        return collect.resolve_dependent_expr_after_substitution(
                            expr,
                            member_template_this_type,
                            error_out);
                    });
            std::vector<const Expr*> default_arguments;
            std::string clone_error;
            if (!clone_function_parameters_for_specialization(
                    collect,
                    pattern_method,
                    *selected_parameters,
                    specialization_bindings,
                    specialized_method,
                    member_template_clone_pass,
                    member_template_resolution_pass,
                    loc,
                    "class template member template",
                    [this](QualType type,
                           size_t element_index,
                           std::string* error_out) -> QualType {
                        return rewrite_class_pack_element_type(
                            type,
                            element_index,
                            error_out);
                    },
                    nullptr,
                    default_arguments,
                    &clone_error)) {
                return fail_instantiation(
                    clone_error.empty()
                        ? "internal error: class template member template parameter clone failed"
                        : clone_error,
                    pattern_method->location);
            }
            member_template_resolution_pass.sync_from_substitution_pass(
                member_template_clone_pass);
            if (!clone_function_body_for_specialization(
                    collect,
                    pattern_method,
                    specialized_method,
                    member_template_clone_pass,
                    member_template_resolution_pass,
                    "class template member template",
                    false,
                    &clone_error)) {
                return fail_instantiation(
                    clone_error.empty()
                        ? "class template member template body cloning is not supported"
                        : clone_error,
                    pattern_method->body ? pattern_method->body->location
                                         : pattern_method->location);
            }
        }
        return true;
    }

    bool clone_pending_member_bodies() {
        for (const auto& [pattern_func, specialized_func] : pending_body_clones) {
            QualType specialized_this_type =
                template_sema_internal::implicit_this_type_for_specialized_function(
                    specialized_func);
            auto member_resolution_pass =
                clone_pass_builder.build_dependent_resolution_pass(
                    clone_pass,
                    [&](std::unique_ptr<Expr>& expr,
                        std::string* error_out) -> bool {
                        return collect.resolve_dependent_expr_after_substitution(
                            expr,
                            specialized_this_type,
                            error_out);
                    });
            std::vector<const Expr*> default_arguments;
            std::string clone_error;
            if (!clone_function_parameters_for_specialization(
                    collect,
                    pattern_func,
                    *selected_parameters,
                    specialization_bindings,
                    specialized_func,
                    clone_pass,
                    member_resolution_pass,
                    loc,
                    "class template member",
                    [this](QualType type,
                           size_t element_index,
                           std::string* error_out) -> QualType {
                        return rewrite_class_pack_element_type(
                            type,
                            element_index,
                            error_out);
                    },
                    nullptr,
                    default_arguments,
                    &clone_error)) {
                return fail_instantiation(
                    clone_error,
                    pattern_func ? pattern_func->location : loc);
            }
            member_resolution_pass.sync_from_substitution_pass(clone_pass);

            auto pattern_ctor = dyn_cast<CppConstructorDecl>(pattern_func);
            auto specialized_ctor = dyn_cast<CppConstructorDecl>(specialized_func);
            if (pattern_ctor && specialized_ctor) {
                if (!clone_ctor_initializers_for_specialization(
                        pattern_ctor,
                        specialized_ctor,
                        clone_pass,
                        member_resolution_pass,
                        &clone_error)) {
                    return fail_instantiation(clone_error, pattern_ctor->location);
                }
                if (!finalize_specialized_ctor_initializers(
                        collect,
                        specialized_ctor,
                        &clone_error)) {
                    return fail_instantiation(clone_error, pattern_ctor->location);
                }
            }

            if (!clone_function_body_for_specialization(
                    collect,
                    pattern_func,
                    specialized_func,
                    clone_pass,
                    member_resolution_pass,
                    "class template member",
                    true,
                    &clone_error)) {
                return fail_instantiation(
                    clone_error,
                    pattern_func ? pattern_func->location : loc);
            }

            std::shared_ptr<Symbol> specialized_symbol = nullptr;
            auto specialized_symbol_it =
                specialized_member_symbols.find(specialized_func);
            if (specialized_symbol_it != specialized_member_symbols.end()) {
                specialized_symbol = specialized_symbol_it->second;
            }
            if (auto* method_decl = dyn_cast<CppMethodDecl>(specialized_func)) {
                for (auto& method : semantic_state.methods) {
                    if (method.decl == method_decl) {
                        method.type = QualType(specialized_func->type);
                        if (!specialized_symbol) {
                            specialized_symbol = method.symbol;
                        }
                        break;
                    }
                }
            } else if (auto* ctor_decl =
                           dyn_cast<CppConstructorDecl>(specialized_func)) {
                for (auto& ctor : semantic_state.constructors) {
                    if (ctor.decl == ctor_decl) {
                        ctor.type = QualType(specialized_func->type);
                        if (!specialized_symbol) {
                            specialized_symbol = ctor.symbol;
                        }
                        break;
                    }
                }
            } else if (auto* dtor_decl =
                           dyn_cast<CppDestructorDecl>(specialized_func)) {
                for (auto& dtor : semantic_state.destructors) {
                    if (dtor.decl == dtor_decl) {
                        dtor.type = QualType(specialized_func->type);
                        if (!specialized_symbol) {
                            specialized_symbol = dtor.symbol;
                        }
                        break;
                    }
                }
            }
            if (specialized_symbol) {
                specialized_symbol->type = QualType(specialized_func->type);
                merge_symbol_cpp_default_arguments(
                    specialized_symbol.get(),
                    default_arguments,
                    nullptr);
                specialized_symbol->is_defined = specialized_func->body != nullptr;
                specialized_symbol->function_definition = specialized_func;
            }
        }
        return true;
    }
};

ObjectDecl* Collect::instantiate_class_template_specialization(
    const ClassTemplateDecl* class_template,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc) const {
    return ClassTemplateSpecializationInstantiator{
        *this,
        class_template,
        arguments,
        loc}
        .run();
}

ObjectDecl* Collect::collect_instantiate_class_template_specialization(
    const ClassTemplateDecl* class_template,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc) const {
    return instantiate_class_template_specialization(
        class_template,
        arguments,
        loc);
}
