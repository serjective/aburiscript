#include "collect.h"
#include "collect_templates_internal.h"

using template_sema_internal::clone_symbol_shallow_for_specialization;
using template_sema_internal::deduce_variable_template_partial_specialization_bindings;
using template_sema_internal::append_template_argument_cache_key;
using template_sema_internal::is_variable_template_partial_specialization_more_specialized;
using template_sema_internal::make_template_binding_clone_pass_builder;
using template_sema_internal::normalize_concrete_template_value_argument;
using template_sema_internal::template_argument_has_known_payload;
using template_sema_internal::template_arguments_depend_on_template_parameters;

namespace {

VariableLinkage variable_linkage_for_specialization(const VariableDecl* pattern) {
    if (!pattern) {
        return VariableLinkage::EXTERNAL;
    }
    if (pattern->storage_class == StorageClass::STATIC) {
        return VariableLinkage::INTERNAL;
    }
    return VariableLinkage::EXTERNAL;
}

} // namespace

struct Collect::VariableTemplateSpecializationInstantiator {
    Collect& collect;
    const VariableTemplateDecl* variable_template = nullptr;
    const std::vector<TemplateArgument>& arguments;
    SrcLoc loc;
    std::shared_ptr<Symbol>* specialization_symbol_out = nullptr;

    const VariableDecl* pattern = nullptr;
    const VariableDecl* selected_pattern = nullptr;
    const TemplateParameterList* selected_parameters = nullptr;
    TemplateArgumentBindings specialization_bindings;
    std::vector<TemplateArgument> normalized_arguments;
    bool specialization_is_dependent = false;
    VariableTemplateSpecializationEntry* entry = nullptr;

    VariableTemplateSpecializationInstantiator(
        Collect& collect,
        const VariableTemplateDecl* variable_template,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc,
        std::shared_ptr<Symbol>* specialization_symbol_out)
        : collect(collect),
          variable_template(variable_template),
          arguments(arguments),
          loc(loc),
          specialization_symbol_out(specialization_symbol_out) {}

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

    VariableDecl* run() {
        if (specialization_symbol_out) {
            *specialization_symbol_out = nullptr;
        }
        if (!variable_template || !ast_ctx()) {
            return nullptr;
        }

        pattern = variable_template->variable_decl();
        selected_pattern = pattern;
        selected_parameters = &variable_template->parameters;
        if (!pattern || !selected_parameters) {
            fail("internal error: missing variable template pattern", loc);
            return nullptr;
        }

        if (!bind_and_normalize_arguments()) {
            return nullptr;
        }
        if (auto* explicit_decl = try_explicit_specialization()) {
            return explicit_decl;
        }
        if (!select_partial_specialization()) {
            return nullptr;
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
            template_arguments_depend_on_template_parameters(normalized_arguments);
        if (entry->is_instantiated || entry->is_instantiating ||
            specialization_is_dependent ||
            !variable_template->is_pattern_complete) {
            return entry->specialization_decl.get();
        }
        return instantiate_entry_definition();
    }

    bool bind_and_normalize_arguments() {
        std::string binding_error;
        if (!collect.bind_template_arguments_for_specialization(
                variable_template,
                arguments,
                specialization_bindings,
                loc,
                &binding_error)) {
            return fail(
                "variable template '" + pattern->name +
                    "' template arguments do not match the parameter list" +
                    (binding_error.empty() ? std::string()
                                           : ": " + binding_error),
                loc);
        }

        for (const auto& argument : arguments) {
            if (!template_argument_has_known_payload(argument)) {
                return fail("variable template argument has unknown type", loc);
            }
        }
        if (!normalize_non_type_arguments(
                variable_template->parameters,
                specialization_bindings,
                "variable template")) {
            return false;
        }

        normalized_arguments =
            flatten_template_argument_bindings(specialization_bindings);
        specialization_is_dependent =
            template_arguments_depend_on_template_parameters(normalized_arguments);
        if (!specialization_is_dependent &&
            !collect.are_template_constraints_satisfied_with_bindings(
                variable_template,
                specialization_bindings,
                loc)) {
            return fail(
                "constraints not satisfied for variable template '" +
                    pattern->name + "'",
                loc);
        }
        return true;
    }

    bool normalize_non_type_arguments(
        const TemplateParameterList& parameters,
        TemplateArgumentBindings& bindings,
        std::string_view context_name) {
        for (size_t idx = 0; idx < parameters.size(); ++idx) {
            auto* non_type_parameter =
                dyn_cast<TemplateNonTypeParmDecl>(parameters[idx].get());
            if (!non_type_parameter || idx >= bindings.size()) {
                continue;
            }
            if (bindings[idx].arguments.empty()) {
                continue;
            }

            QualType expected_type =
                collect.substitute_template_type_with_bindings(
                    non_type_parameter->type,
                    parameters,
                    bindings,
                    loc);
            expected_type =
                collect.finalize_deferred_semantic_type(expected_type, loc);
            for (auto& bound_argument : bindings[idx].arguments) {
                std::string normalize_error;
                if (!normalize_concrete_template_value_argument(
                        bound_argument,
                        expected_type,
                        &normalize_error)) {
                    return fail(
                        normalize_error.empty()
                            ? "failed to normalize " +
                                  std::string(context_name) +
                                  " value argument"
                            : normalize_error,
                        loc);
                }
            }
        }
        return true;
    }

    const TemplateExplicitSpecializationDecl* lookup_explicit_specialization()
        const {
        const auto* lookup_pattern =
            dyn_cast<VariableTemplateDecl>(
                const_cast<TemplateDecl*>(
                    variable_template->get_pattern_template_decl()));
        if (!lookup_pattern) {
            lookup_pattern = variable_template;
        }
        const auto* canonical_template =
            dyn_cast<VariableTemplateDecl>(
                const_cast<TemplateDecl*>(
                    get_template_decl_canonical_decl(lookup_pattern)));
        if (!canonical_template) {
            canonical_template = lookup_pattern;
        }

        if (const auto* exact =
                canonical_template->find_explicit_specialization(
                    normalized_arguments)) {
            return exact;
        }

        for (const auto* explicit_specialization :
             canonical_template->explicit_specializations()) {
            auto* explicit_variable = explicit_specialization
                ? dyn_cast<VariableDecl>(
                      const_cast<Decl*>(
                          explicit_specialization->get_specialized_decl()))
                : nullptr;
            if (!explicit_variable) {
                continue;
            }

            TemplateArgumentBindings explicit_bindings;
            std::string binding_error;
            if (!collect.bind_template_arguments_for_specialization(
                    canonical_template,
                    explicit_specialization->specialization_arguments,
                    explicit_bindings,
                    explicit_specialization->location,
                    &binding_error)) {
                continue;
            }

            auto normalized_explicit_arguments =
                flatten_template_argument_bindings(explicit_bindings);
            if (normalized_explicit_arguments.size() !=
                normalized_arguments.size()) {
                continue;
            }

            bool matches = true;
            for (size_t idx = 0; idx < normalized_arguments.size(); ++idx) {
                if (!normalized_explicit_arguments[idx].equals(
                        normalized_arguments[idx])) {
                    matches = false;
                    break;
                }
            }
            if (matches) {
                return explicit_specialization;
            }
        }
        return nullptr;
    }

    void copy_variable_symbol_metadata(
        const VariableDecl* source_decl,
        Symbol* symbol) const {
        if (!source_decl || !symbol) {
            return;
        }
        symbol->is_constexpr = source_decl->is_constexpr;
        symbol->is_block_byref = source_decl->is_block_byref;
        symbol->set_language_linkage(source_decl->get_language_linkage());
        if (source_decl->asm_label) {
            symbol->asm_label = *source_decl->asm_label;
        }
        if (source_decl->sym) {
            if (const auto* qualifier_prefix =
                    get_symbol_cxx_qualifier_prefix(source_decl->sym.get())) {
                set_symbol_cxx_qualifier_prefix(
                    symbol,
                    std::string(*qualifier_prefix));
            }
            if (QualType owner_type =
                    get_symbol_owner_record_type(source_decl->sym.get())) {
                set_symbol_owner_record_type(symbol, owner_type);
            }
        }
    }

    void apply_specialization_metadata(
        VariableDecl* specialization_decl,
        Symbol* specialization_symbol) const {
        if (specialization_decl) {
            set_variable_decl_variable_template_specialization(
                specialization_decl,
                VariableTemplateSpecializationInfo{
                    variable_template,
                    normalized_arguments});
        }
        if (specialization_symbol) {
            set_symbol_variable_template_specialization(
                specialization_symbol,
                VariableTemplateSpecializationInfo{
                    variable_template,
                    normalized_arguments});
        }
    }

    void ensure_explicit_specialization_uid(Symbol* specialization_symbol) const {
        if (!specialization_symbol || !specialization_symbol->uid.empty()) {
            return;
        }

        const auto* canonical_template =
            dyn_cast<VariableTemplateDecl>(
                const_cast<TemplateDecl*>(
                    get_template_decl_canonical_decl(variable_template)));
        if (!canonical_template) {
            canonical_template = variable_template;
        }

        std::string uid = pattern && !pattern->name.empty()
            ? pattern->name
            : std::string("variable-template");
        uid += ".explicit-specialization.";
        uid += std::to_string(reinterpret_cast<uintptr_t>(canonical_template));
        uid += ".";
        for (const auto& argument : normalized_arguments) {
            append_template_argument_cache_key(uid, argument);
        }
        specialization_symbol->uid = std::move(uid);
    }

    std::shared_ptr<Symbol> synthesize_explicit_specialization_symbol(
        VariableDecl* explicit_decl) const {
        if (!explicit_decl) {
            return nullptr;
        }
        if (explicit_decl->sym) {
            apply_specialization_metadata(explicit_decl, explicit_decl->sym.get());
            ensure_explicit_specialization_uid(explicit_decl->sym.get());
            return explicit_decl->sym;
        }

        auto synthesized_symbol = pattern && pattern->sym
            ? clone_symbol_shallow_for_specialization(
                  pattern->sym,
                  desugar_type(explicit_decl->type, ast_ctx()))
            : std::make_shared<Symbol>(
                  explicit_decl->name,
                  SymbolKind::VARIABLE,
                  desugar_type(explicit_decl->type, ast_ctx()),
                  explicit_decl->storage_class,
                  variable_linkage_for_specialization(explicit_decl),
                  explicit_decl->is_inline != 0);
        if (!synthesized_symbol) {
            return nullptr;
        }
        synthesized_symbol->storage_class = explicit_decl->storage_class;
        synthesized_symbol->linkage =
            variable_linkage_for_specialization(explicit_decl);
        synthesized_symbol->is_inline = explicit_decl->is_inline;
        synthesized_symbol->is_defined =
            explicit_decl->init != nullptr ||
            explicit_decl->storage_class != StorageClass::EXTERN;
        synthesized_symbol->is_constexpr = explicit_decl->is_constexpr;
        synthesized_symbol->is_block_byref = explicit_decl->is_block_byref;
        synthesized_symbol->type = desugar_type(explicit_decl->type, ast_ctx());
        synthesized_symbol->variable_definition = explicit_decl;
        if (pattern) {
            copy_variable_symbol_metadata(pattern, synthesized_symbol.get());
        }
        copy_variable_symbol_metadata(explicit_decl, synthesized_symbol.get());
        apply_specialization_metadata(explicit_decl, synthesized_symbol.get());
        ensure_explicit_specialization_uid(synthesized_symbol.get());
        explicit_decl->sym = synthesized_symbol;
        return synthesized_symbol;
    }

    VariableDecl* try_explicit_specialization() {
        const auto* explicit_specialization = lookup_explicit_specialization();
        if (!explicit_specialization) {
            return nullptr;
        }

        auto* explicit_decl = dyn_cast<VariableDecl>(
            const_cast<Decl*>(explicit_specialization->get_specialized_decl()));
        if (!explicit_decl) {
            fail(
                "internal error: explicit variable specialization did not preserve a variable declaration",
                loc);
            return nullptr;
        }

        if (specialization_symbol_out) {
            *specialization_symbol_out =
                synthesize_explicit_specialization_symbol(explicit_decl);
        } else {
            apply_specialization_metadata(
                explicit_decl,
                explicit_decl->sym.get());
        }
        return explicit_decl;
    }

    bool select_partial_specialization() {
        if (specialization_is_dependent ||
            variable_template->partial_specializations().empty()) {
            selected_pattern = pattern;
            selected_parameters = &variable_template->parameters;
            return true;
        }

        struct PartialMatch {
            const VariableTemplatePartialSpecializationDecl* partial = nullptr;
            TemplateArgumentBindings bindings;
        };

        std::vector<PartialMatch> matches;
        matches.reserve(variable_template->partial_specializations().size());
        for (const auto* partial : variable_template->partial_specializations()) {
            if (!partial) {
                continue;
            }
            TemplateArgumentBindings partial_bindings;
            if (!deduce_variable_template_partial_specialization_bindings(
                    collect,
                    partial,
                    normalized_arguments,
                    partial_bindings)) {
                continue;
            }
            std::string binding_error;
            if (!collect.complete_template_argument_bindings_with_substituted_defaults(
                    partial,
                    partial_bindings,
                    loc,
                    &binding_error)) {
                return fail(
                    binding_error.empty()
                        ? "variable template partial specialization arguments do not satisfy parameter defaults"
                        : binding_error,
                    loc);
            }
            if (!normalize_non_type_arguments(
                    partial->parameters,
                    partial_bindings,
                    "variable template partial specialization")) {
                return false;
            }
            if (!collect.are_template_constraints_satisfied_with_bindings(
                    partial,
                    partial_bindings,
                    loc)) {
                continue;
            }
            matches.push_back(PartialMatch{partial, std::move(partial_bindings)});
        }

        if (matches.empty()) {
            selected_pattern = pattern;
            selected_parameters = &variable_template->parameters;
            return true;
        }

        size_t selected_index = 0;
        bool ambiguous = false;
        for (size_t idx = 0; idx < matches.size(); ++idx) {
            bool more_specialized_than_selected =
                is_variable_template_partial_specialization_more_specialized(
                    collect,
                    matches[idx].partial,
                    matches[selected_index].partial);
            bool selected_more_specialized =
                is_variable_template_partial_specialization_more_specialized(
                    collect,
                    matches[selected_index].partial,
                    matches[idx].partial);
            if (more_specialized_than_selected && !selected_more_specialized) {
                selected_index = idx;
                ambiguous = false;
                continue;
            }
            if (idx != selected_index &&
                !more_specialized_than_selected &&
                !selected_more_specialized) {
                ambiguous = true;
            }
        }

        if (ambiguous) {
            return fail(
                "variable template partial specialization for '" +
                    pattern->name + "' is ambiguous",
                loc);
        }

        specialization_bindings = std::move(matches[selected_index].bindings);
        selected_pattern = matches[selected_index].partial->variable_decl();
        selected_parameters = &matches[selected_index].partial->parameters;
        if (!selected_pattern || !selected_parameters) {
            return fail(
                "internal error: selected variable template partial specialization is incomplete",
                loc);
        }
        return true;
    }

    QualType build_specialization_type(QualType pattern_type) const {
        auto specialized_type = collect.substitute_template_type_with_bindings(
            pattern_type,
            *selected_parameters,
            specialization_bindings,
            loc);
        return collect.finalize_deferred_semantic_type(specialized_type, loc);
    }

    std::shared_ptr<Symbol> create_specialization_symbol(
        QualType specialized_type) const {
        std::shared_ptr<Symbol> specialization_symbol =
            pattern->sym
                ? clone_symbol_shallow_for_specialization(
                      pattern->sym,
                      desugar_type(specialized_type, ast_ctx()))
                : std::make_shared<Symbol>(
                      pattern->name,
                      SymbolKind::VARIABLE,
                      desugar_type(specialized_type, ast_ctx()),
                      pattern->storage_class,
                      variable_linkage_for_specialization(pattern),
                      pattern->is_inline != 0);
        if (!specialization_symbol) {
            return nullptr;
        }

        specialization_symbol->name = pattern->name;
        specialization_symbol->kind = SymbolKind::VARIABLE;
        specialization_symbol->type = desugar_type(specialized_type, ast_ctx());
        specialization_symbol->storage_class = pattern->storage_class;
        specialization_symbol->linkage =
            variable_linkage_for_specialization(pattern);
        specialization_symbol->is_inline = pattern->is_inline;
        copy_variable_symbol_metadata(pattern, specialization_symbol.get());
        apply_specialization_metadata(nullptr, specialization_symbol.get());
        return specialization_symbol;
    }

    std::unique_ptr<VariableDecl> create_placeholder_decl(
        QualType specialized_type,
        const std::shared_ptr<Symbol>& specialization_symbol) const {
        auto specialization_decl = collect.collect_make<VariableDecl>(
            specialized_type,
            pattern->name,
            nullptr,
            specialization_symbol,
            pattern->storage_class,
            pattern->is_inline != 0,
            pattern->location);
        specialization_decl->is_constexpr = pattern->is_constexpr;
        specialization_decl->is_thread_local = pattern->is_thread_local;
        specialization_decl->is_block_byref = pattern->is_block_byref;
        specialization_decl->original_type = build_specialization_type(
            selected_pattern->original_type ? selected_pattern->original_type
                                            : selected_pattern->type);
        specialization_decl->set_language_linkage(pattern->get_language_linkage());
        if (pattern->asm_label) {
            specialization_decl->set_asm_label(*pattern->asm_label);
        }
        apply_specialization_metadata(
            specialization_decl.get(),
            specialization_symbol.get());
        if (specialization_decl->sym) {
            specialization_decl->sym->variable_definition =
                specialization_decl.get();
        }
        return specialization_decl;
    }

    bool prepare_entry() {
        entry = ast_ctx()->lookup_variable_template_specialization(
            variable_template,
            normalized_arguments);
        if (entry) {
            return true;
        }

        QualType specialized_type = build_specialization_type(selected_pattern->type);
        if (!specialized_type) {
            return fail(
                "internal error: variable template specialization did not produce a valid type",
                loc);
        }

        auto specialization_symbol = create_specialization_symbol(specialized_type);
        auto specialization_decl =
            create_placeholder_decl(specialized_type, specialization_symbol);
        entry = &ast_ctx()->get_or_create_variable_template_specialization(
            variable_template,
            normalized_arguments,
            std::move(specialization_decl),
            specialization_symbol);
        return true;
    }

    bool materialize_entry_declaration() {
        if (!entry || !entry->specialization_decl || !entry->specialization_symbol) {
            return false;
        }

        auto rewrite_specialized_type = [this](QualType type) -> QualType {
            return collect.substitute_template_type_with_bindings(
                type,
                *selected_parameters,
                specialization_bindings,
                loc);
        };
        auto rewrite_specialized_arguments =
            [this](const std::vector<TemplateArgument>& template_arguments)
            -> std::vector<TemplateArgument> {
            return collect.substitute_template_arguments_with_bindings(
                template_arguments,
                *selected_parameters,
                specialization_bindings,
                loc);
        };
        auto clone_pass_builder = make_template_binding_clone_pass_builder(
            ast_ctx(),
            &collect,
            *selected_parameters,
            specialization_bindings,
            loc,
            "variable template non-type parameter requires a concrete value",
            rewrite_specialized_type,
            rewrite_specialized_arguments,
            {},
            {});
        auto clone_pass = clone_pass_builder.build_substitution_pass();

        QualType specialized_type = build_specialization_type(selected_pattern->type);
        QualType specialized_original_type = build_specialization_type(
            selected_pattern->original_type ? selected_pattern->original_type
                                            : selected_pattern->type);
        std::unique_ptr<Expr> specialized_init;
        if (selected_pattern->init) {
            std::string clone_error;
            specialized_init =
                clone_pass.clone_expr(selected_pattern->init.get(), &clone_error);
            if (!specialized_init) {
                return fail_instantiation(
                    clone_error.empty()
                        ? "variable template initializer cloning is not supported"
                        : clone_error,
                    selected_pattern->location);
            }

            std::string resolution_error;
            if (!collect.resolve_dependent_expr_after_substitution(
                    specialized_init,
                    QualType(),
                    &resolution_error)) {
                return fail_instantiation(
                    resolution_error.empty()
                        ? "failed to resolve variable template initializer after substitution"
                        : resolution_error,
                    selected_pattern->location);
            }
        }

        auto* specialization_decl = entry->specialization_decl.get();
        auto specialization_symbol = entry->specialization_symbol;
        specialization_decl->type = specialized_type;
        specialization_decl->original_type = specialized_original_type;
        specialization_decl->name = pattern->name;
        specialization_decl->storage_class = pattern->storage_class;
        specialization_decl->is_inline = pattern->is_inline;
        specialization_decl->is_constexpr = pattern->is_constexpr;
        specialization_decl->is_thread_local = pattern->is_thread_local;
        specialization_decl->is_block_byref = pattern->is_block_byref;
        specialization_decl->init = std::move(specialized_init);
        specialization_decl->explicit_specialization_arguments.clear();
        specialization_decl->has_explicit_specialization_argument_list = false;
        specialization_decl->set_language_linkage(pattern->get_language_linkage());
        if (pattern->asm_label) {
            specialization_decl->set_asm_label(*pattern->asm_label);
        }
        specialization_decl->sym = specialization_symbol;

        specialization_symbol->type = desugar_type(specialized_type, ast_ctx());
        specialization_symbol->storage_class = pattern->storage_class;
        specialization_symbol->linkage =
            variable_linkage_for_specialization(pattern);
        specialization_symbol->is_inline = pattern->is_inline;
        specialization_symbol->variable_definition = specialization_decl;
        copy_variable_symbol_metadata(pattern, specialization_symbol.get());
        apply_specialization_metadata(
            specialization_decl,
            specialization_symbol.get());
        return true;
    }

    VariableDecl* instantiate_entry_definition() {
        if (!ast_ctx()->push_template_instantiation_frame()) {
            fail_instantiation(
                "template instantiation depth exceeded while instantiating variable template '" +
                    pattern->name + "'",
                loc);
            return nullptr;
        }

        if (specialization_symbol_out) {
            *specialization_symbol_out = entry->specialization_symbol;
        }

        if (!specialization_is_dependent) {
            collect.collect_add_global_symbol(entry->specialization_symbol);
        }

        entry->is_instantiating = true;
        struct InstantiationGuard {
            VariableTemplateSpecializationEntry& entry;
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

        if (!materialize_entry_declaration()) {
            return nullptr;
        }

        entry->is_instantiated = true;
        return entry->specialization_decl.get();
    }
};

VariableDecl* Collect::instantiate_variable_template_specialization(
    const VariableTemplateDecl* variable_template,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc,
    std::shared_ptr<Symbol>* specialization_symbol_out) {
    return VariableTemplateSpecializationInstantiator(
               *this,
               variable_template,
               arguments,
               loc,
               specialization_symbol_out)
        .run();
}
