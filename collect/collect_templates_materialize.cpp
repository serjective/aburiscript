#include "collect.h"
#include "collect_templates_internal.h"

namespace {
bool function_symbol_matches_specialized_member(
    const Symbol* symbol,
    const FuncDecl* member_decl,
    const ASTContext* ast_ctx) {
    if (!symbol || !member_decl || symbol->kind != SymbolKind::FUNCTION) {
        return false;
    }
    if (symbol->function_definition == member_decl) {
        return true;
    }
    if (symbol->name != member_decl->name || !symbol->type || !member_decl->type) {
        return false;
    }
    return desugar_type(symbol->type, ast_ctx)
        .equals_unqualified(
            desugar_type(QualType(member_decl->type), ast_ctx));
}

bool nested_template_arguments_are_dependent(
    const Decl* nested_template,
    const std::vector<TemplateArgument>& arguments,
    const ASTContext* ast_ctx) {
    return template_specialization_components_are_dependent(
        nested_template,
        arguments,
        /*explicitly_dependent=*/false,
        ast_ctx);
}

QualType make_deferred_nested_template_specialization_type(
    const std::string& name,
    const Decl* nested_template,
    const std::vector<TemplateArgument>& arguments) {
    return QualType(std::make_shared<TemplateSpecializationType>(
        name,
        nested_template,
        arguments,
        /*is_dependent=*/true));
}
} // namespace

void Collect::note_specialization_use_for_symbol(
    const std::shared_ptr<Symbol>& symbol,
    SrcLoc loc) const {
    std::shared_ptr<Symbol> stable_symbol = symbol;
    if (!ast_ctx_ || !stable_symbol || loc.isInvalid()) {
        return;
    }

    const auto* specialization_info =
        get_symbol_function_template_specialization(stable_symbol.get());
    if (specialization_info && specialization_info->primary_template) {
        if (auto* entry =
                ast_ctx_->lookup_function_template_specialization(
                    specialization_info->primary_template,
                    specialization_info->arguments)) {
            entry->note_first_required_loc(loc);
        }
        return;
    }

    const auto* variable_specialization_info =
        get_symbol_variable_template_specialization(stable_symbol.get());
    if (variable_specialization_info &&
        variable_specialization_info->primary_template) {
        if (auto* entry =
                ast_ctx_->lookup_variable_template_specialization(
                    variable_specialization_info->primary_template,
                    variable_specialization_info->arguments)) {
            entry->note_first_required_loc(loc);
        }
        return;
    }

    QualType owner_type = get_symbol_owner_record_type(stable_symbol.get());
    auto owner_record_type =
        desugar_type(owner_type, ast_ctx_.get()).as_shared<ObjectType>();
    if (!owner_record_type || !owner_record_type->is_class_template_specialization()) {
        return;
    }

    const auto* owner_primary_template =
        owner_record_type->get_primary_class_template();
    if (!owner_primary_template) {
        return;
    }

    auto* owner_entry =
        ast_ctx_->lookup_class_template_specialization(
            owner_primary_template,
            owner_record_type->get_template_specialization_arguments());
    if (!owner_entry) {
        return;
    }

    const auto* primary_member_decl =
        owner_entry->lookup_primary_member_for_specialized_symbol(
            stable_symbol.get());
    if (!primary_member_decl) {
        const auto* specialized_member_decl =
            dyn_cast<FuncDecl>(stable_symbol->function_definition);
        if (specialized_member_decl) {
            primary_member_decl =
                owner_entry->lookup_primary_member_for_specialized_decl(
                    specialized_member_decl);
        }
    }
    if (!primary_member_decl) {
        for (const auto& member_decl : owner_entry->member_decls) {
            const auto* specialized_member_decl =
                dyn_cast<FuncDecl>(member_decl.get());
            if (!function_symbol_matches_specialized_member(
                    stable_symbol.get(),
                    specialized_member_decl,
                    ast_ctx_.get())) {
                continue;
            }
            primary_member_decl =
                owner_entry->lookup_primary_member_for_specialized_decl(
                    specialized_member_decl);
            if (primary_member_decl) {
                owner_entry->map_specialized_member_symbol_to_primary_member(
                    stable_symbol.get(),
                    primary_member_decl);
                break;
            }
        }
    }
    if (!primary_member_decl) {
        return;
    }
    owner_entry->note_primary_member_first_required_loc(
        primary_member_decl,
        loc);
    const_cast<Collect*>(this)->materialize_class_template_member_body(
        *owner_entry,
        primary_member_decl,
        loc);
    if (auto* pending_body =
            owner_entry->lookup_pending_member_body_instantiation(
                primary_member_decl);
        pending_body &&
        pending_body->is_materialized &&
        pending_body->specialized_function) {
        stable_symbol->type = QualType(pending_body->specialized_function->type);
        stable_symbol->is_defined =
            function_decl_defines_entity(pending_body->specialized_function);
        stable_symbol->function_definition =
            stable_symbol->is_defined ? pending_body->specialized_function : nullptr;
    }
}

QualType Collect::instantiate_alias_template_specialization(
    const AliasTemplateDecl* alias_template,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc) {
    if (!alias_template) {
        return QualType();
    }

    const auto* alias_decl = alias_template->alias_decl();
    if (!alias_decl) {
        report_error("internal error: missing alias template pattern", loc);
        return QualType();
    }

    TemplateArgumentBindings specialization_bindings;
    std::string binding_error;
    if (!bind_template_arguments_for_specialization(
            alias_template,
            arguments,
            specialization_bindings,
            loc,
            &binding_error)) {
        report_error(
            "alias template '" + alias_decl->name +
                "' template arguments do not match the parameter list" +
                (binding_error.empty() ? std::string() : ": " + binding_error),
            loc);
        return QualType();
    }

    for (const auto& argument : arguments) {
        if (!collect_template_internal::template_argument_has_known_payload(argument)) {
            report_error("alias template argument has unknown type", loc);
            return QualType();
        }
    }
    for (size_t idx = 0; idx < alias_template->parameters.size(); ++idx) {
        auto* non_type_parameter =
            dyn_cast<TemplateNonTypeParmDecl>(alias_template->parameters[idx].get());
        if (!non_type_parameter || idx >= specialization_bindings.size()) {
            continue;
        }
        if (specialization_bindings[idx].arguments.empty()) {
            continue;
        }
        QualType expected_type = substitute_template_type_with_bindings(
            non_type_parameter->type,
            alias_template->parameters,
            specialization_bindings,
            loc);
        expected_type = finalize_deferred_semantic_type(expected_type, loc);
        for (auto& bound_argument : specialization_bindings[idx].arguments) {
            std::string normalize_error;
            if (!collect_template_internal::normalize_concrete_template_value_argument(
                    bound_argument,
                    expected_type,
                    &normalize_error)) {
                report_error(
                    normalize_error.empty()
                        ? "failed to normalize alias template value argument"
                        : normalize_error,
                    loc);
                return QualType();
            }
        }
    }
    std::string invalid_value_error;
    if (!collect_template_internal::
            template_argument_bindings_have_valid_nondependent_values(
                specialization_bindings,
                &invalid_value_error)) {
        report_error(
            invalid_value_error.empty()
                ? "alias template argument has invalid non-dependent value"
                : invalid_value_error,
            loc);
        return QualType();
    }

    auto rewritten = substitute_template_type_with_bindings(
        alias_decl->type,
        alias_template->parameters,
        specialization_bindings,
        loc);
    auto finalized = finalize_deferred_semantic_type(rewritten, loc);
    if (!finalized) {
        return QualType();
    }

    auto canonical = desugar_type(finalized, ast_ctx_.get());
    return canonical ? canonical : finalized;
}

QualType Collect::collect_lookup_record_nested_template_type(
    QualType owner_type,
    const std::string& name,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc,
    bool* matched_template) {
    if (matched_template) {
        *matched_template = false;
    }

    const auto* nested_template =
        collect_lookup_record_nested_template(owner_type, name);
    if (!nested_template || !nested_template->decl) {
        return QualType();
    }
    if (matched_template) {
        *matched_template = true;
    }

    const auto* nested_template_decl =
        static_cast<const Decl*>(nested_template->decl);
    if (nested_template_arguments_are_dependent(
            nested_template_decl,
            arguments,
            ast_ctx_.get())) {
        return make_deferred_nested_template_specialization_type(
            name,
            nested_template_decl,
            arguments);
    }

    if (auto* alias_template =
            dyn_cast<AliasTemplateDecl>(
                const_cast<TemplateDecl*>(nested_template->decl))) {
        return instantiate_alias_template_specialization(
            alias_template,
            arguments,
            loc);
    }

    if (auto* class_template =
            dyn_cast<ClassTemplateDecl>(
                const_cast<TemplateDecl*>(nested_template->decl))) {
        auto* specialization_decl =
            instantiate_class_template_specialization(
                class_template,
                arguments,
                loc);
        if (specialization_decl) {
            return QualType(specialization_decl->get_record_type());
        }
        return QualType();
    }

    return QualType();
}

QualType Collect::substitute_class_template_type(
    QualType type,
    const ClassTemplateDecl* class_template,
    const std::vector<TemplateArgument>& specialization_arguments,
    SrcLoc loc) {
    if (!class_template) {
        return type;
    }
    auto substituted = substitute_template_type(
        type,
        class_template->parameters,
        specialization_arguments,
        loc);
    if (!ast_ctx_) {
        return substituted;
    }
    const ObjectDecl* pattern_semantic_decl = class_template->pattern_semantic_decl();
    if (!pattern_semantic_decl) {
        return substituted;
    }
    auto* specialization_entry = ast_ctx_->lookup_class_template_specialization(
        class_template,
        specialization_arguments);
    if (!specialization_entry || !specialization_entry->specialization_type) {
        return substituted;
    }
    return collect_template_internal::replace_record_decl_in_type(
        substituted,
        pattern_semantic_decl,
        QualType(specialization_entry->specialization_type),
        ast_ctx_.get());
}

std::vector<TemplateArgument> Collect::substitute_class_template_arguments(
    const std::vector<TemplateArgument>& arguments,
    const ClassTemplateDecl* class_template,
    const std::vector<TemplateArgument>& specialization_arguments,
    SrcLoc loc) {
    if (!class_template) {
        return arguments;
    }
    return substitute_template_arguments(
        arguments,
        class_template->parameters,
        specialization_arguments,
        loc);
}
