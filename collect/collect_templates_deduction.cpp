#include "collect_templates_internal.h"

namespace {

enum class TemplateTypeDeductionMode : uint8_t {
    Call,
    PartialOrdering,
};

std::optional<size_t> find_template_parameter_index(
    const TemplateTypeParmType* parm_type,
    const TemplateParameterList& parameters) {
    if (!parm_type) {
        return std::nullopt;
    }
    if (parm_type->parameter_decl) {
        for (size_t idx = 0; idx < parameters.size(); ++idx) {
            if (parameters[idx].get() == parm_type->parameter_decl) {
                return idx;
            }
        }
    }
    if (parm_type->index < parameters.size()) {
        return parm_type->index;
    }
    return std::nullopt;
}

QualType strip_top_level_qualifiers(QualType type) {
    if (!type) {
        return type;
    }
    return QualType(type.get_shared());
}

struct TemplateSpecializationMatchInfo {
    const Decl* primary_template = nullptr;
    std::string_view template_name;
    const std::vector<TemplateArgument>* arguments = nullptr;
};

std::optional<TemplateSpecializationMatchInfo> extract_template_specialization_match_info(
    QualType type) {
    auto spelled = desugar_typedefs(type);
    auto raw = spelled.get_shared();
    if (!raw) {
        return std::nullopt;
    }

    if (auto specialization = dyn_cast_shared<TemplateSpecializationType>(raw)) {
        return TemplateSpecializationMatchInfo{
            specialization->primary_template,
            specialization->template_name,
            &specialization->arguments};
    }

    auto object = desugar_type(spelled).as_shared<ObjectType>();
    if (!object || !object->is_class_template_specialization()) {
        return std::nullopt;
    }

    std::string_view template_name;
    if (auto* primary_template = object->get_primary_class_template()) {
        if (auto* record = primary_template->record_decl()) {
            template_name = record->name;
        }
    }
    return TemplateSpecializationMatchInfo{
        object->get_primary_class_template(),
        template_name,
        &object->get_template_specialization_arguments()};
}

bool bind_deduced_template_argument(
    QualType pattern_type,
    const TemplateTypeParmType* parm_type,
    QualType argument_type,
    const TemplateParameterList& parameters,
    TemplateArgumentBindings& deduced_arguments) {
    auto index = find_template_parameter_index(parm_type, parameters);
    if (!index.has_value() || *index >= deduced_arguments.size()) {
        return false;
    }

    auto deduced_type = desugar_typedefs(argument_type);
    if (pattern_type.get_qualifiers() != QUAL_NONE) {
        deduced_type = QualType(
            deduced_type.get_shared(),
            static_cast<uint8_t>(
                deduced_type.get_qualifiers() & ~pattern_type.get_qualifiers()));
    }

    auto& existing = deduced_arguments[*index];
    const auto* parameter = parameters[*index].get();
    if (!parameter) {
        return false;
    }

    TemplateArgument deduced_argument(deduced_type);
    if (parameter->is_parameter_pack || parm_type->is_parameter_pack) {
        if (existing.is_unbound()) {
            existing.kind = TemplateArgumentBindingKind::Pack;
        } else if (!existing.is_pack()) {
            return false;
        }
        existing.arguments.push_back(std::move(deduced_argument));
        return true;
    }

    if (existing.is_unbound()) {
        existing = TemplateArgumentBinding::single(std::move(deduced_argument));
        return true;
    }
    const auto* existing_single = existing.single_argument();
    return existing_single &&
           existing_single->kind == TemplateArgumentKind::Type &&
           existing_single->type.equals_qualified(deduced_type);
}

bool bind_deduced_template_template_argument(
    const TemplateTemplateParmDecl* parameter_decl,
    const Decl* argument_template_decl,
    const TemplateParameterList& parameters,
    TemplateArgumentBindings& deduced_arguments) {
    if (!parameter_decl || !argument_template_decl) {
        return false;
    }

    auto parameter_index = template_sema_internal::find_template_parameter_index_by_decl(
        parameter_decl,
        parameters);
    if (!parameter_index || *parameter_index >= deduced_arguments.size()) {
        return false;
    }

    TemplateArgument deduced_argument;
    if (auto* argument_template_parameter = dyn_cast<TemplateTemplateParmDecl>(
            const_cast<Decl*>(argument_template_decl))) {
        deduced_argument = TemplateArgument::dependent_template_argument(
            argument_template_parameter->get_name(),
            argument_template_parameter);
    } else {
        const TemplateDecl* argument_template = nullptr;
        switch (argument_template_decl->get_kind()) {
            case DeclKind::AliasTemplateDecl:
            case DeclKind::ClassTemplateDecl:
                argument_template =
                    static_cast<const TemplateDecl*>(argument_template_decl);
                break;
            default:
                break;
        }
        if (!argument_template) {
            return false;
        }
        deduced_argument =
            TemplateArgument::template_argument(argument_template);
    }

    auto& existing = deduced_arguments[*parameter_index];
    if (parameter_decl->is_parameter_pack) {
        if (existing.is_unbound()) {
            existing.kind = TemplateArgumentBindingKind::Pack;
        } else if (!existing.is_pack()) {
            return false;
        }
        existing.arguments.push_back(std::move(deduced_argument));
        return true;
    }

    if (existing.is_unbound()) {
        existing = TemplateArgumentBinding::single(std::move(deduced_argument));
        return true;
    }
    const auto* existing_single = existing.single_argument();
    return existing_single &&
           existing_single->kind == TemplateArgumentKind::Template &&
           existing_single->equals(deduced_argument);
}

bool deduce_template_argument_types_impl(
    QualType pattern_type,
    QualType argument_type,
    const TemplateParameterList& parameters,
    TemplateArgumentBindings& deduced_arguments,
    TemplateTypeDeductionMode deduction_mode,
    bool argument_is_lvalue = false) {
    if (!pattern_type) {
        return true;
    }
    if (!argument_type) {
        return false;
    }
    if (!type_depends_on_template_parameters(pattern_type)) {
        if (deduction_mode == TemplateTypeDeductionMode::Call) {
            return true;
        }
        return desugar_type(pattern_type).equals_qualified(desugar_type(argument_type));
    }

    auto spelled_pattern = desugar_typedefs(pattern_type);
    auto pattern_raw = spelled_pattern.get_shared();
    if (!pattern_raw) {
        return false;
    }

    if (auto pattern_ref = dyn_cast_shared<ReferenceType>(pattern_raw)) {
        auto referred_pattern = desugar_typedefs(pattern_ref->referred_type);
        auto parm_type = dyn_cast_shared<TemplateTypeParmType>(
            referred_pattern.get_shared());
        if (deduction_mode == TemplateTypeDeductionMode::Call) {
            if (argument_is_lvalue &&
                pattern_ref->isRValueReference() &&
                parm_type &&
                pattern_ref->referred_type.get_qualifiers() == QUAL_NONE) {
                return deduce_template_argument_types_impl(
                    pattern_ref->referred_type,
                    make_reference_type(argument_type, ReferenceKind::LValue),
                    parameters,
                    deduced_arguments,
                    deduction_mode);
            }
            return deduce_template_argument_types_impl(
                pattern_ref->referred_type,
                remove_reference(argument_type),
                parameters,
                deduced_arguments,
                deduction_mode);
        }

        auto spelled_argument = desugar_typedefs(argument_type);
        auto argument_ref =
            dyn_cast_shared<ReferenceType>(spelled_argument.get_shared());
        if (pattern_ref->isRValueReference() &&
            parm_type &&
            pattern_ref->referred_type.get_qualifiers() == QUAL_NONE &&
            argument_ref &&
            argument_ref->isLValueReference()) {
            return deduce_template_argument_types_impl(
                pattern_ref->referred_type,
                spelled_argument,
                parameters,
                deduced_arguments,
                deduction_mode);
        }
        if (!argument_ref ||
            pattern_ref->reference_kind != argument_ref->reference_kind) {
            return false;
        }
        return deduce_template_argument_types_impl(
            pattern_ref->referred_type,
            argument_ref->referred_type,
            parameters,
            deduced_arguments,
            deduction_mode);
    }

    if (auto pattern_dependent_name =
            dyn_cast_shared<DependentNameType>(pattern_raw)) {
        if (auto resolved_type = lookup_dependent_name_resolved_type(
                pattern_dependent_name.get(),
                nullptr)) {
            return deduce_template_argument_types_impl(
                QualType(resolved_type),
                argument_type,
                parameters,
                deduced_arguments,
                deduction_mode);
        }
        return true;
    }

    if (auto parm_type = dyn_cast_shared<TemplateTypeParmType>(pattern_raw)) {
        return bind_deduced_template_argument(
            spelled_pattern,
            parm_type.get(),
            argument_type,
            parameters,
            deduced_arguments);
    }

    spelled_pattern = strip_top_level_qualifiers(spelled_pattern);
    auto spelled_argument = strip_top_level_qualifiers(desugar_typedefs(argument_type));
    auto argument_raw = spelled_argument.get_shared();
    if (!argument_raw) {
        return false;
    }

    if (auto pattern_ptr = dyn_cast_shared<PointerType>(pattern_raw)) {
        auto argument_ptr = dyn_cast_shared<PointerType>(argument_raw);
        return argument_ptr &&
            deduce_template_argument_types_impl(
                pattern_ptr->pointed_type,
                argument_ptr->pointed_type,
                parameters,
                deduced_arguments,
                deduction_mode);
    }

    if (auto pattern_mem_ptr = dyn_cast_shared<MemberPointerType>(pattern_raw)) {
        auto argument_mem_ptr = dyn_cast_shared<MemberPointerType>(argument_raw);
        return argument_mem_ptr &&
            deduce_template_argument_types_impl(
                pattern_mem_ptr->class_type,
                argument_mem_ptr->class_type,
                parameters,
                deduced_arguments,
                deduction_mode) &&
            deduce_template_argument_types_impl(
                pattern_mem_ptr->member_type,
                argument_mem_ptr->member_type,
                parameters,
                deduced_arguments,
                deduction_mode);
    }

    if (auto pattern_block_ptr = dyn_cast_shared<BlockPointerType>(pattern_raw)) {
        auto argument_block_ptr = dyn_cast_shared<BlockPointerType>(argument_raw);
        return argument_block_ptr &&
            deduce_template_argument_types_impl(
                pattern_block_ptr->pointed_type,
                argument_block_ptr->pointed_type,
                parameters,
                deduced_arguments,
                deduction_mode);
    }

    if (auto pattern_array = dyn_cast_shared<ArrayType>(pattern_raw)) {
        auto argument_array = dyn_cast_shared<ArrayType>(argument_raw);
        if (!argument_array) {
            return false;
        }
        if (pattern_array->size_kind != argument_array->size_kind ||
            pattern_array->size != argument_array->size) {
            return false;
        }
        return deduce_template_argument_types_impl(
            pattern_array->element_type,
            argument_array->element_type,
            parameters,
            deduced_arguments,
            deduction_mode);
    }

    if (auto pattern_fn = dyn_cast_shared<FunctionType>(pattern_raw)) {
        auto argument_fn = dyn_cast_shared<FunctionType>(argument_raw);
        if (!argument_fn ||
            pattern_fn->parameters.size() != argument_fn->parameters.size() ||
            pattern_fn->is_variadic != argument_fn->is_variadic) {
            return false;
        }
        if (!deduce_template_argument_types_impl(
                pattern_fn->ret_type,
                argument_fn->ret_type,
                parameters,
                deduced_arguments,
                deduction_mode)) {
            return false;
        }
        for (size_t idx = 0; idx < pattern_fn->parameters.size(); ++idx) {
            if (!deduce_template_argument_types_impl(
                    pattern_fn->parameters[idx],
                    argument_fn->parameters[idx],
                    parameters,
                    deduced_arguments,
                    deduction_mode)) {
                return false;
            }
        }
        return true;
    }

    if (auto pattern_vector = dyn_cast_shared<VectorType>(pattern_raw)) {
        auto argument_vector = dyn_cast_shared<VectorType>(argument_raw);
        return argument_vector &&
            pattern_vector->total_bytes == argument_vector->total_bytes &&
            deduce_template_argument_types_impl(
                pattern_vector->element_type,
                argument_vector->element_type,
                parameters,
                deduced_arguments,
                deduction_mode);
    }

    if (auto pattern_specialization =
            dyn_cast_shared<TemplateSpecializationType>(pattern_raw)) {
        auto argument_specialization =
            extract_template_specialization_match_info(argument_type);
        if (!argument_specialization.has_value() ||
            !argument_specialization->arguments) {
            return false;
        }
        if (auto* pattern_template_parameter = dyn_cast<TemplateTemplateParmDecl>(
                const_cast<Decl*>(pattern_specialization->primary_template))) {
            if (!bind_deduced_template_template_argument(
                    pattern_template_parameter,
                    argument_specialization->primary_template,
                    parameters,
                    deduced_arguments)) {
                return false;
            }
        } else {
            if (pattern_specialization->primary_template &&
                argument_specialization->primary_template &&
                pattern_specialization->primary_template !=
                    argument_specialization->primary_template) {
                return false;
            }
            if ((!pattern_specialization->primary_template ||
                 !argument_specialization->primary_template) &&
                pattern_specialization->template_name !=
                    argument_specialization->template_name) {
                return false;
            }
        }
        if (pattern_specialization->arguments.size() !=
            argument_specialization->arguments->size()) {
            return false;
        }
        for (size_t idx = 0; idx < pattern_specialization->arguments.size(); ++idx) {
            const auto& pattern_argument = pattern_specialization->arguments[idx];
            const auto& argument_argument =
                (*argument_specialization->arguments)[idx];
            if (pattern_argument.kind != argument_argument.kind) {
                return false;
            }
            if (pattern_argument.kind == TemplateArgumentKind::Type) {
                if (!deduce_template_argument_types_impl(
                        pattern_argument.type,
                        argument_argument.type,
                        parameters,
                        deduced_arguments,
                        deduction_mode)) {
                    return false;
                }
                continue;
            }
            if (pattern_argument.is_dependent &&
                pattern_argument.referenced_parameter) {
                auto parameter_index = template_sema_internal::
                    find_template_parameter_index_by_decl(
                        pattern_argument.referenced_parameter,
                        parameters);
                if (!parameter_index ||
                    *parameter_index >= deduced_arguments.size()) {
                    return false;
                }
                auto& existing = deduced_arguments[*parameter_index];
                if (existing.is_unbound()) {
                    existing = TemplateArgumentBinding::single(argument_argument);
                } else {
                    const auto* existing_single = existing.single_argument();
                    if (!existing_single ||
                        !existing_single->equals(argument_argument)) {
                        return false;
                    }
                }
                continue;
            }
            TemplateArgument normalized_pattern = pattern_argument;
            TemplateArgument normalized_argument = argument_argument;
            QualType target_type = normalized_argument.value_type
                ? normalized_argument.value_type
                : normalized_pattern.value_type;
            if (!template_sema_internal::normalize_concrete_template_value_argument(
                    normalized_pattern,
                    target_type,
                    nullptr) ||
                !template_sema_internal::normalize_concrete_template_value_argument(
                    normalized_argument,
                    target_type,
                    nullptr) ||
                !normalized_pattern.equals(normalized_argument)) {
                return false;
            }
        }
        return true;
    }

    auto canonical_pattern = desugar_type(spelled_pattern);
    auto canonical_argument = desugar_type(spelled_argument);
    if (!canonical_pattern || !canonical_argument) {
        return false;
    }
    return canonical_pattern->equals(*canonical_argument.get_shared());
}

bool deduce_function_template_argument_types(
    QualType pattern_type,
    QualType argument_type,
    const TemplateParameterList& parameters,
    TemplateArgumentBindings& deduced_arguments,
    bool argument_is_lvalue = false) {
    return deduce_template_argument_types_impl(
        pattern_type,
        argument_type,
        parameters,
        deduced_arguments,
        TemplateTypeDeductionMode::Call,
        argument_is_lvalue);
}

bool class_template_partial_specialization_is_at_least_as_specialized_as(
    const ClassTemplatePartialSpecializationDecl* parameter_partial,
    const ClassTemplatePartialSpecializationDecl* argument_partial) {
    if (!parameter_partial || !argument_partial) {
        return false;
    }
    if (parameter_partial->specialization_arguments.size() !=
        argument_partial->specialization_arguments.size()) {
        return false;
    }
    for (const auto& parameter : parameter_partial->parameters) {
        if (parameter && parameter->is_parameter_pack) {
            return false;
        }
    }

    TemplateArgumentBindings deduced_bindings(
        parameter_partial->parameters.size());
    for (size_t idx = 0;
         idx < parameter_partial->specialization_arguments.size();
         ++idx) {
        const auto& pattern_argument =
            parameter_partial->specialization_arguments[idx];
        const auto& argument_argument =
            argument_partial->specialization_arguments[idx];
        if (pattern_argument.kind != argument_argument.kind) {
            return false;
        }
        if (pattern_argument.kind == TemplateArgumentKind::Type) {
            auto pattern_argument_type = desugar_typedefs(pattern_argument.type);
            auto argument_argument_type = desugar_typedefs(argument_argument.type);
            if (auto pattern_ref =
                    dyn_cast_shared<ReferenceType>(
                        pattern_argument_type.get_shared())) {
                auto argument_ref =
                    dyn_cast_shared<ReferenceType>(
                        argument_argument_type.get_shared());
                if (!argument_ref ||
                    pattern_ref->reference_kind != argument_ref->reference_kind) {
                    return false;
                }
            }
            if (!type_depends_on_template_parameters(pattern_argument.type)) {
                if (!desugar_type(pattern_argument.type).equals_qualified(
                        desugar_type(argument_argument.type))) {
                    return false;
                }
                continue;
            }
            if (!deduce_function_template_argument_types(
                    pattern_argument.type,
                    argument_argument.type,
                    parameter_partial->parameters,
                    deduced_bindings)) {
                return false;
            }
            continue;
        }

        if (pattern_argument.is_dependent &&
            pattern_argument.referenced_parameter) {
            auto parameter_index =
                template_sema_internal::find_template_parameter_index_by_decl(
                    pattern_argument.referenced_parameter,
                    parameter_partial->parameters);
            if (!parameter_index ||
                *parameter_index >= deduced_bindings.size()) {
                return false;
            }
            auto& existing = deduced_bindings[*parameter_index];
            if (existing.is_unbound()) {
                existing = TemplateArgumentBinding::single(argument_argument);
            } else {
                const auto* existing_single = existing.single_argument();
                if (!existing_single ||
                    !existing_single->equals(argument_argument)) {
                    return false;
                }
            }
            continue;
        }

        TemplateArgument normalized_pattern = pattern_argument;
        TemplateArgument normalized_argument = argument_argument;
        QualType target_type = normalized_argument.value_type
            ? normalized_argument.value_type
            : normalized_pattern.value_type;
        if (!template_sema_internal::normalize_concrete_template_value_argument(
                normalized_pattern,
                target_type,
                nullptr) ||
            !template_sema_internal::normalize_concrete_template_value_argument(
                normalized_argument,
                target_type,
                nullptr) ||
            !normalized_pattern.equals(normalized_argument)) {
            return false;
        }
    }

    for (const auto& binding : deduced_bindings) {
        if (binding.is_unbound()) {
            return false;
        }
    }
    return true;
}

} // namespace

namespace template_sema_internal {

bool deduce_class_template_partial_specialization_bindings(
    const ClassTemplatePartialSpecializationDecl* partial_specialization,
    const std::vector<TemplateArgument>& actual_arguments,
    TemplateArgumentBindings& deduced_bindings_out) {
    deduced_bindings_out.clear();
    if (!partial_specialization) {
        return false;
    }
    if (partial_specialization->specialization_arguments.size() !=
        actual_arguments.size()) {
        return false;
    }
    for (const auto& parameter : partial_specialization->parameters) {
        if (parameter && parameter->is_parameter_pack) {
            return false;
        }
    }

    deduced_bindings_out.resize(partial_specialization->parameters.size());
    for (size_t idx = 0; idx < actual_arguments.size(); ++idx) {
        const auto& pattern_argument =
            partial_specialization->specialization_arguments[idx];
        const auto& actual_argument = actual_arguments[idx];
        if (pattern_argument.kind != actual_argument.kind) {
            return false;
        }
        if (pattern_argument.kind == TemplateArgumentKind::Type) {
            auto pattern_argument_type = desugar_typedefs(pattern_argument.type);
            auto actual_argument_type = desugar_typedefs(actual_argument.type);
            if (auto pattern_ref =
                    dyn_cast_shared<ReferenceType>(
                        pattern_argument_type.get_shared())) {
                auto actual_ref =
                    dyn_cast_shared<ReferenceType>(
                        actual_argument_type.get_shared());
                if (!actual_ref ||
                    pattern_ref->reference_kind != actual_ref->reference_kind) {
                    return false;
                }
            }
            if (!type_depends_on_template_parameters(pattern_argument.type)) {
                if (!desugar_type(pattern_argument.type).equals_qualified(
                        desugar_type(actual_argument.type))) {
                    return false;
                }
                continue;
            }
            if (!deduce_function_template_argument_types(
                    pattern_argument.type,
                    actual_argument.type,
                    partial_specialization->parameters,
                    deduced_bindings_out)) {
                return false;
            }
            continue;
        }

        if (pattern_argument.is_dependent &&
            pattern_argument.referenced_parameter) {
            auto parameter_index = find_template_parameter_index_by_decl(
                pattern_argument.referenced_parameter,
                partial_specialization->parameters);
            if (!parameter_index ||
                *parameter_index >= deduced_bindings_out.size()) {
                return false;
            }
            auto& existing = deduced_bindings_out[*parameter_index];
            if (existing.is_unbound()) {
                existing = TemplateArgumentBinding::single(actual_argument);
            } else {
                const auto* existing_single = existing.single_argument();
                if (!existing_single ||
                    !existing_single->equals(actual_argument)) {
                    return false;
                }
            }
            continue;
        }

        TemplateArgument normalized_pattern = pattern_argument;
        TemplateArgument normalized_actual = actual_argument;
        QualType target_type = normalized_actual.value_type
            ? normalized_actual.value_type
            : normalized_pattern.value_type;
        if (!normalize_concrete_template_value_argument(
                normalized_pattern,
                target_type,
                nullptr) ||
            !normalize_concrete_template_value_argument(
                normalized_actual,
                target_type,
                nullptr) ||
            !normalized_pattern.equals(normalized_actual)) {
            return false;
        }
    }

    for (const auto& binding : deduced_bindings_out) {
        if (binding.is_unbound()) {
            return false;
        }
    }
    return true;
}

bool is_class_template_partial_specialization_more_specialized(
    const ClassTemplatePartialSpecializationDecl* lhs_partial,
    const ClassTemplatePartialSpecializationDecl* rhs_partial) {
    if (!lhs_partial || !rhs_partial || lhs_partial == rhs_partial) {
        return false;
    }

    bool rhs_from_lhs =
        class_template_partial_specialization_is_at_least_as_specialized_as(
            rhs_partial,
            lhs_partial);
    if (!rhs_from_lhs) {
        return false;
    }
    bool lhs_from_rhs =
        class_template_partial_specialization_is_at_least_as_specialized_as(
            lhs_partial,
            rhs_partial);
    return !lhs_from_rhs;
}

} // namespace template_sema_internal

bool Collect::deduce_function_template_call_arguments(
    const FunctionTemplateDecl* function_template,
    const std::vector<std::unique_ptr<Expr>>& call_args,
    std::vector<TemplateArgument>& deduced_arguments_out,
    const TemplateArgumentBindings* initial_bindings) const {
    std::vector<Expr*> raw_call_args;
    raw_call_args.reserve(call_args.size());
    for (const auto& call_arg : call_args) {
        raw_call_args.push_back(call_arg.get());
    }
    return deduce_function_template_call_arguments(
        function_template,
        raw_call_args,
        deduced_arguments_out,
        initial_bindings);
}

bool Collect::deduce_function_template_call_arguments(
    const FunctionTemplateDecl* function_template,
    const std::vector<Expr*>& call_args,
    std::vector<TemplateArgument>& deduced_arguments_out,
    const TemplateArgumentBindings* initial_bindings) const {
    deduced_arguments_out.clear();
    if (!function_template) {
        return false;
    }

    const auto* pattern = function_template->function_decl();
    if (!pattern) {
        return false;
    }

    TemplateArgumentBindings deduced_arguments(
        function_template->parameters.size());
    if (initial_bindings) {
        if (initial_bindings->size() != function_template->parameters.size()) {
            return false;
        }
        deduced_arguments = *initial_bindings;

        bool has_unbound_parameter_pack = false;
        for (size_t idx = 0; idx < function_template->parameters.size(); ++idx) {
            if (!deduced_arguments[idx].is_unbound()) {
                continue;
            }
            const auto* parameter = function_template->parameters[idx].get();
            if (parameter && parameter->is_parameter_pack) {
                has_unbound_parameter_pack = true;
                break;
            }
        }

        if (!has_unbound_parameter_pack) {
            TemplateArgumentBindings completed_bindings = deduced_arguments;
            std::string default_error;
            if (complete_template_argument_bindings_with_substituted_defaults(
                    function_template,
                    completed_bindings,
                    pattern->location,
                    &default_error)) {
                bool all_bound = true;
                for (const auto& binding : completed_bindings) {
                    if (binding.is_unbound()) {
                        all_bound = false;
                        break;
                    }
                }
                if (all_bound) {
                    deduced_arguments_out =
                        flatten_template_argument_bindings(completed_bindings);
                    return true;
                }
            }
        }
    }
    std::optional<size_t> pack_param_index;
    for (size_t idx = 0; idx < pattern->parameters.size(); ++idx) {
        auto* param_decl = dyn_cast<ParamDecl>(pattern->parameters[idx].get());
        if (!param_decl || !param_decl->is_parameter_pack) {
            continue;
        }
        if (pack_param_index.has_value()) {
            deduced_arguments_out.clear();
            return false;
        }
        pack_param_index = idx;
    }

    auto deduce_one_parameter =
        [&](size_t param_index, size_t arg_index) -> bool {
        auto* param_decl = dyn_cast<ParamDecl>(pattern->parameters[param_index].get());
        Expr* call_arg = arg_index < call_args.size() ? call_args[arg_index] : nullptr;
        if (!param_decl || !call_arg || !call_arg->get_type()) {
            return false;
        }

        QualType pattern_type = param_decl->type;
        QualType argument_type = call_arg->get_type();
        ValueCategory argument_category = classify_value_category(call_arg);
        auto canonical_pattern = desugar_typedefs(pattern_type);
        bool is_reference_parameter =
            canonical_pattern &&
            isa<ReferenceType>(canonical_pattern.get_shared().get());
        if (!is_reference_parameter) {
            pattern_type = strip_top_level_qualifiers(pattern_type);
            argument_type = remove_reference(argument_type);
            argument_type = decay_parameter_type(argument_type);
            argument_type = strip_top_level_qualifiers(argument_type);
        }

        return deduce_function_template_argument_types(
            pattern_type,
            argument_type,
            function_template->parameters,
            deduced_arguments,
            argument_category == ValueCategory::LValue);
    };

    if (!pack_param_index.has_value()) {
        size_t compare_count = std::min(call_args.size(), pattern->parameters.size());
        for (size_t idx = 0; idx < compare_count; ++idx) {
            if (!deduce_one_parameter(idx, idx)) {
                return false;
            }
        }
    } else {
        size_t leading_count = *pack_param_index;
        size_t trailing_count = pattern->parameters.size() - *pack_param_index - 1;
        if (call_args.size() < leading_count + trailing_count) {
            deduced_arguments_out.clear();
            return false;
        }
        for (size_t idx = 0; idx < leading_count; ++idx) {
            if (!deduce_one_parameter(idx, idx)) {
                return false;
            }
        }

        size_t pack_arg_count = call_args.size() - leading_count - trailing_count;
        for (size_t idx = 0; idx < pack_arg_count; ++idx) {
            if (!deduce_one_parameter(*pack_param_index, leading_count + idx)) {
                return false;
            }
        }

        for (size_t idx = 0; idx < trailing_count; ++idx) {
            size_t param_index = *pack_param_index + 1 + idx;
            size_t arg_index = leading_count + pack_arg_count + idx;
            if (!deduce_one_parameter(param_index, arg_index)) {
                return false;
            }
        }
    }

    std::string default_error;
    if (!complete_template_argument_bindings_with_substituted_defaults(
            function_template,
            deduced_arguments,
            pattern->location,
            &default_error)) {
        deduced_arguments_out.clear();
        return false;
    }
    deduced_arguments_out = flatten_template_argument_bindings(deduced_arguments);
    return true;
}

bool Collect::deduce_function_template_specialization_arguments(
    const FunctionTemplateDecl* function_template,
    QualType specialized_function_type,
    std::vector<TemplateArgument>& deduced_arguments_out,
    const TemplateArgumentBindings* initial_bindings) const {
    deduced_arguments_out.clear();
    if (!function_template || !specialized_function_type) {
        return false;
    }

    const auto* pattern = function_template->function_decl();
    if (!pattern || !pattern->type) {
        return false;
    }

    size_t implicit_object_parameter_count = 0;
    uint8_t parsed_trailing_cv_qualifiers = QUAL_NONE;
    if (const auto* method_decl = dyn_cast<CppMethodDecl>(pattern);
        method_decl && method_decl->storage_class != StorageClass::STATIC) {
        implicit_object_parameter_count = 1;
    }

    return deduce_function_template_specialization_arguments_from_pattern(
        QualType(pattern->type),
        function_template->parameters,
        function_template,
        specialized_function_type,
        deduced_arguments_out,
        initial_bindings,
        parsed_trailing_cv_qualifiers,
        implicit_object_parameter_count);
}

bool Collect::deduce_function_template_specialization_arguments_from_pattern(
    QualType pattern_function_type,
    const TemplateParameterList& template_parameters,
    const TemplateDecl* template_decl_for_defaults,
    QualType specialized_function_type,
    std::vector<TemplateArgument>& deduced_arguments_out,
    const TemplateArgumentBindings* initial_bindings,
    uint8_t parsed_trailing_cv_qualifiers,
    size_t implicit_object_parameter_count) const {
    deduced_arguments_out.clear();
    if (!pattern_function_type || !specialized_function_type) {
        return false;
    }

    auto pattern_function =
        desugar_type(pattern_function_type).as_shared<FunctionType>();
    auto specialized_function =
        desugar_type(specialized_function_type).as_shared<FunctionType>();
    if (!pattern_function || !specialized_function) {
        return false;
    }

    if (pattern_function->parameters.size() < implicit_object_parameter_count) {
        return false;
    }

    if (pattern_function->member_ref_qualifier !=
            specialized_function->member_ref_qualifier ||
        pattern_function->has_prototype != specialized_function->has_prototype ||
        pattern_function->is_variadic != specialized_function->is_variadic ||
        pattern_function->has_explicit_exception_spec !=
            specialized_function->has_explicit_exception_spec ||
        pattern_function->exception_spec != specialized_function->exception_spec ||
        pattern_function->parameters.size() !=
            specialized_function->parameters.size() +
                implicit_object_parameter_count) {
        return false;
    }

    if (implicit_object_parameter_count > 0) {
        auto this_ptr_type =
            desugar_type(pattern_function->parameters.front()).as_shared<PointerType>();
        if (!this_ptr_type) {
            return false;
        }
        uint8_t expected_cv =
            this_ptr_type->pointed_type.get_qualifiers() &
            static_cast<uint8_t>(QUAL_CONST | QUAL_VOLATILE);
        uint8_t parsed_cv =
            parsed_trailing_cv_qualifiers &
            static_cast<uint8_t>(QUAL_CONST | QUAL_VOLATILE);
        if (parsed_cv != expected_cv) {
            return false;
        }
    } else if (parsed_trailing_cv_qualifiers != QUAL_NONE) {
        return false;
    }

    TemplateArgumentBindings deduced_arguments(template_parameters.size());
    if (initial_bindings) {
        if (initial_bindings->size() != template_parameters.size()) {
            return false;
        }
        deduced_arguments = *initial_bindings;
    }

    if (!deduce_function_template_argument_types(
            pattern_function->ret_type,
            specialized_function->ret_type,
            template_parameters,
            deduced_arguments)) {
        return false;
    }

    for (size_t idx = 0; idx < specialized_function->parameters.size(); ++idx) {
        if (!deduce_function_template_argument_types(
                pattern_function->parameters[idx + implicit_object_parameter_count],
                specialized_function->parameters[idx],
                template_parameters,
                deduced_arguments)) {
            return false;
        }
    }

    std::string default_error;
    if (!complete_template_argument_bindings_with_substituted_defaults(
            template_decl_for_defaults,
            deduced_arguments,
            SrcLoc(),
            &default_error)) {
        deduced_arguments_out.clear();
        return false;
    }

    deduced_arguments_out = flatten_template_argument_bindings(deduced_arguments);
    return true;
}

Collect::TemplatePartialOrderingResult
Collect::compare_function_template_partial_ordering(
    const FunctionTemplateDecl* lhs_template,
    const FunctionTemplateDecl* rhs_template) const {
    if (!lhs_template || !rhs_template || lhs_template == rhs_template) {
        return TemplatePartialOrderingResult::Unordered;
    }

    const auto* lhs_pattern = lhs_template->function_decl();
    const auto* rhs_pattern = rhs_template->function_decl();
    if (!lhs_pattern || !rhs_pattern) {
        return TemplatePartialOrderingResult::Unordered;
    }

    auto count_named_params = [](const FuncDecl* pattern) -> size_t {
        if (!pattern) {
            return 0;
        }
        auto function_type = desugar_type(QualType(pattern->type)).as_shared<FunctionType>();
        bool has_void_param = function_type &&
            function_type->parameters.size() == 1 &&
            function_type->parameters[0]->isVoid();
        return has_void_param ? 0 : pattern->parameters.size();
    };

    size_t lhs_param_count = count_named_params(lhs_pattern);
    size_t rhs_param_count = count_named_params(rhs_pattern);
    if (lhs_param_count != rhs_param_count) {
        return TemplatePartialOrderingResult::Unordered;
    }
    auto has_parameter_pack = [](const FuncDecl* pattern) -> bool {
        if (!pattern) {
            return false;
        }
        for (const auto& parameter : pattern->parameters) {
            auto* param_decl = dyn_cast<ParamDecl>(parameter.get());
            if (param_decl && param_decl->is_parameter_pack) {
                return true;
            }
        }
        return false;
    };
    if (has_parameter_pack(lhs_pattern) || has_parameter_pack(rhs_pattern)) {
        return TemplatePartialOrderingResult::Unordered;
    }

    auto build_partial_ordering_argument_types =
        [&](const FunctionTemplateDecl* argument_template,
            std::vector<QualType>& transformed_types_out) -> bool {
        transformed_types_out.clear();
        const auto* argument_pattern =
            argument_template ? argument_template->function_decl() : nullptr;
        if (!argument_pattern) {
            return false;
        }

        TemplateArgumentBindings transformed_bindings(
            argument_template->parameters.size());
        for (size_t idx = 0; idx < argument_template->parameters.size(); ++idx) {
            const auto* parameter = argument_template->parameters[idx].get();
            if (!parameter || parameter->is_parameter_pack) {
                return false;
            }
            if (isa<TemplateTypeParmDecl>(parameter)) {
                auto unique_type = std::make_shared<ObjectType>(
                    "__aburi_partial_ordering_" + std::to_string(idx),
                    false,
                    true);
                transformed_bindings[idx] = TemplateArgumentBinding::single(
                    TemplateArgument(QualType(unique_type)));
            }
        }

        transformed_types_out.reserve(rhs_param_count);
        for (size_t idx = 0; idx < rhs_param_count; ++idx) {
            auto* argument_decl =
                dyn_cast<ParamDecl>(argument_pattern->parameters[idx].get());
            if (!argument_decl) {
                return false;
            }
            auto transformed_type = substitute_template_type_with_bindings(
                argument_decl->type,
                argument_template->parameters,
                transformed_bindings,
                argument_decl->location,
                true);
            if (type_depends_on_template_parameters(transformed_type)) {
                return false;
            }
            transformed_types_out.push_back(transformed_type);
        }
        return true;
    };

    auto template_is_at_least_as_specialized_as =
        [&](const FunctionTemplateDecl* parameter_template,
            const FunctionTemplateDecl* argument_template) -> bool {
        const auto* parameter_pattern = parameter_template->function_decl();
        if (!parameter_pattern) {
            return false;
        }

        std::vector<QualType> transformed_argument_types;
        if (!build_partial_ordering_argument_types(
                argument_template,
                transformed_argument_types) ||
            transformed_argument_types.size() != lhs_param_count) {
            return false;
        }

        TemplateArgumentBindings deduced_arguments(
            parameter_template->parameters.size());
        for (size_t idx = 0; idx < lhs_param_count; ++idx) {
            auto* parameter_decl =
                dyn_cast<ParamDecl>(parameter_pattern->parameters[idx].get());
            if (!parameter_decl) {
                return false;
            }

            QualType pattern_type = parameter_decl->type;
            QualType argument_type = transformed_argument_types[idx];
            if (!deduce_template_argument_types_impl(
                    pattern_type,
                    argument_type,
                    parameter_template->parameters,
                    deduced_arguments,
                    TemplateTypeDeductionMode::PartialOrdering)) {
                return false;
            }
        }

        for (size_t idx = 0; idx < deduced_arguments.size(); ++idx) {
            if (deduced_arguments[idx].is_unbound()) {
                const auto* parameter = parameter_template->parameters[idx].get();
                if (parameter && parameter->is_parameter_pack) {
                    deduced_arguments[idx] = TemplateArgumentBinding::pack({});
                    continue;
                }
                return false;
            }
        }
        return true;
    };

    bool lhs_at_least_as =
        template_is_at_least_as_specialized_as(rhs_template, lhs_template);
    bool rhs_at_least_as =
        template_is_at_least_as_specialized_as(lhs_template, rhs_template);

    if (lhs_at_least_as && !rhs_at_least_as) {
        return TemplatePartialOrderingResult::LhsMoreSpecialized;
    }
    if (rhs_at_least_as && !lhs_at_least_as) {
        return TemplatePartialOrderingResult::RhsMoreSpecialized;
    }
    if (lhs_at_least_as && rhs_at_least_as) {
        return TemplatePartialOrderingResult::Equivalent;
    }
    return TemplatePartialOrderingResult::Unordered;
}

bool Collect::is_function_template_more_specialized(
    const FunctionTemplateDecl* lhs_template,
    const FunctionTemplateDecl* rhs_template) const {
    return compare_function_template_partial_ordering(lhs_template, rhs_template) ==
        TemplatePartialOrderingResult::LhsMoreSpecialized;
}
