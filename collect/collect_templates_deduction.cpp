#include "collect_templates_internal.h"

#include <functional>
#include <unordered_set>

namespace {

enum class TemplateTypeDeductionMode : uint8_t {
    Call,
    PartialOrdering,
};

enum class TemplateArgumentDeductionResult : uint8_t {
    Match,
    Mismatch,
    NonDeduced,
};

bool deduce_function_template_argument_types(
    QualType pattern_type,
    QualType argument_type,
    const TemplateParameterList& parameters,
    TemplateArgumentBindings& deduced_arguments,
    bool argument_is_lvalue = false);

bool deduce_template_argument_types_impl(
    QualType pattern_type,
    QualType argument_type,
    const TemplateParameterList& parameters,
    TemplateArgumentBindings& deduced_arguments,
    TemplateTypeDeductionMode deduction_mode,
    bool argument_is_lvalue = false);

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

bool deduced_type_arguments_match(QualType existing_type, QualType deduced_type) {
    if (!existing_type || !deduced_type) {
        return existing_type.equals_qualified(deduced_type);
    }
    if (existing_type.equals_qualified(deduced_type)) {
        return true;
    }

    // Repeated deductions must name the same type; substituted dependent
    // aliases may only become comparable after side-table-backed desugaring.
    auto existing_canonical = desugar_type(existing_type);
    auto deduced_canonical = desugar_type(deduced_type);
    return existing_canonical && deduced_canonical &&
           existing_canonical.equals_qualified(deduced_canonical);
}

struct TemplateSpecializationMatchInfo {
    const Decl* primary_template = nullptr;
    std::string_view template_name;
    std::vector<TemplateArgument> arguments;
};

struct TemplatePatternLayout {
    size_t element_count = 0;
    std::optional<size_t> pack_index;
    size_t leading_count = 0;
    size_t trailing_count = 0;
    bool valid = true;

    size_t fixed_count() const {
        return leading_count + trailing_count;
    }
};

struct FunctionParameterLayout {
    size_t parameter_count = 0;
    std::optional<size_t> pack_index;
    size_t leading_count = 0;
    size_t trailing_count = 0;
    bool valid = true;

    size_t fixed_count() const {
        return leading_count + trailing_count;
    }
};

std::optional<TemplateSpecializationMatchInfo> extract_template_specialization_match_info(
    QualType type) {
    auto canonical_type = desugar_type(type);
    auto object = canonical_type.as_shared<ObjectType>();
    if (object && object->is_class_template_specialization()) {
        std::string_view template_name;
        if (auto* primary_template = object->get_primary_class_template()) {
            if (auto* record = primary_template->record_decl()) {
                template_name = record->name;
            }
        }
        return TemplateSpecializationMatchInfo{
            object->get_primary_class_template(),
            template_name,
            object->get_template_specialization_arguments()};
    }

    auto spelled = desugar_typedefs(type);
    auto raw = spelled.get_shared();
    if (!raw) {
        return std::nullopt;
    }

    if (auto specialization = dyn_cast_shared<TemplateSpecializationType>(raw)) {
        std::vector<TemplateArgument> arguments = specialization->arguments;
        if (auto* class_template = dyn_cast<ClassTemplateDecl>(
                const_cast<Decl*>(specialization->primary_template))) {
            TemplateArgumentBindings bindings;
            if (bind_explicit_template_arguments_prefix_to_parameters(
                    class_template->parameters,
                    specialization->arguments,
                    bindings,
                    nullptr) &&
                complete_template_argument_bindings_with_defaults(
                    class_template,
                    bindings,
                    nullptr)) {
                arguments = flatten_template_argument_bindings(bindings);
            }
        }
        return TemplateSpecializationMatchInfo{
            specialization->primary_template,
            specialization->template_name,
            std::move(arguments)};
    }

    object = desugar_type(spelled).as_shared<ObjectType>();
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
        object->get_template_specialization_arguments()};
}

TemplatePatternLayout analyze_template_argument_pattern_layout(
    const std::vector<TemplateArgument>& arguments) {
    TemplatePatternLayout layout;
    layout.element_count = arguments.size();
    size_t pack_count = 0;
    for (size_t idx = 0; idx < arguments.size(); ++idx) {
        if (!arguments[idx].expands_parameter_pack) {
            continue;
        }
        ++pack_count;
        layout.pack_index = idx;
    }
    if (pack_count > 1) {
        layout.valid = false;
        return layout;
    }
    if (layout.pack_index.has_value()) {
        layout.leading_count = *layout.pack_index;
        layout.trailing_count = arguments.size() - *layout.pack_index - 1;
    }
    return layout;
}

FunctionParameterLayout analyze_function_parameter_layout(const FuncDecl* pattern) {
    FunctionParameterLayout layout;
    if (!pattern) {
        layout.valid = false;
        return layout;
    }

    auto function_type =
        desugar_type(QualType(pattern->type)).as_shared<FunctionType>();
    bool has_void_param = function_type &&
        function_type->parameters.size() == 1 &&
        function_type->parameters[0]->isVoid();
    layout.parameter_count = has_void_param ? 0 : pattern->parameters.size();

    size_t pack_count = 0;
    for (size_t idx = 0; idx < layout.parameter_count; ++idx) {
        auto* param_decl = dyn_cast<ParamDecl>(pattern->parameters[idx].get());
        if (!param_decl || !param_decl->is_parameter_pack) {
            continue;
        }
        ++pack_count;
        layout.pack_index = idx;
    }
    if (pack_count > 1) {
        layout.valid = false;
        return layout;
    }
    if (layout.pack_index.has_value()) {
        layout.leading_count = *layout.pack_index;
        layout.trailing_count = layout.parameter_count - *layout.pack_index - 1;
    }
    return layout;
}

bool finalize_deduced_template_bindings(const TemplateParameterList& parameters,
                                        TemplateArgumentBindings& deduced_arguments) {
    for (size_t idx = 0; idx < deduced_arguments.size(); ++idx) {
        if (!deduced_arguments[idx].is_unbound()) {
            continue;
        }
        const auto* parameter = idx < parameters.size() ? parameters[idx].get() : nullptr;
        if (parameter && parameter->is_parameter_pack) {
            deduced_arguments[idx] = TemplateArgumentBinding::pack({});
            continue;
        }
        return false;
    }
    return true;
}

TemplateArgument make_partial_ordering_unique_type_argument(size_t ordinal) {
    auto unique_type = std::make_shared<ObjectType>(
        "__aburi_partial_ordering_" + std::to_string(ordinal),
        false,
        true);
    return TemplateArgument(QualType(unique_type));
}

TemplateArgument make_partial_ordering_pack_placeholder_argument(
    const TemplateParameterDecl* parameter,
    size_t ordinal) {
    if (!parameter) {
        return TemplateArgument();
    }
    if (auto* type_parameter = dyn_cast<TemplateTypeParmDecl>(
            const_cast<TemplateParameterDecl*>(parameter))) {
        (void)type_parameter;
        return make_partial_ordering_unique_type_argument(ordinal);
    }
    if (auto* non_type_parameter = dyn_cast<TemplateNonTypeParmDecl>(
            const_cast<TemplateParameterDecl*>(parameter))) {
        return TemplateArgument::dependent_value_argument(
            non_type_parameter->type,
            nullptr,
            non_type_parameter->get_name(),
            non_type_parameter);
    }
    if (auto* template_parameter = dyn_cast<TemplateTemplateParmDecl>(
            const_cast<TemplateParameterDecl*>(parameter))) {
        return TemplateArgument::dependent_template_argument(
            template_parameter->get_name(),
            template_parameter);
    }
    return TemplateArgument();
}

bool build_partial_ordering_transformed_bindings(
    const TemplateParameterList& parameters,
    size_t pack_arity,
    TemplateArgumentBindings& transformed_bindings_out) {
    transformed_bindings_out.clear();
    transformed_bindings_out.resize(parameters.size());

    size_t unique_type_ordinal = 0;
    for (size_t idx = 0; idx < parameters.size(); ++idx) {
        const auto* parameter = parameters[idx].get();
        if (!parameter) {
            return false;
        }

        if (!parameter->is_parameter_pack) {
            if (isa<TemplateTypeParmDecl>(parameter)) {
                transformed_bindings_out[idx] = TemplateArgumentBinding::single(
                    make_partial_ordering_unique_type_argument(
                        unique_type_ordinal++));
            }
            continue;
        }

        std::vector<TemplateArgument> pack_arguments;
        pack_arguments.reserve(pack_arity);
        for (size_t element_index = 0; element_index < pack_arity; ++element_index) {
            pack_arguments.push_back(
                make_partial_ordering_pack_placeholder_argument(
                    parameter,
                    unique_type_ordinal++));
        }
        transformed_bindings_out[idx] =
            TemplateArgumentBinding::pack(std::move(pack_arguments));
    }
    return true;
}

bool bind_deduced_template_argument_value(
    const TemplateParameterDecl* parameter,
    const TemplateArgument& argument,
    const TemplateParameterList& parameters,
    TemplateArgumentBindings& deduced_arguments) {
    auto parameter_index = collect_template_internal::find_template_parameter_index_by_decl(
        parameter,
        parameters);
    if (!parameter_index || *parameter_index >= deduced_arguments.size()) {
        return false;
    }

    TemplateArgument deduced_argument = argument;
    // A deduced argument may contain nested defaults from the argument type
    // itself, but this binding was not supplied by the function template's
    // own default argument.
    deduced_argument.is_defaulted = false;

    auto& existing = deduced_arguments[*parameter_index];
    if (parameter->is_parameter_pack) {
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
    return existing_single && existing_single->equals(deduced_argument);
}

const Expr* strip_array_bound_deduction_expr(const Expr* expr) {
    while (expr) {
        if (auto* cast = dyn_cast<ImplicitCast>(expr)) {
            expr = cast->expr.get();
            continue;
        }
        if (auto* paren = dyn_cast<ParenExpr>(expr)) {
            expr = paren->subexpr.get();
            continue;
        }
        break;
    }
    return expr;
}

const TemplateNonTypeParmDecl* direct_non_type_template_parameter_bound(
    const Expr* expr) {
    expr = strip_array_bound_deduction_expr(expr);
    auto* var_ref = dyn_cast<VarRef>(expr);
    if (!var_ref || !var_ref->symref) {
        return nullptr;
    }
    return dyn_cast<TemplateNonTypeParmDecl>(
        const_cast<TemplateParameterDecl*>(
            var_ref->symref->template_parameter_decl));
}

bool deduce_array_bound_template_argument(
    const ArrayType& pattern_array,
    const ArrayType& argument_array,
    const TemplateParameterList& parameters,
    TemplateArgumentBindings& deduced_arguments) {
    if (pattern_array.size_kind == ArraySizeKind::Incomplete) {
        return true;
    }

    if (pattern_array.size_kind == ArraySizeKind::Constant) {
        return argument_array.size_kind == ArraySizeKind::Constant &&
               pattern_array.size == argument_array.size;
    }

    if (pattern_array.size_kind != ArraySizeKind::Variable ||
        !pattern_array.size_expr) {
        return argument_array.size_kind == pattern_array.size_kind;
    }

    const auto* bound_parameter =
        direct_non_type_template_parameter_bound(pattern_array.size_expr.get());
    if (!bound_parameter) {
        return argument_array.size_kind == pattern_array.size_kind;
    }
    if (argument_array.size_kind != ArraySizeKind::Constant ||
        !argument_array.size.has_value()) {
        return false;
    }

    TemplateArgument bound_argument = TemplateArgument::value_argument(
        bound_parameter->type,
        ConstValue::integer(
            ConstIntValue::from_unsigned(*argument_array.size, 64)),
        std::to_string(*argument_array.size));
    if (!collect_template_internal::normalize_concrete_template_value_argument(
            bound_argument,
            bound_parameter->type,
            nullptr)) {
        return false;
    }
    return bind_deduced_template_argument_value(
        bound_parameter,
        bound_argument,
        parameters,
        deduced_arguments);
}

TemplateArgument materialize_template_argument_pack_element(
    const TemplateArgument& argument) {
    TemplateArgument element_argument = argument;
    element_argument.expands_parameter_pack = false;
    element_argument.pack_expansion_parameters.clear();
    return element_argument;
}

bool partial_specialization_deduction_can_continue(
    TemplateArgumentDeductionResult result) {
    return result != TemplateArgumentDeductionResult::Mismatch;
}

TemplateArgumentDeductionResult deduce_class_template_argument_binding(
    const TemplateArgument& pattern_argument,
    const TemplateArgument& argument_argument,
    const TemplateParameterList& parameters,
    TemplateArgumentBindings& deduced_bindings) {
    if (pattern_argument.kind != argument_argument.kind) {
        return TemplateArgumentDeductionResult::Mismatch;
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
                return TemplateArgumentDeductionResult::Mismatch;
            }
        }
        if (!type_depends_on_template_parameters(pattern_argument.type)) {
            return desugar_type(pattern_argument.type).equals_qualified(
                       desugar_type(argument_argument.type))
                ? TemplateArgumentDeductionResult::Match
                : TemplateArgumentDeductionResult::Mismatch;
        }
        return deduce_template_argument_types_impl(
                   pattern_argument.type,
                   argument_argument.type,
                   parameters,
                   deduced_bindings,
                   TemplateTypeDeductionMode::PartialOrdering)
            ? TemplateArgumentDeductionResult::Match
            : TemplateArgumentDeductionResult::Mismatch;
    }

    if (pattern_argument.is_dependent &&
        pattern_argument.referenced_parameter) {
        return bind_deduced_template_argument_value(
                   pattern_argument.referenced_parameter,
                   argument_argument,
                   parameters,
                   deduced_bindings)
            ? TemplateArgumentDeductionResult::Match
            : TemplateArgumentDeductionResult::Mismatch;
    }

    if (pattern_argument.is_dependent) {
        return TemplateArgumentDeductionResult::NonDeduced;
    }

    TemplateArgument normalized_pattern = pattern_argument;
    TemplateArgument normalized_argument = argument_argument;
    QualType target_type = normalized_argument.value_type
        ? normalized_argument.value_type
        : normalized_pattern.value_type;
    bool arguments_match =
        collect_template_internal::normalize_concrete_template_value_argument(
            normalized_pattern,
            target_type,
            nullptr) &&
        collect_template_internal::normalize_concrete_template_value_argument(
            normalized_argument,
            target_type,
            nullptr) &&
        normalized_pattern.equals(normalized_argument);
    return arguments_match
        ? TemplateArgumentDeductionResult::Match
        : TemplateArgumentDeductionResult::Mismatch;
}

bool deduce_class_template_specialization_argument_list_into_existing_bindings(
    const std::vector<TemplateArgument>& pattern_arguments,
    const TemplatePatternLayout& pattern_layout,
    const TemplateParameterList& parameters,
    const std::vector<TemplateArgument>& actual_arguments,
    TemplateArgumentBindings& deduced_bindings,
    bool finalize_bindings) {
    if (!pattern_layout.valid) {
        return false;
    }
    if (deduced_bindings.size() < parameters.size()) {
        return false;
    }

    if (!pattern_layout.pack_index.has_value()) {
        if (pattern_arguments.size() != actual_arguments.size()) {
            return false;
        }
    } else if (actual_arguments.size() < pattern_layout.fixed_count()) {
        return false;
    }

    if (!pattern_layout.pack_index.has_value()) {
        for (size_t idx = 0; idx < pattern_arguments.size(); ++idx) {
            if (!partial_specialization_deduction_can_continue(
                    deduce_class_template_argument_binding(
                        pattern_arguments[idx],
                        actual_arguments[idx],
                        parameters,
                        deduced_bindings))) {
                return false;
            }
        }
        return !finalize_bindings ||
            finalize_deduced_template_bindings(parameters, deduced_bindings);
    }

    for (size_t idx = 0; idx < pattern_layout.leading_count; ++idx) {
        if (!partial_specialization_deduction_can_continue(
                deduce_class_template_argument_binding(
                    pattern_arguments[idx],
                    actual_arguments[idx],
                    parameters,
                    deduced_bindings))) {
            return false;
        }
    }

    if (pattern_layout.pack_index.has_value()) {
        const size_t pack_argument_count =
            actual_arguments.size() - pattern_layout.fixed_count();
        TemplateArgument pack_pattern_argument =
            materialize_template_argument_pack_element(
                pattern_arguments[*pattern_layout.pack_index]);
        for (size_t idx = 0; idx < pack_argument_count; ++idx) {
            if (!partial_specialization_deduction_can_continue(
                    deduce_class_template_argument_binding(
                        pack_pattern_argument,
                        actual_arguments[pattern_layout.leading_count + idx],
                        parameters,
                        deduced_bindings))) {
                return false;
            }
        }
    }

    for (size_t idx = 0; idx < pattern_layout.trailing_count; ++idx) {
        const size_t pattern_index =
            pattern_arguments.size() - pattern_layout.trailing_count + idx;
        const size_t argument_index =
            actual_arguments.size() - pattern_layout.trailing_count + idx;
        if (!partial_specialization_deduction_can_continue(
                deduce_class_template_argument_binding(
                    pattern_arguments[pattern_index],
                    actual_arguments[argument_index],
                    parameters,
                    deduced_bindings))) {
            return false;
        }
    }

    return !finalize_bindings ||
        finalize_deduced_template_bindings(parameters, deduced_bindings);
}

bool deduce_class_template_specialization_argument_list(
    const std::vector<TemplateArgument>& pattern_arguments,
    const TemplatePatternLayout& pattern_layout,
    const TemplateParameterList& parameters,
    const std::vector<TemplateArgument>& actual_arguments,
    TemplateArgumentBindings& deduced_bindings_out) {
    deduced_bindings_out.clear();
    deduced_bindings_out.resize(parameters.size());
    return deduce_class_template_specialization_argument_list_into_existing_bindings(
        pattern_arguments,
        pattern_layout,
        parameters,
        actual_arguments,
        deduced_bindings_out,
        true);
}

bool expand_partial_specialization_argument_pattern(
    const std::vector<TemplateArgument>& pattern_arguments,
    const TemplatePatternLayout& pattern_layout,
    size_t target_argument_count,
    std::vector<TemplateArgument>& expanded_arguments_out) {
    expanded_arguments_out.clear();
    if (!pattern_layout.valid) {
        return false;
    }
    if (!pattern_layout.pack_index.has_value()) {
        if (pattern_arguments.size() != target_argument_count) {
            return false;
        }
        expanded_arguments_out = pattern_arguments;
        return true;
    }
    if (target_argument_count < pattern_layout.fixed_count()) {
        return false;
    }

    const size_t pack_argument_count =
        target_argument_count - pattern_layout.fixed_count();
    expanded_arguments_out.reserve(target_argument_count);
    for (size_t idx = 0; idx < pattern_layout.leading_count; ++idx) {
        expanded_arguments_out.push_back(pattern_arguments[idx]);
    }

    TemplateArgument pack_pattern_argument =
        materialize_template_argument_pack_element(
            pattern_arguments[*pattern_layout.pack_index]);
    for (size_t idx = 0; idx < pack_argument_count; ++idx) {
        expanded_arguments_out.push_back(pack_pattern_argument);
    }

    for (size_t idx = 0; idx < pattern_layout.trailing_count; ++idx) {
        expanded_arguments_out.push_back(
            pattern_arguments[pattern_arguments.size() -
                              pattern_layout.trailing_count + idx]);
    }
    return true;
}

bool complete_partial_specialization_primary_arguments(
    Collect& collect,
    const TemplateDecl* primary_template,
    const std::vector<TemplateArgument>& written_arguments,
    SrcLoc loc,
    std::vector<TemplateArgument>& completed_arguments_out) {
    std::string binding_error;
    return collect.complete_partial_specialization_primary_arguments(
        primary_template,
        written_arguments,
        loc,
        completed_arguments_out,
        &binding_error);
}

std::vector<TemplateArgument> normalize_actual_arguments_for_partial_matching(
    Collect& collect,
    const std::vector<TemplateArgument>& actual_arguments,
    SrcLoc loc) {
    std::vector<TemplateArgument> normalized_arguments = actual_arguments;
    for (auto& argument : normalized_arguments) {
        if (argument.kind != TemplateArgumentKind::Type || !argument.type) {
            continue;
        }
        QualType realized_type =
            collect.collect_try_realize_deferred_semantic_type(argument.type);
        if (!realized_type) {
            continue;
        }
        QualType canonical_type = desugar_type(realized_type);
        argument.type = canonical_type ? canonical_type : realized_type;
        argument.is_dependent =
            type_depends_on_template_parameters(argument.type);
    }
    return normalized_arguments;
}

bool substituted_partial_specialization_arguments_match_actual(
    Collect& collect,
    const std::vector<TemplateArgument>& pattern_arguments,
    const TemplateParameterList& parameters,
    const TemplateArgumentBindings& deduced_bindings,
    const std::vector<TemplateArgument>& actual_arguments,
    SrcLoc loc) {
    auto diagnostic_checkpoint = collect.collect_diagnostic_checkpoint();
    Collect::UnevaluatedContextScope unevaluated_context(
        &collect,
        "partial specialization validation");
    Collect::FunctionTemplateRequirementNoteSuppressionScope
        suppress_requirement_notes(&collect);
    auto substituted_arguments =
        collect.collect_substitute_template_arguments_with_bindings(
            pattern_arguments,
            parameters,
            deduced_bindings,
            loc);
    bool substitution_reported_diagnostic =
        collect.collect_diagnostics_changed_since(diagnostic_checkpoint);
    collect.collect_restore_diagnostic_checkpoint(diagnostic_checkpoint);
    if (substitution_reported_diagnostic) {
        return false;
    }

    if (substituted_arguments.size() != actual_arguments.size()) {
        return false;
    }

    for (size_t idx = 0; idx < substituted_arguments.size(); ++idx) {
        const auto& substituted = substituted_arguments[idx];
        const auto& actual = actual_arguments[idx];
        if (substituted.kind != actual.kind) {
            return false;
        }

        if (substituted.kind == TemplateArgumentKind::Type) {
            QualType substituted_type =
                collect.collect_try_realize_deferred_semantic_type(
                    substituted.type);
            QualType actual_type =
                collect.collect_try_realize_deferred_semantic_type(
                    actual.type);
            if (!desugar_type(substituted_type).equals_qualified(
                    desugar_type(actual_type))) {
                return false;
            }
            continue;
        }

        TemplateArgument normalized_substituted = substituted;
        TemplateArgument normalized_actual = actual;
        QualType target_type = normalized_actual.value_type
            ? normalized_actual.value_type
            : normalized_substituted.value_type;
        if (!collect_template_internal::normalize_concrete_template_value_argument(
                normalized_substituted,
                target_type,
                nullptr) ||
            !collect_template_internal::normalize_concrete_template_value_argument(
                normalized_actual,
                target_type,
                nullptr) ||
            !normalized_substituted.equals(normalized_actual)) {
            return false;
        }
    }
    return true;
}

int compare_pack_layout_specificity(const TemplatePatternLayout& lhs,
                                    const TemplatePatternLayout& rhs) {
    if (lhs.pack_index.has_value() != rhs.pack_index.has_value()) {
        return lhs.pack_index.has_value() ? -1 : 1;
    }
    if (!lhs.pack_index.has_value()) {
        return 0;
    }
    if (lhs.fixed_count() != rhs.fixed_count()) {
        return lhs.fixed_count() > rhs.fixed_count() ? 1 : -1;
    }
    return 0;
}

int compare_pack_layout_specificity(const FunctionParameterLayout& lhs,
                                    const FunctionParameterLayout& rhs) {
    if (lhs.pack_index.has_value() != rhs.pack_index.has_value()) {
        return lhs.pack_index.has_value() ? -1 : 1;
    }
    if (!lhs.pack_index.has_value()) {
        return 0;
    }
    if (lhs.fixed_count() != rhs.fixed_count()) {
        return lhs.fixed_count() > rhs.fixed_count() ? 1 : -1;
    }
    return 0;
}

template <typename CompleteBindings>
bool function_template_is_at_least_as_specialized_as(
    const FunctionTemplateDecl* parameter_template,
    const FunctionParameterLayout& parameter_layout,
    const std::vector<QualType>& transformed_argument_types,
    CompleteBindings&& complete_bindings) {
    if (!parameter_template) {
        return false;
    }

    const auto* parameter_pattern = parameter_template->function_decl();
    if (!parameter_pattern || !parameter_layout.valid) {
        return false;
    }

    TemplateArgumentBindings deduced_arguments(
        parameter_template->parameters.size());

    auto deduce_one_parameter =
        [&](size_t parameter_index, size_t argument_index) -> bool {
        auto* parameter_decl = dyn_cast<ParamDecl>(
            parameter_pattern->parameters[parameter_index].get());
        if (!parameter_decl || argument_index >= transformed_argument_types.size()) {
            return false;
        }
        return deduce_template_argument_types_impl(
            parameter_decl->type,
            transformed_argument_types[argument_index],
            parameter_template->parameters,
            deduced_arguments,
            TemplateTypeDeductionMode::PartialOrdering);
    };

    if (!parameter_layout.pack_index.has_value()) {
        if (transformed_argument_types.size() != parameter_layout.parameter_count) {
            return false;
        }
        for (size_t idx = 0; idx < parameter_layout.parameter_count; ++idx) {
            if (!deduce_one_parameter(idx, idx)) {
                return false;
            }
        }
    } else {
        if (transformed_argument_types.size() < parameter_layout.fixed_count()) {
            return false;
        }
        for (size_t idx = 0; idx < parameter_layout.leading_count; ++idx) {
            if (!deduce_one_parameter(idx, idx)) {
                return false;
            }
        }

        const size_t pack_argument_count =
            transformed_argument_types.size() - parameter_layout.fixed_count();
        for (size_t idx = 0; idx < pack_argument_count; ++idx) {
            if (!deduce_one_parameter(
                    *parameter_layout.pack_index,
                    parameter_layout.leading_count + idx)) {
                return false;
            }
        }

        for (size_t idx = 0; idx < parameter_layout.trailing_count; ++idx) {
            const size_t parameter_index =
                parameter_layout.parameter_count - parameter_layout.trailing_count +
                idx;
            const size_t argument_index =
                transformed_argument_types.size() -
                parameter_layout.trailing_count + idx;
            if (!deduce_one_parameter(parameter_index, argument_index)) {
                return false;
            }
        }
    }

    return complete_bindings(
        parameter_template,
        deduced_arguments,
        parameter_pattern->location);
}

bool bind_deduced_template_argument(
    QualType pattern_type,
    const TemplateTypeParmType* parm_type,
    QualType argument_type,
    const TemplateParameterList& parameters,
    TemplateArgumentBindings& deduced_arguments,
    TemplateTypeDeductionMode deduction_mode) {
    auto index = find_template_parameter_index(parm_type, parameters);
    if (!index.has_value() || *index >= deduced_arguments.size()) {
        return false;
    }

    auto deduced_type = desugar_typedefs(argument_type);
    if (pattern_type.get_qualifiers() != QUAL_NONE) {
        if (deduction_mode != TemplateTypeDeductionMode::Call &&
            (deduced_type.get_qualifiers() & pattern_type.get_qualifiers()) !=
                pattern_type.get_qualifiers()) {
            return false;
        }
        // Function-call deduction should bind through qualifiers written around
        // the template parameter itself. For shapes like `const T*` against
        // `int*` or `const int*`, bind `T` to `int`.
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
           deduced_type_arguments_match(existing_single->type, deduced_type);
}

bool bind_deduced_template_template_argument(
    const TemplateTemplateParmDecl* parameter_decl,
    const Decl* argument_template_decl,
    const TemplateParameterList& parameters,
    TemplateArgumentBindings& deduced_arguments) {
    if (!parameter_decl || !argument_template_decl) {
        return false;
    }

    auto parameter_index = collect_template_internal::find_template_parameter_index_by_decl(
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

const ObjectDecl* canonical_record_decl_for_template_deduction(
    const ObjectDecl* decl) {
    if (!decl) {
        return nullptr;
    }
    if (auto record_type = decl->get_record_type()) {
        if (auto* canonical_decl =
                dyn_cast<ObjectDecl>(record_type->get_decl())) {
            return canonical_decl;
        }
    }
    return decl;
}

const ObjectDecl* record_decl_from_template_deduction_type(QualType type) {
    auto object_type = desugar_type(type).as_shared<ObjectType>();
    return object_type
        ? canonical_record_decl_for_template_deduction(
              dyn_cast<ObjectDecl>(object_type->get_decl()))
        : nullptr;
}

bool template_argument_bindings_equal(const TemplateArgumentBindings& lhs,
                                      const TemplateArgumentBindings& rhs) {
    if (lhs.size() != rhs.size()) {
        return false;
    }
    for (size_t idx = 0; idx < lhs.size(); ++idx) {
        if (!lhs[idx].equals(rhs[idx])) {
            return false;
        }
    }
    return true;
}

bool deduce_class_template_specialization_match_into_bindings(
    const TemplateSpecializationType& pattern_specialization,
    const TemplateSpecializationMatchInfo& argument_specialization,
    const TemplateParameterList& parameters,
    TemplateArgumentBindings& deduced_bindings) {
    TemplateArgumentBindings candidate_bindings = deduced_bindings;
    if (auto* pattern_template_parameter = dyn_cast<TemplateTemplateParmDecl>(
            const_cast<Decl*>(pattern_specialization.primary_template))) {
        if (!bind_deduced_template_template_argument(
                pattern_template_parameter,
                argument_specialization.primary_template,
                parameters,
                candidate_bindings)) {
            return false;
        }
    } else {
        if (pattern_specialization.primary_template &&
            argument_specialization.primary_template &&
            !template_decls_share_lookup_identity(
                pattern_specialization.primary_template,
                argument_specialization.primary_template)) {
            return false;
        }
        if ((!pattern_specialization.primary_template ||
             !argument_specialization.primary_template) &&
            pattern_specialization.template_name !=
                argument_specialization.template_name) {
            return false;
        }
    }

    TemplatePatternLayout pattern_layout =
        analyze_template_argument_pattern_layout(
            pattern_specialization.arguments);
    if (!deduce_class_template_specialization_argument_list_into_existing_bindings(
            pattern_specialization.arguments,
            pattern_layout,
            parameters,
            argument_specialization.arguments,
            candidate_bindings,
            false)) {
        return false;
    }

    deduced_bindings = std::move(candidate_bindings);
    return true;
}

bool deduce_class_template_specialization_from_base_classes(
    const TemplateSpecializationType& pattern_specialization,
    QualType argument_type,
    const TemplateParameterList& parameters,
    TemplateArgumentBindings& deduced_bindings) {
    const ObjectDecl* argument_decl =
        record_decl_from_template_deduction_type(argument_type);
    if (!argument_decl) {
        return false;
    }

    std::optional<TemplateArgumentBindings> matched_bindings;
    bool saw_conflicting_match = false;
    std::unordered_set<const ObjectDecl*> active_stack;
    active_stack.insert(argument_decl);

    std::function<void(const ObjectDecl*)> walk =
        [&](const ObjectDecl* current_decl) {
        current_decl = canonical_record_decl_for_template_deduction(current_decl);
        if (!current_decl || saw_conflicting_match) {
            return;
        }

        const RecordSemanticState* state =
            record_semantics_cache_lookup(current_decl);
        if (!state) {
            return;
        }

        for (const auto& base : state->bases) {
            const ObjectDecl* base_decl =
                canonical_record_decl_for_template_deduction(base.record_decl);
            if (!base_decl) {
                base_decl = record_decl_from_template_deduction_type(base.type);
            }
            if (!base_decl || active_stack.contains(base_decl)) {
                continue;
            }

            if (auto base_specialization =
                    extract_template_specialization_match_info(base.type)) {
                TemplateArgumentBindings candidate_bindings = deduced_bindings;
                if (deduce_class_template_specialization_match_into_bindings(
                        pattern_specialization,
                        *base_specialization,
                        parameters,
                        candidate_bindings)) {
                    if (!matched_bindings.has_value()) {
                        matched_bindings = std::move(candidate_bindings);
                    } else if (!template_argument_bindings_equal(
                                   *matched_bindings,
                                   candidate_bindings)) {
                        saw_conflicting_match = true;
                        return;
                    }
                }
            }

            active_stack.insert(base_decl);
            walk(base_decl);
            active_stack.erase(base_decl);
        }
    };

    walk(argument_decl);
    if (!matched_bindings.has_value() || saw_conflicting_match) {
        return false;
    }
    deduced_bindings = std::move(*matched_bindings);
    return true;
}

bool deduce_template_argument_types_impl(
    QualType pattern_type,
    QualType argument_type,
    const TemplateParameterList& parameters,
    TemplateArgumentBindings& deduced_arguments,
    TemplateTypeDeductionMode deduction_mode,
    bool argument_is_lvalue) {
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

    if (deduction_mode == TemplateTypeDeductionMode::PartialOrdering &&
        isa<DecltypeExprType>(pattern_raw.get())) {
        return true;
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
                resolved_type,
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
            deduced_arguments,
            deduction_mode);
    }

    auto spelled_argument = desugar_typedefs(argument_type);
    if (deduction_mode != TemplateTypeDeductionMode::Call &&
        spelled_pattern.get_qualifiers() != spelled_argument.get_qualifiers()) {
        return false;
    }
    spelled_pattern = strip_top_level_qualifiers(spelled_pattern);
    spelled_argument = strip_top_level_qualifiers(spelled_argument);
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
        if (!deduce_array_bound_template_argument(
                *pattern_array,
                *argument_array,
                parameters,
                deduced_arguments)) {
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
        if (argument_specialization.has_value()) {
            if (deduce_class_template_specialization_match_into_bindings(
                    *pattern_specialization,
                    *argument_specialization,
                    parameters,
                    deduced_arguments)) {
                return true;
            }
        } else {
            if (deduction_mode == TemplateTypeDeductionMode::PartialOrdering &&
                isa<AliasTemplateDecl>(
                    const_cast<Decl*>(
                        pattern_specialization->primary_template))) {
                return true;
            }
        }
        return deduction_mode == TemplateTypeDeductionMode::Call &&
            deduce_class_template_specialization_from_base_classes(
                *pattern_specialization,
                argument_type,
                parameters,
                deduced_arguments);
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
    bool argument_is_lvalue) {
    return deduce_template_argument_types_impl(
        pattern_type,
        argument_type,
        parameters,
        deduced_arguments,
        TemplateTypeDeductionMode::Call,
        argument_is_lvalue);
}

bool class_template_partial_specialization_is_at_least_as_specialized_as(
    Collect& collect,
    const ClassTemplatePartialSpecializationDecl* parameter_partial,
    const ClassTemplatePartialSpecializationDecl* argument_partial) {
    if (!parameter_partial || !argument_partial) {
        return false;
    }
    std::vector<TemplateArgument> parameter_arguments;
    std::vector<TemplateArgument> argument_arguments;
    if (!complete_partial_specialization_primary_arguments(
            collect,
            parameter_partial->primary_template(),
            parameter_partial->specialization_arguments,
            parameter_partial->location,
            parameter_arguments) ||
        !complete_partial_specialization_primary_arguments(
            collect,
            argument_partial->primary_template(),
            argument_partial->specialization_arguments,
            argument_partial->location,
            argument_arguments)) {
        return false;
    }
    TemplatePatternLayout parameter_layout =
        analyze_template_argument_pattern_layout(
            parameter_arguments);
    TemplatePatternLayout argument_layout =
        analyze_template_argument_pattern_layout(
            argument_arguments);
    if (!parameter_layout.valid || !argument_layout.valid) {
        return false;
    }

    size_t transformed_argument_count = 0;
    if (!argument_layout.pack_index.has_value()) {
        transformed_argument_count = argument_layout.element_count;
    } else if (!parameter_layout.pack_index.has_value()) {
        transformed_argument_count = parameter_layout.element_count;
    } else {
        transformed_argument_count =
            std::max(parameter_layout.fixed_count(), argument_layout.fixed_count()) + 1;
    }

    std::vector<TemplateArgument> transformed_argument_patterns;
    if (!expand_partial_specialization_argument_pattern(
            argument_arguments,
            argument_layout,
            transformed_argument_count,
            transformed_argument_patterns)) {
        return false;
    }

    TemplateArgumentBindings deduced_bindings;
    return deduce_class_template_specialization_argument_list(
        parameter_arguments,
        parameter_layout,
        parameter_partial->parameters,
        transformed_argument_patterns,
        deduced_bindings);
}

} // namespace

namespace collect_template_internal {

bool deduce_class_template_partial_specialization_bindings(
    Collect& collect,
    const ClassTemplatePartialSpecializationDecl* partial_specialization,
    const std::vector<TemplateArgument>& actual_arguments,
    TemplateArgumentBindings& deduced_bindings_out) {
    deduced_bindings_out.clear();
    if (!partial_specialization) {
        return false;
    }
    std::vector<TemplateArgument> pattern_arguments;
    if (!complete_partial_specialization_primary_arguments(
            collect,
            partial_specialization->primary_template(),
            partial_specialization->specialization_arguments,
            partial_specialization->location,
            pattern_arguments)) {
        return false;
    }
    TemplatePatternLayout pattern_layout =
        analyze_template_argument_pattern_layout(
            pattern_arguments);
    auto normalized_actual_arguments =
        normalize_actual_arguments_for_partial_matching(
            collect,
            actual_arguments,
            partial_specialization->location);
    deduced_bindings_out.clear();
    deduced_bindings_out.resize(partial_specialization->parameters.size());
    if (!deduce_class_template_specialization_argument_list_into_existing_bindings(
            pattern_arguments,
            pattern_layout,
            partial_specialization->parameters,
            normalized_actual_arguments,
            deduced_bindings_out,
            /*finalize_bindings=*/false) ||
        !finalize_deduced_template_bindings(
            partial_specialization->parameters,
            deduced_bindings_out)) {
        return false;
    }
    return substituted_partial_specialization_arguments_match_actual(
        collect,
        pattern_arguments,
        partial_specialization->parameters,
        deduced_bindings_out,
        normalized_actual_arguments,
        partial_specialization->location);
}

bool is_class_template_partial_specialization_more_specialized(
    Collect& collect,
    const ClassTemplatePartialSpecializationDecl* lhs_partial,
    const ClassTemplatePartialSpecializationDecl* rhs_partial) {
    if (!lhs_partial || !rhs_partial || lhs_partial == rhs_partial) {
        return false;
    }

    bool rhs_from_lhs =
        class_template_partial_specialization_is_at_least_as_specialized_as(
            collect,
            rhs_partial,
            lhs_partial);
    if (!rhs_from_lhs) {
        return false;
    }
    bool lhs_from_rhs =
        class_template_partial_specialization_is_at_least_as_specialized_as(
            collect,
            lhs_partial,
            rhs_partial);
    if (!lhs_from_rhs) {
        return true;
    }
    std::vector<TemplateArgument> lhs_arguments;
    std::vector<TemplateArgument> rhs_arguments;
    if (!complete_partial_specialization_primary_arguments(
            collect,
            lhs_partial->primary_template(),
            lhs_partial->specialization_arguments,
            lhs_partial->location,
            lhs_arguments) ||
        !complete_partial_specialization_primary_arguments(
            collect,
            rhs_partial->primary_template(),
            rhs_partial->specialization_arguments,
            rhs_partial->location,
            rhs_arguments)) {
        return false;
    }
    TemplatePatternLayout lhs_layout =
        analyze_template_argument_pattern_layout(
            lhs_arguments);
    TemplatePatternLayout rhs_layout =
        analyze_template_argument_pattern_layout(
            rhs_arguments);
    return compare_pack_layout_specificity(lhs_layout, rhs_layout) > 0;
}

bool deduce_variable_template_partial_specialization_bindings(
    Collect& collect,
    const VariableTemplatePartialSpecializationDecl* partial_specialization,
    const std::vector<TemplateArgument>& actual_arguments,
    TemplateArgumentBindings& deduced_bindings_out) {
    deduced_bindings_out.clear();
    if (!partial_specialization) {
        return false;
    }
    std::vector<TemplateArgument> pattern_arguments;
    if (!complete_partial_specialization_primary_arguments(
            collect,
            partial_specialization->primary_template(),
            partial_specialization->specialization_arguments,
            partial_specialization->location,
            pattern_arguments)) {
        return false;
    }
    TemplatePatternLayout pattern_layout =
        analyze_template_argument_pattern_layout(
            pattern_arguments);
    auto normalized_actual_arguments =
        normalize_actual_arguments_for_partial_matching(
            collect,
            actual_arguments,
            partial_specialization->location);
    deduced_bindings_out.clear();
    deduced_bindings_out.resize(partial_specialization->parameters.size());
    if (!deduce_class_template_specialization_argument_list_into_existing_bindings(
            pattern_arguments,
            pattern_layout,
            partial_specialization->parameters,
            normalized_actual_arguments,
            deduced_bindings_out,
            /*finalize_bindings=*/false) ||
        !finalize_deduced_template_bindings(
            partial_specialization->parameters,
            deduced_bindings_out)) {
        return false;
    }
    return substituted_partial_specialization_arguments_match_actual(
        collect,
        pattern_arguments,
        partial_specialization->parameters,
        deduced_bindings_out,
        normalized_actual_arguments,
        partial_specialization->location);
}

bool is_variable_template_partial_specialization_more_specialized(
    Collect& collect,
    const VariableTemplatePartialSpecializationDecl* lhs_partial,
    const VariableTemplatePartialSpecializationDecl* rhs_partial) {
    if (!lhs_partial || !rhs_partial || lhs_partial == rhs_partial) {
        return false;
    }

    auto variable_partial_is_at_least_as_specialized_as =
        [&collect](const VariableTemplatePartialSpecializationDecl* parameter_partial,
                   const VariableTemplatePartialSpecializationDecl* argument_partial)
        -> bool {
            if (!parameter_partial || !argument_partial) {
                return false;
            }
            std::vector<TemplateArgument> parameter_arguments;
            std::vector<TemplateArgument> argument_arguments;
            if (!complete_partial_specialization_primary_arguments(
                    collect,
                    parameter_partial->primary_template(),
                    parameter_partial->specialization_arguments,
                    parameter_partial->location,
                    parameter_arguments) ||
                !complete_partial_specialization_primary_arguments(
                    collect,
                    argument_partial->primary_template(),
                    argument_partial->specialization_arguments,
                    argument_partial->location,
                    argument_arguments)) {
                return false;
            }
            TemplatePatternLayout parameter_layout =
                analyze_template_argument_pattern_layout(
                    parameter_arguments);
            TemplatePatternLayout argument_layout =
                analyze_template_argument_pattern_layout(
                    argument_arguments);
            if (!parameter_layout.valid || !argument_layout.valid) {
                return false;
            }

            size_t transformed_argument_count = 0;
            if (!argument_layout.pack_index.has_value()) {
                transformed_argument_count = argument_layout.element_count;
            } else if (!parameter_layout.pack_index.has_value()) {
                transformed_argument_count = parameter_layout.element_count;
            } else {
                transformed_argument_count =
                    std::max(parameter_layout.fixed_count(),
                             argument_layout.fixed_count()) +
                    1;
            }

            std::vector<TemplateArgument> transformed_argument_patterns;
            if (!expand_partial_specialization_argument_pattern(
                    argument_arguments,
                    argument_layout,
                    transformed_argument_count,
                    transformed_argument_patterns)) {
                return false;
            }

            TemplateArgumentBindings deduced_bindings;
            return deduce_class_template_specialization_argument_list(
                parameter_arguments,
                parameter_layout,
                parameter_partial->parameters,
                transformed_argument_patterns,
                deduced_bindings);
        };

    bool rhs_from_lhs =
        variable_partial_is_at_least_as_specialized_as(rhs_partial, lhs_partial);
    if (!rhs_from_lhs) {
        return false;
    }
    bool lhs_from_rhs =
        variable_partial_is_at_least_as_specialized_as(lhs_partial, rhs_partial);
    if (!lhs_from_rhs) {
        return true;
    }
    std::vector<TemplateArgument> lhs_arguments;
    std::vector<TemplateArgument> rhs_arguments;
    if (!complete_partial_specialization_primary_arguments(
            collect,
            lhs_partial->primary_template(),
            lhs_partial->specialization_arguments,
            lhs_partial->location,
            lhs_arguments) ||
        !complete_partial_specialization_primary_arguments(
            collect,
            rhs_partial->primary_template(),
            rhs_partial->specialization_arguments,
            rhs_partial->location,
            rhs_arguments)) {
        return false;
    }
    TemplatePatternLayout lhs_layout =
        analyze_template_argument_pattern_layout(
            lhs_arguments);
    TemplatePatternLayout rhs_layout =
        analyze_template_argument_pattern_layout(
            rhs_arguments);
    return compare_pack_layout_specificity(lhs_layout, rhs_layout) > 0;
}

} // namespace collect_template_internal

bool Collect::deduce_function_template_call_arguments(
    const FunctionTemplateDecl* function_template,
    const std::vector<std::unique_ptr<Expr>>& call_args,
    std::vector<TemplateArgument>& deduced_arguments_out,
    const TemplateArgumentBindings* initial_bindings) {
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
    const TemplateArgumentBindings* initial_bindings) {
    deduced_arguments_out.clear();
    if (!function_template) {
        return false;
    }

    const auto* pattern = function_template->function_decl();
    if (!pattern) {
        return false;
    }
    // Member-template defaults can mention enclosing class template
    // parameters that are intentionally outside the function template's own
    // parameter list. Preserve those outer dependencies during call deduction.
    bool allow_unsubstituted_member_defaults =
        static_cast<bool>(get_func_decl_owner_record_type(pattern));

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
                    &default_error,
                    allow_unsubstituted_member_defaults)) {
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
    size_t implicit_object_parameter_count = 0;
    if (const auto* method_decl = dyn_cast<CppMethodDecl>(pattern);
        method_decl && method_decl->storage_class != StorageClass::STATIC) {
        implicit_object_parameter_count = 1;
    } else if (isa<CppConstructorDecl>(pattern)) {
        implicit_object_parameter_count = 1;
    }
    if (implicit_object_parameter_count != 0) {
        if (call_args.size() < implicit_object_parameter_count ||
            pattern->parameters.size() < implicit_object_parameter_count) {
            deduced_arguments_out.clear();
            return false;
        }
    }

    for (size_t idx = implicit_object_parameter_count;
         idx < pattern->parameters.size();
         ++idx) {
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

        bool deduced = deduce_function_template_argument_types(
            pattern_type,
            argument_type,
            function_template->parameters,
            deduced_arguments,
            argument_category == ValueCategory::LValue);
        return deduced;
    };

    if (!pack_param_index.has_value()) {
        size_t compare_count =
            std::min(call_args.size() - implicit_object_parameter_count,
                     pattern->parameters.size() - implicit_object_parameter_count);
        for (size_t idx = 0; idx < compare_count; ++idx) {
            if (!deduce_one_parameter(
                    implicit_object_parameter_count + idx,
                    implicit_object_parameter_count + idx)) {
                return false;
            }
        }
    } else {
        size_t leading_count = *pack_param_index - implicit_object_parameter_count;
        size_t trailing_count =
            pattern->parameters.size() - *pack_param_index - 1;
        if (call_args.size() - implicit_object_parameter_count <
            leading_count + trailing_count) {
            deduced_arguments_out.clear();
            return false;
        }
        for (size_t idx = 0; idx < leading_count; ++idx) {
            if (!deduce_one_parameter(
                    implicit_object_parameter_count + idx,
                    implicit_object_parameter_count + idx)) {
                return false;
            }
        }

        size_t pack_arg_count =
            call_args.size() - implicit_object_parameter_count -
            leading_count - trailing_count;
        for (size_t idx = 0; idx < pack_arg_count; ++idx) {
            if (!deduce_one_parameter(
                    *pack_param_index,
                    implicit_object_parameter_count + leading_count + idx)) {
                return false;
            }
        }

        for (size_t idx = 0; idx < trailing_count; ++idx) {
            size_t param_index = *pack_param_index + 1 + idx;
            size_t arg_index =
                implicit_object_parameter_count + leading_count +
                pack_arg_count + idx;
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
            &default_error,
            allow_unsubstituted_member_defaults)) {
        deduced_arguments_out.clear();
        return false;
    }
    deduced_arguments_out = flatten_template_argument_bindings(deduced_arguments);
    return true;
}

bool Collect::resolve_class_template_argument_deduction(
    const ClassTemplateDecl* class_template,
    const std::vector<Expr*>& init_args,
    bool,
    bool is_copy_initialization,
    SrcLoc loc,
    QualType& deduced_type_out) {
    deduced_type_out = QualType();
    if (!class_template) {
        return false;
    }

    struct DeductionGuideCandidateEval {
        const CppDeductionGuideDecl* guide = nullptr;
        QualType deduced_type = nullptr;
        std::shared_ptr<FunctionType> function_type = nullptr;
        std::vector<ImplicitConversionSequence> conversions;
        bool viable = false;
    };

    auto exact_match_subrank =
        [](const ImplicitConversionSequence& seq) -> int {
        if (seq.exact_subrank >= 0) {
            return seq.exact_subrank;
        }
        switch (seq.kind) {
            case ConversionSequenceKind::Identity:
                return 0;
            case ConversionSequenceKind::Qualification:
                return 1;
            default:
                return 2;
        }
    };

    auto is_better_candidate =
        [&](const DeductionGuideCandidateEval& lhs,
            const DeductionGuideCandidateEval& rhs) -> bool {
        bool strictly_better = false;
        size_t compare_count =
            std::min(lhs.conversions.size(), rhs.conversions.size());
        for (size_t idx = 0; idx < compare_count; ++idx) {
            int lhs_rank = static_cast<int>(lhs.conversions[idx].rank);
            int rhs_rank = static_cast<int>(rhs.conversions[idx].rank);
            if (lhs_rank > rhs_rank) {
                return false;
            }
            if (lhs_rank < rhs_rank) {
                strictly_better = true;
                continue;
            }
            if (lhs.conversions[idx].rank == ConversionSequenceRank::ExactMatch) {
                int lhs_subrank = exact_match_subrank(lhs.conversions[idx]);
                int rhs_subrank = exact_match_subrank(rhs.conversions[idx]);
                if (lhs_subrank > rhs_subrank) {
                    return false;
                }
                if (lhs_subrank < rhs_subrank) {
                    strictly_better = true;
                }
            }
        }
        return strictly_better;
    };

    auto select_best_candidate =
        [&](const std::vector<DeductionGuideCandidateEval>& evaluated,
            const std::vector<size_t>& viable_indices) -> std::optional<size_t> {
        std::optional<size_t> best_index;
        for (size_t idx : viable_indices) {
            bool better_than_all = true;
            for (size_t other : viable_indices) {
                if (idx == other) {
                    continue;
                }
                if (!is_better_candidate(evaluated[idx], evaluated[other])) {
                    better_than_all = false;
                    break;
                }
            }
            if (!better_than_all) {
                continue;
            }
            if (best_index.has_value()) {
                return std::nullopt;
            }
            best_index = idx;
        }
        return best_index;
    };

    auto deduce_guide_arguments =
        [&](const CppDeductionGuideDecl* guide,
            TemplateArgumentBindings& bindings_out) -> bool {
        if (!guide ||
            !guide->function_type ||
            guide->guide_parameters.size() !=
                guide->function_type->parameters.size()) {
            return false;
        }

        bindings_out = TemplateArgumentBindings(guide->parameters.size());
        std::optional<size_t> pack_param_index;
        for (size_t idx = 0; idx < guide->guide_parameters.size(); ++idx) {
            auto* param_decl =
                dyn_cast<ParamDecl>(guide->guide_parameters[idx].get());
            if (!param_decl || !param_decl->is_parameter_pack) {
                continue;
            }
            if (pack_param_index.has_value()) {
                return false;
            }
            pack_param_index = idx;
        }

        auto deduce_one_parameter =
            [&](size_t param_index, size_t arg_index) -> bool {
            if (param_index >= guide->guide_parameters.size() ||
                arg_index >= init_args.size()) {
                return false;
            }
            auto* param_decl =
                dyn_cast<ParamDecl>(guide->guide_parameters[param_index].get());
            Expr* init_arg = init_args[arg_index];
            if (!param_decl || !init_arg || !init_arg->get_type()) {
                return false;
            }

            QualType pattern_type = param_decl->type;
            QualType argument_type = init_arg->get_type();
            ValueCategory argument_category = classify_value_category(init_arg);
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
                guide->parameters,
                bindings_out,
                argument_category == ValueCategory::LValue);
        };

        if (!pack_param_index.has_value()) {
            if (guide->guide_parameters.size() != init_args.size()) {
                return false;
            }
            for (size_t idx = 0; idx < init_args.size(); ++idx) {
                if (!deduce_one_parameter(idx, idx)) {
                    return false;
                }
            }
        } else {
            size_t leading_count = *pack_param_index;
            size_t trailing_count =
                guide->guide_parameters.size() - *pack_param_index - 1;
            if (init_args.size() < leading_count + trailing_count) {
                return false;
            }
            for (size_t idx = 0; idx < leading_count; ++idx) {
                if (!deduce_one_parameter(idx, idx)) {
                    return false;
                }
            }
            size_t pack_arg_count =
                init_args.size() - leading_count - trailing_count;
            for (size_t idx = 0; idx < pack_arg_count; ++idx) {
                if (!deduce_one_parameter(
                        *pack_param_index,
                        leading_count + idx)) {
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
                guide,
                bindings_out,
                guide->location,
                &default_error)) {
            return false;
        }
        return are_template_constraints_satisfied_with_bindings(
            guide,
            bindings_out,
            loc);
    };

    std::vector<DeductionGuideCandidateEval> evaluated;
    for (const auto* guide : class_template->deduction_guides()) {
        DeductionGuideCandidateEval eval;
        eval.guide = guide;
        if (!guide ||
            (is_copy_initialization &&
             guide->explicit_specifier.is_present &&
             guide->explicit_specifier.effective_value)) {
            evaluated.push_back(std::move(eval));
            continue;
        }

        TemplateArgumentBindings bindings;
        if (!deduce_guide_arguments(guide, bindings)) {
            evaluated.push_back(std::move(eval));
            continue;
        }

        QualType substituted_return =
            substitute_template_type_with_bindings(
                guide->return_type(),
                guide->parameters,
                bindings,
                loc);
        substituted_return =
            collect_try_realize_deferred_semantic_type(substituted_return);
        auto return_specialization =
            dyn_cast_shared<TemplateSpecializationType>(
                desugar_typedefs(substituted_return).get_shared());
        auto* return_primary_template =
            return_specialization
                ? dyn_cast<ClassTemplateDecl>(
                      const_cast<Decl*>(return_specialization->primary_template))
                : nullptr;
        if (const auto* canonical_return_template =
                get_template_decl_canonical_decl(return_primary_template)) {
            return_primary_template =
                dyn_cast<ClassTemplateDecl>(
                    const_cast<TemplateDecl*>(canonical_return_template));
        }
        if (!return_specialization ||
            return_specialization->is_class_template_placeholder ||
            return_primary_template != class_template) {
            evaluated.push_back(std::move(eval));
            continue;
        }

        auto* specialization_decl =
            instantiate_class_template_specialization(
                class_template,
                return_specialization->arguments,
                loc);
        if (!specialization_decl || !specialization_decl->get_record_type()) {
            evaluated.push_back(std::move(eval));
            continue;
        }

        eval.function_type =
            desugar_type(
                substitute_template_type_with_bindings(
                    QualType(guide->function_type),
                    guide->parameters,
                    bindings,
                    loc),
                ast_ctx_.get())
                .as_shared<FunctionType>();
        if (!eval.function_type ||
            eval.function_type->parameters.size() != init_args.size()) {
            evaluated.push_back(std::move(eval));
            continue;
        }

        eval.viable = true;
        eval.conversions.reserve(init_args.size());
        for (size_t idx = 0; idx < init_args.size(); ++idx) {
            QualType param_type =
                decay_parameter_type(eval.function_type->parameters[idx]);
            auto seq = build_cpp_overload_conversion_sequence(
                init_args[idx],
                param_type);
            eval.conversions.push_back(seq);
            if (!seq.viable) {
                eval.viable = false;
                break;
            }
        }
        if (eval.viable) {
            eval.deduced_type = QualType(specialization_decl->get_record_type());
        }
        evaluated.push_back(std::move(eval));
    }

    std::vector<size_t> viable_indices;
    for (size_t idx = 0; idx < evaluated.size(); ++idx) {
        if (evaluated[idx].viable) {
            viable_indices.push_back(idx);
        }
    }
    if (viable_indices.empty()) {
        report_error(
            "no viable deduction guide for class template '" +
                class_template->record_decl()->name + "'",
            loc);
        return false;
    }

    auto best_index = select_best_candidate(evaluated, viable_indices);
    if (!best_index.has_value()) {
        report_error(
            "class template argument deduction for '" +
                class_template->record_decl()->name + "' is ambiguous",
            loc);
        return false;
    }

    deduced_type_out = evaluated[*best_index].deduced_type;
    return static_cast<bool>(deduced_type_out);
}

bool Collect::deduce_function_template_specialization_arguments(
    const FunctionTemplateDecl* function_template,
    QualType specialized_function_type,
    std::vector<TemplateArgument>& deduced_arguments_out,
    const TemplateArgumentBindings* initial_bindings) {
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
    } else if (isa<CppConstructorDecl>(pattern)) {
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
    size_t implicit_object_parameter_count) {
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
        !function_exception_specs_equal(
            *pattern_function,
            *specialized_function) ||
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
    const FunctionTemplateDecl* rhs_template) {
    if (!lhs_template || !rhs_template || lhs_template == rhs_template) {
        return TemplatePartialOrderingResult::Unordered;
    }

    const auto* lhs_pattern = lhs_template->function_decl();
    const auto* rhs_pattern = rhs_template->function_decl();
    if (!lhs_pattern || !rhs_pattern) {
        return TemplatePartialOrderingResult::Unordered;
    }

    FunctionParameterLayout lhs_layout =
        analyze_function_parameter_layout(lhs_pattern);
    FunctionParameterLayout rhs_layout =
        analyze_function_parameter_layout(rhs_pattern);
    if (!lhs_layout.valid || !rhs_layout.valid) {
        return TemplatePartialOrderingResult::Unordered;
    }

    auto complete_partial_ordering_bindings =
        [&](const TemplateDecl* template_decl,
            TemplateArgumentBindings& bindings,
            SrcLoc loc) {
        std::string default_error;
        return complete_template_argument_bindings_with_substituted_defaults(
            template_decl,
            bindings,
            loc,
            &default_error);
    };

    if (!lhs_layout.pack_index.has_value() &&
        !rhs_layout.pack_index.has_value() &&
        lhs_layout.parameter_count == rhs_layout.parameter_count) {
        const size_t lhs_param_count = lhs_layout.parameter_count;
        const size_t rhs_param_count = rhs_layout.parameter_count;

        auto build_non_pack_partial_ordering_argument_types =
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
                    transformed_bindings[idx] = TemplateArgumentBinding::single(
                        make_partial_ordering_unique_type_argument(idx));
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
            std::vector<QualType> transformed_argument_types;
            if (!build_non_pack_partial_ordering_argument_types(
                    argument_template,
                    transformed_argument_types) ||
                transformed_argument_types.size() != lhs_param_count) {
                return false;
            }

            FunctionParameterLayout parameter_layout =
                analyze_function_parameter_layout(
                    parameter_template ? parameter_template->function_decl() : nullptr);
            return function_template_is_at_least_as_specialized_as(
                parameter_template,
                parameter_layout,
                transformed_argument_types,
                complete_partial_ordering_bindings);
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

    auto build_partial_ordering_argument_types =
        [&](const FunctionTemplateDecl* argument_template,
            const FunctionParameterLayout& parameter_layout,
            std::vector<QualType>& transformed_types_out) -> bool {
        transformed_types_out.clear();
        const auto* argument_pattern =
            argument_template ? argument_template->function_decl() : nullptr;
        if (!argument_pattern) {
            return false;
        }

        FunctionParameterLayout argument_layout =
            analyze_function_parameter_layout(argument_pattern);
        if (!argument_layout.valid) {
            return false;
        }

        size_t target_parameter_count = 0;
        if (!argument_layout.pack_index.has_value()) {
            target_parameter_count = argument_layout.parameter_count;
        } else if (!parameter_layout.pack_index.has_value()) {
            target_parameter_count = parameter_layout.parameter_count;
        } else {
            target_parameter_count =
                std::max(parameter_layout.fixed_count(),
                         argument_layout.fixed_count()) + 1;
        }

        size_t pack_argument_count = 0;
        if (!argument_layout.pack_index.has_value()) {
            if (argument_layout.parameter_count != target_parameter_count) {
                return false;
            }
        } else {
            if (target_parameter_count < argument_layout.fixed_count()) {
                return false;
            }
            pack_argument_count =
                target_parameter_count - argument_layout.fixed_count();
        }

        TemplateArgumentBindings transformed_bindings;
        if (!build_partial_ordering_transformed_bindings(
                argument_template->parameters,
                pack_argument_count,
                transformed_bindings)) {
            return false;
        }

        transformed_types_out.reserve(target_parameter_count);
        auto append_parameter_type =
            [&](const ParamDecl* argument_decl,
                std::optional<size_t> pack_element_index) -> bool {
            if (!argument_decl) {
                return false;
            }

            TemplateArgumentBindings active_bindings = transformed_bindings;
            if (pack_element_index.has_value()) {
                std::string binding_error;
                if (!collect_template_internal::build_pack_element_argument_bindings(
                        argument_template->parameters,
                        transformed_bindings,
                        *pack_element_index,
                        active_bindings,
                        &binding_error)) {
                    return false;
                }
            }

            auto transformed_type = substitute_template_type_with_bindings(
                argument_decl->type,
                argument_template->parameters,
                active_bindings,
                argument_decl->location,
                true);
            if (type_depends_on_template_parameters(transformed_type)) {
                return false;
            }
            transformed_types_out.push_back(transformed_type);
            return true;
        };

        for (size_t idx = 0; idx < argument_layout.leading_count; ++idx) {
            auto* argument_decl =
                dyn_cast<ParamDecl>(argument_pattern->parameters[idx].get());
            if (!append_parameter_type(argument_decl, std::nullopt)) {
                return false;
            }
        }

        if (argument_layout.pack_index.has_value()) {
            auto* argument_decl = dyn_cast<ParamDecl>(
                argument_pattern->parameters[*argument_layout.pack_index].get());
            for (size_t element_index = 0;
                 element_index < pack_argument_count;
                 ++element_index) {
                if (!append_parameter_type(argument_decl, element_index)) {
                    return false;
                }
            }
        }

        for (size_t idx = 0; idx < argument_layout.trailing_count; ++idx) {
            const size_t parameter_index =
                argument_layout.parameter_count - argument_layout.trailing_count + idx;
            auto* argument_decl = dyn_cast<ParamDecl>(
                argument_pattern->parameters[parameter_index].get());
            if (!append_parameter_type(argument_decl, std::nullopt)) {
                return false;
            }
        }
        return true;
    };

    auto template_is_at_least_as_specialized_as =
        [&](const FunctionTemplateDecl* parameter_template,
            const FunctionTemplateDecl* argument_template) -> bool {
        FunctionParameterLayout parameter_layout =
            analyze_function_parameter_layout(
                parameter_template ? parameter_template->function_decl() : nullptr);

        std::vector<QualType> transformed_argument_types;
        if (!build_partial_ordering_argument_types(
                argument_template,
                parameter_layout,
                transformed_argument_types)) {
            return false;
        }

        return function_template_is_at_least_as_specialized_as(
            parameter_template,
            parameter_layout,
            transformed_argument_types,
            complete_partial_ordering_bindings);
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
        int specificity = compare_pack_layout_specificity(lhs_layout, rhs_layout);
        if (specificity > 0) {
            return TemplatePartialOrderingResult::LhsMoreSpecialized;
        }
        if (specificity < 0) {
            return TemplatePartialOrderingResult::RhsMoreSpecialized;
        }
        return TemplatePartialOrderingResult::Equivalent;
    }
    return TemplatePartialOrderingResult::Unordered;
}

bool Collect::is_function_template_more_specialized(
    const FunctionTemplateDecl* lhs_template,
    const FunctionTemplateDecl* rhs_template) {
    return compare_function_template_partial_ordering(lhs_template, rhs_template) ==
        TemplatePartialOrderingResult::LhsMoreSpecialized;
}
