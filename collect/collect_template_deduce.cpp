#include "collect.h"
#include "collect_template_state.h"

#include "../perf_stats.h"

#include <algorithm>
#include <cstring>
#include <unordered_set>
#include <utility>
#include <variant>
#include <vector>

namespace aburi::collect {

namespace {

void bump_deduce_counter(PerfCounter counter) {
    if (auto* profiler = active_perf_profiler()) {
        profiler->add_counter(counter);
    }
}

bool is_reference_kind(cir::TypeKind kind) {
    return kind == cir::TypeKind::LValueReference ||
           kind == cir::TypeKind::RValueReference;
}

const Session::TemplateInfo* transformed_alias_info(
    const Session& session,
    cir::TypeId type) {
    const cir::File& file = session.file();
    if (!file.valid(type) ||
        file.type(type).kind != cir::TypeKind::AliasSpecialization) {
        return nullptr;
    }
    const auto& alias =
        std::get<cir::AliasSpecializationTypePayload>(
            file.type_payload(type));
    const Session::TemplateInfo* info =
        session.template_info(alias.alias_template);
    return info &&
            info->alias_type_transform_kind !=
                Session::TemplateInfo::AliasTypeTransformKind::None
        ? info
        : nullptr;
}

cir::TypeId deduction_pattern_type(const Session& session,
                                   cir::TypeId type) {
    return transformed_alias_info(session, type)
        ? type
        : session.file().resolved_type(type);
}

bool same_type_parameter_identity(const cir::File& file,
                                  cir::TypeId lhs,
                                  cir::TypeId rhs) {
    lhs = file.resolved_type(lhs);
    rhs = file.resolved_type(rhs);
    if (lhs == rhs) {
        return lhs.valid();
    }
    if (!file.valid(lhs) || !file.valid(rhs) ||
        file.type(lhs).kind != cir::TypeKind::TypeParam ||
        file.type(rhs).kind != cir::TypeKind::TypeParam) {
        return false;
    }
    const auto* lhs_parameter = std::get_if<cir::TypeParamTypePayload>(
        &file.type_payload(lhs));
    const auto* rhs_parameter = std::get_if<cir::TypeParamTypePayload>(
        &file.type_payload(rhs));
    return lhs_parameter && rhs_parameter &&
        lhs_parameter->entity.valid() &&
        lhs_parameter->entity == rhs_parameter->entity;
}

bool is_forwarding_reference_parameter(const cir::File& file,
                                       cir::TypeId parameter_type) {
    parameter_type = file.resolved_type(parameter_type);
    if (!file.valid(parameter_type) ||
        file.type(parameter_type).kind != cir::TypeKind::RValueReference) {
        return false;
    }
    cir::TypeRef referred = file.reference_referred_ref(parameter_type);
    if (referred.qualifiers != cir::QualNone) {
        return false;
    }
    cir::TypeId referred_type = file.resolved_type(referred.type);
    return file.valid(referred_type) &&
           file.type(referred_type).kind == cir::TypeKind::TypeParam;
}

bool exception_specs_match_type_pattern(
    cir::FunctionExceptionSpecKind pattern,
    cir::FunctionExceptionSpecKind argument,
    Session::TypePatternExceptionMatch match) {
    using ExceptionMatch = Session::TypePatternExceptionMatch;
    if (match == ExceptionMatch::IgnoreAtCurrentFunction ||
        pattern == argument) {
        return true;
    }
    if (match == ExceptionMatch::
                     ArgumentToPatternFunctionPointerConversion) {
        return pattern ==
                   cir::FunctionExceptionSpecKind::PotentiallyThrowing &&
               argument == cir::FunctionExceptionSpecKind::NonThrowing;
    }
    if (match == ExceptionMatch::
                     PatternToArgumentFunctionPointerConversion) {
        return pattern == cir::FunctionExceptionSpecKind::NonThrowing &&
               argument ==
                   cir::FunctionExceptionSpecKind::PotentiallyThrowing;
    }
    return false;
}

bool argument_is_type(const cir::TemplateArgument& argument) {
    return argument.kind == cir::TemplateArgumentKind::Type;
}

bool template_argument_has_dependent_template_name(
    const cir::TemplateArgument& argument) {
    return argument.kind == cir::TemplateArgumentKind::Template &&
           argument.dependent_template_qualifier.type.valid() &&
           argument.template_name.valid();
}

bool template_value_exprs_equivalent(
    const cir::TemplateValueExpression& lhs,
    const cir::TemplateValueExpression& rhs) {
    if (lhs.root != rhs.root || lhs.nodes.size() != rhs.nodes.size()) {
        return false;
    }
    for (size_t i = 0; i < lhs.nodes.size(); ++i) {
        const cir::TemplateValueExprNode& a = lhs.nodes[i];
        const cir::TemplateValueExprNode& b = rhs.nodes[i];
        if (a.kind != b.kind || a.op != b.op ||
            a.trait_kind != b.trait_kind || a.value != b.value ||
            a.parameter_index != b.parameter_index || a.lhs != b.lhs ||
            a.rhs != b.rhs || a.third != b.third || a.type != b.type ||
            a.operands != b.operands ||
            a.expands_parameter_pack != b.expands_parameter_pack ||
            a.pack_references != b.pack_references ||
            a.result_type != b.result_type ||
            (a.kind != cir::TemplateValueExprKind::Parameter &&
             a.entity != b.entity) ||
            a.name != b.name || a.qualifier_type != b.qualifier_type ||
            a.semantic_key != b.semantic_key) {
            return false;
        }
    }
    return true;
}

std::optional<uint32_t> direct_exception_parameter(
    const cir::TemplateValueExpression& expression) {
    if (!expression.valid()) {
        return std::nullopt;
    }
    uint32_t index = expression.root;
    while (index < expression.nodes.size() &&
           expression.nodes[index].kind ==
               cir::TemplateValueExprKind::Cast) {
        index = expression.nodes[index].lhs;
    }
    if (index >= expression.nodes.size()) {
        return std::nullopt;
    }
    const cir::TemplateValueExprNode& root = expression.nodes[index];
    if (root.kind != cir::TemplateValueExprKind::Parameter ||
        root.parameter_index == cir::TemplateValueExprNoParameter) {
        return std::nullopt;
    }
    return root.parameter_index;
}

const cir::TemplateArgument* partial_ordering_argument_identity(
    const Session::PatternBindings& bindings,
    cir::TemplateArgumentKind kind,
    uint32_t index) {
    if (!bindings.partial_ordering ||
        !bindings.partial_ordering_argument_identities ||
        index == cir::ArrayTypePayload::no_extent_param ||
        index >= bindings.partial_ordering_argument_identities->size()) {
        return nullptr;
    }
    const cir::TemplateArgument& identity =
        (*bindings.partial_ordering_argument_identities)[index];
    return identity.kind == kind ? &identity : nullptr;
}

cir::TemplateArgument transformed_partial_ordering_argument(
    const cir::TemplateArgument& argument,
    const Session::PatternBindings& bindings) {
    uint32_t parameter = cir::ArrayTypePayload::no_extent_param;
    if (argument.kind == cir::TemplateArgumentKind::Value) {
        parameter = argument.value_param_index;
    } else if (argument.kind == cir::TemplateArgumentKind::Template) {
        parameter = argument.template_param_index;
    }
    if (const cir::TemplateArgument* identity =
            partial_ordering_argument_identity(bindings,
                                               argument.kind,
                                               parameter)) {
        return *identity;
    }
    return argument;
}

bool bind_value_argument(uint32_t index,
                         const cir::TemplateArgument& argument,
                         Session::PatternBindings& bindings,
                         const Session& session,
                         cir::TypeRef deduction_source_type,
                         bool source_type_requires_exact_match,
                         bool deduced_from_array_bound);

bool deduce_exception_spec_pattern(
    const cir::FunctionExceptionSpec& pattern,
    const cir::FunctionExceptionSpec& argument,
    Session::TypePatternExceptionMatch policy,
    Session::PatternBindings& bindings,
    const Session& session) {
    if (policy ==
        Session::TypePatternExceptionMatch::IgnoreAtCurrentFunction) {
        return true;
    }
    if (pattern.kind != cir::FunctionExceptionSpecKind::Dependent) {
        if (argument.kind == cir::FunctionExceptionSpecKind::Dependent) {
            return bindings.partial_ordering &&
                   pattern.kind == argument.kind;
        }
        return exception_specs_match_type_pattern(pattern.kind,
                                                  argument.kind,
                                                  policy);
    }

    if (std::optional<uint32_t> parameter =
            direct_exception_parameter(pattern.predicate)) {
        cir::TemplateArgument value;
        value.kind = cir::TemplateArgumentKind::Value;
        value.value_type = session.file().type_ref(
            session.file().builtin_type(cir::BuiltinTypeKind::Bool));
        if (argument.kind == cir::FunctionExceptionSpecKind::Dependent) {
            if (!argument.predicate.valid()) {
                return false;
            }
            if (std::optional<uint32_t> argument_parameter =
                    direct_exception_parameter(argument.predicate);
                argument_parameter.has_value()) {
                if (const cir::TemplateArgument* identity =
                        partial_ordering_argument_identity(
                            bindings,
                            cir::TemplateArgumentKind::Value,
                            *argument_parameter)) {
                    value = *identity;
                } else {
                    value.value_kind = cir::TemplateValueKind::None;
                    value.dependent_value_expr = argument.predicate;
                    value.is_dependent = true;
                }
            } else {
                value.value_kind = cir::TemplateValueKind::None;
                value.dependent_value_expr = argument.predicate;
                value.is_dependent = true;
            }
        } else {
            value.value_kind = cir::TemplateValueKind::Boolean;
            value.integer_value = cir::IntegerValue::from_unsigned(
                argument.kind == cir::FunctionExceptionSpecKind::NonThrowing
                    ? 1
                    : 0,
                1);
        }
        return bind_value_argument(
            *parameter,
            value,
            bindings,
            session,
            value.value_type,
            /*source_type_requires_exact_match=*/true,
            /*deduced_from_array_bound=*/false);
    }

    if (bindings.partial_ordering) {
        return argument.kind == cir::FunctionExceptionSpecKind::Dependent &&
               template_value_exprs_equivalent(pattern.predicate,
                                                argument.predicate);
    }
    bindings.pending_exception_matches.push_back(
        {pattern, argument, policy});
    return true;
}

bool bind_value_argument(uint32_t index,
                         const cir::TemplateArgument& argument,
                         Session::PatternBindings& bindings,
                         const Session& session,
                         cir::TypeRef deduction_source_type = {},
                         bool source_type_requires_exact_match = false,
                         bool deduced_from_array_bound = false) {
    if (index < bindings.explicit_values.size() &&
        bindings.explicit_values[index]) {
        return true;
    }
    if (index >= bindings.values.size()) {
        bindings.values.resize(index + 1);
    }
    Session::PatternBindings::ValueBinding& binding = bindings.values[index];
    if (!binding.bound) {
        binding.bound = true;
        binding.argument = argument;
    } else if (!session.template_value_arguments_equivalent(binding.argument,
                                                             argument)) {
        constexpr uint32_t no_parameter =
            cir::ArrayTypePayload::no_extent_param;
        bool binding_is_concrete_integral =
            binding.argument.kind == cir::TemplateArgumentKind::Value &&
            (binding.argument.value_kind == cir::TemplateValueKind::Integer ||
             binding.argument.value_kind == cir::TemplateValueKind::Boolean) &&
            binding.argument.value_param_index == no_parameter &&
            !binding.argument.dependent_value_expr.valid() &&
            !binding.argument.is_dependent;
        bool argument_is_concrete_integral =
            argument.kind == cir::TemplateArgumentKind::Value &&
            (argument.value_kind == cir::TemplateValueKind::Integer ||
             argument.value_kind == cir::TemplateValueKind::Boolean) &&
            argument.value_param_index == no_parameter &&
            !argument.dependent_value_expr.valid() &&
            !argument.is_dependent;
        bool same_concrete_integral_value =
            binding_is_concrete_integral &&
            argument_is_concrete_integral &&
            binding.argument.integer_value.low_bits ==
                argument.integer_value.low_bits &&
            binding.argument.integer_value.high_bits ==
                argument.integer_value.high_bits;
        if (!(same_concrete_integral_value &&
              (binding.deduced_from_array_bound ||
               deduced_from_array_bound))) {
            return false;
        }
    }
    if (source_type_requires_exact_match &&
        !binding.source_type_requires_exact_match) {

        binding.argument = argument;
    }
    if (deduction_source_type.valid()) {
        if (source_type_requires_exact_match ||
            !binding.deduction_source_type.valid()) {
            if (binding.source_type_requires_exact_match &&
                binding.deduction_source_type != deduction_source_type) {
                return false;
            }
            binding.deduction_source_type = deduction_source_type;
        }
        binding.source_type_requires_exact_match =
            binding.source_type_requires_exact_match ||
            source_type_requires_exact_match;
    }
    binding.deduced_from_array_bound =
        binding.deduced_from_array_bound || deduced_from_array_bound;
    return true;
}

bool bind_type_argument(uint32_t index,
                        cir::TypeRef argument,
                        Session::PatternBindings& bindings) {
    if (index < bindings.explicit_types.size() &&
        bindings.explicit_types[index]) {
        return true;
    }
    if (index >= bindings.types.size()) {
        bindings.types.resize(index + 1);
    }
    cir::TypeRef& binding = bindings.types[index];
    if (!binding.valid()) {
        binding = argument;
        return true;
    }
    return binding == argument;
}

bool template_template_arguments_equivalent(
    const cir::TemplateArgument& lhs,
    const cir::TemplateArgument& rhs) {
    return lhs.kind == cir::TemplateArgumentKind::Template &&
           rhs.kind == cir::TemplateArgumentKind::Template &&
           lhs.template_entity == rhs.template_entity &&
           lhs.template_param_index == rhs.template_param_index &&
           lhs.dependent_template_qualifier.type ==
               rhs.dependent_template_qualifier.type;
}

bool bind_template_argument(uint32_t index,
                            const cir::TemplateArgument& argument,
                            Session::PatternBindings& bindings) {
    if (index < bindings.explicit_templates.size() &&
        bindings.explicit_templates[index]) {
        return true;
    }
    if (index >= bindings.templates.size()) {
        bindings.templates.resize(index + 1);
    }
    Session::PatternBindings::TemplateBinding& binding =
        bindings.templates[index];
    if (!binding.bound) {
        binding.bound = true;
        binding.argument = argument;
        return true;
    }
    return template_template_arguments_equivalent(binding.argument, argument);
}

cir::TypeRef deduction_argument_ref(const cir::File& file,
                                    const ExprResult& argument_expr,
                                    cir::TypeId fallback_type) {
    cir::TypeRef argument = file.type_ref(fallback_type);
    if (argument_expr.semantic_object_qualifiers.has_value()) {

        argument.qualifiers = static_cast<uint8_t>(
            argument.qualifiers |
            *argument_expr.semantic_object_qualifiers);
    }
    if ((argument_expr.category != ValueCategory::LValue &&
         argument_expr.category != ValueCategory::XValue) ||
        !argument_expr.place.valid() ||
        !file.valid(argument_expr.place)) {
        return argument;
    }
    cir::TypeId place_type = file.inst(argument_expr.place).result_type;
    if (!file.valid(place_type) ||
        file.type(place_type).kind != cir::TypeKind::Place) {
        return argument;
    }
    cir::TypeRef object = file.place_object_ref(place_type);
    object.type = file.resolved_type(object.type);
    return object.type.valid() ? object : argument;
}

} // namespace

namespace detail {
bool deduce_exception_spec_for_partial_ordering(
    const cir::FunctionExceptionSpec& pattern,
    const cir::FunctionExceptionSpec& argument,
    Session::PatternBindings& bindings,
    const Session& session) {
    return deduce_exception_spec_pattern(
        pattern,
        argument,
        Session::TypePatternExceptionMatch::Exact,
        bindings,
        session);
}
} // namespace detail

bool Session::deduce_initializer_list_argument(cir::TypeId parameter_type,
                                               const ExprResult& argument,
                                               PatternBindings& bindings,
                                               SrcLoc loc) {
    if (!argument.init_list || argument.init_list->elements.empty()) {
        return true;
    }

    cir::TypeId pattern = file_.resolved_type(parameter_type);
    if (!file_.valid(pattern)) {
        return false;
    }
    if (is_reference_kind(file_.type(pattern).kind)) {
        pattern = file_.resolved_type(file_.reference_referred_type(pattern));
        if (!file_.valid(pattern)) {
            return false;
        }
    }

    if (std::optional<cir::TypeRef> element =
            initializer_list_element_type(pattern)) {
        for (const InitElementInput& input : argument.init_list->elements) {
            if (!input.designators.empty() ||
                !deduce_call_argument(element->type,
                                      input.value,
                                      bindings,
                                      loc)) {
                return false;
            }
        }
        return true;
    }
    if (file_.type(pattern).kind != cir::TypeKind::Array) {
        return true;
    }
    const auto* array =
        std::get_if<cir::ArrayTypePayload>(&file_.type_payload(pattern));
    if (!array) {
        return false;
    }

    constexpr uint32_t no_extent = cir::ArrayTypePayload::no_extent_param;
    if (array->extent_param != no_extent) {
        cir::TemplateArgument extent_argument;
        extent_argument.kind = cir::TemplateArgumentKind::Value;
        extent_argument.value_kind = cir::TemplateValueKind::Integer;
        extent_argument.integer_value = cir::IntegerValue::from_unsigned(
            argument.init_list->elements.size(), 64);
        if (!bind_value_argument(array->extent_param,
                                 extent_argument,
                                 bindings,
                                 *this,
                                 file_.type_ref(builder_.usize_type()),
                                 /*source_type_requires_exact_match=*/false,
                                 /*deduced_from_array_bound=*/true)) {
            return false;
        }
    }

    for (const InitElementInput& element : argument.init_list->elements) {
        if (!element.designators.empty()) {
            return false;
        }
        if (!deduce_call_argument(array->element_type.type,
                                  element.value,
                                  bindings,
                                  loc)) {
            return false;
        }
    }
    return true;
}

bool Session::deduce_call_argument(cir::TypeId parameter_type,
                                   const ExprResult& argument_expr,
                                   PatternBindings& bindings,
                                   SrcLoc loc) {
    parameter_type = deduction_pattern_type(*this, parameter_type);
    if (!file_.valid(parameter_type)) {
        return false;
    }
    if ((argument_expr.category == ValueCategory::FunctionDesignator ||
         argument_expr.category == ValueCategory::OverloadDesignator) &&
        (!argument_expr.candidates.empty() ||
         argument_expr.overload_designator ||
         (argument_expr.entity.valid() &&
          template_info(argument_expr.entity) != nullptr))) {
        return deduce_overload_set_argument(parameter_type,
                                            argument_expr,
                                            bindings,
                                            loc);
    }
    if (argument_expr.category == ValueCategory::MemberPointerDesignator &&
        !argument_expr.candidates.empty()) {
        return deduce_overload_set_argument(parameter_type,
                                            argument_expr,
                                            bindings,
                                            loc);
    }
    if (argument_expr.category == ValueCategory::InitList ||
        argument_expr.init_list) {
        return deduce_initializer_list_argument(parameter_type,
                                               argument_expr,
                                               bindings,
                                               loc);
    }

    cir::TypeId argument = file_.resolved_type(argument_expr.type);
    if (!file_.valid(argument)) {
        return false;
    }
    cir::TypeRef deduction_parameter = file_.type_ref(parameter_type);
    cir::TypeRef deduction_argument = file_.type_ref(argument);
    cir::TypeKind parameter_kind = file_.type(parameter_type).kind;
    if (is_reference_kind(parameter_kind)) {
        cir::TypeRef referred_pattern_ref =
            file_.reference_referred_ref(parameter_type);
        cir::TypeRef referred_argument =
            deduction_argument_ref(file_, argument_expr, argument);
        bool forwarding_lvalue =
            is_forwarding_reference_parameter(file_, parameter_type) &&
            argument_expr.category == ValueCategory::LValue;

        parameter_type =
            deduction_pattern_type(*this, referred_pattern_ref.type);
        if (forwarding_lvalue) {
            argument = reference_type(referred_argument,
                                      cir::ReferenceKind::LValue);
            deduction_parameter = file_.type_ref(parameter_type);
            deduction_argument = file_.type_ref(argument);
        } else {
            referred_pattern_ref.type = parameter_type;
            deduction_parameter = referred_pattern_ref;
            deduction_argument = referred_argument;

            const cir::Type& referred_pattern_node = file_.type(parameter_type);
            if (referred_pattern_node.kind == cir::TypeKind::TypeParam) {
                const auto* leaf = std::get_if<cir::TypeParamTypePayload>(
                    &file_.type_payload(parameter_type));
                cir::TypeRef deduced = referred_argument;
                deduced.qualifiers = static_cast<uint8_t>(
                    deduced.qualifiers &
                    static_cast<uint8_t>(~referred_pattern_ref.qualifiers));
                if (referred_pattern_ref.memory_space !=
                    cir::MemorySpace::Default) {
                    if (referred_pattern_ref.memory_space !=
                        referred_argument.memory_space) {
                        return false;
                    }
                    deduced.memory_space = cir::MemorySpace::Default;
                }
                return leaf &&
                       bind_type_argument(leaf->index, deduced, bindings);
            }

            constexpr uint8_t top_level_cv =
                cir::QualConst | cir::QualVolatile;
            cir::TypeId cv_parameter_type =
                file_.resolved_type(deduction_parameter.type);
            cir::TypeId cv_argument_type =
                file_.resolved_type(deduction_argument.type);
            bool array_pair =
                file_.valid(cv_parameter_type) &&
                file_.valid(cv_argument_type) &&
                file_.type(cv_parameter_type).kind == cir::TypeKind::Array &&
                file_.type(cv_argument_type).kind == cir::TypeKind::Array;
            auto effective_cv = [&](cir::TypeRef type) {
                uint8_t qualifiers = type.qualifiers;
                cir::TypeId resolved = file_.resolved_type(type.type);
                if (file_.valid(resolved) &&
                    file_.type(resolved).kind == cir::TypeKind::Array) {
                    if (const auto* array =
                            std::get_if<cir::ArrayTypePayload>(
                                &file_.type_payload(resolved))) {

                        qualifiers = static_cast<uint8_t>(
                            qualifiers | array->element_type.qualifiers);
                    }
                }
                return static_cast<uint8_t>(qualifiers & top_level_cv);
            };
            uint8_t parameter_cv = effective_cv(deduction_parameter);
            uint8_t argument_cv = effective_cv(deduction_argument);
            if (!array_pair && (argument_cv & ~parameter_cv) != 0) {
                return false;
            }
            if (!array_pair) {
                deduction_parameter.qualifiers = static_cast<uint8_t>(
                    deduction_parameter.qualifiers & ~top_level_cv);
                deduction_argument.qualifiers = static_cast<uint8_t>(
                    deduction_argument.qualifiers & ~top_level_cv);
            } else {

                deduction_argument.qualifiers = static_cast<uint8_t>(
                    deduction_argument.qualifiers |
                    (parameter_cv & static_cast<uint8_t>(~argument_cv)));
            }
        }
    } else {

        const cir::Type& argument_node = file_.type(argument);
        if (argument_node.kind == cir::TypeKind::Array) {
            const auto* array = std::get_if<cir::ArrayTypePayload>(
                &file_.type_payload(argument));
            if (array) {

                cir::TypeRef array_object =
                    deduction_argument_ref(file_, argument_expr, argument);
                cir::TypeRef element = array->element_type;
                element.qualifiers = static_cast<uint8_t>(
                    element.qualifiers | array_object.qualifiers);
                if (element.memory_space == cir::MemorySpace::Default &&
                    array_object.memory_space != cir::MemorySpace::Default) {
                    element.memory_space = array_object.memory_space;
                }
                argument = file_.pointer_type(element);
            }
        } else if (argument_node.kind == cir::TypeKind::Function) {
            argument = file_.pointer_type(
                cir::TypeRef{argument, cir::QualNone,
                             cir::MemorySpace::Default});
        }
        deduction_parameter = file_.type_ref(parameter_type);
        deduction_argument = file_.type_ref(argument);
    }
    if (!file_.valid(parameter_type)) {
        return false;
    }

    PatternBindings strict_bindings = bindings;
    if (unify_type_ref_pattern(deduction_parameter,
                               deduction_argument,
                               strict_bindings)) {
        bindings = std::move(strict_bindings);
        return true;
    }
    PatternBindings converted_bindings = bindings;
    QualificationConversionAnalysis qualification =
        analyze_qualification_conversion(
            deduction_argument,
            deduction_parameter,
            QualificationTargetKind::TypePattern);
    if (qualification.has_indirection && qualification.similar &&
        qualification.allowed &&
        unify_type_ref_pattern(
            deduction_parameter,
            deduction_argument,
            converted_bindings,
            TypePatternExceptionMatch::
                ArgumentToPatternFunctionPointerConversion,
            /*allow_qualification_conversion=*/true)) {
        bindings = std::move(converted_bindings);
        return true;
    }
    return deduce_call_derived_class_alternative(parameter_type,
                                                 argument,
                                                 bindings);
}

bool Session::deduce_call_derived_class_alternative(
    cir::TypeId parameter_type,
    cir::TypeId argument_type,
    PatternBindings& bindings) {
    cir::TypeRef pattern = file_.type_ref(parameter_type);
    cir::TypeRef argument = file_.type_ref(argument_type);
    cir::TypeId pattern_record = file_.resolved_type(pattern.type);
    cir::TypeId derived_record = file_.resolved_type(argument.type);
    bool pointer_form = false;

    if (file_.valid(pattern_record) && file_.valid(derived_record) &&
        file_.type(pattern_record).kind == cir::TypeKind::Pointer &&
        file_.type(derived_record).kind == cir::TypeKind::Pointer) {
        QualificationConversionAnalysis qualification =
            analyze_qualification_conversion(
                argument,
                pattern,
                QualificationTargetKind::TypePattern);
        if (!qualification.similar || !qualification.allowed) {
            return false;
        }
        pattern = file_.pointer_pointee_ref(pattern_record);
        argument = file_.pointer_pointee_ref(derived_record);
        pattern_record = file_.resolved_type(pattern.type);
        derived_record = file_.resolved_type(argument.type);
        pointer_form = true;
    }

    if (!file_.valid(pattern_record) || !file_.valid(derived_record) ||
        pattern_record == derived_record ||
        (file_.type(pattern_record).kind != cir::TypeKind::Record &&
         file_.type(pattern_record).kind !=
             cir::TypeKind::TemplateSpecialization) ||
        file_.type(derived_record).kind != cir::TypeKind::Record) {
        return false;
    }
    if (file_.type(pattern_record).kind == cir::TypeKind::Record) {
        const cir::TemplateSpecializationFact* pattern_fact =
            file_.template_specialization(
                file_.record_entity(pattern_record));
        if (!pattern_fact || !pattern_fact->template_entity.valid()) {
            return false;
        }
    }

    struct Candidate {
        cir::TypeId base_type;
        PatternBindings bindings;
    };
    std::vector<Candidate> candidates;
    std::unordered_set<uint32_t> visited;
    auto visit_bases = [&](auto&& self, cir::TypeId record_type) -> void {
        const cir::RecordFacts* facts =
            file_.record_facts_for_type(file_.resolved_type(record_type));
        if (!facts) {
            return;
        }
        for (const cir::RecordBaseFact& base : facts->bases) {
            cir::TypeId base_type = file_.resolved_type(base.type.type);
            if (!file_.valid(base_type) ||
                file_.type(base_type).kind != cir::TypeKind::Record ||
                !visited.insert(static_cast<uint32_t>(base_type.index)).second) {
                continue;
            }
            PatternBindings trial = bindings;
            if (unify_type_ref_pattern(
                    pattern,
                    base.type,
                    trial,
                    TypePatternExceptionMatch::Exact,
                    /*allow_qualification_conversion=*/pointer_form)) {
                candidates.push_back(Candidate{base_type, std::move(trial)});
            }
            self(self, base_type);
        }
    };
    visit_bases(visit_bases, derived_record);
    if (candidates.empty()) {
        return false;
    }

    std::vector<bool> eliminated(candidates.size(), false);
    for (size_t i = 0; i < candidates.size(); ++i) {
        for (size_t j = 0; j < candidates.size(); ++j) {
            if (i == j || eliminated[i]) {
                continue;
            }
            if (analyze_derived_to_base_path(candidates[j].base_type,
                                             candidates[i].base_type)
                    .kind != DerivedToBasePathKind::NotFound) {
                eliminated[i] = true;
            }
        }
    }
    size_t winner = candidates.size();
    for (size_t i = 0; i < candidates.size(); ++i) {
        if (eliminated[i]) {
            continue;
        }
        if (winner != candidates.size()) {
            return false;
        }
        winner = i;
    }
    if (winner == candidates.size()) {
        return false;
    }
    bindings = std::move(candidates[winner].bindings);
    return true;
}

bool Session::template_parameter_is_deducible_from_type(
    const TemplateParameter& parameter,
    cir::TypeId type) const {
    std::unordered_set<uint32_t> visited_types;
    std::function<bool(const cir::TemplateArgument&)> argument_mentions;
    std::function<bool(cir::TypeId)> type_mentions;

    argument_mentions = [&](const cir::TemplateArgument& argument) {
        switch (parameter.kind) {
            case TemplateParameterKind::Type:
                return argument.kind == cir::TemplateArgumentKind::Type &&
                       type_mentions(argument.type.type);
            case TemplateParameterKind::NonType: {
                if (argument.kind != cir::TemplateArgumentKind::Value) {
                    return false;
                }
                if (argument.value_param_index == parameter.index) {
                    return true;
                }

                const cir::TemplateValueExpression& expression =
                    argument.dependent_value_expr;
                if (expression.root < expression.nodes.size()) {
                    const cir::TemplateValueExprNode& root =
                        expression.nodes[expression.root];
                    return root.kind ==
                               cir::TemplateValueExprKind::Parameter &&
                           root.parameter_index == parameter.index;
                }
                return false;
            }
            case TemplateParameterKind::Template:
                return argument.kind == cir::TemplateArgumentKind::Template &&
                       argument.template_param_index == parameter.index;
        }
        return false;
    };

    type_mentions = [&](cir::TypeId type) -> bool {
        if (const TemplateInfo* alias_info =
                transformed_alias_info(*this, type)) {
            (void)alias_info;
            if (!visited_types.insert(
                    static_cast<uint32_t>(type.index)).second) {
                return false;
            }
            const auto& alias =
                std::get<cir::AliasSpecializationTypePayload>(
                    file_.type_payload(type));
            if (type_mentions(alias.associated_type.type)) {
                return true;
            }
            return std::any_of(alias.arguments.begin(),
                               alias.arguments.end(),
                               argument_mentions);
        }
        type = file_.resolved_type(type);
        if (!file_.valid(type) ||
            !visited_types.insert(static_cast<uint32_t>(type.index)).second) {
            return false;
        }
        const cir::Type& node = file_.type(type);
        const cir::TypePayload& payload = file_.type_payload(type);
        if (node.kind == cir::TypeKind::TypeParam) {
            const auto* type_parameter =
                std::get_if<cir::TypeParamTypePayload>(&payload);
            return parameter.kind == TemplateParameterKind::Type &&
                   type_parameter && type_parameter->index == parameter.index &&
                   type_parameter->depth == parameter.depth;
        }
        switch (node.kind) {
            case cir::TypeKind::Pointer: {
                const auto* pointer =
                    std::get_if<cir::PointerTypePayload>(&payload);
                return pointer && type_mentions(pointer->pointee.type);
            }
            case cir::TypeKind::BlockPointer: {
                const auto* pointer =
                    std::get_if<cir::BlockPointerTypePayload>(&payload);
                return pointer && type_mentions(pointer->pointee.type);
            }
            case cir::TypeKind::MemberPointer: {
                const auto* member =
                    std::get_if<cir::MemberPointerTypePayload>(&payload);
                return member &&
                       (type_mentions(member->class_type.type) ||
                        type_mentions(member->member_type.type));
            }
            case cir::TypeKind::LValueReference:
            case cir::TypeKind::RValueReference: {
                const auto* reference =
                    std::get_if<cir::ReferenceTypePayload>(&payload);
                return reference &&
                       type_mentions(reference->referred_type.type);
            }
            case cir::TypeKind::Array: {
                const auto* array =
                    std::get_if<cir::ArrayTypePayload>(&payload);
                if (!array) {
                    return false;
                }
                if (parameter.kind == TemplateParameterKind::NonType &&
                    array->extent_param == parameter.index) {
                    return true;
                }
                return type_mentions(array->element_type.type);
            }
            case cir::TypeKind::Function: {
                const auto* nested =
                    std::get_if<cir::FunctionTypePayload>(&payload);
                if (!nested) {
                    return false;
                }
                if (type_mentions(nested->return_type.type)) {
                    return true;
                }
                for (const cir::TypeRef& nested_parameter :
                     nested->parameters) {
                    if (type_mentions(nested_parameter.type)) {
                        return true;
                    }
                }
                if (parameter.kind == TemplateParameterKind::NonType) {
                    for (const cir::TemplateValueExprNode& expression_node :
                         nested->exception_spec.predicate.nodes) {
                        if (expression_node.kind ==
                                cir::TemplateValueExprKind::Parameter &&
                            expression_node.parameter_index ==
                                parameter.index) {
                            return true;
                        }
                    }
                }
                return false;
            }
            case cir::TypeKind::Record: {
                cir::EntityId record = file_.record_entity(type);
                const cir::TemplateSpecializationFact* fact =
                    file_.template_specialization(record);
                std::vector<TemplateArgument> arguments;
                if (fact) {
                    arguments = fact->template_arguments();
                } else if (!class_template_arguments_for_record(
                               record, nullptr, &arguments)) {
                    return false;
                }
                if (parameter.kind == TemplateParameterKind::Template &&
                    fact &&
                    fact->template_param_index == parameter.index) {
                    return true;
                }
                return std::any_of(arguments.begin(),
                                   arguments.end(),
                                   argument_mentions);
            }
            case cir::TypeKind::TemplateSpecialization: {
                const auto* specialization =
                    std::get_if<cir::TemplateSpecializationTypePayload>(
                        &payload);
                if (!specialization) {
                    return false;
                }
                if (parameter.kind == TemplateParameterKind::NonType) {
                    for (const cir::TemplateValueExprNode& node :
                         specialization->splice_operand.nodes) {
                        if (node.kind ==
                                cir::TemplateValueExprKind::Parameter &&
                            node.parameter_index == parameter.index) {
                            return true;
                        }
                    }
                }
                return std::any_of(specialization->arguments.begin(),
                                   specialization->arguments.end(),
                                   argument_mentions);
            }
            case cir::TypeKind::Vector: {
                const auto* vector =
                    std::get_if<cir::VectorTypePayload>(&payload);
                return vector && type_mentions(vector->element_type.type);
            }
            case cir::TypeKind::Complex: {
                const auto* complex =
                    std::get_if<cir::ComplexTypePayload>(&payload);
                return complex && type_mentions(complex->element_type.type);
            }
            case cir::TypeKind::Typedef: {
                const auto* alias =
                    std::get_if<cir::TypedefTypePayload>(&payload);
                return alias && type_mentions(alias->underlying_type.type);
            }
            case cir::TypeKind::Place: {
                const auto* place =
                    std::get_if<cir::PlaceTypePayload>(&payload);
                return place && type_mentions(place->object_type.type);
            }
            default:

                return false;
        }
    };

    return type_mentions(type);
}

bool Session::template_parameter_is_deducible_from_function_parameter_types(
    const TemplateParameter& parameter,
    cir::TypeId function_type) const {
    cir::TypeId resolved_function = file_.resolved_type(function_type);
    if (!file_.valid(resolved_function) ||
        file_.type(resolved_function).kind != cir::TypeKind::Function) {
        return false;
    }
    const auto* function = std::get_if<cir::FunctionTypePayload>(
        &file_.type_payload(resolved_function));
    if (!function) {
        return false;
    }
    for (const cir::TypeRef& function_parameter : function->parameters) {
        if (template_parameter_is_deducible_from_type(
                parameter, function_parameter.type)) {
            return true;
        }
    }
    return false;
}

bool Session::reconcile_deduced_value_parameter_types(
    const TemplateInfo& info,
    PatternBindings& bindings) {
    for (size_t i = 0; i < info.parameters.size(); ++i) {
        const TemplateParameter& parameter = info.parameters[i];
        if (parameter.kind != TemplateParameterKind::NonType ||
            i >= bindings.values.size()) {
            continue;
        }
        PatternBindings::ValueBinding& binding = bindings.values[i];
        if (!binding.bound ||
            (!binding.deduction_source_type.valid() &&
             !binding.deduced_from_array_bound) ||
            (i < bindings.explicit_values.size() &&
             bindings.explicit_values[i])) {
            continue;
        }

        cir::TypeId declared_type = parameter.non_type_type.valid()
            ? parameter.non_type_type
            : builder_.int_type();
        if (!binding.deduction_source_type.valid()) {
            binding.deduction_source_type =
                file_.type_ref(builder_.usize_type());
        }
        cir::TypeId source_type =
            file_.resolved_type(binding.deduction_source_type.type);
        if (!file_.valid(declared_type) || !file_.valid(source_type)) {
            return false;
        }

        if (contains_auto_type(declared_type)) {
            cir::TypeId resolved_declared = file_.resolved_type(declared_type);
            const auto* placeholder = file_.valid(resolved_declared) &&
                    file_.type(resolved_declared).kind == cir::TypeKind::Auto
                ? std::get_if<cir::AutoTypePayload>(
                      &file_.type_payload(resolved_declared))
                : nullptr;
            bool is_decltype_auto = placeholder &&
                (placeholder->flavor == cir::AutoTypeFlavor::DecltypeAuto ||
                 placeholder->flavor ==
                     cir::AutoTypeFlavor::DecltypeAutoTemplateNonType);
            if (is_decltype_auto) {
                binding.argument.value_type = binding.deduction_source_type;
                continue;
            }
            if (placeholder) {
                cir::TypeRef adjusted = binding.deduction_source_type;
                cir::TypeId adjusted_type = file_.resolved_type(adjusted.type);
                if (file_.valid(adjusted_type) &&
                    (file_.type(adjusted_type).kind ==
                         cir::TypeKind::LValueReference ||
                     file_.type(adjusted_type).kind ==
                         cir::TypeKind::RValueReference)) {
                    adjusted = file_.reference_referred_ref(adjusted_type);
                }
                adjusted.qualifiers = cir::QualNone;
                adjusted.type = file_.resolved_type(adjusted.type);

                cir::TypeRef source = binding.deduction_source_type;
                source.type = file_.resolved_type(source.type);
                source.qualifiers = cir::QualNone;
                if (adjusted != source) {
                    return false;
                }
                binding.argument.value_type = adjusted;
                continue;
            }

            binding.argument.value_type = binding.deduction_source_type;
            continue;
        }

        auto convert_array_bound_to_declared_type =
            [&](cir::TypeId target_type,
                PatternBindings::ValueBinding& target_binding) {
                if (!target_binding.deduced_from_array_bound ||
                    target_binding.source_type_requires_exact_match) {
                    return true;
                }
                constexpr uint32_t no_parameter =
                    cir::ArrayTypePayload::no_extent_param;
                if (target_binding.argument.is_dependent ||
                    target_binding.argument.value_param_index != no_parameter ||
                    target_binding.argument.dependent_value_expr.valid()) {

                    return true;
                }
                TemplateValueConstant constant;
                constant.kind = target_binding.argument.value_kind;
                constant.integer_value =
                    target_binding.argument.integer_value;
                constant.floating_value =
                    target_binding.argument.floating_value;
                TemplateArgument converted;
                if (!build_template_value_argument(target_type,
                                                   constant,
                                                   converted)) {
                    return false;
                }
                target_binding.argument = std::move(converted);
                return true;
            };

        PatternBindings trial = bindings;
        if (unify_type_pattern(declared_type, source_type, trial)) {
            bindings = std::move(trial);
            PatternBindings::ValueBinding& reconciled = bindings.values[i];
            if (!reconciled.argument.value_type.valid()) {
                reconciled.argument.value_type =
                    reconciled.deduction_source_type;
            }
            cir::TypeId resolved_declared =
                file_.resolved_type(declared_type);
            bool declared_is_concrete_integral =
                file_.valid(resolved_declared) &&
                file_.type(resolved_declared).kind != cir::TypeKind::TypeParam &&
                file_.type(resolved_declared).kind != cir::TypeKind::Enum &&
                is_integer_type(resolved_declared);
            if (declared_is_concrete_integral &&
                !convert_array_bound_to_declared_type(resolved_declared,
                                                      reconciled)) {
                return false;
            }
            continue;
        }

        cir::TypeId resolved_declared = file_.resolved_type(declared_type);
        bool declared_is_integral =
            file_.valid(resolved_declared) &&
            file_.type(resolved_declared).kind != cir::TypeKind::Enum &&
            is_integer_type(resolved_declared);
        if (binding.source_type_requires_exact_match ||
            !binding.deduced_from_array_bound || !declared_is_integral) {
            return false;
        }
        if (!convert_array_bound_to_declared_type(resolved_declared,
                                                  binding)) {
            return false;
        }
    }
    return true;
}

bool Session::finalize_pending_exception_matches(
    PatternBindings& bindings,
    const TemplateArgumentBindings& argument_bindings,
    PatternInstantiationCallbacks* callbacks) {
    if (bindings.pending_exception_matches.empty()) {
        return true;
    }
    PatternInstantiationCallbacks fallback_callbacks;
    PatternInstantiationCallbacks& active_callbacks =
        callbacks ? *callbacks : fallback_callbacks;

    auto substitute_spec = [&](cir::FunctionExceptionSpec spec)
        -> std::optional<cir::FunctionExceptionSpec> {
        if (spec.kind != cir::FunctionExceptionSpecKind::Dependent) {
            return spec;
        }
        TemplateArgument predicate;
        predicate.kind = cir::TemplateArgumentKind::Value;
        predicate.value_type =
            file_.type_ref(file_.builtin_type(cir::BuiltinTypeKind::Bool));
        predicate.value_kind = cir::TemplateValueKind::None;
        predicate.dependent_value_expr = std::move(spec.predicate);
        predicate.is_dependent = true;
        if (!substitute_template_value_argument(predicate,
                                                argument_bindings,
                                                active_callbacks)) {
            return std::nullopt;
        }
        if (predicate.is_dependent) {
            spec.predicate = std::move(predicate.dependent_value_expr);
            return spec;
        }
        if (predicate.value_kind != cir::TemplateValueKind::Integer &&
            predicate.value_kind != cir::TemplateValueKind::Boolean) {
            return std::nullopt;
        }
        return !predicate.integer_value.is_zero()
            ? cir::FunctionExceptionSpec{
                  cir::FunctionExceptionSpecKind::NonThrowing}
            : cir::FunctionExceptionSpec{
                  cir::FunctionExceptionSpecKind::PotentiallyThrowing};
    };

    for (const PatternBindings::PendingExceptionMatch& pending :
         bindings.pending_exception_matches) {
        std::optional<cir::FunctionExceptionSpec> pattern =
            substitute_spec(pending.pattern);
        if (!pattern.has_value()) {
            return false;
        }
        if (pattern->kind == cir::FunctionExceptionSpecKind::Dependent ||
            pending.argument.kind ==
                cir::FunctionExceptionSpecKind::Dependent) {
            if (pattern->kind != pending.argument.kind ||
                !template_value_exprs_equivalent(
                    pattern->predicate, pending.argument.predicate)) {
                return false;
            }
            continue;
        }
        if (!exception_specs_match_type_pattern(pattern->kind,
                                                pending.argument.kind,
                                                pending.policy)) {
            return false;
        }
    }
    bindings.pending_exception_matches.clear();
    return true;
}

bool Session::pattern_bindings_equivalent(const PatternBindings& lhs,
                                          const PatternBindings& rhs) const {
    size_t type_count = std::max(lhs.types.size(), rhs.types.size());
    for (size_t i = 0; i < type_count; ++i) {
        cir::TypeRef left = i < lhs.types.size() ? lhs.types[i] : cir::TypeRef{};
        cir::TypeRef right = i < rhs.types.size() ? rhs.types[i] : cir::TypeRef{};
        if (left != right) {
            return false;
        }
    }
    size_t value_count = std::max(lhs.values.size(), rhs.values.size());
    for (size_t i = 0; i < value_count; ++i) {
        const PatternBindings::ValueBinding* left =
            i < lhs.values.size() ? &lhs.values[i] : nullptr;
        const PatternBindings::ValueBinding* right =
            i < rhs.values.size() ? &rhs.values[i] : nullptr;
        bool left_bound = left && left->bound;
        bool right_bound = right && right->bound;
        if (left_bound != right_bound) {
            return false;
        }
        if (left_bound &&
            !template_value_arguments_equivalent(left->argument,
                                                 right->argument)) {
            return false;
        }
        if (left_bound &&
            (left->deduction_source_type != right->deduction_source_type ||
             left->source_type_requires_exact_match !=
                 right->source_type_requires_exact_match ||
             left->deduced_from_array_bound !=
                 right->deduced_from_array_bound)) {
            return false;
        }
    }
    size_t template_count =
        std::max(lhs.templates.size(), rhs.templates.size());
    for (size_t i = 0; i < template_count; ++i) {
        const PatternBindings::TemplateBinding* left =
            i < lhs.templates.size() ? &lhs.templates[i] : nullptr;
        const PatternBindings::TemplateBinding* right =
            i < rhs.templates.size() ? &rhs.templates[i] : nullptr;
        bool left_bound = left && left->bound;
        bool right_bound = right && right->bound;
        if (left_bound != right_bound) {
            return false;
        }
        if (left_bound &&
            !template_template_arguments_equivalent(left->argument,
                                                    right->argument)) {
            return false;
        }
    }
    if (lhs.pending_exception_matches.size() !=
        rhs.pending_exception_matches.size()) {
        return false;
    }
    for (size_t i = 0; i < lhs.pending_exception_matches.size(); ++i) {
        const PatternBindings::PendingExceptionMatch& left =
            lhs.pending_exception_matches[i];
        const PatternBindings::PendingExceptionMatch& right =
            rhs.pending_exception_matches[i];
        if (left.policy != right.policy ||
            left.pattern.kind != right.pattern.kind ||
            left.argument.kind != right.argument.kind ||
            !template_value_exprs_equivalent(left.pattern.predicate,
                                             right.pattern.predicate) ||
            !template_value_exprs_equivalent(left.argument.predicate,
                                             right.argument.predicate)) {
            return false;
        }
    }
    return true;
}

bool Session::deduce_overload_set_argument(cir::TypeId parameter_type,
                                           const ExprResult& argument,
                                           PatternBindings& bindings,
                                           SrcLoc loc) {
    std::shared_ptr<const OverloadDesignator> designator =
        canonical_overload_designator(argument);
    if (!designator || designator->candidates.empty()) {
        return true;
    }
    std::vector<OverloadDesignatorCandidate> candidates;
    candidates.reserve(designator->candidates.size());
    bool retains_function_template = false;
    for (const OverloadDesignatorCandidate& entry : designator->candidates) {
        cir::EntityId candidate = entry.entity;
        const TemplateInfo* info =
            candidate.valid() ? template_info(candidate) : nullptr;
        if (!info) {
            candidates.push_back(entry);
            continue;
        }

        if (!designator->has_explicit_template_arguments ||
            !tstate().function_template_instantiation_callback_) {
            retains_function_template = true;
            continue;
        }
        const std::vector<TemplateArgument>* explicit_arguments =
            &designator->explicit_template_arguments;
        auto candidate_arguments = std::find_if(
            designator->candidate_explicit_template_arguments.begin(),
            designator->candidate_explicit_template_arguments.end(),
            [&](const CandidateExplicitTemplateArguments& entry) {
                return entry.template_entity == candidate;
            });
        if (candidate_arguments !=
            designator->candidate_explicit_template_arguments.end()) {
            if (!candidate_arguments->viable) {
                continue;
            }
            explicit_arguments = &candidate_arguments->arguments;
        }
        TemplateArgumentBindings argument_bindings;
        if (!bind_explicit_template_arguments_prefix_to_parameters(
                info->parameters,
                *explicit_arguments,
                argument_bindings,
                nullptr,
                TemplateArgumentBindingMode::FunctionExplicitPrefix)) {
            continue;
        }
        bool needs_further_deduction = false;
        for (size_t i = 0; i < info->parameters.size(); ++i) {
            const TemplateParameter& parameter = info->parameters[i];
            if (argument_bindings[i].is_unbound() &&
                !parameter.is_parameter_pack &&
                !parameter.default_argument.has_value()) {
                needs_further_deduction = true;
                break;
            }
        }
        if (needs_further_deduction) {
            retains_function_template = true;
            continue;
        }
        PatternInstantiationCallbacks callbacks;
        if (tstate().pattern_instantiation_callback_configurator_) {
            tstate().pattern_instantiation_callback_configurator_(
                callbacks, loc);
        }
        callbacks.point_lookup_generation = designator->lookup_generation;
        if (!complete_template_argument_bindings_with_defaults(
                *info,
                argument_bindings,
                nullptr,
                &callbacks,
                loc,
                TemplateArgumentCompletionMode::Candidate)) {
            continue;
        }
        cir::EntityId specialization =
            tstate().function_template_instantiation_callback_(
                *info, argument_bindings, loc);
        if (specialization.valid() && file_.valid(specialization)) {
            OverloadDesignatorCandidate resolved = entry;
            resolved.entity = specialization;
            candidates.push_back(resolved);
        }
    }
    if (retains_function_template) {
        return true;
    }

    bool saw_success = false;
    PatternBindings selected;
    for (const OverloadDesignatorCandidate& entry : candidates) {
        cir::EntityId candidate = entry.entity;
        if (!candidate.valid() || !file_.valid(candidate)) {
            continue;
        }

        if (const cir::RecordMethodFact* method =
                file_.method_fact(candidate);
            method &&
            (method->constraint_satisfaction ==
                 cir::ConstraintSatisfactionKind::Unsatisfied ||
             method->constraint_satisfaction ==
                 cir::ConstraintSatisfactionKind::Invalid)) {
            continue;
        }
        const cir::Entity& entity = file_.entity(candidate);
        cir::EntityKind kind = entity.kind;
        if (entry.address_category ==
            OverloadAddressCategory::MemberPointer) {
            if (!designator->address_of_written ||
                !designator->qualified_name ||
                designator->address_operand_parenthesized) {
                continue;
            }
            if (kind != cir::EntityKind::Method) {
                continue;
            }
            const cir::RecordMethodFact* method = file_.method_fact(candidate);
            if (!method || method->is_static || !entity.parent.valid() ||
                !file_.valid(entity.parent)) {
                continue;
            }
            ExprResult single = argument;
            single.entity = candidate;
            single.candidates.clear();
            single.overload_designator.reset();
            single.type = member_pointer_type(file_.type_ref(
                                                  file_.entity(entity.parent).type),
                                              method->type);
            single.category = ValueCategory::PrValue;
            PatternBindings trial = bindings;
            if (!deduce_call_argument(parameter_type, single, trial, loc)) {
                continue;
            }
            if (!saw_success) {
                selected = std::move(trial);
                saw_success = true;
                continue;
            }
            if (!pattern_bindings_equivalent(selected, trial)) {
                return true;
            }
            continue;
        }
        if (kind != cir::EntityKind::Function &&
            kind != cir::EntityKind::Method) {
            continue;
        }
        ExprResult single = argument;
        single.entity = candidate;
        single.candidates.clear();
        single.overload_designator.reset();
        if (designator->address_of_written) {
            single.type = pointer_type(file_.type_ref(entity.type));
            single.category = ValueCategory::PrValue;
        } else {
            single.type = entity.type;

            single.category = ValueCategory::LValue;
        }
        PatternBindings trial = bindings;
        if (!deduce_call_argument(parameter_type, single, trial, loc)) {
            continue;
        }
        if (!saw_success) {
            selected = std::move(trial);
            saw_success = true;
            continue;
        }
        if (!pattern_bindings_equivalent(selected, trial)) {
            return true;
        }
    }
    if (saw_success) {
        bindings = std::move(selected);
    }
    return true;
}

void Session::populate_enclosing_type_pack_bindings(
    const TemplateInfo& info,
    PatternBindings& bindings) const {
    auto append_binding = [&](const std::vector<TemplateParameter>& parameters,
                              const TemplateArgumentBindings&
                                  argument_bindings) {
        for (size_t i = 0; i < parameters.size(); ++i) {
            const TemplateParameter& parameter = parameters[i];
            if (parameter.kind != TemplateParameterKind::Type ||
                !parameter.is_parameter_pack ||
                !parameter.type_param_type.valid() ||
                i >= argument_bindings.size() ||
                !argument_bindings[i].is_pack()) {
                continue;
            }
            cir::TypeId pattern_type =
                file_.resolved_type(parameter.type_param_type);
            bool aliases_local_parameter = std::any_of(
                info.parameters.begin(),
                info.parameters.end(),
                [&](const TemplateParameter& local) {
                    return local.kind == TemplateParameterKind::Type &&
                        local.type_param_type.valid() &&
                        same_type_parameter_identity(
                            file_, pattern_type, local.type_param_type);
                });
            if (aliases_local_parameter) {

                continue;
            }
            auto existing = std::find_if(
                bindings.fixed_type_packs.begin(),
                bindings.fixed_type_packs.end(),
                [&](const PatternBindings::FixedTypePack& pack) {
                    return pack.pattern_type == pattern_type;
                });
            if (existing == bindings.fixed_type_packs.end()) {
                bindings.fixed_type_packs.push_back(
                    PatternBindings::FixedTypePack{
                        pattern_type,
                        argument_bindings[i].arguments});
            }
        }
    };
    for (const TemplateInfo::TemplateInstantiationBinding& enclosing :
         info.enclosing_instantiation_bindings) {
        append_binding(enclosing.parameters, enclosing.argument_bindings);
    }

    cir::EntityId owner = info.entity.valid() && file_.valid(info.entity)
        ? file_.entity(info.entity).parent
        : cir::EntityId{};
    std::unordered_set<uint32_t> visited;
    while (owner.valid() && file_.valid(owner) &&
           visited.insert(static_cast<uint32_t>(owner.index)).second) {
        if (const cir::TemplateSpecializationFact* fact =
                file_.template_specialization(owner)) {
            if (const TemplateInfo* owner_info =
                    template_info(fact->template_entity)) {
                append_binding(owner_info->parameters,
                               fact->argument_bindings);
            }
        }
        owner = file_.entity(owner).parent;
    }
}

bool Session::deduce_template_arguments(
    const TemplateInfo& info,
    const std::vector<ExprResult>& arguments,
    std::vector<TemplateArgument>& deduced,
    const std::vector<TemplateArgument>* explicit_arguments,
    PatternInstantiationCallbacks* callbacks,
    TemplateArgumentBindings* deduced_bindings,
    SrcLoc loc,
    const std::vector<uint8_t>* parameter_default_argument_flags) {
    PatternInstantiationCallbacks configured_callbacks;

    if (!callbacks &&
        tstate().pattern_instantiation_callback_configurator_) {
        tstate().pattern_instantiation_callback_configurator_(
            configured_callbacks, loc);
        callbacks = &configured_callbacks;
    }
    if (info.is_class_template || !info.pattern_type.valid()) {
        return false;
    }
    const auto* pattern = std::get_if<cir::FunctionTypePayload>(
        &file_.type_payload(file_.resolved_type(info.pattern_type)));
    if (!pattern) {
        return false;
    }
    auto parameter_has_default_argument = [&](size_t index) {
        if (parameter_default_argument_flags &&
            index < parameter_default_argument_flags->size() &&
            (*parameter_default_argument_flags)[index] != 0) {
            return true;
        }
        if (info.pattern_function.valid() &&
            file_.valid(info.pattern_function)) {
            cir::EntityId pattern_entity =
                file_.function(info.pattern_function).entity;
            if (callable_default_argument(pattern_entity, index)) {
                return true;
            }
        }
        return callable_default_argument(info.entity, index) != nullptr;
    };
    size_t minimum_parameters = pattern->parameters.size();
    while (minimum_parameters > 0 &&
           parameter_has_default_argument(minimum_parameters - 1)) {
        --minimum_parameters;
    }
    PatternBindings bindings;
    bindings.types.resize(info.parameters.size());
    bindings.values.resize(info.parameters.size());
    bindings.templates.resize(info.parameters.size());
    bindings.pack_arguments.resize(info.parameters.size());
    bindings.template_parameters = &info.parameters;
    populate_enclosing_type_pack_bindings(info, bindings);
    bindings.explicit_types.resize(info.parameters.size(), false);
    bindings.explicit_values.resize(info.parameters.size(), false);
    bindings.explicit_templates.resize(info.parameters.size(), false);

    bool has_trailing_pack = !pattern->parameters.empty() &&
        pattern->parameter_pack_flags.size() == pattern->parameters.size() &&
        pattern->parameter_pack_flags.back() != 0;
    bool has_nontrailing_pack =
        pattern->parameter_pack_flags.size() == pattern->parameters.size() &&
        std::any_of(pattern->parameter_pack_flags.begin(),
                    pattern->parameter_pack_flags.end() -
                        (has_trailing_pack ? 1 : 0),
                    [](uint8_t flag) { return flag != 0; });

    TemplateArgumentBindings argument_bindings;
    if (explicit_arguments) {
        if (!bind_explicit_template_arguments_prefix_to_parameters(
                info.parameters,
                *explicit_arguments,
                argument_bindings,
                nullptr,
                TemplateArgumentBindingMode::FunctionExplicitPrefix)) {
            return false;
        }

    } else {
        argument_bindings.resize(info.parameters.size());
    }

    size_t fixed_parameters = has_trailing_pack
        ? pattern->parameters.size() - 1
        : pattern->parameters.size();
    if (has_nontrailing_pack && !has_trailing_pack) {

        size_t argument_index = 0;
        for (size_t parameter_index = 0;
             parameter_index < pattern->parameters.size();
             ++parameter_index) {
            bool is_pack =
                pattern->parameter_pack_flags[parameter_index] != 0;
            if (is_pack) {
                size_t element_count = 0;
                if (std::optional<uint32_t> pack_index =
                        type_parameter_pack_index(
                            pattern->parameters[parameter_index].type)) {
                    if (*pack_index < argument_bindings.size() &&
                        argument_bindings[*pack_index].is_pack()) {
                        element_count =
                            argument_bindings[*pack_index].arguments.size();
                    } else if (*pack_index < info.parameters.size() &&
                               info.parameters[*pack_index]
                                   .is_parameter_pack &&
                               argument_bindings[*pack_index].is_unbound()) {
                        argument_bindings[*pack_index].kind =
                            TemplateArgumentBindingKind::Pack;
                    }
                }
                if (argument_index + element_count > arguments.size()) {
                    return false;
                }
                argument_index += element_count;
                continue;
            }
            if (argument_index >= arguments.size()) {
                if (parameter_has_default_argument(parameter_index)) {
                    continue;
                }
                return false;
            }
            cir::TypeId parameter_type = deduction_pattern_type(
                *this, pattern->parameters[parameter_index].type);
            bool participates_in_deduction = false;
            for (size_t template_index = 0;
                 template_index < info.parameters.size();
                 ++template_index) {
                if (!argument_bindings[template_index].is_unbound()) {
                    continue;
                }
                if (template_parameter_is_deducible_from_type(
                        info.parameters[template_index], parameter_type)) {
                    participates_in_deduction = true;
                    break;
                }
            }
            if (participates_in_deduction &&
                !deduce_call_argument(parameter_type,
                                      arguments[argument_index],
                                      bindings,
                                      loc)) {
                return false;
            }
            ++argument_index;
        }
        if (argument_index != arguments.size()) {
            return false;
        }
    } else if (has_trailing_pack) {
        if (arguments.size() <
            std::min(minimum_parameters, fixed_parameters)) {
            return false;
        }
    } else if (arguments.size() < minimum_parameters ||
               (!pattern->is_variadic &&
                arguments.size() > pattern->parameters.size())) {
        return false;
    }
    for (size_t i = 0; i < argument_bindings.size(); ++i) {
        if (!argument_bindings[i].is_single() ||
            argument_bindings[i].arguments.empty()) {
            continue;
        }
        const TemplateArgument& argument =
            argument_bindings[i].arguments.front();
        if (i >= info.parameters.size()) {
            return false;
        }
        if (info.parameters[i].kind == TemplateParameterKind::Type &&
            argument.kind == cir::TemplateArgumentKind::Type) {
            bindings.types[i] = argument.type;
            bindings.explicit_types[i] = true;
        } else if (info.parameters[i].kind == TemplateParameterKind::NonType &&
                   argument.kind == cir::TemplateArgumentKind::Value) {
            bindings.values[i].bound = true;
            bindings.values[i].argument = argument;
            bindings.explicit_values[i] = true;
        } else if (info.parameters[i].kind == TemplateParameterKind::Template &&
                   argument.kind == cir::TemplateArgumentKind::Template) {
            bindings.templates[i].bound = true;
            bindings.templates[i].argument = argument;
            bindings.explicit_templates[i] = true;
        }
    }

    for (size_t i = 0;
         !has_nontrailing_pack && i < arguments.size() &&
             i < fixed_parameters;
         ++i) {
        cir::TypeRef parameter = pattern->parameters[i];
        cir::TypeId parameter_type =
            deduction_pattern_type(*this, parameter.type);
        bool participates_in_deduction = false;
        for (size_t parameter_index = 0;
             parameter_index < info.parameters.size();
             ++parameter_index) {
            if (!argument_bindings[parameter_index].is_unbound()) {
                continue;
            }
            if (template_parameter_is_deducible_from_type(
                    info.parameters[parameter_index], parameter_type)) {
                participates_in_deduction = true;
                break;
            }
        }

        if (!participates_in_deduction) {
            continue;
        }
        if (!deduce_call_argument(parameter_type,
                                  arguments[i],
                                  bindings,
                                  loc)) {
            return false;
        }
    }
    if (has_trailing_pack) {

        cir::TypeId pack_pattern =
            file_.resolved_type(pattern->parameters.back().type);
        std::vector<size_t> pack_indices;
        for (size_t i = 0; i < info.parameters.size(); ++i) {
            if (info.parameters[i].is_parameter_pack &&
                template_parameter_is_deducible_from_type(info.parameters[i],
                                                           pack_pattern)) {
                pack_indices.push_back(i);
            }
        }
        if (pack_indices.empty()) {
            return false;
        }

        std::optional<size_t> explicit_pack_elements;
        std::vector<std::vector<TemplateArgument>> pack_arguments;
        pack_arguments.reserve(pack_indices.size());
        for (size_t pack_index : pack_indices) {
            if (argument_bindings[pack_index].is_pack()) {
                size_t count =
                    argument_bindings[pack_index].arguments.size();
                if (explicit_pack_elements.has_value() &&
                    *explicit_pack_elements != count) {
                    return false;
                }
                explicit_pack_elements = count;
            } else if (!argument_bindings[pack_index].is_unbound()) {
                return false;
            }
            pack_arguments.push_back(
                argument_bindings[pack_index].arguments);
        }
        size_t explicit_count = explicit_pack_elements.value_or(0);
        if (arguments.size() <
            fixed_parameters + explicit_count) {
            return false;
        }
        for (std::vector<TemplateArgument>& elements : pack_arguments) {
            elements.reserve(arguments.size() - fixed_parameters);
        }
        for (size_t i = fixed_parameters + explicit_count;
             i < arguments.size();
             ++i) {

            PatternBindings element_bindings = bindings;
            element_bindings.expansion_element_index =
                i - fixed_parameters;
            element_bindings.expansion_element_count =
                arguments.size() - fixed_parameters;
            if (!deduce_call_argument(pack_pattern,
                                      arguments[i],
                                      element_bindings,
                                      loc)) {
                return false;
            }
            if (!reconcile_deduced_value_parameter_types(info,
                                                         element_bindings)) {
                return false;
            }
            for (size_t pack_slot = 0;
                 pack_slot < pack_indices.size();
                 ++pack_slot) {
                size_t pack_index = pack_indices[pack_slot];
                TemplateArgument element;
                switch (info.parameters[pack_index].kind) {
                    case TemplateParameterKind::Type:
                        if (!element_bindings.types[pack_index].valid()) {
                            return false;
                        }
                        element.kind = cir::TemplateArgumentKind::Type;
                        element.type = element_bindings.types[pack_index];
                        break;
                    case TemplateParameterKind::NonType:
                        if (!element_bindings.values[pack_index].bound) {
                            return false;
                        }
                        element =
                            element_bindings.values[pack_index].argument;
                        break;
                    case TemplateParameterKind::Template:
                        if (!element_bindings.templates[pack_index].bound) {
                            return false;
                        }
                        element =
                            element_bindings.templates[pack_index].argument;
                        break;
                }
                element.expands_parameter_pack = false;
                pack_arguments[pack_slot].push_back(std::move(element));
            }
        }
        for (size_t pack_slot = 0;
             pack_slot < pack_indices.size();
             ++pack_slot) {
            size_t pack_index = pack_indices[pack_slot];
            argument_bindings[pack_index].kind =
                TemplateArgumentBindingKind::Pack;
            argument_bindings[pack_index].arguments =
                std::move(pack_arguments[pack_slot]);
        }
    }
    if (!reconcile_deduced_value_parameter_types(info, bindings)) {
        return false;
    }
    if (bindings.types.size() > info.parameters.size() ||
        bindings.values.size() > info.parameters.size() ||
        bindings.templates.size() > info.parameters.size()) {
        return false;
    }

    for (size_t i = 0; i < info.parameters.size(); ++i) {
        if (!argument_bindings[i].is_unbound()) {
            continue;
        }
        if (info.parameters[i].is_parameter_pack &&
            i < bindings.pack_arguments.size() &&
            bindings.pack_arguments[i].has_value()) {
            argument_bindings[i].kind =
                TemplateArgumentBindingKind::Pack;
            argument_bindings[i].arguments =
                *bindings.pack_arguments[i];
            continue;
        }
        TemplateArgument argument;
        if (info.parameters[i].kind == TemplateParameterKind::Type) {
            if (!bindings.types[i].valid()) {
                continue;
            }
            argument.kind = cir::TemplateArgumentKind::Type;
            argument.type = bindings.types[i];
        } else if (info.parameters[i].kind == TemplateParameterKind::NonType) {
            if (!bindings.values[i].bound) {
                continue;
            }
            argument = bindings.values[i].argument;
            cir::TypeId value_type = info.parameters[i].non_type_type.valid()
                ? info.parameters[i].non_type_type
                : builder_.int_type();
            if (!argument.value_type.type.valid()) {
                argument.value_type = cir::TypeRef{value_type,
                                                   cir::QualNone,
                                                   cir::MemorySpace::Default};
            }
        } else if (info.parameters[i].kind == TemplateParameterKind::Template) {
            if (!bindings.templates[i].bound) {
                continue;
            }
            argument = bindings.templates[i].argument;
        } else {
            continue;
        }
        argument_bindings[i].kind = TemplateArgumentBindingKind::Single;
        argument_bindings[i].arguments = {std::move(argument)};
    }
    if (!complete_template_argument_bindings_with_defaults(
            info,
            argument_bindings,
            nullptr,
            callbacks,
            loc,
            TemplateArgumentCompletionMode::Candidate)) {
        return false;
    }
    if (!finalize_pending_exception_matches(bindings,
                                            argument_bindings,
                                            callbacks)) {
        return false;
    }
    deduced = flatten_template_argument_bindings(argument_bindings);
    if (deduced_bindings) {
        *deduced_bindings = std::move(argument_bindings);
    }
    return true;
}

bool Session::deduce_conversion_template_arguments(
    const TemplateInfo& info,
    cir::TypeId target_type,
    std::vector<TemplateArgument>& deduced,
    TemplateArgumentBindings* deduced_bindings) {
    if (info.is_class_template || !info.pattern_type.valid() ||
        !target_type.valid()) {
        return false;
    }
    const auto* pattern = std::get_if<cir::FunctionTypePayload>(
        &file_.type_payload(file_.resolved_type(info.pattern_type)));
    if (!pattern) {
        return false;
    }

    cir::TypeRef parameter = pattern->return_type;
    parameter.type = file_.resolved_type(parameter.type);
    cir::TypeRef argument = file_.type_ref(target_type);
    argument.type = file_.resolved_type(argument.type);
    if (!file_.valid(parameter.type) || !file_.valid(argument.type)) {
        return false;
    }

    cir::TypeKind parameter_kind = file_.type(parameter.type).kind;
    if (is_reference_kind(parameter_kind)) {
        parameter = file_.reference_referred_ref(parameter.type);
        parameter.type = file_.resolved_type(parameter.type);
        if (!file_.valid(parameter.type)) {
            return false;
        }
        parameter_kind = file_.type(parameter.type).kind;
    }

    cir::TypeKind original_argument_kind = file_.type(argument.type).kind;
    bool original_argument_is_reference =
        is_reference_kind(original_argument_kind);
    auto is_potentially_throwing_function_pointer =
        [&](cir::TypeId type) {
            type = file_.resolved_type(type);
            if (!file_.valid(type)) {
                return false;
            }
            cir::TypeRef function_ref;
            if (file_.type(type).kind == cir::TypeKind::Pointer) {
                function_ref = file_.pointer_pointee_ref(type);
            } else if (file_.type(type).kind ==
                       cir::TypeKind::MemberPointer) {
                const auto* member =
                    std::get_if<cir::MemberPointerTypePayload>(
                        &file_.type_payload(type));
                if (member) {
                    function_ref = member->member_type;
                }
            }
            cir::TypeId function = file_.resolved_type(function_ref.type);
            if (!file_.valid(function) ||
                file_.type(function).kind != cir::TypeKind::Function) {
                return false;
            }
            const auto* payload =
                std::get_if<cir::FunctionTypePayload>(
                    &file_.type_payload(function));
            return payload &&
                   payload->exception_spec.kind ==
                       cir::FunctionExceptionSpecKind::PotentiallyThrowing;
        };
    bool may_ignore_exception_spec =
        is_potentially_throwing_function_pointer(argument.type);

    if (original_argument_is_reference) {
        argument = file_.reference_referred_ref(argument.type);
        argument.type = file_.resolved_type(argument.type);
    } else if (parameter_kind == cir::TypeKind::Array) {
        const auto* array = std::get_if<cir::ArrayTypePayload>(
            &file_.type_payload(parameter.type));
        if (!array) {
            return false;
        }
        parameter = file_.type_ref(file_.pointer_type(array->element_type));
    } else if (parameter_kind == cir::TypeKind::Function) {
        parameter = file_.type_ref(file_.pointer_type(parameter));
    } else {
        constexpr uint8_t cv_mask = cir::QualConst | cir::QualVolatile;
        parameter.qualifiers = static_cast<uint8_t>(
            parameter.qualifiers & static_cast<uint8_t>(~cv_mask));
    }
    if (!original_argument_is_reference) {
        constexpr uint8_t cv_mask = cir::QualConst | cir::QualVolatile;
        argument.qualifiers = static_cast<uint8_t>(
            argument.qualifiers & static_cast<uint8_t>(~cv_mask));
    }
    if (!file_.valid(parameter.type) || !file_.valid(argument.type)) {
        return false;
    }

    auto make_bindings = [&]() {
        PatternBindings result;
        result.types.resize(info.parameters.size());
        result.values.resize(info.parameters.size());
        result.templates.resize(info.parameters.size());
        return result;
    };

    PatternBindings bindings = make_bindings();
    if (!unify_type_ref_pattern(parameter, argument, bindings)) {
        enum Alternative : uint8_t {
            IgnoreReferenceCv = 1 << 0,
            IgnoreExceptionSpec = 1 << 1,
            AllowQualificationConversion = 1 << 2,
        };
        uint8_t available = AllowQualificationConversion;
        if (original_argument_is_reference) {
            available = static_cast<uint8_t>(available |
                                             IgnoreReferenceCv);
        }
        if (may_ignore_exception_spec) {
            available = static_cast<uint8_t>(available |
                                             IgnoreExceptionSpec);
        }

        bool saw_success = false;
        PatternBindings selected;
        for (uint8_t mask = 1; mask < 8; ++mask) {
            if ((mask & static_cast<uint8_t>(~available)) != 0) {
                continue;
            }
            cir::TypeRef trial_parameter = parameter;
            cir::TypeRef trial_argument = argument;
            if ((mask & IgnoreReferenceCv) != 0) {
                constexpr uint8_t cv_mask =
                    cir::QualConst | cir::QualVolatile;
                trial_parameter.qualifiers = static_cast<uint8_t>(
                    trial_parameter.qualifiers &
                    static_cast<uint8_t>(~cv_mask));
                trial_argument.qualifiers = static_cast<uint8_t>(
                    trial_argument.qualifiers &
                    static_cast<uint8_t>(~cv_mask));
            }

            bool allow_qualification =
                (mask & AllowQualificationConversion) != 0;
            if (allow_qualification) {
                QualificationConversionAnalysis qualification =
                    analyze_qualification_conversion(
                        trial_parameter,
                        trial_argument,
                        QualificationTargetKind::TypePattern);
                if (!qualification.has_indirection ||
                    !qualification.similar || !qualification.allowed) {
                    continue;
                }
            }
            TypePatternExceptionMatch exception_match =
                (mask & IgnoreExceptionSpec) != 0
                    ? TypePatternExceptionMatch::
                          PatternToArgumentFunctionPointerConversion
                    : TypePatternExceptionMatch::Exact;
            PatternBindings trial = make_bindings();
            if (!unify_type_ref_pattern(trial_parameter,
                                        trial_argument,
                                        trial,
                                        exception_match,
                                        allow_qualification)) {
                continue;
            }
            if (!saw_success) {
                selected = std::move(trial);
                saw_success = true;
            } else if (!pattern_bindings_equivalent(selected, trial)) {
                return false;
            }
        }
        if (!saw_success) {
            return false;
        }
        bindings = std::move(selected);
    }

    if (!reconcile_deduced_value_parameter_types(info, bindings)) {
        return false;
    }

    TemplateArgumentBindings argument_bindings(info.parameters.size());
    for (size_t i = 0; i < info.parameters.size(); ++i) {
        TemplateArgument argument_value;
        if (info.parameters[i].kind == TemplateParameterKind::Type) {
            if (!bindings.types[i].valid()) {
                continue;
            }
            argument_value.kind = cir::TemplateArgumentKind::Type;
            argument_value.type = bindings.types[i];
        } else if (info.parameters[i].kind == TemplateParameterKind::NonType) {
            if (!bindings.values[i].bound) {
                continue;
            }
            argument_value = bindings.values[i].argument;
            cir::TypeId value_type = info.parameters[i].non_type_type.valid()
                ? info.parameters[i].non_type_type
                : file_.builtin_type(cir::BuiltinTypeKind::Int);
            if (!argument_value.value_type.type.valid()) {
                argument_value.value_type =
                    cir::TypeRef{value_type,
                                 cir::QualNone,
                                 cir::MemorySpace::Default};
            }
        } else if (info.parameters[i].kind == TemplateParameterKind::Template) {
            if (!bindings.templates[i].bound) {
                continue;
            }
            argument_value = bindings.templates[i].argument;
        } else {
            continue;
        }
        argument_bindings[i].kind = TemplateArgumentBindingKind::Single;
        argument_bindings[i].arguments = {std::move(argument_value)};
    }
    if (!complete_template_argument_bindings_with_defaults(
            info,
            argument_bindings,
            nullptr,
            nullptr,
            SrcLoc(),
            TemplateArgumentCompletionMode::Candidate)) {
        return false;
    }
    if (!finalize_pending_exception_matches(bindings,
                                            argument_bindings)) {
        return false;
    }
    deduced = flatten_template_argument_bindings(argument_bindings);
    if (deduced_bindings) {
        *deduced_bindings = std::move(argument_bindings);
    }
    return true;
}

bool Session::deduce_function_template_address_arguments(
    const TemplateInfo& info,
    cir::TypeId target_function_type,
    std::vector<TemplateArgument>& deduced,
    const std::vector<TemplateArgument>* explicit_arguments,
    PatternInstantiationCallbacks* callbacks,
    SrcLoc loc,
    TypePatternExceptionMatch exception_match,
    TypePatternReturnMatch return_match,
    TemplateArgumentBindings* deduced_bindings) {
    if (info.is_class_template || !info.pattern_type.valid() ||
        !target_function_type.valid()) {
        return false;
    }

    cir::TypeId pattern_type = file_.resolved_type(info.pattern_type);
    cir::TypeId target_type = file_.resolved_type(target_function_type);
    if (!file_.valid(pattern_type) || !file_.valid(target_type) ||
        file_.type(pattern_type).kind != cir::TypeKind::Function ||
        file_.type(target_type).kind != cir::TypeKind::Function) {
        return false;
    }

    PatternBindings bindings;
    bindings.types.resize(info.parameters.size());
    bindings.values.resize(info.parameters.size());
    bindings.templates.resize(info.parameters.size());
    bindings.pack_arguments.resize(info.parameters.size());
    bindings.template_parameters = &info.parameters;
    populate_enclosing_type_pack_bindings(info, bindings);
    bindings.explicit_types.resize(info.parameters.size(), false);
    bindings.explicit_values.resize(info.parameters.size(), false);
    bindings.explicit_templates.resize(info.parameters.size(), false);

    TemplateArgumentBindings argument_bindings;
    if (explicit_arguments) {
        if (!bind_explicit_template_arguments_prefix_to_parameters(
                info.parameters,
                *explicit_arguments,
                argument_bindings,
                nullptr,
                TemplateArgumentBindingMode::FunctionExplicitPrefix)) {
            return false;
        }
    } else {
        argument_bindings.resize(info.parameters.size());
    }
    for (size_t i = 0; i < argument_bindings.size(); ++i) {
        if (!argument_bindings[i].is_single() ||
            argument_bindings[i].arguments.empty()) {
            continue;
        }
        const TemplateArgument& argument =
            argument_bindings[i].arguments.front();
        if (i >= info.parameters.size()) {
            return false;
        }
        if (info.parameters[i].kind == TemplateParameterKind::Type &&
            argument.kind == cir::TemplateArgumentKind::Type) {
            bindings.types[i] = argument.type;
            bindings.explicit_types[i] = true;
        } else if (info.parameters[i].kind == TemplateParameterKind::NonType &&
                   argument.kind == cir::TemplateArgumentKind::Value) {
            bindings.values[i].bound = true;
            bindings.values[i].argument = argument;
            bindings.explicit_values[i] = true;
        } else if (info.parameters[i].kind == TemplateParameterKind::Template &&
                   argument.kind == cir::TemplateArgumentKind::Template) {
            bindings.templates[i].bound = true;
            bindings.templates[i].argument = argument;
            bindings.explicit_templates[i] = true;
        }
    }

    if (!unify_type_pattern(pattern_type,
                            target_type,
                            bindings,
                            exception_match,
                            /*allow_qualification_conversion=*/false,
                            return_match,
                            TypePatternParameterMatch::
                                AdjustForwardingReferencesAtCurrentFunction)) {
        return false;
    }
    if (!reconcile_deduced_value_parameter_types(info, bindings)) {
        return false;
    }
    if (bindings.types.size() > info.parameters.size() ||
        bindings.values.size() > info.parameters.size() ||
        bindings.templates.size() > info.parameters.size()) {
        return false;
    }

    for (size_t i = 0; i < info.parameters.size(); ++i) {
        if (!argument_bindings[i].is_unbound()) {
            continue;
        }
        if (info.parameters[i].is_parameter_pack &&
            i < bindings.pack_arguments.size() &&
            bindings.pack_arguments[i].has_value()) {
            argument_bindings[i].kind =
                TemplateArgumentBindingKind::Pack;
            argument_bindings[i].arguments =
                *bindings.pack_arguments[i];
            continue;
        }
        TemplateArgument argument;
        if (info.parameters[i].kind == TemplateParameterKind::Type) {
            if (!bindings.types[i].valid()) {
                continue;
            }
            argument.kind = cir::TemplateArgumentKind::Type;
            argument.type = bindings.types[i];
        } else if (info.parameters[i].kind == TemplateParameterKind::NonType) {
            if (!bindings.values[i].bound) {
                continue;
            }
            argument = bindings.values[i].argument;
            cir::TypeId value_type = info.parameters[i].non_type_type.valid()
                ? info.parameters[i].non_type_type
                : builder_.int_type();
            if (!argument.value_type.type.valid()) {
                argument.value_type = cir::TypeRef{value_type,
                                                   cir::QualNone,
                                                   cir::MemorySpace::Default};
            }
        } else if (info.parameters[i].kind == TemplateParameterKind::Template) {
            if (!bindings.templates[i].bound) {
                continue;
            }
            argument = bindings.templates[i].argument;
        } else {
            continue;
        }
        argument_bindings[i].kind = TemplateArgumentBindingKind::Single;
        argument_bindings[i].arguments = {std::move(argument)};
    }
    if (!complete_template_argument_bindings_with_defaults(
            info,
            argument_bindings,
            nullptr,
            callbacks,
            loc,
            TemplateArgumentCompletionMode::Candidate)) {
        return false;
    }
    if (!finalize_pending_exception_matches(bindings,
                                            argument_bindings,
                                            callbacks)) {
        return false;
    }
    deduced = flatten_template_argument_bindings(argument_bindings);
    if (deduced_bindings) {
        *deduced_bindings = std::move(argument_bindings);
    }
    return true;
}

Session::PartialSpecializationSelection
Session::select_template_partial_specialization(
    const TemplateInfo& primary,
    const std::vector<TemplateArgument>& arguments,
    const PartialSpecializationConstraintPredicate& constraint_satisfied,
    const PartialSpecializationCandidatePredicate& candidate_viable) {
    PartialSpecializationSelection selection;
    if ((!primary.is_class_template && !primary.is_variable_template) ||
        primary.is_partial_specialization ||
        primary.partial_specializations.empty()) {
        return selection;
    }
    bump_deduce_counter(PerfCounter::PartialSpecSelections);
    bool has_constrained_partial = false;
    for (const TemplateInfo::PartialSpecialization& partial_entry :
         primary.partial_specializations) {
        const TemplateInfo* partial = template_info(partial_entry.entity);
        if (partial && !partial->introduced_constraints.empty()) {
            has_constrained_partial = true;
            break;
        }
    }

    if ((has_constrained_partial && constraint_satisfied) ||
        candidate_viable) {
        return select_template_partial_specialization_uncached(
            primary,
            arguments,
            constraint_satisfied,
            candidate_viable);
    }

    std::string key = template_memo_key(primary.entity, arguments);
    uint64_t partial_count = primary.partial_specializations.size();
    char count_bytes[sizeof(partial_count)];
    std::memcpy(count_bytes, &partial_count, sizeof(partial_count));
    key.append(count_bytes, sizeof(count_bytes));
    auto found = tstate().partial_spec_selection_cache_.find(key);
    if (found != tstate().partial_spec_selection_cache_.end()) {
        return found->second;
    }
    selection =
        select_template_partial_specialization_uncached(primary,
                                                         arguments,
                                                         {},
                                                         {});
    auto [it, inserted] = tstate().partial_spec_selection_cache_.emplace(key, selection);
    if (inserted && is_speculative_parsing()) {
        track_speculative_rollback(
            [this, key] { tstate().partial_spec_selection_cache_.erase(key); });
    }
    return selection;
}

Session::TemplateArgumentListDeductionResult
Session::deduce_template_argument_list(
    const std::vector<TemplateParameter>& pattern_parameters,
    const std::vector<TemplateArgument>& pattern_arguments,
    const std::vector<TemplateArgument>& actual_arguments,
    PatternBindings& bindings,
    TemplateArgumentListDeductionMode mode,
    const std::vector<TemplateParameter>* actual_parameters) const {
    PatternBindings trial = bindings;
    const size_t parameter_count = pattern_parameters.size();
    trial.types.resize(std::max(trial.types.size(), parameter_count));
    trial.values.resize(std::max(trial.values.size(), parameter_count));
    trial.templates.resize(std::max(trial.templates.size(), parameter_count));
    trial.pack_arguments.resize(
        std::max(trial.pack_arguments.size(), parameter_count));
    trial.template_parameters = &pattern_parameters;

    auto match_one = [&](const TemplateArgument& pattern,
                         const TemplateArgument& actual,
                         PatternBindings& target) {
        TemplateArgument transformed_actual =
            mode == TemplateArgumentListDeductionMode::PartialOrdering
            ? transformed_partial_ordering_argument(actual, target)
            : actual;
        return template_argument_patterns_match(
            std::vector<TemplateArgument>{pattern},
            std::vector<TemplateArgument>{transformed_actual},
            target,
            &pattern_parameters,
            mode == TemplateArgumentListDeductionMode::PartialOrdering
                ? nullptr
                : actual_parameters);
    };
    auto reference_matches_parameter = [&](const cir::TemplateValuePackReference&
                                               reference,
                                           const TemplateParameter& parameter) {
        if (reference.index != parameter.index ||
            reference.depth != parameter.depth) {
            return false;
        }
        switch (parameter.kind) {
            case TemplateParameterKind::Type:
                return reference.kind == cir::TemplateValuePackKind::Type;
            case TemplateParameterKind::NonType:
                return reference.kind == cir::TemplateValuePackKind::Value;
            case TemplateParameterKind::Template:
                return reference.kind == cir::TemplateValuePackKind::Template;
        }
        return false;
    };
    auto argument_mentions_parameter = [&](const TemplateArgument& argument,
                                            const TemplateParameter& parameter) {
        if (argument.kind == cir::TemplateArgumentKind::Type) {
            return template_parameter_is_deducible_from_type(
                parameter, argument.type.type);
        }
        if (argument.kind == cir::TemplateArgumentKind::Value) {
            if (parameter.kind == TemplateParameterKind::NonType &&
                argument.value_param_index == parameter.index) {
                return true;
            }
            for (const cir::TemplateValueExprNode& node :
                 argument.dependent_value_expr.nodes) {
                if (parameter.kind == TemplateParameterKind::NonType &&
                    node.kind == cir::TemplateValueExprKind::Parameter &&
                    node.parameter_index == parameter.index) {
                    return true;
                }
                if (std::any_of(
                        node.pack_references.begin(),
                        node.pack_references.end(),
                        [&](const cir::TemplateValuePackReference& reference) {
                            return reference_matches_parameter(reference,
                                                               parameter);
                        })) {
                    return true;
                }
            }
            return false;
        }
        return parameter.kind == TemplateParameterKind::Template &&
               argument.template_param_index == parameter.index;
    };
    auto expansion_parameters = [&](const TemplateArgument& expansion) {
        std::vector<size_t> indices;
        for (size_t i = 0; i < parameter_count; ++i) {
            const TemplateParameter& parameter = pattern_parameters[i];
            if (parameter.is_parameter_pack &&
                argument_mentions_parameter(expansion, parameter)) {
                indices.push_back(i);
            }
        }
        return indices;
    };
    if (mode == TemplateArgumentListDeductionMode::PartialOrdering) {
        trial.partial_ordering_used_parameters.resize(parameter_count);
        for (size_t i = 0; i < parameter_count; ++i) {
            if (std::any_of(
                    pattern_arguments.begin(),
                    pattern_arguments.end(),
                    [&](const TemplateArgument& argument) {
                        return argument_mentions_parameter(
                            argument, pattern_parameters[i]);
                    })) {
                trial.partial_ordering_used_parameters[i] = true;
            }
        }
    }
    auto clear_element_binding = [&](PatternBindings& target,
                                     size_t parameter_index) {
        const TemplateParameter& parameter =
            pattern_parameters[parameter_index];
        switch (parameter.kind) {
            case TemplateParameterKind::Type:
                target.types[parameter_index] = {};
                if (parameter_index < target.explicit_types.size()) {
                    target.explicit_types[parameter_index] = false;
                }
                break;
            case TemplateParameterKind::NonType:
                target.values[parameter_index] = {};
                if (parameter_index < target.explicit_values.size()) {
                    target.explicit_values[parameter_index] = false;
                }
                break;
            case TemplateParameterKind::Template:
                target.templates[parameter_index] = {};
                if (parameter_index < target.explicit_templates.size()) {
                    target.explicit_templates[parameter_index] = false;
                }
                break;
        }
    };
    auto extract_element = [&](const PatternBindings& source,
                               size_t parameter_index,
                               bool symbolic)
        -> std::optional<TemplateArgument> {
        const TemplateParameter& parameter =
            pattern_parameters[parameter_index];
        TemplateArgument element;
        switch (parameter.kind) {
            case TemplateParameterKind::Type:
                if (parameter_index >= source.types.size() ||
                    !source.types[parameter_index].valid()) {
                    return std::nullopt;
                }
                element.kind = cir::TemplateArgumentKind::Type;
                element.type = source.types[parameter_index];
                break;
            case TemplateParameterKind::NonType:
                if (parameter_index >= source.values.size() ||
                    !source.values[parameter_index].bound) {
                    return std::nullopt;
                }
                element = source.values[parameter_index].argument;
                break;
            case TemplateParameterKind::Template:
                if (parameter_index >= source.templates.size() ||
                    !source.templates[parameter_index].bound) {
                    return std::nullopt;
                }
                element = source.templates[parameter_index].argument;
                break;
        }
        element.expands_parameter_pack = symbolic;
        element.expands_pack_pattern = false;
        return element;
    };

    std::optional<size_t> expansion_index;
    for (size_t i = 0; i < pattern_arguments.size(); ++i) {
        if (!pattern_arguments[i].expands_parameter_pack) {
            continue;
        }
        if (i + 1 != pattern_arguments.size()) {
            if (mode == TemplateArgumentListDeductionMode::PartialOrdering) {
                bindings.partial_ordering_used_parameters =
                    trial.partial_ordering_used_parameters;
            }
            return TemplateArgumentListDeductionResult::NonDeduced;
        }
        expansion_index = i;
    }

    if (!expansion_index.has_value()) {
        size_t compared_actual_count = actual_arguments.size();
        if (mode == TemplateArgumentListDeductionMode::PartialOrdering &&
            !actual_arguments.empty() &&
            actual_arguments.back().expands_parameter_pack &&
            pattern_arguments.size() < actual_arguments.size()) {

            --compared_actual_count;
            trial.partial_ordering_ignored_argument_pack = true;
        }
        if (pattern_arguments.size() != compared_actual_count) {
            return TemplateArgumentListDeductionResult::Mismatch;
        }
        for (size_t i = 0; i < pattern_arguments.size(); ++i) {
            if (mode == TemplateArgumentListDeductionMode::PartialOrdering &&
                actual_arguments[i].expands_parameter_pack) {
                return TemplateArgumentListDeductionResult::Mismatch;
            }
            if (!match_one(pattern_arguments[i], actual_arguments[i], trial)) {
                return TemplateArgumentListDeductionResult::Mismatch;
            }
        }
        bindings = std::move(trial);
        return TemplateArgumentListDeductionResult::Match;
    }

    const size_t fixed_count = *expansion_index;
    if (actual_arguments.size() < fixed_count) {
        return TemplateArgumentListDeductionResult::Mismatch;
    }
    for (size_t i = 0; i < fixed_count; ++i) {
        if (mode == TemplateArgumentListDeductionMode::PartialOrdering &&
            actual_arguments[i].expands_parameter_pack) {
            return TemplateArgumentListDeductionResult::Mismatch;
        }
        if (!match_one(pattern_arguments[i], actual_arguments[i], trial)) {
            return TemplateArgumentListDeductionResult::Mismatch;
        }
    }

    const TemplateArgument& expansion = pattern_arguments.back();
    std::vector<size_t> pack_indices = expansion_parameters(expansion);
    if (pack_indices.empty()) {
        return TemplateArgumentListDeductionResult::Mismatch;
    }
    std::vector<std::optional<std::vector<TemplateArgument>>>
        existing_elements;
    existing_elements.reserve(pack_indices.size());
    std::vector<std::vector<TemplateArgument>> deduced_elements(
        pack_indices.size());
    for (size_t parameter_index : pack_indices) {
        existing_elements.push_back(trial.pack_arguments[parameter_index]);
    }
    std::optional<size_t> existing_size;
    for (const auto& elements : existing_elements) {
        if (!elements.has_value()) {
            continue;
        }
        if (existing_size.has_value() &&
            *existing_size != elements->size()) {
            return TemplateArgumentListDeductionResult::Mismatch;
        }
        existing_size = elements->size();
    }
    if (existing_size.has_value() && *existing_size !=
        (actual_arguments.size() - fixed_count)) {
        return TemplateArgumentListDeductionResult::Mismatch;
    }

    const size_t remaining_count = actual_arguments.size() - fixed_count;
    size_t symbolic_expansion_count = static_cast<size_t>(std::count_if(
        actual_arguments.begin() + fixed_count,
        actual_arguments.end(),
        [](const TemplateArgument& argument) {
            return argument.expands_parameter_pack;
        }));
    if (symbolic_expansion_count > 1 ||
        (symbolic_expansion_count == 1 &&
         !actual_arguments.back().expands_parameter_pack)) {
        return TemplateArgumentListDeductionResult::Mismatch;
    }

    const size_t element_count = remaining_count;
    for (size_t element_index = 0; element_index < element_count;
         ++element_index) {
        PatternBindings element_bindings = trial;
        element_bindings.expansion_element_index = element_index;
        element_bindings.expansion_element_count = element_count;
        for (size_t parameter_index : pack_indices) {
            clear_element_binding(element_bindings, parameter_index);
        }
        const TemplateArgument& actual =
            actual_arguments[fixed_count + element_index];
        if (!match_one(expansion, actual, element_bindings)) {
            return TemplateArgumentListDeductionResult::Mismatch;
        }
        for (size_t pack_slot = 0; pack_slot < pack_indices.size();
             ++pack_slot) {
            std::optional<TemplateArgument> element = extract_element(
                element_bindings,
                pack_indices[pack_slot],
                actual.expands_parameter_pack);
            if (!element.has_value()) {
                return TemplateArgumentListDeductionResult::Mismatch;
            }
            if (existing_elements[pack_slot].has_value()) {
                if (!template_arguments_equivalent(
                        (*existing_elements[pack_slot])[element_index],
                        *element)) {
                    return TemplateArgumentListDeductionResult::Mismatch;
                }
            }
            deduced_elements[pack_slot].push_back(std::move(*element));
        }
        trial = std::move(element_bindings);
    }
    for (size_t pack_slot = 0; pack_slot < pack_indices.size(); ++pack_slot) {
        size_t parameter_index = pack_indices[pack_slot];
        trial.pack_arguments[parameter_index] =
            std::move(deduced_elements[pack_slot]);
    }
    trial.expansion_element_index.reset();
    trial.expansion_element_count.reset();
    bindings = std::move(trial);
    return TemplateArgumentListDeductionResult::Match;
}

bool Session::deduce_template_arguments_from_argument_pattern(
    const TemplateInfo& pattern_info,
    const std::vector<TemplateArgument>& pattern_arguments,
    const std::vector<TemplateArgument>& actual_arguments,
    std::vector<TemplateArgument>& deduced_arguments,
    bool complete_defaults) {
    deduced_arguments.clear();

    PatternBindings bindings;
    if (deduce_template_argument_list(
            pattern_info.parameters,
            pattern_arguments,
            actual_arguments,
            bindings,
            TemplateArgumentListDeductionMode::Ordinary) !=
        TemplateArgumentListDeductionResult::Match) {
        return false;
    }

    if (!reconcile_deduced_value_parameter_types(pattern_info, bindings)) {
        return false;
    }
    if (bindings.types.size() > pattern_info.parameters.size() ||
        bindings.values.size() > pattern_info.parameters.size() ||
        bindings.templates.size() > pattern_info.parameters.size()) {
        return false;
    }

    TemplateArgumentBindings argument_bindings(
        pattern_info.parameters.size());
    for (size_t i = 0; i < pattern_info.parameters.size(); ++i) {
        if (pattern_info.parameters[i].is_parameter_pack &&
            i < bindings.pack_arguments.size() &&
            bindings.pack_arguments[i].has_value()) {
            argument_bindings[i].kind = TemplateArgumentBindingKind::Pack;
            argument_bindings[i].arguments = *bindings.pack_arguments[i];
            continue;
        }
        TemplateArgument argument;
        switch (pattern_info.parameters[i].kind) {
            case TemplateParameterKind::Type:
                if (i >= bindings.types.size() ||
                    !bindings.types[i].valid()) {
                    continue;
                }
                argument.kind = cir::TemplateArgumentKind::Type;
                argument.type = bindings.types[i];
                break;
            case TemplateParameterKind::NonType:
                if (i >= bindings.values.size() ||
                    !bindings.values[i].bound) {
                    continue;
                }
                argument = bindings.values[i].argument;
                break;
            case TemplateParameterKind::Template:
                if (i >= bindings.templates.size() ||
                    !bindings.templates[i].bound) {
                    continue;
                }
                argument = bindings.templates[i].argument;
                break;
        }
        argument_bindings[i].kind = TemplateArgumentBindingKind::Single;
        argument_bindings[i].arguments = {std::move(argument)};
    }

    if (complete_defaults) {
        if (!complete_template_argument_bindings_with_defaults(
                pattern_info,
                argument_bindings,
                nullptr,
                nullptr,
                SrcLoc(),
                TemplateArgumentCompletionMode::Candidate)) {
            return false;
        }
    } else if (std::any_of(
                   argument_bindings.begin(),
                   argument_bindings.end(),
                   [](const TemplateArgumentBinding& binding) {
                       return binding.is_unbound();
                   })) {
        return false;
    }
    deduced_arguments = flatten_template_argument_bindings(argument_bindings);
    return true;
}

Session::PartialSpecializationSelection
Session::select_template_partial_specialization_uncached(
    const TemplateInfo& primary,
    const std::vector<TemplateArgument>& arguments,
    const PartialSpecializationConstraintPredicate& constraint_satisfied,
    const PartialSpecializationCandidatePredicate& candidate_viable) {
    PartialSpecializationSelection selection;

    auto match_arguments =
        [&](const TemplateInfo& partial,
            const std::vector<TemplateArgument>& pattern_arguments,
            const std::vector<TemplateArgument>& actual_arguments,
            TemplateArgumentBindings* deduced_bindings,
            const std::vector<TemplateParameter>* actual_parameters =
                nullptr) -> bool {
        PatternBindings bindings;
        if (deduce_template_argument_list(
                partial.parameters,
                pattern_arguments,
                actual_arguments,
                bindings,
                TemplateArgumentListDeductionMode::Ordinary,
                actual_parameters) !=
            TemplateArgumentListDeductionResult::Match) {
            return false;
        }
        std::vector<std::optional<TemplateArgument>> raw_array_bounds(
            bindings.values.size());
        for (size_t i = 0; i < bindings.values.size(); ++i) {
            const PatternBindings::ValueBinding& binding = bindings.values[i];
            if (binding.bound && binding.deduced_from_array_bound &&
                !binding.source_type_requires_exact_match &&
                !binding.argument.is_dependent) {
                raw_array_bounds[i] = binding.argument;
            }
        }
        if (!reconcile_deduced_value_parameter_types(partial, bindings)) {
            return false;
        }
        // The C++20 template invariant must materialize converted non-type
        // bounds because partial specializations have no viability check.
        for (size_t i = 0; i < raw_array_bounds.size(); ++i) {
            if (!raw_array_bounds[i].has_value() ||
                i >= bindings.values.size() ||
                !bindings.values[i].bound) {
                continue;
            }
            const TemplateArgument& raw = *raw_array_bounds[i];
            const TemplateArgument& converted = bindings.values[i].argument;
            bool raw_is_integral =
                raw.value_kind == cir::TemplateValueKind::Integer ||
                raw.value_kind == cir::TemplateValueKind::Boolean;
            bool converted_is_integral =
                converted.value_kind == cir::TemplateValueKind::Integer ||
                converted.value_kind == cir::TemplateValueKind::Boolean;
            if (raw_is_integral && converted_is_integral &&
                raw.integer_value != converted.integer_value) {
                return false;
            }
        }
        if (bindings.types.size() > partial.parameters.size() ||
            bindings.values.size() > partial.parameters.size() ||
            bindings.templates.size() > partial.parameters.size()) {
            return false;
        }
        if (!deduced_bindings) {
            return true;
        }

        TemplateArgumentBindings argument_bindings(partial.parameters.size());
        for (size_t i = 0; i < partial.parameters.size(); ++i) {
            TemplateArgument deduced;
            if (partial.parameters[i].is_parameter_pack &&
                i < bindings.pack_arguments.size() &&
                bindings.pack_arguments[i].has_value()) {
                argument_bindings[i].kind = TemplateArgumentBindingKind::Pack;
                argument_bindings[i].arguments =
                    *bindings.pack_arguments[i];
                continue;
            }
            if (partial.parameters[i].kind == TemplateParameterKind::Type) {
                if (i >= bindings.types.size() ||
                    !bindings.types[i].valid()) {
                    continue;
                }
                deduced.kind = cir::TemplateArgumentKind::Type;
                deduced.type = bindings.types[i];
            } else if (partial.parameters[i].kind ==
                       TemplateParameterKind::NonType) {
                if (i >= bindings.values.size() ||
                    !bindings.values[i].bound) {
                    continue;
                }
                deduced = bindings.values[i].argument;
                cir::TypeId value_type =
                    partial.parameters[i].non_type_type.valid()
                        ? partial.parameters[i].non_type_type
                        : file_.builtin_type(cir::BuiltinTypeKind::Int);
                if (!deduced.value_type.type.valid()) {
                    deduced.value_type =
                        cir::TypeRef{value_type,
                                     cir::QualNone,
                                     cir::MemorySpace::Default};
                }
            } else if (partial.parameters[i].kind ==
                       TemplateParameterKind::Template) {
                if (i >= bindings.templates.size() ||
                    !bindings.templates[i].bound) {
                    continue;
                }
                deduced = bindings.templates[i].argument;
            } else {
                continue;
            }
            argument_bindings[i].kind = TemplateArgumentBindingKind::Single;
            argument_bindings[i].arguments = {std::move(deduced)};
        }
        if (!complete_template_argument_bindings_with_defaults(
                partial,
                argument_bindings,
                nullptr,
                nullptr,
                SrcLoc(),
                TemplateArgumentCompletionMode::Candidate)) {
            return false;
        }
        if (argument_bindings.size() != partial.parameters.size()) {
            return false;
        }
        for (size_t i = 0; i < partial.parameters.size(); ++i) {
            const TemplateArgumentBinding& binding = argument_bindings[i];
            if (partial.parameters[i].is_parameter_pack) {
                if (!binding.is_pack()) {
                    return false;
                }
            } else if (!binding.is_single() ||
                       binding.arguments.size() != 1) {
                return false;
            }
        }
        *deduced_bindings = std::move(argument_bindings);
        return true;
    };

    struct Candidate {
        const TemplateInfo* info = nullptr;
        const TemplateInfo::PartialSpecialization* entry = nullptr;
        TemplateArgumentBindings argument_bindings;
        FunctionTemplateOrderingCandidate ordering_candidate;
    };
    std::vector<Candidate> candidates;
    for (const TemplateInfo::PartialSpecialization& partial_entry :
         primary.partial_specializations) {
        const TemplateInfo* partial = template_info(partial_entry.entity);
        if (!partial || !partial->is_partial_specialization) {
            continue;
        }
        TemplateArgumentBindings deduced_bindings;
        if (!match_arguments(*partial,
                             partial_entry.arguments,
                             arguments,
                             &deduced_bindings)) {
            continue;
        }
        if (candidate_viable &&
            !candidate_viable(*partial, deduced_bindings)) {
            continue;
        }
        if (constraint_satisfied &&
            !constraint_satisfied(*partial, deduced_bindings)) {
            continue;
        }
        Candidate candidate;
        candidate.info = partial;
        candidate.entry = &partial_entry;
        candidate.argument_bindings = std::move(deduced_bindings);
        candidate.ordering_candidate =
            partial_specialization_ordering_candidate(
                primary,
                *partial,
                partial_entry.arguments);
        candidates.push_back(std::move(candidate));
    }
    if (candidates.empty()) {
        return selection;
    }
    if (candidates.size() == 1) {
        selection.info = candidates.front().info;
        selection.argument_bindings =
            std::move(candidates.front().argument_bindings);
        return selection;
    }

    auto ordering_relation = [&](const Candidate& lhs,
                                 const Candidate& rhs) {
        return function_template_partial_ordering(
            lhs.ordering_candidate,
            rhs.ordering_candidate,
            FunctionTemplateOrderingContext::declaration());
    };
    auto more_specialized = [&](const Candidate& lhs,
                                const Candidate& rhs) {
        FunctionTemplatePartialOrdering ordering =
            ordering_relation(lhs, rhs);
        if (ordering.lhs_at_least_as_specialized &&
            ordering.rhs_at_least_as_specialized) {
            return declaration_more_constrained(
                lhs.info->introduced_constraints,
                rhs.info->introduced_constraints);
        }
        return ordering.lhs_at_least_as_specialized &&
               !ordering.rhs_at_least_as_specialized;
    };
    auto constraints_are_unordered_tie = [&](const Candidate& lhs,
                                             const Candidate& rhs) {
        FunctionTemplatePartialOrdering ordering =
            ordering_relation(lhs, rhs);
        if (!ordering.lhs_at_least_as_specialized ||
            !ordering.rhs_at_least_as_specialized) {
            return false;
        }
        if (lhs.info->introduced_constraints.empty() &&
            rhs.info->introduced_constraints.empty()) {
            return false;
        }
        return !declaration_more_constrained(
                   lhs.info->introduced_constraints,
                   rhs.info->introduced_constraints) &&
               !declaration_more_constrained(
                   rhs.info->introduced_constraints,
                   lhs.info->introduced_constraints);
    };
    std::vector<bool> eliminated(candidates.size(), false);
    for (size_t i = 0; i < candidates.size(); ++i) {
        for (size_t j = 0; j < candidates.size(); ++j) {
            if (i == j || eliminated[i]) {
                continue;
            }
            if (more_specialized(candidates[j], candidates[i])) {
                eliminated[i] = true;
            }
        }
    }

    size_t remaining = 0;
    size_t winner = 0;
    for (size_t i = 0; i < candidates.size(); ++i) {
        if (eliminated[i]) {
            continue;
        }
        ++remaining;
        winner = i;
    }
    if (remaining == 1) {
        selection.info = candidates[winner].info;
        selection.argument_bindings =
            std::move(candidates[winner].argument_bindings);
    } else {
        for (size_t i = 0; i < candidates.size(); ++i) {
            if (eliminated[i]) {
                continue;
            }
            selection.candidate_locs.push_back(candidates[i].entry->loc);
            for (size_t j = i + 1; j < candidates.size(); ++j) {
                if (!eliminated[j] &&
                    constraints_are_unordered_tie(candidates[i],
                                                 candidates[j])) {
                    selection.has_unordered_associated_constraints = true;
                }
            }
        }
        selection.is_ambiguous = true;
    }
    return selection;
}

bool Session::unify_type_pattern(cir::TypeId pattern_type,
                                 cir::TypeId argument_type,
                                 PatternBindings& bindings,
                                 TypePatternExceptionMatch exception_match,
                                 bool allow_qualification_conversion,
                                 TypePatternReturnMatch return_match,
                                 TypePatternParameterMatch parameter_match) const {
    return unify_type_ref_pattern(file_.type_ref(pattern_type),
                                  file_.type_ref(argument_type),
                                  bindings,
                                  exception_match,
                                  allow_qualification_conversion,
                                  return_match,
                                  parameter_match);
}

bool Session::unify_type_ref_pattern(
    cir::TypeRef pattern_type,
    cir::TypeRef argument_type,
    PatternBindings& bindings,
    TypePatternExceptionMatch exception_match,
    bool allow_qualification_conversion,
    TypePatternReturnMatch return_match,
    TypePatternParameterMatch parameter_match) const {
    if (pattern_type.type.valid() && argument_type.type.valid() &&
        file_.valid(pattern_type.type) && file_.valid(argument_type.type) &&
        file_.type(pattern_type.type).kind ==
            cir::TypeKind::AliasSpecialization &&
        file_.type(argument_type.type).kind ==
            cir::TypeKind::AliasSpecialization &&
        (!bindings.deduce_through_alias_associated_type ||
         transformed_alias_info(*this, pattern_type.type))) {
        const auto& pattern_alias =
            std::get<cir::AliasSpecializationTypePayload>(
                file_.type_payload(pattern_type.type));
        const auto& argument_alias =
            std::get<cir::AliasSpecializationTypePayload>(
                file_.type_payload(argument_type.type));
        if (pattern_alias.alias_template == argument_alias.alias_template) {
            if ((!allow_qualification_conversion &&
                 pattern_type.qualifiers != argument_type.qualifiers) ||
                pattern_type.memory_space != argument_type.memory_space) {
                return false;
            }
            static const std::vector<TemplateParameter> no_parameters;
            const std::vector<TemplateParameter>& pattern_parameters =
                bindings.template_parameters
                    ? *bindings.template_parameters
                    : no_parameters;
            TemplateArgumentListDeductionResult result =
                deduce_template_argument_list(
                    pattern_parameters,
                    pattern_alias.arguments,
                    argument_alias.arguments,
                    bindings,
                    bindings.partial_ordering
                        ? TemplateArgumentListDeductionMode::PartialOrdering
                        : TemplateArgumentListDeductionMode::Ordinary,
                    bindings.partial_ordering_argument_parameters);
            return result != TemplateArgumentListDeductionResult::Mismatch;
        }
    }
    if (pattern_type.type.valid() && file_.valid(pattern_type.type) &&
        file_.type(pattern_type.type).kind ==
            cir::TypeKind::AliasSpecialization) {
        const auto& pattern_alias =
            std::get<cir::AliasSpecializationTypePayload>(
                file_.type_payload(pattern_type.type));
        const TemplateInfo* alias_info =
            template_info(pattern_alias.alias_template);
        using Transform = TemplateInfo::AliasTypeTransformKind;
        if (alias_info &&
            alias_info->alias_type_transform_kind != Transform::None) {
            cir::TypeId resolved_argument =
                file_.resolved_type(argument_type.type);
            if (!file_.valid(resolved_argument) ||
                file_.type(resolved_argument).kind != cir::TypeKind::Vector ||
                alias_info->alias_type_transform_parameter >=
                    pattern_alias.arguments.size()) {
                return false;
            }
            if ((!allow_qualification_conversion &&
                 pattern_type.qualifiers != argument_type.qualifiers) ||
                pattern_type.memory_space != argument_type.memory_space) {
                return false;
            }
            const auto& vector =
                std::get<cir::VectorTypePayload>(
                    file_.type_payload(resolved_argument));
            if (!unify_type_ref_pattern(
                    pattern_alias.associated_type,
                    vector.element_type,
                    bindings,
                    exception_match,
                    allow_qualification_conversion,
                    return_match,
                    parameter_match)) {
                return false;
            }

            TemplateArgument actual_count;
            actual_count.kind = cir::TemplateArgumentKind::Value;
            actual_count.value_kind = cir::TemplateValueKind::Integer;
            actual_count.integer_value = cir::IntegerValue::from_unsigned(
                alias_info->alias_type_transform_kind == Transform::VectorSize
                    ? vector.size_bytes
                    : vector.element_count,
                64);
            const TemplateArgument& pattern_count =
                pattern_alias.arguments[
                    alias_info->alias_type_transform_parameter];
            actual_count.value_type = pattern_count.value_type.valid()
                ? pattern_count.value_type
                : file_.type_ref(file_.builtin_type(
                      cir::BuiltinTypeKind::Int));

            static const std::vector<TemplateParameter> no_parameters;
            const std::vector<TemplateParameter>& pattern_parameters =
                bindings.template_parameters
                    ? *bindings.template_parameters
                    : no_parameters;
            TemplateArgumentListDeductionResult result =
                deduce_template_argument_list(
                    pattern_parameters,
                    std::vector<TemplateArgument>{pattern_count},
                    std::vector<TemplateArgument>{actual_count},
                    bindings,
                    bindings.partial_ordering
                        ? TemplateArgumentListDeductionMode::PartialOrdering
                        : TemplateArgumentListDeductionMode::Ordinary,
                    bindings.partial_ordering_argument_parameters);
            return result != TemplateArgumentListDeductionResult::Mismatch;
        }
    }
    cir::TypeId p = file_.resolved_type(pattern_type.type);
    cir::TypeId a = file_.resolved_type(argument_type.type);
    if (!file_.valid(p) || !file_.valid(a)) {
        return false;
    }
    if (bindings.partial_ordering &&
        file_.type(a).kind == cir::TypeKind::TypeParam) {
        const auto* argument_leaf = std::get_if<cir::TypeParamTypePayload>(
            &file_.type_payload(a));
        if (argument_leaf) {
            if (const cir::TemplateArgument* identity =
                    partial_ordering_argument_identity(
                        bindings,
                        cir::TemplateArgumentKind::Type,
                        argument_leaf->index)) {
                argument_type.type = identity->type.type;
                argument_type.qualifiers = static_cast<uint8_t>(
                    argument_type.qualifiers | identity->type.qualifiers);
                a = file_.resolved_type(argument_type.type);
                if (!file_.valid(a)) {
                    return false;
                }
            }
        }
    }
    const cir::Type& pattern_node = file_.type(p);
    if (pattern_node.kind == cir::TypeKind::DependentName ||
        pattern_node.kind == cir::TypeKind::DecltypeExpr ||
        pattern_node.kind == cir::TypeKind::PackIndex) {

        return true;
    }
    if (pattern_node.kind == cir::TypeKind::TypeParam) {
        const auto* leaf =
            std::get_if<cir::TypeParamTypePayload>(&file_.type_payload(p));
        if (!leaf) {
            return false;
        }
        auto fixed_pack = std::find_if(
            bindings.fixed_type_packs.begin(),
            bindings.fixed_type_packs.end(),
            [&](const PatternBindings::FixedTypePack& pack) {
                return same_type_parameter_identity(
                    file_, pack.pattern_type, p);
            });
        if (fixed_pack != bindings.fixed_type_packs.end()) {
            if (!bindings.expansion_element_index.has_value() ||
                !bindings.expansion_element_count.has_value() ||
                fixed_pack->arguments.size() !=
                    *bindings.expansion_element_count ||
                *bindings.expansion_element_index >=
                    fixed_pack->arguments.size()) {
                return false;
            }
            const TemplateArgument& fixed_argument =
                fixed_pack->arguments[*bindings.expansion_element_index];
            if (fixed_argument.kind != cir::TemplateArgumentKind::Type) {
                return false;
            }
            cir::TypeRef fixed_type = fixed_argument.type;
            fixed_type.qualifiers = static_cast<uint8_t>(
                fixed_type.qualifiers | pattern_type.qualifiers);
            if (pattern_type.memory_space != cir::MemorySpace::Default) {
                if (fixed_type.memory_space != cir::MemorySpace::Default &&
                    fixed_type.memory_space != pattern_type.memory_space) {
                    return false;
                }
                fixed_type.memory_space = pattern_type.memory_space;
            }
            return unify_type_ref_pattern(fixed_type,
                                          argument_type,
                                          bindings,
                                          exception_match,
                                          allow_qualification_conversion,
                                          return_match,
                                          parameter_match);
        }
        if (leaf->index >= bindings.types.size()) {
            bindings.types.resize(leaf->index + 1);
        }
        if (leaf->index < bindings.explicit_types.size() &&
            bindings.explicit_types[leaf->index]) {
            return true;
        }
        if (!allow_qualification_conversion &&
            (pattern_type.qualifiers &
             static_cast<uint8_t>(~argument_type.qualifiers)) != 0) {
            return false;
        }
        cir::TypeRef deduced = argument_type;
        deduced.qualifiers = static_cast<uint8_t>(
            deduced.qualifiers &
            static_cast<uint8_t>(~pattern_type.qualifiers));
        if (pattern_type.memory_space != cir::MemorySpace::Default) {
            if (pattern_type.memory_space != argument_type.memory_space) {
                return false;
            }
            deduced.memory_space = cir::MemorySpace::Default;
        }
        return bind_type_argument(leaf->index,
                                  deduced,
                                  bindings);
    }
    bool array_pair =
        pattern_node.kind == cir::TypeKind::Array &&
        file_.type(a).kind == cir::TypeKind::Array;
    constexpr uint8_t cv_mask = cir::QualConst | cir::QualVolatile;
    bool qualifiers_match = pattern_type.qualifiers == argument_type.qualifiers;
    if (array_pair) {

        qualifiers_match =
            (pattern_type.qualifiers & ~cv_mask) ==
            (argument_type.qualifiers & ~cv_mask);
    }
    if ((!allow_qualification_conversion && !qualifiers_match) ||
        pattern_type.memory_space != argument_type.memory_space) {
        return false;
    }
    if (pattern_node.kind == cir::TypeKind::Record &&
        file_.type(a).kind == cir::TypeKind::TemplateSpecialization) {
        cir::EntityId pattern_template{};
        std::vector<TemplateArgument> pattern_arguments;
        const auto* argument_specialization =
            std::get_if<cir::TemplateSpecializationTypePayload>(
                &file_.type_payload(a));
        if (!argument_specialization ||
            !class_template_arguments_for_record(
                file_.record_entity(p),
                &pattern_template,
                &pattern_arguments) ||
            pattern_template != argument_specialization->primary_template) {
            return false;
        }
        static const std::vector<TemplateParameter> no_parameters;
        const std::vector<TemplateParameter>& pattern_parameters =
            bindings.template_parameters
                ? *bindings.template_parameters
                : no_parameters;
        TemplateArgumentListDeductionResult result =
            deduce_template_argument_list(
                pattern_parameters,
                pattern_arguments,
                argument_specialization->arguments,
                bindings,
                bindings.partial_ordering
                    ? TemplateArgumentListDeductionMode::PartialOrdering
                    : TemplateArgumentListDeductionMode::Ordinary,
                bindings.partial_ordering_argument_parameters);
        return result != TemplateArgumentListDeductionResult::Mismatch;
    }
    if (pattern_node.kind == cir::TypeKind::TemplateSpecialization) {
        const auto* pattern_specialization =
            std::get_if<cir::TemplateSpecializationTypePayload>(
                &file_.type_payload(p));
        if (!pattern_specialization) {
            return false;
        }
        cir::EntityId argument_template{};
        uint32_t argument_template_param =
            cir::ArrayTypePayload::no_extent_param;
        const std::vector<TemplateArgument>* argument_arguments = nullptr;
        std::vector<TemplateArgument> fact_arguments;
        if (file_.type(a).kind == cir::TypeKind::TemplateSpecialization) {
            const auto* argument_specialization =
                std::get_if<cir::TemplateSpecializationTypePayload>(
                    &file_.type_payload(a));
            if (!argument_specialization) {
                return false;
            }
            argument_template = argument_specialization->primary_template;
            argument_arguments = &argument_specialization->arguments;
            if (const TemplateInfo* argument_info =
                    template_info(argument_template)) {
                argument_template_param =
                    argument_info->template_parameter_index;
            }
        } else if (file_.type(a).kind == cir::TypeKind::Record) {
            const cir::TemplateSpecializationFact* fact =
                file_.template_specialization(file_.record_entity(a));
            if (fact) {
                argument_template = fact->template_entity;
                argument_template_param = fact->template_param_index;
                fact_arguments = fact->template_arguments();
            } else if (!class_template_arguments_for_record(
                           file_.record_entity(a),
                           &argument_template,
                           &fact_arguments)) {
                return false;
            }
            argument_arguments = &fact_arguments;
        } else {
            return false;
        }
        if (!argument_arguments) {
            return false;
        }
        std::optional<uint32_t> splice_parameter =
            direct_exception_parameter(
                pattern_specialization->splice_operand);
        uint32_t pattern_template_param =
            cir::ArrayTypePayload::no_extent_param;
        if (!splice_parameter.has_value()) {
            if (const TemplateInfo* pattern_info =
                    template_info(pattern_specialization->primary_template)) {
                pattern_template_param =
                    pattern_info->template_parameter_index;
            }
        }
        if (splice_parameter.has_value()) {
            cir::TemplateArgument reflection;
            reflection.kind = cir::TemplateArgumentKind::Value;
            reflection.value_kind = cir::TemplateValueKind::MetaInfo;
            reflection.meta_kind = cir::MetaInfoKind::Template;
            reflection.value_entity = argument_template;
            uint32_t root =
                pattern_specialization->splice_operand.root;
            if (root < pattern_specialization->splice_operand.nodes.size()) {
                reflection.value_type =
                    pattern_specialization->splice_operand.nodes[root]
                        .result_type;
            }
            if (*splice_parameter < bindings.explicit_values.size() &&
                bindings.explicit_values[*splice_parameter]) {
                if (*splice_parameter >= bindings.values.size() ||
                    !bindings.values[*splice_parameter].bound) {
                    return false;
                }
                const TemplateArgument& explicit_reflection =
                    bindings.values[*splice_parameter].argument;
                if (explicit_reflection.kind !=
                        cir::TemplateArgumentKind::Value ||
                    explicit_reflection.value_kind !=
                        cir::TemplateValueKind::MetaInfo ||
                    explicit_reflection.meta_kind !=
                        cir::MetaInfoKind::Template ||
                    explicit_reflection.value_entity != argument_template) {
                    return false;
                }
            } else if (!bind_value_argument(
                           *splice_parameter,
                           reflection,
                           bindings,
                           *this,
                           reflection.value_type,
                           /*source_type_requires_exact_match=*/true,
                           /*deduced_from_array_bound=*/false)) {
                return false;
            }
        } else if (pattern_template_param !=
                   cir::ArrayTypePayload::no_extent_param) {
            TemplateArgument template_argument;
            template_argument.kind = cir::TemplateArgumentKind::Template;
            template_argument.template_entity = argument_template;
            template_argument.template_param_index = argument_template_param;
            if (!bind_template_argument(pattern_template_param,
                                        template_argument,
                                        bindings)) {
                return false;
            }
        } else if (pattern_specialization->primary_template !=
                   argument_template) {
            return false;
        }
        static const std::vector<TemplateParameter> no_parameters;
        const std::vector<TemplateParameter>& pattern_parameters =
            bindings.template_parameters
            ? *bindings.template_parameters
            : no_parameters;
        TemplateArgumentListDeductionResult result =
            deduce_template_argument_list(
                pattern_parameters,
                pattern_specialization->arguments,
                *argument_arguments,
                bindings,
                bindings.partial_ordering
                    ? TemplateArgumentListDeductionMode::PartialOrdering
                    : TemplateArgumentListDeductionMode::Ordinary,
                bindings.partial_ordering_argument_parameters);
        return result != TemplateArgumentListDeductionResult::Mismatch;
    }
    if (pattern_node.kind != file_.type(a).kind) {
        return false;
    }
    auto nested_function_pointer_match =
        [&](cir::TypeId nested_pattern,
            cir::TypeId nested_argument) {
            bool function_pointer_conversion =
                exception_match == TypePatternExceptionMatch::
                                       ArgumentToPatternFunctionPointerConversion ||
                exception_match == TypePatternExceptionMatch::
                                       PatternToArgumentFunctionPointerConversion;
            if (!function_pointer_conversion) {
                return TypePatternExceptionMatch::Exact;
            }
            nested_pattern = file_.resolved_type(nested_pattern);
            nested_argument = file_.resolved_type(nested_argument);
            return file_.valid(nested_pattern) &&
                           file_.valid(nested_argument) &&
                           file_.type(nested_pattern).kind ==
                               cir::TypeKind::Function &&
                           file_.type(nested_argument).kind ==
                               cir::TypeKind::Function
                       ? exception_match
                       : TypePatternExceptionMatch::Exact;
        };
    switch (pattern_node.kind) {
        case cir::TypeKind::Pointer: {
            cir::TypeId pattern_pointee = file_.pointer_pointee_type(p);
            cir::TypeId argument_pointee = file_.pointer_pointee_type(a);
            return unify_type_ref_pattern(
                file_.pointer_pointee_ref(p),
                file_.pointer_pointee_ref(a),
                bindings,
                nested_function_pointer_match(pattern_pointee,
                                              argument_pointee),
                allow_qualification_conversion);
        }
        case cir::TypeKind::BlockPointer: {
            const auto* pattern_pointer =
                std::get_if<cir::BlockPointerTypePayload>(
                    &file_.type_payload(p));
            const auto* argument_pointer =
                std::get_if<cir::BlockPointerTypePayload>(
                    &file_.type_payload(a));
            if (!pattern_pointer || !argument_pointer) {
                return false;
            }
            return unify_type_ref_pattern(
                pattern_pointer->pointee,
                argument_pointer->pointee,
                bindings,
                nested_function_pointer_match(pattern_pointer->pointee.type,
                                              argument_pointer->pointee.type),
                allow_qualification_conversion);
        }
        case cir::TypeKind::MemberPointer: {
            const auto* pattern_member =
                std::get_if<cir::MemberPointerTypePayload>(
                    &file_.type_payload(p));
            const auto* argument_member =
                std::get_if<cir::MemberPointerTypePayload>(
                    &file_.type_payload(a));
            if (!pattern_member || !argument_member) {
                return false;
            }
            return unify_type_ref_pattern(pattern_member->class_type,
                                          argument_member->class_type,
                                          bindings,
                                          TypePatternExceptionMatch::Exact,
                                          /*allow_qualification_conversion=*/false) &&
                   unify_type_ref_pattern(
                       pattern_member->member_type,
                       argument_member->member_type,
                       bindings,
                       nested_function_pointer_match(
                           pattern_member->member_type.type,
                           argument_member->member_type.type),
                       allow_qualification_conversion);
        }
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference:
            return unify_type_ref_pattern(file_.reference_referred_ref(p),
                                          file_.reference_referred_ref(a),
                                          bindings,
                                          TypePatternExceptionMatch::Exact,
                                          allow_qualification_conversion);
        case cir::TypeKind::Array: {
            const auto* pattern_array =
                std::get_if<cir::ArrayTypePayload>(&file_.type_payload(p));
            const auto* argument_array =
                std::get_if<cir::ArrayTypePayload>(&file_.type_payload(a));
            if (!pattern_array || !argument_array) {
                return false;
            }
            constexpr uint32_t no_extent =
                cir::ArrayTypePayload::no_extent_param;
            if (pattern_array->extent_param != no_extent) {

                uint32_t index = pattern_array->extent_param;
                cir::TemplateArgument extent_argument;
                extent_argument.kind = cir::TemplateArgumentKind::Value;
                if (argument_array->extent_param != no_extent) {
                    if (const cir::TemplateArgument* identity =
                            partial_ordering_argument_identity(
                                bindings,
                                cir::TemplateArgumentKind::Value,
                                argument_array->extent_param)) {
                        extent_argument = *identity;
                    } else {
                        extent_argument.value_param_index =
                            argument_array->extent_param;
                        extent_argument.is_dependent = true;
                    }
                } else {
                    if (!argument_array->size.has_value()) {
                        return false;
                    }
                    extent_argument.value_kind =
                        cir::TemplateValueKind::Integer;
                    extent_argument.integer_value =
                        cir::IntegerValue::from_unsigned(
                            *argument_array->size, 64);
                }
                if (!bind_value_argument(index,
                                         extent_argument,
                                         bindings,
                                         *this,
                                         {},
                                         /*source_type_requires_exact_match=*/false,
                                         /*deduced_from_array_bound=*/true)) {
                    return false;
                }
            } else if (pattern_array->dependent_size_expr.valid() ||
                       pattern_array->size_expr_is_dependent) {

                if (bindings.partial_ordering) {
                    if (!argument_array->dependent_size_expr.valid() ||
                        !template_value_exprs_equivalent(
                            pattern_array->dependent_size_expr,
                            argument_array->dependent_size_expr)) {
                        return false;
                    }
                }
            } else if (argument_array->extent_param != no_extent ||
                       pattern_array->size != argument_array->size) {
                return false;
            }
            cir::TypeRef pattern_element = pattern_array->element_type;
            pattern_element.qualifiers = static_cast<uint8_t>(
                pattern_element.qualifiers |
                (pattern_type.qualifiers & cv_mask));
            cir::TypeRef argument_element = argument_array->element_type;
            argument_element.qualifiers = static_cast<uint8_t>(
                argument_element.qualifiers |
                (argument_type.qualifiers & cv_mask));
            return unify_type_ref_pattern(pattern_element,
                                          argument_element,
                                          bindings,
                                          TypePatternExceptionMatch::Exact,
                                          allow_qualification_conversion);
        }
        case cir::TypeKind::Function: {
            const auto* pattern_function =
                std::get_if<cir::FunctionTypePayload>(&file_.type_payload(p));
            const auto* argument_function =
                std::get_if<cir::FunctionTypePayload>(&file_.type_payload(a));
            if (!pattern_function || !argument_function ||
                pattern_function->is_variadic != argument_function->is_variadic ||
                pattern_function->has_prototype !=
                    argument_function->has_prototype ||
                pattern_function->member_ref_qualifier !=
                    argument_function->member_ref_qualifier ||
                pattern_function->member_is_const !=
                    argument_function->member_is_const ||
                pattern_function->member_is_volatile !=
                    argument_function->member_is_volatile ||
                pattern_function->calling_convention !=
                    argument_function->calling_convention) {
                return false;
            }
            bool placeholder_return_is_nondeduced =
                return_match == TypePatternReturnMatch::
                                    PlaceholderIsNonDeducedAtCurrentFunction &&
                contains_auto_type(pattern_function->return_type.type);
            if (!placeholder_return_is_nondeduced &&
                !unify_type_ref_pattern(pattern_function->return_type,
                                        argument_function->return_type,
                                        bindings)) {
                return false;
            }

            auto match_parameter = [&](cir::TypeRef pattern_parameter,
                                       cir::TypeRef argument_parameter,
                                       PatternBindings& target) {
                cir::TypeId pattern_parameter_type =
                    file_.resolved_type(pattern_parameter.type);
                cir::TypeId argument_parameter_type =
                    file_.resolved_type(argument_parameter.type);
                if (parameter_match ==
                        TypePatternParameterMatch::
                            AdjustForwardingReferencesAtCurrentFunction &&
                    is_forwarding_reference_parameter(
                        file_, pattern_parameter_type) &&
                    file_.valid(argument_parameter_type) &&
                    file_.type(argument_parameter_type).kind ==
                        cir::TypeKind::LValueReference) {
                    pattern_parameter =
                        file_.reference_referred_ref(pattern_parameter_type);
                }
                pattern_parameter.qualifiers = cir::QualNone;
                argument_parameter.qualifiers = cir::QualNone;
                return unify_type_ref_pattern(pattern_parameter,
                                              argument_parameter,
                                              target);
            };

            bool pattern_has_pack =
                pattern_function->parameter_pack_flags.size() ==
                    pattern_function->parameters.size() &&
                std::any_of(pattern_function->parameter_pack_flags.begin(),
                            pattern_function->parameter_pack_flags.end(),
                            [](uint8_t flag) { return flag != 0; });
            bool argument_has_pack =
                argument_function->parameter_pack_flags.size() ==
                    argument_function->parameters.size() &&
                std::any_of(argument_function->parameter_pack_flags.begin(),
                            argument_function->parameter_pack_flags.end(),
                            [](uint8_t flag) { return flag != 0; });

            if (!pattern_has_pack || argument_has_pack) {
                if (pattern_function->parameters.size() !=
                        argument_function->parameters.size() ||
                    pattern_function->parameter_pack_flags !=
                        argument_function->parameter_pack_flags) {
                    return false;
                }
                for (size_t i = 0;
                     i < pattern_function->parameters.size(); ++i) {
                    if (!match_parameter(pattern_function->parameters[i],
                                         argument_function->parameters[i],
                                         bindings)) {
                        return false;
                    }
                }
            } else {
                struct PackRef {
                    TemplateParameterKind kind = TemplateParameterKind::Type;
                    uint32_t index = cir::ArrayTypePayload::no_extent_param;
                };
                auto is_pack_parameter = [&](TemplateParameterKind kind,
                                             uint32_t index) {
                    return bindings.template_parameters &&
                           index < bindings.template_parameters->size() &&
                           (*bindings.template_parameters)[index].kind == kind &&
                           (*bindings.template_parameters)[index]
                               .is_parameter_pack;
                };
                auto add_pack = [&](std::vector<PackRef>& refs,
                                    TemplateParameterKind kind,
                                    uint32_t index) {
                    if (index == cir::ArrayTypePayload::no_extent_param ||
                        (kind != TemplateParameterKind::Type &&
                         !is_pack_parameter(kind, index))) {
                        return;
                    }
                    if (std::none_of(refs.begin(), refs.end(),
                                     [&](const PackRef& ref) {
                                         return ref.kind == kind &&
                                                ref.index == index;
                                     })) {
                        refs.push_back(PackRef{kind, index});
                    }
                };
                std::optional<size_t> fixed_pack_arity;
                bool fixed_pack_arity_mismatch = false;
                auto add_type_pack = [&](std::vector<PackRef>& refs,
                                         cir::TypeId type,
                                         uint32_t fallback_index,
                                         bool& has_pack_source) {
                    type = file_.resolved_type(type);
                    auto fixed = std::find_if(
                        bindings.fixed_type_packs.begin(),
                        bindings.fixed_type_packs.end(),
                        [&](const PatternBindings::FixedTypePack& pack) {
                            return same_type_parameter_identity(
                                file_, pack.pattern_type, type);
                        });
                    if (fixed != bindings.fixed_type_packs.end()) {
                        if (fixed_pack_arity.has_value() &&
                            *fixed_pack_arity != fixed->arguments.size()) {
                            fixed_pack_arity_mismatch = true;
                        } else {
                            fixed_pack_arity = fixed->arguments.size();
                        }
                        has_pack_source = true;
                        return;
                    }
                    if (bindings.template_parameters) {
                        for (size_t i = 0;
                             i < bindings.template_parameters->size(); ++i) {
                            const TemplateParameter& parameter =
                                (*bindings.template_parameters)[i];
                            if (parameter.kind == TemplateParameterKind::Type &&
                                parameter.is_parameter_pack &&
                                parameter.type_param_type.valid() &&
                                file_.resolved_type(
                                    parameter.type_param_type) == type) {
                                add_pack(refs,
                                         TemplateParameterKind::Type,
                                         static_cast<uint32_t>(i));
                                has_pack_source = true;
                                return;
                            }
                        }
                    }
                    if (is_pack_parameter(TemplateParameterKind::Type,
                                          fallback_index)) {
                        add_pack(refs,
                                 TemplateParameterKind::Type,
                                 fallback_index);
                        has_pack_source = true;
                    }
                };
                auto collect_type = [&](auto&& self,
                                        cir::TypeId type,
                                        std::vector<PackRef>& refs,
                                        bool& has_pack_source) -> void {
                    type = file_.resolved_type(type);
                    if (!file_.valid(type)) {
                        return;
                    }
                    switch (file_.type(type).kind) {
                        case cir::TypeKind::TypeParam: {
                            const auto& parameter =
                                std::get<cir::TypeParamTypePayload>(
                                    file_.type_payload(type));
                            if (parameter.is_parameter_pack) {
                                add_type_pack(refs,
                                              type,
                                              parameter.index,
                                              has_pack_source);
                            }
                            return;
                        }
                        case cir::TypeKind::Pointer:
                            self(self,
                                 std::get<cir::PointerTypePayload>(
                                     file_.type_payload(type)).pointee.type,
                                 refs,
                                 has_pack_source);
                            return;
                        case cir::TypeKind::BlockPointer:
                            self(self,
                                 std::get<cir::BlockPointerTypePayload>(
                                     file_.type_payload(type)).pointee.type,
                                 refs,
                                 has_pack_source);
                            return;
                        case cir::TypeKind::LValueReference:
                        case cir::TypeKind::RValueReference:
                            self(self,
                                 file_.reference_referred_ref(type).type,
                                 refs,
                                 has_pack_source);
                            return;
                        case cir::TypeKind::Array: {
                            const auto& array =
                                std::get<cir::ArrayTypePayload>(
                                    file_.type_payload(type));
                            self(self,
                                 array.element_type.type,
                                 refs,
                                 has_pack_source);
                            add_pack(refs,
                                     TemplateParameterKind::NonType,
                                     array.extent_param);
                            return;
                        }
                        case cir::TypeKind::MemberPointer: {
                            const auto& member =
                                std::get<cir::MemberPointerTypePayload>(
                                    file_.type_payload(type));
                            self(self,
                                 member.class_type.type,
                                 refs,
                                 has_pack_source);
                            self(self,
                                 member.member_type.type,
                                 refs,
                                 has_pack_source);
                            return;
                        }
                        case cir::TypeKind::Function: {
                            const auto& function =
                                std::get<cir::FunctionTypePayload>(
                                    file_.type_payload(type));
                            self(self,
                                 function.return_type.type,
                                 refs,
                                 has_pack_source);
                            for (size_t i = 0;
                                 i < function.parameters.size(); ++i) {
                                bool nested_expansion =
                                    i < function.parameter_pack_flags.size() &&
                                    function.parameter_pack_flags[i] != 0;
                                if (!nested_expansion) {
                                    self(self,
                                         function.parameters[i].type,
                                         refs,
                                         has_pack_source);
                                }
                            }
                            return;
                        }
                        case cir::TypeKind::TemplateSpecialization: {
                            const auto& specialization =
                                std::get<cir::TemplateSpecializationTypePayload>(
                                    file_.type_payload(type));
                            for (const cir::TemplateArgument& argument :
                                 specialization.arguments) {
                                if (argument.expands_parameter_pack ||
                                    argument.expands_pack_pattern) {
                                    continue;
                                }
                                if (argument.kind ==
                                    cir::TemplateArgumentKind::Type) {
                                    self(self,
                                         argument.type.type,
                                         refs,
                                         has_pack_source);
                                } else if (argument.kind ==
                                           cir::TemplateArgumentKind::Value) {
                                    add_pack(refs,
                                             TemplateParameterKind::NonType,
                                             argument.value_param_index);
                                } else {
                                    add_pack(refs,
                                             TemplateParameterKind::Template,
                                             argument.template_param_index);
                                }
                            }
                            return;
                        }
                        case cir::TypeKind::DependentName: {
                            const auto& dependent =
                                std::get<cir::DependentNameTypePayload>(
                                    file_.type_payload(type));
                            self(self,
                                 dependent.qualifier_type.type,
                                 refs,
                                 has_pack_source);
                            for (const cir::TemplateArgument& argument :
                                 dependent.template_arguments) {
                                if (argument.expands_parameter_pack ||
                                    argument.expands_pack_pattern) {
                                    continue;
                                }
                                if (argument.kind ==
                                    cir::TemplateArgumentKind::Type) {
                                    self(self,
                                         argument.type.type,
                                         refs,
                                         has_pack_source);
                                } else if (argument.kind ==
                                           cir::TemplateArgumentKind::Value) {
                                    add_pack(refs,
                                             TemplateParameterKind::NonType,
                                             argument.value_param_index);
                                } else {
                                    add_pack(refs,
                                             TemplateParameterKind::Template,
                                             argument.template_param_index);
                                }
                            }
                            return;
                        }
                        default:
                            return;
                    }
                };

                auto clear_element_binding = [&](PatternBindings& target,
                                                 const PackRef& pack) {
                    if (pack.kind == TemplateParameterKind::Type &&
                        pack.index < target.types.size()) {
                        target.types[pack.index] = {};
                        if (pack.index < target.explicit_types.size()) {
                            target.explicit_types[pack.index] = false;
                        }
                    } else if (pack.kind ==
                                   TemplateParameterKind::NonType &&
                               pack.index < target.values.size()) {
                        target.values[pack.index] = {};
                        if (pack.index < target.explicit_values.size()) {
                            target.explicit_values[pack.index] = false;
                        }
                    } else if (pack.kind == TemplateParameterKind::Template &&
                               pack.index < target.templates.size()) {
                        target.templates[pack.index] = {};
                        if (pack.index < target.explicit_templates.size()) {
                            target.explicit_templates[pack.index] = false;
                        }
                    }
                };
                auto append_element_binding = [&](PatternBindings& target,
                                                  const PackRef& pack) {
                    if (pack.index >= target.pack_arguments.size()) {
                        target.pack_arguments.resize(pack.index + 1);
                    }
                    auto& elements = target.pack_arguments[pack.index];
                    if (!elements.has_value()) {
                        elements.emplace();
                    }
                    cir::TemplateArgument element;
                    if (pack.kind == TemplateParameterKind::Type) {
                        if (pack.index >= target.types.size() ||
                            !target.types[pack.index].valid()) {
                            return false;
                        }
                        element.kind = cir::TemplateArgumentKind::Type;
                        element.type = target.types[pack.index];
                    } else if (pack.kind ==
                               TemplateParameterKind::NonType) {
                        if (pack.index >= target.values.size() ||
                            !target.values[pack.index].bound) {
                            return false;
                        }
                        element = target.values[pack.index].argument;
                    } else {
                        if (pack.index >= target.templates.size() ||
                            !target.templates[pack.index].bound) {
                            return false;
                        }
                        element = target.templates[pack.index].argument;
                    }
                    element.expands_parameter_pack = false;
                    element.expands_pack_pattern = false;
                    elements->push_back(std::move(element));
                    return true;
                };

                size_t argument_index = 0;
                for (size_t pattern_index = 0;
                     pattern_index < pattern_function->parameters.size();
                     ++pattern_index) {
                    bool is_pack =
                        pattern_function->parameter_pack_flags[pattern_index] !=
                        0;
                    if (!is_pack) {
                        if (argument_index >=
                                argument_function->parameters.size() ||
                            !match_parameter(
                                pattern_function->parameters[pattern_index],
                                argument_function->parameters[argument_index],
                                bindings)) {
                            return false;
                        }
                        ++argument_index;
                        continue;
                    }

                    std::vector<PackRef> packs;
                    bool has_pack_source = false;
                    fixed_pack_arity.reset();
                    fixed_pack_arity_mismatch = false;
                    collect_type(collect_type,
                                 pattern_function->parameters[pattern_index]
                                     .type,
                                 packs,
                                 has_pack_source);
                    if (!has_pack_source) {
                        return false;
                    }
                    for (const PackRef& pack : packs) {
                        if (pack.index >= bindings.pack_arguments.size()) {
                            bindings.pack_arguments.resize(pack.index + 1);
                        }
                        if (!bindings.pack_arguments[pack.index].has_value()) {
                            bindings.pack_arguments[pack.index].emplace();
                        }
                    }

                    bool trailing =
                        pattern_index + 1 ==
                        pattern_function->parameters.size();
                    size_t remaining_fixed =
                        pattern_function->parameters.size() -
                        pattern_index - 1;
                    if (argument_function->parameters.size() <
                        argument_index + remaining_fixed) {
                        return false;
                    }
                    size_t element_count = trailing
                        ? argument_function->parameters.size() -
                              argument_index - remaining_fixed
                        : 0;
                    if (fixed_pack_arity_mismatch ||
                        (fixed_pack_arity.has_value() &&
                         *fixed_pack_arity != element_count)) {
                        return false;
                    }
                    for (size_t element_index = 0;
                         element_index < element_count; ++element_index) {
                        PatternBindings trial = bindings;
                        trial.expansion_element_index = element_index;
                        trial.expansion_element_count = element_count;
                        for (const PackRef& pack : packs) {
                            clear_element_binding(trial, pack);
                        }
                        if (!match_parameter(
                                pattern_function->parameters[pattern_index],
                                argument_function->parameters[argument_index],
                                trial)) {
                            return false;
                        }
                        for (const PackRef& pack : packs) {
                            if (!append_element_binding(trial, pack)) {
                                return false;
                            }
                        }
                        bindings = std::move(trial);
                        ++argument_index;
                    }
                    bindings.expansion_element_index.reset();
                    bindings.expansion_element_count.reset();
                }
                if (argument_index != argument_function->parameters.size()) {
                    return false;
                }
            }

            return deduce_exception_spec_pattern(
                pattern_function->exception_spec,
                argument_function->exception_spec,
                exception_match,
                bindings,
                *this);
        }
        case cir::TypeKind::Record: {

            const cir::TemplateSpecializationFact* pattern_fact =
                file_.template_specialization(file_.record_entity(p));
            const cir::TemplateSpecializationFact* argument_fact =
                file_.template_specialization(file_.record_entity(a));
            if (pattern_fact && argument_fact) {
                PatternBindings trial = bindings;
                if (pattern_fact->template_param_index !=
                    cir::ArrayTypePayload::no_extent_param) {
                    cir::TemplateArgument template_argument;
                    template_argument.kind =
                        cir::TemplateArgumentKind::Template;
                    template_argument.template_entity =
                        argument_fact->template_entity;
                    template_argument.template_param_index =
                        argument_fact->template_param_index;
                    if (!bind_template_argument(
                            pattern_fact->template_param_index,
                            template_argument,
                            trial)) {
                        return false;
                    }
                } else if (pattern_fact->template_entity !=
                           argument_fact->template_entity) {
                    return p == a;
                }

                static const std::vector<TemplateParameter> no_parameters;
                const std::vector<TemplateParameter>& pattern_parameters =
                    trial.template_parameters
                    ? *trial.template_parameters
                    : no_parameters;
                std::vector<TemplateArgument> pattern_arguments =
                    pattern_fact->template_arguments();
                std::vector<TemplateArgument> argument_arguments =
                    argument_fact->template_arguments();
                TemplateArgumentListDeductionResult result =
                    deduce_template_argument_list(
                        pattern_parameters,
                        pattern_arguments,
                        argument_arguments,
                        trial,
                        trial.partial_ordering
                            ? TemplateArgumentListDeductionMode::PartialOrdering
                            : TemplateArgumentListDeductionMode::Ordinary,
                        trial.partial_ordering_argument_parameters);
                if (result !=
                    TemplateArgumentListDeductionResult::Mismatch) {
                    bindings = std::move(trial);
                    return true;
                }
            }
            if (!pattern_fact || !argument_fact) {
                cir::EntityId pattern_template{};
                cir::EntityId argument_template{};
                std::vector<TemplateArgument> pattern_arguments;
                std::vector<TemplateArgument> argument_arguments;
                if (class_template_arguments_for_record(
                        file_.record_entity(p),
                        &pattern_template,
                        &pattern_arguments) &&
                    class_template_arguments_for_record(
                        file_.record_entity(a),
                        &argument_template,
                        &argument_arguments) &&
                    pattern_template == argument_template) {
                    PatternBindings trial = bindings;
                    static const std::vector<TemplateParameter> no_parameters;
                    const std::vector<TemplateParameter>& pattern_parameters =
                        trial.template_parameters
                            ? *trial.template_parameters
                            : no_parameters;
                    TemplateArgumentListDeductionResult result =
                        deduce_template_argument_list(
                            pattern_parameters,
                            pattern_arguments,
                            argument_arguments,
                            trial,
                            trial.partial_ordering
                                ? TemplateArgumentListDeductionMode::
                                      PartialOrdering
                                : TemplateArgumentListDeductionMode::Ordinary,
                            trial.partial_ordering_argument_parameters);
                    if (result !=
                        TemplateArgumentListDeductionResult::Mismatch) {
                        bindings = std::move(trial);
                        return true;
                    }
                }
            }
            return p == a;
        }
        default:

            return p == a;
    }
}

bool Session::function_pointer_conversion_matches(cir::TypeRef source,
                                                  cir::TypeRef target) const {
    cir::TypeId source_type = file_.resolved_type(source.type);
    cir::TypeId target_type = file_.resolved_type(target.type);
    if (!file_.valid(source_type) || !file_.valid(target_type)) {
        return false;
    }
    cir::TypeKind source_kind = file_.type(source_type).kind;
    if ((source_kind != cir::TypeKind::Pointer &&
         source_kind != cir::TypeKind::MemberPointer) ||
        source_kind != file_.type(target_type).kind) {
        return false;
    }
    PatternBindings no_bindings;
    return unify_type_ref_pattern(
        source,
        target,
        no_bindings,
        TypePatternExceptionMatch::
            PatternToArgumentFunctionPointerConversion);
}

bool Session::function_type_conversion_matches(cir::TypeRef source,
                                                cir::TypeRef target) const {
    cir::TypeId source_type = file_.resolved_type(source.type);
    cir::TypeId target_type = file_.resolved_type(target.type);
    if (!file_.valid(source_type) || !file_.valid(target_type) ||
        file_.type(source_type).kind != cir::TypeKind::Function ||
        file_.type(target_type).kind != cir::TypeKind::Function) {
        return false;
    }
    PatternBindings no_bindings;
    return unify_type_ref_pattern(
        source,
        target,
        no_bindings,
        TypePatternExceptionMatch::
            PatternToArgumentFunctionPointerConversion);
}

} // namespace aburi::collect
