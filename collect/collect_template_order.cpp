#include "collect.h"

#include <algorithm>

namespace aburi::collect {

namespace detail {
bool deduce_exception_spec_for_partial_ordering(
    const cir::FunctionExceptionSpec& pattern,
    const cir::FunctionExceptionSpec& argument,
    Session::PatternBindings& bindings,
    const Session& session);
} // namespace detail

std::vector<Session::TemplateArgument>
Session::function_template_ordering_identities(const TemplateInfo& info,
                                                cir::TypeId identity_source) {
    std::vector<TemplateArgument> identities(info.parameters.size());
    for (size_t i = 0; i < info.parameters.size(); ++i) {
        const TemplateParameter& parameter = info.parameters[i];
        TemplateArgument identity;
        if (parameter.kind == TemplateParameterKind::Type) {
            identity.kind = cir::TemplateArgumentKind::Type;
            std::string spelling = "__aburi_order_type_" +
                std::to_string(parameter.depth) + "_" +
                std::to_string(parameter.index);
            if (!info.entity.valid() && identity_source.valid()) {
                spelling += "_from_" +
                    std::to_string(identity_source.index);
            }
            identity.type = file_.type_ref(file_.type_param_type(
                info.entity,
                spelling,
                parameter.index,
                parameter.depth,
                parameter.is_parameter_pack));
        } else if (parameter.kind == TemplateParameterKind::NonType) {
            identity.kind = cir::TemplateArgumentKind::Value;
            identity.value_kind = cir::TemplateValueKind::None;
            identity.value_entity = parameter.entity.valid()
                ? parameter.entity
                : info.entity;
            identity.value_byte_offset =
                static_cast<int64_t>(parameter.index) + 1;
            identity.value_type = file_.type_ref(parameter.non_type_type);
            if (contains_auto_type(parameter.non_type_type)) {
                std::string spelling = "__aburi_order_value_type_" +
                    std::to_string(parameter.depth) + "_" +
                    std::to_string(parameter.index);
                cir::TypeId placeholder = file_.type_param_type(
                    info.entity,
                    spelling,
                    parameter.index,
                    parameter.depth,
                    parameter.is_parameter_pack);
                identity.value_type = file_.type_ref(replace_auto_type(
                    parameter.non_type_type,
                    file_.type_ref(placeholder)));
            }
            identity.is_dependent = true;
        } else {
            identity.kind = cir::TemplateArgumentKind::Template;
            identity.template_entity = parameter.entity.valid()
                ? parameter.entity
                : info.entity;
            identity.is_dependent = true;
        }
        identity.expands_parameter_pack = parameter.is_parameter_pack;
        identities[i] = std::move(identity);
    }
    return identities;
}

Session::FunctionTemplateOrderingCandidate
Session::function_template_ordering_candidate(
    cir::EntityId template_entity,
    cir::TypeId original_function_type) {
    FunctionTemplateOrderingCandidate candidate;
    candidate.template_entity = template_entity;
    candidate.original_function_type = original_function_type;

    const TemplateInfo* info = template_info(template_entity);
    if (!info) {
        return candidate;
    }
    return function_template_ordering_candidate(*info,
                                                original_function_type);
}

Session::FunctionTemplateOrderingCandidate
Session::function_template_ordering_candidate(
    const TemplateInfo& info,
    cir::TypeId original_function_type) {
    FunctionTemplateOrderingCandidate candidate;
    candidate.template_entity = info.entity;
    candidate.original_function_type = original_function_type;
    candidate.template_parameters = &info.parameters;
    candidate.synthesized_arguments =
        function_template_ordering_identities(info, original_function_type);

    const cir::RecordMethodFact* method = file_.method_fact(info.entity);
    cir::EntityKind entity_kind = file_.valid(info.entity)
        ? file_.entity(info.entity).kind
        : cir::EntityKind::Invalid;
    candidate.is_non_static_member = method && !method->is_static &&
        entity_kind != cir::EntityKind::Constructor &&
        entity_kind != cir::EntityKind::Destructor;
    if (candidate.is_non_static_member) {
        // Template pattern types contain only the written parameter list;
        // unlike an emitted method's ABI type they do not carry a leading
        // `this` pointer. A written first pointer parameter must therefore
        // never be mistaken for the implicit object parameter.
        if (file_.valid(info.entity)) {
            cir::EntityId owner = file_.entity(info.entity).parent;
            if (owner.valid() && file_.valid(owner)) {
                candidate.member_class_type =
                    file_.type_ref(file_.entity(owner).type);
            }
        }
    }
    return candidate;
}

Session::FunctionTemplateOrderingCandidate
Session::partial_specialization_ordering_candidate(
    const TemplateInfo& primary,
    const TemplateInfo& specialization,
    const std::vector<TemplateArgument>& arguments) {
    FunctionTemplateOrderingCandidate candidate;
    candidate.template_entity = specialization.entity;
    candidate.template_parameters = &specialization.parameters;
    candidate.synthesized_arguments =
        function_template_ordering_identities(specialization,
                                              specialization.pattern_type);

    std::vector<TemplateArgument> pattern_arguments = arguments;
    for (TemplateArgument& argument : pattern_arguments) {
        if (argument.kind != cir::TemplateArgumentKind::Value ||
            argument.value_param_index ==
                cir::ArrayTypePayload::no_extent_param ||
            argument.value_param_index >=
                candidate.synthesized_arguments.size()) {
            continue;
        }
        const TemplateArgument& identity =
            candidate.synthesized_arguments[argument.value_param_index];
        if (identity.kind == cir::TemplateArgumentKind::Value &&
            identity.value_type.valid()) {
            argument.value_type = identity.value_type;
        }
    }

    cir::NameId primary_name = file_.intern_name(primary.name);
    cir::TypeId parameter_type = file_.template_specialization_type(
        primary_name,
        primary.entity,
        std::move(pattern_arguments),
        /*is_dependent=*/true,
        /*is_class_template_placeholder=*/false);
    candidate.original_function_type = file_.function_type(
        file_.builtin_type(cir::BuiltinTypeKind::Void),
        std::vector<cir::TypeId>{parameter_type});
    return candidate;
}

Session::FunctionTemplatePartialOrdering
Session::function_template_partial_ordering(
    const FunctionTemplateOrderingCandidate& lhs_candidate,
    const FunctionTemplateOrderingCandidate& rhs_candidate,
    const FunctionTemplateOrderingContext& context) {

    FunctionTemplatePartialOrdering ordering;
    const auto* lhs_payload = std::get_if<cir::FunctionTypePayload>(
        &file_.type_payload(
            file_.resolved_type(lhs_candidate.original_function_type)));
    const auto* rhs_payload = std::get_if<cir::FunctionTypePayload>(
        &file_.type_payload(
            file_.resolved_type(rhs_candidate.original_function_type)));
    if (!lhs_payload || !rhs_payload) {
        return ordering;
    }

    const cir::FunctionTypePayload lhs_copy = *lhs_payload;
    const cir::FunctionTypePayload rhs_copy = *rhs_payload;
    const cir::FunctionTypePayload* lhs = &lhs_copy;
    const cir::FunctionTypePayload* rhs = &rhs_copy;

    struct Transformed {
        cir::TypeId stripped{};
        bool was_reference = false;
        bool was_lvalue_reference = false;
        uint8_t referred_qualifiers = 0;
    };

    auto transform = [&](cir::TypeRef parameter) {
        Transformed out;
        cir::TypeId resolved = file_.resolved_type(parameter.type);
        if (!file_.valid(resolved)) {
            return out;
        }
        cir::TypeKind kind = file_.type(resolved).kind;
        if (kind == cir::TypeKind::LValueReference ||
            kind == cir::TypeKind::RValueReference) {
            out.was_reference = true;
            out.was_lvalue_reference = kind == cir::TypeKind::LValueReference;
            cir::TypeRef referred = file_.reference_referred_ref(resolved);
            out.referred_qualifiers = referred.qualifiers;
            out.stripped = file_.resolved_type(referred.type);
        } else {
            out.stripped = resolved;
        }
        return out;
    };
    auto more_cv = [](uint8_t a, uint8_t b) {
        return a != b && (b & ~a) == 0;
    };

    struct ParameterEntry {
        cir::TypeRef type;
        bool from_pack = false;
    };
    auto parameter_entries = [&](const FunctionTemplateOrderingCandidate& candidate,
                                 const cir::FunctionTypePayload& function,
                                 const FunctionTemplateOrderingCandidate& other,
                                 const cir::FunctionTypePayload& other_function) {
        std::vector<ParameterEntry> entries;
        entries.reserve(function.parameters.size() +
                        (candidate.is_non_static_member ? 1 : 0));
        bool other_first_is_rvalue = false;
        if (other.is_non_static_member) {
            other_first_is_rvalue =
                other_function.member_ref_qualifier ==
                cir::FunctionRefQualifierKind::RValue;
        } else if (!other_function.parameters.empty()) {
            cir::TypeId first =
                file_.resolved_type(other_function.parameters.front().type);
            other_first_is_rvalue =
                file_.valid(first) &&
                file_.type(first).kind == cir::TypeKind::RValueReference;
        }
        if (candidate.is_non_static_member) {
            cir::TypeRef object = candidate.member_class_type;
            if (!object.type.valid()) {
                return entries;
            }
            if (function.member_is_const) {
                object.qualifiers |= cir::QualConst;
            }
            if (function.member_is_volatile) {
                object.qualifiers |= cir::QualVolatile;
            }
            bool rvalue =
                function.member_ref_qualifier ==
                    cir::FunctionRefQualifierKind::RValue ||
                (function.member_ref_qualifier ==
                     cir::FunctionRefQualifierKind::None &&
                 other_first_is_rvalue);
            ParameterEntry object_entry;
            object_entry.type = file_.type_ref(file_.reference_type(
                object,
                rvalue ? cir::ReferenceKind::RValue
                       : cir::ReferenceKind::LValue));
            entries.push_back(object_entry);
        }
        for (size_t i = 0; i < function.parameters.size(); ++i) {
            ParameterEntry entry;
            entry.type = function.parameters[i];
            entry.from_pack =
                i < function.parameter_pack_flags.size() &&
                function.parameter_pack_flags[i] != 0;
            entries.push_back(entry);
        }
        return entries;
    };

    std::vector<ParameterEntry> lhs_entries =
        parameter_entries(lhs_candidate, *lhs, rhs_candidate, *rhs);
    std::vector<ParameterEntry> rhs_entries =
        parameter_entries(rhs_candidate, *rhs, lhs_candidate, *lhs);
    if (context.kind !=
            FunctionTemplateOrderingContextKind::ConversionCall &&
        ((lhs_candidate.is_non_static_member && lhs_entries.empty()) ||
         (rhs_candidate.is_non_static_member && rhs_entries.empty()))) {
        return {};
    }
    if (context.lhs_reversed != context.rhs_reversed) {
        if (context.lhs_reversed) {
            std::reverse(lhs_entries.begin(), lhs_entries.end());
        } else {
            std::reverse(rhs_entries.begin(), rhs_entries.end());
        }
    }

    ordering.lhs_at_least_as_specialized = true;
    ordering.rhs_at_least_as_specialized = true;
    PatternBindings deduced_into_rhs;
    PatternBindings deduced_into_lhs;
    deduced_into_rhs.partial_ordering = true;
    deduced_into_lhs.partial_ordering = true;
    deduced_into_rhs.partial_ordering_argument_identities =
        &lhs_candidate.synthesized_arguments;
    deduced_into_lhs.partial_ordering_argument_identities =
        &rhs_candidate.synthesized_arguments;

    auto reset_pack_bindings = [](PatternBindings& bindings,
                                  const std::vector<TemplateParameter>*
                                      parameters) {
        if (!parameters) {
            return;
        }
        for (const TemplateParameter& parameter : *parameters) {
            if (!parameter.is_parameter_pack) {
                continue;
            }
            size_t index = parameter.index;
            if (index < bindings.types.size()) {
                bindings.types[index] = {};
            }
            if (index < bindings.values.size()) {
                bindings.values[index] = {};
            }
            if (index < bindings.templates.size()) {
                bindings.templates[index] = {};
            }
        }
    };
    const TemplateInfo* lhs_template =
        template_info(lhs_candidate.template_entity);
    const TemplateInfo* rhs_template =
        template_info(rhs_candidate.template_entity);
    const std::vector<TemplateParameter>* lhs_parameters =
        lhs_candidate.template_parameters;
    const std::vector<TemplateParameter>* rhs_parameters =
        rhs_candidate.template_parameters;
    if (!lhs_parameters && lhs_template) {
        lhs_parameters = &lhs_template->parameters;
    }
    if (!rhs_parameters && rhs_template) {
        rhs_parameters = &rhs_template->parameters;
    }
    if (rhs_parameters) {
        deduced_into_rhs.template_parameters = rhs_parameters;
    }
    if (lhs_parameters) {
        deduced_into_lhs.template_parameters = lhs_parameters;
    }
    if (lhs_parameters) {
        deduced_into_rhs.partial_ordering_argument_parameters =
            lhs_parameters;
    }
    if (rhs_parameters) {
        deduced_into_lhs.partial_ordering_argument_parameters =
            rhs_parameters;
    }

    auto compare_pair = [&](const Transformed& left,
                            bool left_from_pack,
                            const Transformed& right,
                            bool right_from_pack) {
        bool lhs_deduces = !left_from_pack || right_from_pack;
        bool rhs_deduces = !right_from_pack || left_from_pack;
        if (lhs_deduces) {

            if (right_from_pack) {
                reset_pack_bindings(deduced_into_rhs, rhs_parameters);
            }
            lhs_deduces = unify_type_pattern(right.stripped,
                                             left.stripped,
                                             deduced_into_rhs);
            if (lhs_deduces &&
                deduced_into_rhs.partial_ordering_ignored_argument_pack) {
                lhs_deduces = false;
            }
        }
        if (rhs_deduces) {
            if (left_from_pack) {
                reset_pack_bindings(deduced_into_lhs, lhs_parameters);
            }
            rhs_deduces = unify_type_pattern(left.stripped,
                                             right.stripped,
                                             deduced_into_lhs);
            if (rhs_deduces &&
                deduced_into_lhs.partial_ordering_ignored_argument_pack) {
                rhs_deduces = false;
            }
        }
        if (!lhs_deduces) {
            ordering.lhs_at_least_as_specialized = false;
        }
        if (!rhs_deduces) {
            ordering.rhs_at_least_as_specialized = false;
        }
        if (lhs_deduces && rhs_deduces && left.was_reference &&
            right.was_reference) {
            if (left.was_lvalue_reference && !right.was_lvalue_reference) {
                ordering.rhs_at_least_as_specialized = false;
            } else if (more_cv(left.referred_qualifiers,
                               right.referred_qualifiers)) {
                ordering.rhs_at_least_as_specialized = false;
            }
            if (right.was_lvalue_reference && !left.was_lvalue_reference) {
                ordering.lhs_at_least_as_specialized = false;
            } else if (more_cv(right.referred_qualifiers,
                               left.referred_qualifiers)) {
                ordering.lhs_at_least_as_specialized = false;
            }
        }
    };
    auto compare_type_pair = [&](cir::TypeRef left,
                                 bool left_from_pack,
                                 cir::TypeRef right,
                                 bool right_from_pack) {
        Transformed transformed_left = transform(left);
        Transformed transformed_right = transform(right);
        if (!file_.valid(transformed_left.stripped) ||
            !file_.valid(transformed_right.stripped)) {
            ordering = {};
            return false;
        }
        compare_pair(transformed_left,
                     left_from_pack,
                     transformed_right,
                     right_from_pack);
        return true;
    };

    if (context.kind ==
        FunctionTemplateOrderingContextKind::ConversionCall) {
        compare_type_pair(lhs->return_type,
                          false,
                          rhs->return_type,
                          false);
        return ordering;
    }

    bool call_context =
        context.kind == FunctionTemplateOrderingContextKind::Call ||
        context.kind == FunctionTemplateOrderingContextKind::RewrittenCall;
    if (!call_context) {
        if (lhs->is_variadic != rhs->is_variadic ||
            lhs->has_prototype != rhs->has_prototype ||
            lhs->calling_convention != rhs->calling_convention) {
            return {};
        }
        if (!compare_type_pair(lhs->return_type,
                               false,
                               rhs->return_type,
                               false)) {
            return {};
        }
    }

    struct Projection {
        std::vector<ParameterEntry> parameters;
        bool trailing_pack = false;
        bool pack_participates = false;
        bool valid = true;
    };
    auto project_to_argument_count = [&](const std::vector<ParameterEntry>& entries,
                                         size_t argument_count,
                                         bool allow_ellipsis) {
        Projection projection;
        projection.trailing_pack =
            !entries.empty() && entries.back().from_pack;
        for (size_t i = 0; i < entries.size(); ++i) {
            const ParameterEntry& entry = entries[i];
            if (!entry.from_pack) {
                if (projection.parameters.size() < argument_count) {
                    projection.parameters.push_back(entry);
                }
                continue;
            }
            size_t suffix = 0;
            for (size_t j = i + 1; j < entries.size(); ++j) {
                if (!entries[j].from_pack) {
                    ++suffix;
                }
            }
            size_t available = argument_count > projection.parameters.size()
                ? argument_count - projection.parameters.size()
                : 0;
            size_t expansion = available > suffix ? available - suffix : 0;
            for (size_t j = 0; j < expansion; ++j) {
                projection.parameters.push_back(entry);
            }
            projection.pack_participates =
                projection.pack_participates || expansion != 0;
        }
        if (projection.parameters.size() < argument_count &&
            !allow_ellipsis) {
            projection.valid = false;
        }
        return projection;
    };
    auto fixed_parameter_count = [](const std::vector<ParameterEntry>& entries) {
        return static_cast<size_t>(std::count_if(
            entries.begin(),
            entries.end(),
            [](const ParameterEntry& entry) { return !entry.from_pack; }));
    };
    auto has_pack = [](const std::vector<ParameterEntry>& entries) {
        return std::any_of(entries.begin(),
                           entries.end(),
                           [](const ParameterEntry& entry) {
                               return entry.from_pack;
                           });
    };

    Projection lhs_projection;
    Projection rhs_projection;
    if (call_context) {
        lhs_projection = project_to_argument_count(
            lhs_entries,
            context.lhs_call_argument_count,
            lhs->is_variadic);
        rhs_projection = project_to_argument_count(
            rhs_entries,
            context.rhs_call_argument_count,
            rhs->is_variadic);
    } else {
        bool lhs_has_pack = has_pack(lhs_entries);
        bool rhs_has_pack = has_pack(rhs_entries);
        if (!lhs_has_pack && !rhs_has_pack) {
            if (lhs_entries.size() != rhs_entries.size()) {
                return {};
            }
            lhs_projection.parameters = lhs_entries;
            rhs_projection.parameters = rhs_entries;
        } else {
            size_t comparison_count = 0;
            if (lhs_has_pack && rhs_has_pack) {
                comparison_count = std::max(
                    fixed_parameter_count(lhs_entries),
                    fixed_parameter_count(rhs_entries)) + 1;
            } else {
                const std::vector<ParameterEntry>& plain =
                    lhs_has_pack ? rhs_entries : lhs_entries;
                comparison_count = plain.size();
            }
            lhs_projection =
                project_to_argument_count(lhs_entries,
                                          comparison_count,
                                          false);
            rhs_projection =
                project_to_argument_count(rhs_entries,
                                          comparison_count,
                                          false);
        }
    }
    if (!lhs_projection.valid || !rhs_projection.valid ||
        lhs_projection.parameters.size() !=
            rhs_projection.parameters.size()) {
        return {};
    }

    for (size_t i = 0; i < lhs_projection.parameters.size(); ++i) {
        const ParameterEntry& left = lhs_projection.parameters[i];
        const ParameterEntry& right = rhs_projection.parameters[i];
        if (!compare_type_pair(left.type,
                               left.from_pack,
                               right.type,
                               right.from_pack)) {
            return {};
        }
        if (!ordering.lhs_at_least_as_specialized &&
            !ordering.rhs_at_least_as_specialized) {
            return ordering;
        }
    }

    if (!call_context) {

        if (ordering.lhs_at_least_as_specialized &&
            !detail::deduce_exception_spec_for_partial_ordering(
                rhs->exception_spec,
                lhs->exception_spec,
                deduced_into_rhs,
                *this)) {
            ordering.lhs_at_least_as_specialized = false;
        }
        if (ordering.rhs_at_least_as_specialized &&
            !detail::deduce_exception_spec_for_partial_ordering(
                lhs->exception_spec,
                rhs->exception_spec,
                deduced_into_lhs,
                *this)) {
            ordering.rhs_at_least_as_specialized = false;
        }
    }

    auto used_parameters_are_bound =
        [](const PatternBindings& bindings,
           const std::vector<TemplateParameter>* parameters) {
        if (!parameters) {
            return true;
        }
        for (size_t i = 0;
             i < bindings.partial_ordering_used_parameters.size() &&
             i < parameters->size();
             ++i) {
            if (!bindings.partial_ordering_used_parameters[i]) {
                continue;
            }
            const TemplateParameter& parameter = (*parameters)[i];
            if (parameter.is_parameter_pack &&
                i < bindings.pack_arguments.size() &&
                bindings.pack_arguments[i].has_value()) {
                continue;
            }
            bool bound = false;
            switch (parameter.kind) {
                case TemplateParameterKind::Type:
                    bound = i < bindings.types.size() &&
                        bindings.types[i].valid();
                    break;
                case TemplateParameterKind::NonType:
                    bound = i < bindings.values.size() &&
                        bindings.values[i].bound;
                    break;
                case TemplateParameterKind::Template:
                    bound = i < bindings.templates.size() &&
                        bindings.templates[i].bound;
                    break;
            }
            if (!bound) {
                return false;
            }
        }
        return true;
    };
    if (ordering.lhs_at_least_as_specialized &&
        !used_parameters_are_bound(deduced_into_rhs, rhs_parameters)) {
        ordering.lhs_at_least_as_specialized = false;
    }
    if (ordering.rhs_at_least_as_specialized &&
        !used_parameters_are_bound(deduced_into_lhs, lhs_parameters)) {
        ordering.rhs_at_least_as_specialized = false;
    }

    if (ordering.lhs_at_least_as_specialized &&
        ordering.rhs_at_least_as_specialized) {
        bool lhs_unused_pack =
            lhs_projection.trailing_pack &&
            !lhs_projection.pack_participates;
        bool rhs_unused_pack =
            rhs_projection.trailing_pack &&
            !rhs_projection.pack_participates;
        if (lhs_unused_pack && !rhs_unused_pack) {
            ordering.lhs_at_least_as_specialized = false;
        } else if (rhs_unused_pack && !lhs_unused_pack) {
            ordering.rhs_at_least_as_specialized = false;
        }
    }
    return ordering;
}

bool Session::function_template_more_specialized(
    cir::TypeId lhs_pattern,
    cir::TypeId rhs_pattern,
    const FunctionTemplateOrderingContext& context) {
    FunctionTemplateOrderingCandidate lhs_candidate;
    lhs_candidate.original_function_type = lhs_pattern;
    FunctionTemplateOrderingCandidate rhs_candidate;
    rhs_candidate.original_function_type = rhs_pattern;
    FunctionTemplatePartialOrdering ordering =
        function_template_partial_ordering(lhs_candidate,
                                           rhs_candidate,
                                           context);
    return ordering.lhs_at_least_as_specialized &&
           !ordering.rhs_at_least_as_specialized;
}

bool Session::function_template_more_specialized(
    cir::TypeId lhs_pattern,
    const TemplateInfo& lhs,
    cir::TypeId rhs_pattern,
    const TemplateInfo& rhs,
    const FunctionTemplateOrderingContext& context) {
    FunctionTemplateOrderingCandidate lhs_candidate =
        function_template_ordering_candidate(lhs, lhs_pattern);
    FunctionTemplateOrderingCandidate rhs_candidate =
        function_template_ordering_candidate(rhs, rhs_pattern);
    FunctionTemplatePartialOrdering ordering =
        function_template_partial_ordering(lhs_candidate,
                                           rhs_candidate,
                                           context);
    if (ordering.lhs_at_least_as_specialized &&
        !ordering.rhs_at_least_as_specialized) {
        return true;
    }
    if (!ordering.lhs_at_least_as_specialized ||
        !ordering.rhs_at_least_as_specialized) {
        return false;
    }
    return declaration_more_constrained(lhs.introduced_constraints,
                                        rhs.introduced_constraints);
}

bool Session::function_template_more_specialized(
    const TemplateInfo& lhs,
    const TemplateInfo& rhs,
    const FunctionTemplateOrderingContext& context) {
    if (!lhs.pattern_type.valid() || !rhs.pattern_type.valid()) {
        return false;
    }
    return function_template_more_specialized(lhs.pattern_type,
                                              lhs,
                                              rhs.pattern_type,
                                              rhs,
                                              context);
}

bool Session::function_template_unordered_constraints_tie(
    cir::TypeId lhs_pattern,
    const TemplateInfo& lhs,
    cir::TypeId rhs_pattern,
    const TemplateInfo& rhs,
    const FunctionTemplateOrderingContext& context) {
    if (lhs.introduced_constraints.empty() &&
        rhs.introduced_constraints.empty()) {
        return false;
    }
    FunctionTemplateOrderingCandidate lhs_candidate =
        function_template_ordering_candidate(lhs.entity, lhs_pattern);
    FunctionTemplateOrderingCandidate rhs_candidate =
        function_template_ordering_candidate(rhs.entity, rhs_pattern);
    FunctionTemplatePartialOrdering ordering =
        function_template_partial_ordering(lhs_candidate,
                                           rhs_candidate,
                                           context);
    if (!ordering.lhs_at_least_as_specialized ||
        !ordering.rhs_at_least_as_specialized) {
        return false;
    }
    return !declaration_more_constrained(lhs.introduced_constraints,
                                         rhs.introduced_constraints) &&
           !declaration_more_constrained(rhs.introduced_constraints,
                                         lhs.introduced_constraints);
}

bool Session::function_template_unordered_constraints_tie(
    const TemplateInfo& lhs,
    const TemplateInfo& rhs,
    const FunctionTemplateOrderingContext& context) {
    if (!lhs.pattern_type.valid() || !rhs.pattern_type.valid()) {
        return false;
    }
    return function_template_unordered_constraints_tie(lhs.pattern_type,
                                                       lhs,
                                                       rhs.pattern_type,
                                                       rhs,
                                                       context);
}

bool Session::function_template_specializations_unordered_constraints_tie(
    cir::EntityId lhs,
    cir::EntityId rhs,
    const FunctionTemplateOrderingContext& context) {
    if (!lhs.valid() || !rhs.valid() || !file_.valid(lhs) ||
        !file_.valid(rhs)) {
        return false;
    }
    const cir::TemplateSpecializationFact* lhs_fact =
        file_.template_specialization(lhs);
    const cir::TemplateSpecializationFact* rhs_fact =
        file_.template_specialization(rhs);
    if (!lhs_fact || !rhs_fact || !lhs_fact->pattern_type.valid() ||
        !rhs_fact->pattern_type.valid()) {
        return false;
    }
    const TemplateInfo* lhs_info = template_info(lhs_fact->template_entity);
    const TemplateInfo* rhs_info = template_info(rhs_fact->template_entity);
    if (!lhs_info || !rhs_info) {
        return false;
    }
    return function_template_unordered_constraints_tie(lhs_fact->pattern_type,
                                                       *lhs_info,
                                                       rhs_fact->pattern_type,
                                                       *rhs_info,
                                                       context);
}

Session::FunctionTemplateSpecializationOrder
Session::compare_function_template_specializations(
    cir::EntityId lhs,
    cir::EntityId rhs,
    const FunctionTemplateOrderingContext& context) {
    if (!lhs.valid() || !rhs.valid() || !file_.valid(lhs) ||
        !file_.valid(rhs)) {
        return FunctionTemplateSpecializationOrder::Unordered;
    }
    const cir::TemplateSpecializationFact* lhs_fact =
        file_.template_specialization(lhs);
    const cir::TemplateSpecializationFact* rhs_fact =
        file_.template_specialization(rhs);
    if (!lhs_fact || !rhs_fact ||
        lhs_fact->template_entity == rhs_fact->template_entity ||
        !lhs_fact->pattern_type.valid() || !rhs_fact->pattern_type.valid()) {
        return FunctionTemplateSpecializationOrder::Unordered;
    }

    FunctionTemplateOrderingCandidate lhs_candidate =
        function_template_ordering_candidate(lhs_fact->template_entity,
                                             lhs_fact->pattern_type);
    FunctionTemplateOrderingCandidate rhs_candidate =
        function_template_ordering_candidate(rhs_fact->template_entity,
                                             rhs_fact->pattern_type);
    FunctionTemplatePartialOrdering ordering =
        function_template_partial_ordering(lhs_candidate,
                                           rhs_candidate,
                                           context);
    if (ordering.lhs_at_least_as_specialized &&
        !ordering.rhs_at_least_as_specialized) {
        return FunctionTemplateSpecializationOrder::LhsMoreSpecialized;
    }
    if (ordering.rhs_at_least_as_specialized &&
        !ordering.lhs_at_least_as_specialized) {
        return FunctionTemplateSpecializationOrder::RhsMoreSpecialized;
    }
    if (!ordering.lhs_at_least_as_specialized ||
        !ordering.rhs_at_least_as_specialized) {
        return FunctionTemplateSpecializationOrder::Unordered;
    }

    const TemplateInfo* lhs_info = template_info(lhs_fact->template_entity);
    const TemplateInfo* rhs_info = template_info(rhs_fact->template_entity);
    if (!lhs_info || !rhs_info) {
        return FunctionTemplateSpecializationOrder::Unordered;
    }
    bool lhs_more = declaration_more_constrained(
        lhs_info->introduced_constraints,
        rhs_info->introduced_constraints);
    bool rhs_more = declaration_more_constrained(
        rhs_info->introduced_constraints,
        lhs_info->introduced_constraints);
    if (lhs_more != rhs_more) {
        return lhs_more
            ? FunctionTemplateSpecializationOrder::LhsMoreSpecialized
            : FunctionTemplateSpecializationOrder::RhsMoreSpecialized;
    }
    return FunctionTemplateSpecializationOrder::Unordered;
}
} // namespace aburi::collect
