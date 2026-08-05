#include "collect.h"
#include "collect_template_state.h"

#include "../perf_stats.h"

#include <algorithm>
#include <functional>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <variant>
#include <vector>

namespace aburi::collect {

namespace {

void bump_overload_counter(PerfCounter counter) {
    if (auto* profiler = active_perf_profiler()) {
        profiler->add_counter(counter);
    }
}

bool is_record_kind(const cir::File& file, cir::TypeId type) {
    cir::TypeId resolved = file.resolved_type(type);
    return file.valid(resolved) &&
           file.type(resolved).kind == cir::TypeKind::Record;
}

const cir::FunctionTypePayload* function_payload_of(const cir::File& file,
                                                    cir::TypeId type) {
    cir::TypeId resolved = file.resolved_type(type);
    if (!file.valid(resolved) ||
        file.type(resolved).kind != cir::TypeKind::Function) {
        return nullptr;
    }
    return std::get_if<cir::FunctionTypePayload>(&file.type_payload(resolved));
}

bool is_conversion_function_name(const cir::File& file,
                                 const cir::RecordMethodFact& method) {
    (void)file;
    return method.is_conversion_function;
}

cir::TypeRef conversion_function_return_type(const cir::File& file,
                                             const cir::RecordMethodFact& method) {
    const cir::FunctionTypePayload* payload =
        function_payload_of(file, method.type.type);
    return payload ? payload->return_type : cir::TypeRef{};
}

struct ConversionResultValue {
    cir::TypeId type{};
    ValueCategory category = ValueCategory::PrValue;
    uint8_t qualifiers = 0;
};

ConversionResultValue conversion_result_value(const cir::File& file,
                                              cir::TypeRef return_type) {
    ConversionResultValue result;
    cir::TypeId type = file.resolved_type(return_type.type);
    if (!file.valid(type)) {
        return result;
    }
    cir::TypeKind kind = file.type(type).kind;
    if (kind == cir::TypeKind::LValueReference) {
        cir::TypeRef referred = file.reference_referred_ref(type);
        result.type = file.resolved_type(referred.type);
        result.category = ValueCategory::LValue;
        result.qualifiers = referred.qualifiers;
        return result;
    }
    if (kind == cir::TypeKind::RValueReference) {
        cir::TypeRef referred = file.reference_referred_ref(type);
        result.type = file.resolved_type(referred.type);
        result.category = ValueCategory::XValue;
        result.qualifiers = referred.qualifiers;
        return result;
    }
    result.type = type;
    result.category = ValueCategory::PrValue;
    result.qualifiers = return_type.qualifiers;
    return result;
}

cir::BuiltinTypeKind builtin_kind_of(const cir::File& file, cir::TypeId type) {
    cir::TypeId resolved = file.resolved_type(type);
    if (!file.valid(resolved) ||
        file.type(resolved).kind != cir::TypeKind::Builtin) {
        return cir::BuiltinTypeKind::Other;
    }
    const auto* payload =
        std::get_if<cir::BuiltinTypePayload>(&file.type_payload(resolved));
    return payload ? payload->kind : cir::BuiltinTypeKind::Other;
}

bool is_integer_builtin(cir::BuiltinTypeKind kind) {
    switch (kind) {
        case cir::BuiltinTypeKind::Bool:
        case cir::BuiltinTypeKind::Char:
        case cir::BuiltinTypeKind::SChar:
        case cir::BuiltinTypeKind::UChar:
        case cir::BuiltinTypeKind::Char8:
        case cir::BuiltinTypeKind::WChar:
        case cir::BuiltinTypeKind::Char16:
        case cir::BuiltinTypeKind::Char32:
        case cir::BuiltinTypeKind::Short:
        case cir::BuiltinTypeKind::UShort:
        case cir::BuiltinTypeKind::Int:
        case cir::BuiltinTypeKind::UInt:
        case cir::BuiltinTypeKind::Long:
        case cir::BuiltinTypeKind::ULong:
        case cir::BuiltinTypeKind::LongLong:
        case cir::BuiltinTypeKind::ULongLong:
        case cir::BuiltinTypeKind::Int128:
        case cir::BuiltinTypeKind::UInt128:
        case cir::BuiltinTypeKind::USize:
            return true;
        default:
            return false;
    }
}

bool is_floating_builtin(cir::BuiltinTypeKind kind) {
    switch (kind) {
        case cir::BuiltinTypeKind::Float16:
        case cir::BuiltinTypeKind::Float:
        case cir::BuiltinTypeKind::Double:
        case cir::BuiltinTypeKind::LongDouble:
            return true;
        default:
            return false;
    }
}

bool is_arithmetic_like(const cir::File& file, cir::TypeId type) {
    cir::TypeId resolved = file.resolved_type(type);
    if (!file.valid(resolved)) {
        return false;
    }
    if (file.type(resolved).kind == cir::TypeKind::Enum ||
        file.type(resolved).kind == cir::TypeKind::BitInt) {
        return true;
    }
    cir::BuiltinTypeKind kind = builtin_kind_of(file, resolved);
    return is_integer_builtin(kind) || is_floating_builtin(kind);
}

cir::TypeId decayed_argument_type(const cir::File& file, cir::TypeId type) {
    cir::TypeId resolved = file.resolved_type(type);
    if (!file.valid(resolved)) {
        return type;
    }
    return resolved;
}

} // namespace

bool Session::function_signatures_match(cir::TypeId lhs, cir::TypeId rhs) const {
    const cir::FunctionTypePayload* left = function_payload_of(file_, lhs);
    const cir::FunctionTypePayload* right = function_payload_of(file_, rhs);
    if (!left || !right) {
        return false;
    }
    if (left->parameters.size() != right->parameters.size() ||
        left->is_variadic != right->is_variadic ||
        left->member_is_const != right->member_is_const ||
        left->member_is_volatile != right->member_is_volatile ||
        left->member_ref_qualifier != right->member_ref_qualifier ||
        left->calling_convention != right->calling_convention) {
        return false;
    }
    for (size_t i = 0; i < left->parameters.size(); ++i) {
        cir::TypeRef a{file_.resolved_type(left->parameters[i].type),
                       cir::QualNone, left->parameters[i].memory_space};
        cir::TypeRef b{file_.resolved_type(right->parameters[i].type),
                       cir::QualNone, right->parameters[i].memory_space};

        if (a != b) {
            return false;
        }
    }
    return true;
}

std::optional<cir::TypeRef> Session::initializer_list_element_type(
    cir::TypeId type) const {
    type = file_.resolved_type(type);
    if (!file_.valid(type)) {
        return std::nullopt;
    }
    if (file_.type(type).kind == cir::TypeKind::LValueReference ||
        file_.type(type).kind == cir::TypeKind::RValueReference) {
        type = file_.resolved_type(file_.reference_referred_type(type));
        if (!file_.valid(type)) {
            return std::nullopt;
        }
    }

    cir::EntityId primary;
    const std::vector<cir::TemplateArgument>* arguments = nullptr;
    std::vector<cir::TemplateArgument> fact_arguments;
    if (file_.type(type).kind == cir::TypeKind::TemplateSpecialization) {
        const auto* specialization =
            std::get_if<cir::TemplateSpecializationTypePayload>(
                &file_.type_payload(type));
        if (specialization) {
            primary = specialization->primary_template;
            arguments = &specialization->arguments;
        }
    } else if (file_.type(type).kind == cir::TypeKind::Record) {
        const cir::TemplateSpecializationFact* specialization =
            file_.template_specialization(file_.record_entity(type));
        if (specialization) {
            primary = specialization->template_entity;
            fact_arguments = specialization->template_arguments();
            arguments = &fact_arguments;
        }
    }
    if (!primary.valid() || !file_.valid(primary) || !arguments ||
        arguments->size() != 1 ||
        arguments->front().kind != cir::TemplateArgumentKind::Type) {
        return std::nullopt;
    }

    const TemplateInfo* info = template_info(primary);
    if (!info || !info->is_class_template ||
        info->name != "initializer_list") {
        return std::nullopt;
    }

    cir::DeclContextId context = file_.entity(primary).semantic_context;
    bool in_std_namespace = false;
    while (context.valid() && file_.valid(context)) {
        const cir::DeclContext& declaration_context =
            file_.decl_context(context);
        if (declaration_context.kind == cir::DeclContextKind::Record) {
            return std::nullopt;
        }
        if (declaration_context.kind == cir::DeclContextKind::Namespace) {
            cir::EntityId owner = declaration_context.owner;
            bool is_std = owner.valid() && file_.valid(owner) &&
                file_.entity(owner).name.valid() &&
                file_.name(file_.entity(owner).name) == "std";
            if (is_std) {
                in_std_namespace = true;
                break;
            }
            // Standard-library implementations place initializer_list in
            // one or more inline ABI namespaces. An ordinary nested
            // namespace named std::detail must not acquire the language
            // privilege merely because an enclosing namespace is std.
            if (!declaration_context.is_inline_namespace) {
                return std::nullopt;
            }
        }
        context = declaration_context.parent;
    }
    if (!in_std_namespace || !arguments->front().type.valid()) {
        return std::nullopt;
    }
    return arguments->front().type;
}

std::optional<cir::TypeRef>
Session::constructor_initializer_list_element_type(
    cir::EntityId constructor) const {
    const cir::RecordMethodFact* fact = file_.method_fact(constructor);
    const cir::FunctionTypePayload* payload = fact
        ? function_payload_of(file_, fact->type.type)
        : nullptr;
    if (!payload || payload->parameters.empty()) {
        return std::nullopt;
    }
    return initializer_list_element_type(payload->parameters.front().type);
}

Session::ConversionRank Session::conversion_rank(
    const ExprResult& from,
    cir::TypeRef to,
    uint8_t from_qualifiers,
    ConversionDetail* detail,
    bool allow_user_defined,
    bool allow_explicit_conversion_functions) const {
    if (!from.init_list && from.category != ValueCategory::InitList) {
        if (lang_opts_.is_cxx_mode() &&
            (from.category == ValueCategory::FunctionDesignator ||
             from.category == ValueCategory::OverloadDesignator) &&
            to.type.valid()) {
            cir::TypeId target = file_.resolved_type(to.type);
            bool target_is_reference = file_.valid(target) &&
                (file_.type(target).kind == cir::TypeKind::LValueReference ||
                 file_.type(target).kind == cir::TypeKind::RValueReference);
            bool target_is_pointer = file_.valid(target) &&
                file_.type(target).kind == cir::TypeKind::Pointer;
            cir::TypeId target_function = target_is_reference
                ? file_.reference_referred_type(target)
                : (target_is_pointer
                       ? file_.pointer_pointee_type(target)
                       : cir::TypeId{});
            target_function = file_.resolved_type(target_function);
            if (file_.valid(target_function) &&
                file_.type(target_function).kind == cir::TypeKind::Function) {
                std::shared_ptr<const OverloadDesignator> designator =
                    canonical_overload_designator(from);
                std::vector<cir::EntityId> candidates;
                if (designator) {
                    for (const OverloadDesignatorCandidate& candidate :
                         designator->candidates) {
                        if (candidate.address_category ==
                            OverloadAddressCategory::FunctionPointer) {
                            candidates.push_back(candidate.entity);
                        }
                    }
                }
                cir::EntityId selected = const_cast<Session*>(this)
                    ->select_addressable_function_target(
                        candidates,
                        target_function,
                        SrcLoc(),
                        !designator ||
                                designator->explicit_template_arguments.empty()
                            ? nullptr
                            : &designator->explicit_template_arguments,
                        !designator
                            ? nullptr
                            : &designator
                                   ->candidate_explicit_template_arguments,
                        nullptr,
                        /*mark_odr_use=*/false);
                if (!selected.valid()) {
                    return ConversionRank::Bad;
                }
                if (detail) {
                    cir::TypeId selected_function =
                        file_.resolved_type(file_.entity(selected).type);
                    detail->standard.source =
                        file_.type_ref(file_.entity(selected).type);
                    detail->standard.target =
                        cir::TypeRef{target, to.qualifiers, to.memory_space};
                    detail->standard.source_category = from.category;
                    detail->standard.add(
                        target_is_reference
                            ? StandardConversionStep::ReferenceBinding
                            : StandardConversionStep::FunctionToPointer);
                    if (file_.valid(selected_function) &&
                        selected_function != target_function &&
                        function_type_conversion_matches(
                            file_.type_ref(selected_function),
                            file_.type_ref(target_function))) {
                        detail->standard.add(
                            StandardConversionStep::FunctionPointerConversion);
                    }
                }
                return ConversionRank::Exact;
            }
        }

        if (lang_opts_.is_cxx_mode() &&
            is_null_pointer_constant(from) && to.type.valid()) {
            cir::TypeId target = file_.resolved_type(to.type);
            cir::TypeKind target_kind = file_.valid(target)
                ? file_.type(target).kind
                : cir::TypeKind::Unknown;
            bool reference_binding =
                target_kind == cir::TypeKind::LValueReference ||
                target_kind == cir::TypeKind::RValueReference;
            cir::TypeRef converted_target = to;
            if (reference_binding) {
                converted_target = file_.reference_referred_ref(target);
            }
            cir::TypeId converted_type =
                file_.resolved_type(converted_target.type);
            cir::TypeKind converted_kind = file_.valid(converted_type)
                ? file_.type(converted_type).kind
                : cir::TypeKind::Unknown;
            if (converted_kind == cir::TypeKind::Pointer ||
                converted_kind == cir::TypeKind::BlockPointer ||
                converted_kind == cir::TypeKind::MemberPointer) {

                bool const_lvalue_reference =
                    target_kind == cir::TypeKind::LValueReference &&
                    (converted_target.qualifiers & cir::QualConst) != 0;
                if (target_kind == cir::TypeKind::LValueReference &&
                    !const_lvalue_reference) {
                    return ConversionRank::Bad;
                }
                if (detail) {
                    detail->standard.source =
                        cir::TypeRef{file_.resolved_type(from.type),
                                     from_qualifiers,
                                     cir::MemorySpace::Default};
                    detail->standard.target =
                        cir::TypeRef{target, to.qualifiers, to.memory_space};
                    detail->standard.source_category = from.category;
                    detail->standard.add(
                        converted_kind == cir::TypeKind::MemberPointer
                            ? StandardConversionStep::MemberPointerConversion
                            : StandardConversionStep::PointerConversion);
                    if (reference_binding) {
                        detail->standard.bound_referred = converted_type;
                        detail->standard.bound_qualifiers =
                            converted_target.qualifiers;
                        detail->standard.add(
                            StandardConversionStep::ReferenceBinding);
                    }
                }
                return ConversionRank::Conversion;
            }
        }
        cir::TypeId source_type = from.type;
        cir::TypeId resolved_source = file_.resolved_type(source_type);
        if ((from.category == ValueCategory::LValue ||
             from.category == ValueCategory::XValue) &&
            file_.valid(resolved_source) &&
            (file_.type(resolved_source).kind ==
                 cir::TypeKind::LValueReference ||
             file_.type(resolved_source).kind ==
                 cir::TypeKind::RValueReference)) {

            cir::TypeRef referred =
                file_.reference_referred_ref(resolved_source);
            source_type = referred.type;
            from_qualifiers = static_cast<uint8_t>(
                from_qualifiers | referred.qualifiers);
        }
        return conversion_rank(
            source_type, from.category, to,
            from_qualifiers, detail,
            allow_user_defined,
            allow_explicit_conversion_functions, &from);
    }
    if (!from.init_list || !to.type.valid()) {
        return ConversionRank::Bad;
    }

    cir::TypeId target = file_.resolved_type(to.type);
    if (!file_.valid(target)) {
        return ConversionRank::Conversion;
    }

    auto plan = std::make_shared<ListInitializationPlan>();
    plan->syntax = from.init_list->syntax;
    plan->target = cir::TypeRef{target, to.qualifiers, to.memory_space};
    plan->has_designators = std::any_of(
        from.init_list->elements.begin(), from.init_list->elements.end(),
        [](const InitElementInput& element) {
            return !element.designators.empty();
        });
    if (detail) {
        detail->standard.source = file_.type_ref(from.type);
        detail->standard.target = plan->target;
        detail->standard.source_category = ValueCategory::InitList;
        detail->list_plan = plan;
    }

    auto rank_elements = [&](cir::TypeRef element_target) {
        ConversionRank worst = ConversionRank::Exact;
        plan->elements.reserve(from.init_list->elements.size());
        for (const InitElementInput& element : from.init_list->elements) {
            ListElementConversionPlan element_plan;
            element_plan.target = element_target;
            element_plan.loc = element.loc;
            ConversionRank rank = conversion_rank(
                element.value, element_target, /*from_qualifiers=*/0,
                /*detail=*/nullptr, /*allow_user_defined=*/true);
            element_plan.viable = rank != ConversionRank::Bad;
            plan->elements.push_back(element_plan);
            if (rank == ConversionRank::Bad) {
                return ConversionRank::Bad;
            }
            if (rank > worst) {
                worst = rank;
            }
        }
        return worst;
    };

    cir::TypeKind target_kind = file_.type(target).kind;
    if (target_kind == cir::TypeKind::LValueReference ||
        target_kind == cir::TypeKind::RValueReference) {
        plan->destination = ListInitializationDestination::Reference;
        cir::TypeRef referred = file_.reference_referred_ref(target);
        if (from.init_list->elements.size() == 1 &&
            from.init_list->elements.front().designators.empty()) {
            ConversionRank direct = conversion_rank(
                from.init_list->elements.front().value, to,
                from_qualifiers, detail, allow_user_defined);
            if (direct != ConversionRank::Bad) {
                plan->viable = true;
                if (detail) {
                    detail->list_plan = plan;
                }
                return direct;
            }
        }
        bool non_const_lvalue =
            target_kind == cir::TypeKind::LValueReference &&
            (referred.qualifiers & cir::QualConst) == 0;
        if (non_const_lvalue) {
            return ConversionRank::Bad;
        }
        cir::TypeRef value_target = referred;
        value_target.qualifiers = cir::QualNone;
        ConversionDetail value_detail;
        ConversionRank converted = conversion_rank(
            from, value_target, /*from_qualifiers=*/0,
            &value_detail, allow_user_defined);
        if (converted == ConversionRank::UserDefined && detail) {

            detail->user_conversion = value_detail.user_conversion;
            detail->user_conversion_unique =
                value_detail.user_conversion_unique;
            detail->trailing_standard = value_detail.standard;
            detail->trailing_standard.trailing_binding =
                target_kind == cir::TypeKind::RValueReference
                    ? TrailingBinding::RValueReference
                    : TrailingBinding::LValueReference;
            detail->trailing_standard.bound_referred =
                file_.resolved_type(referred.type);
            detail->trailing_standard.bound_qualifiers =
                referred.qualifiers;
            detail->trailing_standard.add(
                StandardConversionStep::ReferenceBinding);
        }
        if (value_detail.list_plan) {
            if (detail) {
                detail->list_plan = value_detail.list_plan;
            }
            plan = std::move(value_detail.list_plan);
        }
        plan->viable = converted != ConversionRank::Bad;
        return converted;
    }

    if (std::optional<cir::TypeRef> element =
            initializer_list_element_type(target)) {
        plan->destination = ListInitializationDestination::InitializerList;
        if (plan->has_designators) {
            return ConversionRank::Bad;
        }
        cir::TypeRef const_element = *element;
        const_element.qualifiers |= cir::QualConst;
        ConversionRank rank = rank_elements(const_element);
        plan->viable = rank != ConversionRank::Bad;
        return rank;
    }

    if (target_kind == cir::TypeKind::Array) {
        plan->destination = ListInitializationDestination::Array;
        if (plan->has_designators) {
            return ConversionRank::Bad;
        }
        const auto* array = std::get_if<cir::ArrayTypePayload>(
            &file_.type_payload(target));
        if (!array || (array->size.has_value() &&
                       from.init_list->elements.size() > *array->size)) {
            return ConversionRank::Bad;
        }
        ConversionRank rank = rank_elements(array->element_type);
        plan->viable = rank != ConversionRank::Bad;
        return rank;
    }

    if (target_kind == cir::TypeKind::Record) {
        const cir::RecordFacts* facts = file_.record_facts_for_type(target);
        if (facts && facts->is_aggregate == cir::ClassPropertyState::True) {
            plan->destination = ListInitializationDestination::Aggregate;
            size_t positional_index = 0;
            for (const InitElementInput& element : from.init_list->elements) {
                if (!element.designators.empty()) {
                    continue;
                }
                while (positional_index < facts->fields.size() &&
                       facts->fields[positional_index].is_base_subobject) {
                    ++positional_index;
                }
                if (positional_index >= facts->fields.size()) {
                    return ConversionRank::Bad;
                }
                ListElementConversionPlan element_plan;
                element_plan.target = facts->fields[positional_index].type;
                element_plan.loc = element.loc;
                ConversionRank rank = conversion_rank(
                    element.value, element_plan.target,
                    /*from_qualifiers=*/0, /*detail=*/nullptr,
                    /*allow_user_defined=*/true);
                element_plan.viable = rank != ConversionRank::Bad;
                plan->elements.push_back(element_plan);
                if (rank == ConversionRank::Bad) {
                    return ConversionRank::Bad;
                }
                ++positional_index;
            }
            plan->viable = true;
            return ConversionRank::UserDefined;
        }

        plan->destination = ListInitializationDestination::ClassConstructor;
        bool ambiguous = false;
        std::vector<ExprResult> arguments{from};
        cir::EntityId constructor = const_cast<Session*>(this)->select_constructor(
            target, arguments, &ambiguous, from.init_list->loc,
            ConstructorInitializationKind::CopyList);
        if (!constructor.valid() || ambiguous) {
            return ConversionRank::Bad;
        }
        const cir::RecordMethodFact* constructor_fact =
            file_.method_fact(constructor);
        if (constructor_fact && constructor_fact->is_explicit) {

            return ConversionRank::Bad;
        }
        plan->selected_constructor = constructor;
        plan->viable = true;
        if (detail) {
            detail->user_conversion = constructor;
            detail->user_conversion_unique = true;
        }
        return ConversionRank::UserDefined;
    }

    if (from.init_list->elements.empty()) {
        plan->destination = ListInitializationDestination::Scalar;
        plan->viable = true;
        return ConversionRank::Exact;
    }
    if (from.init_list->elements.size() == 1 && !plan->has_designators) {
        plan->destination = ListInitializationDestination::Scalar;
        ConversionRank rank = conversion_rank(
            from.init_list->elements.front().value,
            cir::TypeRef{target, to.qualifiers, to.memory_space},
            /*from_qualifiers=*/0, /*detail=*/nullptr, allow_user_defined);
        plan->viable = rank != ConversionRank::Bad;
        return rank;
    }
    return ConversionRank::Bad;
}

Session::ConversionRank Session::conversion_rank(cir::TypeId from,
                                                 ValueCategory category,
                                                 cir::TypeRef to,
                                                 uint8_t from_qualifiers,
                                                 ConversionDetail* detail,
                                                 bool allow_user_defined,
                                                 bool allow_explicit_conversion_functions,
                                                 const ExprResult*
                                                     source_expression) const {
    bump_overload_counter(PerfCounter::ConversionRankCalls);
    if (!to.type.valid() || !from.valid()) {
        return ConversionRank::Conversion;
    }
    cir::TypeId from_resolved = decayed_argument_type(file_, from);
    cir::TypeId to_resolved = file_.resolved_type(to.type);
    if (!file_.valid(from_resolved) || !file_.valid(to_resolved)) {
        return ConversionRank::Conversion;
    }
    if (detail) {
        detail->standard.source =
            cir::TypeRef{from_resolved, from_qualifiers,
                         cir::MemorySpace::Default};
        detail->standard.target =
            cir::TypeRef{to_resolved, to.qualifiers, to.memory_space};
        detail->standard.source_category = category;
        detail->standard.rank = ConversionRank::Bad;
        detail->standard.steps = 0;
    }

    auto finish_bad = [&]() {
        if (allow_user_defined) {
            UserConversionProbe probe =
                probe_user_defined_conversion(
                    from_resolved, category, to,
                    allow_explicit_conversion_functions,
                    source_expression);
            if (probe.viable) {
                if (detail) {
                    detail->user_conversion =
                        probe.unique ? probe.route : cir::EntityId{};
                    detail->user_conversion_unique = probe.unique;
                }
                return ConversionRank::UserDefined;
            }
        }
        return ConversionRank::Bad;
    };
    auto identity_types_match = [&](cir::TypeRef lhs, cir::TypeRef rhs) {
        lhs.type = file_.resolved_type(lhs.type);
        rhs.type = file_.resolved_type(rhs.type);
        if (lang_opts_.is_cxx_mode()) {
            return lhs == rhs;
        }
        return types_compatible(lhs, rhs);
    };

    cir::TypeKind from_kind = file_.type(from_resolved).kind;

    cir::TypeKind to_kind = file_.type(to_resolved).kind;
    if (to_kind == cir::TypeKind::LValueReference ||
        to_kind == cir::TypeKind::RValueReference) {
        cir::TypeRef referred = file_.reference_referred_ref(to_resolved);
        cir::TypeRef source_object{from_resolved, from_qualifiers,
                                   to.memory_space};
        QualificationConversionAnalysis reference_qualification =
            analyze_qualification_conversion(
                source_object,
                referred,
                QualificationTargetKind::ReferenceCompatible);
        bool same = reference_qualification.similar &&
                    reference_qualification.allowed;
        DerivedToBasePathResult base_result =
            analyze_derived_to_base_path(from_resolved, referred.type);

        bool base_binding = !same &&
            base_result.kind != DerivedToBasePathKind::NotFound;
        if (base_binding) {

            if (to_kind == cir::TypeKind::LValueReference &&
                category != ValueCategory::LValue &&
                (referred.qualifiers & cir::QualConst) == 0) {
                return ConversionRank::Bad;
            }
            if (to_kind == cir::TypeKind::RValueReference &&
                category == ValueCategory::LValue) {
                return ConversionRank::Bad;
            }
            if ((from_qualifiers &
                 static_cast<uint8_t>(~referred.qualifiers)) != 0) {
                return ConversionRank::Bad;
            }
            if (detail) {
                detail->standard.bound_referred =
                    file_.resolved_type(referred.type);
                detail->standard.bound_qualifiers = referred.qualifiers;
                detail->standard.add(
                    StandardConversionStep::ReferenceBinding);
                detail->standard.add(StandardConversionStep::DerivedToBase);
            }
            return ConversionRank::Conversion;
        }

        if (!same) {
            QualificationConversionAnalysis related =
                analyze_qualification_conversion(
                    source_object, referred, QualificationTargetKind::Concrete);
            if (related.similar && related.allowed) {
                return ConversionRank::Bad;
            }
        }
        bool is_const_lref =
            to_kind == cir::TypeKind::LValueReference &&
            ((referred.qualifiers & cir::QualConst) != 0 ||
             array_type_has_const_element(referred.type));

        bool source_is_lvalue =
            category == ValueCategory::LValue ||
            category == ValueCategory::FunctionDesignator;
        bool lvalue_function_binding =
            source_is_lvalue &&
            from_kind == cir::TypeKind::Function;
        if (same) {
            if (to_kind == cir::TypeKind::LValueReference &&
                !is_const_lref && !source_is_lvalue) {
                return ConversionRank::Bad;
            }
            if (to_kind == cir::TypeKind::RValueReference &&
                source_is_lvalue &&
                !lvalue_function_binding) {
                return ConversionRank::Bad;
            }

            if (detail) {
                detail->standard.bound_referred =
                    file_.resolved_type(referred.type);
                detail->standard.bound_qualifiers = referred.qualifiers;
                detail->standard.add(StandardConversionStep::ReferenceBinding);
            }
            return ConversionRank::Exact;
        }
        if (allow_user_defined && from_kind == cir::TypeKind::Record) {

            ExprResult conversion_source;
            conversion_source.type = from_resolved;
            conversion_source.category =
                category == ValueCategory::PrValue
                    ? ValueCategory::XValue
                    : category;
            conversion_source.unevaluated_semantic_operand = true;
            if (source_expression) {
                conversion_source.place = source_expression->place;
                conversion_source.semantic_object_qualifiers =
                    source_expression->semantic_object_qualifiers;
            }
            std::vector<cir::EntityId> conversion_candidates;
            const_cast<Session*>(this)->collect_conversion_function_candidates(
                conversion_source, to_resolved,
                allow_explicit_conversion_functions, SrcLoc{},
                conversion_candidates);
            std::vector<OverloadCandidate> conversion_inputs;
            conversion_inputs.reserve(conversion_candidates.size());
            for (cir::EntityId candidate : conversion_candidates) {
                conversion_inputs.push_back(OverloadCandidate{
                    candidate,
                    /*member_object_leading=*/true,
                    /*ranks_conversion_result=*/true});
            }
            OverloadSelection direct_conversion =
                const_cast<Session*>(this)->select_overload_detailed(
                    conversion_inputs, {conversion_source}, to_resolved,
                    /*ambiguity_info=*/nullptr,
                    /*allow_user_defined_argument_conversions=*/false);
            if (direct_conversion.entity.valid()) {
                if (detail) {
                    detail->user_conversion = direct_conversion.entity;
                    detail->user_conversion_unique = true;
                    if (const cir::RecordMethodFact* method =
                            file_.method_fact(direct_conversion.entity)) {
                        ConversionResultValue converted =
                            conversion_result_value(
                                file_, conversion_function_return_type(
                                           file_, *method));
                        ConversionDetail binding;
                        (void)conversion_rank(
                            converted.type, converted.category, to,
                            converted.qualifiers, &binding,
                            /*allow_user_defined=*/false);
                        detail->trailing_standard = binding.standard;
                        detail->trailing_standard.trailing_binding =
                            to_kind == cir::TypeKind::RValueReference
                                ? TrailingBinding::RValueReference
                                : TrailingBinding::LValueReference;
                    }
                }
                return ConversionRank::UserDefined;
            }
        }
        if (!is_const_lref && to_kind != cir::TypeKind::RValueReference) {
            return ConversionRank::Bad;
        }
        if (category == ValueCategory::InitList) {
            cir::TypeId referred_resolved = file_.resolved_type(referred.type);
            if (file_.valid(referred_resolved) &&
                file_.type(referred_resolved).kind == cir::TypeKind::Array &&
                (is_const_lref ||
                 array_type_has_const_element(referred_resolved) ||
                 to_kind == cir::TypeKind::RValueReference)) {
                return ConversionRank::Conversion;
            }
            return ConversionRank::Bad;
        }

        cir::TypeRef referred_value{referred.type, cir::QualNone,
                                    referred.memory_space};
        ConversionDetail inner_detail;
        ConversionRank inner = conversion_rank(
            from_resolved, ValueCategory::PrValue, referred_value,
            /*from_qualifiers=*/0, &inner_detail, allow_user_defined,
            allow_explicit_conversion_functions);
        ConversionDetail converted_binding_detail;
        bool has_converted_binding_detail = false;
        if (inner == ConversionRank::UserDefined &&
            inner_detail.user_conversion_unique &&
            inner_detail.user_conversion.valid() &&
            file_.valid(inner_detail.user_conversion)) {
            ConversionResultValue converted_result;
            const cir::Entity& route =
                file_.entity(inner_detail.user_conversion);
            if (route.kind == cir::EntityKind::Constructor) {
                converted_result.type = file_.resolved_type(referred.type);
                converted_result.category = ValueCategory::PrValue;
            } else if (const cir::RecordMethodFact* method =
                           file_.method_fact(inner_detail.user_conversion)) {
                converted_result = conversion_result_value(
                    file_, conversion_function_return_type(file_, *method));
            }
            if (converted_result.type.valid()) {
                ConversionRank binding = conversion_rank(
                    converted_result.type, converted_result.category, to,
                    converted_result.qualifiers,
                    &converted_binding_detail,
                    /*allow_user_defined=*/false);
                if (binding == ConversionRank::Bad) {
                    return ConversionRank::Bad;
                }
                has_converted_binding_detail = true;
            }
        }
        if (inner == ConversionRank::UserDefined && detail) {
            detail->user_conversion = inner_detail.user_conversion;
            detail->user_conversion_unique =
                inner_detail.user_conversion_unique;
            detail->trailing_standard = has_converted_binding_detail
                ? converted_binding_detail.standard
                : inner_detail.standard;
            detail->trailing_standard.trailing_binding =
                to_kind == cir::TypeKind::RValueReference
                    ? TrailingBinding::RValueReference
                    : TrailingBinding::LValueReference;
            if (!has_converted_binding_detail) {
                detail->trailing_standard.bound_referred =
                    file_.resolved_type(referred.type);
                detail->trailing_standard.bound_qualifiers =
                    referred.qualifiers;
                detail->trailing_standard.add(
                    StandardConversionStep::ReferenceBinding);
            }
        } else if (inner != ConversionRank::Bad && detail) {

            detail->standard = inner_detail.standard;
            detail->standard.target =
                cir::TypeRef{to_resolved, to.qualifiers, to.memory_space};
            detail->standard.source_category = ValueCategory::PrValue;
            detail->standard.bound_referred =
                file_.resolved_type(referred.type);
            detail->standard.bound_qualifiers = referred.qualifiers;
            detail->standard.add(
                StandardConversionStep::ReferenceBinding);

            detail->standard.binds_converted_temporary = true;
        }
        return inner == ConversionRank::Exact ? ConversionRank::Exact : inner;
    }

    if (detail &&
        (category == ValueCategory::LValue ||
         category == ValueCategory::XValue) &&
        from_kind != cir::TypeKind::Array &&
        from_kind != cir::TypeKind::Function) {
        detail->standard.add(StandardConversionStep::LValueToRValue);
    }

    if (identity_types_match(
            cir::TypeRef{from_resolved, cir::QualNone, to.memory_space},
            cir::TypeRef{to_resolved, cir::QualNone, to.memory_space})) {
        return ConversionRank::Exact;
    }

    if ((from_kind == cir::TypeKind::Enum &&
         is_scoped_enum_type(from_resolved)) ||
        to_kind == cir::TypeKind::Enum) {
        return finish_bad();
    }

    QualificationConversionAnalysis qualification =
        analyze_qualification_conversion(
            cir::TypeRef{from_resolved,
                         cir::QualNone,
                         to.memory_space},
            cir::TypeRef{to_resolved,
                         cir::QualNone,
                         to.memory_space});
    if (qualification.has_indirection && qualification.similar &&
        qualification.allowed) {
        if (detail) {
            detail->standard.add(
                StandardConversionStep::QualificationAdjustment);
        }
        return ConversionRank::Exact;
    }

    if (function_pointer_conversion_matches(file_.type_ref(from_resolved),
                                            file_.type_ref(to_resolved))) {
        if (detail) {
            detail->standard.add(
                StandardConversionStep::FunctionPointerConversion);
        }
        return ConversionRank::Exact;
    }

    cir::BuiltinTypeKind from_builtin = builtin_kind_of(file_, from_resolved);
    cir::BuiltinTypeKind to_builtin = builtin_kind_of(file_, to_resolved);

    if (from_kind == cir::TypeKind::Record &&
        to_kind == cir::TypeKind::Record) {
        DerivedToBasePathResult base_result =
            analyze_derived_to_base_path(from_resolved, to_resolved);
        if (base_result.kind != DerivedToBasePathKind::NotFound) {
            if (detail) {
                detail->standard.add(StandardConversionStep::DerivedToBase);
            }
            return ConversionRank::Conversion;
        }
    }

    if (from_kind == cir::TypeKind::MemberPointer &&
        to_kind == cir::TypeKind::MemberPointer) {
        const auto* source_member =
            std::get_if<cir::MemberPointerTypePayload>(
                &file_.type_payload(from_resolved));
        const auto* target_member =
            std::get_if<cir::MemberPointerTypePayload>(
                &file_.type_payload(to_resolved));
        if (source_member && target_member) {
            cir::TypeRef source_value = source_member->member_type;
            cir::TypeRef target_value = target_member->member_type;
            bool same_value =
                file_.resolved_type(source_value.type) ==
                    file_.resolved_type(target_value.type) &&
                (source_value.qualifiers &
                 static_cast<uint8_t>(~target_value.qualifiers)) == 0;
            QualificationConversionAnalysis member_qualification =
                analyze_qualification_conversion(source_value,
                                                  target_value);
            bool member_function_adjustment =
                function_type_conversion_matches(source_value,
                                                 target_value);
            bool compatible_value = same_value ||
                (member_qualification.has_indirection &&
                 member_qualification.similar &&
                 member_qualification.allowed) ||
                member_function_adjustment;
            DerivedToBasePathResult class_path =
                analyze_derived_to_base_path(target_member->class_type.type,
                                             source_member->class_type.type);
            if (compatible_value &&
                class_path.kind != DerivedToBasePathKind::NotFound) {
                if (detail) {
                    detail->standard.add(
                        StandardConversionStep::MemberPointerConversion);
                    detail->standard.add(
                        StandardConversionStep::DerivedToBase);
                    if (!same_value) {
                        detail->standard.add(
                            member_function_adjustment
                                ? StandardConversionStep::
                                      FunctionPointerConversion
                                : StandardConversionStep::
                                      QualificationAdjustment);
                    }
                }
                return ConversionRank::Conversion;
            }
        }
    }

    if (to_kind == cir::TypeKind::Pointer) {
        if (from_kind == cir::TypeKind::Array) {
            const auto* array = std::get_if<cir::ArrayTypePayload>(
                &file_.type_payload(from_resolved));
            cir::TypeId target_pointee = file_.resolved_type(
                file_.pointer_pointee_type(to_resolved));
            bool exact_element = array && identity_types_match(
                cir::TypeRef{file_.resolved_type(array->element_type.type),
                             cir::QualNone, to.memory_space},
                cir::TypeRef{target_pointee, cir::QualNone,
                             to.memory_space});
            bool converts_to_void = array && file_.valid(target_pointee) &&
                builtin_kind_of(file_, target_pointee) ==
                    cir::BuiltinTypeKind::Void;
            if (exact_element || converts_to_void) {
                if (detail) {
                    detail->standard.add(
                        StandardConversionStep::ArrayToPointer);
                    if (converts_to_void) {
                        detail->standard.add(
                            StandardConversionStep::PointerConversion);
                    }
                }
                return converts_to_void
                    ? ConversionRank::Conversion
                    : ConversionRank::Exact;
            }
        }
        if (from_kind == cir::TypeKind::Function) {
            cir::TypeRef target_function =
                file_.pointer_pointee_ref(to_resolved);
            cir::TypeRef source_function = file_.type_ref(from_resolved);
            if (identity_types_match(source_function, target_function)) {
                if (detail) {
                    detail->standard.add(
                        StandardConversionStep::FunctionToPointer);
                }
                return ConversionRank::Exact;
            }
            if (function_type_conversion_matches(source_function,
                                                 target_function)) {
                if (detail) {
                    detail->standard.add(
                        StandardConversionStep::FunctionToPointer);
                    detail->standard.add(
                        StandardConversionStep::FunctionPointerConversion);
                }
                return ConversionRank::Exact;
            }
            return ConversionRank::Bad;
        }
        if (from_kind == cir::TypeKind::Pointer) {
            cir::TypeRef to_pointee_ref =
                file_.pointer_pointee_ref(to_resolved);
            cir::TypeRef from_pointee_ref =
                file_.pointer_pointee_ref(from_resolved);
            cir::TypeId to_pointee =
                file_.resolved_type(to_pointee_ref.type);
            cir::TypeId from_pointee =
                file_.resolved_type(from_pointee_ref.type);
            if (file_.valid(to_pointee) &&
                builtin_kind_of(file_, to_pointee) == cir::BuiltinTypeKind::Void) {
                if (detail) {
                    detail->standard.add(
                        StandardConversionStep::PointerConversion);
                }
                return ConversionRank::Conversion;
            }
            if (file_.valid(from_pointee) &&
                builtin_kind_of(file_, from_pointee) == cir::BuiltinTypeKind::Void) {

                return ConversionRank::Bad;
            }

            DerivedToBasePathResult base_result =
                analyze_derived_to_base_path(from_pointee, to_pointee);
            if (base_result.kind != DerivedToBasePathKind::NotFound) {
                if ((from_pointee_ref.qualifiers &
                     static_cast<uint8_t>(~to_pointee_ref.qualifiers)) != 0) {
                    return ConversionRank::Bad;
                }
                if (detail) {
                    detail->standard.add(
                        StandardConversionStep::PointerConversion);
                    detail->standard.add(
                        StandardConversionStep::DerivedToBase);
                    if (from_pointee_ref.qualifiers !=
                        to_pointee_ref.qualifiers) {
                        detail->standard.add(
                            StandardConversionStep::
                                QualificationAdjustment);
                    }
                }
                return ConversionRank::Conversion;
            }
            return ConversionRank::Bad;
        }
        return finish_bad();
    }

    if (to_builtin == cir::BuiltinTypeKind::Bool) {
        bool from_pointer_like =
            from_kind == cir::TypeKind::Pointer ||
            from_kind == cir::TypeKind::BlockPointer ||
            from_kind == cir::TypeKind::MemberPointer;
        if (from_pointer_like ||
            is_arithmetic_like(file_, from_resolved)) {
            if (detail) {
                detail->standard.add(
                    from_pointer_like
                        ? StandardConversionStep::PointerToBool
                        : StandardConversionStep::NumericConversion);
            }
            return ConversionRank::Conversion;
        }
        return finish_bad();
    }

    if (to_builtin == cir::BuiltinTypeKind::Int) {
        switch (from_builtin) {
            case cir::BuiltinTypeKind::Bool:
            case cir::BuiltinTypeKind::Char:
            case cir::BuiltinTypeKind::SChar:
            case cir::BuiltinTypeKind::UChar:
            case cir::BuiltinTypeKind::Short:
            case cir::BuiltinTypeKind::UShort:
                if (detail) {
                    detail->standard.add(
                        StandardConversionStep::Promotion);
                }
                return ConversionRank::Promotion;
            default:
                break;
        }
    }
    if (to_builtin == cir::BuiltinTypeKind::Double &&
        from_builtin == cir::BuiltinTypeKind::Float) {
        if (detail) {
            detail->standard.add(StandardConversionStep::Promotion);
        }
        return ConversionRank::Promotion;
    }

    if (is_arithmetic_like(file_, from_resolved) &&
        is_arithmetic_like(file_, to_resolved)) {
        if (detail) {
            detail->standard.add(StandardConversionStep::NumericConversion);
        }
        return ConversionRank::Conversion;
    }

    return finish_bad();
}

Session::UserConversionProbe Session::probe_user_defined_conversion(
    cir::TypeId from,
    ValueCategory category,
    cir::TypeRef to,
    bool allow_explicit_conversion_functions,
    const ExprResult* source_expression) const {
    UserConversionProbe probe;
    auto add_route = [&probe](cir::EntityId route) {
        if (!probe.viable) {
            probe.viable = true;
            probe.route = route;
            probe.unique = true;
        } else if (probe.route != route) {
            probe.unique = false;
            probe.route = {};
        }
    };
    if (!lang_opts_.is_cxx_mode()) {
        return probe;
    }
    cir::TypeId from_resolved = file_.resolved_type(from);
    cir::TypeId to_resolved = file_.resolved_type(to.type);
    if (!file_.valid(from_resolved) || !file_.valid(to_resolved)) {
        return probe;
    }
    bool from_is_record =
        file_.type(from_resolved).kind == cir::TypeKind::Record;
    bool to_is_record = file_.type(to_resolved).kind == cir::TypeKind::Record;
    if (!from_is_record && !to_is_record) {
        return probe;
    }
    if (from_is_record && to_is_record && from_resolved == to_resolved) {

        return probe;
    }
    bool target_is_base_of_source = from_is_record && to_is_record &&
        analyze_derived_to_base_path(from_resolved, to_resolved).kind !=
            DerivedToBasePathKind::NotFound;

    ExprResult source_view;
    source_view.type = from_resolved;
    source_view.category = category;
    if (source_expression) {
        source_view.value = source_expression->value;
        source_view.place = source_expression->place;
        source_view.semantic_object_qualifiers =
            source_expression->semantic_object_qualifiers;
        source_view.unevaluated_semantic_operand =
            source_expression->unevaluated_semantic_operand;
    }

    if (to_is_record) {
        std::vector<ExprResult> arguments;
        arguments.push_back(source_view);
        std::vector<cir::EntityId> constructors;
        const_cast<Session*>(this)->collect_constructor_candidates(
            to_resolved, arguments, ConstructorInitializationKind::Copy,
            SrcLoc(), constructors);
        const cir::RecordFacts* facts =
            file_.record_facts_for_type(to_resolved);
        bool has_virtual_bases = facts && !facts->virtual_bases.empty();
        for (cir::EntityId constructor : constructors) {
            const cir::RecordMethodFact* method =
                file_.method_fact(constructor);
            if (!method || method->is_explicit ||
                method->constraint_satisfaction ==
                    cir::ConstraintSatisfactionKind::Unsatisfied ||
                method->constraint_satisfaction ==
                    cir::ConstraintSatisfactionKind::Invalid) {
                continue;
            }
            const cir::FunctionTypePayload* payload = function_payload_of(
                file_, file_.entity(constructor).type);
            if (!payload || payload->parameters.size() < 2) {
                continue;
            }

            size_t real_parameters = payload->parameters.size() - 1;
            if (has_virtual_bases && real_parameters >= 2) {
                real_parameters -= 2;
            }
            if (real_parameters < 1) {
                continue;
            }
            bool trailing_defaulted = true;
            for (size_t i = 1; i < real_parameters; ++i) {
                if (!callable_default_argument(constructor, i)) {
                    trailing_defaulted = false;
                    break;
                }
            }
            if (trailing_defaulted &&
                conversion_rank(source_view, payload->parameters[1],
                                /*from_qualifiers=*/0,
                                /*detail=*/nullptr,
                                /*allow_user_defined=*/false) !=
                    ConversionRank::Bad) {
                add_route(constructor);
            }
        }
    }

    if (from_is_record && !target_is_base_of_source) {
        std::vector<cir::EntityId> conversions;
        const_cast<Session*>(this)->collect_conversion_function_candidates(
            source_view, to_resolved,
            allow_explicit_conversion_functions, SrcLoc(),
            conversions);
        for (cir::EntityId conversion : conversions) {
            const cir::RecordMethodFact* method =
                file_.method_fact(conversion);
            if (!method || method->constraint_satisfaction ==
                    cir::ConstraintSatisfactionKind::Unsatisfied ||
                method->constraint_satisfaction ==
                    cir::ConstraintSatisfactionKind::Invalid) {
                continue;
            }
            ConversionResultValue result = conversion_result_value(
                file_, conversion_function_return_type(file_, *method));
            if (result.type.valid() &&
                conversion_rank(result.type, result.category, to,
                                result.qualifiers,
                                /*detail=*/nullptr,
                                /*allow_user_defined=*/false) !=
                    ConversionRank::Bad) {
                add_route(conversion);
            }
        }
    }
    return probe;
}

cir::EntityId Session::select_overload(const std::vector<cir::EntityId>& candidates,
                                       const std::vector<ExprResult>& arguments,
                                       bool member_object_leading,
                                       bool* ambiguous_out,
                                       cir::TypeId conversion_result_target,
                                       OverloadAmbiguityInfo* ambiguity_info) {
    std::vector<OverloadCandidate> inputs;
    inputs.reserve(candidates.size());
    for (cir::EntityId candidate : candidates) {
        inputs.push_back(OverloadCandidate{candidate,
                                           member_object_leading,
                                           /*ranks_conversion_result=*/true});
    }
    return select_overload(inputs,
                           arguments,
                           ambiguous_out,
                           conversion_result_target,
                           ambiguity_info);
}

cir::EntityId Session::select_overload(const std::vector<OverloadCandidate>& candidates,
                                       const std::vector<ExprResult>& arguments,
                                       bool* ambiguous_out,
                                       cir::TypeId conversion_result_target,
                                       OverloadAmbiguityInfo* ambiguity_info,
                                       bool allow_user_defined_argument_conversions,
                                       cir::TypeId direct_constructor_target) {
    OverloadSelection selection = select_overload_detailed(
        candidates, arguments, conversion_result_target, ambiguity_info,
        allow_user_defined_argument_conversions,
        direct_constructor_target);
    if (ambiguous_out) {
        *ambiguous_out = selection.ambiguous;
    }
    return selection.entity;
}

int Session::compare_implicit_conversion_sequences(
    ConversionRank lhs_rank,
    const ConversionDetail& lhs,
    ConversionRank rhs_rank,
    const ConversionDetail& rhs,
    bool implicit_object_parameter) const {

    if (lhs.list_plan && rhs.list_plan &&
        lhs.list_plan->destination != rhs.list_plan->destination) {
        if (lhs.list_plan->destination ==
            ListInitializationDestination::InitializerList) {
            return 1;
        }
        if (rhs.list_plan->destination ==
            ListInitializationDestination::InitializerList) {
            return -1;
        }
    }
    if (lhs.list_plan && rhs.list_plan &&
        lhs.list_plan->destination == ListInitializationDestination::Array &&
        rhs.list_plan->destination == ListInitializationDestination::Array) {
        cir::TypeId lhs_array =
            file_.resolved_type(lhs.list_plan->target.type);
        cir::TypeId rhs_array =
            file_.resolved_type(rhs.list_plan->target.type);
        const auto* lhs_payload = file_.valid(lhs_array)
            ? std::get_if<cir::ArrayTypePayload>(
                  &file_.type_payload(lhs_array))
            : nullptr;
        const auto* rhs_payload = file_.valid(rhs_array)
            ? std::get_if<cir::ArrayTypePayload>(
                  &file_.type_payload(rhs_array))
            : nullptr;
        if (lhs_payload && rhs_payload &&
            file_.resolved_type(lhs_payload->element_type.type) ==
                file_.resolved_type(rhs_payload->element_type.type)) {
            size_t lhs_count = lhs_payload->size.value_or(
                lhs.list_plan->elements.size());
            size_t rhs_count = rhs_payload->size.value_or(
                rhs.list_plan->elements.size());
            if (lhs_count != rhs_count) {
                return lhs_count < rhs_count ? 1 : -1;
            }
            bool lhs_known = lhs_payload->size.has_value();
            bool rhs_known = rhs_payload->size.has_value();
            if (lhs_known != rhs_known) {
                return lhs_known ? 1 : -1;
            }
        }
    }
    if (lhs_rank != rhs_rank) {
        return lhs_rank < rhs_rank ? 1 : -1;
    }

    auto standard_adjustment_extends =
        [&](const ConversionDetail& base,
            const ConversionDetail& adjusted) {
            auto has_adjustment =
                [](const StandardConversionSequence& sequence) {
                    return sequence.has(StandardConversionStep::
                                            QualificationAdjustment) ||
                        sequence.has(StandardConversionStep::
                                         FunctionPointerConversion);
                };
            if (has_adjustment(base.standard) ||
                !has_adjustment(adjusted.standard) ||
                !base.standard.target.valid() ||
                !adjusted.standard.target.valid()) {
                return false;
            }
            QualificationConversionAnalysis qualification =
                analyze_qualification_conversion(base.standard.target,
                                                 adjusted.standard.target);
            return (qualification.has_indirection &&
                    qualification.similar && qualification.allowed) ||
                function_pointer_conversion_matches(base.standard.target,
                                                    adjusted.standard.target);
        };

    if (standard_adjustment_extends(lhs, rhs)) {
        return 1;
    }
    if (standard_adjustment_extends(rhs, lhs)) {
        return -1;
    }

    auto qualification_yield_compare =
        [&](const ConversionDetail& a_detail,
            const ConversionDetail& b_detail) {
            const StandardConversionSequence& a = a_detail.standard;
            const StandardConversionSequence& b = b_detail.standard;
            constexpr uint16_t qualification_step = static_cast<uint16_t>(
                StandardConversionStep::QualificationAdjustment);
            if (!a.source.valid() || a.source != b.source ||
                !a.target.valid() || !b.target.valid() ||
                a.target == b.target ||
                ((a.steps | b.steps) & qualification_step) == 0 ||
                (a.steps & ~qualification_step) !=
                    (b.steps & ~qualification_step)) {
                return 0;
            }
            QualificationConversionAnalysis a_to_b =
                analyze_qualification_conversion(a.target, b.target);
            QualificationConversionAnalysis b_to_a =
                analyze_qualification_conversion(b.target, a.target);
            bool a_less_qualified = a_to_b.has_indirection &&
                a_to_b.similar && a_to_b.allowed;
            bool b_less_qualified = b_to_a.has_indirection &&
                b_to_a.similar && b_to_a.allowed;
            if (a_less_qualified == b_less_qualified) {
                return 0;
            }
            return a_less_qualified ? 1 : -1;
        };
    if (int qualification = qualification_yield_compare(lhs, rhs);
        qualification != 0) {
        return qualification;
    }

    auto pointee_type = [&](cir::TypeRef ref) -> cir::TypeId {
        cir::TypeId type = file_.resolved_type(ref.type);
        if (!file_.valid(type) ||
            file_.type(type).kind != cir::TypeKind::Pointer) {
            return {};
        }
        return file_.resolved_type(file_.pointer_pointee_type(type));
    };
    auto member_pointer_class = [&](cir::TypeRef ref) -> cir::TypeId {
        cir::TypeId type = file_.resolved_type(ref.type);
        if (!file_.valid(type) ||
            file_.type(type).kind != cir::TypeKind::MemberPointer) {
            return {};
        }
        const auto* member = std::get_if<cir::MemberPointerTypePayload>(
            &file_.type_payload(type));
        return member
            ? file_.resolved_type(member->class_type.type)
            : cir::TypeId{};
    };
    auto is_derived_from = [&](cir::TypeId derived, cir::TypeId base) {
        if (!is_record_kind(file_, derived) ||
            !is_record_kind(file_, base) ||
            file_.resolved_type(derived) == file_.resolved_type(base)) {
            return false;
        }
        return analyze_derived_to_base_path(derived, base).kind !=
            DerivedToBasePathKind::NotFound;
    };
    auto hierarchy_standard_compare =
        [&](const ConversionDetail& a_detail,
            const ConversionDetail& b_detail) {
            const StandardConversionSequence& a = a_detail.standard;
            const StandardConversionSequence& b = b_detail.standard;
            if (!a.source.valid() || !b.source.valid() ||
                !a.target.valid() || !b.target.valid()) {
                return 0;
            }

            cir::TypeId a_source_pointer = pointee_type(a.source);
            cir::TypeId b_source_pointer = pointee_type(b.source);
            bool a_pointer_to_bool = a_source_pointer.valid() &&
                is_bool_type(file_.resolved_type(a.target.type));
            bool b_pointer_to_bool = b_source_pointer.valid() &&
                is_bool_type(file_.resolved_type(b.target.type));
            if (a_pointer_to_bool != b_pointer_to_bool) {
                return a_pointer_to_bool ? -1 : 1;
            }

            cir::TypeId a_source_member = member_pointer_class(a.source);
            cir::TypeId b_source_member = member_pointer_class(b.source);
            bool a_member_to_bool = a_source_member.valid() &&
                is_bool_type(file_.resolved_type(a.target.type));
            bool b_member_to_bool = b_source_member.valid() &&
                is_bool_type(file_.resolved_type(b.target.type));
            if (a_member_to_bool != b_member_to_bool) {
                return a_member_to_bool ? -1 : 1;
            }

            cir::TypeId a_target_member = member_pointer_class(a.target);
            cir::TypeId b_target_member = member_pointer_class(b.target);
            if (a_source_member.valid() && b_source_member.valid() &&
                a_target_member.valid() && b_target_member.valid()) {
                if (a_source_member == b_source_member) {
                    if (is_derived_from(b_target_member, a_target_member)) {
                        return 1;
                    }
                    if (is_derived_from(a_target_member, b_target_member)) {
                        return -1;
                    }
                }
                if (a_target_member == b_target_member) {
                    if (is_derived_from(a_source_member, b_source_member)) {
                        return 1;
                    }
                    if (is_derived_from(b_source_member, a_source_member)) {
                        return -1;
                    }
                }
            }

            cir::TypeId a_target_pointer = pointee_type(a.target);
            cir::TypeId b_target_pointer = pointee_type(b.target);
            if (a_source_pointer.valid() && b_source_pointer.valid() &&
                a_target_pointer.valid() && b_target_pointer.valid()) {
                bool same_source = a_source_pointer == b_source_pointer;
                bool same_target = a_target_pointer == b_target_pointer;
                bool a_target_void = is_void_type(a_target_pointer);
                bool b_target_void = is_void_type(b_target_pointer);
                if (same_source && a_target_void != b_target_void) {
                    return a_target_void ? -1 : 1;
                }
                if (same_source && !a_target_void && !b_target_void) {
                    if (is_derived_from(a_target_pointer, b_target_pointer)) {
                        return 1;
                    }
                    if (is_derived_from(b_target_pointer, a_target_pointer)) {
                        return -1;
                    }
                }
                if (same_target) {
                    if (is_derived_from(b_source_pointer, a_source_pointer)) {
                        return 1;
                    }
                    if (is_derived_from(a_source_pointer, b_source_pointer)) {
                        return -1;
                    }
                }
            }

            cir::TypeId a_source = file_.resolved_type(a.source.type);
            cir::TypeId b_source = file_.resolved_type(b.source.type);
            cir::TypeId a_target = file_.resolved_type(a.target.type);
            cir::TypeId b_target = file_.resolved_type(b.target.type);
            if (a_source == b_source && is_record_kind(file_, a_target) &&
                is_record_kind(file_, b_target)) {
                if (is_derived_from(a_target, b_target)) {
                    return 1;
                }
                if (is_derived_from(b_target, a_target)) {
                    return -1;
                }
            }
            if (a_target == b_target && is_record_kind(file_, a_source) &&
                is_record_kind(file_, b_source)) {
                if (is_derived_from(b_source, a_source)) {
                    return 1;
                }
                if (is_derived_from(a_source, b_source)) {
                    return -1;
                }
            }
            return 0;
        };
    auto reference_binding_compare =
        [&](const ConversionDetail& a_detail,
            const ConversionDetail& b_detail) {
            const StandardConversionSequence& a = a_detail.standard;
            const StandardConversionSequence& b = b_detail.standard;
            if (!a.has(StandardConversionStep::ReferenceBinding) ||
                !b.has(StandardConversionStep::ReferenceBinding)) {
                return 0;
            }
            cir::TypeId a_target = file_.resolved_type(a.target.type);
            cir::TypeId b_target = file_.resolved_type(b.target.type);
            if (!file_.valid(a_target) || !file_.valid(b_target)) {
                return 0;
            }
            cir::TypeKind a_kind = file_.type(a_target).kind;
            cir::TypeKind b_kind = file_.type(b_target).kind;
            bool a_lvalue = a_kind == cir::TypeKind::LValueReference;
            bool a_rvalue = a_kind == cir::TypeKind::RValueReference;
            bool b_lvalue = b_kind == cir::TypeKind::LValueReference;
            bool b_rvalue = b_kind == cir::TypeKind::RValueReference;
            if ((!a_lvalue && !a_rvalue) ||
                (!b_lvalue && !b_rvalue) ||
                a.source_category != b.source_category) {
                return 0;
            }
            bool source_is_rvalue =
                a.source_category == ValueCategory::PrValue ||
                a.source_category == ValueCategory::XValue;
            if (source_is_rvalue && a_rvalue != b_rvalue) {
                return a_rvalue ? 1 : -1;
            }
            cir::TypeId source_type = file_.resolved_type(a.source.type);
            bool source_is_lvalue_function =
                (a.source_category == ValueCategory::LValue ||
                 a.source_category == ValueCategory::FunctionDesignator) &&
                file_.valid(source_type) &&
                file_.type(source_type).kind == cir::TypeKind::Function;
            if (source_is_lvalue_function && a_lvalue != b_lvalue) {
                return a_lvalue ? 1 : -1;
            }
            return 0;
        };

    if (!implicit_object_parameter) {
        if (int hierarchy = hierarchy_standard_compare(lhs, rhs);
            hierarchy != 0) {
            return hierarchy;
        }
        if (int reference = reference_binding_compare(lhs, rhs);
            reference != 0) {
            return reference;
        }
    }
    if (lhs_rank == ConversionRank::UserDefined) {
        bool same_user_conversion =
            lhs.user_conversion_unique && rhs.user_conversion_unique &&
            lhs.user_conversion == rhs.user_conversion;
        bool same_aggregate_initialization =
            lhs.list_plan && rhs.list_plan &&
            lhs.list_plan->destination ==
                ListInitializationDestination::Aggregate &&
            rhs.list_plan->destination ==
                ListInitializationDestination::Aggregate &&
            file_.resolved_type(lhs.list_plan->target.type) ==
                file_.resolved_type(rhs.list_plan->target.type);
        if (!same_user_conversion && !same_aggregate_initialization) {
            return 0;
        }
        if (lhs.trailing_standard.trailing_binding !=
                rhs.trailing_standard.trailing_binding &&
            lhs.trailing_standard.trailing_binding != TrailingBinding::None &&
            rhs.trailing_standard.trailing_binding != TrailingBinding::None) {
            return lhs.trailing_standard.trailing_binding ==
                    TrailingBinding::RValueReference
                ? 1
                : -1;
        }
    }
    if (lhs.standard.bound_referred.valid() &&
        lhs.standard.bound_referred == rhs.standard.bound_referred &&
        lhs.standard.bound_qualifiers != rhs.standard.bound_qualifiers) {
        if ((lhs.standard.bound_qualifiers &
             ~rhs.standard.bound_qualifiers) == 0) {
            return 1;
        }
        if ((rhs.standard.bound_qualifiers &
             ~lhs.standard.bound_qualifiers) == 0) {
            return -1;
        }
    }
    return 0;
}

Session::OverloadSelection Session::select_overload_detailed(
    const std::vector<OverloadCandidate>& candidates,
    const std::vector<ExprResult>& arguments,
    cir::TypeId conversion_result_target,
    OverloadAmbiguityInfo* ambiguity_info,
    bool allow_user_defined_argument_conversions,
    cir::TypeId direct_constructor_target) {
    bump_overload_counter(PerfCounter::OverloadResolveCalls);
    if (ambiguity_info) {
        *ambiguity_info = {};
    }

    auto object_qualifiers = [&](const ExprResult& argument) -> uint8_t {
        if (argument.semantic_object_qualifiers.has_value()) {
            return *argument.semantic_object_qualifiers;
        }
        if ((argument.category != ValueCategory::LValue &&
             argument.category != ValueCategory::XValue) ||
            !argument.place.valid()) {
            return 0;
        }

        uint8_t qualifiers = 0;
        const cir::Inst& place_inst = file_.inst(argument.place);
        qualifiers |= file_.place_object_ref(place_inst.result_type).qualifiers;
        if (place_inst.place_fact.valid()) {
            qualifiers |= file_.place_fact(place_inst.place_fact)
                .object_type.qualifiers;
        }
        return qualifiers;
    };
    struct Scored {
        cir::EntityId entity{};
        std::vector<ConversionRank> ranks;
        std::vector<ConversionDetail> details;
        ConversionRank result_rank = ConversionRank::Bad;
        ConversionDetail result_detail;
        bool has_result_rank = false;
        bool is_template_specialization = false;
        bool ranks_conversion_result = false;
        size_t ordering_argument_count = 0;
        OperatorRewriteKind rewrite_kind = OperatorRewriteKind::None;
        bool has_reversed_parameters = false;
        bool has_implicit_object_rank = false;
    };
    std::vector<Scored> viable;

    std::vector<uint8_t> argument_object_qualifiers(arguments.size(), 0);
    for (size_t i = 0; i < arguments.size(); ++i) {
        argument_object_qualifiers[i] = object_qualifiers(arguments[i]);
    }

    struct ConversionMemoKey {
        uint32_t argument = 0;
        uint32_t type_index = 0;
        uint32_t type_generation = 0;
        uint32_t qualifiers_and_space = 0;
        bool operator==(const ConversionMemoKey&) const = default;
    };
    struct ConversionMemoKeyHash {
        size_t operator()(const ConversionMemoKey& key) const {
            uint64_t hashed = key.argument;
            hashed = hashed * 0x9E3779B97F4A7C15ull + key.type_index;
            hashed = hashed * 0x9E3779B97F4A7C15ull + key.type_generation;
            hashed = hashed * 0x9E3779B97F4A7C15ull + key.qualifiers_and_space;
            return static_cast<size_t>(hashed);
        }
    };
    struct ConversionMemoEntry {
        ConversionRank rank = ConversionRank::Bad;
        ConversionDetail detail;
    };
    std::unordered_map<ConversionMemoKey, ConversionMemoEntry,
                       ConversionMemoKeyHash> conversion_memo;
    auto permits_explicit_conversion_function =
        [&](cir::TypeRef parameter) {
            cir::TypeId target = file_.resolved_type(parameter.type);
            if (!direct_constructor_target.valid() ||
                !file_.valid(target) ||
                (file_.type(target).kind !=
                     cir::TypeKind::LValueReference &&
                 file_.type(target).kind !=
                     cir::TypeKind::RValueReference)) {
                return false;
            }
            return file_.resolved_type(
                       file_.reference_referred_ref(target).type) ==
                file_.resolved_type(direct_constructor_target);
        };
    auto memoized_conversion_rank = [&](size_t argument_index,
                                        cir::TypeRef to,
                                        ConversionDetail* detail) {
        ConversionMemoKey key;
        key.argument = static_cast<uint32_t>(argument_index);
        key.type_index = to.type.index;
        key.type_generation = to.type.generation;
        key.qualifiers_and_space =
            (static_cast<uint32_t>(to.qualifiers) << 8) |
            static_cast<uint32_t>(to.memory_space);
        auto found = conversion_memo.find(key);
        if (found != conversion_memo.end()) {
            bump_overload_counter(PerfCounter::OverloadConversionCacheHits);
            *detail = found->second.detail;
            return found->second.rank;
        }
        bump_overload_counter(PerfCounter::OverloadConversionCacheMisses);
        ConversionRank rank =
            conversion_rank(arguments[argument_index],
                            to,
                            argument_object_qualifiers[argument_index],
                            detail,
                            allow_user_defined_argument_conversions,
                            permits_explicit_conversion_function(to));
        detail->standard.rank = rank;
        conversion_memo.emplace(key, ConversionMemoEntry{rank, *detail});
        return rank;
    };

    std::vector<OverloadCandidate> filtered;
    filtered.reserve(candidates.size());
    std::unordered_map<uint64_t, std::vector<size_t>> supersede_buckets;
    std::vector<uint64_t> supersede_keys(candidates.size(), 0);
    std::vector<bool> supersede_bucketed(candidates.size(), false);
    for (size_t i = 0; i < candidates.size(); ++i) {
        if (!candidates[i].entity.valid() || !file_.valid(candidates[i].entity)) {
            continue;
        }
        const cir::Entity& entity = file_.entity(candidates[i].entity);
        const cir::FunctionTypePayload* payload =
            function_payload_of(file_, entity.type);
        if (!payload) {
            continue;
        }
        const cir::TemplateSpecializationFact* spec =
            file_.template_specialization(candidates[i].entity);
        uint64_t key = static_cast<uint64_t>(entity.kind);
        key = key * 0x9E3779B97F4A7C15ull +
              (entity.name.valid()
                   ? static_cast<uint64_t>(entity.name.index) + 1
                   : 0);
        key = key * 0x9E3779B97F4A7C15ull +
              (spec ? static_cast<uint64_t>(spec->template_entity.index) + 1
                    : 0);
        key = key * 0x9E3779B97F4A7C15ull + payload->parameters.size();
        key = key * 0x9E3779B97F4A7C15ull +
              ((static_cast<uint64_t>(payload->is_variadic) << 4) |
               (static_cast<uint64_t>(payload->member_is_const) << 3) |
               (static_cast<uint64_t>(payload->member_is_volatile) << 2) |
               static_cast<uint64_t>(payload->member_ref_qualifier));
        supersede_keys[i] = key;
        supersede_bucketed[i] = true;
        supersede_buckets[key].push_back(i);
    }
    for (size_t i = 0; i < candidates.size(); ++i) {
        if (!candidates[i].entity.valid() || !file_.valid(candidates[i].entity)) {
            continue;
        }

        if (template_info(candidates[i].entity) != nullptr) {
            continue;
        }
        bool superseded = false;
        if (supersede_bucketed[i]) {
            const cir::TemplateSpecializationFact* spec_i =
                file_.template_specialization(candidates[i].entity);
            for (size_t j : supersede_buckets[supersede_keys[i]]) {
                if (j <= i) {
                    continue;
                }
                const cir::TemplateSpecializationFact* spec_j =
                    file_.template_specialization(candidates[j].entity);
                superseded =
                    candidates[i].rewrite_kind == candidates[j].rewrite_kind &&
                    candidates[i].has_reversed_parameters ==
                        candidates[j].has_reversed_parameters &&
                    file_.entity(candidates[i].entity).kind ==
                        file_.entity(candidates[j].entity).kind &&
                    file_.entity(candidates[i].entity).name ==
                        file_.entity(candidates[j].entity).name &&
                    (spec_i != nullptr) == (spec_j != nullptr) &&
                    (!spec_i || !spec_j ||
                     spec_i->template_entity == spec_j->template_entity) &&
                    function_signatures_match(file_.entity(candidates[i].entity).type,
                                              file_.entity(candidates[j].entity).type);
                if (superseded) {
                    const cir::RecordMethodFact* method_i =
                        file_.method_fact(candidates[i].entity);
                    const cir::RecordMethodFact* method_j =
                        file_.method_fact(candidates[j].entity);
                    superseded = (!method_i && !method_j) ||
                        (method_i && method_j &&
                         !method_i->inherited_constructor &&
                         !method_j->inherited_constructor &&
                         method_i->associated_constraint_fingerprint ==
                             method_j->associated_constraint_fingerprint);
                }
                if (superseded) {
                    break;
                }
            }
        }
        if (!superseded) {
            filtered.push_back(candidates[i]);
        }
    }

    for (const OverloadCandidate& input : filtered) {
        cir::EntityId candidate = input.entity;
        if (!candidate.valid() || !file_.valid(candidate)) {
            continue;
        }
        const cir::Entity& entity = file_.entity(candidate);
        const cir::FunctionTypePayload* payload_view =
            function_payload_of(file_, entity.type);
        if (!payload_view) {
            continue;
        }

        const cir::FunctionTypePayload payload = *payload_view;
        bump_overload_counter(PerfCounter::OverloadCandidateEvaluations);
        bool is_member = entity.kind == cir::EntityKind::Method ||
                         entity.kind == cir::EntityKind::Constructor ||
                         entity.kind == cir::EntityKind::Destructor ||
                         entity.is_static_member_function;
        const cir::RecordMethodFact* fact =
            is_member ? file_.method_fact(candidate) : nullptr;
        if (fact &&
            (fact->constraint_satisfaction ==
                 cir::ConstraintSatisfactionKind::Unsatisfied ||
             fact->constraint_satisfaction ==
                 cir::ConstraintSatisfactionKind::Invalid)) {
            continue;
        }
        bool has_this = is_member &&
                        !entity.is_static_member_function &&
                        !(fact && fact->is_static);

        size_t param_offset = has_this ? 1 : 0;
        size_t argument_offset = 0;
        Scored scored;
        scored.entity = candidate;
        scored.rewrite_kind = input.rewrite_kind;
        auto effective_argument_index = [&](size_t index) {
            return input.has_reversed_parameters && arguments.size() == 2
                ? size_t{1} - index
                : index;
        };

        if (input.member_object_leading) {
            if (has_this) {

                cir::TypeId class_type =
                    file_.pointer_pointee_type(file_.resolved_type(
                        payload.parameters.empty()
                            ? cir::TypeId{}
                            : payload.parameters.front().type));
                size_t object_index = effective_argument_index(0);
                cir::TypeId source_object_type = arguments.empty()
                    ? cir::TypeId{}
                    : arguments[object_index].type;
                cir::TypeId object_parameter_type =
                    input.canonical_member_object_type.valid()
                        ? input.canonical_member_object_type
                        : class_type;
                bool same_class = arguments.empty()
                    ? false
                    : types_compatible(
                          cir::TypeRef{file_.resolved_type(
                                           object_parameter_type),
                                       cir::QualNone,
                                       cir::MemorySpace::Default},
                          cir::TypeRef{file_.resolved_type(source_object_type),
                                       cir::QualNone,
                                       cir::MemorySpace::Default});
                bool derived_object = !arguments.empty() &&
                    derived_to_base_path(source_object_type,
                                         object_parameter_type, nullptr);
                if (!same_class && !derived_object &&
                    !input.canonical_member_object_type.valid()) {
                    continue;
                }
                bool method_is_const = payload.member_is_const;
                bool method_is_volatile = payload.member_is_volatile;
                uint8_t object_cv = argument_object_qualifiers[object_index];
                if (!method_is_const &&
                    (object_cv & cir::QualConst) != 0) {
                    continue;
                }
                if (!method_is_volatile &&
                    (object_cv & cir::QualVolatile) != 0) {
                    continue;
                }
                bool object_is_lvalue =
                    arguments[object_index].category == ValueCategory::LValue;
                if (payload.member_ref_qualifier ==
                        cir::FunctionRefQualifierKind::LValue &&
                    !object_is_lvalue) {
                    continue;
                }
                if (payload.member_ref_qualifier ==
                        cir::FunctionRefQualifierKind::RValue &&
                    object_is_lvalue) {
                    continue;
                }
                ConversionRank object_rank = same_class
                    ? ConversionRank::Exact
                    : ConversionRank::Conversion;
                scored.ranks.push_back(object_rank);
                scored.has_implicit_object_rank = true;
                ConversionDetail object_detail;
                object_detail.standard.bound_referred =
                    file_.resolved_type(object_parameter_type);
                object_detail.standard.bound_qualifiers = cir::QualNone;
                object_detail.standard.source =
                    file_.type_ref(arguments[object_index].type);
                object_detail.standard.target =
                    file_.type_ref(object_parameter_type);
                object_detail.standard.source_category =
                    arguments[object_index].category;
                object_detail.standard.rank = object_rank;
                if (!same_class) {
                    object_detail.standard.add(
                        StandardConversionStep::DerivedToBase);
                }
                object_detail.standard.add(
                    StandardConversionStep::ReferenceBinding);
                if (method_is_const) {
                    object_detail.standard.bound_qualifiers |= cir::QualConst;
                }
                if (method_is_volatile) {
                    object_detail.standard.bound_qualifiers |=
                        cir::QualVolatile;
                }
                scored.details.push_back(object_detail);
                argument_offset = 1;
            } else if (is_member) {

                argument_offset = 1;
            }
        }

        size_t remaining_params = payload.parameters.size() - param_offset;
        if (is_member &&
            (entity.kind == cir::EntityKind::Constructor ||
             entity.kind == cir::EntityKind::Destructor)) {

            const cir::RecordFacts* record = file_.record_facts(entity.parent);
            if (record && !record->virtual_bases.empty()) {
                for (int i = 0; i < 2 && remaining_params > 0; ++i) {
                    --remaining_params;
                }
            }
        }
        size_t remaining_arguments = arguments.size() - argument_offset;
        size_t minimum_params = remaining_params;
        while (minimum_params > 0 &&
               callable_default_argument(candidate,
                                         minimum_params - 1)) {
            --minimum_params;
        }
        if (payload.is_variadic) {
            if (remaining_arguments < minimum_params) {
                continue;
            }
        } else if (remaining_arguments < minimum_params ||
                   remaining_arguments > remaining_params) {
            continue;
        }

        scored.is_template_specialization =
            file_.template_specialization(candidate) != nullptr;
        scored.ranks_conversion_result = input.ranks_conversion_result;
        scored.ordering_argument_count = remaining_arguments +
            ((input.member_object_leading && has_this) ? 1 : 0);
        scored.has_reversed_parameters = input.has_reversed_parameters;
        bool viable_candidate = true;
        for (size_t i = 0; i < remaining_arguments; ++i) {
            ConversionRank rank;
            ConversionDetail detail;
            if (i < remaining_params) {
                rank = memoized_conversion_rank(
                    effective_argument_index(argument_offset + i),
                    payload.parameters[param_offset + i],
                    &detail);
            } else {
                rank = ConversionRank::Ellipsis;
            }
            if (rank == ConversionRank::Bad) {
                viable_candidate = false;
                break;
            }
            scored.ranks.push_back(rank);
            scored.details.push_back(detail);
        }
        if (viable_candidate) {
            if (input.has_reversed_parameters && scored.ranks.size() == 2) {
                std::swap(scored.ranks[0], scored.ranks[1]);
                std::swap(scored.details[0], scored.details[1]);
                scored.has_implicit_object_rank = false;
            }
            if (conversion_result_target.valid() &&
                input.ranks_conversion_result) {
                cir::TypeRef return_type = payload.return_type;
                ConversionResultValue result_value =
                    conversion_result_value(file_, return_type);
                if (!result_value.type.valid()) {
                    continue;
                }
                scored.result_rank = conversion_rank(
                    result_value.type,
                    result_value.category,
                    file_.type_ref(conversion_result_target),
                    result_value.qualifiers,
                    &scored.result_detail);
                scored.result_detail.standard.rank = scored.result_rank;
                if (scored.result_rank == ConversionRank::Bad) {
                    continue;
                }
                scored.has_result_rank = true;
            }
            viable.push_back(std::move(scored));
        }
    }

    if (viable.empty()) {
        return {};
    }
    if (viable.size() == 1) {
        return OverloadSelection{viable.front().entity,
                                 viable.front().rewrite_kind,
                                 viable.front().has_reversed_parameters,
                                 false};
    }

    auto position_compare = [&](const Scored& a, const Scored& b,
                                size_t i) -> int {
        const ConversionDetail& da = a.details[i];
        const ConversionDetail& db = b.details[i];
        return compare_implicit_conversion_sequences(
            a.ranks[i],
            da,
            b.ranks[i],
            db,
            i == 0 && a.has_implicit_object_rank &&
                b.has_implicit_object_rank);
    };
    auto better = [&](const Scored& a, const Scored& b) {

        bool any_better = false;
        size_t common = std::min(a.ranks.size(), b.ranks.size());
        for (size_t i = 0; i < common; ++i) {
            int cmp = position_compare(a, b, i);
            if (cmp < 0) {
                return false;
            }
            if (cmp > 0) {
                any_better = true;
            }
        }
        if (any_better) {
            return true;
        }
        if (a.has_result_rank && b.has_result_rank) {
            int result_comparison =
                compare_implicit_conversion_sequences(
                    a.result_rank,
                    a.result_detail,
                    b.result_rank,
                    b.result_detail);
            if (result_comparison != 0) {
                return result_comparison > 0;
            }
        }
        if (!a.is_template_specialization && b.is_template_specialization) {
            return true;
        }
        const cir::RecordMethodFact* a_method = file_.method_fact(a.entity);
        const cir::RecordMethodFact* b_method = file_.method_fact(b.entity);
        if (a_method && b_method) {
            bool a_inherited =
                a_method->inherited_constructor.has_value();
            bool b_inherited =
                b_method->inherited_constructor.has_value();
            if (a_inherited != b_inherited) {
                return !a_inherited;
            }
            if (a_inherited && b_inherited) {
                cir::EntityId a_origin_owner =
                    a_method->inherited_constructor->origin_record;
                cir::EntityId b_origin_owner =
                    b_method->inherited_constructor->origin_record;
                if (a_origin_owner.valid() && b_origin_owner.valid() &&
                    a_origin_owner != b_origin_owner &&
                    file_.valid(a_origin_owner) &&
                    file_.valid(b_origin_owner)) {
                    bool a_origin_more_derived = derived_to_base_path(
                        file_.entity(a_origin_owner).type,
                        file_.entity(b_origin_owner).type, nullptr);
                    bool b_origin_more_derived = derived_to_base_path(
                        file_.entity(b_origin_owner).type,
                        file_.entity(a_origin_owner).type, nullptr);
                    if (a_origin_more_derived != b_origin_more_derived) {
                        return a_origin_more_derived;
                    }
                }
            }
            cir::EntityId a_owner = file_.entity(a.entity).parent;
            cir::EntityId b_owner = file_.entity(b.entity).parent;
            if (a_owner.valid() && b_owner.valid() && a_owner != b_owner &&
                file_.valid(a_owner) && file_.valid(b_owner)) {
                bool a_is_more_derived = derived_to_base_path(
                    file_.entity(a_owner).type,
                    file_.entity(b_owner).type,
                    nullptr);
                bool b_is_more_derived = derived_to_base_path(
                    file_.entity(b_owner).type,
                    file_.entity(a_owner).type,
                    nullptr);
                if (a_is_more_derived != b_is_more_derived) {
                    return a_is_more_derived;
                }
            }
        }
        if (!(a.is_template_specialization &&
              b.is_template_specialization) &&
            a_method && b_method &&
            b_method->associated_constraint_fingerprint != 0 &&
            std::find(a_method->more_constrained_than.begin(),
                      a_method->more_constrained_than.end(),
                      b_method->associated_constraint_fingerprint) !=
                a_method->more_constrained_than.end()) {
            return true;
        }
        if (a.is_template_specialization && b.is_template_specialization) {

            bool conversion_ordering = conversion_result_target.valid() &&
                                       a.ranks_conversion_result &&
                                       b.ranks_conversion_result;
            FunctionTemplateOrderingContext ordering_context =
                conversion_ordering
                    ? FunctionTemplateOrderingContext::conversion_call()
                    : FunctionTemplateOrderingContext::call(
                          a.ordering_argument_count,
                          b.ordering_argument_count,
                          a.has_reversed_parameters,
                          b.has_reversed_parameters);
            FunctionTemplateSpecializationOrder order =
                compare_function_template_specializations(
                    a.entity, b.entity, ordering_context);
            if (order != FunctionTemplateSpecializationOrder::Unordered) {
                return order ==
                    FunctionTemplateSpecializationOrder::LhsMoreSpecialized;
            }
        }
        bool a_rewritten = a.rewrite_kind != OperatorRewriteKind::None;
        bool b_rewritten = b.rewrite_kind != OperatorRewriteKind::None;
        if (a_rewritten != b_rewritten) {
            return !a_rewritten;
        }
        if (a_rewritten && b_rewritten &&
            a.has_reversed_parameters != b.has_reversed_parameters) {
            return !a.has_reversed_parameters;
        }
        return false;
    };
    size_t best = 0;
    for (size_t i = 1; i < viable.size(); ++i) {
        if (better(viable[i], viable[best])) {
            best = i;
        }
    }
    for (size_t i = 0; i < viable.size(); ++i) {
        if (i != best && !better(viable[best], viable[i])) {
            if (ambiguity_info) {
                describe_function_selection_ambiguity(
                    {viable[best].entity, viable[i].entity},
                    *ambiguity_info);
            }
            return OverloadSelection{{}, OperatorRewriteKind::None, false,
                                     true};
        }
    }
    return OverloadSelection{viable[best].entity,
                             viable[best].rewrite_kind,
                             viable[best].has_reversed_parameters,
                             false};
}

void Session::describe_function_selection_ambiguity(
    const std::vector<cir::EntityId>& candidates,
    OverloadAmbiguityInfo& info) {
    info = {};
    auto candidate_note_loc = [&](cir::EntityId candidate) {
        if (const cir::TemplateSpecializationFact* fact =
                file_.template_specialization(candidate);
            fact && fact->template_entity.valid() &&
            file_.valid(fact->template_entity)) {
            return file_.entity(fact->template_entity).loc;
        }
        return file_.entity(candidate).loc;
    };
    auto push_unique_loc = [&](SrcLoc loc) {
        if (loc.isInvalid() ||
            std::find_if(info.candidate_locs.begin(),
                         info.candidate_locs.end(),
                         [loc](SrcLoc existing) {
                             return existing.offset == loc.offset;
                         }) != info.candidate_locs.end()) {
            return;
        }
        info.candidate_locs.push_back(loc);
    };
    for (cir::EntityId candidate : candidates) {
        if (candidate.valid() && file_.valid(candidate)) {
            push_unique_loc(candidate_note_loc(candidate));
        }
    }
    for (size_t i = 0; i < candidates.size(); ++i) {
        if (!candidates[i].valid() || !file_.valid(candidates[i])) {
            continue;
        }
        for (size_t j = i + 1; j < candidates.size(); ++j) {
            if (candidates[j].valid() && file_.valid(candidates[j]) &&
                function_template_specializations_unordered_constraints_tie(
                    candidates[i],
                    candidates[j],
                    FunctionTemplateOrderingContext::declaration())) {
                info.has_unordered_associated_constraints = true;
                return;
            }
        }
    }
}

void Session::report_overload_ambiguity_notes(
    const OverloadAmbiguityInfo& info,
    SrcLoc loc) {
    for (SrcLoc candidate_loc : info.candidate_locs) {
        if (!candidate_loc.isInvalid()) {
            report_note("candidate function declared here", candidate_loc);
        }
    }
    if (info.has_unordered_associated_constraints) {
        report_note(
            "candidate associated constraints are not ordered by subsumption",
            loc);
    }
}

const ParamInput::DefaultArgument* Session::callable_default_argument(
    cir::EntityId entity,
    size_t parameter_index) const {
    auto from_entity = [&](cir::EntityId candidate)
        -> const ParamInput::DefaultArgument* {
        auto found = function_default_arguments_.find(
            static_cast<uint64_t>(candidate.index));
        if (found == function_default_arguments_.end() ||
            parameter_index >= found->second.size() ||
            found->second[parameter_index].loc.isInvalid()) {
            return nullptr;
        }
        return &found->second[parameter_index];
    };
    if (!entity.valid() || !file_.valid(entity)) {
        return nullptr;
    }
    if (const cir::RecordMethodFact* method = file_.method_fact(entity);
        method && method->inherited_constructor &&
        method->inherited_constructor->origin_constructor.valid()) {
        entity = method->inherited_constructor->origin_constructor;
    }
    if (const ParamInput::DefaultArgument* direct = from_entity(entity)) {
        return direct;
    }
    cir::EntityKind entity_kind = file_.entity(entity).kind;
    if (entity_kind == cir::EntityKind::Method ||
        entity_kind == cir::EntityKind::Constructor) {
        std::vector<TemplateArgument> member_arguments;
        const TemplateInfo* owner_info =
            member_instantiation_template(entity, &member_arguments);
        if (owner_info && owner_info->is_class_template) {
            cir::EntityId method_entity = structor_impl_entity(entity);
            cir::EntityId pattern_member =
                class_template_member_pattern_entity(method_entity,
                                                     *owner_info);
            if (!pattern_member.valid()) {
                cir::EntityId record_entity = file_.entity(entity).parent;
                const cir::RecordFacts* facts =
                    record_entity.valid() && file_.valid(record_entity)
                        ? file_.record_facts(record_entity)
                        : nullptr;
                if (facts) {
                    const cir::Entity& selected = file_.entity(entity);
                    for (const cir::RecordMethodFact& fact :
                         facts->methods) {
                        if (!fact.entity.valid() ||
                            !file_.valid(fact.entity)) {
                            continue;
                        }
                        const cir::Entity& candidate =
                            file_.entity(fact.entity);
                        bool same_named_method =
                            selected.name.valid() &&
                            candidate.name == selected.name;
                        bool same_structor_kind =
                            !selected.name.valid() &&
                            candidate.kind == selected.kind;
                        if ((same_named_method || same_structor_kind) &&
                            function_signatures_match(candidate.type,
                                                      selected.type)) {
                            cir::EntityId candidate_pattern =
                                class_template_member_pattern_entity(
                                    fact.entity, *owner_info);
                            if (candidate_pattern.valid()) {
                                pattern_member = candidate_pattern;
                                break;
                            }
                        }
                    }
                }
            }
            if (const ParamInput::DefaultArgument* argument =
                    from_entity(pattern_member)) {
                return argument;
            }
        }
    }
    if (const cir::TemplateSpecializationFact* fact =
            file_.template_specialization(entity)) {
        if (fact->template_entity.valid()) {
            if (const TemplateInfo* info = template_info(fact->template_entity)) {
                if (!info->is_class_template && !info->is_alias_template &&
                    !info->is_variable_template && !info->is_concept &&
                    info->pattern_function.valid() &&
                    file_.valid(info->pattern_function)) {
                    cir::EntityId pattern_entity =
                        file_.function(info->pattern_function).entity;
                    if (const ParamInput::DefaultArgument* argument =
                            from_entity(pattern_entity)) {
                        return argument;
                    }
                }
                if (const ParamInput::DefaultArgument* argument =
                        from_entity(info->entity)) {
                    return argument;
                }
            }
        }
    }
    const cir::Entity& record = file_.entity(entity);
    if (!record.name.valid() || !record.semantic_context.valid()) {
        return nullptr;
    }
    const cir::Binding* binding =
        file_.lookup_callable_binding(record.semantic_context,
                                      record.name,
                                      /*include_parents=*/false);
    if (!binding) {
        return nullptr;
    }
    for (cir::EntityId candidate : binding->entities) {
        if (!candidate.valid() || !file_.valid(candidate) ||
            candidate == entity ||
            !function_signatures_match(file_.entity(candidate).type,
                                       record.type)) {
            continue;
        }
        if (const ParamInput::DefaultArgument* argument =
                from_entity(candidate)) {
            return argument;
        }
    }
    return nullptr;
}

Session::DefaultArgumentReplayInfo Session::prepare_default_argument_replay(
    cir::EntityId entity,
    size_t parameter_index,
    SrcLoc use_loc) {
    DefaultArgumentReplayInfo result;
    auto from_entity = [&](cir::EntityId candidate)
        -> const ParamInput::DefaultArgument* {
        auto found = function_default_arguments_.find(
            static_cast<uint64_t>(candidate.index));
        if (found == function_default_arguments_.end() ||
            parameter_index >= found->second.size() ||
            found->second[parameter_index].loc.isInvalid()) {
            return nullptr;
        }
        return &found->second[parameter_index];
    };
    if (!entity.valid() || !file_.valid(entity)) {
        return result;
    }
    if (const cir::RecordMethodFact* method = file_.method_fact(entity);
        method && method->inherited_constructor &&
        method->inherited_constructor->origin_constructor.valid()) {
        entity = method->inherited_constructor->origin_constructor;
    }

    cir::EntityKind kind = file_.entity(entity).kind;
    bool is_member_like = kind == cir::EntityKind::Method ||
                          kind == cir::EntityKind::Constructor;
    auto prepare_class_template_member_default = [&]() {
        if (!is_member_like) {
            return false;
        }

        if (const cir::TemplateSpecializationFact* specialization =
                file_.template_specialization(entity);
            specialization && specialization->template_entity.valid()) {
            if (const TemplateInfo* callable =
                    template_info(specialization->template_entity);
                callable && !callable->is_class_template &&
                !callable->is_alias_template &&
                !callable->is_variable_template &&
                !callable->is_concept) {
                return false;
            }
        }
        std::vector<TemplateArgument> member_arguments;
        const cir::TemplateSpecializationFact* owner_fact = nullptr;
        const TemplateInfo* owner_info =
            member_instantiation_template(entity,
                                          &member_arguments,
                                          &owner_fact);
        if (!owner_info || !owner_info->is_class_template) {
            return false;
        }
        auto canonical_record_method = [&]() {
            cir::EntityId method = structor_impl_entity(entity);
            if (file_.method_fact(method)) {
                return method;
            }
            cir::EntityId record_entity = file_.entity(entity).parent;
            const cir::RecordFacts* facts =
                record_entity.valid() && file_.valid(record_entity)
                    ? file_.record_facts(record_entity)
                    : nullptr;
            if (!facts) {
                return method;
            }
            const cir::Entity& selected = file_.entity(entity);
            for (const cir::RecordMethodFact& fact : facts->methods) {
                if (!fact.entity.valid() || !file_.valid(fact.entity)) {
                    continue;
                }
                const cir::Entity& candidate = file_.entity(fact.entity);
                bool same_named_method =
                    selected.name.valid() && candidate.name == selected.name;
                bool same_structor_kind =
                    !selected.name.valid() &&
                    candidate.kind == selected.kind;
                if ((same_named_method || same_structor_kind) &&
                    function_signatures_match(candidate.type,
                                              selected.type)) {
                    return fact.entity;
                }
            }
            return method;
        };
        cir::EntityId method_entity = canonical_record_method();
        cir::EntityId pattern_member =
            class_template_member_pattern_entity(method_entity, *owner_info);
        if (pattern_member.valid()) {
            result.argument = from_entity(pattern_member);
        }
        if (!result.argument) {
            result.argument = from_entity(method_entity);
        }
        if (!result.argument && method_entity != entity) {
            result.argument = from_entity(entity);
        }
        if (!result.argument) {
            const cir::Entity& selected = file_.entity(method_entity);
            if (selected.name.valid() && selected.semantic_context.valid()) {
                const cir::Binding* binding =
                    file_.lookup_callable_binding(selected.semantic_context,
                                                  selected.name,
                                                  /*include_parents=*/false);
                if (binding) {
                    for (cir::EntityId candidate : binding->entities) {
                        if (!candidate.valid() || !file_.valid(candidate) ||
                            candidate == entity ||
                            !function_signatures_match(
                                file_.entity(candidate).type,
                                selected.type)) {
                            continue;
                        }
                        result.argument = from_entity(candidate);
                        if (result.argument) {
                            break;
                        }
                    }
                }
            }
        }
        if (!result.argument) {
            return false;
        }

        SrcLoc point = use_loc;
        uint64_t point_generation = current_point_lookup_generation();
        if (point_generation == 0) {
            point_generation = lookup_generation_;
        }
        if (const cir::RecordMethodFact* method_fact =
                file_.method_fact(method_entity)) {
            if (!method_fact->first_required_loc.isInvalid()) {
                point = method_fact->first_required_loc;
            }
            if (method_fact->first_required_lookup_generation != 0) {
                point_generation =
                    method_fact->first_required_lookup_generation;
            } else {
                if (point.isInvalid() && owner_fact &&
                    !owner_fact->point_of_instantiation.isInvalid()) {
                    point = owner_fact->point_of_instantiation;
                }
                if (point.isInvalid()) {
                    point = file_.entity(method_entity).loc;
                }
                mark_record_method_required_at(method_entity,
                                               point,
                                               point_generation);
            }
        }
        if (point.isInvalid() && owner_fact &&
            !owner_fact->point_of_instantiation.isInvalid()) {
            point = owner_fact->point_of_instantiation;
        }
        if (point.isInvalid()) {
            point = file_.entity(method_entity).loc;
        }
        cir::EntityId record_entity = file_.entity(method_entity).parent;
        if (record_entity.valid() && file_.valid(record_entity)) {
            result.declaration_context =
                file_.entity(record_entity).semantic_context;
        }
        result.template_info = owner_info;
        result.arguments = std::move(member_arguments);
        result.point_of_instantiation = point;
        result.point_lookup_generation = point_generation;
        return true;
    };
    if (prepare_class_template_member_default()) {
        return result;
    }

    const cir::TemplateSpecializationFact* selected_specialization =
        file_.template_specialization(entity);
    if (selected_specialization &&
        selected_specialization->template_entity.valid()) {
        const TemplateInfo* info =
            template_info(selected_specialization->template_entity);
        if (info && !info->is_class_template && !info->is_alias_template &&
            !info->is_variable_template && !info->is_concept) {
            result.template_info = info;
            result.arguments =
                selected_specialization->template_arguments();
            result.point_of_instantiation =
                selected_specialization->point_of_instantiation.isInvalid()
                    ? use_loc
                    : selected_specialization->point_of_instantiation;
            result.point_lookup_generation =
                selected_specialization->point_lookup_generation;
            if (info->pattern_function.valid() &&
                file_.valid(info->pattern_function)) {
                cir::EntityId pattern_entity =
                    file_.function(info->pattern_function).entity;
                result.argument = from_entity(pattern_entity);
            }
        }
    }

    if (!result.argument && selected_specialization &&
        selected_specialization->template_entity.valid()) {
        // Hidden friend templates register their defaults at the in-class
        // declaration; that capture carries the declaration point whose
        // access rights govern the replay ([dcl.fct.default]p5), unlike the
        // recapture made while the definition replays in the enclosing
        // namespace.
        result.argument =
            from_entity(selected_specialization->template_entity);
    }
    if (!result.argument) {
        result.argument = from_entity(entity);
    }
    if (!result.argument && selected_specialization &&
        selected_specialization->template_entity.valid()) {
        if (const TemplateInfo* info =
                template_info(selected_specialization->template_entity)) {
            if (!info->is_class_template && !info->is_alias_template &&
                !info->is_variable_template && !info->is_concept &&
                info->pattern_function.valid() &&
                file_.valid(info->pattern_function)) {
                cir::EntityId pattern_entity =
                    file_.function(info->pattern_function).entity;
                result.argument = from_entity(pattern_entity);
            }
        }
    }
    if (!result.argument) {
        const cir::Entity& record = file_.entity(entity);
        if (record.name.valid() && record.semantic_context.valid()) {
            const cir::Binding* binding =
                file_.lookup_callable_binding(record.semantic_context,
                                              record.name,
                                              /*include_parents=*/false);
            if (binding) {
                for (cir::EntityId candidate : binding->entities) {
                    if (!candidate.valid() || !file_.valid(candidate) ||
                        candidate == entity ||
                        !function_signatures_match(file_.entity(candidate).type,
                                                   record.type)) {
                        continue;
                    }
                    result.argument = from_entity(candidate);
                    if (result.argument) {
                        break;
                    }
                }
            }
        }
    }
    return result;
}

std::vector<Session::CompleteClassDefaultArgumentRef>
Session::prepare_complete_class_default_arguments(
    cir::EntityId record,
    uint64_t lookup_generation) {
    std::vector<CompleteClassDefaultArgumentRef> result;
    const cir::RecordFacts* facts = file_.record_facts(record);
    if (!facts) {
        return result;
    }
    cir::DeclContextId record_context =
        file_.valid(record) ? file_.entity(record).semantic_context
                            : cir::DeclContextId{};
    std::vector<cir::EntityId> functions;
    functions.reserve(facts->methods.size() + facts->function_friends.size());
    for (const cir::RecordMethodFact& method : facts->methods) {
        functions.push_back(method.entity);
    }
    for (const cir::RecordFunctionFriendGrant& grant :
         facts->function_friends) {
        if (grant.kind ==
                cir::RecordFunctionFriendGrantKind::ExactFunction &&
            grant.entity.valid()) {
            functions.push_back(grant.entity);
        }
    }
    std::sort(functions.begin(), functions.end(), [](auto lhs, auto rhs) {
        return lhs.index < rhs.index;
    });
    functions.erase(std::unique(functions.begin(), functions.end()),
                    functions.end());
    for (cir::EntityId function : functions) {

        const TemplateInfo* function_template = template_info(function);
        if (!function_template) {
            if (const TemplateInfo* owner =
                    member_instantiation_template(function, nullptr)) {
                cir::EntityId pattern =
                    class_template_member_pattern_entity(function, *owner);
                function_template = template_info(pattern);
            }
        }
        if (function_template && !function_template->is_class_template &&
            !function_template->is_alias_template &&
            !function_template->is_variable_template &&
            !function_template->is_concept) {
            continue;
        }
        auto found = function_default_arguments_.find(
            static_cast<uint64_t>(function.index));
        if (found == function_default_arguments_.end()) {
            continue;
        }
        std::vector<ParamInput::DefaultArgument> previous = found->second;
        bool changed = false;
        for (size_t index = 0; index < found->second.size(); ++index) {
            ParamInput::DefaultArgument& argument = found->second[index];
            if (!argument.requires_complete_class_replay ||
                argument.loc.isInvalid()) {
                continue;
            }
            argument.lookup_generation = lookup_generation;
            if (!argument.declaration_context.valid()) {
                argument.declaration_context = record_context;
            }
            result.push_back(
                CompleteClassDefaultArgumentRef{function,
                                                index,
                                                argument.loc});
            changed = true;
        }
        if (changed) {
            uint64_t key = static_cast<uint64_t>(function.index);
            track_speculative_rollback(
                [this, key, previous = std::move(previous)]() mutable {
                    function_default_arguments_[key] = std::move(previous);
                });
        }
    }
    return result;
}

bool Session::callable_can_use_default_arguments(
    cir::EntityId entity,
    size_t provided_arguments,
    size_t hidden_arguments) const {
    if (!entity.valid() || !file_.valid(entity)) {
        return false;
    }
    const cir::FunctionTypePayload* payload =
        function_payload_of(file_, file_.entity(entity).type);
    if (!payload || hidden_arguments > payload->parameters.size()) {
        return false;
    }
    size_t visible_parameters = payload->parameters.size() - hidden_arguments;
    size_t first_missing = provided_arguments;
    if (first_missing >= visible_parameters) {
        return false;
    }
    for (size_t i = first_missing; i < visible_parameters; ++i) {
        if (!callable_default_argument(entity, i)) {
            return false;
        }
    }
    return true;
}

void Session::add_adl_candidates(std::string_view name,
                                 const std::vector<ExprResult>& arguments,
                                 std::vector<cir::EntityId>& candidates) {
    cir::NameId requested_name = file_.intern_name(name);
    auto push_unique = [&](cir::EntityId entity) {
        if (entity.valid() && file_.valid(entity) &&
            std::find(candidates.begin(), candidates.end(), entity) ==
                candidates.end()) {
            candidates.push_back(entity);
        }
    };

    std::vector<cir::DeclContextId> associated_contexts;
    std::vector<cir::EntityId> associated_records;
    std::unordered_set<uint32_t> visited_types;
    std::unordered_set<uint64_t> visited_entities;
    std::unordered_set<uint32_t> visited_contexts;

    std::function<void(cir::TypeId)> associate_type;
    std::function<void(cir::EntityId)> associate_entity;

    auto associate_enclosing_class = [&](cir::EntityId entity) {
        if (!entity.valid() || !file_.valid(entity)) {
            return;
        }
        cir::DeclContextId context = file_.entity(entity).semantic_context;
        while (context.valid()) {
            const cir::DeclContext& declaration_context =
                file_.decl_context(context);
            if (declaration_context.kind == cir::DeclContextKind::Record) {
                if (declaration_context.owner != entity) {
                    cir::EntityId owner = declaration_context.owner;
                    if (owner.valid() && file_.valid(owner)) {
                        associate_type(file_.entity(owner).type);
                    }
                    return;
                }
                context = declaration_context.parent;
                continue;
            }
            if (declaration_context.kind ==
                    cir::DeclContextKind::Namespace ||
                declaration_context.kind ==
                    cir::DeclContextKind::TranslationUnit) {
                return;
            }
            context = declaration_context.parent;
        }
    };

    associate_entity = [&](cir::EntityId entity) {
        if (!entity.valid() || !file_.valid(entity) ||
            !visited_entities.insert(entity.index).second) {
            return;
        }

        const cir::Entity& associated = file_.entity(entity);
        cir::DeclContextId context = associated.semantic_context;
        while (context.valid()) {
            const cir::DeclContext& declaration_context =
                file_.decl_context(context);
            if (declaration_context.kind == cir::DeclContextKind::Namespace) {
                if (visited_contexts.insert(context.index).second) {
                    associated_contexts.push_back(context);
                }
                // Inline namespaces and their enclosing namespaces form one
                // associated namespace set. Lookup from the first non-inline
                // namespace also follows its implicit inline using-directives.
                if (!declaration_context.is_inline_namespace) {
                    break;
                }
            }
            if (declaration_context.kind ==
                cir::DeclContextKind::TranslationUnit) {
                if (visited_contexts.insert(context.index).second) {
                    associated_contexts.push_back(context);
                }
                break;
            }
            context = declaration_context.parent;
        }

        if (associated.kind == cir::EntityKind::Record) {
            associated_records.push_back(entity);
        }
        associate_enclosing_class(entity);
    };

    associate_type = [&](cir::TypeId type) {
        cir::TypeId resolved = file_.resolved_type(type);
        if (!file_.valid(resolved) ||
            !visited_types.insert(resolved.index).second) {
            return;
        }

        const cir::TypePayload& payload = file_.type_payload(resolved);
        switch (file_.type(resolved).kind) {
            case cir::TypeKind::Pointer: {
                const auto* pointer =
                    std::get_if<cir::PointerTypePayload>(&payload);
                if (pointer) associate_type(pointer->pointee.type);
                break;
            }
            case cir::TypeKind::BlockPointer: {
                const auto* pointer =
                    std::get_if<cir::BlockPointerTypePayload>(&payload);
                if (pointer) associate_type(pointer->pointee.type);
                break;
            }
            case cir::TypeKind::LValueReference:
            case cir::TypeKind::RValueReference: {
                const auto* reference =
                    std::get_if<cir::ReferenceTypePayload>(&payload);
                if (reference) associate_type(reference->referred_type.type);
                break;
            }
            case cir::TypeKind::Array: {
                const auto* array =
                    std::get_if<cir::ArrayTypePayload>(&payload);
                if (array) associate_type(array->element_type.type);
                break;
            }
            case cir::TypeKind::Function: {
                const auto* function =
                    std::get_if<cir::FunctionTypePayload>(&payload);
                if (!function) break;
                associate_type(function->return_type.type);
                for (cir::TypeRef parameter : function->parameters) {
                    associate_type(parameter.type);
                }
                break;
            }
            case cir::TypeKind::MemberPointer: {
                const auto* member =
                    std::get_if<cir::MemberPointerTypePayload>(&payload);
                if (!member) break;
                associate_type(member->class_type.type);
                associate_type(member->member_type.type);
                break;
            }
            case cir::TypeKind::Record: {
                cir::EntityId record = file_.record_entity(resolved);
                associate_entity(record);
                const cir::RecordFacts* facts = file_.record_facts(record);
                if (facts && !facts->is_incomplete) {
                    for (const cir::RecordBaseFact& base : facts->bases) {
                        associate_type(base.type.type);
                    }
                }
                const cir::TemplateSpecializationFact* specialization =
                    file_.template_specialization(record);
                if (!specialization) break;
                for (const cir::TemplateArgument& argument :
                     specialization->template_arguments()) {
                    if (argument.kind ==
                        cir::TemplateArgumentKind::Type) {
                        associate_type(argument.type.type);
                        continue;
                    }
                    if (argument.kind !=
                            cir::TemplateArgumentKind::Template ||
                        !argument.template_entity.valid() ||
                        !file_.valid(argument.template_entity)) {
                        continue;
                    }
                    const TemplateInfo* info =
                        template_info(argument.template_entity);
                    if (info &&
                        (info->is_class_template ||
                         info->is_alias_template)) {
                        associate_entity(argument.template_entity);
                    }
                }
                break;
            }
            case cir::TypeKind::Enum: {
                const auto* enumeration =
                    std::get_if<cir::EnumTypePayload>(&payload);
                if (enumeration) associate_entity(enumeration->entity);
                break;
            }
            case cir::TypeKind::TemplateSpecialization: {
                const auto* specialization =
                    std::get_if<cir::TemplateSpecializationTypePayload>(&payload);
                if (!specialization) break;
                if (specialization->primary_template.valid()) {
                    associate_entity(specialization->primary_template);
                }
                for (const cir::TemplateArgument& argument :
                     specialization->arguments) {
                    if (argument.kind == cir::TemplateArgumentKind::Type) {
                        associate_type(argument.type.type);
                    } else if (argument.kind ==
                                   cir::TemplateArgumentKind::Template &&
                               argument.template_entity.valid()) {
                        const TemplateInfo* info =
                            template_info(argument.template_entity);
                        if (info && (info->is_class_template ||
                                     info->is_alias_template)) {
                            associate_entity(argument.template_entity);
                        }
                    }
                }
                break;
            }
            default:
                break;
        }
    };

    for (const ExprResult& argument : arguments) {
        associate_type(argument.type);
        if (argument.category == ValueCategory::FunctionDesignator) {
            if (argument.entity.valid() && file_.valid(argument.entity)) {
                associate_type(file_.entity(argument.entity).type);
            }
            for (cir::EntityId candidate : argument.candidates) {
                if (candidate.valid() && file_.valid(candidate)) {
                    associate_type(file_.entity(candidate).type);
                }
            }
        }
    }

    for (cir::DeclContextId context : associated_contexts) {
        const cir::Binding* binding = file_.lookup_callable_binding(
            context, name, /*include_parents=*/false);
        if (!binding) {
            continue;
        }
        for (cir::EntityId entity : binding->entities) {
            push_unique(entity);
        }
    }

    for (cir::EntityId record : associated_records) {
        const cir::RecordFacts* facts = file_.record_facts(record);
        if (!facts) {
            continue;
        }
        for (const cir::RecordFunctionFriendGrant& grant :
             facts->function_friends) {
            if (grant.kind ==
                    cir::RecordFunctionFriendGrantKind::ExactFunction) {
                if (grant.name == requested_name && grant.entity.valid() &&
                    file_.valid(grant.entity)) {
                    push_unique(grant.entity);
                }
                continue;
            }
            if (grant.kind != cir::RecordFunctionFriendGrantKind::
                                  PrimaryFunctionTemplate) {
                continue;
            }
            cir::EntityId template_entity = grant.entity;
            if (!template_entity.valid() ||
                !file_.valid(template_entity)) {
                continue;
            }
            const cir::Entity& entity = file_.entity(template_entity);
            const TemplateInfo* info = template_info(template_entity);
            if (!info ||
                info->is_class_template ||
                info->is_alias_template ||
                info->is_variable_template ||
                info->is_concept ||
                entity.kind != cir::EntityKind::Function ||
                entity.name != requested_name) {
                continue;
            }
            push_unique(template_entity);
        }
    }
}

cir::EntityId Session::resolve_call_overload(ExprResult& callee,
                                             const std::vector<ExprResult>& arguments,
                                             SrcLoc loc) {
    if (callee.category != ValueCategory::FunctionDesignator ||
        !callee.entity.valid()) {
        return callee.entity;
    }
    std::vector<cir::EntityId> candidates = callee.candidates;
    if (candidates.empty()) {
        candidates.push_back(callee.entity);
    }
    bool member_bound = callee.place.valid();
    if (member_bound) {
        cir::TypeId bound_object_type =
            file_.resolved_type(object_type_from_place(callee.place));
        cir::TypeId retained_object_type =
            file_.resolved_type(callee.member_access_object_type);

        if (bound_object_type.valid() &&
            (!retained_object_type.valid() ||
             (bound_object_type != retained_object_type &&
              analyze_derived_to_base_path(bound_object_type,
                                           retained_object_type).kind !=
                  DerivedToBasePathKind::NotFound))) {
            callee.member_access_object_type = bound_object_type;
        }
    }
    if (!member_bound && !callee.qualified_name &&
        !callee.suppress_argument_dependent_lookup && !callee.name.empty()) {
        add_adl_candidates(callee.name, arguments, candidates);
    }
    if (candidates.size() == 1 && !member_bound) {
        cir::EntityId selected = candidates.front();
        const MemberCandidateObjectPaths* selected_lookup =
            member_candidate_paths_for_selected(
                callee.member_candidate_object_paths, selected);
        if (selected_lookup) {
            (void)check_selected_member_candidate_access(
                *selected_lookup, selected, loc,
                callee.member_access_object_type);
        } else if (const cir::RecordMethodFact* fact =
                       file_.method_fact(selected)) {
            MemberLookupDeclaration declaration;
            declaration.entity = selected;
            declaration.access_owner =
                file_.entity(selected).parent;
            declaration.declared_access = fact->declared_access;
            declaration.has_declared_access = true;
            (void)check_member_lookup_access(
                declaration, loc, callee.member_access_object_type);

            if (member_bound && !fact->is_static && callee.place.valid()) {
                const cir::Inst& place_inst = file_.inst(callee.place);
                uint8_t object_cv =
                    file_.place_object_ref(place_inst.result_type).qualifiers;
                if (place_inst.place_fact.valid()) {
                    object_cv |= file_.place_fact(place_inst.place_fact)
                                     .object_type.qualifiers;
                }
                const auto* payload = std::get_if<cir::FunctionTypePayload>(
                    &file_.type_payload(file_.resolved_type(
                        file_.entity(selected).type)));
                if ((object_cv & cir::QualConst) != 0 && payload &&
                    !payload->member_is_const) {
                    report_error("cannot call the non-const member function '" +
                                     callee.name +
                                     "' on a const-qualified object",
                                 loc);
                }
            }
        }
        return selected;
    }
    bool ambiguous = false;

    bool member_leading = false;
    std::vector<ExprResult> ranked_arguments;
    if (member_bound) {
        for (cir::EntityId candidate : candidates) {
            if (!candidate.valid() || !file_.valid(candidate)) {
                continue;
            }
            cir::EntityKind kind = file_.entity(candidate).kind;
            if (kind == cir::EntityKind::Method ||
                kind == cir::EntityKind::Constructor ||
                kind == cir::EntityKind::Destructor) {
                member_leading = true;
                break;
            }
        }
    }
    // [over.match.funcs]p4: a non-conversion function introduced by a
    // using-declaration is treated as a member of the *derived* class when
    // forming the implicit object parameter.  Without this the base member
    // ranks a spurious derived-to-base object conversion and ties with a
    // derived overload that converts one of its explicit arguments instead.
    auto implicit_object_class_for =
        [&](cir::EntityId candidate) -> cir::TypeId {
        for (const MemberCandidateObjectPaths& lookup :
             callee.member_candidate_object_paths) {
            if (lookup.entity == candidate &&
                lookup.implicit_object_class.valid() &&
                lookup.paths.size() <= 1) {
                return file_.resolved_type(lookup.implicit_object_class);
            }
        }
        return {};
    };
    if (member_leading) {
        ExprResult object;
        object.place = callee.place;
        object.type = object_type_from_place(callee.place);

        if (!callee.member_candidate_object_paths.empty()) {
            cir::TypeId common_owner{};
            bool same_owner = true;
            for (cir::EntityId candidate : candidates) {
                cir::TypeId effective_owner =
                    implicit_object_class_for(candidate);
                cir::EntityId owner = file_.valid(candidate)
                    ? file_.entity(candidate).parent
                    : cir::EntityId{};
                cir::TypeId owner_type = effective_owner.valid()
                    ? effective_owner
                    : (owner.valid() && file_.valid(owner)
                           ? file_.resolved_type(file_.entity(owner).type)
                           : cir::TypeId{});
                if (!owner_type.valid()) {
                    continue;
                }
                if (!common_owner.valid()) {
                    common_owner = owner_type;
                } else if (common_owner != owner_type) {
                    same_owner = false;
                    break;
                }
            }
            if (same_owner && common_owner.valid()) {
                object.type = common_owner;
            }
        }
        object.category = callee.bound_member_object_category ==
                                  ValueCategory::Invalid
            ? ValueCategory::LValue
            : callee.bound_member_object_category;
        ranked_arguments.reserve(arguments.size() + 1);
        ranked_arguments.push_back(std::move(object));
        for (const ExprResult& argument : arguments) {

            ranked_arguments.push_back(argument);
        }
    }
    OverloadAmbiguityInfo ambiguity_info;
    std::vector<OverloadCandidate> ranked_candidates;
    ranked_candidates.reserve(candidates.size());
    for (cir::EntityId candidate : candidates) {
        OverloadCandidate input{candidate,
                                member_leading,
                                /*ranks_conversion_result=*/true};
        if (member_leading) {
            input.canonical_member_object_type =
                implicit_object_class_for(candidate);
        }
        ranked_candidates.push_back(input);
    }
    cir::EntityId selected = select_overload(
        ranked_candidates,
        member_leading ? ranked_arguments : arguments,
        &ambiguous,
        {},
        &ambiguity_info);
    if (!selected.valid()) {
        bool rejected_const_object = false;
        if (!ambiguous && member_bound && callee.place.valid()) {
            const cir::Inst& place_inst = file_.inst(callee.place);
            uint8_t object_cv =
                file_.place_object_ref(place_inst.result_type).qualifiers;
            if (place_inst.place_fact.valid()) {
                object_cv |= file_.place_fact(place_inst.place_fact)
                                 .object_type.qualifiers;
            }
            if ((object_cv & cir::QualConst) != 0) {
                for (cir::EntityId candidate : candidates) {
                    const cir::RecordMethodFact* fact =
                        file_.method_fact(candidate);
                    if (!fact || fact->is_static) {
                        continue;
                    }
                    const auto* payload =
                        std::get_if<cir::FunctionTypePayload>(
                            &file_.type_payload(file_.resolved_type(
                                fact->type.type)));
                    if (payload && !payload->member_is_const) {
                        rejected_const_object = true;
                        break;
                    }
                }
            }
        }
        if (rejected_const_object) {
            report_error("cannot call the non-const member function '" +
                             callee.name +
                             "' on a const-qualified object",
                         loc);
        } else {
            report_error((ambiguous ? "call to '"
                                    : "no matching function for call to '") +
                             callee.name +
                             (ambiguous ? "' is ambiguous" : "'"),
                         loc);
        }
        if (ambiguous) {
            report_overload_ambiguity_notes(ambiguity_info, loc);
        }
    } else {

        const MemberCandidateObjectPaths* selected_lookup =
            member_candidate_paths_for_selected(
                callee.member_candidate_object_paths, selected);
        if (selected_lookup) {
            (void)check_selected_member_candidate_access(
                *selected_lookup, selected, loc,
                callee.member_access_object_type);
        } else if (const cir::RecordMethodFact* fact =
                       file_.method_fact(selected)) {
            MemberLookupDeclaration declaration;
            declaration.entity = selected;
            declaration.access_owner = file_.entity(selected).parent;
            declaration.declared_access = fact->declared_access;
            declaration.has_declared_access = true;
            (void)check_member_lookup_access(
                declaration, loc, callee.member_access_object_type);
        }
    }
    return selected;
}

void Session::collect_constructor_candidates(
    cir::TypeId record_type,
    const std::vector<ExprResult>& arguments,
    ConstructorInitializationKind init_kind,
    SrcLoc loc,
    std::vector<cir::EntityId>& candidates) {
    cir::TypeId resolved_record = file_.resolved_type(record_type);
    cir::EntityId record = file_.record_entity(resolved_record);
    if (record.valid()) {
        InstantiationDemandResult declaration_demand =
            require_complete_class_type_result(
                resolved_record,
                loc,
                cir::InstantiationDemandKind::DeclarationSet);
        if (declaration_demand != InstantiationDemandResult::Satisfied) {

            return;
        }
    }
    const cir::RecordFacts* facts =
        file_.record_facts_for_type(resolved_record);
    if (!facts) {
        return;
    }
    auto push_unique = [&](cir::EntityId entity) {
        if (!entity.valid() || !file_.valid(entity)) {
            return;
        }
        if (std::find(candidates.begin(), candidates.end(), entity) ==
            candidates.end()) {
            candidates.push_back(entity);
        }
    };
    auto excluded_inherited_single_argument = [&](cir::EntityId entity) {
        if (arguments.size() != 1) {
            return false;
        }
        const cir::RecordMethodFact* method = file_.method_fact(entity);
        if (!method || !method->inherited_constructor) {
            return false;
        }
        const cir::FunctionTypePayload* payload =
            function_payload_of(file_, method->type.type);
        if (!payload || payload->parameters.empty()) {
            return false;
        }
        cir::TypeId first =
            file_.resolved_type(payload->parameters.front().type);
        if (!file_.valid(first) ||
            (file_.type(first).kind != cir::TypeKind::LValueReference &&
             file_.type(first).kind != cir::TypeKind::RValueReference)) {
            return false;
        }
        cir::TypeId parameter_record = file_.resolved_type(
            file_.reference_referred_type(first));
        cir::TypeId origin_record = file_.entity(
            method->inherited_constructor->origin_record).type;
        cir::TypeId derived_record = file_.resolved_type(record_type);
        auto reference_related = [&](cir::TypeId base,
                                     cir::TypeId derived) {
            base = file_.resolved_type(base);
            derived = file_.resolved_type(derived);
            return base == derived ||
                derived_to_base_path(derived, base, nullptr);
        };
        return reference_related(origin_record, parameter_record) &&
            reference_related(parameter_record, derived_record);
    };
    auto forms_self_value_constructor_signature =
        [&](const TemplateInfo& info,
            const std::vector<TemplateArgument>& arguments,
            cir::EntityId pattern_entity) {
            const cir::FunctionTypePayload* payload =
                function_payload_of(file_, info.pattern_type);
            if (!payload || payload->parameters.empty()) {
                return false;
            }

            PatternInstantiationCallbacks callbacks;
            TemplateArgumentBindings argument_bindings;
            if (!bind_template_arguments_to_parameters(info.parameters,
                                                       arguments,
                                                       argument_bindings)) {
                return false;
            }
            cir::TypeId first_parameter =
                substitute_pattern_type(payload->parameters.front().type,
                                        argument_bindings,
                                        callbacks);
            cir::TypeId self_type = file_.resolved_type(record_type);
            if (!first_parameter.valid() || !file_.valid(self_type) ||
                file_.resolved_type(first_parameter) != self_type) {
                return false;
            }

            for (size_t i = 1; i < payload->parameters.size(); ++i) {
                if (!callable_default_argument(pattern_entity, i)) {
                    return false;
                }
            }
            return true;
    };
    for (const cir::RecordMethodFact& method : facts->methods) {

        if (const cir::TemplateSpecializationFact* specialization =
                file_.template_specialization(method.entity);
            specialization && specialization->template_entity.valid() &&
            template_info(specialization->template_entity)) {
            continue;
        }
        const bool ignored_deleted_move =
            method.is_deleted && method.is_defaulted &&
            method.special_member_kind ==
                cir::SpecialMemberKind::MoveConstructor;
        if (method.entity.valid() &&
            file_.entity(method.entity).kind == cir::EntityKind::Constructor &&
            !ignored_deleted_move) {
            if (const TemplateInfo* info = template_info(method.entity)) {
                if (init_kind == ConstructorInitializationKind::Copy &&
                    info->explicit_specifier !=
                        cir::ExplicitSpecifierKind::Dependent &&
                    method.is_explicit) {
                    continue;
                }
                if (!tstate().function_template_instantiation_callback_) {
                    continue;
                }
                std::vector<TemplateArgument> deduced;
                TemplateArgumentBindings deduced_bindings;
                if (!deduce_template_arguments(*info,
                                               arguments,
                                               deduced,
                                               nullptr,
                                               nullptr,
                                               &deduced_bindings)) {
                    continue;
                }

                if (forms_self_value_constructor_signature(*info,
                                                           deduced,
                                                           method.entity)) {
                    continue;
                }
                cir::EntityId specialization =
                    tstate().function_template_instantiation_callback_(
                        *info, deduced_bindings, loc);
                const cir::RecordMethodFact* specialization_method =
                    specialization.valid()
                        ? file_.method_fact(specialization)
                        : nullptr;
                if (init_kind == ConstructorInitializationKind::Copy &&
                    specialization_method &&
                    specialization_method->is_explicit) {
                    continue;
                }
                if (!excluded_inherited_single_argument(specialization)) {
                    push_unique(specialization);
                }
                continue;
            }
            if (init_kind == ConstructorInitializationKind::Copy &&
                method.is_explicit) {
                continue;
            }
            if (!excluded_inherited_single_argument(method.entity)) {
                push_unique(method.entity);
            }
        }
    }
}

cir::EntityId Session::select_constructor(cir::TypeId record_type,
                                          const std::vector<ExprResult>& arguments,
                                          bool* ambiguous_out,
                                          SrcLoc loc,
                                          ConstructorInitializationKind init_kind,
                                          bool demand_selected) {
    auto select_from = [&](const std::vector<cir::EntityId>& entities,
                           const std::vector<ExprResult>& phase_arguments,
                           bool* phase_ambiguous) {
        std::vector<OverloadCandidate> candidates;
        candidates.reserve(entities.size());
        for (cir::EntityId entity : entities) {
            candidates.push_back(OverloadCandidate{
                entity,
                /*member_object_leading=*/false,
                /*ranks_conversion_result=*/false});
        }

        return select_overload(
            candidates,
            phase_arguments,
            phase_ambiguous,
            /*conversion_result_target=*/{},
            /*ambiguity_info=*/nullptr,
            init_kind == ConstructorInitializationKind::Direct,
            init_kind == ConstructorInitializationKind::Direct &&
                    phase_arguments.size() == 1
                ? record_type
                : cir::TypeId{});
    };

    cir::EntityId selected;
    const bool has_braced_list = arguments.size() == 1 &&
        arguments.front().init_list &&
        arguments.front().init_list->syntax == InitListSyntax::Braced;
    if (has_braced_list) {
        const InitListValue& list = *arguments.front().init_list;
        bool has_default_constructor = false;
        if (list.elements.empty()) {
            if (const cir::RecordFacts* facts = file_.record_facts_for_type(
                    file_.resolved_type(record_type))) {
                has_default_constructor = std::any_of(
                    facts->methods.begin(), facts->methods.end(),
                    [](const cir::RecordMethodFact& method) {
                        return method.special_member_kind ==
                            cir::SpecialMemberKind::DefaultConstructor;
                    });
            }
        }

        // The [over.match.list] overload invariant tests initializer-list
        // constructors before considering individual initializer clauses.
        if (!has_default_constructor) {
            std::vector<cir::EntityId> phase_one;
            collect_constructor_candidates(record_type, arguments, init_kind,
                                           loc, phase_one);
            std::erase_if(phase_one, [&](cir::EntityId entity) {
                return !constructor_initializer_list_element_type(entity)
                            .has_value();
            });
            bool phase_ambiguous = false;
            selected = select_from(phase_one, arguments, &phase_ambiguous);
            if (phase_ambiguous) {
                if (ambiguous_out) {
                    *ambiguous_out = true;
                }
                return {};
            }
        }

        if (!selected.valid()) {
            std::vector<ExprResult> element_arguments;
            element_arguments.reserve(list.elements.size());
            for (const InitElementInput& element : list.elements) {
                if (!element.designators.empty()) {
                    if (ambiguous_out) {
                        *ambiguous_out = false;
                    }
                    return {};
                }
                element_arguments.push_back(element.value);
            }
            std::vector<cir::EntityId> phase_two;
            collect_constructor_candidates(record_type, element_arguments,
                                           init_kind, loc, phase_two);
            selected = select_from(phase_two, element_arguments,
                                   ambiguous_out);
        } else if (ambiguous_out) {
            *ambiguous_out = false;
        }
    } else {
        std::vector<cir::EntityId> entities;
        collect_constructor_candidates(record_type, arguments, init_kind,
                                       loc, entities);
        selected = select_from(entities, arguments, ambiguous_out);
    }
    if (demand_selected && selected.valid() &&
        file_.template_specialization(selected)) {
        (void)request_function_instantiation(
            selected, cir::InstantiationDemandKind::OdrUse, loc);
    }
    return selected;
}

Session::ImplicitMoveEligibility Session::classify_implicit_move_operand(
    const ExprResult& source,
    ImplicitMoveContext context) const {
    ImplicitMoveEligibility result;
    result.entity = source.entity;
    if (!source.possibly_parenthesized_identifier ||
        !source.entity.valid() || !file_.valid(source.entity) ||
        (source.category != ValueCategory::LValue &&
         source.category != ValueCategory::XValue)) {
        return result;
    }

    const cir::Entity& entity = file_.entity(source.entity);
    if ((entity.kind != cir::EntityKind::Variable &&
         entity.kind != cir::EntityKind::Parameter) ||
        (entity.storage_duration != cir::StorageDuration::Automatic &&
         entity.storage_duration != cir::StorageDuration::Parameter) ||
        (entity.qualifiers & cir::QualVolatile) != 0 ||
        (entity.owning_function.valid() && current_function_.valid() &&
         entity.owning_function != file_.function(current_function_).entity)) {
        return result;
    }

    cir::TypeId entity_type = file_.resolved_type(entity.type);
    bool is_reference_entity = false;
    if (file_.valid(entity_type) &&
        (file_.type(entity_type).kind == cir::TypeKind::LValueReference ||
         file_.type(entity_type).kind == cir::TypeKind::RValueReference)) {
        is_reference_entity = true;
        if (file_.type(entity_type).kind != cir::TypeKind::RValueReference) {
            return result;
        }
        cir::TypeRef referred = file_.reference_referred_ref(entity_type);
        if ((referred.qualifiers & cir::QualVolatile) != 0) {
            return result;
        }
    }

    if (entity.kind != cir::EntityKind::Parameter &&
        entity.lexical_context.valid()) {
        cir::DeclContextId cursor = current_decl_context();
        bool found = false;
        while (cursor.valid()) {
            if (cursor == entity.lexical_context) {
                found = true;
                break;
            }
            const cir::DeclContext& scope = file_.decl_context(cursor);
            if (scope.kind != cir::DeclContextKind::Block) {
                break;
            }
            cursor = scope.parent;
        }
        if (!found) {
            return result;
        }
    }

    if (context == ImplicitMoveContext::Throw) {
        auto context_contains = [&](cir::DeclContextId outer,
                                    cir::DeclContextId inner) {
            for (cir::DeclContextId cursor = inner; cursor.valid();) {
                if (cursor == outer) {
                    return true;
                }
                cursor = file_.decl_context(cursor).parent;
            }
            return false;
        };
        for (cir::DeclContextId try_outer : active_try_move_boundaries_) {
            bool source_contains_try =
                entity.kind == cir::EntityKind::Parameter ||
                (entity.lexical_context.valid() &&
                 context_contains(entity.lexical_context, try_outer));
            if (source_contains_try) {
                result.blocked_by_try_scope = true;
                return result;
            }
        }
    }

    result.eligible = true;
    result.nrvo_eligible =
        context == ImplicitMoveContext::Return &&
        entity.kind == cir::EntityKind::Variable &&
        entity.storage_duration == cir::StorageDuration::Automatic &&
        !is_reference_entity &&
        !entity.is_exception_declaration;
    return result;
}

Session::ObjectTransferSelection
Session::select_object_transfer_constructor(cir::TypeId target_type,
                                            const ExprResult& source,
                                            ImplicitMoveContext context,
                                            SrcLoc loc) {
    ObjectTransferSelection result;
    result.move = classify_implicit_move_operand(source, context);

    auto select_for = [&](ValueCategory category, bool* ambiguous) {
        ExprResult argument = source;
        argument.category = category;
        std::vector<ExprResult> arguments;
        arguments.push_back(std::move(argument));
        return select_constructor(target_type, arguments, ambiguous, loc,
                                  ConstructorInitializationKind::Copy,
                                  /*demand_selected=*/false);
    };
    auto first_parameter_is_matching_rvalue_reference =
        [&](cir::EntityId constructor) {
            const cir::RecordMethodFact* fact = file_.method_fact(constructor);
            if (!fact) {
                return false;
            }
            const auto* payload = std::get_if<cir::FunctionTypePayload>(
                &file_.type_payload(file_.resolved_type(fact->type.type)));
            if (!payload || payload->parameters.empty()) {
                return false;
            }
            cir::TypeId parameter =
                file_.resolved_type(payload->parameters.front().type);
            if (!file_.valid(parameter) ||
                file_.type(parameter).kind !=
                    cir::TypeKind::RValueReference) {
                return false;
            }
            cir::TypeId referred = file_.resolved_type(
                file_.reference_referred_ref(parameter).type);
            return referred == file_.resolved_type(source.type);
        };

    if (!result.move.eligible) {
        result.selected_category = source.category;
        result.constructor = select_for(source.category, &result.ambiguous);
    } else if (lang_opts_.is_cxx26_or_later()) {
        result.selected_category = ValueCategory::XValue;
        result.constructor =
            select_for(ValueCategory::XValue, &result.ambiguous);
    } else {
        bool first_ambiguous = false;
        cir::EntityId first =
            select_for(ValueCategory::XValue, &first_ambiguous);
        if (first.valid() &&
            first_parameter_is_matching_rvalue_reference(first)) {
            result.constructor = first;
            result.selected_category = ValueCategory::XValue;
            result.ambiguous = false;
        } else {
            result.used_fallback = true;
            result.selected_category = source.category;
            result.constructor =
                select_for(source.category, &result.ambiguous);
        }
    }

    if (result.constructor.valid() &&
        file_.template_specialization(result.constructor)) {
        (void)request_function_instantiation(
            result.constructor, cir::InstantiationDemandKind::OdrUse, loc);
    }
    result.has_error = !result.constructor.valid() || result.ambiguous;
    return result;
}

void Session::collect_conversion_function_candidates(
    const ExprResult& source,
    cir::TypeId target_type,
    bool allow_explicit,
    SrcLoc loc,
    std::vector<cir::EntityId>& candidates) {
    cir::TypeId source_type = file_.resolved_type(source.type);
    if (!file_.valid(source_type) ||
        file_.type(source_type).kind != cir::TypeKind::Record) {
        return;
    }
    auto push_unique = [&](cir::EntityId entity) {
        if (!entity.valid() || !file_.valid(entity)) {
            return;
        }
        const cir::RecordMethodFact* method = file_.method_fact(entity);
        if (method && method->is_explicit) {
            if (!allow_explicit) {
                return;
            }
            cir::TypeRef target = file_.type_ref(target_type);
            cir::TypeId target_resolved = file_.resolved_type(target_type);
            if (file_.valid(target_resolved) &&
                (file_.type(target_resolved).kind ==
                     cir::TypeKind::LValueReference ||
                 file_.type(target_resolved).kind ==
                     cir::TypeKind::RValueReference)) {
                target = file_.reference_referred_ref(target_resolved);
            }
            ConversionResultValue result = conversion_result_value(
                file_, conversion_function_return_type(file_, *method));
            cir::TypeRef source_result{result.type, result.qualifiers,
                                       target.memory_space};
            bool same = file_.resolved_type(source_result.type) ==
                    file_.resolved_type(target.type) &&
                (source_result.qualifiers &
                 static_cast<uint8_t>(~target.qualifiers)) == 0;
            QualificationConversionAnalysis qualification =
                analyze_qualification_conversion(source_result, target);
            if (!same && !(qualification.has_indirection &&
                           qualification.similar && qualification.allowed)) {

                return;
            }
        }
        if (std::find(candidates.begin(), candidates.end(), entity) ==
            candidates.end()) {
            candidates.push_back(entity);
        }
    };

    if (const cir::RecordFacts* source_facts =
            file_.record_facts_for_type(source_type)) {
        if (source_facts->is_lambda_closure) {
            cir::EntityId source_entity = file_.record_entity(source_type);
            for (const cir::RecordMethodFact& method :
                 source_facts->methods) {
                if (!method.entity.valid() || !file_.valid(method.entity) ||
                    method.is_static ||
                    file_.entity(method.entity).parent != source_entity ||
                    !is_conversion_function_name(file_, method) ||
                    template_info(method.entity)) {
                    continue;
                }
                push_unique(method.entity);
            }
        }
    }

    std::vector<cir::NameId> conversion_names;
    std::vector<cir::TypeId> pending{source_type};
    std::unordered_set<uint64_t> visited;
    while (!pending.empty()) {
        cir::TypeId current = file_.resolved_type(pending.back());
        pending.pop_back();
        if (!current.valid() ||
            !visited.insert(static_cast<uint64_t>(current.index)).second) {
            continue;
        }
        const cir::RecordFacts* facts = file_.record_facts_for_type(current);
        if (!facts) {
            continue;
        }
        for (const cir::RecordMethodFact& method : facts->methods) {
            if (!method.entity.valid() || !file_.valid(method.entity) ||
                !is_conversion_function_name(file_, method)) {
                continue;
            }

            cir::NameId method_name = method.name;
            if (method_name.valid() &&
                std::find(conversion_names.begin(), conversion_names.end(),
                          method_name) == conversion_names.end()) {
                conversion_names.push_back(method_name);
            }
        }
        for (const cir::RecordBaseFact& base : facts->bases) {
            pending.push_back(base.type.type);
        }
    }

    for (cir::NameId conversion_name : conversion_names) {
        MemberLookupResult lookup =
            lookup_member_name(source_type, file_.name(conversion_name));
        if (lookup.ambiguous || !lookup.found_name) {
            continue;
        }
        for (const MemberLookupDeclaration& declaration :
             lookup.declarations) {
            const cir::RecordMethodFact* method =
                file_.method_fact(declaration.entity);
            if (!method || method->is_static ||
                (method->is_explicit && !allow_explicit) ||
                !is_conversion_function_name(file_, *method)) {
                continue;
            }
            if (const TemplateInfo* info = template_info(method->entity)) {
                if (!tstate().function_template_instantiation_callback_) {
                    continue;
                }
                std::vector<TemplateArgument> deduced;
                TemplateArgumentBindings deduced_bindings;
                if (!deduce_conversion_template_arguments(*info,
                                                           target_type,
                                                           deduced,
                                                           &deduced_bindings)) {
                    continue;
                }
                cir::EntityId specialization =
                    tstate().function_template_instantiation_callback_(
                        *info, deduced_bindings, loc);
                push_unique(specialization);
                continue;
            }
            push_unique(method->entity);
        }
    }
}

void Session::retain_selected_conversion_template_emission(
    cir::EntityId selected,
    const std::vector<cir::EntityId>& candidates) {
    if (!selected.valid() || !file_.valid(selected)) {
        return;
    }
    const cir::TemplateSpecializationFact* selected_fact =
        file_.template_specialization(selected);
    if (!selected_fact) {
        return;
    }
    cir::Entity& selected_entity = file_.entity_mut(selected);
    if (selected_entity.suppressed_as_unselected_template_candidate) {
        selected_entity.suppressed_as_unselected_template_candidate = false;
        track_speculative_rollback([this, selected] {
            if (selected.valid() && file_.valid(selected)) {
                file_.entity_mut(selected)
                    .suppressed_as_unselected_template_candidate = true;
            }
        });
    }

    cir::TypeId selected_type = file_.resolved_type(selected_entity.type);
    for (cir::EntityId candidate : candidates) {
        if (candidate == selected || !candidate.valid() ||
            !file_.valid(candidate)) {
            continue;
        }
        const cir::TemplateSpecializationFact* candidate_fact =
            file_.template_specialization(candidate);
        cir::Entity& candidate_entity = file_.entity_mut(candidate);
        if (!candidate_fact ||
            candidate_fact->template_entity ==
                selected_fact->template_entity ||
            candidate_entity.parent != selected_entity.parent ||
            file_.resolved_type(candidate_entity.type) != selected_type ||
            candidate_entity.is_explicit_template_specialization) {
            continue;
        }
        const TemplateInfo* candidate_info =
            template_info(candidate_fact->template_entity);
        if (!candidate_info ||
            explicit_instantiation_definition_declared(
                *candidate_info,
                candidate_fact->template_arguments()) ||
            candidate_entity.suppressed_as_unselected_template_candidate) {
            continue;
        }
        candidate_entity.suppressed_as_unselected_template_candidate = true;
        track_speculative_rollback([this, candidate] {
            if (candidate.valid() && file_.valid(candidate)) {
                file_.entity_mut(candidate)
                    .suppressed_as_unselected_template_candidate = false;
            }
        });
    }
}

cir::EntityId Session::select_conversion_function(const ExprResult& source,
                                                  cir::TypeId target_type,
                                                  bool* ambiguous_out,
                                                  SrcLoc loc,
                                                  UserConversionContext context) {
    if (ambiguous_out) {
        *ambiguous_out = false;
    }
    if (!target_type.valid() || !source.type.valid() ||
        (!source.place.valid() && !source.unevaluated_semantic_operand) ||
        (source.category != ValueCategory::LValue &&
         source.category != ValueCategory::XValue)) {
        return {};
    }

    cir::TypeId source_type = file_.resolved_type(source.type);
    cir::TypeId target_resolved = file_.resolved_type(target_type);
    if (!file_.valid(source_type) || !file_.valid(target_resolved) ||
        file_.type(source_type).kind != cir::TypeKind::Record ||
        file_.type(target_resolved).kind == cir::TypeKind::Record ||
        builtin_kind_of(file_, target_resolved) == cir::BuiltinTypeKind::Void) {
        return {};
    }

    std::vector<cir::EntityId> candidates;
    bool allow_explicit =
        context == UserConversionContext::DirectInitialization ||
        context == UserConversionContext::DirectReferenceBinding ||
        context == UserConversionContext::ContextualBool;
    collect_conversion_function_candidates(source,
                                           target_type,
                                           allow_explicit,
                                           loc,
                                           candidates);
    if (candidates.empty()) {
        return {};
    }

    ExprResult object;
    object.place = source.place;
    object.type = source.type;
    object.category = source.category;
    object.semantic_object_qualifiers = source.semantic_object_qualifiers;
    object.unevaluated_semantic_operand =
        source.unevaluated_semantic_operand;
    std::vector<ExprResult> arguments;
    arguments.push_back(std::move(object));
    std::vector<OverloadCandidate> inputs;
    inputs.reserve(candidates.size());
    for (cir::EntityId candidate : candidates) {
        inputs.push_back(OverloadCandidate{candidate,
                                           /*member_object_leading=*/true,
                                           /*ranks_conversion_result=*/true});
    }

    cir::EntityId selected = select_overload(
        inputs,
        arguments,
        ambiguous_out,
        target_type,
        /*ambiguity_info=*/nullptr,
        /*allow_user_defined_argument_conversions=*/false);
    retain_selected_conversion_template_emission(selected, candidates);
    return selected;
}

Session::UserConversionSequence Session::resolve_initialization_user_conversion(
    const ExprResult& source,
    cir::TypeId target_type,
    UserConversionContext context,
    SrcLoc loc) {
    UserConversionSequence result;
    result.context = context;
    if (!lang_opts_.is_cxx_mode() || !target_type.valid() ||
        !source.type.valid()) {
        return result;
    }
    cir::TypeId source_resolved = file_.resolved_type(source.type);
    cir::TypeId target_resolved = file_.resolved_type(target_type);
    if (!file_.valid(source_resolved) || !file_.valid(target_resolved) ||
        is_void_type(target_resolved)) {
        return result;
    }
    bool source_is_record =
        file_.type(source_resolved).kind == cir::TypeKind::Record;
    bool target_is_record =
        file_.type(target_resolved).kind == cir::TypeKind::Record;
    if (!source_is_record && !target_is_record) {
        return result;
    }
    if (target_is_record) {
        cir::EntityId target_record = file_.record_entity(target_resolved);
        if (target_record.valid() &&
            file_.template_specialization(target_record) &&
            request_class_instantiation(
                target_record,
                cir::InstantiationDemandKind::DeclarationSet,
                loc) != InstantiationDemandResult::Satisfied) {

            return result;
        }
    }
    if (source_is_record && target_is_record &&
        file_.resolved_type(source_resolved) ==
            file_.resolved_type(target_resolved)) {

        return result;
    }

    ExprResult source_view;
    source_view.place = source.place;
    source_view.type = source.type;
    source_view.category = source.category;
    source_view.semantic_object_qualifiers =
        source.semantic_object_qualifiers;
    source_view.unevaluated_semantic_operand =
        source.unevaluated_semantic_operand;
    std::vector<ExprResult> arguments;
    arguments.push_back(std::move(source_view));

    std::vector<OverloadCandidate> candidates;
    bool copy_initialization =
        context == UserConversionContext::CopyInitialization ||
        context == UserConversionContext::DirectConstructorReference ||
        context == UserConversionContext::ContextualImplicit;
    if (target_is_record && record_has_user_constructor(target_resolved)) {
        std::vector<cir::EntityId> constructors;
        collect_constructor_candidates(
            target_resolved,
            arguments,
            copy_initialization ? ConstructorInitializationKind::Copy
                                : ConstructorInitializationKind::Direct,
            loc,
            constructors);
        for (cir::EntityId constructor : constructors) {
            candidates.push_back(OverloadCandidate{
                constructor,
                /*member_object_leading=*/false,
                /*ranks_conversion_result=*/false});
        }
    }

    bool source_object_usable =
        (source.place.valid() || source.unevaluated_semantic_operand) &&
        (source.category == ValueCategory::LValue ||
         source.category == ValueCategory::XValue);
    bool target_is_base_of_source = source_is_record && target_is_record &&
        analyze_derived_to_base_path(source_resolved, target_resolved).kind !=
            DerivedToBasePathKind::NotFound;
    bool conversion_functions_apply =
        source_is_record && source_object_usable &&
        (!target_is_record || copy_initialization) &&
        !target_is_base_of_source;
    std::vector<cir::EntityId> conversions;
    if (conversion_functions_apply) {
        bool allow_explicit =
            context == UserConversionContext::DirectInitialization ||
            context == UserConversionContext::DirectConstructorReference ||
            context == UserConversionContext::DirectReferenceBinding ||
            context == UserConversionContext::ContextualBool;
        collect_conversion_function_candidates(
            arguments.front(),
            target_type,
            allow_explicit,
            loc,
            conversions);
        for (cir::EntityId conversion : conversions) {
            candidates.push_back(OverloadCandidate{
                conversion,
                /*member_object_leading=*/true,
                /*ranks_conversion_result=*/true});
        }
    }
    if (candidates.empty()) {
        return result;
    }

    bool ambiguous = false;
    cir::EntityId selected = select_overload(
        candidates,
        arguments,
        &ambiguous,
        target_type,
        &result.ambiguity,
        /*allow_user_defined_argument_conversions=*/false);
    if (ambiguous) {
        result.kind = UserConversionSequence::Kind::Ambiguous;
        return result;
    }
    if (!selected.valid()) {
        return result;
    }
    retain_selected_conversion_template_emission(selected, conversions);
    result.callable = selected;
    result.kind =
        file_.entity(selected).kind == cir::EntityKind::Constructor
            ? UserConversionSequence::Kind::Constructor
            : UserConversionSequence::Kind::ConversionFunction;
    if (result.kind == UserConversionSequence::Kind::Constructor &&
        file_.template_specialization(selected)) {
        (void)request_function_instantiation(
            selected, cir::InstantiationDemandKind::OdrUse, loc);
    }
    if (const cir::RecordMethodFact* method = file_.method_fact(selected)) {
        result.explicit_candidate = method->is_explicit;
        if (method->is_deleted) {
            result.usability = UserConversionSequence::Usability::Deleted;
        } else if (!member_access_allowed(file_.entity(selected).parent,
                                          method->declared_access)) {
            result.usability =
                UserConversionSequence::Usability::Inaccessible;
        } else {
            result.usability = UserConversionSequence::Usability::Usable;
        }
    }

    const cir::FunctionTypePayload* selected_payload = function_payload_of(
        file_, file_.entity(selected).type);
    if (result.kind == UserConversionSequence::Kind::Constructor &&
        selected_payload && selected_payload->parameters.size() >= 2) {
        ConversionDetail initial;
        ConversionRank initial_rank = conversion_rank(
            source.type, source.category, selected_payload->parameters[1],
            source.semantic_object_qualifiers.value_or(0), &initial,
            /*allow_user_defined=*/false);
        result.initial_standard = initial.standard;
        result.initial_standard.rank = initial_rank;
        result.trailing_standard.source = file_.type_ref(target_resolved);
        result.trailing_standard.target = file_.type_ref(target_resolved);
        result.trailing_standard.source_category = ValueCategory::PrValue;
        result.trailing_standard.rank = ConversionRank::Exact;
    } else if (result.kind ==
                   UserConversionSequence::Kind::ConversionFunction &&
               selected_payload) {
        result.initial_standard.source = file_.type_ref(source_resolved);
        result.initial_standard.target = file_.type_ref(source_resolved);
        result.initial_standard.source_category = source.category;
        result.initial_standard.rank = ConversionRank::Exact;
        ConversionResultValue conversion_result =
            conversion_result_value(file_, selected_payload->return_type);
        ConversionDetail trailing;
        ConversionRank trailing_rank = conversion_rank(
            conversion_result.type, conversion_result.category,
            file_.type_ref(target_type), conversion_result.qualifiers,
            &trailing, /*allow_user_defined=*/false);
        result.trailing_standard = trailing.standard;
        result.trailing_standard.rank = trailing_rank;
    }
    return result;
}

Session::UserConversionSequence Session::resolve_permitted_implicit_conversion(
    const ExprResult& source,
    PermittedImplicitTarget permitted_target,
    cir::TypeId* target_type,
    SrcLoc loc) {
    UserConversionSequence result;
    result.context = UserConversionContext::ContextualImplicit;
    if (target_type) {
        *target_type = {};
    }
    cir::TypeId source_type = file_.resolved_type(source.type);
    if (!file_.valid(source_type) ||
        file_.type(source_type).kind != cir::TypeKind::Record) {
        return result;
    }

    auto permitted = [&](cir::TypeId candidate) {
        candidate = file_.resolved_type(candidate);
        if (!file_.valid(candidate)) {
            return false;
        }
        switch (permitted_target) {
            case PermittedImplicitTarget::IntegralOrEnum:
                return is_integer_type(candidate) ||
                    file_.type(candidate).kind == cir::TypeKind::Enum;
            case PermittedImplicitTarget::PointerToObject: {
                if (file_.type(candidate).kind != cir::TypeKind::Pointer) {
                    return false;
                }
                cir::TypeId pointee = file_.resolved_type(
                    file_.pointer_pointee_type(candidate));
                return file_.valid(pointee) && !is_void_type(pointee) &&
                    file_.type(pointee).kind != cir::TypeKind::Function;
            }
            case PermittedImplicitTarget::UnaryPlus:

                return is_arithmetic_type(candidate) ||
                    is_pointer_type(candidate);
        }
        return false;
    };

    std::vector<cir::NameId> conversion_names;
    std::unordered_set<uint64_t> names_with_permitted_results;
    std::vector<cir::TypeId> pending{source_type};
    std::unordered_set<uint64_t> visited;
    while (!pending.empty()) {
        cir::TypeId current = file_.resolved_type(pending.back());
        pending.pop_back();
        if (!current.valid() ||
            !visited.insert(static_cast<uint64_t>(current.index)).second) {
            continue;
        }
        const cir::RecordFacts* facts = file_.record_facts_for_type(current);
        if (!facts) {
            continue;
        }
        for (const cir::RecordMethodFact& method : facts->methods) {
            if (!method.entity.valid() || !file_.valid(method.entity) ||
                method.is_static || method.is_explicit ||
                !is_conversion_function_name(file_, method)) {
                continue;
            }
            if (method.name.valid() &&
                std::find(conversion_names.begin(), conversion_names.end(),
                          method.name) == conversion_names.end()) {
                conversion_names.push_back(method.name);
            }
            if (!template_info(method.entity)) {
                ConversionResultValue converted = conversion_result_value(
                    file_, conversion_function_return_type(file_, method));
                if (method.name.valid() && permitted(converted.type)) {
                    names_with_permitted_results.insert(
                        static_cast<uint64_t>(method.name.index));
                }
            }
        }
        for (const cir::RecordBaseFact& base : facts->bases) {
            pending.push_back(base.type.type);
        }
    }

    std::vector<cir::TypeId> targets;
    bool ambiguous_lookup = false;
    for (cir::NameId conversion_name : conversion_names) {
        MemberLookupResult lookup =
            lookup_member_name(source_type, file_.name(conversion_name));
        if (lookup.ambiguous) {
            ambiguous_lookup = ambiguous_lookup ||
                names_with_permitted_results.contains(
                    static_cast<uint64_t>(conversion_name.index));
            continue;
        }
        if (!lookup.found_name) {
            continue;
        }
        for (const MemberLookupDeclaration& declaration :
             lookup.declarations) {
            const cir::RecordMethodFact* method =
                file_.method_fact(declaration.entity);
            if (!method || method->is_static || method->is_explicit ||
                !is_conversion_function_name(file_, *method) ||
                template_info(method->entity)) {
                continue;
            }
            ConversionResultValue converted = conversion_result_value(
                file_, conversion_function_return_type(file_, *method));
            cir::TypeId candidate = file_.resolved_type(converted.type);
            if (permitted(candidate) &&
                std::find(targets.begin(), targets.end(), candidate) ==
                    targets.end()) {
                targets.push_back(candidate);
            }
        }
    }

    if (ambiguous_lookup || targets.size() > 1) {
        result.kind = UserConversionSequence::Kind::Ambiguous;
        return result;
    }
    if (targets.empty()) {
        return result;
    }
    if (target_type) {
        *target_type = targets.front();
    }
    return resolve_initialization_user_conversion(
        source, targets.front(), UserConversionContext::ContextualImplicit,
        loc);
}

void Session::expand_operator_function_template_candidates(
    std::vector<cir::EntityId>& candidates,
    const std::vector<ExprResult>& ranking,
    SrcLoc loc) {
    if (!tstate().function_template_instantiation_callback_) {
        return;
    }
    std::vector<cir::EntityId> expanded;
    expanded.reserve(candidates.size());
    for (cir::EntityId candidate : candidates) {
        const TemplateInfo* info = template_info(candidate);
        if (!info) {
            expanded.push_back(candidate);
            continue;
        }
        if (info->is_class_template || info->is_alias_template ||
            info->is_variable_template || info->is_concept) {
            continue;
        }
        const cir::RecordMethodFact* method = file_.method_fact(candidate);
        const std::vector<ExprResult>* deduction_arguments = &ranking;
        std::vector<ExprResult> member_arguments;
        if (method && !method->is_static && !ranking.empty()) {

            member_arguments.assign(ranking.begin() + 1, ranking.end());
            deduction_arguments = &member_arguments;
        }
        std::vector<TemplateArgument> deduced;
        TemplateArgumentBindings deduced_bindings;
        if (!deduce_template_arguments(*info,
                                       *deduction_arguments,
                                       deduced,
                                       /*explicit_arguments=*/nullptr,
                                       /*callbacks=*/nullptr,
                                       &deduced_bindings,
                                       loc)) {
            continue;
        }
        cir::EntityId specialization =
            tstate().function_template_instantiation_callback_(
                *info, deduced_bindings, loc);
        if (specialization.valid()) {
            expanded.push_back(specialization);
        }
    }
    candidates = std::move(expanded);
}

void Session::expand_operator_function_template_candidates(
    std::vector<OverloadCandidate>& candidates,
    const std::vector<ExprResult>& ranking,
    SrcLoc loc) {
    if (!tstate().function_template_instantiation_callback_) {
        return;
    }
    std::vector<OverloadCandidate> expanded;
    expanded.reserve(candidates.size());
    for (const OverloadCandidate& candidate : candidates) {
        const TemplateInfo* info = template_info(candidate.entity);
        if (!info) {
            expanded.push_back(candidate);
            continue;
        }
        if (info->is_class_template || info->is_alias_template ||
            info->is_variable_template || info->is_concept) {
            continue;
        }
        std::vector<ExprResult> oriented = ranking;
        if (candidate.has_reversed_parameters && oriented.size() == 2) {
            std::swap(oriented[0], oriented[1]);
        }
        const cir::RecordMethodFact* method =
            file_.method_fact(candidate.entity);
        const std::vector<ExprResult>* deduction_arguments = &oriented;
        std::vector<ExprResult> member_arguments;
        if (method && !method->is_static && !oriented.empty()) {
            member_arguments.assign(oriented.begin() + 1, oriented.end());
            deduction_arguments = &member_arguments;
        }
        std::vector<TemplateArgument> deduced;
        TemplateArgumentBindings deduced_bindings;
        if (!deduce_template_arguments(*info,
                                       *deduction_arguments,
                                       deduced,
                                       /*explicit_arguments=*/nullptr,
                                       /*callbacks=*/nullptr,
                                       &deduced_bindings,
                                       loc)) {
            continue;
        }
        cir::EntityId specialization =
            tstate().function_template_instantiation_callback_(
                *info, deduced_bindings, loc);
        if (specialization.valid()) {
            OverloadCandidate retained = candidate;
            retained.entity = specialization;
            expanded.push_back(retained);
        }
    }
    candidates = std::move(expanded);
}

ExprResult Session::try_overloaded_binary(syntax::BinaryOperator op,
                                          ExprResult& lhs,
                                          ExprResult& rhs,
                                          bool* handled,
                                          SrcLoc loc,
                                          bool allow_comparison_rewrites) {
    *handled = false;
    const char* spelling = nullptr;
    switch (op) {
        case syntax::BinaryOperator::Assign: spelling = "="; break;
        case syntax::BinaryOperator::Add: spelling = "+"; break;
        case syntax::BinaryOperator::Sub: spelling = "-"; break;
        case syntax::BinaryOperator::Mul: spelling = "*"; break;
        case syntax::BinaryOperator::Div: spelling = "/"; break;
        case syntax::BinaryOperator::Mod: spelling = "%"; break;
        case syntax::BinaryOperator::Less: spelling = "<"; break;
        case syntax::BinaryOperator::LessEqual: spelling = "<="; break;
        case syntax::BinaryOperator::Greater: spelling = ">"; break;
        case syntax::BinaryOperator::GreaterEqual: spelling = ">="; break;
        case syntax::BinaryOperator::Equal: spelling = "=="; break;
        case syntax::BinaryOperator::NotEqual: spelling = "!="; break;
        case syntax::BinaryOperator::ThreeWay: spelling = "<=>"; break;
        case syntax::BinaryOperator::BitAnd: spelling = "&"; break;
        case syntax::BinaryOperator::BitOr: spelling = "|"; break;
        case syntax::BinaryOperator::BitXor: spelling = "^"; break;
        case syntax::BinaryOperator::Shl: spelling = "<<"; break;
        case syntax::BinaryOperator::Shr: spelling = ">>"; break;
        case syntax::BinaryOperator::AssignAdd: spelling = "+="; break;
        case syntax::BinaryOperator::AssignSub: spelling = "-="; break;
        case syntax::BinaryOperator::AssignMul: spelling = "*="; break;
        case syntax::BinaryOperator::AssignDiv: spelling = "/="; break;
        case syntax::BinaryOperator::AssignMod: spelling = "%="; break;
        case syntax::BinaryOperator::AssignShl: spelling = "<<="; break;
        case syntax::BinaryOperator::AssignShr: spelling = ">>="; break;
        case syntax::BinaryOperator::AssignAnd: spelling = "&="; break;
        case syntax::BinaryOperator::AssignXor: spelling = "^="; break;
        case syntax::BinaryOperator::AssignOr: spelling = "|="; break;
        default:
            return {};
    }
    bool lhs_record = is_record_kind(file_, lhs.type);
    bool rhs_record = is_record_kind(file_, rhs.type);
    auto is_enum = [&](cir::TypeId type) {
        cir::TypeId resolved = file_.resolved_type(type);
        return file_.valid(resolved) &&
            file_.type(resolved).kind == cir::TypeKind::Enum;
    };
    bool lhs_enum = is_enum(lhs.type);
    bool rhs_enum = is_enum(rhs.type);

    bool comparison = op == syntax::BinaryOperator::Less ||
        op == syntax::BinaryOperator::LessEqual ||
        op == syntax::BinaryOperator::Greater ||
        op == syntax::BinaryOperator::GreaterEqual ||
        op == syntax::BinaryOperator::Equal ||
        op == syntax::BinaryOperator::NotEqual ||
        op == syntax::BinaryOperator::ThreeWay;
    if (comparison && (lhs_record || rhs_record)) {
        std::vector<ExprResult> ranking{lhs, rhs};
        std::vector<OverloadCandidate> comparison_candidates;
        auto add_path = [&](std::string_view operator_name,
                            OperatorRewriteKind rewrite_kind,
                            bool reversed) {
            const ExprResult& first = reversed ? rhs : lhs;
            const ExprResult& second = reversed ? lhs : rhs;
            std::vector<cir::EntityId> path;
            if (is_record_kind(file_, first.type)) {
                MemberLookupResult lookup =
                    lookup_member_name(first.type, operator_name);
                if (lookup.ambiguous) {
                    report_error("member '" + std::string(operator_name) +
                                     "' is ambiguous through base classes",
                                 loc);
                    return;
                }
                for (const MemberLookupDeclaration& declaration :
                     lookup.declarations) {
                    if (declaration.entity.valid() &&
                        file_.valid(declaration.entity) &&
                        file_.entity(declaration.entity).kind ==
                            cir::EntityKind::Method) {
                        path.push_back(declaration.entity);
                    }
                }
            }
            if (const cir::Binding* free_binding =
                    file_.lookup_callable_binding(
                        current_decl_context(), operator_name,
                        /*include_parents=*/true)) {
                for (cir::EntityId entity : free_binding->entities) {
                    if (std::find(path.begin(), path.end(), entity) ==
                        path.end()) {
                        path.push_back(entity);
                    }
                }
            }
            std::vector<ExprResult> oriented{first, second};
            add_adl_candidates(operator_name, oriented, path);
            for (cir::EntityId entity : path) {

                if (entity == current_function_entity()) {
                    const cir::RecordMethodFact* active =
                        file_.method_fact(entity);
                    if ((active && active->is_defaulted) ||
                        file_.defaulted_comparison_fact(entity)) {
                        continue;
                    }
                }
                OverloadCandidate candidate;
                candidate.entity = entity;
                candidate.member_object_leading = true;
                candidate.is_rewritten_candidate =
                    rewrite_kind != OperatorRewriteKind::None;
                candidate.has_reversed_parameters = reversed;
                candidate.rewrite_kind = rewrite_kind;
                comparison_candidates.push_back(candidate);
            }
        };

        const std::string direct_name = std::string("operator") + spelling;
        add_path(direct_name, OperatorRewriteKind::None,
                 /*reversed=*/false);
        if (allow_comparison_rewrites &&
            lang_opts_.is_cxx20_or_later()) {
            if (op == syntax::BinaryOperator::Less ||
                op == syntax::BinaryOperator::LessEqual ||
                op == syntax::BinaryOperator::Greater ||
                op == syntax::BinaryOperator::GreaterEqual) {
                add_path("operator<=>", OperatorRewriteKind::ThreeWay,
                         /*reversed=*/false);
                add_path("operator<=>", OperatorRewriteKind::ThreeWay,
                         /*reversed=*/true);
            } else if (op == syntax::BinaryOperator::ThreeWay) {
                add_path("operator<=>", OperatorRewriteKind::ThreeWay,
                         /*reversed=*/true);
            } else if (op == syntax::BinaryOperator::Equal) {
                add_path("operator==", OperatorRewriteKind::Equality,
                         /*reversed=*/true);
            } else if (op == syntax::BinaryOperator::NotEqual) {
                add_path("operator==", OperatorRewriteKind::Equality,
                         /*reversed=*/false);
                add_path("operator==", OperatorRewriteKind::Equality,
                         /*reversed=*/true);
            }
        }

        if (op == syntax::BinaryOperator::NotEqual) {
            auto declaration_type = [&](cir::EntityId entity) {
                if (const cir::RecordMethodFact* method =
                        file_.method_fact(entity)) {
                    return method->type.type;
                }
                return file_.entity(entity).type;
            };
            auto corresponding = [&](cir::EntityId equality,
                                     cir::EntityId not_equal) {
                const cir::Entity& lhs_entity = file_.entity(equality);
                const cir::Entity& rhs_entity = file_.entity(not_equal);
                if (lhs_entity.kind != rhs_entity.kind) {
                    return false;
                }
                if (lhs_entity.kind == cir::EntityKind::Method &&
                    lhs_entity.parent != rhs_entity.parent) {
                    return false;
                }
                if (lhs_entity.kind == cir::EntityKind::Function &&
                    lhs_entity.semantic_context !=
                        rhs_entity.semantic_context) {
                    return false;
                }
                return function_signatures_match(
                    declaration_type(equality),
                    declaration_type(not_equal));
            };
            std::vector<cir::EntityId> direct_not_equal;
            for (const OverloadCandidate& candidate :
                 comparison_candidates) {
                if (candidate.rewrite_kind == OperatorRewriteKind::None) {
                    direct_not_equal.push_back(candidate.entity);
                }
            }
            std::erase_if(
                comparison_candidates,
                [&](const OverloadCandidate& candidate) {
                    if (candidate.rewrite_kind !=
                        OperatorRewriteKind::Equality) {
                        return false;
                    }
                    return std::any_of(
                        direct_not_equal.begin(), direct_not_equal.end(),
                        [&](cir::EntityId direct) {
                            return corresponding(candidate.entity, direct);
                        });
                });
        }

        expand_operator_function_template_candidates(
            comparison_candidates, ranking, loc);
        OverloadAmbiguityInfo ambiguity_info;
        OverloadSelection selection = select_overload_detailed(
            comparison_candidates, ranking, {}, &ambiguity_info);
        if (selection.ambiguous) {
            report_error("use of overloaded operator '" +
                             std::string(spelling) + "' is ambiguous",
                         loc);
            report_overload_ambiguity_notes(ambiguity_info, loc);
            *handled = true;
            ExprResult error;
            error.has_error = true;
            error.type = builder_.unknown_type();
            error.category = ValueCategory::PrValue;
            return error;
        }
        if (selection.entity.valid()) {
            *handled = true;
            bool reversed = selection.has_reversed_parameters;
            ExprResult first = reversed ? std::move(rhs) : std::move(lhs);
            ExprResult second = reversed ? std::move(lhs) : std::move(rhs);
            const cir::Entity& entity = file_.entity(selection.entity);
            std::string selected_name = entity.name.valid()
                ? std::string(file_.name(entity.name))
                : direct_name;
            ExprResult call;
            if (entity.kind == cir::EntityKind::Method) {

                std::string selected_lookup_name = selected_name;
                if (const cir::TemplateSpecializationFact* specialization =
                        file_.template_specialization(selection.entity);
                    specialization &&
                    specialization->template_entity.valid() &&
                    file_.valid(specialization->template_entity)) {
                    const cir::Entity& primary =
                        file_.entity(specialization->template_entity);
                    if (primary.name.valid()) {
                        selected_lookup_name =
                            std::string(file_.name(primary.name));
                    }
                }
                MemberLookupResult selected_lookup =
                    lookup_member_name(first.type, selected_lookup_name);
                MemberAccessBase access = collect_member_access_base(
                    std::move(first), /*is_arrow=*/false, loc);
                ExprResult callee = collect_bound_member_function_access_expr(
                    std::move(access), {selection.entity},
                    selected_lookup_name, loc, &selected_lookup);
                callee.qualified_name = true;
                call = collect_call_expr(std::move(callee),
                                         {std::move(second)}, loc);
            } else {
                ExprResult callee;
                callee.entity = selection.entity;
                callee.type = entity.type;
                callee.name = selected_name;
                callee.qualified_name = true;
                callee.category = ValueCategory::FunctionDesignator;
                std::vector<ExprResult> arguments;
                arguments.push_back(std::move(first));
                arguments.push_back(std::move(second));
                call = collect_call_expr(std::move(callee),
                                         std::move(arguments), loc);
            }
            if (selection.rewrite_kind == OperatorRewriteKind::None) {
                return call;
            }
            if (selection.rewrite_kind == OperatorRewriteKind::Equality) {
                if (file_.resolved_type(call.type) !=
                    file_.resolved_type(builder_.bool_type())) {
                    report_error("rewritten equality candidate must return bool",
                                 loc);
                    call.has_error = true;
                    return call;
                }
                if (op == syntax::BinaryOperator::NotEqual) {
                    return collect_unary_expr(
                        syntax::UnaryOperator::LogicalNot,
                        std::move(call), loc);
                }
                return call;
            }
            ExprResult zero = make_integer_literal(0, "0", loc);
            if (reversed) {
                return collect_binary_expr_impl(
                    op, std::move(zero), std::move(call), loc,
                    /*allow_comparison_rewrites=*/false);
            }
            return collect_binary_expr_impl(
                op, std::move(call), std::move(zero), loc,
                /*allow_comparison_rewrites=*/false);
        }
        return {};
    }

    if (!lhs_record && !rhs_record && !lhs_enum && !rhs_enum) {
        return {};
    }

    std::string name = std::string("operator") + spelling;
    std::vector<cir::EntityId> member_candidates;
    MemberLookupResult member_lookup;
    if (lhs_record) {
        member_lookup =
            lookup_member_name(file_.resolved_type(lhs.type), name);
        if (member_lookup.ambiguous) {
            report_error("member '" + name +
                             "' is ambiguous through base classes",
                         loc);
            *handled = true;
            ExprResult result;
            result.has_error = true;
            result.type = builder_.unknown_type();
            result.category = ValueCategory::PrValue;
            return result;
        }
        for (const MemberLookupDeclaration& declaration :
             member_lookup.declarations) {
            if (!declaration.entity.valid() ||
                !file_.valid(declaration.entity) ||
                file_.entity(declaration.entity).kind !=
                    cir::EntityKind::Method) {
                continue;
            }
            const cir::RecordMethodFact* method =
                file_.method_fact(declaration.entity);
            if (method && method->is_deleted && method->is_defaulted &&
                method->special_member_kind ==
                    cir::SpecialMemberKind::MoveAssignment) {
                continue;
            }
            member_candidates.push_back(declaration.entity);
        }
    }
    std::vector<cir::EntityId> candidates = member_candidates;
    if (const cir::Binding* free_binding = file_.lookup_callable_binding(
            current_decl_context(), name, /*include_parents=*/true)) {
        for (cir::EntityId entity : free_binding->entities) {
            if (std::find(candidates.begin(), candidates.end(), entity) ==
                candidates.end()) {
                candidates.push_back(entity);
            }
        }
    }
    {
        std::vector<ExprResult> operand_view;
        operand_view.push_back(ExprResult{});
        operand_view.back().place = lhs.place;
        operand_view.back().type = lhs.type;
        operand_view.back().category = lhs.category;
        operand_view.push_back(ExprResult{});
        operand_view.back().place = rhs.place;
        operand_view.back().type = rhs.type;
        operand_view.back().category = rhs.category;
        add_adl_candidates(name, operand_view, candidates);
    }
    if (candidates.empty()) {
        return {};
    }

    std::vector<ExprResult> ranking{lhs, rhs};

    expand_operator_function_template_candidates(candidates, ranking, loc);
    if (candidates.empty()) {
        return {};
    }
    bool ambiguous = false;
    OverloadAmbiguityInfo ambiguity_info;
    std::vector<OverloadCandidate> selection_candidates;
    selection_candidates.reserve(candidates.size());
    for (cir::EntityId candidate : candidates) {
        OverloadCandidate input{candidate,
                                /*member_object_leading=*/true,
                                /*ranks_conversion_result=*/true};
        if (file_.method_fact(candidate)) {
            cir::EntityId lookup_candidate = candidate;
            if (const cir::TemplateSpecializationFact* specialization =
                    file_.template_specialization(candidate);
                specialization &&
                specialization->template_entity.valid()) {
                lookup_candidate = specialization->template_entity;
            }
            for (const MemberLookupDeclaration& declaration :
                 member_lookup.declarations) {
                if (declaration.entity != candidate &&
                    declaration.entity != lookup_candidate) {
                    continue;
                }
                if (declaration.implicit_object_class.valid() &&
                    declaration.object_paths.size() <= 1) {
                    input.canonical_member_object_type =
                        declaration.implicit_object_class;
                } else {
                    input.canonical_member_object_type =
                        declaration.declaring_class;
                }
                break;
            }
        }
        selection_candidates.push_back(input);
    }
    cir::EntityId selected = select_overload(
        selection_candidates,
        ranking,
        &ambiguous,
        {},
        &ambiguity_info);
    if (!selected.valid()) {
        if (ambiguous) {
            report_error("use of overloaded operator '" + std::string(spelling) +
                             "' is ambiguous",
                         loc);
            report_overload_ambiguity_notes(ambiguity_info, loc);
            *handled = true;
            ExprResult result;
            result.has_error = true;
            result.type = builder_.unknown_type();
            result.category = ValueCategory::PrValue;
            return result;
        }

        if (op == syntax::BinaryOperator::Assign && lhs_record) {
            report_error("no matching function for call to 'operator='", loc);
            *handled = true;
            ExprResult result;
            result.has_error = true;
            result.type = builder_.unknown_type();
            result.category = ValueCategory::PrValue;
            return result;
        }
        return {};
    }

    *handled = true;
    const cir::Entity& entity = file_.entity(selected);
    bool is_member = entity.kind == cir::EntityKind::Method;
    if (is_member) {
        MemberAccessBase access = collect_member_access_base(
            std::move(lhs), /*is_arrow=*/false, loc);
        ExprResult callee = collect_bound_member_function_access_expr(
            std::move(access), {selected}, name, loc, &member_lookup);
        callee.qualified_name = true;
        std::vector<ExprResult> call_arguments;
        call_arguments.push_back(std::move(rhs));
        return collect_call_expr(std::move(callee), std::move(call_arguments), loc);
    }
    ExprResult callee;
    callee.entity = selected;
    callee.type = entity.type;
    callee.name = name;
    callee.qualified_name = true;
    callee.category = ValueCategory::FunctionDesignator;
    std::vector<ExprResult> call_arguments;
    call_arguments.push_back(std::move(lhs));
    call_arguments.push_back(std::move(rhs));
    return collect_call_expr(std::move(callee), std::move(call_arguments), loc);
}

ExprResult Session::try_overloaded_subscript(ExprResult& base,
                                             ExprResult& index,
                                             bool* handled,
                                             SrcLoc loc) {
    *handled = false;
    if (!is_record_kind(file_, base.type)) {
        return {};
    }

    std::string name = "operator[]";
    std::vector<cir::EntityId> candidates;
    MemberLookupResult member_lookup =
        lookup_member_name(file_.resolved_type(base.type), name);
    if (member_lookup.ambiguous) {
        report_error("member 'operator[]' is ambiguous through base classes",
                     loc);
        *handled = true;
        ExprResult result;
        result.has_error = true;
        result.type = builder_.unknown_type();
        result.category = ValueCategory::PrValue;
        return result;
    }
    for (const MemberLookupDeclaration& declaration :
         member_lookup.declarations) {
        if (declaration.entity.valid() && file_.valid(declaration.entity) &&
            file_.entity(declaration.entity).kind == cir::EntityKind::Method) {
            candidates.push_back(declaration.entity);
        }
    }
    if (candidates.empty()) {
        return {};
    }

    auto make_ranking_view = [](const ExprResult& source) {
        ExprResult view;
        view.value = source.value;
        view.place = source.place;
        view.type = source.type;
        view.category = source.category;
        view.semantic_object_qualifiers =
            source.semantic_object_qualifiers;
        view.unevaluated_semantic_operand =
            source.unevaluated_semantic_operand;

        view.init_list = source.init_list;
        return view;
    };
    std::vector<ExprResult> ranking;
    ranking.push_back(make_ranking_view(base));
    ranking.push_back(make_ranking_view(index));
    cir::TypeId common_owner{};
    bool same_owner = true;
    for (cir::EntityId candidate : candidates) {
        cir::EntityId owner = file_.entity(candidate).parent;
        cir::TypeId owner_type = owner.valid() && file_.valid(owner)
            ? file_.resolved_type(file_.entity(owner).type)
            : cir::TypeId{};
        if (!owner_type.valid()) {
            continue;
        }
        if (!common_owner.valid()) {
            common_owner = owner_type;
        } else if (common_owner != owner_type) {
            same_owner = false;
            break;
        }
    }
    if (same_owner && common_owner.valid()) {
        ranking.front().type = common_owner;
    }
    bool ambiguous = false;
    OverloadAmbiguityInfo ambiguity_info;
    cir::EntityId selected = select_overload(candidates,
                                             ranking,
                                             /*member_object_leading=*/true,
                                             &ambiguous,
                                             {},
                                             &ambiguity_info);
    if (!selected.valid()) {
        if (ambiguous) {
            report_error("use of overloaded operator '[]' is ambiguous", loc);
            report_overload_ambiguity_notes(ambiguity_info, loc);
            *handled = true;
            ExprResult result;
            result.has_error = true;
            result.type = builder_.unknown_type();
            result.category = ValueCategory::PrValue;
            return result;
        }
        return {};
    }

    *handled = true;
    MemberAccessBase access = collect_member_access_base(
        std::move(base), /*is_arrow=*/false, loc);
    ExprResult callee = collect_bound_member_function_access_expr(
        std::move(access), {selected}, name, loc, &member_lookup);
    callee.qualified_name = true;
    std::vector<ExprResult> call_arguments;
    call_arguments.push_back(std::move(index));
    return collect_call_expr(std::move(callee), std::move(call_arguments), loc);
}

cir::EntityId Session::select_overloaded_unary_candidate(
    syntax::UnaryOperator op,
    const ExprResult& operand,
    std::string* name_out,
    bool* postfix_out,
    bool* ambiguous_out,
    SrcLoc loc,
    bool diagnose) {
    if (name_out) {
        name_out->clear();
    }
    if (postfix_out) {
        *postfix_out = false;
    }
    if (ambiguous_out) {
        *ambiguous_out = false;
    }
    bool operand_record = is_record_kind(file_, operand.type);
    cir::TypeId resolved_operand = file_.resolved_type(operand.type);
    bool operand_enum = file_.valid(resolved_operand) &&
        file_.type(resolved_operand).kind == cir::TypeKind::Enum;
    if (!operand_record && !operand_enum) {
        return {};
    }
    const char* spelling = nullptr;
    bool postfix = false;
    switch (op) {
        case syntax::UnaryOperator::Dereference: spelling = "*"; break;
        case syntax::UnaryOperator::LogicalNot: spelling = "!"; break;
        case syntax::UnaryOperator::Minus: spelling = "-"; break;
        case syntax::UnaryOperator::Plus: spelling = "+"; break;
        case syntax::UnaryOperator::BitwiseNot: spelling = "~"; break;
        case syntax::UnaryOperator::PrefixIncrement: spelling = "++"; break;
        case syntax::UnaryOperator::PrefixDecrement: spelling = "--"; break;
        case syntax::UnaryOperator::PostfixIncrement:
            spelling = "++";
            postfix = true;
            break;
        case syntax::UnaryOperator::PostfixDecrement:
            spelling = "--";
            postfix = true;
            break;
        case syntax::UnaryOperator::CoAwait:

            spelling = "co_await";
            break;
        default:
            return {};
    }

    std::string name = std::string("operator") + spelling;
    if (name_out) {
        *name_out = name;
    }
    if (postfix_out) {
        *postfix_out = postfix;
    }
    std::vector<cir::EntityId> candidates;
    std::vector<cir::EntityId> member_candidates;
    MemberLookupResult member_lookup;
    if (operand_record) {
        member_lookup = lookup_member_name(resolved_operand, name);
        if (member_lookup.ambiguous) {
            if (ambiguous_out) {
                *ambiguous_out = true;
            }
            if (diagnose) {
                report_error("member '" + name +
                                 "' is ambiguous through base classes",
                             loc);
            }
            return {};
        }
        for (const MemberLookupDeclaration& declaration :
             member_lookup.declarations) {
            if (declaration.entity.valid() && file_.valid(declaration.entity) &&
                file_.entity(declaration.entity).kind == cir::EntityKind::Method) {
                member_candidates.push_back(declaration.entity);
            }
        }
    }
    candidates = member_candidates;
    if (const cir::Binding* free_binding = file_.lookup_callable_binding(
            current_decl_context(), name, /*include_parents=*/true)) {
        for (cir::EntityId entity : free_binding->entities) {
            if (std::find(candidates.begin(), candidates.end(), entity) ==
                candidates.end()) {
                candidates.push_back(entity);
            }
        }
    }
    {
        std::vector<ExprResult> operand_view;
        operand_view.push_back(ExprResult{});
        operand_view.back().type = operand.type;
        operand_view.back().category = operand.category;
        add_adl_candidates(name, operand_view, candidates);
    }
    if (candidates.empty()) {
        return {};
    }

    std::vector<ExprResult> ranking;
    ranking.push_back(ExprResult{});
    ranking.back().type = operand.type;
    ranking.back().category = operand.category;

    ranking.back().place = operand.place;
    ranking.back().semantic_object_qualifiers =
        operand.semantic_object_qualifiers;
    ranking.back().unevaluated_semantic_operand =
        operand.unevaluated_semantic_operand;
    if (postfix) {
        ranking.push_back(ExprResult{});
        ranking.back().type = builder_.int_type();
        ranking.back().category = ValueCategory::PrValue;
    }
    if (!member_candidates.empty()) {
        cir::TypeId common_owner{};
        bool same_owner = true;
        for (cir::EntityId candidate : member_candidates) {
            cir::EntityId owner = file_.entity(candidate).parent;
            cir::TypeId owner_type = owner.valid() && file_.valid(owner)
                ? file_.resolved_type(file_.entity(owner).type)
                : cir::TypeId{};
            if (!owner_type.valid()) {
                continue;
            }
            if (!common_owner.valid()) {
                common_owner = owner_type;
            } else if (common_owner != owner_type) {
                same_owner = false;
                break;
            }
        }
        if (same_owner && common_owner.valid()) {
            ranking.front().type = common_owner;
        }
    }
    expand_operator_function_template_candidates(candidates, ranking, loc);
    if (candidates.empty()) {
        return {};
    }
    bool ambiguous = false;
    OverloadAmbiguityInfo ambiguity_info;
    cir::EntityId selected = select_overload(
        candidates,
        ranking,
        /*member_object_leading=*/true,
        &ambiguous,
        {},
        &ambiguity_info);
    if (!selected.valid()) {
        if (ambiguous) {
            if (ambiguous_out) {
                *ambiguous_out = true;
            }
            if (diagnose) {
                report_error("use of overloaded operator '" +
                                 std::string(spelling) + "' is ambiguous",
                             loc);
                report_overload_ambiguity_notes(ambiguity_info, loc);
            }
        }
        return {};
    }
    return selected;
}

ExprResult Session::try_overloaded_unary(syntax::UnaryOperator op,
                                         ExprResult& operand,
                                         bool* handled,
                                         SrcLoc loc) {
    *handled = false;
    std::string name;
    bool postfix = false;
    bool ambiguous = false;
    cir::EntityId selected = select_overloaded_unary_candidate(
        op,
        operand,
        &name,
        &postfix,
        &ambiguous,
        loc,
        /*diagnose=*/true);
    if (!selected.valid()) {
        if (ambiguous) {
            *handled = true;
            ExprResult result;
            result.has_error = true;
            result.type = builder_.unknown_type();
            result.category = ValueCategory::PrValue;
            return result;
        }
        return {};
    }

    *handled = true;
    const cir::Entity& entity = file_.entity(selected);
    std::vector<ExprResult> call_arguments;
    if (postfix) {
        call_arguments.push_back(make_integer_literal(0, "0", loc));
    }
    if (entity.kind == cir::EntityKind::Method) {
        MemberLookupResult member_lookup =
            lookup_member_name(file_.resolved_type(operand.type), name);
        MemberAccessBase access =
            collect_member_access_base(std::move(operand),
                                       /*is_arrow=*/false,
                                       loc);
        ExprResult designator = collect_bound_member_function_access_expr(
            std::move(access), {selected}, name, loc, &member_lookup);
        designator.qualified_name = true;
        return collect_call_expr(std::move(designator),
                                 std::move(call_arguments),
                                 loc);
    }
    ExprResult designator;
    designator.entity = selected;
    designator.type = entity.type;
    designator.name = name;
    designator.qualified_name = true;
    designator.category = ValueCategory::FunctionDesignator;
    call_arguments.insert(call_arguments.begin(), std::move(operand));
    return collect_call_expr(std::move(designator),
                             std::move(call_arguments),
                             loc);
}

ExprResult Session::try_overloaded_call(ExprResult& callee,
                                        std::vector<ExprResult>& args,
                                        bool* handled,
                                        SrcLoc loc) {
    *handled = false;
    callee = materialize_deferred_entity_place(
        std::move(callee), /*allow_non_odr_constant=*/false, loc);
    if (!callee.has_error && callee.category == ValueCategory::LValue &&
        is_reference_type(callee.type)) {

        callee = deref_reference_lvalue(std::move(callee), loc);
    }
    if (!is_record_kind(file_, callee.type)) {
        return {};
    }

    if (in_template_definition()) {
        const cir::RecordFacts* callee_facts =
            file_.record_facts_for_type(file_.resolved_type(callee.type));
        if (callee_facts && callee_facts->is_lambda_closure) {
            bump_pattern_taint();
            ExprResult combined = std::move(callee);
            for (ExprResult& arg : args) {
                combined.fragment = chain(std::move(combined.fragment),
                                          std::move(arg.fragment), loc);
            }
            *handled = true;
            return make_dependent_expr(std::move(combined), loc);
        }
    }

    // [over.call.object]: the candidates are the operator() members of the
    // class. C++23 permits static call operators; their member-template
    // placeholders are Function entities in the record context rather than
    // Method entities with an implicit object. There is still no
    // namespace-scope or ADL candidate set. Surrogate call functions from
    // conversion-to-function-pointer are not considered yet.
    MemberLookupResult member_lookup =
        lookup_member_name(file_.resolved_type(callee.type), "operator()");
    if (member_lookup.ambiguous) {
        report_error("member 'operator()' is ambiguous through base classes",
                     loc);
        *handled = true;
        ExprResult result;
        result.has_error = true;
        result.type = builder_.unknown_type();
        result.category = ValueCategory::PrValue;
        return result;
    }
    std::vector<cir::EntityId> candidates;
    for (const MemberLookupDeclaration& declaration :
         member_lookup.declarations) {
        cir::EntityId entity = declaration.entity;
        if (!entity.valid() || !file_.valid(entity)) {
            continue;
        }
        const TemplateInfo* member_template = template_info(entity);
        bool callable_member =
            file_.entity(entity).kind == cir::EntityKind::Method ||
            (member_template &&
             !member_template->is_class_template &&
             !member_template->is_alias_template &&
             !member_template->is_variable_template &&
             !member_template->is_concept);
        if (!callable_member) {
            continue;
        }

        if (member_template) {
            if (!tstate().function_template_instantiation_callback_) {
                continue;
            }
            std::vector<TemplateArgument> deduced;
            TemplateArgumentBindings deduced_bindings;
            if (!deduce_template_arguments(*member_template,
                                           args,
                                           deduced,
                                           nullptr,
                                           nullptr,
                                           &deduced_bindings)) {
                continue;
            }
            cir::EntityId specialization =
                tstate().function_template_instantiation_callback_(
                    *member_template, deduced_bindings, loc);
            if (specialization.valid()) {
                candidates.push_back(specialization);
            }
            continue;
        }
        candidates.push_back(entity);
    }
    if (candidates.empty()) {
        report_error("called object of type '" + file_.format_type(callee.type) +
                         "' does not provide a call operator",
                     loc);
        *handled = true;
        ExprResult result;
        result.has_error = true;
        result.type = builder_.unknown_type();
        result.category = ValueCategory::PrValue;
        return result;
    }

    std::vector<ExprResult> ranking;
    ranking.push_back(ExprResult{});
    ranking.back().type = callee.type;
    ranking.back().category = callee.category;

    ranking.back().place = callee.place;
    ranking.back().semantic_object_qualifiers =
        callee.semantic_object_qualifiers;
    ranking.back().unevaluated_semantic_operand =
        callee.unevaluated_semantic_operand;
    for (const ExprResult& arg : args) {
        ranking.push_back(ExprResult{});
        ranking.back().type = arg.type;
        ranking.back().category = arg.category;
        ranking.back().place = arg.place;
        ranking.back().semantic_object_qualifiers =
            arg.semantic_object_qualifiers;
        ranking.back().unevaluated_semantic_operand =
            arg.unevaluated_semantic_operand;
    }
    cir::TypeId common_owner{};
    bool same_owner = true;
    for (cir::EntityId candidate : candidates) {
        cir::EntityId owner = file_.entity(candidate).parent;
        cir::TypeId owner_type = owner.valid() && file_.valid(owner)
            ? file_.resolved_type(file_.entity(owner).type)
            : cir::TypeId{};
        if (!owner_type.valid()) {
            continue;
        }
        if (!common_owner.valid()) {
            common_owner = owner_type;
        } else if (common_owner != owner_type) {
            same_owner = false;
            break;
        }
    }
    if (same_owner && common_owner.valid()) {
        ranking.front().type = common_owner;
    }
    bool ambiguous = false;
    OverloadAmbiguityInfo ambiguity_info;
    cir::EntityId selected = select_overload(
        candidates,
        ranking,
        /*member_object_leading=*/true,
        &ambiguous,
        {},
        &ambiguity_info);
    if (!selected.valid()) {
        report_error((ambiguous
                          ? "call to object of type '"
                          : "no matching call operator for object of type '") +
                         file_.format_type(callee.type) +
                         (ambiguous ? "' is ambiguous" : "'"),
                     loc);
        if (ambiguous) {
            report_overload_ambiguity_notes(ambiguity_info, loc);
        }
        *handled = true;
        ExprResult result;
        result.has_error = true;
        result.type = builder_.unknown_type();
        result.category = ValueCategory::PrValue;
        return result;
    }

    *handled = true;

    size_t visible_parameters = 0;
    if (const cir::FunctionTypePayload* payload =
            function_payload_of(file_, file_.entity(selected).type)) {
        const cir::RecordMethodFact* fact = file_.method_fact(selected);
        size_t hidden_parameters = fact && !fact->is_static ? 1 : 0;
        if (hidden_parameters <= payload->parameters.size()) {
            visible_parameters =
                payload->parameters.size() - hidden_parameters;
        }
    }
    while (args.size() < visible_parameters) {
        size_t parameter_index = args.size();
        if (!callable_default_argument(selected, parameter_index)) {
            report_error("selected call operator is missing default argument facts",
                         loc);
            break;
        }
        if (!default_argument_replay_callback_) {
            report_error("cannot materialize call operator default argument",
                         loc);
            break;
        }
        args.push_back(default_argument_replay_callback_(selected,
                                                         parameter_index,
                                                         loc));
    }

    MemberAccessBase access =
        collect_member_access_base(std::move(callee), /*is_arrow=*/false, loc);
    ExprResult designator = collect_bound_member_function_access_expr(
        std::move(access), {selected}, "operator()", loc, &member_lookup);
    designator.qualified_name = true;
    return collect_call_expr(std::move(designator), std::move(args), loc);
}

cir::BindingId Session::bind_callable(std::string_view name,
                                      cir::EntityId entity,
                                      cir::TypeId type,
                                      bool is_definition,
                                      SrcLoc loc) {
    cir::DeclContextId context = current_decl_context();
    if (!context.valid()) {
        return {};
    }

    for (cir::DeclContextId enclosing = context;
         enclosing.valid() && file_.valid(enclosing);
         enclosing = file_.decl_context(enclosing).parent) {
        cir::DeclContextKind kind = file_.decl_context(enclosing).kind;
        if (kind == cir::DeclContextKind::Record) {
            auto active_access = record_member_access_by_context_.find(
                static_cast<uint64_t>(enclosing.index));
            if (active_access != record_member_access_by_context_.end()) {
                record_member_declaration(
                    entity, file_.decl_context(enclosing).owner,
                    active_access->second, loc);
            }
            break;
        }
        if (kind == cir::DeclContextKind::Function ||
            kind == cir::DeclContextKind::Block ||
            kind == cir::DeclContextKind::Namespace ||
            kind == cir::DeclContextKind::TranslationUnit) {
            break;
        }
    }
    cir::BindingId binding = file_.bind_callable_overload(
        context,
        file_.intern_name(name),
        entity,
        type.valid() ? file_.type_ref(type) : cir::TypeRef{},
        is_definition,
        loc);
    if (binding.valid()) {
        file_.entity_mut(entity).lexical_context = context;
        file_.entity_mut(entity).semantic_context = context;
        bump_lookup_generation();
        cir::Binding* record = file_.binding_mut(binding);
        record->generation = lookup_generation();
        if (!record->entity_generations.empty()) {
            record->entity_generations.back() = lookup_generation();
        }
    }
    return binding;
}

void Session::diagnose_cxx_callable_redeclaration(const cir::Binding& previous,
                                                  std::string_view name,
                                                  cir::TypeId new_type,
                                                  SrcLoc loc) {
    for (cir::EntityId prior : previous.entities) {
        if (!prior.valid() || !file_.valid(prior)) {
            continue;
        }
        cir::TypeId prior_type = file_.entity(prior).type;
        cir::PlaceholderResultFactId placeholder =
            file_.entity(prior).placeholder_result;
        cir::TypeId prior_declared_type = file_.valid(placeholder)
            ? file_.placeholder_result_fact(placeholder)
                  .declared_function_type
            : prior_type;
        if (!function_signatures_match(prior_declared_type, new_type)) {
            continue;
        }
        cir::TypeRef a{file_.resolved_type(prior_declared_type), cir::QualNone,
                       cir::MemorySpace::Default};
        cir::TypeRef b{file_.resolved_type(new_type), cir::QualNone,
                       cir::MemorySpace::Default};
        if (!types_compatible(a, b)) {
            report_error("functions that differ only in their return type "
                         "cannot be overloaded: '" +
                             std::string(name) + "'",
                         loc);
            return;
        }

        const cir::FunctionTypePayload* prior_fn =
            function_payload_of(file_, prior_declared_type);
        const cir::FunctionTypePayload* new_fn =
            function_payload_of(file_, new_type);
        if (prior_fn && new_fn &&
            prior_fn->exception_spec.kind !=
                cir::FunctionExceptionSpecKind::Dependent &&
            new_fn->exception_spec.kind !=
                cir::FunctionExceptionSpecKind::Dependent &&
            prior_fn->exception_spec.kind != new_fn->exception_spec.kind) {
            report_error("exception specification of '" + std::string(name) +
                             "' does not match the previous declaration",
                         loc);
        }
        return;
    }
}

ExprResult Session::collect_binary_expr(syntax::BinaryOperator op,
                                        ExprResult lhs,
                                        ExprResult rhs,
                                        SrcLoc loc) {
    return collect_binary_expr_impl(op, std::move(lhs), std::move(rhs), loc,
                                    /*allow_comparison_rewrites=*/true);
}

ExprResult Session::collect_binary_expr_impl(
    syntax::BinaryOperator op,
    ExprResult lhs,
    ExprResult rhs,
    SrcLoc loc,
    bool allow_comparison_rewrites) {
    if (lhs.objc_property && op == syntax::BinaryOperator::Assign) {

        std::shared_ptr<ObjCPropertyReference> reference =
            std::move(lhs.objc_property);
        if (reference->setter.empty()) {
            report_error("assignment to a readonly property", loc);
            rhs.has_error = true;
            return rhs;
        }
        ObjCMessageSendInput send;
        send.receiver = std::move(*reference->receiver);
        send.selector = reference->setter;
        send.args.push_back(std::move(rhs));
        if (reference->subscript_index) {
            send.args.push_back(std::move(*reference->subscript_index));
        }
        send.loc = loc;
        ExprResult sent = collect_objc_message_send(std::move(send));
        sent.fragment = chain(std::move(lhs.fragment),
                              std::move(sent.fragment), loc);
        return sent;
    }
    if (lhs.objc_property) {
        lhs = resolve_objc_property_load(std::move(lhs), loc);
    }
    if (rhs.objc_property) {
        rhs = resolve_objc_property_load(std::move(rhs), loc);
    }

    if (lhs.has_error || rhs.has_error) {
        lhs.fragment = chain(std::move(lhs.fragment), std::move(rhs.fragment),
                             loc);
        lhs.value = {};
        lhs.place = {};
        lhs.entity = {};
        lhs.type = builder_.unknown_type();
        lhs.category = ValueCategory::PrValue;
        lhs.has_error = true;
        return lhs;
    }
    if (expr_is_dependent(lhs) || expr_is_dependent(rhs)) {

        return make_dependent_binary_operator_expr(
            op, std::move(lhs), std::move(rhs), loc);
    }

    if (lang_opts_.is_cxx_mode()) {
        bool handled = false;
        ExprResult rewritten = try_overloaded_binary(
            op, lhs, rhs, &handled, loc, allow_comparison_rewrites);
        if (handled) {
            return rewritten;
        }

        if (op == syntax::BinaryOperator::Assign) {
            const cir::RecordFacts* facts =
                file_.record_facts_for_type(file_.resolved_type(lhs.type));
            if (facts && facts->is_lambda_closure && !facts->fields.empty()) {
                report_error("the closure type's copy assignment operator "
                             "is deleted",
                             loc);
                ExprResult result;
                result.has_error = true;
                result.type = builder_.unknown_type();
                result.category = ValueCategory::PrValue;
                return result;
            }
        }
    }
    return collect_binary_expr_builtin(op, std::move(lhs), std::move(rhs), loc);
}

} // namespace aburi::collect
