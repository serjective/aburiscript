#include "collect.h"

#include <algorithm>

namespace aburi::collect {

namespace {

const cir::FunctionTypePayload* function_payload(const cir::File& file,
                                                 cir::EntityId callable) {
    if (!callable.valid() || !file.valid(callable)) {
        return nullptr;
    }
    cir::TypeId type = file.resolved_type(file.entity(callable).type);
    if (!file.valid(type) || file.type(type).kind != cir::TypeKind::Function) {
        return nullptr;
    }
    return std::get_if<cir::FunctionTypePayload>(&file.type_payload(type));
}

} // namespace

Session::UnevaluatedOperand Session::make_declval_operand(
    cir::TypeRef input) const {
    UnevaluatedOperand operand;
    if (!input.valid()) {
        return operand;
    }

    cir::TypeId resolved = file_.resolved_type(input.type);
    if (!file_.valid(resolved)) {
        return operand;
    }

    operand.type = input;
    operand.object_qualifiers = input.qualifiers;
    switch (file_.type(resolved).kind) {
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference: {
            cir::TypeRef referred = file_.reference_referred_ref(resolved);
            if (!referred.valid()) {
                return {};
            }
            operand.type = referred;
            operand.object_qualifiers |= referred.qualifiers;
            cir::TypeId referred_type = file_.resolved_type(referred.type);
            bool function = file_.valid(referred_type) &&
                file_.type(referred_type).kind == cir::TypeKind::Function;
            operand.category =
                file_.type(resolved).kind == cir::TypeKind::LValueReference ||
                        function
                    ? ValueCategory::LValue
                    : ValueCategory::XValue;
            return operand;
        }
        case cir::TypeKind::Function:

            operand.category = ValueCategory::LValue;
            return operand;
        case cir::TypeKind::Builtin: {
            const auto* builtin = std::get_if<cir::BuiltinTypePayload>(
                &file_.type_payload(resolved));
            if (builtin && builtin->kind == cir::BuiltinTypeKind::Void) {
                operand.category = ValueCategory::PrValue;
                return operand;
            }
            break;
        }
        default:
            break;
    }

    operand.category = ValueCategory::XValue;
    return operand;
}

ExprResult Session::unevaluated_operand_view(
    const UnevaluatedOperand& operand) const {
    ExprResult result;
    if (!operand.valid()) {
        result.has_error = true;
        return result;
    }
    result.type = operand.type.type;
    result.category = operand.category;
    result.semantic_object_qualifiers = operand.object_qualifiers;
    result.unevaluated_semantic_operand = true;
    return result;
}

bool Session::operation_probe_record_callable(OperationProbe& probe,
                                              cir::EntityId callable) const {
    if (!callable.valid() || !file_.valid(callable)) {
        return false;
    }
    const cir::RecordMethodFact* method = file_.method_fact(callable);
    if (method && (method->is_deleted || !method->is_eligible)) {
        probe.failure = OperationProbeFailure::Deleted;
        return false;
    }
    if (method &&
        method->declared_access != cir::RecordMemberAccess::Public) {
        probe.failure = OperationProbeFailure::Inaccessible;
        return false;
    }
    const cir::FunctionTypePayload* payload =
        function_payload(file_, callable);
    OperationProbeStep step;
    step.callable = callable;
    step.trivial = method && method->is_trivial;
    step.nothrow = payload &&
        payload->exception_spec.kind ==
            cir::FunctionExceptionSpecKind::NonThrowing;
    probe.steps.push_back(step);
    probe.selected = callable;
    probe.trivial = probe.trivial && step.trivial;
    probe.nothrow = probe.nothrow && step.nothrow;
    return true;
}

bool Session::operation_probe_public_base_conversion(cir::TypeId source,
                                                     cir::TypeId target) const {
    source = file_.resolved_type(source);
    target = file_.resolved_type(target);
    DerivedToBasePathResult path =
        analyze_derived_to_base_path(source, target);
    if (path.kind != DerivedToBasePathKind::Unique) {
        return false;
    }
    std::vector<cir::TypeId> pending{source};
    std::unordered_set<uint64_t> visited;
    while (!pending.empty()) {
        cir::TypeId current = file_.resolved_type(pending.back());
        pending.pop_back();
        if (!file_.valid(current) ||
            !visited.insert(static_cast<uint64_t>(current.index)).second) {
            continue;
        }
        if (current == target) {
            return true;
        }
        const cir::RecordFacts* facts = file_.record_facts_for_type(current);
        if (!facts) {
            continue;
        }
        for (const cir::RecordBaseFact& base : facts->bases) {
            if (base.declared_access == cir::RecordMemberAccess::Public) {
                pending.push_back(base.type.type);
            }
        }
    }
    return false;
}

bool Session::operation_probe_standard_sequence_usable(
    const StandardConversionSequence& sequence) const {
    if (!sequence.has(StandardConversionStep::DerivedToBase)) {
        return true;
    }
    cir::TypeId source = file_.resolved_type(sequence.source.type);
    cir::TypeId target = file_.resolved_type(sequence.target.type);
    if (!file_.valid(source) || !file_.valid(target)) {
        return false;
    }
    cir::TypeKind source_kind = file_.type(source).kind;
    cir::TypeKind target_kind = file_.type(target).kind;
    if (source_kind == cir::TypeKind::Pointer &&
        target_kind == cir::TypeKind::Pointer) {
        source = file_.pointer_pointee_type(source);
        target = file_.pointer_pointee_type(target);
    } else if (source_kind == cir::TypeKind::MemberPointer &&
               target_kind == cir::TypeKind::MemberPointer) {
        const auto* source_member =
            std::get_if<cir::MemberPointerTypePayload>(
                &file_.type_payload(source));
        const auto* target_member =
            std::get_if<cir::MemberPointerTypePayload>(
                &file_.type_payload(target));
        if (!source_member || !target_member) {
            return false;
        }

        source = target_member->class_type.type;
        target = source_member->class_type.type;
    }
    target = file_.resolved_type(target);
    if (file_.valid(target) &&
        (file_.type(target).kind == cir::TypeKind::LValueReference ||
         file_.type(target).kind == cir::TypeKind::RValueReference)) {
        target = file_.reference_referred_ref(target).type;
    }
    return operation_probe_public_base_conversion(source, target);
}

bool Session::operation_probe_require_public_destructor(
    OperationProbe& probe,
    cir::TypeId type) const {
    cir::TypeId resolved = file_.resolved_type(type);
    if (!file_.valid(resolved) ||
        file_.type(resolved).kind != cir::TypeKind::Record) {
        return true;
    }
    const cir::RecordMethodFact* destructor =
        selected_record_destructor(resolved);
    if (!destructor || !destructor->is_selected_destructor ||
        !destructor->is_eligible || destructor->is_deleted) {
        probe.failure = OperationProbeFailure::Deleted;
        return false;
    }
    if (destructor->declared_access != cir::RecordMemberAccess::Public) {
        probe.failure = OperationProbeFailure::Inaccessible;
        return false;
    }
    cir::EntityId primary = probe.selected;
    bool usable = operation_probe_record_callable(probe, destructor->entity);
    if (primary.valid()) {
        probe.selected = primary;
    }
    return usable;
}

Session::OperationProbe Session::probe_implicit_conversion(
    cir::TypeRef from,
    cir::TypeRef to,
    bool core_convertibility) {
    OperationProbe result;
    auto transaction = speculative_parse();

    auto fail = [&](OperationProbeFailure failure) {
        result.failure = failure;
        result.viable = false;
        result.trivial = false;
        result.nothrow = false;
        return result;
    };

    if (!from.valid() || !to.valid()) {
        return fail(OperationProbeFailure::InvalidType);
    }
    cir::TypeId from_type = file_.resolved_type(from.type);
    cir::TypeId to_type = file_.resolved_type(to.type);
    if (!file_.valid(from_type) || !file_.valid(to_type) ||
        is_dependent_type(from_type) || is_dependent_type(to_type)) {
        return fail(OperationProbeFailure::Dependent);
    }

    auto require_complete_record = [&](cir::TypeId candidate) {
        candidate = file_.resolved_type(candidate);
        if (!file_.valid(candidate) ||
            file_.type(candidate).kind != cir::TypeKind::Record) {
            return true;
        }
        const cir::RecordFacts* facts =
            file_.record_facts_for_type(candidate);
        if (facts && !facts->is_incomplete) {
            return true;
        }
        if (!require_complete_class_type(
                candidate, SrcLoc(),
                cir::InstantiationDemandKind::CompleteClass)) {
            return false;
        }
        facts = file_.record_facts_for_type(candidate);
        return facts && !facts->is_incomplete;
    };
    cir::TypeKind from_kind = file_.type(from_type).kind;
    cir::TypeKind to_kind = file_.type(to_type).kind;
    if (from_kind == cir::TypeKind::Pointer &&
        to_kind == cir::TypeKind::Pointer) {
        cir::TypeId source_pointee = file_.resolved_type(
            file_.pointer_pointee_type(from_type));
        cir::TypeId target_pointee = file_.resolved_type(
            file_.pointer_pointee_type(to_type));
        if (file_.valid(source_pointee) && file_.valid(target_pointee) &&
            source_pointee != target_pointee &&
            file_.type(source_pointee).kind == cir::TypeKind::Record &&
            file_.type(target_pointee).kind == cir::TypeKind::Record &&
            !require_complete_record(source_pointee)) {
            return fail(OperationProbeFailure::NoViableOperation);
        }
    } else if (from_kind == cir::TypeKind::MemberPointer &&
               to_kind == cir::TypeKind::MemberPointer) {
        const auto* target_member =
            std::get_if<cir::MemberPointerTypePayload>(
                &file_.type_payload(to_type));
        const auto* source_member =
            std::get_if<cir::MemberPointerTypePayload>(
                &file_.type_payload(from_type));
        if (target_member && source_member &&
            file_.resolved_type(target_member->class_type.type) !=
                file_.resolved_type(source_member->class_type.type) &&
            !require_complete_record(target_member->class_type.type)) {
            return fail(OperationProbeFailure::NoViableOperation);
        }
    }

    const bool from_void = is_void_type(from_type);
    const bool to_void = is_void_type(to_type);
    if (core_convertibility) {
        if (from_void || to_void) {
            return fail(OperationProbeFailure::NoViableOperation);
        }
    } else if (from_void || to_void) {
        if (!(from_void && to_void)) {
            return fail(OperationProbeFailure::NoViableOperation);
        }
        result.failure = OperationProbeFailure::None;
        result.viable = true;
        result.trivial = true;
        result.nothrow = true;
        return result;
    }

    cir::TypeKind target_kind = to_kind;
    if (target_kind == cir::TypeKind::Array ||
        target_kind == cir::TypeKind::Function ||
        target_kind == cir::TypeKind::Invalid ||
        target_kind == cir::TypeKind::Error ||
        target_kind == cir::TypeKind::Unknown) {
        return fail(OperationProbeFailure::NoViableOperation);
    }
    if (target_kind == cir::TypeKind::Record) {
        const cir::RecordFacts* facts = file_.record_facts_for_type(to_type);
        if (!facts || facts->is_incomplete || facts->is_abstract) {
            return fail(OperationProbeFailure::NoViableOperation);
        }
    }
    if (from_kind == cir::TypeKind::Record) {
        const cir::RecordFacts* facts = file_.record_facts_for_type(from_type);
        if (!facts || facts->is_incomplete) {
            return fail(OperationProbeFailure::NoViableOperation);
        }
    }

    UnevaluatedOperand operand = make_declval_operand(from);
    if (!operand.valid()) {
        return fail(OperationProbeFailure::InvalidType);
    }
    if (core_convertibility) {

        operand.category = ValueCategory::PrValue;
    }
    ExprResult source = unevaluated_operand_view(operand);
    result.failure = OperationProbeFailure::None;
    result.viable = true;
    result.trivial = true;
    result.nothrow = true;

    if (target_kind == cir::TypeKind::Record &&
        core_convertibility && from_type == to_type) {
        if (!operation_probe_require_public_destructor(result, to_type)) {
            return fail(result.failure);
        }
        return result;
    }

    cir::EntityId selected;
    UserConversionSequence user_sequence;
    bool used_user_sequence = false;
    if (target_kind == cir::TypeKind::Record ||
        file_.type(from_type).kind == cir::TypeKind::Record) {
        user_sequence = resolve_initialization_user_conversion(
            source, to_type, UserConversionContext::CopyInitialization,
            SrcLoc());
        if (user_sequence.kind == UserConversionSequence::Kind::Ambiguous) {
            return fail(OperationProbeFailure::Ambiguous);
        }
        if (user_sequence.kind != UserConversionSequence::Kind::None) {
            selected = user_sequence.callable;
            used_user_sequence = true;
            if (!operation_probe_standard_sequence_usable(
                    user_sequence.initial_standard) ||
                !operation_probe_standard_sequence_usable(
                    user_sequence.trailing_standard)) {
                return fail(OperationProbeFailure::Inaccessible);
            }
        }
    }

    ConversionDetail detail;
    if (!used_user_sequence && target_kind == cir::TypeKind::Record) {
        bool ambiguous = false;
        selected = select_constructor(
            to_type, {source}, &ambiguous, SrcLoc(),
            ConstructorInitializationKind::Copy,
            /*demand_selected=*/false);
        if (ambiguous) {
            return fail(OperationProbeFailure::Ambiguous);
        }
        if (!selected.valid()) {
            return fail(OperationProbeFailure::NoViableOperation);
        }
        const cir::FunctionTypePayload* constructor =
            function_payload(file_, selected);
        if (constructor && constructor->parameters.size() >= 2) {
            ConversionRank rank = conversion_rank(
                source, constructor->parameters[1],
                operand.object_qualifiers, &detail,
                /*allow_user_defined=*/false);
            if (rank == ConversionRank::Bad ||
                !operation_probe_standard_sequence_usable(detail.standard)) {
                return fail(OperationProbeFailure::Inaccessible);
            }
        }
    } else if (!used_user_sequence) {
        ConversionRank rank = conversion_rank(
            source, to, operand.object_qualifiers, &detail,
            /*allow_user_defined=*/true);
        if (rank == ConversionRank::Bad) {
            return fail(OperationProbeFailure::NoViableOperation);
        }
        if (rank == ConversionRank::UserDefined) {
            if (!detail.user_conversion_unique ||
                !detail.user_conversion.valid()) {
                return fail(OperationProbeFailure::Ambiguous);
            }
            selected = detail.user_conversion;
        }
        if (!operation_probe_standard_sequence_usable(detail.standard) ||
            !operation_probe_standard_sequence_usable(
                detail.trailing_standard)) {
            return fail(OperationProbeFailure::Inaccessible);
        }
    }

    if (selected.valid() &&
        !operation_probe_record_callable(result, selected)) {
        return fail(result.failure);
    }

    if (selected.valid() && file_.valid(selected) &&
        file_.entity(selected).kind == cir::EntityKind::Method) {
        cir::EntityId owner = file_.entity(selected).parent;
        cir::TypeId owner_type = owner.valid() && file_.valid(owner)
            ? file_.resolved_type(file_.entity(owner).type)
            : cir::TypeId{};
        if (owner_type.valid() && owner_type != from_type &&
            file_.type(from_type).kind == cir::TypeKind::Record &&
            !operation_probe_public_base_conversion(from_type, owner_type)) {
            return fail(OperationProbeFailure::Inaccessible);
        }
    }

    if (!operation_probe_require_public_destructor(result, to_type)) {
        return fail(result.failure);
    }
    return result;
}

bool Session::probe_reference_binds_to_temporary(cir::TypeRef target,
                                                 cir::TypeRef source) {
    auto transaction = speculative_parse();
    if (!target.valid() || !source.valid()) {
        return false;
    }

    cir::TypeId target_type = file_.resolved_type(target.type);
    cir::TypeId source_type = file_.resolved_type(source.type);
    if (!file_.valid(target_type) || !file_.valid(source_type) ||
        is_dependent_type(target_type) || is_dependent_type(source_type)) {
        return false;
    }
    cir::TypeKind target_kind = file_.type(target_type).kind;
    if (target_kind != cir::TypeKind::LValueReference &&
        target_kind != cir::TypeKind::RValueReference) {
        return false;
    }
    cir::TypeRef referred = file_.reference_referred_ref(target_type);
    cir::TypeId referred_type = file_.resolved_type(referred.type);
    if (!file_.valid(referred_type) ||
        file_.type(referred_type).kind == cir::TypeKind::Function) {
        return false;
    }

    if (!probe_construction(target, {source}).viable) {
        return false;
    }

    UnevaluatedOperand operand = make_declval_operand(source);
    if (!operand.valid()) {
        return false;
    }
    cir::TypeKind written_source_kind = file_.type(source_type).kind;
    if (written_source_kind != cir::TypeKind::LValueReference &&
        written_source_kind != cir::TypeKind::RValueReference &&
        written_source_kind != cir::TypeKind::Function) {
        operand.category = ValueCategory::PrValue;
    }
    ExprResult source_view = unevaluated_operand_view(operand);

    ConversionDetail detail;
    ConversionRank rank = conversion_rank(
        source_view, target, operand.object_qualifiers, &detail,
        /*allow_user_defined=*/true);

    if (rank != ConversionRank::Bad &&
        detail.standard.has(StandardConversionStep::ReferenceBinding) &&
        !detail.standard.binds_converted_temporary) {
        return false;
    }

    cir::EntityId conversion;
    if (rank == ConversionRank::UserDefined &&
        detail.user_conversion_unique) {
        conversion = detail.user_conversion;
    }
    if (!conversion.valid()) {
        bool ambiguous = false;
        ExprResult conversion_source = source_view;
        if (conversion_source.category == ValueCategory::PrValue &&
            file_.type(source_type).kind == cir::TypeKind::Record) {

            conversion_source.category = ValueCategory::XValue;
        }
        conversion = select_conversion_function(
            conversion_source, target_type, &ambiguous, SrcLoc(),
            UserConversionContext::DirectReferenceBinding);
        if (ambiguous) {
            return false;
        }
    }
    if (!conversion.valid() || !file_.valid(conversion)) {

        return true;
    }
    if (file_.entity(conversion).kind == cir::EntityKind::Constructor) {
        return true;
    }

    const cir::FunctionTypePayload* payload =
        function_payload(file_, conversion);
    if (!payload || !payload->return_type.valid()) {
        return true;
    }
    cir::TypeId return_type =
        file_.resolved_type(payload->return_type.type);
    if (!file_.valid(return_type) ||
        (file_.type(return_type).kind != cir::TypeKind::LValueReference &&
         file_.type(return_type).kind != cir::TypeKind::RValueReference)) {

        return true;
    }

    UnevaluatedOperand converted =
        make_declval_operand(payload->return_type);
    if (!converted.valid()) {
        return true;
    }
    ConversionDetail converted_detail;
    ConversionRank converted_rank = conversion_rank(
        unevaluated_operand_view(converted), target,
        converted.object_qualifiers, &converted_detail,
        /*allow_user_defined=*/false);
    return converted_rank == ConversionRank::Bad ||
        !converted_detail.standard.has(
            StandardConversionStep::ReferenceBinding);
}

Session::OperationProbe Session::probe_assignment(cir::TypeRef lhs,
                                                  cir::TypeRef rhs) {
    OperationProbe result;
    auto transaction = speculative_parse();

    auto fail = [&](OperationProbeFailure failure) {
        result.failure = failure;
        result.viable = false;
        result.trivial = false;
        result.nothrow = false;
        return result;
    };
    if (!lhs.valid() || !rhs.valid()) {
        return fail(OperationProbeFailure::InvalidType);
    }
    cir::TypeId lhs_written = file_.resolved_type(lhs.type);
    cir::TypeId rhs_written = file_.resolved_type(rhs.type);
    if (!file_.valid(lhs_written) || !file_.valid(rhs_written) ||
        is_dependent_type(lhs_written) || is_dependent_type(rhs_written)) {
        return fail(OperationProbeFailure::Dependent);
    }

    UnevaluatedOperand lhs_operand = make_declval_operand(lhs);
    UnevaluatedOperand rhs_operand = make_declval_operand(rhs);
    if (!lhs_operand.valid() || !rhs_operand.valid()) {
        return fail(OperationProbeFailure::InvalidType);
    }
    cir::TypeId lhs_type = file_.resolved_type(lhs_operand.type.type);
    if (!file_.valid(lhs_type)) {
        return fail(OperationProbeFailure::InvalidType);
    }
    cir::TypeKind lhs_kind = file_.type(lhs_type).kind;
    if (lhs_kind == cir::TypeKind::Array ||
        lhs_kind == cir::TypeKind::Function ||
        lhs_kind == cir::TypeKind::Invalid ||
        lhs_kind == cir::TypeKind::Error ||
        lhs_kind == cir::TypeKind::Unknown ||
        is_void_type(lhs_type)) {
        return fail(OperationProbeFailure::NoViableOperation);
    }

    ExprResult lhs_view = unevaluated_operand_view(lhs_operand);
    ExprResult rhs_view = unevaluated_operand_view(rhs_operand);
    result.failure = OperationProbeFailure::None;
    result.viable = true;
    result.trivial = true;
    result.nothrow = true;

    if (lhs_kind != cir::TypeKind::Record) {
        if (lhs_operand.category != ValueCategory::LValue ||
            (lhs_operand.object_qualifiers & cir::QualConst) != 0) {
            return fail(OperationProbeFailure::NoViableOperation);
        }
        OperationProbe conversion = probe_implicit_conversion(
            rhs, lhs_operand.type);
        if (!conversion.viable) {
            return fail(conversion.failure);
        }
        result.trivial = conversion.trivial;
        result.nothrow = conversion.nothrow;
        result.steps = std::move(conversion.steps);
        result.selected = conversion.selected;
        return result;
    }

    const cir::RecordFacts* facts = file_.record_facts_for_type(lhs_type);
    if (!facts || facts->is_incomplete) {
        return fail(OperationProbeFailure::NoViableOperation);
    }
    MemberLookupResult lookup = lookup_member_name(lhs_type, "operator=");
    if (lookup.ambiguous) {
        return fail(OperationProbeFailure::Ambiguous);
    }
    std::vector<OverloadCandidate> candidates;
    for (const MemberLookupDeclaration& declaration : lookup.declarations) {
        if (!declaration.entity.valid() ||
            !file_.valid(declaration.entity) ||
            file_.entity(declaration.entity).kind != cir::EntityKind::Method) {
            continue;
        }
        OverloadCandidate candidate;
        candidate.entity = declaration.entity;
        candidate.member_object_leading = true;
        candidates.push_back(candidate);
    }
    if (candidates.empty()) {
        return fail(OperationProbeFailure::NoViableOperation);
    }

    std::vector<ExprResult> ranking{lhs_view, rhs_view};
    expand_operator_function_template_candidates(candidates, ranking,
                                                 SrcLoc());
    bool ambiguous = false;
    cir::EntityId selected = select_overload(
        candidates, ranking, &ambiguous, {}, nullptr,
        /*allow_user_defined_argument_conversions=*/true);
    if (ambiguous) {
        return fail(OperationProbeFailure::Ambiguous);
    }
    if (!selected.valid()) {
        return fail(OperationProbeFailure::NoViableOperation);
    }

    cir::EntityId owner = file_.entity(selected).parent;
    cir::TypeId owner_type = owner.valid() && file_.valid(owner)
        ? file_.resolved_type(file_.entity(owner).type)
        : cir::TypeId{};
    if (owner_type.valid() && owner_type != lhs_type &&
        !operation_probe_public_base_conversion(lhs_type, owner_type)) {
        return fail(OperationProbeFailure::Inaccessible);
    }
    if (!operation_probe_record_callable(result, selected)) {
        return fail(result.failure);
    }

    const cir::FunctionTypePayload* payload =
        function_payload(file_, selected);
    if (!payload || payload->parameters.size() < 2) {
        return fail(OperationProbeFailure::NoViableOperation);
    }
    OperationProbe argument =
        probe_implicit_conversion(rhs, payload->parameters[1]);
    if (!argument.viable) {
        return fail(argument.failure);
    }
    result.trivial = result.trivial && argument.trivial;
    result.nothrow = result.nothrow && argument.nothrow;
    result.steps.insert(result.steps.end(), argument.steps.begin(),
                        argument.steps.end());
    result.selected = selected;
    return result;
}

Session::OperationProbe Session::probe_construction(
    cir::TypeRef target,
    const std::vector<cir::TypeRef>& arguments) {
    OperationProbe result;
    auto transaction = speculative_parse();

    auto fail = [&](OperationProbeFailure failure) {
        result.failure = failure;
        result.viable = false;
        result.trivial = false;
        result.nothrow = false;
        return result;
    };
    auto merge = [&](const OperationProbe& nested) {
        if (!nested.viable) {
            result.failure = nested.failure;
            return false;
        }
        result.trivial = result.trivial && nested.trivial;
        result.nothrow = result.nothrow && nested.nothrow;
        result.steps.insert(result.steps.end(), nested.steps.begin(),
                            nested.steps.end());
        return true;
    };

    if (!target.valid() ||
        std::any_of(arguments.begin(), arguments.end(),
                    [](cir::TypeRef argument) {
                        return !argument.valid();
                    })) {
        return fail(OperationProbeFailure::InvalidType);
    }
    cir::TypeId target_type = file_.resolved_type(target.type);
    if (!file_.valid(target_type) || is_dependent_type(target_type)) {
        return fail(OperationProbeFailure::Dependent);
    }
    for (cir::TypeRef argument : arguments) {
        cir::TypeId argument_type = file_.resolved_type(argument.type);
        if (!file_.valid(argument_type) ||
            is_dependent_type(argument_type)) {
            return fail(OperationProbeFailure::Dependent);
        }
    }

    result.failure = OperationProbeFailure::None;
    result.viable = true;
    result.trivial = true;
    result.nothrow = true;

    cir::TypeKind target_kind = file_.type(target_type).kind;
    if (target_kind == cir::TypeKind::Invalid ||
        target_kind == cir::TypeKind::Error ||
        target_kind == cir::TypeKind::Unknown ||
        target_kind == cir::TypeKind::Function || is_void_type(target_type)) {
        return fail(OperationProbeFailure::NoViableOperation);
    }

    if (target_kind == cir::TypeKind::Array) {
        const auto* array = std::get_if<cir::ArrayTypePayload>(
            &file_.type_payload(target_type));
        if (!array ||
            array->size_kind != cir::ArraySizeKind::Constant ||
            !array->size.has_value() || arguments.size() > *array->size) {
            return fail(OperationProbeFailure::NoViableOperation);
        }
        for (size_t i = 0; i < *array->size; ++i) {
            std::vector<cir::TypeRef> element_arguments;
            if (i < arguments.size()) {
                element_arguments.push_back(arguments[i]);
            }
            OperationProbe element =
                probe_construction(array->element_type, element_arguments);
            if (!merge(element)) {
                return fail(result.failure);
            }
        }
        return result;
    }

    const bool target_reference =
        target_kind == cir::TypeKind::LValueReference ||
        target_kind == cir::TypeKind::RValueReference;
    if (target_reference && arguments.size() != 1) {
        return fail(OperationProbeFailure::NoViableOperation);
    }

    if (target_kind != cir::TypeKind::Record) {
        if (arguments.empty()) {
            return target_reference
                ? fail(OperationProbeFailure::NoViableOperation)
                : result;
        }
        if (arguments.size() != 1) {
            return fail(OperationProbeFailure::NoViableOperation);
        }

        OperationProbe conversion =
            probe_implicit_conversion(arguments.front(), target);
        if (conversion.viable) {
            return conversion;
        }

        UnevaluatedOperand source_operand =
            make_declval_operand(arguments.front());
        cir::TypeId source_type = source_operand.valid()
            ? file_.resolved_type(source_operand.type.type)
            : cir::TypeId{};
        if (!source_operand.valid() || !file_.valid(source_type) ||
            file_.type(source_type).kind != cir::TypeKind::Record) {
            return fail(conversion.failure);
        }
        ExprResult source = unevaluated_operand_view(source_operand);
        bool ambiguous = false;
        cir::EntityId selected = select_conversion_function(
            source, target_type, &ambiguous, SrcLoc(),
            target_reference
                ? UserConversionContext::DirectReferenceBinding
                : UserConversionContext::DirectInitialization);
        if (ambiguous) {
            return fail(OperationProbeFailure::Ambiguous);
        }
        if (!selected.valid()) {
            return fail(conversion.failure);
        }
        cir::EntityId owner = file_.entity(selected).parent;
        cir::TypeId owner_type = owner.valid() && file_.valid(owner)
            ? file_.resolved_type(file_.entity(owner).type)
            : cir::TypeId{};
        if (owner_type.valid() && owner_type != source_type &&
            !operation_probe_public_base_conversion(source_type,
                                                    owner_type)) {
            return fail(OperationProbeFailure::Inaccessible);
        }
        if (!operation_probe_record_callable(result, selected)) {
            return fail(result.failure);
        }
        return result;
    }

    const cir::RecordFacts* facts = file_.record_facts_for_type(target_type);
    if (!facts || facts->is_incomplete || facts->is_abstract) {
        return fail(OperationProbeFailure::NoViableOperation);
    }

    bool copy_or_move_initialization = false;
    if (arguments.size() == 1) {
        UnevaluatedOperand source = make_declval_operand(arguments.front());
        cir::TypeId source_type = source.valid()
            ? file_.resolved_type(source.type.type)
            : cir::TypeId{};
        copy_or_move_initialization = file_.valid(source_type) &&
            file_.type(source_type).kind == cir::TypeKind::Record &&
            (source_type == target_type ||
             analyze_derived_to_base_path(source_type, target_type).kind !=
                 DerivedToBasePathKind::NotFound);
    }

    const bool aggregate =
        facts->is_aggregate == cir::ClassPropertyState::True &&
        !record_has_user_constructor(target_type) &&
        !copy_or_move_initialization;
    if (aggregate) {
        std::vector<const cir::RecordFieldFact*> elements;
        for (const cir::RecordFieldFact& field : facts->fields) {
            bool initializable = field.name.valid() ||
                (!field.is_bitfield && field.type.type.valid());
            if (initializable && !field.is_flexible_array_member) {
                elements.push_back(&field);
            }
        }
        if (facts->kind == cir::RecordKind::Union && elements.size() > 1) {
            elements.resize(1);
        }
        if (arguments.size() > elements.size()) {
            return fail(OperationProbeFailure::NoViableOperation);
        }
        for (size_t i = 0; i < elements.size(); ++i) {
            const cir::RecordFieldFact& field = *elements[i];
            if (i >= arguments.size() &&
                field.has_default_member_initializer) {
                result.trivial = false;
                result.nothrow = result.nothrow &&
                    !field.default_member_initializer_potentially_throwing;
                continue;
            }
            std::vector<cir::TypeRef> field_arguments;
            if (i < arguments.size()) {
                field_arguments.push_back(arguments[i]);
            }
            OperationProbe field_probe =
                probe_construction(field.type, field_arguments);
            if (!merge(field_probe)) {
                return fail(result.failure);
            }
        }
        if (!operation_probe_require_public_destructor(result,
                                                       target_type)) {
            return fail(result.failure);
        }
        return result;
    }

    std::vector<ExprResult> argument_views;
    argument_views.reserve(arguments.size());
    for (cir::TypeRef argument : arguments) {
        UnevaluatedOperand operand = make_declval_operand(argument);
        if (!operand.valid()) {
            return fail(OperationProbeFailure::InvalidType);
        }
        argument_views.push_back(unevaluated_operand_view(operand));
    }
    bool ambiguous = false;
    cir::EntityId selected = select_constructor(
        target_type, argument_views, &ambiguous, SrcLoc(),
        ConstructorInitializationKind::Direct,
        /*demand_selected=*/false);
    if (ambiguous) {
        return fail(OperationProbeFailure::Ambiguous);
    }
    if (!selected.valid()) {
        return fail(OperationProbeFailure::NoViableOperation);
    }
    if (!operation_probe_record_callable(result, selected)) {
        return fail(result.failure);
    }

    const cir::FunctionTypePayload* payload =
        function_payload(file_, selected);
    if (!payload || payload->parameters.empty()) {
        return fail(OperationProbeFailure::NoViableOperation);
    }
    size_t visible_parameters = payload->parameters.size() - 1;
    if (!facts->virtual_bases.empty()) {
        visible_parameters = visible_parameters >= 2
            ? visible_parameters - 2
            : 0;
    }
    if (arguments.size() > visible_parameters) {
        return fail(OperationProbeFailure::NoViableOperation);
    }
    for (size_t i = 0; i < arguments.size(); ++i) {
        OperationProbe parameter = probe_implicit_conversion(
            arguments[i], payload->parameters[i + 1]);
        if (!merge(parameter)) {
            return fail(result.failure);
        }
    }
    for (size_t i = arguments.size(); i < visible_parameters; ++i) {
        if (!callable_default_argument(selected, i) ||
            !default_argument_replay_callback_) {
            return fail(OperationProbeFailure::NoViableOperation);
        }
        ExprResult default_argument =
            default_argument_replay_callback_(selected, i, SrcLoc());
        if (default_argument.has_error) {
            return fail(OperationProbeFailure::NoViableOperation);
        }
        bool dependent = false;
        result.nothrow = result.nothrow &&
            !expression_potentially_throws(default_argument, &dependent) &&
            !dependent;
        result.trivial = false;
    }
    if (!operation_probe_require_public_destructor(result, target_type)) {
        return fail(result.failure);
    }
    result.selected = selected;
    return result;
}

} // namespace aburi::collect
