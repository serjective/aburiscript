#include "collect.h"
#include "collect_template_state.h"

#include <algorithm>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>

namespace aburi::collect {

cir::TypeId Session::rebuild_function_result(cir::TypeId function_type,
                                             cir::TypeRef result) {
    if (!file_.valid(function_type)) {
        return function_type;
    }
    cir::TypeId resolved = file_.resolved_type(function_type);
    const auto* function = file_.valid(resolved)
        ? std::get_if<cir::FunctionTypePayload>(&file_.type_payload(resolved))
        : nullptr;
    if (!function) {
        return function_type;
    }
    return this->function_type(result,
                               function->parameters,
                               function->is_variadic,
                               function->has_prototype,
                               function->member_is_const,
                               function->exception_spec,
                               function->parameter_pack_flags,
                               function->member_ref_qualifier,
                               function->member_is_volatile);
}

cir::PlaceholderResultFactId Session::register_placeholder_result(
    cir::EntityId entity,
    cir::TypeId declared_function_type,
    const cir::Binding* previous,
    SrcLoc loc) {
    cir::TypeRef return_pattern;
    if (!entity.valid() || !file_.valid(entity) ||
        !function_has_placeholder_return(declared_function_type,
                                         &return_pattern)) {
        return {};
    }
    if (file_.valid(file_.entity(entity).placeholder_result)) {
        return file_.entity(entity).placeholder_result;
    }

    cir::PlaceholderResultFactId shared;

    if (previous && !file_.template_specialization(entity)) {
        for (auto it = previous->entities.rbegin();
             it != previous->entities.rend(); ++it) {
            cir::EntityId prior = *it;
            if (prior == entity || !prior.valid() || !file_.valid(prior)) {
                continue;
            }
            cir::TypeId prior_declared_type = file_.entity(prior).type;
            cir::PlaceholderResultFactId prior_fact_id =
                file_.entity(prior).placeholder_result;
            if (file_.valid(prior_fact_id)) {
                prior_declared_type =
                    file_.placeholder_result_fact(prior_fact_id)
                        .declared_function_type;
            }
            if (!function_signatures_match(prior_declared_type,
                                           declared_function_type) ||
                !types_compatible(file_.type_ref(prior_declared_type),
                                  file_.type_ref(declared_function_type))) {
                continue;
            }
            if (!file_.valid(prior_fact_id)) {
                cir::TypeRef prior_pattern;
                if (!function_has_placeholder_return(prior_declared_type,
                                                     &prior_pattern)) {
                    continue;
                }
                cir::PlaceholderResultFact prior_fact;
                prior_fact.declared_function_type = prior_declared_type;
                prior_fact.declared_return_pattern = prior_pattern;
                prior_fact.declaration_loc = file_.entity(prior).loc;
                prior_fact_id = file_.add_placeholder_result_fact(
                    std::move(prior_fact));
                file_.entity_mut(prior).placeholder_result = prior_fact_id;
            }
            shared = prior_fact_id;
            break;
        }
    }

    if (!shared.valid()) {
        cir::PlaceholderResultFact fact;
        fact.declared_function_type = declared_function_type;
        fact.declared_return_pattern = return_pattern;
        fact.declaration_loc = loc;
        shared = file_.add_placeholder_result_fact(std::move(fact));
    }
    file_.entity_mut(entity).placeholder_result = shared;
    const cir::PlaceholderResultFact& shared_fact =
        file_.placeholder_result_fact(shared);
    if (shared_fact.state == cir::PlaceholderResultState::Complete &&
        shared_fact.result.type.valid()) {
        file_.entity_mut(entity).type = rebuild_function_result(
            declared_function_type, shared_fact.result);
    }
    return shared;
}

void Session::begin_function_return_deduction(cir::EntityId fn_entity,
                                              cir::TypeId declared_type,
                                              SrcLoc loc) {
    cir::PlaceholderResultFactId fact_id =
        register_placeholder_result(fn_entity, declared_type, nullptr, loc);
    if (file_.valid(fact_id)) {
        cir::PlaceholderResultFact& fact =
            file_.placeholder_result_fact_mut(fact_id);
        fact.state = cir::PlaceholderResultState::Deducing;
        fact.candidate = {};
        fact.result = {};
        fact.defining_entity = fn_entity;
        fact.first_return_loc = {};
        fact.conflict_diagnosed = false;
    }
    current_result_type_ = {};
    deduce_return_type_ = true;
}

cir::TypeRef Session::deduce_placeholder_return_candidate(
    const cir::PlaceholderResultFact& fact,
    const ExprResult* operand,
    SrcLoc loc,
    bool* deferred_pattern_candidate) {
    if (deferred_pattern_candidate) {
        *deferred_pattern_candidate = false;
    }
    cir::TypeId void_type = file_.builtin_type(cir::BuiltinTypeKind::Void);
    if (!operand) {
        cir::TypeId pattern = file_.resolved_type(
            fact.declared_return_pattern.type);
        if (!file_.valid(pattern) ||
            file_.type(pattern).kind != cir::TypeKind::Auto) {
            report_error("a decorated placeholder return type cannot be "
                         "deduced from void",
                         loc);
            return {};
        }
        return file_.type_ref(void_type);
    }
    if (operand->has_error) {
        return {};
    }
    if (operand->category == ValueCategory::InitList || operand->init_list) {
        report_error("a function with a deduced return type cannot return "
                     "an initializer list",
                     loc);
        return {};
    }
    if (!operand->type.valid()) {
        return {};
    }

    ExprResult deduction_operand = *operand;
    if (lang_opts_.is_cxx_mode()) {
        ImplicitMoveEligibility move = classify_implicit_move_operand(
            deduction_operand, ImplicitMoveContext::Return);
        if (move.eligible) {
            deduction_operand.category = ValueCategory::XValue;
        }
    }

    cir::TypeRef pattern = fact.declared_return_pattern;
    cir::TypeId resolved_pattern = file_.resolved_type(pattern.type);
    if (!file_.valid(resolved_pattern)) {
        return {};
    }
    const cir::Type& type = file_.type(resolved_pattern);
    const auto* auto_payload = type.kind == cir::TypeKind::Auto
        ? std::get_if<cir::AutoTypePayload>(
              &file_.type_payload(resolved_pattern))
        : nullptr;
    if (auto_payload &&
        auto_payload->flavor == cir::AutoTypeFlavor::DecltypeAuto) {
        return resolve_decltype_expr_type(
            deduction_operand,
            deduction_operand.unparenthesized_id_or_member,
            loc);
    }

    if (is_void_type(deduction_operand.type) &&
        type.kind != cir::TypeKind::Auto) {
        report_error("a decorated placeholder return type cannot be deduced "
                     "from void",
                     loc);
        return {};
    }
    cir::TypeId deduced = deduce_auto_type(pattern.type,
                                           deduction_operand,
                                           loc);
    if (!deduced.valid()) {
        if (collecting_pattern() &&
            expr_is_dependent(deduction_operand)) {
            if (deferred_pattern_candidate) {
                *deferred_pattern_candidate = true;
            }
            return {};
        }
        report_error("cannot deduce the function return type from this "
                     "return operand",
                     loc);
        return {};
    }
    cir::TypeRef result = file_.type_ref(deduced);
    result.qualifiers = static_cast<uint8_t>(result.qualifiers |
                                             pattern.qualifiers);
    if (result.memory_space == cir::MemorySpace::Default) {
        result.memory_space = pattern.memory_space;
    }
    return result;
}

void Session::publish_placeholder_result(
    cir::PlaceholderResultFactId fact_id,
    cir::TypeRef result,
    SrcLoc loc,
    bool final) {
    if (!file_.valid(fact_id) || !result.type.valid()) {
        return;
    }
    cir::PlaceholderResultFact& fact =
        file_.placeholder_result_fact_mut(fact_id);
    fact.result = result;
    if (final) {
        fact.state = cir::PlaceholderResultState::Complete;
    }

    for (cir::EntityId candidate : file_.entity_ids()) {
        if (file_.entity(candidate).placeholder_result != fact_id) {
            continue;
        }
        cir::TypeId rebuilt = rebuild_function_result(
            fact.declared_function_type, result);
        file_.entity_mut(candidate).type = rebuilt;

        if (file_.method_fact(candidate)) {
            cir::EntityId record = file_.entity(candidate).parent;
            if (const cir::RecordFacts* facts = file_.record_facts(record)) {
                cir::RecordFacts updated = *facts;
                for (cir::RecordMethodFact& method : updated.methods) {
                    if (method.entity == candidate) {
                        method.type = file_.type_ref(rebuild_function_result(
                            method.type.type, result));
                        break;
                    }
                }
                file_.set_record_facts(record, std::move(updated));
            }
        }
    }

    if (file_.valid(current_function_) &&
        file_.function(current_function_).entity.valid() &&
        file_.entity(file_.function(current_function_).entity)
                .placeholder_result == fact_id) {
        cir::Function& function = file_.function_mut(current_function_);
        function.type = rebuild_function_result(
            fact.declared_function_type, result);
        function.result_type = result.type;
        current_result_type_ = result.type;
    }
    (void)loc;
}

bool Session::record_placeholder_return(const ExprResult* operand,
                                        SrcLoc loc,
                                        bool* deferred_pattern_candidate) {
    if (deferred_pattern_candidate) {
        *deferred_pattern_candidate = false;
    }
    if (!deduce_return_type_ || !file_.valid(current_function_)) {
        return true;
    }

    if (in_discarded_statement_validation()) {
        return true;
    }
    cir::EntityId entity = file_.function(current_function_).entity;
    if (!entity.valid() || !file_.valid(entity)) {
        return false;
    }
    cir::PlaceholderResultFactId fact_id =
        file_.entity(entity).placeholder_result;
    if (!file_.valid(fact_id)) {

        if (!current_result_type_.valid()) {
            current_result_type_ = operand && operand->type.valid()
                ? operand->type
                : file_.builtin_type(cir::BuiltinTypeKind::Void);
        }
        return true;
    }
    cir::PlaceholderResultFact& fact =
        file_.placeholder_result_fact_mut(fact_id);
    cir::TypeRef candidate = deduce_placeholder_return_candidate(
        fact, operand, loc, deferred_pattern_candidate);
    if (!candidate.type.valid() ||
        candidate.type == file_.unknown_type()) {
        if (deferred_pattern_candidate &&
            *deferred_pattern_candidate) {

            if (fact.first_return_loc.isInvalid()) {
                fact.first_return_loc = loc;
            }
            bump_pattern_taint();
            return true;
        }
        fact.state = cir::PlaceholderResultState::Failed;
        return false;
    }
    if (!fact.candidate.type.valid()) {
        fact.candidate = candidate;
        fact.first_return_loc = loc;
        publish_placeholder_result(fact_id, candidate, loc,
                                   /*final=*/false);
        return true;
    }
    bool same = file_.resolved_type(fact.candidate.type) ==
                    file_.resolved_type(candidate.type) &&
                fact.candidate.qualifiers == candidate.qualifiers &&
                fact.candidate.memory_space == candidate.memory_space;
    if (collecting_pattern()) {

        if (!same) {
            if (deferred_pattern_candidate) {
                *deferred_pattern_candidate = true;
            }

            bump_pattern_taint();
        }
        current_result_type_ = fact.candidate.type;
        return true;
    }
    if (!same) {
        if (!fact.conflict_diagnosed) {
            report_error("inconsistent deduction for placeholder function "
                         "return type: '" + file_.format_type(candidate) +
                             "' does not match '" +
                             file_.format_type(fact.candidate) + "'",
                         loc);
            report_note("previous return type was deduced here",
                        fact.first_return_loc);
            fact.conflict_diagnosed = true;
        }
        fact.state = cir::PlaceholderResultState::Failed;
        return false;
    }
    current_result_type_ = fact.candidate.type;
    return true;
}

cir::TypeId Session::resolve_deduced_return_type(cir::EntityId fn_entity,
                                                 cir::TypeId declared_type,
                                                 SrcLoc loc,
                                                 bool pattern_only) {
    cir::PlaceholderResultFactId fact_id = fn_entity.valid() &&
                                                   file_.valid(fn_entity)
        ? file_.entity(fn_entity).placeholder_result
        : cir::PlaceholderResultFactId{};
    if (!file_.valid(fact_id)) {
        fact_id = register_placeholder_result(fn_entity, declared_type,
                                              nullptr, loc);
    }
    if (!file_.valid(fact_id)) {
        return declared_type;
    }
    cir::PlaceholderResultFact& fact =
        file_.placeholder_result_fact_mut(fact_id);
    bool has_deferred_pattern_return =
        pattern_only && !fact.first_return_loc.isInvalid() &&
        !fact.candidate.type.valid();
    if (fact.state != cir::PlaceholderResultState::Failed &&
        !fact.candidate.type.valid() && !has_deferred_pattern_return) {
        (void)record_placeholder_return(nullptr, loc);
    }
    cir::TypeRef result = fact.candidate;
    if (!result.type.valid()) {
        result = file_.type_ref(file_.unknown_type());
    }
    cir::TypeId rebuilt = rebuild_function_result(
        fact.declared_function_type, result);

    if (pattern_only) {
        if (file_.valid(current_function_)) {
            cir::Function& function = file_.function_mut(current_function_);
            function.type = rebuilt;
            function.result_type = result.type;
        }
        current_result_type_ = result.type;
        fact.state = cir::PlaceholderResultState::Undeduced;
        fact.candidate = {};
        fact.result = {};
        fact.defining_entity = {};
        deduce_return_type_ = false;
        return rebuilt;
    }

    if (fact.state != cir::PlaceholderResultState::Failed) {
        publish_placeholder_result(fact_id, result, loc, /*final=*/true);
    } else {
        cir::TypeRef recovery = fact.candidate.type.valid()
            ? fact.candidate
            : file_.type_ref(
                  file_.builtin_type(cir::BuiltinTypeKind::Void));
        publish_placeholder_result(fact_id, recovery, loc,
                                   /*final=*/false);
        fact.state = cir::PlaceholderResultState::Failed;
        rebuilt = rebuild_function_result(
            fact.declared_function_type, recovery);
    }
    deduce_return_type_ = false;
    return rebuilt;
}

bool Session::lambda_capture_source_usable(cir::EntityId entity) const {
    if (lambda_stack_.empty() || !entity.valid() || !file_.valid(entity)) {
        return false;
    }

    for (const LambdaFrame& frame : lambda_stack_) {
        if (std::any_of(frame.captures.begin(), frame.captures.end(),
                        [&](const LambdaCapture& capture) {
                            return capture.field_entity == entity;
                        })) {
            return true;
        }
    }
    cir::EntityId owner = file_.entity(entity).owning_function;
    if (!owner.valid() || is_default_argument_local(entity)) {
        return false;
    }
    if (owner == lambda_stack_.front().capture_origin_function) {
        return true;
    }
    return std::any_of(
        lambda_stack_.begin(), lambda_stack_.end(),
        [&](const LambdaFrame& frame) { return frame.call_operator == owner; });
}

bool Session::note_potential_lambda_capture(cir::EntityId entity,
                                            SrcLoc loc) {
    if (lambda_stack_.empty() ||
        (in_unevaluated_operand() && !in_typeid_capture_discovery()) ||
        lambda_stack_.back().capture_default == LambdaCaptureDefault::None ||
        !lambda_capture_source_usable(entity)) {
        return true;
    }
    return add_lambda_capture(
               entity,
               lambda_stack_.back().capture_default ==
                   LambdaCaptureDefault::ByRef,
               loc) != SIZE_MAX;
}

size_t Session::add_lambda_capture(cir::EntityId source,
                                   bool by_ref,
                                   SrcLoc loc) {
    uint64_t key = static_cast<uint64_t>(source.index);
    const cir::Entity& entity = file_.entity(source);
    std::string source_name = entity.name.valid()
        ? std::string(file_.name(entity.name))
        : std::string(".capture");
    if (!lambda_capture_source_usable(source)) {
        report_error("local entity '" + source_name +
                         "' is not odr-usable in this capture context",
                     loc);
        return SIZE_MAX;
    }

    cir::TypeRef object_ref = file_.entity_type_ref(source);
    cir::TypeId resolved = file_.resolved_type(object_ref.type);
    if (is_reference_type(resolved)) {
        object_ref = file_.reference_referred_ref(resolved);
    }
    cir::TypeId object_type = object_ref.type;
    uint8_t source_qualifiers = object_ref.qualifiers;

    size_t result = SIZE_MAX;
    bool chained_const = false;
    for (size_t i = 0; i < lambda_stack_.size(); ++i) {
        LambdaFrame& frame = lambda_stack_[i];
        auto found = frame.capture_memo.find(key);
        if (found != frame.capture_memo.end()) {
            result = found->second;
            if (!frame.captures[result].by_ref && !frame.is_mutable) {
                chained_const = true;
            }
            continue;
        }

        if (entity.owning_function == frame.call_operator) {
            continue;
        }
        if (source.index >= frame.entity_watermark) {
            continue;
        }
        bool innermost = i + 1 == lambda_stack_.size();
        bool frame_by_ref = innermost
            ? by_ref
            : frame.capture_default == LambdaCaptureDefault::ByRef;
        if (!innermost &&
            frame.capture_default == LambdaCaptureDefault::None) {
            report_error("variable '" + source_name +
                             "' cannot be implicitly captured by an "
                             "enclosing lambda with no capture-default",
                         loc);
            return SIZE_MAX;
        }
        cir::TypeRef referred = object_ref;
        if (chained_const) {
            referred.qualifiers |= cir::QualConst;
        }
        cir::TypeId field_type = frame_by_ref
            ? file_.reference_type(referred, cir::ReferenceKind::LValue)
            : object_type;
        cir::EntityId field = builder_.add_entity(cir::EntityKind::Field,
                                                  source_name,
                                                  field_type,
                                                  frame.closure_record,
                                                  loc);
        if (!frame_by_ref) {

            uint8_t qualifiers = source_qualifiers;
            if (chained_const) {
                qualifiers |= cir::QualConst;
            }
            file_.entity_mut(field).qualifiers = qualifiers;
            if (!frame.is_mutable) {
                chained_const = true;
            }
        }
        LambdaCapture capture;
        capture.kind = LambdaCaptureKind::Entity;
        capture.source_entity = source;
        capture.field_entity = field;
        capture.field_type = field_type;
        capture.by_ref = frame_by_ref;
        capture.loc = loc;
        frame.captures.push_back(std::move(capture));
        result = frame.captures.size() - 1;
        frame.capture_memo[key] = result;
        frame.capture_memo[static_cast<uint64_t>(field.index)] = result;
    }
    return result;
}

size_t Session::add_lambda_this_capture(bool object, bool implicit, SrcLoc loc) {
    LambdaFrame& frame = lambda_stack_.back();
    if (frame.this_capture != SIZE_MAX) {
        return frame.this_capture;
    }

    const LambdaFrame& outermost = lambda_stack_.front();
    if (!outermost.enclosing_this_place.valid() ||
        !outermost.enclosing_member_record.valid()) {
        report_error("'this' cannot be captured outside a non-static member "
                     "function",
                     loc);
        return SIZE_MAX;
    }
    if (implicit &&
        frame.capture_default == LambdaCaptureDefault::None) {
        report_error("'this' cannot be implicitly captured in a lambda with "
                     "no capture-default",
                     loc);
        return SIZE_MAX;
    }
    if (implicit && frame.capture_default == LambdaCaptureDefault::ByCopy) {
        report_warning(WarningId::DeprecatedDeclarations,
                       "implicit capture of 'this' with a capture-default "
                       "of '=' is deprecated",
                       loc);
    }
    if (object &&
        lambda_stack_.size() > 1) {
        report_error("'*this' capture inside a nested lambda is not "
                     "supported yet",
                     loc);
        return SIZE_MAX;
    }

    cir::TypeId field_type;
    if (object) {
        field_type = file_.entity(outermost.enclosing_member_record).type;
    } else {
        field_type = object_type_from_place(outermost.enclosing_this_place);
    }
    cir::EntityId field = builder_.add_entity(cir::EntityKind::Field,
                                              ".this",
                                              field_type,
                                              frame.closure_record,
                                              loc);
    LambdaCapture capture;
    capture.kind = object ? LambdaCaptureKind::ThisObject
                          : LambdaCaptureKind::ThisPointer;
    capture.field_entity = field;
    capture.field_type = field_type;
    capture.loc = loc;
    frame.captures.push_back(std::move(capture));
    frame.this_capture = frame.captures.size() - 1;
    return frame.this_capture;
}

ExprResult Session::lambda_enclosing_this_value(SrcLoc loc) {
    size_t index = add_lambda_this_capture(/*object=*/false,
                                           /*implicit=*/true,
                                           loc);
    ExprResult result;
    LambdaFrame& frame = lambda_stack_.back();
    if (index == SIZE_MAX) {

        if (frame.this_capture == SIZE_MAX) {
            result.has_error = true;
            result.type = builder_.unknown_type();
            result.category = ValueCategory::PrValue;
            return result;
        }
        index = frame.this_capture;
    }
    const LambdaCapture& capture = frame.captures[index];

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.lambda.this");
    cir::InstId this_value = builder_.lvalue_to_rvalue(current_this_place_, loc);
    cir::InstId object_place = builder_.deref(this_value, loc);
    cir::InstId field_place = builder_.field_addr(
        object_place, capture.field_entity, capture.field_type, loc);
    cir::InstId value{};
    if (capture.kind == LambdaCaptureKind::ThisObject) {
        value = builder_.addr_of(field_place, loc);
    } else {
        value = builder_.lvalue_to_rvalue(field_place, loc);
    }
    result.fragment = finish_fragment_block(block, previous);
    result.value = value;
    result.type = file_.inst(value).result_type;
    result.category = ValueCategory::PrValue;
    return result;
}

ExprResult Session::lambda_capture_access(ExprResult result,
                                          std::string_view name,
                                          SrcLoc loc) {
    LambdaFrame& frame = lambda_stack_.back();
    uint64_t key = static_cast<uint64_t>(result.entity.index);
    size_t index = SIZE_MAX;
    auto found = frame.capture_memo.find(key);
    if (found != frame.capture_memo.end()) {
        index = found->second;
    } else if (frame.capture_default == LambdaCaptureDefault::None) {
        report_error("variable '" + std::string(name) +
                         "' cannot be implicitly captured in a lambda with "
                         "no capture-default",
                     loc);
        result.has_error = true;
        result.type = builder_.unknown_type();
        result.category = ValueCategory::PrValue;
        return result;
    } else {
        index = add_lambda_capture(
            result.entity,
            frame.capture_default == LambdaCaptureDefault::ByRef,
            loc);
    }
    if (index == SIZE_MAX) {
        result.has_error = true;
        result.type = builder_.unknown_type();
        result.category = ValueCategory::PrValue;
        return result;
    }

    const LambdaCapture& capture = lambda_stack_.back().captures[index];
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.lambda.capture");
    cir::InstId this_value = builder_.lvalue_to_rvalue(current_this_place_, loc);
    cir::InstId object_place = builder_.deref(this_value, loc);
    cir::InstId field_place = builder_.field_addr(
        object_place, capture.field_entity, capture.field_type, loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);

    result.fragment = chain(std::move(result.fragment), std::move(fragment), loc);
    result.place = field_place;
    result.entity = capture.field_entity;
    result.type = capture.field_type;
    result.category = ValueCategory::LValue;

    if (is_reference_type(result.type)) {
        result = deref_reference_lvalue(std::move(result), loc);
    }
    return result;
}

cir::InstId Session::lambda_capture_source_place(const LambdaCapture& capture,
                                                 SrcLoc loc) {

    if (!lambda_stack_.empty()) {
        LambdaFrame& outer = lambda_stack_.back();
        auto found = outer.capture_memo.find(
            static_cast<uint64_t>(capture.source_entity.index));
        if (found != outer.capture_memo.end()) {
            const LambdaCapture& outer_capture = outer.captures[found->second];
            cir::InstId this_value =
                builder_.lvalue_to_rvalue(current_this_place_, loc);
            cir::InstId object_place = builder_.deref(this_value, loc);
            cir::InstId field_place = builder_.field_addr(
                object_place, outer_capture.field_entity,
                outer_capture.field_type, loc);
            if (is_reference_type(file_.resolved_type(outer_capture.field_type))) {
                cir::InstId reference_value =
                    builder_.lvalue_to_rvalue(field_place, loc);
                return builder_.deref(reference_value, loc);
            }
            return field_place;
        }
    }
    const cir::Entity& source = file_.entity(capture.source_entity);
    if (source.kind == cir::EntityKind::StructuredBinding) {
        return structured_binding_projection_place(capture.source_entity, loc);
    }
    cir::InstId source_place =
        builder_.local_place(capture.source_entity, source.type, loc);
    if (is_reference_type(file_.resolved_type(source.type))) {
        cir::InstId reference_value =
            builder_.lvalue_to_rvalue(source_place, loc);
        source_place = builder_.deref(reference_value, loc);
    }
    return source_place;
}

LambdaClosureStart Session::begin_lambda_closure(
    std::vector<ParamInput> params,
    cir::TypeId trailing_return_type,
    LambdaSpecifiers specifiers,
    LambdaCaptureDefault capture_default,
    std::vector<LambdaCaptureItem> explicit_captures,
    SrcLoc loc) {
    LambdaClosureStart start;
    start.index = ++lambda_closure_counter_;
    start.loc = loc;
    start.is_mutable = specifiers.is_mutable;
    start.exception_spec = std::move(specifiers.exception_spec);
    start.is_static = specifiers.is_static;
    start.is_constexpr = specifiers.is_constexpr;
    start.is_consteval = specifiers.is_consteval;
    start.deduced_return = !trailing_return_type.valid();
    start.has_lambda_capture =
        capture_default != LambdaCaptureDefault::None ||
        !explicit_captures.empty();

    if (start.is_static &&
        (capture_default != LambdaCaptureDefault::None ||
         !explicit_captures.empty())) {
        report_error("a static lambda cannot have captures", loc);
        start.has_error = true;
        capture_default = LambdaCaptureDefault::None;
        explicit_captures.clear();
    }
    if (start.is_static && start.is_mutable) {
        report_error("a lambda cannot be both 'static' and 'mutable'", loc);
        start.has_error = true;
        start.is_mutable = false;
    }

    bump_pattern_taint();

    uint32_t watermark = file_.entity_table_size();

    std::string tag = ".lambda." + std::to_string(start.index);
    start.record =
        create_record_tag(cir::RecordKind::Struct, tag, loc, /*bind_tag=*/false);
    if (cir::RecordFacts* facts = file_.record_facts(start.record.entity)) {
        facts->is_lambda_closure = true;
        facts->lambda_has_capture = start.has_lambda_capture;
    }

    cir::TypeId return_type = trailing_return_type.valid()
        ? trailing_return_type
        : file_.auto_type(cir::AutoTypeFlavor::Cxx);
    std::vector<cir::TypeRef> param_types;
    std::vector<uint8_t> parameter_pack_flags;
    bool has_parameter_pack = false;
    param_types.reserve(params.size());
    parameter_pack_flags.reserve(params.size());
    for (const ParamInput& param : params) {
        param_types.push_back(param.type);
        uint8_t pack_flag = param.is_parameter_pack ? 1 : 0;
        parameter_pack_flags.push_back(pack_flag);
        has_parameter_pack = has_parameter_pack || pack_flag != 0;
    }
    if (!has_parameter_pack) {
        parameter_pack_flags.clear();
    }
    start.declared_fn_type = function_type(
        file_.type_ref(return_type), param_types,
        /*is_variadic=*/false, /*has_prototype=*/true,
        /*member_is_const=*/!start.is_mutable && !start.is_static,
        start.exception_spec,
        parameter_pack_flags);
    cir::TypeId entity_type = start.is_static
        ? start.declared_fn_type
        : member_function_type_with_this(start.record.type,
                                         start.declared_fn_type);

    DeclFlags operator_flags;
    operator_flags.is_inline = true;

    operator_flags.is_constexpr = true;
    operator_flags.is_consteval = start.is_consteval;

    start.call_operator = builder_.add_entity(cir::EntityKind::Method,
                                              tag + ".op",
                                              entity_type,
                                              start.record.entity,
                                              loc,
                                              cir::StorageDuration::None,
                                              cir::MemorySpace::Default,
                                              operator_flags.to_cir());
    apply_attributes(start.call_operator,
                     AttributeTarget::Function,
                     specifiers.attrs,
                     loc);
    file_.entity_mut(start.call_operator).operator_function = {
        .kind = cir::OperatorFunctionKind::Symbolic,
        .spelling = cir::OperatorFunctionSpelling::Call,
    };
    cir::ClosureIdentityFact closure_identity;
    closure_identity.source_loc = loc;
    closure_identity.key_loc = loc;
    closure_identity.lexical_owner = current_function_entity().valid()
        ? current_function_entity()
        : current_member_record_;
    closure_identity.record = start.record.entity;
    closure_identity.type = file_.type_ref(start.record.type);
    closure_identity.call_operator = start.call_operator;
    if (current_function_entity().valid()) {
        closure_identity.abi_context =
            cir::ClosureAbiContextKind::FunctionBody;
    } else if (!closure_abi_context_stack_.empty()) {
        const ActiveClosureAbiContext& context =
            closure_abi_context_stack_.back();
        closure_identity.abi_context = context.kind;
        closure_identity.abi_context_name = context.name;
        closure_identity.abi_context_decl = context.declaration_context;
    } else {
        closure_identity.abi_context =
            cir::ClosureAbiContextKind::TranslationUnit;
    }
    closure_identity.is_structural = !start.has_lambda_capture;
    start.closure_identity =
        file_.add_closure_identity(std::move(closure_identity));
    if (cir::RecordFacts* facts = file_.record_facts(start.record.entity)) {
        facts->closure_identity = start.closure_identity;
    }
    start.params = std::move(params);

    if (start.is_static) {
        if (cir::RecordFacts* facts = file_.record_facts(start.record.entity)) {
            cir::RecordMethodFact fact;
            fact.name = file_.intern_name("operator()");
            fact.entity = start.call_operator;
            fact.type = file_.type_ref(start.declared_fn_type);
            fact.is_static = true;
            facts->methods.push_back(std::move(fact));
        }
    }

    LambdaFrame frame;
    frame.closure_record = start.record.entity;
    frame.call_operator = start.call_operator;
    frame.capture_origin_function = lambda_stack_.empty()
        ? current_function_entity()
        : lambda_stack_.front().capture_origin_function;
    frame.entity_watermark = watermark;
    frame.capture_default = capture_default;
    frame.is_mutable = start.is_mutable;

    frame.enclosing_this_place =
        lambda_stack_.empty() ? current_this_place_
                              : lambda_stack_.front().enclosing_this_place;
    frame.enclosing_member_record =
        lambda_stack_.empty() ? current_member_record_
                              : lambda_stack_.front().enclosing_member_record;
    frame.closure_index = start.index;
    lambda_stack_.push_back(std::move(frame));

    register_explicit_lambda_captures(start, std::move(explicit_captures), loc);

    lambda_context_stack_.push_back(
        save_function_context(/*preserve_lambda_context=*/true));

    FunctionDeclStart fn =
        begin_member_function(start.call_operator, start.params, loc);
    if (fn.decl.has_error) {
        start.has_error = true;
    }

    if (!tstate().function_parameter_pack_scope_stack_.empty()) {
        const auto& saved_packs =
            tstate().function_parameter_pack_scope_stack_.back();
        tstate().function_parameter_pack_names_ = saved_packs.names;
        tstate().function_parameter_pack_elements_ = saved_packs.elements;
        tstate().function_parameter_pack_template_indices_ =
            saved_packs.template_pack_indices;
    }
    if (start.deduced_return) {
        begin_function_return_deduction(start.call_operator,
                                        entity_type,
                                        loc);
    }
    return start;
}

void Session::register_explicit_lambda_captures(
    LambdaClosureStart& start,
    std::vector<LambdaCaptureItem> explicit_captures,
    SrcLoc loc) {
    (void)loc;
    cir::DeclContextId record_context =
        file_.entity(start.record.entity).semantic_context;

    auto register_init_capture = [&](const std::string& capture_name,
                                     const std::string& field_spelling,
                                     bool by_ref,
                                     ExprResult init,
                                     bool bind_name,
                                     SrcLoc item_loc) -> cir::EntityId {
        for (const ParamInput& param : start.params) {
            if (param.name == capture_name) {
                report_error("init-capture '" + capture_name +
                                 "' has the same name as a lambda "
                                 "parameter",
                             item_loc);
                return cir::EntityId{};
            }
        }
        if (!init.type.valid() || init.has_error) {
            report_error("cannot deduce the type of init-capture '" +
                             capture_name + "'",
                         item_loc);
            return cir::EntityId{};
        }
        LambdaCapture capture;
        capture.kind = LambdaCaptureKind::Init;
        capture.by_ref = by_ref;
        capture.loc = item_loc;
        cir::TypeId object_type = file_.resolved_type(init.type);
        if (by_ref) {

            if (init.category != ValueCategory::LValue ||
                !init.place.valid()) {
                report_error("by-reference init-capture '" + capture_name +
                         "' must bind to an lvalue",
                         item_loc);
                return cir::EntityId{};
            }
            capture.field_type = file_.reference_type(
                file_.type_ref(object_type), cir::ReferenceKind::LValue);
            capture.init_place = init.place;
            capture.init_fragment = std::move(init.fragment);
        } else if (file_.valid(object_type) &&
                   file_.type(object_type).kind == cir::TypeKind::Record) {
            capture.field_type = object_type;
            if (init.category == ValueCategory::LValue &&
                init.place.valid()) {
                capture.init_place = init.place;
            } else {
                capture.init_value = init.value;
            }
            capture.init_lifetimes =
                std::move(init.materialized_lifetimes);
            capture.init_fragment = std::move(init.fragment);
        } else {

            if (file_.valid(object_type) &&
                file_.type(object_type).kind == cir::TypeKind::Array) {
                object_type =
                pointer_type(file_.array_element_ref(object_type));
            } else if (file_.valid(object_type) &&
                   file_.type(object_type).kind ==
                       cir::TypeKind::Function) {
                object_type =
                pointer_type(file_.type_ref(object_type));
            }
            ExprResult value = convert_to(std::move(init), object_type,
                                  UseContext::Init, item_loc);

            bool deferred_dependent = !value.has_error &&
                (expr_is_dependent(value) ||
                 (file_.valid(object_type) &&
                  is_dependent_type(object_type)));
            if ((value.has_error || !value.value.valid()) &&
                !deferred_dependent) {
                report_error("cannot initialize init-capture '" +
                         capture_name + "'",
                         item_loc);
                return cir::EntityId{};
            }
            if (deferred_dependent) {

                file_.entity_mut(start.record.entity).is_template_pattern =
                    true;
            }
            capture.field_type = object_type;
            capture.init_value = value.value;
            capture.init_lifetimes =
                std::move(value.materialized_lifetimes);
            capture.init_fragment = std::move(value.fragment);
        }
        cir::EntityId field = builder_.add_entity(cir::EntityKind::Field,
                                                  field_spelling,
                                                  capture.field_type,
                                                  start.record.entity,
                                                  item_loc);
        capture.field_entity = field;

        if (bind_name && record_context.valid()) {
            file_.bind_entity(record_context,
                              file_.intern_name(capture_name),
                              cir::LookupNamespace::Ordinary,
                              field,
                              file_.type_ref(capture.field_type),
                              false,
                              false,
                              true,
                              {},
                              item_loc);
        }
        LambdaFrame& frame = lambda_stack_.back();
        frame.captures.push_back(std::move(capture));

        frame.capture_memo[static_cast<uint64_t>(field.index)] =
            frame.captures.size() - 1;
        return field;
    };

    for (LambdaCaptureItem& item : explicit_captures) {
        if (item.is_init_pack) {

            if (item.pack_inits.empty()) {
                if (!in_template_definition()) {
                    report_error("init-capture pack '" + item.name +
                                     "' has no expansion elements",
                                 item.loc);
                    start.has_error = true;
                } else {

                    tstate().function_parameter_pack_names_.insert(item.name);
                }
                continue;
            }
            std::vector<FunctionParameterPackElement> elements;
            bool pack_error = false;
            for (ExprResult& init : item.pack_inits) {

                cir::EntityId field = register_init_capture(
                    item.name,
                    item.name + "#" + std::to_string(elements.size()),
                    item.by_ref, std::move(init),
                    /*bind_name=*/false, item.loc);
                if (!field.valid()) {
                    pack_error = true;
                    break;
                }
                FunctionParameterPackElement element;
                element.entity = field;
                element.type =
                    lambda_stack_.back().captures.back().field_type;
                element.loc = item.loc;
                elements.push_back(element);
            }
            if (pack_error) {
                start.has_error = true;
                continue;
            }

            tstate().function_parameter_pack_names_.insert(item.name);
            tstate().function_parameter_pack_elements_[item.name] =
                std::move(elements);
            continue;
        }
        if (item.is_pack) {

            auto found =
                tstate().function_parameter_pack_elements_.find(item.name);
            if (found == tstate().function_parameter_pack_elements_.end()) {
                if (!in_template_definition()) {
                    report_error("'" + item.name +
                                     "' does not name a function parameter "
                                     "pack",
                                 item.loc);
                    start.has_error = true;
                }
                continue;
            }
            for (const FunctionParameterPackElement& element : found->second) {
                if (add_lambda_capture(element.entity, item.by_ref,
                                       item.loc) == SIZE_MAX) {
                    start.has_error = true;
                }
            }
            continue;
        }
        if (item.is_this || item.is_star_this) {
            if (add_lambda_this_capture(item.is_star_this,
                                        /*implicit=*/false,
                                        item.loc) == SIZE_MAX) {
                start.has_error = true;
            }
            continue;
        }
        if (item.init.has_value()) {
            if (!register_init_capture(item.name, item.name, item.by_ref,
                                       std::move(*item.init),
                                       /*bind_name=*/true,
                                       item.loc)
                     .valid()) {
                start.has_error = true;
            }
            continue;
        }
        const cir::Binding* binding = lookup_ordinary_binding(item.name);
        cir::EntityId entity = binding && !binding->entities.empty()
            ? binding->entities.back()
            : cir::EntityId{};
        bool enclosing_init_capture =
            entity.valid() && file_.valid(entity) &&
            file_.entity(entity).kind == cir::EntityKind::Field &&
            lambda_capture_source_usable(entity);
        if (!entity.valid() || !file_.valid(entity) ||
            (!enclosing_init_capture &&
             file_.entity(entity).kind != cir::EntityKind::Variable &&
             file_.entity(entity).kind != cir::EntityKind::Parameter &&
             file_.entity(entity).kind !=
                 cir::EntityKind::StructuredBinding)) {
            report_error("capture '" + item.name + "' does not name a variable",
                         item.loc);
            start.has_error = true;
            continue;
        }
        const cir::Entity& record = file_.entity(entity);
        if (!enclosing_init_capture &&
            record.storage_duration != cir::StorageDuration::Automatic &&
            record.storage_duration != cir::StorageDuration::Parameter) {
            report_error("'" + item.name +
                             "' cannot be captured because it does not have "
                             "automatic storage duration",
                         item.loc);
            start.has_error = true;
            continue;
        }
        if (add_lambda_capture(entity, item.by_ref, item.loc) == SIZE_MAX) {
            start.has_error = true;
        }
    }
}

ExprResult Session::finish_lambda_closure(LambdaClosureStart start,
                                          StmtResult body,
                                          SrcLoc loc) {
    if (file_.valid(start.closure_identity)) {
        file_.closure_identity_mut(start.closure_identity).key_loc = loc;
    }

    if (start.deduced_return) {
        cir::TypeId declared_entity_type =
            file_.placeholder_result_fact(
                file_.entity(start.call_operator).placeholder_result)
                .declared_function_type;
        (void)resolve_deduced_return_type(start.call_operator,
                                          declared_entity_type,
                                          loc);
        const cir::PlaceholderResultFact& fact =
            file_.placeholder_result_fact(
                file_.entity(start.call_operator).placeholder_result);
        start.declared_fn_type = rebuild_function_result(
            start.declared_fn_type, fact.result);
    }
    if (!start.has_error) {
        finish_member_function(std::move(body), loc);
    }

    file_.entity_mut(start.call_operator).linkage = cir::LinkageKind::Internal;

    LambdaFrame frame = std::move(lambda_stack_.back());
    lambda_stack_.pop_back();
    if (!lambda_context_stack_.empty()) {
        std::unique_ptr<BlockContextState> saved =
            std::move(lambda_context_stack_.back());
        lambda_context_stack_.pop_back();
        restore_function_context(std::move(saved));
    }

    std::string tag = ".lambda." + std::to_string(start.index);
    bool captureless = frame.captures.empty();

    cir::TypeId invoker_fn_type =
        lambda_invoker_function_type(start.declared_fn_type);
    cir::TypeId fnptr_type = pointer_type(file_.type_ref(invoker_fn_type));
    cir::TypeId conversion_fn_type{};
    cir::EntityId conversion_entity{};
    if (captureless) {
        conversion_fn_type = function_type(
            file_.type_ref(fnptr_type), {},
            /*is_variadic=*/false, /*has_prototype=*/true,
            /*member_is_const=*/true);
        DeclFlags conversion_flags;
        conversion_flags.is_inline = true;
        conversion_flags.is_constexpr =
            file_.entity(start.call_operator).decl_flags.is_constexpr;
        conversion_entity = builder_.add_entity(
            cir::EntityKind::Method,
            tag + ".conv",
            member_function_type_with_this(start.record.type, conversion_fn_type),
            start.record.entity,
            loc,
            cir::StorageDuration::None,
            cir::MemorySpace::Default,
            conversion_flags.to_cir());
        file_.entity_mut(conversion_entity).operator_function = {
            .kind = cir::OperatorFunctionKind::Conversion,
            .conversion_type = file_.type_ref(fnptr_type),
        };
    }

    std::vector<RecordMethodInput> extra_methods;
    if (conversion_entity.valid()) {
        RecordMethodInput conversion;
        conversion.name = "operator " + file_.format_type(fnptr_type);
        conversion.operator_function =
            file_.entity(conversion_entity).operator_function;
        conversion.is_conversion_function = true;
        conversion.type = conversion_fn_type;
        conversion.loc = start.loc;
        conversion.flags.is_inline = true;
        conversion.flags.is_constexpr =
            file_.entity(start.call_operator).decl_flags.is_constexpr;
        conversion.precreated_entity = conversion_entity;
        extra_methods.push_back(std::move(conversion));
    }
    publish_lambda_closure(start, frame, std::move(extra_methods), loc);

    cir::EntityId invoke_entity{};
    if (!start.has_error && captureless) {
        invoke_entity = start.is_static
            ? start.call_operator
            : synthesize_lambda_invoker(start.record.type,
                                        start.call_operator,
                                        invoker_fn_type,
                                        tag + ".invoke",
                                        loc);
        if (file_.valid(start.closure_identity)) {
            cir::ClosureIdentityFact& identity =
                file_.closure_identity_mut(start.closure_identity);
            identity.invoker = invoke_entity;
            if (identity.lexical_owner.valid() && invoke_entity.valid()) {
                cir::Entity& invoker = file_.entity_mut(invoke_entity);
                invoker.linkage = file_.entity(start.record.entity).linkage;
                invoker.abi_owner = start.record.entity;
            }
        }
    }

    if (!start.has_error && invoke_entity.valid()) {
        std::unique_ptr<BlockContextState> saved = save_function_context();
        FunctionDeclStart fn =
            begin_member_function(conversion_entity, {}, loc);
        if (!fn.decl.has_error) {
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("lambda.conv");
            cir::InstId pointer =
                builder_.function_to_pointer(invoke_entity, loc);
            cir::Fragment fragment = finish_fragment_block(block, previous);
            ExprResult value;
            value.fragment = std::move(fragment);
            value.value = pointer;
            value.type = fnptr_type;
            value.category = ValueCategory::PrValue;
            StmtResult ret = collect_return_stmt(std::move(value), loc);
            finish_member_function(std::move(ret), loc);
            file_.entity_mut(conversion_entity).linkage =
                cir::LinkageKind::Internal;
        }
        restore_function_context(std::move(saved));
    }

    if (start.has_error) {
        ExprResult result;
        result.has_error = true;
        result.type = builder_.unknown_type();
        result.category = ValueCategory::PrValue;
        return result;
    }

    return materialize_lambda_closure(start, frame, loc);
}

void Session::publish_lambda_closure(LambdaClosureStart& start,
                                     const LambdaFrame& frame,
                                     std::vector<RecordMethodInput> extra_methods,
                                     SrcLoc loc) {
    std::string tag = ".lambda." + std::to_string(start.index);

    std::vector<RecordFieldInput> fields;
    fields.reserve(frame.captures.size());
    for (const LambdaCapture& capture : frame.captures) {
        RecordFieldInput field;
        const cir::Entity& field_entity = file_.entity(capture.field_entity);
        field.name = field_entity.name.valid()
            ? std::string(file_.name(field_entity.name))
            : std::string();
        field.type = capture.field_type;
        field.qualifiers = field_entity.qualifiers;
        field.lambda_capture_source = capture.source_entity;
        switch (capture.kind) {
            case LambdaCaptureKind::Entity:
                field.lambda_capture_kind =
                    cir::LambdaCaptureFieldKind::Entity;
                break;
            case LambdaCaptureKind::Init:
                field.lambda_capture_kind =
                    cir::LambdaCaptureFieldKind::Init;
                break;
            case LambdaCaptureKind::ThisPointer:
                field.lambda_capture_kind =
                    cir::LambdaCaptureFieldKind::ThisPointer;
                break;
            case LambdaCaptureKind::ThisObject:
                field.lambda_capture_kind =
                    cir::LambdaCaptureFieldKind::ThisObject;
                break;
        }
        field.loc = capture.loc;
        field.entity = capture.field_entity;
        fields.push_back(std::move(field));
    }
    RecordMethodInput call_operator;
    call_operator.name = "operator()";
    call_operator.operator_function = {
        .kind = cir::OperatorFunctionKind::Symbolic,
        .spelling = cir::OperatorFunctionSpelling::Call,
    };
    call_operator.type = start.declared_fn_type;
    call_operator.params = start.params;
    call_operator.loc = start.loc;
    call_operator.flags.is_inline = true;
    call_operator.flags.is_constexpr = true;
    call_operator.flags.is_consteval = start.is_consteval;
    call_operator.is_static = start.is_static;
    call_operator.precreated_entity = start.call_operator;
    std::vector<RecordMethodInput> methods;
    methods.push_back(std::move(call_operator));
    for (RecordMethodInput& extra : extra_methods) {
        methods.push_back(std::move(extra));
    }
    start.record = finish_record_definition(start.record,
                                            cir::RecordKind::Struct,
                                            std::move(fields),
                                            {},
                                            std::move(methods),
                                            loc);

    if (const cir::RecordFacts* facts = file_.record_facts(start.record.entity)) {
        auto reference_role = [&](cir::TypeId function_type,
                                  cir::EntityId entity) {
            const auto* payload = std::get_if<cir::FunctionTypePayload>(
                &file_.type_payload(file_.resolved_type(function_type)));
            if (!payload || payload->parameters.size() != 1) {
                return std::string("entity.") +
                       std::to_string(entity.index);
            }
            cir::TypeId parameter =
                file_.resolved_type(payload->parameters.front().type);
            if (!file_.valid(parameter)) {
                return std::string("entity.") +
                       std::to_string(entity.index);
            }
            if (file_.type(parameter).kind ==
                cir::TypeKind::LValueReference) {
                return std::string("copy");
            }
            if (file_.type(parameter).kind ==
                cir::TypeKind::RValueReference) {
                return std::string("move");
            }
            return std::string("entity.") +
                   std::to_string(entity.index);
        };
        for (const cir::RecordMethodFact& method : facts->methods) {
            if (!method.entity.valid() || !file_.valid(method.entity)) {
                continue;
            }
            cir::EntityKind member_kind = file_.entity(method.entity).kind;
            if (member_kind == cir::EntityKind::Destructor) {
                file_.entity_mut(method.entity).name =
                    file_.intern_name(tag + ".dtor");
                file_.entity_mut(method.entity).linkage =
                    cir::LinkageKind::Internal;
            } else if (member_kind == cir::EntityKind::Constructor) {
                const auto* payload = std::get_if<cir::FunctionTypePayload>(
                    &file_.type_payload(file_.resolved_type(method.type.type)));
                std::string role = payload && payload->parameters.empty()
                    ? "default"
                    : reference_role(method.type.type, method.entity);
                file_.entity_mut(method.entity).name =
                    file_.intern_name(tag + ".ctor." + role);
                file_.entity_mut(method.entity).linkage =
                    cir::LinkageKind::Internal;
            } else if (member_kind == cir::EntityKind::Method &&
                       method.name.valid() &&
                       file_.name(method.name) == "operator=") {
                file_.entity_mut(method.entity).name = file_.intern_name(
                    tag + ".assign." +
                    reference_role(method.type.type, method.entity));
                file_.entity_mut(method.entity).linkage =
                    cir::LinkageKind::Internal;
            }
        }
    }
}

ExprResult Session::materialize_lambda_closure(const LambdaClosureStart& start,
                                               LambdaFrame& frame,
                                               SrcLoc loc) {

    std::string temp_name = ".lambda.tmp." + std::to_string(start.index);
    cir::EntityId temp = builder_.add_entity(cir::EntityKind::Variable,
                                             temp_name,
                                             start.record.type,
                                             {},
                                             loc,
                                             cir::StorageDuration::Automatic,
                                             cir::MemorySpace::Default,
                                             {});
    file_.entity_mut(temp).is_definition = true;

    cir::Fragment fragment;
    for (LambdaCapture& capture : frame.captures) {

        ExprResult this_source;
        if (capture.kind == LambdaCaptureKind::ThisPointer ||
            capture.kind == LambdaCaptureKind::ThisObject) {
            this_source = collect_this_expr(loc);
            if (this_source.has_error) {
                continue;
            }
            fragment = chain(std::move(fragment),
                             std::move(this_source.fragment), loc);
        }
        if (capture.kind == LambdaCaptureKind::Init) {
            fragment = chain(std::move(fragment),
                             std::move(capture.init_fragment), loc);
        }

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.lambda.capture.init");
        cir::InstId place = builder_.local_place(temp, start.record.type, loc);
        cir::InstId field_place = builder_.field_addr(
            place, capture.field_entity, capture.field_type, loc);
        switch (capture.kind) {
        case LambdaCaptureKind::Entity: {
            cir::InstId source_place =
                lambda_capture_source_place(capture, loc);
            if (capture.by_ref) {
                cir::InstId address = builder_.addr_of(source_place, loc);
                cir::InstId bound = builder_.cast(capture.field_type, address,
                                                  "reference", loc);
                builder_.store(field_place, bound, loc);
                break;
            }
            cir::EntityId copy_constructor =
                record_copy_constructor(capture.field_type);
            if (copy_constructor.valid()) {
                emit_construct_in_place(
                    field_place,
                    structor_complete_variant(copy_constructor),
                    {builder_.addr_of(source_place, loc)},
                    loc);
            } else {
                builder_.store(field_place,
                               builder_.lvalue_to_rvalue(source_place, loc),
                               loc);
            }
            break;
        }
        case LambdaCaptureKind::Init: {
            if (capture.by_ref) {
                cir::InstId address =
                    builder_.addr_of(capture.init_place, loc);
                cir::InstId bound = builder_.cast(capture.field_type, address,
                                                  "reference", loc);
                builder_.store(field_place, bound, loc);
                break;
            }
            if (capture.init_place.valid()) {
                cir::EntityId copy_constructor =
                    record_copy_constructor(capture.field_type);
                if (copy_constructor.valid()) {
                    emit_construct_in_place(
                        field_place,
                        structor_complete_variant(copy_constructor),
                        {builder_.addr_of(capture.init_place, loc)},
                        loc);
                } else {
                    builder_.store(
                        field_place,
                        builder_.lvalue_to_rvalue(capture.init_place, loc),
                        loc);
                }
                break;
            }
            if (!capture.init_value.valid()) {

                break;
            }
            builder_.store(field_place, capture.init_value, loc);

            if (!capture.init_lifetimes.empty()) {
                for (cir::LifetimeId lifetime : capture.init_lifetimes) {
                    retire_lifetime(lifetime);
                }
            } else {

                remove_destructor_cleanup(
                    temporary_entity_of_value(capture.init_value));
            }
            break;
        }
        case LambdaCaptureKind::ThisPointer: {
            builder_.store(field_place, this_source.value, loc);
            break;
        }
        case LambdaCaptureKind::ThisObject: {
            cir::InstId source_place = builder_.deref(this_source.value, loc);
            cir::EntityId copy_constructor =
                record_copy_constructor(capture.field_type);
            if (copy_constructor.valid()) {
                emit_construct_in_place(
                    field_place,
                    structor_complete_variant(copy_constructor),
                    {builder_.addr_of(source_place, loc)},
                    loc);
            } else {
                builder_.store(field_place,
                               builder_.lvalue_to_rvalue(source_place, loc),
                               loc);
            }
            break;
        }
        }
        fragment = chain(std::move(fragment),
                         finish_fragment_block(block, previous), loc);
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.lambda");
    cir::InstId place = builder_.local_place(temp, start.record.type, loc);
    cir::InstId value = builder_.lvalue_to_rvalue(place, loc);
    fragment = chain(std::move(fragment),
                     finish_fragment_block(block, previous), loc);

    cir::LifetimeId lifetime = register_destructor_cleanup(
        temp, start.record.type, loc,
        /*full_expression_temporary=*/true);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = value;
    result.type = start.record.type;
    result.category = ValueCategory::PrValue;
    if (lifetime.valid()) {
        result.materialized_lifetimes.push_back(lifetime);
    }
    return result;
}

LambdaClosureStart Session::begin_generic_lambda_closure(
    std::vector<ParamInput> params,
    cir::TypeId trailing_return_type,
    LambdaSpecifiers specifiers,
    LambdaCaptureDefault capture_default,
    std::vector<LambdaCaptureItem> explicit_captures,
    TemplateInfo& info,
    SrcLoc loc) {
    LambdaClosureStart start;
    start.index = ++lambda_closure_counter_;
    start.loc = loc;
    start.is_mutable = specifiers.is_mutable;
    start.exception_spec = std::move(specifiers.exception_spec);
    start.is_constexpr = specifiers.is_constexpr;
    start.is_consteval = specifiers.is_consteval;
    start.deduced_return = !trailing_return_type.valid();
    start.is_generic = true;
    start.has_lambda_capture =
        capture_default != LambdaCaptureDefault::None ||
        !explicit_captures.empty();
    if (specifiers.is_static) {
        report_error("static generic lambdas are not supported yet", loc);
        start.has_error = true;
    }

    bump_pattern_taint();

    uint32_t watermark = file_.entity_table_size();

    std::string tag = ".lambda." + std::to_string(start.index);
    start.record =
        create_record_tag(cir::RecordKind::Struct, tag, loc, /*bind_tag=*/false);
    if (cir::RecordFacts* facts = file_.record_facts(start.record.entity)) {
        facts->is_lambda_closure = true;
        facts->lambda_has_capture = start.has_lambda_capture;
    }

    cir::TypeId return_type = trailing_return_type.valid()
        ? trailing_return_type
        : file_.auto_type(cir::AutoTypeFlavor::Cxx);
    std::vector<cir::TypeRef> param_types;
    std::vector<uint8_t> parameter_pack_flags;
    bool has_parameter_pack = false;
    param_types.reserve(params.size());
    parameter_pack_flags.reserve(params.size());
    for (const ParamInput& param : params) {
        param_types.push_back(param.type);
        uint8_t pack_flag = param.is_parameter_pack ? 1 : 0;
        parameter_pack_flags.push_back(pack_flag);
        has_parameter_pack = has_parameter_pack || pack_flag != 0;
    }
    if (!has_parameter_pack) {
        parameter_pack_flags.clear();
    }
    start.declared_fn_type = function_type(
        file_.type_ref(return_type), param_types,
        /*is_variadic=*/false, /*has_prototype=*/true,
        /*member_is_const=*/!start.is_mutable,
        start.exception_spec,
        parameter_pack_flags);
    cir::TypeId entity_type =
        member_function_type_with_this(start.record.type, start.declared_fn_type);

    DeclFlags operator_flags;
    operator_flags.is_inline = true;
    operator_flags.is_constexpr = true;
    operator_flags.is_consteval = start.is_consteval;
    start.call_operator = builder_.add_entity(cir::EntityKind::Method,
                                              tag + ".op",
                                              entity_type,
                                              start.record.entity,
                                              loc,
                                              cir::StorageDuration::None,
                                              cir::MemorySpace::Default,
                                              operator_flags.to_cir());
    apply_attributes(start.call_operator,
                     AttributeTarget::Function,
                     specifiers.attrs,
                     loc);
    file_.entity_mut(start.call_operator).operator_function = {
        .kind = cir::OperatorFunctionKind::Symbolic,
        .spelling = cir::OperatorFunctionSpelling::Call,
    };
    cir::ClosureIdentityFact closure_identity;
    closure_identity.source_loc = loc;
    closure_identity.key_loc = loc;
    closure_identity.lexical_owner = current_function_entity().valid()
        ? current_function_entity()
        : current_member_record_;
    closure_identity.record = start.record.entity;
    closure_identity.type = file_.type_ref(start.record.type);
    closure_identity.call_operator = start.call_operator;
    if (current_function_entity().valid()) {
        closure_identity.abi_context =
            cir::ClosureAbiContextKind::FunctionBody;
    } else if (!closure_abi_context_stack_.empty()) {
        const ActiveClosureAbiContext& context =
            closure_abi_context_stack_.back();
        closure_identity.abi_context = context.kind;
        closure_identity.abi_context_name = context.name;
        closure_identity.abi_context_decl = context.declaration_context;
    } else {
        closure_identity.abi_context =
            cir::ClosureAbiContextKind::TranslationUnit;
    }
    closure_identity.is_structural = !start.has_lambda_capture;
    closure_identity.is_generic = true;
    start.closure_identity =
        file_.add_closure_identity(std::move(closure_identity));
    if (cir::RecordFacts* facts = file_.record_facts(start.record.entity)) {
        facts->closure_identity = start.closure_identity;
    }
    start.params = std::move(params);

    info.entity = start.call_operator;
    info.name = "operator()";
    info.declaration_attrs.append(specifiers.attrs);
    info.operator_function =
        file_.entity(start.call_operator).operator_function;
    info.pattern_type = start.declared_fn_type;
    info.lexical_context = file_.entity(start.record.entity).semantic_context;

    LambdaFrame frame;
    frame.closure_record = start.record.entity;
    frame.call_operator = start.call_operator;
    frame.capture_origin_function = lambda_stack_.empty()
        ? current_function_entity()
        : lambda_stack_.front().capture_origin_function;
    frame.entity_watermark = watermark;
    frame.capture_default = capture_default;
    frame.is_mutable = start.is_mutable;
    frame.enclosing_this_place =
        lambda_stack_.empty() ? current_this_place_
                              : lambda_stack_.front().enclosing_this_place;
    frame.enclosing_member_record =
        lambda_stack_.empty() ? current_member_record_
                              : lambda_stack_.front().enclosing_member_record;
    frame.closure_index = start.index;
    lambda_stack_.push_back(std::move(frame));

    register_explicit_lambda_captures(start, std::move(explicit_captures), loc);
    return start;
}

ExprResult Session::finish_generic_lambda_closure(LambdaClosureStart start,
                                                  TemplateInfo info,
                                                  SrcLoc loc) {
    if (file_.valid(start.closure_identity)) {
        file_.closure_identity_mut(start.closure_identity).key_loc = loc;
    }
    file_.entity_mut(start.call_operator).linkage = cir::LinkageKind::Internal;

    LambdaFrame frame = std::move(lambda_stack_.back());
    lambda_stack_.pop_back();

    publish_lambda_closure(start, frame, {}, loc);
    register_template_entity(std::move(info), start.call_operator, loc);

    if (start.has_error) {
        ExprResult result;
        result.has_error = true;
        result.type = builder_.unknown_type();
        result.category = ValueCategory::PrValue;
        return result;
    }
    return materialize_lambda_closure(start, frame, loc);
}

void Session::finalize_variable_initializer_closure_linkage(
    cir::EntityId variable) {
    if (!variable.valid() || !file_.valid(variable)) {
        return;
    }
    const cir::Entity& object = file_.entity(variable);
    if (object.kind != cir::EntityKind::Variable || !object.name.valid()) {
        return;
    }
    cir::LinkageKind linkage = object.decl_flags.is_inline
        ? cir::LinkageKind::LinkOnceODR
        : cir::LinkageKind::Internal;
    for (cir::ClosureIdentityId identity_id :
         file_.closure_identity_ids()) {
        cir::ClosureIdentityFact& identity =
            file_.closure_identity_mut(identity_id);
        if (identity.abi_context !=
                cir::ClosureAbiContextKind::VariableInitializer ||
            identity.abi_context_name != object.name ||
            identity.lexical_owner.valid()) {
            continue;
        }
        identity.lexical_owner = variable;
        if (!identity.record.valid() || !file_.valid(identity.record)) {
            continue;
        }
        cir::Entity& record = file_.entity_mut(identity.record);
        record.linkage = linkage;
        record.abi_owner = variable;
        if (const cir::RecordFacts* facts =
                file_.record_facts(identity.record)) {
            for (const cir::RecordMethodFact& method : facts->methods) {
                if (!method.entity.valid() || !file_.valid(method.entity)) {
                    continue;
                }
                cir::Entity& member = file_.entity_mut(method.entity);
                member.linkage = linkage;
                member.abi_owner = identity.record;
            }
        }
        if (identity.invoker.valid() && file_.valid(identity.invoker)) {
            cir::Entity& invoker = file_.entity_mut(identity.invoker);
            invoker.linkage = linkage;
            invoker.abi_owner = identity.record;
        }
    }
}

void Session::push_lambda_instantiation_frame(cir::EntityId method) {
    cir::EntityId record = file_.entity(method).parent;
    LambdaFrame frame;
    frame.closure_record = record;
    frame.call_operator = method;

    frame.entity_watermark = 0;
    const cir::RecordFacts* facts = file_.record_facts(record);
    if (facts) {
        for (const cir::RecordFieldFact& field : facts->fields) {
            if (field.lambda_capture_kind ==
                cir::LambdaCaptureFieldKind::None) {
                continue;
            }
            LambdaCapture capture;
            cir::TypeId field_type = field.type.type;
            cir::TypeId resolved = file_.resolved_type(field_type);
            bool is_this = false;
            bool is_pointer = false;
            switch (field.lambda_capture_kind) {
                case cir::LambdaCaptureFieldKind::None:
                    continue;
                case cir::LambdaCaptureFieldKind::Entity:
                    capture.kind = LambdaCaptureKind::Entity;
                    break;
                case cir::LambdaCaptureFieldKind::Init:
                    capture.kind = LambdaCaptureKind::Init;
                    break;
                case cir::LambdaCaptureFieldKind::ThisPointer:
                    capture.kind = LambdaCaptureKind::ThisPointer;
                    is_this = true;
                    is_pointer = true;
                    break;
                case cir::LambdaCaptureFieldKind::ThisObject:
                    capture.kind = LambdaCaptureKind::ThisObject;
                    is_this = true;
                    break;
            }
            capture.source_entity = field.lambda_capture_source;
            capture.field_entity = field.entity;
            capture.field_type = field_type;
            capture.by_ref = is_reference_type(resolved);
            frame.captures.push_back(std::move(capture));
            size_t index = frame.captures.size() - 1;
            frame.capture_memo[static_cast<uint64_t>(field.entity.index)] =
                index;
            if (field.lambda_capture_source.valid()) {
                frame.capture_memo[static_cast<uint64_t>(
                    field.lambda_capture_source.index)] = index;
            }
            if (is_this) {
                frame.this_capture = index;

                cir::TypeId pointee = is_pointer
                    ? file_.pointer_pointee_type(resolved)
                    : resolved;
                frame.enclosing_member_record =
                    file_.record_entity(file_.resolved_type(pointee));
            }
        }
    }
    lambda_stack_.push_back(std::move(frame));
}

void Session::pop_lambda_instantiation_frame() {
    if (!lambda_stack_.empty()) {
        lambda_stack_.pop_back();
    }
}

cir::TypeId Session::lambda_invoker_function_type(cir::TypeId method_type) {
    cir::TypeId resolved = file_.resolved_type(method_type);
    const auto* payload = std::get_if<cir::FunctionTypePayload>(
        &file_.type_payload(resolved));
    if (!payload) {
        return {};
    }
    cir::TypeRef result = payload->return_type;
    std::vector<cir::TypeRef> parameters = payload->parameters;
    bool is_variadic = payload->is_variadic;
    bool has_prototype = payload->has_prototype;
    cir::FunctionExceptionSpec exception_spec = payload->exception_spec;
    std::vector<uint8_t> pack_flags = payload->parameter_pack_flags;
    return function_type(result, parameters, is_variadic, has_prototype,
                         /*member_is_const=*/false,
                         std::move(exception_spec), pack_flags,
                         cir::FunctionRefQualifierKind::None,
                         /*member_is_volatile=*/false);
}

cir::EntityId Session::synthesize_lambda_invoker(cir::TypeId closure_type,
                                                 cir::EntityId call_operator,
                                                 cir::TypeId declared_fn_type,
                                                 const std::string& name,
                                                 SrcLoc loc) {
    declared_fn_type = lambda_invoker_function_type(declared_fn_type);
    cir::TypeId resolved_fn = file_.resolved_type(declared_fn_type);
    const auto* fn_payload = std::get_if<cir::FunctionTypePayload>(
        &file_.type_payload(resolved_fn));
    if (!fn_payload) {
        return {};
    }
    cir::TypeRef invoke_result = fn_payload->return_type;
    std::vector<ParamInput> invoke_params;
    invoke_params.reserve(fn_payload->parameters.size());

    std::vector<cir::TypeRef> parameter_types = fn_payload->parameters;
    fn_payload = nullptr;
    for (size_t i = 0; i < parameter_types.size(); ++i) {
        ParamInput param;
        param.name = ".lambda.arg." + std::to_string(i);
        param.type = parameter_types[i];
        param.loc = loc;
        invoke_params.push_back(std::move(param));
    }

    std::unique_ptr<BlockContextState> saved = save_function_context();
    DeclFlags invoke_flags;
    invoke_flags.is_static = true;
    invoke_flags.is_constexpr =
        file_.entity(call_operator).decl_flags.is_constexpr;
    invoke_flags.is_consteval =
        file_.entity(call_operator).decl_flags.is_consteval;
    FunctionDeclStart fn = begin_function_type(name,
                                               declared_fn_type,
                                               invoke_result,
                                               invoke_params,
                                               loc,
                                               invoke_flags);
    cir::EntityId invoke_entity = fn.decl.entity;

    cir::EntityId instance = builder_.add_entity(
        cir::EntityKind::Variable, name + ".instance", closure_type,
        {}, loc, cir::StorageDuration::Automatic);
    file_.entity_mut(instance).is_definition = true;
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("lambda.invoke.this");
    cir::InstId instance_place =
        builder_.local_place(instance, closure_type, loc);
    cir::Fragment body_fragment = finish_fragment_block(block, previous);

    ExprResult callee;
    callee.fragment = std::move(body_fragment);
    callee.place = instance_place;
    callee.entity = call_operator;
    callee.type = file_.entity(call_operator).type;
    callee.name = "operator()";
    callee.qualified_name = true;
    callee.category = ValueCategory::FunctionDesignator;
    std::vector<ExprResult> forwarded;
    forwarded.reserve(fn.function.parameters.size());
    for (const cir::FunctionParameter& parameter : fn.function.parameters) {
        cir::BlockId arg_previous = builder_.current_block();
        cir::BlockId arg_block = begin_fragment_block("lambda.invoke.arg");
        cir::InstId arg_place = builder_.local_place(
            parameter.entity, file_.entity(parameter.entity).type, loc);
        ExprResult arg;
        arg.fragment = finish_fragment_block(arg_block, arg_previous);
        arg.place = arg_place;
        arg.type = file_.entity(parameter.entity).type;
        arg.category = ValueCategory::LValue;
        cir::TypeId parameter_type = file_.resolved_type(arg.type);
        cir::TypeKind parameter_kind = file_.valid(parameter_type)
            ? file_.type(parameter_type).kind
            : cir::TypeKind::Invalid;
        arg = deref_reference_lvalue(std::move(arg), loc);

        if (parameter_kind == cir::TypeKind::RValueReference) {
            arg.category = ValueCategory::XValue;
        }
        forwarded.push_back(std::move(arg));
    }
    ExprResult call =
        collect_call_expr(std::move(callee), std::move(forwarded), loc);
    bool returns_void = !invoke_result.type.valid() ||
        file_.resolved_type(invoke_result.type) ==
            file_.builtin_type(cir::BuiltinTypeKind::Void);
    StmtResult ret;
    if (returns_void) {
        StmtResult call_stmt = make_stmt_result(std::move(call.fragment));
        StmtResult plain_return = collect_return_stmt(std::nullopt, loc);
        call_stmt.fragment = chain(std::move(call_stmt.fragment),
                                   std::move(plain_return.fragment), loc);
        ret = std::move(call_stmt);
    } else {
        ret = collect_return_stmt(std::move(call), loc);
    }
    finish_function(std::move(ret), loc);
    file_.entity_mut(invoke_entity).linkage = cir::LinkageKind::Internal;
    restore_function_context(std::move(saved));
    return invoke_entity;
}

ExprResult Session::convert_generic_lambda_to_function_pointer(
    ExprResult expr,
    cir::TypeId target_type,
    bool* handled,
    SrcLoc loc) {
    *handled = false;
    cir::TypeId source_resolved = file_.resolved_type(expr.type);
    cir::TypeId target_resolved = file_.resolved_type(target_type);
    if (!file_.valid(source_resolved) || !file_.valid(target_resolved) ||
        file_.type(source_resolved).kind != cir::TypeKind::Record ||
        file_.type(target_resolved).kind != cir::TypeKind::Pointer) {
        return expr;
    }
    const cir::RecordFacts* facts = file_.record_facts_for_type(source_resolved);
    if (!facts || !facts->is_lambda_closure || !facts->fields.empty()) {
        return expr;
    }
    cir::TypeId pointee =
        file_.resolved_type(file_.pointer_pointee_type(target_resolved));
    if (!file_.valid(pointee) ||
        file_.type(pointee).kind != cir::TypeKind::Function) {
        return expr;
    }

    cir::EntityId record_entity = file_.record_entity(source_resolved);
    cir::DeclContextId record_context = record_entity.valid()
        ? file_.entity(record_entity).semantic_context
        : cir::DeclContextId{};
    const cir::Binding* binding = record_context.valid()
        ? file_.lookup_callable_binding(record_context, "operator()",
                                        /*include_parents=*/false)
        : nullptr;
    const TemplateInfo* info = nullptr;
    for (cir::EntityId entity : binding ? binding->entities
                                        : std::vector<cir::EntityId>{}) {
        if (const TemplateInfo* candidate = template_info(entity)) {
            info = candidate;
            break;
        }
    }
    if (!info || !tstate().function_template_instantiation_callback_) {
        return expr;
    }

    const auto* target_payload =
        std::get_if<cir::FunctionTypePayload>(&file_.type_payload(pointee));
    if (!target_payload) {
        return expr;
    }
    std::vector<ExprResult> probe_args;
    probe_args.reserve(target_payload->parameters.size());
    for (const cir::TypeRef& parameter : target_payload->parameters) {
        ExprResult probe;
        probe.type = parameter.type;
        probe.category = ValueCategory::PrValue;
        probe_args.push_back(std::move(probe));
    }
    std::vector<TemplateArgument> deduced;
    TemplateArgumentBindings deduced_bindings;
    if (!deduce_template_arguments(*info,
                                   probe_args,
                                   deduced,
                                   nullptr,
                                   nullptr,
                                   &deduced_bindings)) {
        return expr;
    }
    cir::EntityId specialization =
        tstate().function_template_instantiation_callback_(
            *info, deduced_bindings, loc);
    if (!specialization.valid()) {
        return expr;
    }
    const cir::RecordMethodFact* fact = file_.method_fact(specialization);
    const cir::FunctionTypePayload* specialization_payload = fact
        ? std::get_if<cir::FunctionTypePayload>(
              &file_.type_payload(file_.resolved_type(fact->type.type)))
        : nullptr;
    if (specialization_payload &&
        contains_auto_type(specialization_payload->return_type.type) &&
        !require_placeholder_result(
            specialization, cir::InstantiationDemandKind::OdrUse, loc)) {
        return expr;
    }
    fact = file_.method_fact(specialization);
    cir::TypeId invoker_type = fact
        ? lambda_invoker_function_type(fact->type.type)
        : cir::TypeId{};
    if (!fact || !type_equal(invoker_type, pointee)) {
        return expr;
    }

    uint64_t memo_key = static_cast<uint64_t>(specialization.index);
    cir::EntityId invoker{};
    auto found = lambda_invoker_memo_.find(memo_key);
    if (found != lambda_invoker_memo_.end()) {
        invoker = found->second;
    } else {
        std::string name = file_.entity(specialization).name.valid()
            ? std::string(file_.name(file_.entity(specialization).name))
            : std::string(".lambda.op");
        invoker = synthesize_lambda_invoker(source_resolved,
                                            specialization,
                                            invoker_type,
                                            name + ".invoke",
                                            loc);
        if (invoker.valid()) {
            lambda_invoker_memo_[memo_key] = invoker;
            if (facts && file_.valid(facts->closure_identity)) {
                cir::ClosureIdentityId closure_id =
                    facts->closure_identity;
                cir::ClosureIdentityFact& identity =
                    file_.closure_identity_mut(closure_id);
                cir::EntityId previous_invoker = identity.invoker;
                identity.invoker = invoker;
                track_speculative_rollback(
                    [this, closure_id, previous_invoker] {
                        if (file_.valid(closure_id)) {
                            file_.closure_identity_mut(closure_id).invoker =
                                previous_invoker;
                        }
                    });
                if (identity.lexical_owner.valid()) {
                    cir::Entity& generated = file_.entity_mut(invoker);
                    generated.linkage =
                        file_.entity(record_entity).linkage;
                    generated.abi_owner = record_entity;
                }
            }
        }
    }
    if (!invoker.valid()) {
        return expr;
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("lambda.generic.conv");
    cir::InstId pointer = builder_.function_to_pointer(invoker, loc);
    cir::InstId value = pointer;
    if (file_.inst(pointer).result_type != target_type) {
        value = builder_.cast(target_type, pointer, "conversion", loc);
    }
    cir::Fragment fragment = finish_fragment_block(block, previous);

    *handled = true;
    ExprResult result;
    result.fragment = chain(std::move(expr.fragment), std::move(fragment), loc);
    result.value = value;
    result.type = target_type;
    result.category = ValueCategory::PrValue;
    return result;
}

} // namespace aburi::collect
