#include "parser.h"

#include "../builtin_registry.h"
#include "../numeric_utils.h"
#include "../token_spelling.h"

#include <algorithm>
#include <cstdint>
#include <functional>
#include <iterator>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace aburi::syntax {

namespace {

TextPayload text_payload(std::string_view text) {
    return TextPayload{std::string(text)};
}

FloatingLiteralKind floating_literal_kind_for(TokenType type) {
    switch (type) {
        case TokenType::FLOAT_CONST:
            return FloatingLiteralKind::Float;
        case TokenType::LONG_DOUBLE_CONST:
            return FloatingLiteralKind::LongDouble;
        default:
            return FloatingLiteralKind::Double;
    }
}

int64_t character_literal_value(std::string_view decoded) {
    int64_t value = 0;
    for (unsigned char byte : decoded) {
        value <<= 8;
        value |= static_cast<int64_t>(byte);
    }
    return value;
}

PrecLevel next_prec_level(PrecLevel level) {
    return static_cast<PrecLevel>(static_cast<uint8_t>(level) + 1);
}

bool is_assignment_token(TokenType type) {
    switch (type) {
        case TokenType::ASSIGN:
        case TokenType::ASSIGN_ADD:
        case TokenType::ASSIGN_SUB:
        case TokenType::ASSIGN_MUL:
        case TokenType::ASSIGN_DIV:
        case TokenType::ASSIGN_MOD:
        case TokenType::ASSIGN_LSHIFT:
        case TokenType::ASSIGN_RSHIFT:
        case TokenType::ASSIGN_AND:
        case TokenType::ASSIGN_XOR:
        case TokenType::ASSIGN_OR:
            return true;
        default:
            return false;
    }
}

bool is_fold_operator(BinaryOperator op) {
    switch (op) {
        case BinaryOperator::Add:
        case BinaryOperator::Sub:
        case BinaryOperator::Mul:
        case BinaryOperator::Div:
        case BinaryOperator::Mod:
        case BinaryOperator::Less:
        case BinaryOperator::LessEqual:
        case BinaryOperator::Greater:
        case BinaryOperator::GreaterEqual:
        case BinaryOperator::Equal:
        case BinaryOperator::NotEqual:
        case BinaryOperator::Assign:
        case BinaryOperator::AssignAdd:
        case BinaryOperator::AssignSub:
        case BinaryOperator::AssignMul:
        case BinaryOperator::AssignDiv:
        case BinaryOperator::AssignMod:
        case BinaryOperator::AssignShl:
        case BinaryOperator::AssignShr:
        case BinaryOperator::AssignAnd:
        case BinaryOperator::AssignXor:
        case BinaryOperator::AssignOr:
        case BinaryOperator::BitAnd:
        case BinaryOperator::BitOr:
        case BinaryOperator::BitXor:
        case BinaryOperator::Shl:
        case BinaryOperator::Shr:
        case BinaryOperator::PtrMemDot:
        case BinaryOperator::PtrMemArrow:
        case BinaryOperator::LogicalAnd:
        case BinaryOperator::LogicalOr:
        case BinaryOperator::Comma:
            return true;
        default:
            return false;
    }
}

bool should_retain_dependent_fold_pattern(
    const collect::Session& session,
    bool retaining_constraint_normal_form) {
    return session.collecting_pattern() &&
        !(session.is_instantiating() &&
          retaining_constraint_normal_form);
}

std::optional<bool> empty_boolean_fold_identity(BinaryOperator op) {
    switch (op) {
        case BinaryOperator::LogicalAnd:
            return true;
        case BinaryOperator::LogicalOr:
            return false;
        default:
            return std::nullopt;
    }
}

std::optional<collect::ExprResult> empty_unary_fold_identity(
    collect::Session& session,
    BinaryOperator op,
    SrcLoc loc) {
    if (std::optional<bool> identity = empty_boolean_fold_identity(op)) {
        return session.make_boolean_literal(*identity,
                                            *identity ? "true" : "false",
                                            loc);
    }
    if (op == BinaryOperator::Comma) {
        return session.make_void_prvalue();
    }
    return std::nullopt;
}

bool token_can_start_cast_operand(TokenType type) {
    switch (type) {
        case TokenType::IDENTIFIER:
        case TokenType::INTEGER_CONST:
        case TokenType::UNSIGNED_INTEGER_CONST:
        case TokenType::LONG_CONST:
        case TokenType::UNSIGNED_LONG_CONST:
        case TokenType::LONG_LONG_CONST:
        case TokenType::UNSIGNED_LONG_LONG_CONST:
        case TokenType::BITINT_CONST:
        case TokenType::UNSIGNED_BITINT_CONST:
        case TokenType::PP_NUMBER:
        case TokenType::FLOAT_CONST:
        case TokenType::DOUBLE_CONST:
        case TokenType::LONG_DOUBLE_CONST:
        case TokenType::CHAR_LITERAL:
        case TokenType::STRING_LITERAL:
        case TokenType::TRUE_KW:
        case TokenType::FALSE_KW:
        case TokenType::NULLPTR_KW:
        case TokenType::THIS_KW:
        case TokenType::LEFT_PAREN:
        case TokenType::PLUS:
        case TokenType::NEGATE:
        case TokenType::LOGICAL_NOT:
        case TokenType::BITWISE_NOT:
        case TokenType::MULTIPLY:
        case TokenType::BITWISE_AND:

        case TokenType::LOGICAL_AND:
        case TokenType::INCREMENT:
        case TokenType::DECREMENT:
        case TokenType::SIZEOF:
        case TokenType::ALIGNOF:
        case TokenType::TYPEID_KW:
        case TokenType::EXTENSION_KW:
        case TokenType::REAL_PART:
        case TokenType::IMAG_PART:

        case TokenType::GENERIC:
        case TokenType::REQUIRES_KW:
            return true;
        default:
            return false;
    }
}

struct CxxNamedCastInfo {
    collect::CppNamedCastKind collect_kind = collect::CppNamedCastKind::Static;
    CastOperator syntax_kind = CastOperator::Invalid;
};

std::optional<CxxNamedCastInfo> cxx_named_cast_kind(std::string_view name) {
    if (name == "static_cast") {
        return CxxNamedCastInfo{collect::CppNamedCastKind::Static,
                                CastOperator::CppStatic};
    }
    if (name == "const_cast") {
        return CxxNamedCastInfo{collect::CppNamedCastKind::Const,
                                CastOperator::CppConst};
    }
    if (name == "reinterpret_cast") {
        return CxxNamedCastInfo{collect::CppNamedCastKind::Reinterpret,
                                CastOperator::CppReinterpret};
    }
    if (name == "dynamic_cast") {
        return CxxNamedCastInfo{collect::CppNamedCastKind::Dynamic,
                                CastOperator::CppDynamic};
    }
    return std::nullopt;
}

struct TemplateReplayGuardScope {
    collect::Session& session;
    bool active = false;

    TemplateReplayGuardScope(collect::Session& session, SrcLoc loc)
        : session(session), active(session.enter_template_replay_guard(loc)) {}

    ~TemplateReplayGuardScope() {
        if (active) {
            session.leave_template_replay_guard();
        }
    }
};

bool template_argument_is_dependent(
    collect::Session& session,
    const collect::Session::TemplateArgument& argument) {
    if (argument.kind == cir::TemplateArgumentKind::Type) {
        return session.type_contains_type_param(argument.type.type);
    }
    if (argument.kind == cir::TemplateArgumentKind::Value) {
        return argument.is_dependent ||
               session.type_contains_type_param(argument.value_type.type) ||
               session.type_contains_type_param(
                   argument.dependent_value_qualifier.type);
    }
    if (argument.kind == cir::TemplateArgumentKind::Template) {
        return argument.is_dependent;
    }
    return false;
}

} // namespace

void Parser::bind_unqualified_member_template_id(
    collect::ExprResult& expression,
    std::string_view name,
    SrcLoc loc) {
    if (expression.qualified_name || expression.has_error) {
        return;
    }
    std::vector<cir::EntityId> candidates = expression.candidates;
    if (candidates.empty() && expression.entity.valid()) {
        candidates.push_back(expression.entity);
    }
    const cir::File& file = collect_session_.file();
    bool has_non_static_method =
        std::any_of(candidates.begin(), candidates.end(),
                    [&](cir::EntityId candidate) {
                        if (!candidate.valid() || !file.valid(candidate) ||
                            file.entity(candidate).kind !=
                                cir::EntityKind::Method) {
                            return false;
                        }
                        const cir::RecordMethodFact* method =
                            file.method_fact(candidate);
                        return !file.entity(candidate)
                                    .is_static_member_function &&
                            !(method && method->is_static);
                    });
    if (!has_non_static_method) {
        return;
    }

    collect::ExprResult bound = collect_session_.lookup_name(name, loc);
    if (bound.category != collect::ValueCategory::FunctionDesignator ||
        !bound.place.valid()) {
        return;
    }
    expression.fragment = std::move(bound.fragment);
    expression.place = bound.place;
    expression.bound_member_object_category =
        bound.bound_member_object_category;
    expression.member_access_object_type =
        bound.member_access_object_type;
    expression.member_candidate_object_paths =
        std::move(bound.member_candidate_object_paths);
    expression.has_error = expression.has_error || bound.has_error;
}

collect::ExprResult Parser::template_id_expression_result(
    const collect::Session::TemplateInfo& info,
    cir::EntityId instantiated,
    SrcLoc loc,
    bool qualified_name) {
    collect::ExprResult sem;
    if (!instantiated.valid()) {
        sem.has_error = true;
        return sem;
    }
    const cir::File& file = collect_session_.file();
    if (info.is_class_template || info.is_alias_template) {
        sem.type = file.entity(instantiated).type;
        sem.category = collect::ValueCategory::Type;
        sem.unparenthesized_id_or_member = true;
        return sem;
    }
    if (info.is_variable_template) {
        std::string display =
            file.entity(instantiated).name.valid()
                ? std::string(file.name(file.entity(instantiated).name))
                : info.name;
        return collect_session_.make_entity_reference(instantiated,
                                                      display,
                                                      loc,
                                                      qualified_name);
    }
    if (info.is_concept) {
        sem.has_error = true;
        return sem;
    }
    sem.entity = instantiated;
    sem.type = file.entity(instantiated).type;
    sem.name = info.name;
    sem.qualified_name = qualified_name;
    sem.category = collect::ValueCategory::FunctionDesignator;
    sem.unparenthesized_id_or_member = true;
    bind_unqualified_member_template_id(sem, info.name, loc);
    return sem;
}

collect::ExprResult Parser::evaluate_concept_id_expression(
    const collect::Session::TemplateInfo& info,
    std::vector<collect::Session::TemplateArgument> arguments,
    SrcLoc loc,
    bool qualified_name,
    std::vector<collect::Session::TemplateArgument>* canonical_arguments_out,
    uint64_t point_lookup_generation) {

    if (Parser* owner = module_unit_parser_for(info.entity)) {
        collect::Session::ModuleVisibilityOverride visibility(
            collect_session_,
            collect_session_.file().entity(info.entity).origin_unit);
        size_t diagnostic_watermark = owner->diagnostics_.size();
        collect::ExprResult result = owner->evaluate_concept_id_expression(
            info,
            std::move(arguments),
            loc,
            qualified_name,
            canonical_arguments_out,
            point_lookup_generation);
        diagnostics_.insert(
            diagnostics_.end(),
            std::make_move_iterator(
                owner->diagnostics_.begin() + diagnostic_watermark),
            std::make_move_iterator(owner->diagnostics_.end()));
        owner->diagnostics_.resize(diagnostic_watermark);
        return result;
    }
    if (info.entity.valid() && collect_session_.file().valid(info.entity) &&
        collect_session_.file().entity(info.entity).attr_facts.is_deprecated) {
        const std::string& note = collect_session_.file()
                                      .entity(info.entity)
                                      .attr_facts.deprecated_message;
        collect_session_.report_warning(
            WarningId::DeprecatedDeclarations,
            "'" + info.name + "' is deprecated" +
                (note.empty() ? "" : ": " + note),
            loc);
    }
    auto make_error = [] {
        collect::ExprResult sem;
        sem.has_error = true;
        return sem;
    };
    auto make_dependent = [&](const std::vector<
                              collect::Session::TemplateArgument>&
                                  canonical_arguments) {
        collect_session_.bump_pattern_taint();
        collect::ExprResult sem =
            collect_session_.make_boolean_literal(false, "false", loc);
        cir::TemplateValueExpression expression;
        expression.loc = loc;
        expression.definition_context =
            collect_session_.current_decl_context();
        expression.definition_lookup_generation =
            point_lookup_generation != 0
                ? point_lookup_generation
                : collect_session_.lookup_generation();
        cir::TemplateValueExprNode concept_node;
        concept_node.kind = cir::TemplateValueExprKind::ConceptId;
        concept_node.result_type =
            collect_session_.type_ref(
                collect_session_.file().builtin_type(
                    cir::BuiltinTypeKind::Bool));
        concept_node.entity = info.entity;
        concept_node.name =
            collect_session_.file().intern_name(info.name);
        concept_node.semantic_key = info.name;
        concept_node.template_arguments =
            cir::TemplateArgumentList(canonical_arguments);
        expression.nodes.push_back(std::move(concept_node));
        expression.root = 0;
        sem.template_value_expr = std::move(expression);
        sem.value_dependent = true;
        sem.name = info.name;
        sem.qualified_name = qualified_name;
        sem.unparenthesized_id_or_member = true;
        return sem;
    };
    auto make_value = [&](bool concept_value) {
        collect::ExprResult sem =
            collect_session_.make_boolean_literal(
                concept_value,
                concept_value ? "true" : "false",
                loc);
        sem.name = info.name;
        sem.qualified_name = qualified_name;
        sem.unparenthesized_id_or_member = true;
        return sem;
    };

    const bool substitution_candidate =
        in_constraint_substitution_failure_context();
    if (!canonicalize_template_arguments(
            info,
            arguments,
            loc,
            &point_lookup_generation,
            substitution_candidate
                ? collect::Session::TemplateArgumentCompletionMode::Candidate
                : collect::Session::TemplateArgumentCompletionMode::Required)) {
        if (substitution_candidate) {

            note_constraint_substitution_failure();
        }
        return make_error();
    }
    if (canonical_arguments_out) {
        *canonical_arguments_out = arguments;
    }
    for (const collect::Session::TemplateArgument& argument : arguments) {
        if (template_argument_is_dependent(collect_session_, argument)) {
            return make_dependent(arguments);
        }
    }
    if (!info.has_definition) {
        diagnose(DiagnosticLevel::Error,
                 "cannot evaluate undefined concept '" + info.name + "'",
                 loc);
        return make_error();
    }

    collect::Session::TemplateArgumentBindings argument_bindings;
    if (!collect_session_.bind_template_arguments_to_parameters(
            info.parameters, arguments, argument_bindings)) {
        return make_error();
    }
    collect_session_.canonicalize_template_argument_bindings(
        argument_bindings);
    using SatisfactionKind =
        collect::Session::ConstraintSatisfactionRequestKind;
    using SatisfactionResult =
        collect::Session::ConstraintSatisfactionResult;
    using SatisfactionState =
        collect::Session::ConstraintSatisfactionScope::State;
    collect::Session::ConstraintSatisfactionScope satisfaction_scope =
        collect_session_.begin_constraint_satisfaction(
            SatisfactionKind::ConceptId,
            info.entity,
            argument_bindings,
            point_lookup_generation);
    if (satisfaction_scope.state == SatisfactionState::Cached) {
        return make_value(
            *satisfaction_scope.cached_result ==
            SatisfactionResult::Satisfied);
    }
    if (satisfaction_scope.state == SatisfactionState::Recursive) {
        diagnose(DiagnosticLevel::Error,
                 "constraint satisfaction depends on itself",
                 loc);
        return make_error();
    }
    struct SatisfactionExit {
        collect::Session* session = nullptr;
        collect::Session::ConstraintSatisfactionScope scope;
        bool complete = false;

        ~SatisfactionExit() {
            if (session && !complete) {
                session->abandon_constraint_satisfaction(std::move(scope));
            }
        }

        void finish(SatisfactionResult result) {
            session->finish_constraint_satisfaction(std::move(scope), result);
            complete = true;
        }
    } satisfaction_exit{&collect_session_, std::move(satisfaction_scope)};

    if (info.constraint_normal_form.has_value()) {
        collect::Session::NormalizedConstraint normal_form;
        uint32_t root =
            normal_form.append_copy_of(*info.constraint_normal_form);
        collect::Session::PatternInstantiationCallbacks callbacks;
        callbacks.point_lookup_generation = point_lookup_generation;
        configure_pattern_instantiation_callbacks(callbacks, loc);
        std::string substitution_error;
        if (!normal_form.valid_node(root)) {
            satisfaction_exit.finish(SatisfactionResult::Unsatisfied);
            return make_value(false);
        }
        {

            TentativeParsingAction mapping_transaction(
                *this, TentativeMode::CollectBacked);
            collect::Session::NormalizedConstraint composed_form =
                normal_form;
            if (collect_session_.compose_constraint_parameter_mappings(
                    composed_form,
                    root,
                    argument_bindings,
                    callbacks,
                    &substitution_error)) {
                normal_form = std::move(composed_form);
                mapping_transaction.commit();
            }
        }
        root = expand_concept_pack_fold_constraints(normal_form, root, loc);
        if (!normal_form.valid_node(root)) {
            satisfaction_exit.finish(SatisfactionResult::Unsatisfied);
            return make_value(false);
        }
        NormalizedConstraintCheckResult normalized =
            evaluate_normalized_associated_constraint(
                info,
                arguments,
                normal_form,
                root,
                loc,
                point_lookup_generation);
        switch (normalized) {
            case NormalizedConstraintCheckResult::Satisfied:
                satisfaction_exit.finish(SatisfactionResult::Satisfied);
                return make_value(true);
            case NormalizedConstraintCheckResult::Unsatisfied:
                satisfaction_exit.finish(SatisfactionResult::Unsatisfied);
                return make_value(false);
            case NormalizedConstraintCheckResult::Invalid:
                satisfaction_exit.finish(SatisfactionResult::Invalid);
                return make_error();
            case NormalizedConstraintCheckResult::Unsupported:
                break;
        }
    }

    TemplateReplayGuardScope replay_guard(collect_session_, loc);
    if (!replay_guard.active) {
        satisfaction_exit.finish(SatisfactionResult::Invalid);
        return make_error();
    }

    size_t error_watermark = collect_session_.file().errors().size();
    collect_session_.begin_speculative_parse();
    collect::Session::InstantiationScope scope =
        collect_session_.begin_template_instantiation(info,
                                                      arguments,
                                                      loc,
                                                      point_lookup_generation);
    if (!scope.active) {
        std::vector<std::pair<SrcLoc, std::string>> captured_errors(
            collect_session_.file().errors().begin() + error_watermark,
            collect_session_.file().errors().end());
        collect_session_.rollback_speculative_parse();
        for (const auto& [error_loc, message] : captured_errors) {
            collect_session_.report_error(message, error_loc);
        }
        satisfaction_exit.finish(SatisfactionResult::Invalid);
        return make_error();
    }

    ParserCheckpoint replay_checkpoint = capture_parser_checkpoint();
    bool isolate_substitution_failure =
        in_constraint_substitution_failure_context();
    bool saved_substitution_failure = constraint_substitution_failure_;
    if (isolate_substitution_failure) {
        constraint_substitution_failure_ = false;
    }
    std::vector<size_t> saved_template_argument_expression_begins =
        template_argument_expression_begins_;
    seek_raw_index(info.constraint_begin);

    pending_template_closes_ = 0;
    template_argument_expression_begins_.clear();

    collect_session_.begin_pattern_collection();
    uint64_t taint_before = collect_session_.pattern_taint();
    ParsedExpr expression = parse_constraint_expression();
    bool value_dependent =
        collect_session_.pattern_taint() != taint_before ||
        collect_session_.expr_is_dependent(expression.sem) ||
        expression.sem.references_template_value_parameter;
    bool consumed_full_expression = current_raw_index() == info.constraint_end;
    bool valid = !expression.sem.has_error;
    if (!consumed_full_expression) {
        diagnose(DiagnosticLevel::Error,
                 "expected ';' after concept constraint-expression",
                 current_loc());
        valid = false;
    }

    std::optional<bool> value;
    if (valid) {
        valid = collect_session_.evaluate_constraint_expression(
            std::move(expression.sem),
            value_dependent,
            value,
            loc_for_index(info.constraint_begin));
    }
    bool concept_substitution_failure =
        isolate_substitution_failure && constraint_substitution_failure_;
    if (isolate_substitution_failure) {
        constraint_substitution_failure_ = saved_substitution_failure;
    }

    (void)collect_session_.finish_pattern_collection();
    collect_session_.finish_template_instantiation(std::move(scope));

    std::vector<std::pair<SrcLoc, std::string>> captured_errors(
        collect_session_.file().errors().begin() + error_watermark,
        collect_session_.file().errors().end());
    std::vector<Diagnostic> captured_parser_diagnostics(
        diagnostics_.begin() + replay_checkpoint.diagnostics_size,
        diagnostics_.end());
    restore_parser_checkpoint(replay_checkpoint);
    template_argument_expression_begins_ =
        std::move(saved_template_argument_expression_begins);
    collect_session_.rollback_speculative_parse();
    if (concept_substitution_failure) {
        satisfaction_exit.finish(SatisfactionResult::Unsatisfied);
        return make_value(false);
    }
    if (!valid) {
        diagnostics_.insert(diagnostics_.end(),
                            captured_parser_diagnostics.begin(),
                            captured_parser_diagnostics.end());
        for (const auto& [error_loc, message] : captured_errors) {
            collect_session_.report_error(message, error_loc);
        }
        satisfaction_exit.finish(SatisfactionResult::Invalid);
        return make_error();
    }
    if (!value.has_value()) {
        satisfaction_exit.finish(SatisfactionResult::Dependent);
        return make_dependent(arguments);
    }

    satisfaction_exit.finish(*value ? SatisfactionResult::Satisfied
                                    : SatisfactionResult::Unsatisfied);
    return make_value(*value);
}

collect::ExprResult Parser::instantiate_template_id_expression_result(
    const collect::Session::TemplateInfo& info,
    std::vector<collect::Session::TemplateArgument> arguments,
    SrcLoc loc,
    bool qualified_name,
    std::vector<collect::Session::TemplateArgument>*
        canonical_concept_arguments_out,
    const std::vector<const collect::Session::TemplateInfo*>*
        function_candidates,
    const std::vector<collect::CandidateExplicitTemplateArguments>*
        candidate_explicit_arguments) {
    auto arguments_for_candidate =
        [&](const collect::Session::TemplateInfo& candidate)
        -> const std::vector<collect::Session::TemplateArgument>& {
        if (candidate_explicit_arguments) {
            auto found = std::find_if(
                candidate_explicit_arguments->begin(),
                candidate_explicit_arguments->end(),
                [&](const collect::CandidateExplicitTemplateArguments&
                        entry) {
                    return entry.template_entity == candidate.entity;
                });
            if (found != candidate_explicit_arguments->end()) {
                return found->arguments;
            }
        }
        return arguments;
    };
    auto candidate_was_rejected =
        [&](const collect::Session::TemplateInfo& candidate) {
        if (!candidate_explicit_arguments) {
            return false;
        }
        auto found = std::find_if(
            candidate_explicit_arguments->begin(),
            candidate_explicit_arguments->end(),
            [&](const collect::CandidateExplicitTemplateArguments& entry) {
                return entry.template_entity == candidate.entity;
            });
        return found != candidate_explicit_arguments->end() &&
            !found->viable;
    };
    if (info.is_concept) {
        return evaluate_concept_id_expression(info,
                                              std::move(arguments),
                                              loc,
                                              qualified_name,
                                              canonical_concept_arguments_out);
    }
    bool dependent_function_template_id =
        !info.is_class_template &&
        !info.is_alias_template &&
        !info.is_variable_template &&
        !info.is_concept;
    if (dependent_function_template_id) {
        dependent_function_template_id = false;
        for (const collect::Session::TemplateArgument& argument : arguments) {
            if (template_argument_is_dependent(collect_session_, argument)) {
                dependent_function_template_id = true;
                break;
            }
        }
    }
    if (dependent_function_template_id) {
        collect::ExprResult sem;
        auto append_candidate = [&](const collect::Session::TemplateInfo* candidate) {
            if (!candidate || candidate->is_class_template ||
                candidate->is_alias_template ||
                candidate->is_variable_template || candidate->is_concept ||
                !candidate->entity.valid() ||
                std::find(sem.candidates.begin(), sem.candidates.end(),
                          candidate->entity) != sem.candidates.end()) {
                return;
            }
            if (candidate_was_rejected(*candidate)) {
                return;
            }
            sem.candidates.push_back(candidate->entity);
        };
        if (function_candidates) {
            for (const collect::Session::TemplateInfo* candidate :
                 *function_candidates) {
                append_candidate(candidate);
            }
        }
        append_candidate(&info);
        if (!sem.candidates.empty()) {
            sem.entity = sem.candidates.front();
        }
        sem.type = info.pattern_type;
        sem.name = info.name;
        sem.qualified_name = qualified_name;

        sem.category = collect::ValueCategory::FunctionDesignator;
        sem.has_explicit_template_arguments = true;
        sem.explicit_template_arguments = std::move(arguments);
        if (candidate_explicit_arguments) {
            sem.candidate_explicit_template_arguments =
                *candidate_explicit_arguments;
        }
        sem.unparenthesized_id_or_member = true;
        bind_unqualified_member_template_id(sem, info.name, loc);
        return sem;
    }
    if (!info.is_class_template &&
        !info.is_alias_template &&
        !info.is_variable_template &&
        !info.is_concept) {
        collect::ExprResult sem;
        const bool followed_by_call = check(TokenType::LEFT_PAREN);
        bool has_unresolved_template_candidate = false;
        auto append_candidate =
            [&](const collect::Session::TemplateInfo* candidate) {
                if (!candidate || candidate->is_class_template ||
                    candidate->is_alias_template ||
                    candidate->is_variable_template ||
                    candidate->is_concept || !candidate->entity.valid() ||
                    std::find(sem.candidates.begin(),
                              sem.candidates.end(),
                              candidate->entity) != sem.candidates.end()) {
                    return;
                }
                if (candidate_was_rejected(*candidate)) {
                    return;
                }

                if (!followed_by_call) {
                    const auto& candidate_arguments =
                        arguments_for_candidate(*candidate);
                    collect::Session::TemplateArgumentBindings bindings;
                    if (!collect_session_
                             .bind_explicit_template_arguments_prefix_to_parameters(
                                 candidate->parameters,
                                 candidate_arguments,
                                 bindings,
                                 nullptr,
                                 collect::Session::
                                     TemplateArgumentBindingMode::
                                         FunctionExplicitPrefix)) {
                        return;
                    }
                    collect::Session::TemplateArgumentBindings completed =
                        bindings;
                    collect::Session::PatternInstantiationCallbacks callbacks;
                    configure_pattern_instantiation_callbacks(callbacks, loc);
                    if (collect_session_
                            .complete_template_argument_bindings_with_defaults(
                                *candidate,
                                completed,
                                nullptr,
                                &callbacks,
                                loc,
                                collect::Session::
                                    TemplateArgumentCompletionMode::Candidate)) {
                        cir::EntityId specialization =
                            instantiate_template_with_args(
                                *candidate,
                                collect_session_
                                    .flatten_template_argument_bindings(
                                        completed),
                                loc,
                                callbacks.point_lookup_generation);
                        if (specialization.valid() &&
                            std::find(sem.candidates.begin(),
                                      sem.candidates.end(),
                                      specialization) ==
                                sem.candidates.end()) {
                            sem.candidates.push_back(specialization);
                        }
                        return;
                    }
                }
                sem.candidates.push_back(candidate->entity);
                has_unresolved_template_candidate = true;
            };
        if (function_candidates) {
            for (const collect::Session::TemplateInfo* candidate :
                 *function_candidates) {
                append_candidate(candidate);
            }
        }
        append_candidate(&info);
        if (sem.candidates.empty()) {
            sem.has_error = true;
            return sem;
        }
        sem.entity = sem.candidates.front();
        sem.has_explicit_template_arguments =
            has_unresolved_template_candidate;
        if (has_unresolved_template_candidate) {
            sem.explicit_template_arguments = std::move(arguments);
            if (candidate_explicit_arguments) {
                sem.candidate_explicit_template_arguments =
                    *candidate_explicit_arguments;
            }
        }
        sem.type = collect_session_.file().valid(sem.entity) &&
                           collect_session_.template_info(sem.entity) == nullptr
                       ? collect_session_.file().entity(sem.entity).type
                       : info.pattern_type;
        sem.name = info.name;
        sem.qualified_name = qualified_name;
        sem.category = collect::ValueCategory::FunctionDesignator;
        sem.unparenthesized_id_or_member = true;
        bind_unqualified_member_template_id(sem, info.name, loc);
        return sem;
    }
    cir::EntityId instantiated =
        instantiate_template_with_args(info, std::move(arguments), loc);
    return template_id_expression_result(info, instantiated, loc, qualified_name);
}

Parser::ParsedExpr Parser::parse_unqualified_template_id_expression(
    const collect::Session::TemplateInfo& info,
    std::string name,
    SrcLoc loc,
    size_t begin) {
    std::vector<const collect::Session::TemplateInfo*> function_candidates;
    if (!info.is_class_template && !info.is_alias_template &&
        !info.is_variable_template && !info.is_concept) {
        function_candidates = collect_session_.function_template_infos_for_name(
            {}, name, /*include_parents=*/true);
    }
    std::vector<collect::Session::TemplateArgument> arguments;
    std::vector<collect::CandidateExplicitTemplateArguments>
        candidate_explicit_arguments;
    const collect::Session::TemplateInfo* selected_info = &info;

    bool parsed_arguments =
        parse_function_template_argument_list_for_candidates(
            info,
            function_candidates,
            arguments,
            candidate_explicit_arguments,
            loc,
            &selected_info);
    std::vector<collect::Session::TemplateArgument> canonical_concept_arguments;
    collect::ExprResult sem = parsed_arguments
        ? instantiate_template_id_expression_result(
              *selected_info,
              std::move(arguments),
              loc,
              /*qualified_name=*/false,
              selected_info->is_concept ? &canonical_concept_arguments
                                        : nullptr,
              function_candidates.empty() ? nullptr : &function_candidates,
              candidate_explicit_arguments.empty()
                  ? nullptr
                  : &candidate_explicit_arguments)
        : collect::ExprResult{};
    sem.has_error = sem.has_error || !parsed_arguments;
    sem.unparenthesized_id_or_member = true;
    NodeId syntax = make_node(NodeKind::Identifier,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              text_payload(name),
                              sem.has_error ? NodeFlagHasError : NodeFlagNone);
    if (parsed_arguments && info.is_concept && !sem.has_error) {
        record_constraint_concept_id_syntax(
            syntax,
            info,
            std::move(canonical_concept_arguments),
            /*qualified_name=*/false);
    }
    return {syntax, std::move(sem)};
}

void Parser::record_constraint_concept_id_syntax(
    NodeId syntax,
    const collect::Session::TemplateInfo& info,
    std::vector<collect::Session::TemplateArgument> arguments,
    bool qualified_name) {
    if (!info.is_concept || syntax == InvalidNodeId) {
        return;
    }
    if (constraint_concept_id_syntax_.size() <= syntax) {
        constraint_concept_id_syntax_.resize(static_cast<size_t>(syntax) + 1);
    }
    ConstraintConceptIdSyntaxInfo annotation;
    annotation.concept_entity = info.entity;
    annotation.concept_name =
        info.name.empty() ? cir::NameId{}
                          : collect_session_.file().intern_name(info.name);
    annotation.qualified_name = qualified_name;
    annotation.arguments = std::move(arguments);
    constraint_concept_id_syntax_[syntax] = std::move(annotation);
}

void Parser::record_dependent_constraint_concept_id_syntax(
    NodeId syntax,
    cir::TypeRef dependent_qualifier,
    std::string_view concept_name,
    bool qualified_name,
    size_t argument_list_begin,
    size_t argument_list_end) {
    if (syntax == InvalidNodeId || !dependent_qualifier.type.valid()) {
        return;
    }
    if (constraint_concept_id_syntax_.size() <= syntax) {
        constraint_concept_id_syntax_.resize(static_cast<size_t>(syntax) + 1);
    }
    ConstraintConceptIdSyntaxInfo annotation;
    annotation.dependent_qualifier = dependent_qualifier;
    annotation.concept_name =
        collect_session_.file().intern_name(concept_name);
    annotation.qualified_name = qualified_name;
    annotation.argument_list_begin = argument_list_begin;
    annotation.argument_list_end = argument_list_end;
    constraint_concept_id_syntax_[syntax] = std::move(annotation);
}

const Parser::ConstraintConceptIdSyntaxInfo*
Parser::constraint_concept_id_syntax_info(NodeId syntax) const {
    if (syntax == InvalidNodeId ||
        syntax >= constraint_concept_id_syntax_.size()) {
        return nullptr;
    }
    const std::optional<ConstraintConceptIdSyntaxInfo>& annotation =
        constraint_concept_id_syntax_[syntax];
    return annotation ? &*annotation : nullptr;
}

void Parser::record_constraint_fold_operand_syntax(
    NodeId syntax,
    ConstraintFoldOperandSyntaxInfo info) {
    if (syntax == InvalidNodeId) {
        return;
    }
    if (constraint_fold_operand_syntax_.size() <= syntax) {
        constraint_fold_operand_syntax_.resize(static_cast<size_t>(syntax) + 1);
    }
    constraint_fold_operand_syntax_[syntax] = std::move(info);
}

const Parser::ConstraintFoldOperandSyntaxInfo*
Parser::constraint_fold_operand_syntax_info(NodeId syntax) const {
    if (syntax == InvalidNodeId ||
        syntax >= constraint_fold_operand_syntax_.size()) {
        return nullptr;
    }
    const std::optional<ConstraintFoldOperandSyntaxInfo>& annotation =
        constraint_fold_operand_syntax_[syntax];
    return annotation ? &*annotation : nullptr;
}

bool Parser::diagnose_invalid_concept_pack_fold_pattern(NodeId syntax,
                                                        SrcLoc loc) {
    const ConstraintFoldOperandSyntaxInfo* info =
        constraint_fold_operand_syntax_info(syntax);
    if (!info) {
        return false;
    }

    bool has_concept_template_pack = false;
    bool has_other_template_parameter_pack = false;
    for (const collect::Session::ParameterPackIdentity& pack : info->packs) {
        if (pack.kind != collect::Session::ParameterPackKind::Template) {
            has_other_template_parameter_pack = true;
            continue;
        }
        const collect::Session::TemplateInfo* pack_info =
            collect_session_.template_parameter_pack_info_for_name(pack.name);
        if (pack_info && pack_info->is_concept) {
            has_concept_template_pack = true;
        } else {
            has_other_template_parameter_pack = true;
        }
    }
    if (!has_concept_template_pack || !has_other_template_parameter_pack) {
        return false;
    }

    diagnose(DiagnosticLevel::Error,
             "constraint fold over a concept template parameter pack cannot "
             "contain another unexpanded template parameter pack",
             loc);
    return true;
}

Parser::ParsedExpr Parser::parse_expression(PrecLevel min_prec) {
    if (min_prec <= PrecLevel::COMMA) {
        ParsedExpr lhs = parse_assignment_expression();
        while (match(TokenType::COMMA)) {
            Token op = last_consumed();
            ParsedExpr rhs = parse_assignment_expression();
            size_t begin = tree_.node(lhs.syntax).tokens.begin;
            NodeId syntax = make_node(NodeKind::BinaryExpr,
                                      begin,
                                      tree_.node(rhs.syntax).tokens.end,
                                      {lhs.syntax, rhs.syntax},
                                      text_payload(op.value),
                                      NodeFlagNone,
                                      static_cast<uint16_t>(BinaryOperator::Comma));
            collect::ExprResult sem =
                collect_session_.collect_binary_expr(BinaryOperator::Comma,
                                                     std::move(lhs.sem),
                                                     std::move(rhs.sem),
                                                     op.loc);
            lhs = {syntax, std::move(sem)};
        }
        return lhs;
    }
    if (min_prec <= PrecLevel::ASSIGNMENT) {
        return parse_assignment_expression();
    }
    return parse_binary_expression(min_prec);
}

Parser::ParsedExpr Parser::parse_assignment_expression() {
    if (lang_opts_.is_cxx_mode() && check(TokenType::THROW_KW)) {
        return parse_throw_expression();
    }
    if (check(TokenType::CO_YIELD_KW)) {
        return parse_yield_expression();
    }
    ParsedExpr lhs = parse_conditional_expression();
    if (!is_assignment_token(current().type)) {
        return lhs;
    }

    Token op = current();
    BinaryOperator sem_op = binary_operator_for(op.type);
    consume();
    ParsedExpr rhs = parse_assignment_expression();
    size_t begin = tree_.node(lhs.syntax).tokens.begin;
    NodeId syntax = make_node(NodeKind::BinaryExpr,
                              begin,
                              tree_.node(rhs.syntax).tokens.end,
                              {lhs.syntax, rhs.syntax},
                              text_payload(op.value),
                              NodeFlagNone,
                              static_cast<uint16_t>(sem_op));
    collect::ExprResult sem =
        collect_session_.collect_binary_expr(sem_op, std::move(lhs.sem), std::move(rhs.sem), op.loc);
    return {syntax, std::move(sem)};
}

Parser::ParsedExpr Parser::parse_throw_expression() {

    size_t begin = current_raw_index();
    SrcLoc loc = current().loc;
    consume();
    std::optional<ParsedExpr> operand;
    std::vector<NodeId> children;
    switch (current().type) {
        case TokenType::SEMICOLON:
        case TokenType::RIGHT_PAREN:
        case TokenType::RIGHT_BRACKET:
        case TokenType::RIGHT_BRACE:
        case TokenType::COMMA:
        case TokenType::COLON:
        case TokenType::Eof:
            break;
        default:
            operand = parse_assignment_expression();
            children.push_back(operand->syntax);
            break;
    }
    NodeId syntax = make_node(NodeKind::ThrowExpr,
                              begin,
                              last_consumed_raw_end(),
                              children,
                              text_payload("throw"));
    collect::ExprResult sem = collect_session_.collect_throw_expr(
        operand.has_value()
            ? std::optional<collect::ExprResult>(std::move(operand->sem))
            : std::nullopt,
        loc);
    return {syntax, std::move(sem)};
}

Parser::ParsedExpr Parser::parse_yield_expression() {

    size_t begin = current_raw_index();
    SrcLoc loc = current().loc;
    consume();
    ParsedExpr operand = check(TokenType::LEFT_BRACE)
        ? parse_init_list_expression()
        : parse_assignment_expression();
    NodeId syntax = make_node(NodeKind::YieldExpr,
                              begin,
                              last_consumed_raw_end(),
                              {operand.syntax},
                              text_payload("co_yield"));
    collect::ExprResult sem =
        collect_session_.collect_yield_expr(std::move(operand.sem), loc);
    return {syntax, std::move(sem)};
}

Parser::ParsedExpr Parser::parse_conditional_expression() {
    ParsedExpr condition = parse_binary_expression(PrecLevel::CONDITIONAL);
    if (!match(TokenType::QUESTION)) {
        return condition;
    }

    Token question = last_consumed();
    std::vector<NodeId> children{condition.syntax};
    std::optional<ParsedExpr> true_expr;
    if (!check(TokenType::COLON)) {
        true_expr = parse_expression();
        children.push_back(true_expr->syntax);
    }
    if (!match(TokenType::COLON)) {
        diagnose(DiagnosticLevel::Error, "expected ':' in conditional expression", current_loc());
    }
    ParsedExpr false_expr = parse_assignment_expression();
    children.push_back(false_expr.syntax);

    NodeId syntax = make_node(NodeKind::ConditionalExpr,
                              tree_.node(condition.syntax).tokens.begin,
                              tree_.node(false_expr.syntax).tokens.end,
                              children,
                              text_payload(true_expr.has_value() ? "?:" : "?:<omitted>"));
    std::optional<collect::ExprResult> true_sem;
    if (true_expr.has_value()) {
        true_sem = std::move(true_expr->sem);
    }
    collect::ExprResult sem =
        collect_session_.collect_conditional_expr(std::move(condition.sem),
                                                  std::move(true_sem),
                                                  std::move(false_expr.sem),
                                                  question.loc);
    return {syntax, std::move(sem)};
}

Parser::ParsedExpr Parser::parse_constraint_expression() {
    return parse_binary_expression(PrecLevel::LOGICAL_OR);
}

uint32_t Parser::expand_concept_pack_fold_constraints(
    collect::Session::NormalizedConstraint& normal_form,
    uint32_t root,
    SrcLoc loc) {
    using Session = collect::Session;
    using NodeKind = Session::NormalizedConstraintKind;
    using Fold = Session::ConstraintFoldOperator;
    using Mapping = Session::ConstraintParameterMapping;
    using TemplateArgument = Session::TemplateArgument;

    struct ConceptPackBinding {
        Session::TemplateParameterKind parameter_kind =
            Session::TemplateParameterKind::Template;
        uint32_t parameter_depth = 0;
        uint32_t parameter_index = cir::ArrayTypePayload::no_extent_param;
        cir::EntityId parameter_entity{};
        std::vector<TemplateArgument> arguments;
    };

    auto same_parameter_as = [](const ConceptPackBinding& binding,
                                const Mapping& mapping) {
        if (binding.parameter_entity.valid() ||
            mapping.parameter_entity.valid()) {
            return binding.parameter_entity == mapping.parameter_entity;
        }
        return binding.parameter_kind == mapping.parameter_kind &&
               binding.parameter_depth == mapping.parameter_depth &&
               binding.parameter_index == mapping.parameter_index;
    };
    auto is_concept_pack_mapping = [](const Mapping& mapping) {
        return mapping.parameter_kind ==
                   Session::TemplateParameterKind::Template &&
               mapping.parameter_template_template_kind ==
                   Session::TemplateTemplateParameterKind::Concept &&
               mapping.parameter_is_pack &&
               mapping.argument.kind == cir::TemplateArgumentKind::Template &&
               mapping.argument_pack.has_value();
    };
    auto argument_lists_equivalent =
        [&](const std::vector<TemplateArgument>& lhs,
            const std::vector<TemplateArgument>& rhs) {
        if (lhs.size() != rhs.size()) {
            return false;
        }
        for (size_t i = 0; i < lhs.size(); ++i) {
            if (!collect_session_.template_arguments_equivalent(lhs[i],
                                                                rhs[i])) {
                return false;
            }
        }
        return true;
    };

    auto add_or_check_binding =
        [&](std::vector<ConceptPackBinding>& bindings,
            const Mapping& mapping) {
        for (ConceptPackBinding& binding : bindings) {
            if (!same_parameter_as(binding, mapping)) {
                continue;
            }
            return argument_lists_equivalent(binding.arguments,
                                             *mapping.argument_pack);
        }

        ConceptPackBinding binding;
        binding.parameter_kind = mapping.parameter_kind;
        binding.parameter_depth = mapping.parameter_depth;
        binding.parameter_index = mapping.parameter_index;
        binding.parameter_entity = mapping.parameter_entity;
        binding.arguments = *mapping.argument_pack;
        bindings.push_back(std::move(binding));
        return true;
    };

    std::function<bool(uint32_t, std::vector<ConceptPackBinding>&)>
        collect_bindings =
            [&](uint32_t index,
                std::vector<ConceptPackBinding>& bindings) -> bool {
        if (!normal_form.valid_node(index)) {
            return false;
        }
        const auto node = normal_form.nodes[index];
        switch (node.kind) {
            case NodeKind::Atomic:
            case NodeKind::ConceptDependent:
                for (const Mapping& mapping : node.atom.parameter_mapping) {
                    if (is_concept_pack_mapping(mapping) &&
                        !add_or_check_binding(bindings, mapping)) {
                        return false;
                    }
                }
                return true;
            case NodeKind::Conjunction:
            case NodeKind::Disjunction:
                return collect_bindings(node.lhs, bindings) &&
                       collect_bindings(node.rhs, bindings);
            case NodeKind::FoldExpanded:
                return collect_bindings(node.lhs, bindings);
        }
        return true;
    };

    auto binding_for_concept_id =
        [&](const Session::NormalizedConstraintNode& node,
            const std::vector<ConceptPackBinding>& bindings)
            -> const ConceptPackBinding* {
        if (node.concept_id_template_parameter_index !=
            cir::ArrayTypePayload::no_extent_param) {
            for (const ConceptPackBinding& binding : bindings) {
                if (binding.parameter_index ==
                    node.concept_id_template_parameter_index) {
                    return &binding;
                }
            }
        }
        if (!node.concept_id_entity.valid()) {
            return nullptr;
        }
        for (const ConceptPackBinding& binding : bindings) {
            if (binding.parameter_entity.valid() &&
                node.concept_id_entity == binding.parameter_entity) {
                return &binding;
            }
        }
        const Session::TemplateInfo* concept_info =
            collect_session_.template_info(node.concept_id_entity);
        if (!concept_info) {
            return nullptr;
        }
        for (const ConceptPackBinding& binding : bindings) {
            if (!binding.parameter_entity.valid() &&
                concept_info->template_parameter_index ==
                    binding.parameter_index) {
                return &binding;
            }
        }
        return nullptr;
    };

    auto replace_pack_mapping_arguments =
        [&](Session::NormalizedConstraintNode& node,
            const std::vector<ConceptPackBinding>& bindings,
            size_t element_index) {
        for (Mapping& mapping : node.atom.parameter_mapping) {
            for (const ConceptPackBinding& binding : bindings) {
                if (!same_parameter_as(binding, mapping)) {
                    continue;
                }
                if (element_index >= binding.arguments.size()) {
                    continue;
                }
                mapping.argument = binding.arguments[element_index];
                mapping.argument_pack.reset();
                break;
            }
        }
    };

    auto append_atomic_like_node =
        [&](Session::NormalizedConstraintNode node) {
        uint32_t copied = node.kind == NodeKind::ConceptDependent
            ? normal_form.add_concept_dependent(std::move(node.atom))
            : normal_form.add_atomic(std::move(node.atom));
        normal_form.nodes[copied].concept_id_entity =
            node.concept_id_entity;
        normal_form.nodes[copied].concept_id_template_parameter_index =
            node.concept_id_template_parameter_index;
        normal_form.nodes[copied].concept_id_dependent_qualifier =
            node.concept_id_dependent_qualifier;
        normal_form.nodes[copied].concept_id_name =
            node.concept_id_name;
        normal_form.nodes[copied].concept_id_qualified_name =
            node.concept_id_qualified_name;
        normal_form.nodes[copied].concept_id_argument_list_begin =
            node.concept_id_argument_list_begin;
        normal_form.nodes[copied].concept_id_argument_list_end =
            node.concept_id_argument_list_end;
        normal_form.nodes[copied].concept_id_arguments =
            std::move(node.concept_id_arguments);
        return copied;
    };

    std::function<uint32_t(uint32_t,
                           const std::vector<ConceptPackBinding>&,
                           size_t)>
        clone_pattern_element =
            [&](uint32_t index,
                const std::vector<ConceptPackBinding>& bindings,
                size_t element_index) -> uint32_t {
        if (!normal_form.valid_node(index)) {
            return Session::NormalizedConstraint::no_node;
        }
        Session::NormalizedConstraintNode node = normal_form.nodes[index];
        switch (node.kind) {
            case NodeKind::Atomic:
            case NodeKind::ConceptDependent: {
                const ConceptPackBinding* concept_binding =
                    binding_for_concept_id(node, bindings);
                replace_pack_mapping_arguments(node,
                                               bindings,
                                               element_index);
                if (!concept_binding ||
                    element_index >= concept_binding->arguments.size()) {
                    return append_atomic_like_node(std::move(node));
                }

                const TemplateArgument& concept_argument =
                    concept_binding->arguments[element_index];
                if (concept_argument.kind !=
                    cir::TemplateArgumentKind::Template) {
                    return Session::NormalizedConstraint::no_node;
                }
                if (concept_argument.template_entity.valid()) {
                    const Session::TemplateInfo* concept_info =
                        collect_session_.template_info(
                            concept_argument.template_entity);
                    if (concept_info && concept_info->is_concept &&
                        concept_info->constraint_normal_form.has_value()) {
                        uint32_t copied =
                            normal_form.append_copy_of(
                                *concept_info->constraint_normal_form);
                        if (!normal_form.valid_node(copied)) {
                            return Session::NormalizedConstraint::no_node;
                        }
                        Session::PatternInstantiationCallbacks callbacks;
                        configure_pattern_instantiation_callbacks(callbacks,
                                                                  loc);
                        std::string substitution_error;
                        Session::TemplateArgumentBindings
                            concept_argument_bindings;
                        if (!collect_session_
                                 .bind_template_arguments_to_parameters(
                                     concept_info->parameters,
                                     node.concept_id_arguments,
                                     concept_argument_bindings)) {
                            return Session::NormalizedConstraint::no_node;
                        }
                        if (!collect_session_
                                 .compose_constraint_parameter_mappings(
                                     normal_form,
                                     copied,
                                     concept_argument_bindings,
                                     callbacks,
                                     &substitution_error)) {
                            return Session::NormalizedConstraint::no_node;
                        }
                        uint32_t expanded =
                            expand_concept_pack_fold_constraints(normal_form,
                                                                 copied,
                                                                 loc);
                        return normal_form.valid_node(expanded)
                            ? expanded
                            : Session::NormalizedConstraint::no_node;
                    }
                }

                node.concept_id_entity = concept_argument.template_entity;
                node.concept_id_template_parameter_index =
                    concept_argument.template_param_index;
                node.concept_id_name = concept_argument.template_name;
                node.concept_id_dependent_qualifier =
                    concept_argument.dependent_template_qualifier;
                return append_atomic_like_node(std::move(node));
            }
            case NodeKind::Conjunction:
            case NodeKind::Disjunction: {
                uint32_t lhs = clone_pattern_element(node.lhs,
                                                     bindings,
                                                     element_index);
                uint32_t rhs = clone_pattern_element(node.rhs,
                                                     bindings,
                                                     element_index);
                if (!normal_form.valid_node(lhs) ||
                    !normal_form.valid_node(rhs)) {
                    return Session::NormalizedConstraint::no_node;
                }
                return node.kind == NodeKind::Conjunction
                    ? normal_form.add_conjunction(lhs, rhs)
                    : normal_form.add_disjunction(lhs, rhs);
            }
            case NodeKind::FoldExpanded: {
                uint32_t lhs = clone_pattern_element(node.lhs,
                                                     bindings,
                                                     element_index);
                if (!normal_form.valid_node(lhs)) {
                    return Session::NormalizedConstraint::no_node;
                }
                uint32_t fold =
                    normal_form.add_fold_expanded(node.fold_operator, lhs);
                uint32_t expanded =
                    expand_concept_pack_fold_constraints(normal_form,
                                                         fold,
                                                         loc);
                return normal_form.valid_node(expanded)
                    ? expanded
                    : Session::NormalizedConstraint::no_node;
            }
        }
        return Session::NormalizedConstraint::no_node;
    };

    auto compose_fold_elements =
        [&](Fold op,
            uint32_t pattern,
            const std::vector<ConceptPackBinding>& bindings) {
        if (bindings.empty()) {
            return Session::NormalizedConstraint::no_node;
        }
        size_t count = bindings.front().arguments.size();
        for (const ConceptPackBinding& binding : bindings) {
            if (binding.arguments.size() != count) {
                return Session::NormalizedConstraint::no_node;
            }
        }
        if (count == 0) {
            return Session::NormalizedConstraint::no_node;
        }

        uint32_t result = Session::NormalizedConstraint::no_node;
        for (size_t i = 0; i < count; ++i) {
            uint32_t element =
                clone_pattern_element(pattern, bindings, i);
            if (!normal_form.valid_node(element)) {
                return Session::NormalizedConstraint::no_node;
            }
            if (!normal_form.valid_node(result)) {
                result = element;
                continue;
            }
            result = op == Fold::LogicalAnd
                ? normal_form.add_conjunction(result, element)
                : normal_form.add_disjunction(result, element);
        }
        return result;
    };

    std::function<uint32_t(uint32_t)> visit =
        [&](uint32_t index) -> uint32_t {
        if (!normal_form.valid_node(index)) {
            return Session::NormalizedConstraint::no_node;
        }
        Session::NormalizedConstraintNode node = normal_form.nodes[index];
        switch (node.kind) {
            case NodeKind::Atomic:
            case NodeKind::ConceptDependent:
                return index;
            case NodeKind::Conjunction:
            case NodeKind::Disjunction: {
                uint32_t lhs = visit(node.lhs);
                uint32_t rhs = visit(node.rhs);
                if (!normal_form.valid_node(lhs) ||
                    !normal_form.valid_node(rhs)) {
                    return Session::NormalizedConstraint::no_node;
                }
                normal_form.nodes[index].lhs = lhs;
                normal_form.nodes[index].rhs = rhs;
                return index;
            }
            case NodeKind::FoldExpanded: {
                uint32_t pattern = visit(node.lhs);
                if (!normal_form.valid_node(pattern)) {
                    return Session::NormalizedConstraint::no_node;
                }
                normal_form.nodes[index].lhs = pattern;

                std::vector<ConceptPackBinding> bindings;
                if (!collect_bindings(pattern, bindings)) {
                    return Session::NormalizedConstraint::no_node;
                }
                if (bindings.empty()) {
                    return index;
                }
                std::string length_error;
                if (!collect_session_
                         .constraint_concept_pack_fold_argument_lengths_match(
                             normal_form,
                             pattern,
                             &length_error)) {
                    diagnose(DiagnosticLevel::Error,
                             length_error.empty()
                                 ? "concept template parameter packs in constraint fold must have the same number of arguments"
                                 : length_error,
                             loc);
                    return Session::NormalizedConstraint::no_node;
                }
                uint32_t expanded =
                    compose_fold_elements(node.fold_operator,
                                          pattern,
                                          bindings);
                return normal_form.valid_node(expanded) ? expanded : index;
            }
        }
        return Session::NormalizedConstraint::no_node;
    };

    return visit(root);
}

uint32_t Parser::normalize_direct_constraint_expression_syntax(
    NodeId syntax,
    collect::Session::NormalizedConstraint& normal_form) {
    if (!tree_.valid(syntax)) {
        return collect::Session::NormalizedConstraint::no_node;
    }
    const Node& node = tree_.node(syntax);
    auto children = tree_.children(syntax);
    if (node.kind == NodeKind::ParenExpr && children.size() == 1) {
        return normalize_direct_constraint_expression_syntax(children[0],
                                                             normal_form);
    }
    if (node.kind == NodeKind::BinaryExpr && children.size() == 2) {
        BinaryOperator op = static_cast<BinaryOperator>(node.opcode);
        if (op == BinaryOperator::LogicalAnd ||
            op == BinaryOperator::LogicalOr) {
            uint32_t lhs =
                normalize_direct_constraint_expression_syntax(children[0],
                                                              normal_form);
            uint32_t rhs =
                normalize_direct_constraint_expression_syntax(children[1],
                                                              normal_form);
            if (!normal_form.valid_node(lhs) ||
                !normal_form.valid_node(rhs)) {
                return collect::Session::NormalizedConstraint::no_node;
            }
            return op == BinaryOperator::LogicalAnd
                ? normal_form.add_conjunction(lhs, rhs)
                : normal_form.add_disjunction(lhs, rhs);
        }
    }
    if (node.kind == NodeKind::AmbiguousSyntax) {
        std::string_view fold_kind = node_text(node);
        bool unary_fold = fold_kind == "unary-left-fold" ||
                          fold_kind == "unary-right-fold";
        bool binary_right_fold = fold_kind == "binary-right-fold";
        bool binary_left_fold = fold_kind == "binary-left-fold";
        bool binary_fold = binary_right_fold || binary_left_fold;
        if (unary_fold || binary_fold) {
            auto constraint_fold_operator =
                [&]() -> std::optional<
                    collect::Session::ConstraintFoldOperator> {
                size_t begin = node.tokens.begin;
                size_t end = std::min(node.tokens.end, tokens_.size());
                auto logical_operator_at =
                    [&](size_t index)
                    -> std::optional<
                        collect::Session::ConstraintFoldOperator> {
                    if (index >= tokens_.size()) {
                        return std::nullopt;
                    }
                    BinaryOperator op =
                        binary_operator_for(tokens_[index].type);
                    if (op == BinaryOperator::LogicalAnd) {
                        return collect::Session::ConstraintFoldOperator::
                            LogicalAnd;
                    }
                    if (op == BinaryOperator::LogicalOr) {
                        return collect::Session::ConstraintFoldOperator::
                            LogicalOr;
                    }
                    return std::nullopt;
                };
                for (size_t i = begin; i < end; ++i) {
                    if (tokens_[i].type != TokenType::ELLIPSIS) {
                        continue;
                    }
                    if (i > begin) {
                        if (auto before = logical_operator_at(i - 1)) {
                            return before;
                        }
                    }
                    if (i + 1 < end) {
                        if (auto after = logical_operator_at(i + 1)) {
                            return after;
                        }
                    }
                    break;
                }
                return std::nullopt;
            }();
            auto add_logical_fold_composition =
                [&](uint32_t lhs,
                    uint32_t rhs,
                    collect::Session::ConstraintFoldOperator op)
                -> uint32_t {
                return op == collect::Session::ConstraintFoldOperator::
                                 LogicalAnd
                    ? normal_form.add_conjunction(lhs, rhs)
                    : normal_form.add_disjunction(lhs, rhs);
            };
            auto fold_expansion_parameters =
                [&](NodeId operand_syntax)
                -> std::vector<
                    collect::Session::ConstraintFoldExpansionParameter> {
                using FoldParameter =
                    collect::Session::ConstraintFoldExpansionParameter;
                using FoldParameterKind =
                    collect::Session::ConstraintFoldExpansionParameterKind;

                std::vector<FoldParameter> parameters;
                const ConstraintFoldOperandSyntaxInfo* info =
                    constraint_fold_operand_syntax_info(operand_syntax);
                if (!info) {
                    return parameters;
                }

                for (const collect::Session::ParameterPackIdentity& pack :
                     info->packs) {
                    FoldParameter parameter;
                    parameter.name = pack.name;
                    parameter.parameter_depth = pack.depth;
                    parameter.parameter_index = pack.index;
                    parameter.owning_template_entity = pack.owner;
                    switch (pack.kind) {
                        case collect::Session::ParameterPackKind::Function:
                            parameter.kind = FoldParameterKind::Function;
                            break;
                        case collect::Session::ParameterPackKind::Type: {
                            parameter.kind = FoldParameterKind::Type;
                            if (auto type =
                                    collect_session_.type_parameter_pack_type(
                                        pack.name)) {
                                parameter.type_parameter_pack_type = *type;
                                parameter.argument.kind =
                                    cir::TemplateArgumentKind::Type;
                                parameter.argument.type =
                                    collect_session_.type_ref(*type);
                                parameter.argument.is_dependent = true;
                            }
                            break;
                        }
                        case collect::Session::ParameterPackKind::Value:
                            parameter.kind = FoldParameterKind::Value;
                            parameter.argument.kind =
                                cir::TemplateArgumentKind::Value;
                            parameter.argument.value_param_index = pack.index;
                            parameter.argument.value_spelling = pack.name;
                            parameter.argument.is_dependent = true;
                            break;
                        case collect::Session::ParameterPackKind::Template: {
                            parameter.kind = FoldParameterKind::Template;
                            parameter.parameter_entity = pack.declaration;
                            parameter.argument.kind =
                                cir::TemplateArgumentKind::Template;
                            parameter.argument.template_entity =
                                pack.declaration;
                            parameter.argument.template_param_index =
                                pack.index;
                            parameter.argument.is_dependent = true;
                            if (const collect::Session::TemplateInfo* info =
                                    collect_session_
                                        .template_parameter_pack_info_for_name(
                                            pack.name)) {
                                parameter.template_template_parameter_kind =
                                    info->is_concept
                                        ? collect::Session::
                                              TemplateTemplateParameterKind::Concept
                                        : collect::Session::
                                              TemplateTemplateParameterKind::Type;
                            }
                            break;
                        }
                    }
                    parameters.push_back(std::move(parameter));
                }
                return parameters;
            };
            if (constraint_fold_operator.has_value() &&
                ((unary_fold && children.size() == 1) ||
                 (binary_fold && children.size() == 2))) {
                NodeId pattern_syntax =
                    binary_left_fold ? children[1] : children[0];
                if (diagnose_invalid_concept_pack_fold_pattern(
                        pattern_syntax,
                        node.loc)) {
                    return collect::Session::NormalizedConstraint::no_node;
                }
                uint32_t pattern =
                    normalize_direct_constraint_expression_syntax(
                        pattern_syntax,
                        normal_form);
                if (!normal_form.valid_node(pattern)) {
                    return collect::Session::NormalizedConstraint::no_node;
                }
                uint32_t fold =
                    normal_form.add_fold_expanded(
                        *constraint_fold_operator,
                        pattern,
                        fold_expansion_parameters(pattern_syntax));
                if (unary_fold) {
                    return expand_concept_pack_fold_constraints(normal_form,
                                                                fold,
                                                                node.loc);
                }

                NodeId init_syntax =
                    binary_left_fold ? children[0] : children[1];
                uint32_t init =
                    normalize_direct_constraint_expression_syntax(init_syntax,
                                                                  normal_form);
                if (!normal_form.valid_node(init)) {
                    return collect::Session::NormalizedConstraint::no_node;
                }
                uint32_t composed = binary_left_fold
                    ? add_logical_fold_composition(
                          init,
                          fold,
                          *constraint_fold_operator)
                    : add_logical_fold_composition(
                          fold,
                          init,
                          *constraint_fold_operator);
                return expand_concept_pack_fold_constraints(normal_form,
                                                            composed,
                                                            node.loc);
            }
        }
    }

    if (const ConstraintConceptIdSyntaxInfo* concept_id =
            constraint_concept_id_syntax_info(syntax)) {
        const collect::Session::TemplateInfo* concept_info =
            collect_session_.template_info(concept_id->concept_entity);
        auto concept_entity_is_template_parameter = [&]() {
            return concept_id->concept_entity.valid() &&
                   collect_session_.file().valid(concept_id->concept_entity) &&
                   collect_session_.file()
                           .entity(concept_id->concept_entity)
                           .kind == cir::EntityKind::TemplateParam;
        };
        if (concept_id->is_dependent_concept_id() ||
            (concept_info && concept_info->is_concept &&
             concept_entity_is_template_parameter())) {
            collect::Session::ConstraintAtomIdentity atom;
            atom.expression_begin = node.tokens.begin;
            atom.expression_end = node.tokens.end;
            if (concept_info && concept_entity_is_template_parameter() &&
                concept_info->template_parameter_index !=
                    cir::ArrayTypePayload::no_extent_param) {
                collect::Session::ConstraintParameterMapping mapping;
                mapping.parameter_kind =
                    collect::Session::TemplateParameterKind::Template;
                mapping.parameter_index =
                    concept_info->template_parameter_index;
                mapping.parameter_template_template_kind =
                    collect::Session::TemplateTemplateParameterKind::Concept;
                mapping.parameter_is_pack =
                    concept_info->is_template_parameter_pack;
                mapping.argument.kind = cir::TemplateArgumentKind::Template;
                mapping.argument.template_param_index =
                    concept_info->template_parameter_index;
                mapping.argument.is_dependent = true;
                atom.parameter_mapping.push_back(std::move(mapping));
            }
            uint32_t dependent =
                normal_form.add_concept_dependent(std::move(atom));
            normal_form.nodes[dependent].concept_id_entity =
                concept_id->concept_entity;
            normal_form.nodes[dependent].concept_id_template_parameter_index =
                concept_info && concept_entity_is_template_parameter()
                    ? concept_info->template_parameter_index
                    : cir::ArrayTypePayload::no_extent_param;
            normal_form.nodes[dependent].concept_id_dependent_qualifier =
                concept_id->dependent_qualifier;
            normal_form.nodes[dependent].concept_id_name =
                concept_id->concept_name;
            normal_form.nodes[dependent].concept_id_qualified_name =
                concept_id->qualified_name;
            normal_form.nodes[dependent].concept_id_argument_list_begin =
                concept_id->argument_list_begin;
            normal_form.nodes[dependent].concept_id_argument_list_end =
                concept_id->argument_list_end;
            normal_form.nodes[dependent].concept_id_arguments =
                concept_id->arguments;
            return dependent;
        }
        if (concept_info && concept_info->is_concept &&
            concept_info->constraint_normal_form.has_value()) {
            uint32_t copied =
                normal_form.append_copy_of(*concept_info
                                                ->constraint_normal_form);
            if (normal_form.valid_node(copied)) {
                collect::Session::PatternInstantiationCallbacks callbacks;
                configure_pattern_instantiation_callbacks(callbacks,
                                                          node.loc);
                std::string substitution_error;
                collect::Session::TemplateArgumentBindings
                    concept_argument_bindings;
                if (!collect_session_
                         .bind_template_arguments_to_parameters(
                             concept_info->parameters,
                             concept_id->arguments,
                             concept_argument_bindings)) {
                    return collect::Session::NormalizedConstraint::no_node;
                }
                if (collect_session_.compose_constraint_parameter_mappings(
                        normal_form,
                        copied,
                        concept_argument_bindings,
                        callbacks,
                        &substitution_error)) {
                    uint32_t expanded =
                        expand_concept_pack_fold_constraints(normal_form,
                                                             copied,
                                                             node.loc);
                    return normal_form.valid_node(expanded)
                        ? expanded
                        : collect::Session::NormalizedConstraint::no_node;
                }
                return collect::Session::NormalizedConstraint::no_node;
            }
        }
    }

    collect::Session::ConstraintAtomIdentity atom;
    atom.expression_begin = node.tokens.begin;
    atom.expression_end = node.tokens.end;
    uint32_t atomic = normal_form.add_atomic(std::move(atom));
    if (const ConstraintConceptIdSyntaxInfo* concept_id =
            constraint_concept_id_syntax_info(syntax)) {
        normal_form.nodes[atomic].concept_id_entity =
            concept_id->concept_entity;
        normal_form.nodes[atomic].concept_id_arguments =
            concept_id->arguments;
        normal_form.nodes[atomic].concept_id_argument_list_begin =
            concept_id->argument_list_begin;
        normal_form.nodes[atomic].concept_id_argument_list_end =
            concept_id->argument_list_end;
    }
    return atomic;
}

void Parser::stamp_constraint_declaration_keys(
    collect::Session::NormalizedConstraint& normal_form,
    const std::vector<collect::Session::TemplateParameter>& parameters) {
    for (collect::Session::NormalizedConstraintNode& node : normal_form.nodes) {
        if (node.kind != collect::Session::NormalizedConstraintKind::Atomic ||
            node.atom.appearance_owner.valid() ||
            node.atom.expression_end <= node.atom.expression_begin) {

            continue;
        }
        uint64_t hash = 1469598103934665603ull;
        auto mix = [&hash](std::string_view text) {
            for (unsigned char ch : text) {
                hash ^= ch;
                hash *= 1099511628211ull;
            }
            hash ^= 0x1fu;
            hash *= 1099511628211ull;
        };
        for (size_t index = node.atom.expression_begin;
             index < node.atom.expression_end && index < cooked_to_raw_.size();
             ++index) {
            const Token& token = tokens_[cooked_to_raw_[index]];
            bool mapped = false;
            if (is_identifier_token(token.type)) {
                for (size_t j = 0; j < parameters.size(); ++j) {
                    if (!parameters[j].name.empty() &&
                        parameters[j].name == token.value) {
                        char slot[24];
                        int written = std::snprintf(slot, sizeof(slot),
                                                    "\x01%zu", j);
                        if (written > 0) {
                            mix(std::string_view(slot,
                                                 static_cast<size_t>(written)));
                        }
                        mapped = true;
                        break;
                    }
                }
            }
            if (!mapped) {
                char kind[16];
                int written = std::snprintf(kind, sizeof(kind), "\x02%u",
                                            static_cast<unsigned>(token.type));
                if (written > 0) {
                    mix(std::string_view(kind, static_cast<size_t>(written)));
                }
                mix(token.value);
            }
        }
        node.atom.declaration_equivalence_key = hash == 0 ? 1 : hash;
    }
}

bool Parser::parse_and_validate_constraint_expression(SrcLoc loc,
                                                      size_t& begin,
                                                      size_t& end,
                                                      std::optional<bool>* value_out,
                                                      collect::Session::
                                                          NormalizedConstraint*
                                                              normal_form_out) {
    begin = current_raw_index();

    bool owns_pattern_collection = !collect_session_.collecting_pattern();
    if (owns_pattern_collection) {
        collect_session_.begin_pattern_collection();
    }
    uint64_t taint_before = collect_session_.pattern_taint();
    bool saved_retain_constraint_normal_form_syntax =
        retain_constraint_normal_form_syntax_;
    ++requires_expression_template_context_depth_;
    retain_constraint_normal_form_syntax_ = normal_form_out != nullptr;
    ParsedExpr expression = parse_constraint_expression();
    retain_constraint_normal_form_syntax_ =
        saved_retain_constraint_normal_form_syntax;
    --requires_expression_template_context_depth_;
    end = current_raw_index();
    if (normal_form_out) {
        collect::Session::NormalizedConstraint normal_form;
        uint32_t root =
            normalize_direct_constraint_expression_syntax(expression.syntax,
                                                          normal_form);
        if (normal_form.valid_node(root)) {
            normal_form.root = root;
            normal_form.value_expression =
                expression.sem.template_value_expr;
            collect_session_.file().canonicalize_template_value_expression(
                normal_form.value_expression);
            *normal_form_out = std::move(normal_form);
        } else {
            *normal_form_out = {};
        }
    }
    bool value_dependent =
        collect_session_.pattern_taint() != taint_before ||
        collect_session_.expr_is_dependent(expression.sem) ||
        expression.sem.references_template_value_parameter;
    bool valid = !expression.sem.has_error;
    if (valid) {
        std::optional<bool> value;
        valid = collect_session_.evaluate_constraint_expression(
            std::move(expression.sem),
            value_dependent,
            value,
            loc);
        if (value_out) {
            *value_out = value;
        }
    } else if (value_out) {
        value_out->reset();
    }
    if (owns_pattern_collection) {
        (void)collect_session_.finish_pattern_collection();
    }
    return valid;
}

bool Parser::parse_requires_parameter_list(
    std::vector<NodeId>& children,
    collect::Session::PrototypeParameterScope& parameter_scope) {
    size_t diagnostic_watermark = diagnostics_.size();
    size_t error_watermark = collect_session_.file().errors().size();
    bool is_variadic = false;
    (void)parse_parameter_list(
        false,
        TypeParseContext::type_only(
            TypeParseContext::Origin::RequirementParameter),
        &is_variadic,
        [&](ParsedParam& parameter, uint32_t) {
            if (parameter.syntax != InvalidNodeId) {
                children.push_back(parameter.syntax);
            }
            collect::Session::TemplateInfo::FunctionConstraintParameter recipe;
            recipe.name = parameter.name;
            recipe.type = parameter.type_ref;
            recipe.loc = parameter.loc;
            recipe.is_parameter_pack = parameter.is_parameter_pack;
            recipe.source_parameter_pack_name =
                parameter.source_parameter_pack_name;
            recipe.is_parameter_pack_expansion_sentinel =
                parameter.is_parameter_pack_expansion_sentinel;
            recipe.type_originates_from_template_parameter =
                parameter.type_originates_from_template_parameter;
            collect_session_.bind_prototype_parameter(parameter_scope,
                                                      recipe);
        },
        ParameterListPolicy::RequirementLocal);
    return diagnostics_.size() == diagnostic_watermark &&
        collect_session_.file().errors().size() == error_watermark &&
        !is_variadic;
}

Parser::ParsedRequiresRequirement Parser::parse_requires_type_requirement() {
    size_t begin = current_raw_index();
    SrcLoc loc = current().loc;
    consume();

    std::vector<NodeId> children;
    cir::TypeRef type;
    bool type_originates_from_template_parameter = false;
    bool valid = true;
    bool qualified_type_name =
        check(TokenType::SCOPE_RESOLUTION) ||
        (is_identifier_token(current().type) &&
         (peek(1).type == TokenType::SCOPE_RESOLUTION ||
          template_id_precedes_scope(0)));

    if (qualified_type_name) {
        if (auto parsed = parse_cxx_qualified_type_name(
                TypeParseContext::type_only(
                    TypeParseContext::Origin::TypeRequirement))) {
            type = *parsed;
        } else {
            valid = false;
            type = collect_session_.type_ref(
                collect_session_.file().unknown_type());
        }
    } else if (is_identifier_token(current().type)) {
        cir::TypeId type_id{};
        NodeId type_syntax =
            parse_type_name(&type_id,
                            nullptr,
                            nullptr,
                            &type,
                            nullptr,
                            &type_originates_from_template_parameter);
        children.push_back(type_syntax);
    } else {
        diagnose(DiagnosticLevel::Error,
                 "expected type name in type requirement",
                 current_loc());
        valid = false;
        type = collect_session_.type_ref(
            collect_session_.file().unknown_type());
    }

    if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ';' after type requirement",
                 current_loc());
        valid = false;
    }

    bool dependent =
        (type.valid() && collect_session_.is_dependent_type(type.type)) ||
        type_originates_from_template_parameter;
    NodeId syntax = make_node(
        NodeKind::TypeName,
        begin,
        last_consumed_raw_end(),
        children,
        text_payload(collect_session_.file().format_type(type)));
    return {syntax, dependent, valid};
}

Parser::ParsedRequiresRequirement Parser::parse_requires_compound_requirement() {
    size_t begin = current_raw_index();
    consume();

    ParsedExpr expression = parse_expression();
    bool saw_close = match(TokenType::RIGHT_BRACE);
    if (!saw_close) {
        diagnose(DiagnosticLevel::Error,
                 "expected '}' after compound requirement expression",
                 current_loc());
    }

    bool has_noexcept = match(TokenType::NOEXCEPT_KW);
    bool valid = !expression.sem.has_error && saw_close;
    bool dependent =
        collect_session_.expr_is_dependent(expression.sem) ||
        expression.sem.references_template_value_parameter;
    if (has_noexcept && valid) {
        bool noexcept_dependent = false;
        bool potentially_throwing =
            collect_session_.expression_potentially_throws(
                expression.sem,
                &noexcept_dependent);
        dependent = dependent || noexcept_dependent;
        if (potentially_throwing && !noexcept_dependent) {
            diagnose(DiagnosticLevel::Error,
                     "compound requirement expression is potentially throwing",
                     tree_.node(expression.syntax).loc);
            valid = false;
        }
    }

    if (match(TokenType::ARROW)) {
        std::optional<ParsedTypeConstraint> type_constraint =
            try_parse_type_constraint();
        if (!type_constraint.has_value()) {
            diagnose(DiagnosticLevel::Error,
                     "expected type-constraint after '->' in compound requirement",
                     current_loc());
            valid = false;
            while (!at_end() && !check(TokenType::SEMICOLON) &&
                   !check(TokenType::RIGHT_BRACE)) {
                consume();
            }
        } else {
            valid = valid && !type_constraint->has_error;
            if (valid) {
                cir::TypeRef result_type =
                    collect_session_.resolve_decltype_expr_type(
                        expression.sem,
                        /*use_declared_type_rule=*/false,
                        tree_.node(expression.syntax).loc);
                bool constraint_dependent = false;
                bool constraint_satisfied = false;
                bool constraint_valid =
                    evaluate_type_constraint_for_constrained_type(
                        *type_constraint,
                        result_type,
                        type_constraint->loc,
                        constraint_dependent,
                        constraint_satisfied);
                dependent = dependent || constraint_dependent;
                valid = constraint_valid && constraint_satisfied;
                if (constraint_valid && !constraint_satisfied) {
                    diagnose(DiagnosticLevel::Error,
                             "compound requirement return type constraint is not satisfied",
                             type_constraint->loc);
                }
            }
        }
    }

    if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ';' after compound requirement",
                 current_loc());
        valid = false;
    }

    NodeId syntax = make_node(NodeKind::BlockExpr,
                              begin,
                              last_consumed_raw_end(),
                              {expression.syntax},
                              text_payload("compound-requirement"));
    return {syntax, dependent, valid};
}

Parser::ParsedRequiresRequirement Parser::parse_requires_nested_requirement() {
    size_t begin = current_raw_index();
    SrcLoc loc = current().loc;
    consume();

    uint64_t taint_before = collect_session_.pattern_taint();
    bool saved_retain_constraint_normal_form_syntax =
        retain_constraint_normal_form_syntax_;
    ++requires_expression_template_context_depth_;
    retain_constraint_normal_form_syntax_ = true;
    ParsedExpr expression = parse_constraint_expression();
    retain_constraint_normal_form_syntax_ =
        saved_retain_constraint_normal_form_syntax;
    --requires_expression_template_context_depth_;

    bool saw_semicolon = match(TokenType::SEMICOLON);
    if (!saw_semicolon) {
        diagnose(DiagnosticLevel::Error,
                 "expected ';' after nested requirement",
                 current_loc());
    }

    bool dependent =
        collect_session_.pattern_taint() != taint_before ||
        collect_session_.expr_is_dependent(expression.sem) ||
        expression.sem.references_template_value_parameter;
    bool valid = !expression.sem.has_error && saw_semicolon;

    auto diagnose_unsatisfied = [&]() {
        diagnose(DiagnosticLevel::Error,
                 "nested requirement is not satisfied",
                 tree_.node(expression.syntax).loc);
    };

    bool evaluated = false;
    if (valid && !dependent) {
        collect::Session::NormalizedConstraint normal_form;
        uint32_t root =
            normalize_direct_constraint_expression_syntax(expression.syntax,
                                                          normal_form);
        if (normal_form.valid_node(root)) {
            normal_form.root = root;
            collect::Session::TemplateInfo dummy_info;
            NormalizedConstraintCheckResult result =
                evaluate_normalized_associated_constraint(
                    dummy_info,
                    {},
                    normal_form,
                    collect::Session::NormalizedConstraint::no_node,
                    loc,
                    /*point_lookup_generation=*/0);
            switch (result) {
                case NormalizedConstraintCheckResult::Satisfied:
                    evaluated = true;
                    break;
                case NormalizedConstraintCheckResult::Unsatisfied:
                    evaluated = true;
                    valid = false;
                    diagnose_unsatisfied();
                    break;
                case NormalizedConstraintCheckResult::Invalid:
                    evaluated = true;
                    valid = false;
                    break;
                case NormalizedConstraintCheckResult::Unsupported:
                    break;
            }
        }
    }

    if (valid && !evaluated) {
        std::optional<bool> value;
        valid = collect_session_.evaluate_constraint_expression(
            std::move(expression.sem),
            dependent,
            value,
            loc);
        if (valid && value.has_value() && !*value) {
            valid = false;
            diagnose_unsatisfied();
        }
        if (valid && !value.has_value()) {
            dependent = true;
        }
    }

    NodeId syntax = make_node(NodeKind::UnaryExpr,
                              begin,
                              last_consumed_raw_end(),
                              {expression.syntax},
                              text_payload("nested-requirement"));
    return {syntax, dependent, valid};
}

Parser::ParsedExpr Parser::parse_requires_expression() {
    size_t begin = current_raw_index();
    SrcLoc loc = current().loc;
    consume();

    std::vector<NodeId> children;
    bool has_error = false;
    bool value = true;
    bool value_dependent = false;

    auto failures_evaluate_false = [&]() {
        return requires_expression_template_context_depth_ > 0 ||
               in_constraint_substitution_failure_context() ||
               collect_session_.in_template_definition() ||
               collect_session_.in_template_instantiation();
    };

    auto skip_requirement = [&]() {
        int parens = 0;
        int brackets = 0;
        int braces = 0;
        while (!at_end()) {
            TokenType type = current().type;
            if (type == TokenType::SEMICOLON && parens == 0 &&
                brackets == 0 && braces == 0) {
                consume();
                return;
            }
            if (type == TokenType::RIGHT_BRACE && parens == 0 &&
                brackets == 0 && braces == 0) {
                return;
            }
            consume();
            if (type == TokenType::LEFT_PAREN) {
                ++parens;
            } else if (type == TokenType::RIGHT_PAREN && parens > 0) {
                --parens;
            } else if (type == TokenType::LEFT_BRACKET) {
                ++brackets;
            } else if (type == TokenType::RIGHT_BRACKET && brackets > 0) {
                --brackets;
            } else if (type == TokenType::LEFT_BRACE) {
                ++braces;
            } else if (type == TokenType::RIGHT_BRACE && braces > 0) {
                --braces;
            }
        }
    };

    auto requirement_is_dependent = [](const collect::ExprResult& expr) {
        return expr.references_template_value_parameter;
    };

    collect::Session::PrototypeParameterScope parameter_scope;
    auto close_parameter_scope = [&]() {
        if (!parameter_scope.active) {
            return;
        }
        collect_session_.finish_prototype_parameter_scope(
            std::move(parameter_scope));
        parameter_scope = {};
    };

    if (match(TokenType::LEFT_PAREN)) {
        size_t parameter_diagnostic_watermark = diagnostics_.size();
        collect_session_.begin_speculative_parse();
        parameter_scope =
            collect_session_.begin_prototype_parameter_scope();
        bool valid_parameters =
            parse_requires_parameter_list(children, parameter_scope);
        bool substitution_failure =
            !valid_parameters &&
            (in_constraint_substitution_failure_context() ||
             collect_session_.in_template_instantiation());
        if (substitution_failure) {

            close_parameter_scope();
            collect_session_.rollback_speculative_parse();
            diagnostics_.resize(parameter_diagnostic_watermark);
            value = false;
        } else {
            collect_session_.commit_speculative_parse();
        }
        if (!valid_parameters && !substitution_failure) {
            has_error = true;
        }
    }

    if (!match(TokenType::LEFT_BRACE)) {
        diagnose(DiagnosticLevel::Error,
                 "expected requirement body after 'requires'",
                 current_loc());
        close_parameter_scope();
        NodeId syntax = make_node(NodeKind::RequiresExpr,
                                  begin,
                                  last_consumed_raw_end(),
                                  children,
                                  {},
                                  NodeFlagHasError);
        collect::ExprResult sem =
            collect_session_.make_boolean_literal(false, "false", loc);
        sem.has_error = true;
        return {syntax, std::move(sem)};
    }

    if (check(TokenType::RIGHT_BRACE)) {
        diagnose(DiagnosticLevel::Error,
                 "expected requirement in requires-expression",
                 current_loc());
        has_error = true;
    }

    while (!at_end() && !check(TokenType::RIGHT_BRACE)) {
        if (!value || has_error) {
            skip_requirement();
            continue;
        }

        ParserCheckpoint checkpoint = capture_parser_checkpoint();
        size_t error_watermark = collect_session_.file().errors().size();
        size_t child_count_before = children.size();
        collect_session_.begin_speculative_parse();

        bool dependent = false;
        bool valid = true;
        uint64_t requirement_taint_before =
            collect_session_.pattern_taint();
        collect_session_.begin_unevaluated_operand();
        if (check(TokenType::LEFT_BRACE)) {
            ParsedRequiresRequirement requirement =
                parse_requires_compound_requirement();
            children.push_back(requirement.syntax);
            dependent = requirement.dependent;
            valid = requirement.valid;
        } else if (check(TokenType::REQUIRES_KW)) {
            ParsedRequiresRequirement requirement =
                parse_requires_nested_requirement();
            children.push_back(requirement.syntax);
            dependent = requirement.dependent;
            valid = requirement.valid;
        } else if (check(TokenType::TYPENAME)) {
            ParsedRequiresRequirement requirement =
                parse_requires_type_requirement();
            children.push_back(requirement.syntax);
            dependent = requirement.dependent;
            valid = requirement.valid;
        } else {
            ParsedExpr requirement = parse_expression();
            children.push_back(requirement.syntax);
            bool saw_semicolon = match(TokenType::SEMICOLON);
            dependent =
                collect_session_.expr_is_dependent(requirement.sem) ||
                requirement_is_dependent(requirement.sem);
            valid = !requirement.sem.has_error && saw_semicolon;
            if (!saw_semicolon) {
                diagnose(DiagnosticLevel::Error,
                         "expected ';' after simple requirement",
                         current_loc());
            }
        }
        collect_session_.end_unevaluated_operand();

        dependent = dependent ||
            collect_session_.pattern_taint() != requirement_taint_before;

        bool parser_had_error =
            std::any_of(diagnostics_.begin() + checkpoint.diagnostics_size,
                        diagnostics_.end(),
                        [](const Diagnostic& diagnostic) {
                            return diagnostic.level == DiagnosticLevel::Error;
                        });
        std::vector<std::pair<SrcLoc, std::string>> captured_errors(
            collect_session_.file().errors().begin() + error_watermark,
            collect_session_.file().errors().end());
        collect_session_.rollback_speculative_parse();
        valid = valid && !parser_had_error && captured_errors.empty();

        if (valid) {
            value_dependent = value_dependent || dependent;
            continue;
        }

        if (failures_evaluate_false()) {
            restore_parser_checkpoint(checkpoint);
            children.resize(child_count_before);
            value = false;
            skip_requirement();
            continue;
        }

        for (const auto& [error_loc, message] : captured_errors) {
            collect_session_.report_error(message, error_loc);
        }
        has_error = true;
    }

    if (!match(TokenType::RIGHT_BRACE)) {
        diagnose(DiagnosticLevel::Error,
                 "expected '}' after requires-expression body",
                 current_loc());
        has_error = true;
    }

    close_parameter_scope();

    uint16_t flags = has_error ? NodeFlagHasError : NodeFlagNone;
    NodeId syntax = make_node(NodeKind::RequiresExpr,
                              begin,
                              last_consumed_raw_end(),
                              children,
                              {},
                              flags);
    collect::ExprResult sem;
    if (has_error) {
        sem = collect_session_.make_boolean_literal(false, "false", loc);
        sem.has_error = true;
    } else if (value_dependent) {
        sem = collect_session_.make_dependent_boolean_expr(loc);
    } else {
        sem = collect_session_.make_boolean_literal(value,
                                                    value ? "true" : "false",
                                                    loc);
    }
    return {syntax, std::move(sem)};
}

NodeId Parser::retain_replayed_fold_operand_syntax(
    size_t operand_cursor,
    size_t operand_last_consumed_raw_end,
    size_t operand_end_cursor,
    SrcLoc ellipsis_loc) {
    cursor_ = operand_cursor;
    last_consumed_raw_end_ = operand_last_consumed_raw_end;
    collect_session_.begin_speculative_parse();
    auto capture_scope =
        collect_session_.begin_parameter_pack_pattern_capture();
    ParsedExpr operand = parse_cast_expression();
    ConstraintFoldOperandSyntaxInfo fold_operand_info;
    fold_operand_info.packs =
        collect_session_.finish_parameter_pack_pattern_capture(capture_scope);
    collect_session_.rollback_speculative_parse();
    record_constraint_fold_operand_syntax(operand.syntax,
                                          std::move(fold_operand_info));
    if (cursor_ != operand_end_cursor) {
        diagnose(DiagnosticLevel::Error,
                 "could not replay fold expression operand",
                 ellipsis_loc);
        cursor_ = operand_end_cursor;
    }
    return operand.syntax;
}

Parser::ParsedExpr Parser::retain_replayed_fold_operand_semantics(
    size_t operand_cursor,
    size_t operand_last_consumed_raw_end,
    size_t operand_end_cursor,
    size_t restore_cursor,
    size_t restore_last_consumed_raw_end,
    SrcLoc ellipsis_loc,
    std::vector<collect::Session::ParameterPackIdentity>* packs) {
    cursor_ = operand_cursor;
    last_consumed_raw_end_ = operand_last_consumed_raw_end;
    auto capture_scope =
        collect_session_.begin_parameter_pack_pattern_capture();
    ParsedExpr operand = parse_cast_expression();
    std::vector<collect::Session::ParameterPackIdentity> retained_packs =
        collect_session_.finish_parameter_pack_pattern_capture(capture_scope);
    if (cursor_ != operand_end_cursor) {
        diagnose(DiagnosticLevel::Error,
                 "could not retain fold expression operand",
                 ellipsis_loc);
    }
    if (packs) {
        *packs = std::move(retained_packs);
    }
    cursor_ = restore_cursor;
    last_consumed_raw_end_ = restore_last_consumed_raw_end;
    return operand;
}

Parser::ParsedExpr Parser::parse_binary_expression(PrecLevel min_prec) {
    ParsedExpr lhs = parse_cast_expression();
    while (!at_end()) {
        if (constraint_expression_replay_end_ != SIZE_MAX &&
            current_raw_index() >= constraint_expression_replay_end_) {
            break;
        }
        if (at_template_argument_expression_close()) {
            break;
        }
        PrecLevel prec = get_prec(current().type);
        if (prec < min_prec || current().type == TokenType::QUESTION ||
            current().type == TokenType::COMMA ||
            is_assignment_token(current().type)) {
            break;
        }
        size_t begin = tree_.node(lhs.syntax).tokens.begin;
        Token op = current();
        BinaryOperator sem_op = binary_operator_for(op.type);
        consume();
        PrecLevel rhs_min = is_right_associative(op.type) ? prec : next_prec_level(prec);
        std::optional<bool> constraint_short_circuit;
        if (requires_expression_template_context_depth_ > 0 &&
            collect_session_.in_template_instantiation() &&
            (sem_op == BinaryOperator::LogicalAnd ||
             sem_op == BinaryOperator::LogicalOr)) {
            int64_t lhs_value = 0;
            if (collect_session_.try_evaluate_required_integer_constant(
                    lhs.sem, lhs_value, op.loc) &&
                ((sem_op == BinaryOperator::LogicalAnd && lhs_value == 0) ||
                 (sem_op == BinaryOperator::LogicalOr && lhs_value != 0))) {
                constraint_short_circuit = lhs_value != 0;
            }
        }

        ParsedExpr rhs;
        if (constraint_short_circuit.has_value()) {

            size_t diagnostic_watermark = diagnostics_.size();
            bool saved_substitution_failure =
                constraint_substitution_failure_;
            collect::Session::TemplateReplayOutcome* replay_outcome =
                collect_session_.current_template_replay_outcome();
            std::optional<collect::Session::TemplateReplayOutcome>
                saved_replay_outcome;
            if (replay_outcome) {
                saved_replay_outcome = *replay_outcome;
            }
            collect_session_.begin_speculative_parse();
            rhs = parse_expression(rhs_min);
            collect_session_.rollback_speculative_parse();
            constraint_substitution_failure_ = saved_substitution_failure;
            if (replay_outcome) {
                *replay_outcome = *saved_replay_outcome;
            }
            diagnostics_.resize(diagnostic_watermark);
            rhs.sem = collect_session_.make_boolean_literal(
                *constraint_short_circuit,
                *constraint_short_circuit ? "true" : "false",
                op.loc);
        } else {
            rhs = parse_expression(rhs_min);
        }
        std::vector<NodeId> children{lhs.syntax, rhs.syntax};
        NodeId syntax = make_node(NodeKind::BinaryExpr,
                                  begin,
                                  tree_.node(rhs.syntax).tokens.end,
                                  children,
                                  text_payload(op.value),
                                  NodeFlagNone,
                                  static_cast<uint16_t>(sem_op));
        collect::ExprResult sem =
            collect_session_.collect_binary_expr(sem_op, std::move(lhs.sem), std::move(rhs.sem), op.loc);
        lhs = ParsedExpr{syntax, std::move(sem)};
    }
    return lhs;
}

Parser::ParsedExpr Parser::parse_cast_expression() {
    if (check(TokenType::LEFT_PAREN)) {
        if (peek(1).type == TokenType::LEFT_BRACE) {

            return parse_postfix_suffixes(parse_statement_expression());
        }
        size_t begin = current_raw_index();
        Token lparen = current();
        {
            RevertingTentativeParsingAction tentative(*this);
            consume();

            std::optional<collect::ObjCBridgeKind> bridge_kind;
            if (lang_opts_.is_objc() &&
                current().type == TokenType::IDENTIFIER) {
                if (current().value == "__bridge") {
                    bridge_kind = collect::ObjCBridgeKind::Bridge;
                } else if (current().value == "__bridge_retained") {
                    bridge_kind = collect::ObjCBridgeKind::BridgeRetained;
                } else if (current().value == "__bridge_transfer") {
                    bridge_kind = collect::ObjCBridgeKind::BridgeTransfer;
                }
                if (bridge_kind.has_value()) {
                    consume();
                }
            }
            if (bridge_kind.has_value()) {
                cir::TypeId type{};
                NodeId type_syntax = parse_type_name(&type);
                if (!match(TokenType::RIGHT_PAREN) || !type.valid()) {
                    diagnose(DiagnosticLevel::Error,
                             "expected a type in the bridged cast",
                             current_loc());
                }
                tentative.commit();
                ParsedExpr operand = parse_cast_expression();
                NodeId syntax = make_node(
                    NodeKind::CastExpr, begin,
                    tree_.node(operand.syntax).tokens.end,
                    {type_syntax, operand.syntax},
                    text_payload(collect_session_.file().format_type(type)),
                    NodeFlagNone,
                    static_cast<uint16_t>(CastOperator::CStyle));
                collect::ExprResult sem =
                    collect_session_.collect_objc_bridge_cast(
                        *bridge_kind, type, std::move(operand.sem),
                        lparen.loc);
                return {syntax, std::move(sem)};
            }
            if (current().type != TokenType::EXTENSION_KW && is_type_start(current().type)) {
                cir::TypeId type{};
                StorageClass storage_class = StorageClass::None;
                bool cast_type_originates_from_template_parameter = false;
                NodeId type_syntax =
                    parse_type_name(&type,
                                    nullptr,
                                    &storage_class,
                                    nullptr,
                                    nullptr,
                                    &cast_type_originates_from_template_parameter);
                cir::TypeId resolved_cast_type = type.valid()
                    ? collect_session_.file().resolved_type(type)
                    : cir::TypeId{};
                bool has_valid_cast_type =
                    collect_session_.file().valid(resolved_cast_type) &&
                    collect_session_.file().type(resolved_cast_type).kind !=
                        cir::TypeKind::Unknown;
                if (match(TokenType::RIGHT_PAREN) && has_valid_cast_type) {
                    bool invalid_type_name_storage =
                        storage_class != StorageClass::None;
                    if (invalid_type_name_storage) {
                        diagnose(DiagnosticLevel::Error,
                                 "storage class specifier is not allowed in a cast type name",
                                 tree_.node(type_syntax).loc);
                    }
                    if (check(TokenType::LEFT_BRACE)) {
                        tentative.commit();
                        ParsedExpr init = parse_init_list_expression();
                        NodeId syntax = make_node(NodeKind::CompoundLiteralExpr,
                                                  begin,
                                                  tree_.node(init.syntax).tokens.end,
                                                  {type_syntax, init.syntax});
                        collect::ExprResult sem =
                            collect_session_.collect_compound_literal_expr(type,
                                                                           std::move(init.sem),
                                                                           lparen.loc);

                        return parse_postfix_suffixes({syntax, std::move(sem)});
                    }
                    bool can_start_cast_operand =
                        token_can_start_cast_operand(current().type);
                    if (lang_opts_.is_cxx_mode() &&
                        current().type == TokenType::SCOPE_RESOLUTION) {
                        can_start_cast_operand = true;
                    }
                    if (lang_opts_.is_objc() &&
                        (current().type == TokenType::AT ||
                         (current().type == TokenType::LEFT_BRACKET &&
                          !lang_opts_.is_cxx_mode()))) {

                        can_start_cast_operand = true;
                    }
                    if (current().type == TokenType::LOGICAL_AND &&
                        peek(1).type != TokenType::IDENTIFIER) {

                        can_start_cast_operand = false;
                    }
                    if (can_start_cast_operand) {
                        tentative.commit();
                        ParsedExpr operand = parse_cast_expression();
                        NodeId syntax = make_node(NodeKind::CastExpr,
                                                  begin,
                                                  tree_.node(operand.syntax).tokens.end,
                                                  {type_syntax, operand.syntax},
                                                  text_payload(collect_session_.file().format_type(type)),
                                                  NodeFlagNone,
                                                  static_cast<uint16_t>(CastOperator::CStyle));
                        collect::ExprResult sem =
                            collect_session_.collect_cast_expr(type, std::move(operand.sem), lparen.loc);
                        sem.type_originates_from_template_parameter =
                            sem.type_originates_from_template_parameter ||
                            cast_type_originates_from_template_parameter;
                        sem.has_error = sem.has_error || invalid_type_name_storage;
                        return {syntax, std::move(sem)};
                    }
                }
            }
        }
    }

    return parse_unary_expression();
}

Parser::ParsedExpr Parser::parse_unary_expression() {

    bool force_global_allocation = false;
    size_t globally_qualified_begin = current_raw_index();
    if (check(TokenType::SCOPE_RESOLUTION) &&
        (peek(1).type == TokenType::NEW ||
         peek(1).type == TokenType::DELETE)) {
        force_global_allocation = true;
        consume();
    }
    switch (current().type) {
        case TokenType::EXTENSION_KW:
            consume();
            return parse_cast_expression();
        case TokenType::CO_AWAIT_KW: {

            size_t begin = current_raw_index();
            Token await_token = current();
            consume();
            ParsedExpr operand = parse_cast_expression();
            NodeId syntax = make_node(NodeKind::AwaitExpr,
                                      begin,
                                      last_consumed_raw_end(),
                                      {operand.syntax},
                                      text_payload("co_await"));
            collect::ExprResult sem = collect_session_.collect_await_expr(
                std::move(operand.sem), await_token.loc);
            return {syntax, std::move(sem)};
        }
        case TokenType::LOGICAL_AND:
            if (is_identifier_token(peek(1).type)) {
                size_t begin = current_raw_index();
                Token op = current();
                consume();
                NodeId label = parse_name_node(NodeKind::Name);
                std::string label_name = node_text(tree_.node(label));
                NodeId syntax = make_node(NodeKind::UnaryExpr,
                                          begin,
                                          last_consumed_raw_end(),
                                          {label},
                                          text_payload("&&"),
                                          NodeFlagNone,
                                          static_cast<uint16_t>(UnaryOperator::LabelAddress));
                collect::ExprResult sem =
                    collect_session_.collect_label_address_expr(label_name, op.loc);
                return {syntax, std::move(sem)};
            }
            return parse_postfix_expression();
        case TokenType::BITWISE_XOR:

            return parse_postfix_expression();
        case TokenType::REFLECT: {

            size_t begin = current_raw_index();
            Token reflect_token = current();
            consume();
            auto finish = [&](collect::ExprResult sem) -> ParsedExpr {
                return {make_node(NodeKind::ReflectExpr,
                                  begin,
                                  last_consumed_raw_end(),
                                  {},
                                  text_payload("^^"),
                                  sem.has_error ? NodeFlagHasError
                                                : NodeFlagNone),
                        std::move(sem)};
            };
            if (check(TokenType::SCOPE_RESOLUTION) &&
                !is_identifier_token(peek(1).type)) {
                consume();
                return finish(
                    collect_session_.collect_reflect_global_namespace_expr(
                        reflect_token.loc));
            }

            bool name_path = false;
            {
                size_t probe = 0;
                bool probe_global = false;
                if (current().type == TokenType::SCOPE_RESOLUTION &&
                    is_identifier_token(peek(1).type)) {
                    probe_global = true;
                    probe = 1;
                }
                if (is_identifier_token(peek(probe).type)) {
                    std::vector<std::string_view> qualifiers;
                    size_t index = probe;
                    while (peek(index + 1).type ==
                               TokenType::SCOPE_RESOLUTION &&
                           is_identifier_token(peek(index + 2).type)) {
                        qualifiers.push_back(peek(index).value);
                        index += 2;
                    }
                    cir::TypeRef probed =
                        collect_session_.peek_qualified_type_ref(
                            probe_global, qualifiers, peek(index).value);
                    name_path = !probed.type.valid();

                    if (name_path &&
                        peek(index + 1).type == TokenType::LESS_THAN &&
                        collect_session_.template_info_for_name(
                            peek(index).value)) {
                        name_path = false;
                    }
                    if (name_path &&
                        peek(index + 1).type == TokenType::ELLIPSIS &&
                        peek(index + 2).type == TokenType::LEFT_BRACKET) {
                        name_path = false;
                    }
                }
            }
            if (!name_path) {
                DeclarationParser type_parser(*this);
                cir::TypeRef reflected =
                    type_parser.parse_declaration(false, true);
                if (!reflected.type.valid()) {
                    collect::ExprResult sem;
                    sem.has_error = true;
                    return finish(std::move(sem));
                }
                while (match(TokenType::MULTIPLY)) {
                    reflected = collect_session_.type_ref(
                        collect_session_.pointer_type(reflected));
                }
                return finish(collect_session_.collect_reflect_type_expr(
                    reflected, reflect_token.loc));
            }
            bool global_qualifier = false;
            if (check(TokenType::SCOPE_RESOLUTION)) {
                consume();
                global_qualifier = true;
            }
            std::vector<std::string> path;
            path.push_back(std::string(current().value));
            consume();
            while (check(TokenType::SCOPE_RESOLUTION) &&
                   is_identifier_token(peek(1).type)) {
                consume();
                path.push_back(std::string(current().value));
                consume();
            }
            return finish(collect_session_.collect_reflect_name_expr(
                global_qualifier, path, reflect_token.loc));
        }
        case TokenType::NEW: {
            size_t begin = force_global_allocation
                ? globally_qualified_begin
                : current_raw_index();
            Token new_token = current();
            consume();

            auto matching_right_paren = [&](size_t left_offset) {
                int depth = 0;
                for (size_t offset = left_offset; offset < 4096; ++offset) {
                    TokenType type = peek(offset).type;
                    if (type == TokenType::Eof) {
                        break;
                    }
                    if (type == TokenType::LEFT_PAREN) {
                        ++depth;
                    } else if (type == TokenType::RIGHT_PAREN &&
                               --depth == 0) {
                        return offset;
                    }
                }
                return size_t{0};
            };
            auto starts_type_at = [&](size_t offset) {
                const Token& token = peek(offset);
                if (is_identifier_token(token.type)) {
                    return collect_session_.is_type_name(token.value);
                }
                if (token.type == TokenType::SCOPE_RESOLUTION) {
                    return true;
                }
                return is_type_start(token.type);
            };
            bool has_placement = false;
            if (check(TokenType::LEFT_PAREN)) {
                size_t right = matching_right_paren(0);
                if (right != 0) {
                    TokenType after = peek(right + 1).type;
                    if (after == TokenType::LEFT_PAREN) {

                        TokenType nested = peek(right + 2).type;
                        has_placement = starts_type_at(right + 2);
                    } else {
                        has_placement = starts_type_at(right + 1);
                    }
                }
            }

            collect::Session::NewExpressionInput input;
            input.force_global = force_global_allocation;
            std::vector<NodeId> children;
            if (has_placement) {
                consume();
                ParsedExpressionList placements =
                    parse_expression_list(TokenType::RIGHT_PAREN);
                children.insert(children.end(),
                                placements.syntax.begin(),
                                placements.syntax.end());
                input.placement_arguments = std::move(placements.sem);
                if (!match(TokenType::RIGHT_PAREN)) {
                    diagnose(DiagnosticLevel::Error,
                             "expected ')' after new placement arguments",
                             current_loc());
                }
            }

            cir::TypeId allocated{};
            const collect::Session::TemplateInfo* deduced_new_template =
                nullptr;
            SrcLoc deduced_new_template_loc{};
            if (check(TokenType::LEFT_PAREN)) {
                consume();
                DeclarationParser type_parser(
                    *this,
                    TypeParseContext::type_only(
                        TypeParseContext::Origin::NewTypeId));
                allocated = type_parser.parse_declaration(true, true).type;
                deduced_new_template =
                    type_parser.deduced_class_template_info;
                deduced_new_template_loc =
                    type_parser.deduced_class_template_loc;
                if (!match(TokenType::RIGHT_PAREN)) {
                    diagnose(DiagnosticLevel::Error,
                             "expected ')' after parenthesized new type-id",
                             current_loc());
                }
            } else {
                DeclarationParser type_parser(
                    *this,
                    TypeParseContext::type_only(
                        TypeParseContext::Origin::NewTypeId));
                cir::TypeRef base =
                    type_parser.parse_declaration(false, true);
                allocated = base.type;
                deduced_new_template =
                    type_parser.deduced_class_template_info;
                deduced_new_template_loc =
                    type_parser.deduced_class_template_loc;
                while (match(TokenType::MULTIPLY)) {
                    allocated = collect_session_.pointer_type(
                        collect_session_.type_ref(allocated));
                }

                struct ParsedNewExtent {
                    bool incomplete = false;
                    bool runtime = false;
                    uint64_t constant = 0;
                    collect::ExprResult expression;
                    NodeId syntax = InvalidNodeId;
                };
                std::vector<ParsedNewExtent> extents;
                while (match(TokenType::LEFT_BRACKET)) {
                    ParsedNewExtent extent;
                    if (check(TokenType::RIGHT_BRACKET)) {
                        extent.incomplete = true;
                    } else {
                        ParsedExpr bound = parse_expression();
                        extent.syntax = bound.syntax;
                        int64_t constant = 0;
                        if (collect_session_.try_evaluate_integer_constant(
                                bound.sem, constant)) {
                            if (constant < 0) {
                                diagnose(DiagnosticLevel::Error,
                                         "new array bound is negative",
                                         tree_.node(bound.syntax).loc);
                            }
                            extent.constant = constant < 0
                                ? 0
                                : static_cast<uint64_t>(constant);
                        } else {
                            extent.runtime = true;
                            bound.sem = collect_session_.require_value(
                                std::move(bound.sem),
                                collect::UseContext::RValue,
                                tree_.node(bound.syntax).loc);
                            extent.expression = std::move(bound.sem);
                        }
                    }
                    if (!match(TokenType::RIGHT_BRACKET)) {
                        diagnose(DiagnosticLevel::Error,
                                 "expected ']' after new array bound",
                                 current_loc());
                    }
                    if (!extents.empty() &&
                        (extent.incomplete || extent.runtime ||
                         extent.constant == 0)) {
                        diagnose(DiagnosticLevel::Error,
                                 "trailing new array bounds must be positive "
                                 "constant expressions",
                                 current_loc());
                    }
                    if (extent.syntax != InvalidNodeId) {
                        children.push_back(extent.syntax);
                    }
                    extents.push_back(std::move(extent));
                }
                if (!extents.empty()) {
                    input.is_array = true;
                    for (size_t i = extents.size(); i-- > 0;) {
                        ParsedNewExtent& extent = extents[i];
                        if (i == 0 && extent.runtime) {
                            input.bound_fragment = std::move(
                                extent.expression.fragment);
                            input.runtime_outer_bound =
                                extent.expression.value;
                            allocated = collect_session_.array_type(
                                collect_session_.type_ref(allocated),
                                cir::ArraySizeKind::Variable,
                                std::nullopt,
                                input.runtime_outer_bound);
                        } else if (extent.incomplete) {
                            allocated = collect_session_.array_type(
                                collect_session_.type_ref(allocated),
                                std::nullopt);
                        } else {
                            allocated = collect_session_.array_type(
                                collect_session_.type_ref(allocated),
                                static_cast<size_t>(extent.constant));
                        }
                    }
                }
            }
            std::vector<NodeId> argument_nodes;
            if (match(TokenType::LEFT_PAREN)) {
                input.initializer_present = true;
                input.initializer_is_parenthesized = true;
                ParsedExpressionList arguments =
                    parse_expression_list(TokenType::RIGHT_PAREN);
                argument_nodes = std::move(arguments.syntax);
                input.initializer_arguments = std::move(arguments.sem);
                if (!match(TokenType::RIGHT_PAREN)) {
                    diagnose(DiagnosticLevel::Error,
                             "expected ')' after new initializer",
                             current_loc());
                }
            } else if (check(TokenType::LEFT_BRACE)) {
                input.initializer_present = true;
                input.initializer_is_braced = true;
                ParsedExpr initializer = parse_init_list_expression();
                argument_nodes.push_back(initializer.syntax);
                input.initializer_arguments.push_back(std::move(initializer.sem));
            }
            if (deduced_new_template) {
                if (input.is_array) {
                    diagnose(DiagnosticLevel::Error,
                             "deduced class type cannot be used as a new array element type",
                             deduced_new_template_loc.isInvalid()
                                 ? new_token.loc
                                 : deduced_new_template_loc);
                    allocated = {};
                } else {
                    std::vector<collect::ExprResult> deduction_arguments;
                    const collect::ExprResult* braced_initializer = nullptr;
                    if (input.initializer_is_braced &&
                        !input.initializer_arguments.empty()) {
                        braced_initializer =
                            &input.initializer_arguments.front();
                        if (braced_initializer->init_list) {
                            for (const collect::InitElementInput& element :
                                 braced_initializer->init_list->elements) {
                                if (element.designators.empty()) {
                                    deduction_arguments.push_back(
                                        element.value);
                                }
                            }
                        }
                    } else {
                        deduction_arguments = input.initializer_arguments;
                    }
                    allocated = deduce_class_template_initialization_type(
                        *deduced_new_template,
                        deduction_arguments,
                        deduced_new_template_loc.isInvalid()
                            ? new_token.loc
                            : deduced_new_template_loc,
                        CtadInitializationKind::Direct,
                        braced_initializer);
                }
            }
            input.allocated_type = allocated;
            children.insert(children.end(), argument_nodes.begin(),
                            argument_nodes.end());
            collect::ExprResult sem =
                collect_session_.collect_new_expr(std::move(input),
                                                  new_token.loc);
            return {make_node(NodeKind::UnaryExpr,
                              begin,
                              last_consumed_raw_end(),
                              children,
                              text_payload("new"),
                              sem.has_error ? NodeFlagHasError : NodeFlagNone),
                    std::move(sem)};
        }
        case TokenType::DELETE: {
            size_t begin = force_global_allocation
                ? globally_qualified_begin
                : current_raw_index();
            Token delete_token = current();
            consume();
            bool is_array = false;
            if (match(TokenType::LEFT_BRACKET)) {
                is_array = true;
                if (!match(TokenType::RIGHT_BRACKET)) {
                    diagnose(DiagnosticLevel::Error,
                             "expected ']' in array delete",
                             current_loc());
                }
            }
            ParsedExpr operand = parse_cast_expression();
            collect::Session::DeleteExpressionInput input;
            input.pointer = std::move(operand.sem);
            input.force_global = force_global_allocation;
            input.is_array = is_array;
            collect::ExprResult sem =
                collect_session_.collect_delete_expr(std::move(input),
                                                     delete_token.loc);
            return {make_node(NodeKind::UnaryExpr,
                              begin,
                              last_consumed_raw_end(),
                              {operand.syntax},
                              text_payload("delete"),
                              sem.has_error ? NodeFlagHasError : NodeFlagNone),
                    std::move(sem)};
        }
        case TokenType::INCREMENT:
        case TokenType::DECREMENT:
        case TokenType::PLUS:
        case TokenType::NEGATE:
        case TokenType::LOGICAL_NOT:
        case TokenType::BITWISE_NOT:
        case TokenType::MULTIPLY:
        case TokenType::BITWISE_AND: {
            size_t begin = current_raw_index();
            Token op = current();
            UnaryOperator sem_op = unary_operator_for(op.type);
            consume();
            ParsedExpr operand = parse_cast_expression();
            NodeId syntax = make_node(NodeKind::UnaryExpr,
                                      begin,
                                      tree_.node(operand.syntax).tokens.end,
                                      {operand.syntax},
                                      text_payload(op.value),
                                      NodeFlagNone,
                                      static_cast<uint16_t>(sem_op));
            collect::ExprResult sem =
                collect_session_.collect_unary_expr(sem_op, std::move(operand.sem), op.loc);
            return {syntax, std::move(sem)};
        }
        case TokenType::NOEXCEPT_KW: {

            if (!lang_opts_.is_cxx_mode()) {
                break;
            }
            size_t begin = current_raw_index();
            SrcLoc loc = current().loc;
            consume();
            if (!match(TokenType::LEFT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "expected '(' after 'noexcept'",
                         current_loc());
            }
            bool potentially_throwing = false;
            bool operand_dependent = false;
            bool operand_error = false;
            collect::ExprResult operand_sem;
            {
                RevertingTentativeParsingAction tentative(
                    *this, TentativeMode::ParserOnly);
                collect_session_.begin_unevaluated_operand();
                uint64_t taint_before = collect_session_.pattern_taint();
                ParsedExpr operand = parse_expression();
                potentially_throwing =
                    collect_session_.expression_potentially_throws(
                        operand.sem, &operand_dependent);
                operand_dependent = operand_dependent ||
                    collect_session_.expr_is_value_dependent(operand.sem) ||
                    collect_session_.pattern_taint() != taint_before;
                operand_error = operand.sem.has_error;
                operand_sem = std::move(operand.sem);
                collect_session_.end_unevaluated_operand();
                tentative.revert();
            }
            int depth = 1;
            while (!at_end() && depth > 0) {
                TokenType type = current().type;
                consume();
                if (type == TokenType::LEFT_PAREN) ++depth;
                if (type == TokenType::RIGHT_PAREN) --depth;
            }
            if (operand_error &&
                (!operand_dependent ||
                 !operand_sem.template_value_expr.valid())) {
                diagnose(DiagnosticLevel::Error,
                         "noexcept operand is ill-formed",
                         loc);
            }
            NodeId syntax = make_node(NodeKind::UnaryExpr,
                                      begin,
                                      last_consumed_raw_end(),
                                      {},
                                      text_payload("noexcept"));
            collect::ExprResult sem = collect_session_.collect_noexcept_expr(
                std::move(operand_sem),
                potentially_throwing,
                operand_dependent,
                loc);
            return {syntax, std::move(sem)};
        }
        case TokenType::SIZEOF: {
            size_t begin = current_raw_index();
            Token op = current();
            consume();
            if (match(TokenType::ELLIPSIS)) {
                std::vector<NodeId> children;
                if (!match(TokenType::LEFT_PAREN)) {
                    diagnose(DiagnosticLevel::Error,
                             "expected '(' after sizeof...",
                             current_loc());
                }
                std::string pack_name;
                SrcLoc pack_loc = current_loc();
                if (is_identifier_token(current().type)) {
                    pack_name = current().value;
                    children.push_back(parse_name_node(NodeKind::Name));
                } else {
                    diagnose(DiagnosticLevel::Error,
                             "expected parameter pack name in sizeof...",
                             current_loc());
                }
                if (!match(TokenType::RIGHT_PAREN)) {
                    diagnose(DiagnosticLevel::Error,
                             "expected ')' after sizeof... operand",
                             current_loc());
                }
                NodeId syntax = make_node(NodeKind::UnaryExpr,
                                          begin,
                                          last_consumed_raw_end(),
                                          children,
                                          text_payload("sizeof..."),
                                          NodeFlagNone,
                                          static_cast<uint16_t>(
                                              UnaryOperator::SizeofExpr));
                collect::ExprResult sem = collect_session_.collect_sizeof_pack(
                    pack_name,
                    pack_loc);
                return {syntax, std::move(sem)};
            }
            if (check(TokenType::LEFT_PAREN)) {
                {
                    RevertingTentativeParsingAction tentative(*this);
                    consume();
                    if (is_type_start(current().type)) {
                        cir::TypeId type{};
                        cir::Fragment vla_bounds;
                        NodeId type_syntax =
                            parse_type_name(&type, nullptr, nullptr, nullptr, &vla_bounds);
                        if (match(TokenType::RIGHT_PAREN) && type.valid() && !check(TokenType::LEFT_BRACE)) {
                            tentative.commit();
                            NodeId syntax = make_node(NodeKind::UnaryExpr,
                                                      begin,
                                                      last_consumed_raw_end(),
                                                      {type_syntax},
                                                      text_payload(op.value),
                                                      NodeFlagNone,
                                                      static_cast<uint16_t>(UnaryOperator::SizeofType));
                            collect::ExprResult sem = collect_session_.collect_sizeof_type(
                                type, op.loc, std::move(vla_bounds));
                            return {syntax, std::move(sem)};
                        }
                    }
                }

                collect_session_.begin_unevaluated_operand();
                ParsedExpr operand = parse_cast_expression();
                collect_session_.end_unevaluated_operand();
                NodeId syntax = make_node(NodeKind::UnaryExpr,
                                          begin,
                                          tree_.node(operand.syntax).tokens.end,
                                          {operand.syntax},
                                          text_payload(op.value),
                                          NodeFlagNone,
                                          static_cast<uint16_t>(UnaryOperator::SizeofExpr));
                collect::ExprResult sem =
                    collect_session_.collect_unary_expr(UnaryOperator::SizeofExpr, std::move(operand.sem), op.loc);
                return {syntax, std::move(sem)};
            }

            collect_session_.begin_unevaluated_operand();
            ParsedExpr operand = parse_unary_expression();
            collect_session_.end_unevaluated_operand();
            NodeId syntax = make_node(NodeKind::UnaryExpr,
                                      begin,
                                      tree_.node(operand.syntax).tokens.end,
                                      {operand.syntax},
                                      text_payload(op.value),
                                      NodeFlagNone,
                                      static_cast<uint16_t>(UnaryOperator::SizeofExpr));
            collect::ExprResult sem =
                collect_session_.collect_unary_expr(UnaryOperator::SizeofExpr, std::move(operand.sem), op.loc);
            return {syntax, std::move(sem)};
        }
        case TokenType::ALIGNOF: {
            size_t begin = current_raw_index();
            Token op = current();
            consume();
            if (!match(TokenType::LEFT_PAREN)) {
                diagnose(DiagnosticLevel::Error, "expected '(' after alignof", current_loc());
                collect::ExprResult sem;
                sem.has_error = true;
                return {make_node(NodeKind::Error, begin, last_consumed_raw_end(), {}, {}, NodeFlagHasError),
                        std::move(sem)};
            }
            {
                RevertingTentativeParsingAction tentative(*this);
                if (is_type_start(current().type)) {
                    cir::TypeId type{};
                    NodeId type_syntax = parse_type_name(&type);
                    if (match(TokenType::RIGHT_PAREN) && type.valid()) {
                        tentative.commit();
                        NodeId syntax = make_node(NodeKind::UnaryExpr,
                                                  begin,
                                                  last_consumed_raw_end(),
                                                  {type_syntax},
                                                  text_payload(op.value),
                                                  NodeFlagNone,
                                                  static_cast<uint16_t>(UnaryOperator::AlignofType));
                        collect::ExprResult sem = collect_session_.collect_alignof_type(type, op.loc);
                        return {syntax, std::move(sem)};
                    }
                }
            }
            collect_session_.begin_unevaluated_operand();
            ParsedExpr operand = parse_assignment_expression();
            collect_session_.end_unevaluated_operand();
            if (!match(TokenType::RIGHT_PAREN)) {
                diagnose(DiagnosticLevel::Error, "expected ')' after alignof expression", current_loc());
            }
            NodeId syntax = make_node(NodeKind::UnaryExpr,
                                      begin,
                                      last_consumed_raw_end(),
                                      {operand.syntax},
                                      text_payload(op.value),
                                      NodeFlagNone,
                                      static_cast<uint16_t>(UnaryOperator::AlignofExpr));
            collect::ExprResult sem =
                collect_session_.collect_unary_expr(UnaryOperator::AlignofExpr, std::move(operand.sem), op.loc);
            return {syntax, std::move(sem)};
        }
        case TokenType::TYPEID_KW: {
            size_t begin = current_raw_index();
            Token op = current();
            consume();
            if (!match(TokenType::LEFT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "expected '(' after typeid",
                         current_loc());
                collect::ExprResult sem;
                sem.has_error = true;
                return {make_node(NodeKind::Error,
                                  begin,
                                  last_consumed_raw_end(),
                                  {},
                                  {},
                                  NodeFlagHasError),
                        std::move(sem)};
            }

            {
                RevertingTentativeParsingAction tentative(*this);
                if (is_type_start(current().type)) {
                    cir::TypeId type{};
                    NodeId type_syntax = parse_type_name(&type);
                    if (match(TokenType::RIGHT_PAREN) && type.valid()) {
                        tentative.commit();
                        NodeId syntax = make_node(
                            NodeKind::UnaryExpr,
                            begin,
                            last_consumed_raw_end(),
                            {type_syntax},
                            text_payload(op.value),
                            NodeFlagNone,
                            static_cast<uint16_t>(UnaryOperator::TypeidType));
                        collect::ExprResult sem =
                            collect_session_.collect_typeid_type(type, op.loc);
                        return parse_postfix_suffixes(
                            ParsedExpr{syntax, std::move(sem)});
                    }
                }
            }

            ParsedExpr operand;
            bool committed_probe = false;
            {
                RevertingTentativeParsingAction tentative(*this);
                collect_session_.begin_typeid_probe_operand();
                ParsedExpr probe = parse_expression();
                collect_session_.end_typeid_probe_operand();
                bool closed = match(TokenType::RIGHT_PAREN);
                if (closed &&
                    !collect_session_.typeid_operand_is_potentially_evaluated(
                        probe.sem)) {
                    tentative.commit();
                    operand = std::move(probe);
                    committed_probe = true;
                }
            }
            if (!committed_probe) {
                operand = parse_expression();
                if (!match(TokenType::RIGHT_PAREN)) {
                    diagnose(DiagnosticLevel::Error,
                             "expected ')' after typeid expression",
                             current_loc());
                }
            }
            NodeId syntax = make_node(
                NodeKind::UnaryExpr,
                begin,
                last_consumed_raw_end(),
                {operand.syntax},
                text_payload(op.value),
                NodeFlagNone,
                static_cast<uint16_t>(UnaryOperator::TypeidExpr));
            collect::ExprResult sem = collect_session_.collect_typeid_expr(
                std::move(operand.sem), op.loc);
            return parse_postfix_suffixes(
                ParsedExpr{syntax, std::move(sem)});
        }
        case TokenType::REAL_PART:
        case TokenType::IMAG_PART: {
            size_t begin = current_raw_index();
            Token op = current();
            consume();
            ParsedExpr operand = parse_cast_expression();
            NodeId syntax = make_node(NodeKind::UnaryExpr,
                                      begin,
                                      tree_.node(operand.syntax).tokens.end,
                                      {operand.syntax},
                                      text_payload(op.value),
                                      NodeFlagDeferred);
            collect::ExprResult sem = collect_session_.collect_complex_part_expr(
                std::move(operand.sem), op.type == TokenType::IMAG_PART, op.loc);
            return {syntax, std::move(sem)};
        }
        default:
            return parse_postfix_expression();
    }
    return parse_postfix_expression();
}

std::optional<Parser::ParsedExpr> Parser::parse_cxx_named_cast_expression() {
    if (!lang_opts_.is_cxx_mode() ||
        current().type != TokenType::IDENTIFIER ||
        peek(1).type != TokenType::LESS_THAN) {
        return std::nullopt;
    }
    std::optional<CxxNamedCastInfo> cast_kind =
        cxx_named_cast_kind(current().value);
    if (!cast_kind.has_value()) {
        return std::nullopt;
    }

    size_t begin = current_raw_index();
    Token cast_token = current();
    consume();
    consume();

    cir::TypeId type{};
    StorageClass storage_class = StorageClass::None;
    bool cast_type_originates_from_template_parameter = false;
    NodeId type_syntax =
        parse_type_name(&type,
                        nullptr,
                        &storage_class,
                        nullptr,
                        nullptr,
                        &cast_type_originates_from_template_parameter,
                        TypeParseContext::type_only(
                            TypeParseContext::Origin::NamedCastTypeId));
    bool invalid_type_name_storage = storage_class != StorageClass::None;
    if (invalid_type_name_storage) {
        diagnose(DiagnosticLevel::Error,
                 "storage class specifier is not allowed in a C++ cast type name",
                 tree_.node(type_syntax).loc);
    }
    bool closed = false;
    if (match(TokenType::GREATER_THAN)) {
        closed = true;
    } else if (check(TokenType::RIGHT_SHIFT) && pending_template_closes_ > 0) {
        --pending_template_closes_;
        consume();
        closed = true;
    }
    if (!closed) {
        pending_template_closes_ = 0;
        diagnose(DiagnosticLevel::Error,
                 "expected '>' after C++ cast type",
                 current_loc());
    }
    if (!match(TokenType::LEFT_PAREN)) {
        diagnose(DiagnosticLevel::Error,
                 "expected '(' after C++ cast type",
                 current_loc());
    }
    ParsedExpr operand = parse_expression();
    if (!match(TokenType::RIGHT_PAREN)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ')' after C++ cast operand",
                 current_loc());
    }
    NodeId syntax = make_node(NodeKind::CastExpr,
                              begin,
                              last_consumed_raw_end(),
                              {type_syntax, operand.syntax},
                              text_payload(std::string(cast_token.value) +
                                           "<" +
                                           collect_session_.file().format_type(type) +
                                           ">"),
                              invalid_type_name_storage ? NodeFlagHasError
                                                        : NodeFlagNone,
                              static_cast<uint16_t>(cast_kind->syntax_kind));
    collect::ExprResult sem =
        collect_session_.collect_cpp_named_cast(cast_kind->collect_kind,
                                                type,
                                                std::move(operand.sem),
                                                cast_token.loc);
    sem.type_originates_from_template_parameter =
        sem.type_originates_from_template_parameter ||
        cast_type_originates_from_template_parameter;
    sem.has_error = sem.has_error || invalid_type_name_storage;
    return ParsedExpr{syntax, std::move(sem)};
}

collect::ExprResult Parser::replay_default_member_initializer(
    cir::EntityId field,
    cir::InstId object_place,
    SrcLoc loc) {
    collect::ExprResult result;
    if (!lang_opts_.is_cxx_mode() || !field.valid() ||
        !collect_session_.file().valid(field)) {
        return result;
    }
    const cir::RecordFieldFact* fact =
        collect_session_.file().field_fact(field);
    if (!fact || !fact->has_default_member_initializer ||
        fact->default_member_initializer_end <=
            fact->default_member_initializer_begin) {
        return result;
    }
    if (std::find(active_default_member_initializer_replays_.begin(),
                  active_default_member_initializer_replays_.end(),
                  field) !=
        active_default_member_initializer_replays_.end()) {
        collect_session_.file().add_error(
            "recursive default member initializer dependency", loc);
        result.has_error = true;
        return result;
    }
    active_default_member_initializer_replays_.push_back(field);
    struct ReplayExit {
        Parser* parser = nullptr;
        collect::Session* session = nullptr;
        collect::Session::CompleteClassInitializerScope object_scope;
        bool entered_context = false;
        ~ReplayExit() {
            if (!parser || !session) {
                return;
            }
            session->finish_complete_class_initializer(object_scope);
            if (entered_context) {
                session->leave_scope();
            }
            parser->active_default_member_initializer_replays_.pop_back();
        }
    } replay_exit;
    replay_exit.parser = this;
    replay_exit.session = &collect_session_;

    cir::DeclContextId context =
        fact->default_member_initializer_context;
    if (context.valid() && collect_session_.file().valid(context)) {
        collect::ScopeFlags flags = collect::ScopeFlags::None;
        switch (collect_session_.file().decl_context(context).kind) {
        case cir::DeclContextKind::TranslationUnit:
            flags = collect::ScopeFlags::FileScope;
            break;
        case cir::DeclContextKind::Namespace:
            flags = collect::ScopeFlags::NamespaceScope |
                    collect::ScopeFlags::FileScope;
            break;
        case cir::DeclContextKind::Record:
            flags = collect::ScopeFlags::RecordScope;
            break;
        case cir::DeclContextKind::Enum:
            flags = collect::ScopeFlags::EnumScope;
            break;
        case cir::DeclContextKind::Function:
            flags = collect::ScopeFlags::FunctionScope;
            break;
        case cir::DeclContextKind::Prototype:
            flags = collect::ScopeFlags::PrototypeScope;
            break;
        case cir::DeclContextKind::TemplateParameter:
            flags = collect::ScopeFlags::TemplateParameterScope;
            break;
        case cir::DeclContextKind::Block:
            flags = collect::ScopeFlags::BlockScope;
            break;
        case cir::DeclContextKind::Invalid:
            break;
        }
        if (flags != collect::ScopeFlags::None) {
            collect::ScopeEnterResult entered =
                collect_session_.enter_existing_context(context, flags);
            replay_exit.entered_context =
                entered.scope != collect::InvalidScopeId;
        }
    }
    cir::EntityId record = collect_session_.file().entity(field).parent;
    replay_exit.object_scope =
        collect_session_.begin_complete_class_initializer(record,
                                                          object_place);
    collect::Session::LookupGenerationCeilingScope ceiling(
        collect_session_,
        fact->default_member_initializer_lookup_generation != 0
            ? fact->default_member_initializer_lookup_generation
            : collect_session_.lookup_generation());
    size_t saved_cursor = cursor_;
    size_t saved_last_end = last_consumed_raw_end_;
    int saved_template_closes = pending_template_closes_;
    cursor_ = fact->default_member_initializer_begin;
    pending_template_closes_ = 0;
    ParsedExpr replayed = fact->default_member_initializer_braced
        ? parse_init_list_expression()
        : parse_expression(PrecLevel::ASSIGNMENT);
    cursor_ = saved_cursor;
    last_consumed_raw_end_ = saved_last_end;
    pending_template_closes_ = saved_template_closes;
    return std::move(replayed.sem);
}

collect::ExprResult Parser::replay_default_argument(cir::EntityId selected,
                                                    size_t parameter_index,
                                                    SrcLoc loc) {
    collect::ExprResult result;
    if (!lang_opts_.is_cxx_mode() || !selected.valid() ||
        !collect_session_.file().valid(selected)) {
        return result;
    }

    TemplateReplayGuardScope replay_guard(collect_session_, loc);
    if (!replay_guard.active) {
        result.has_error = true;
        return result;
    }
    collect::Session::DefaultArgumentReplayInfo replay_info =
        collect_session_.prepare_default_argument_replay(selected,
                                                         parameter_index,
                                                         loc);
    const collect::ParamInput::DefaultArgument* default_argument =
        replay_info.argument;
    if (!default_argument) {
        return result;
    }

    const collect::Session::TemplateInfo* selected_template_info =
        replay_info.template_info;
    SrcLoc selected_template_point =
        replay_info.point_of_instantiation.isInvalid()
            ? loc
            : replay_info.point_of_instantiation;
    uint64_t selected_template_point_generation =
        replay_info.point_lookup_generation;
    auto scope_flags_for_context = [&](cir::DeclContextId context) {
        if (!context.valid() || !collect_session_.file().valid(context)) {
            return collect::ScopeFlags::None;
        }
        switch (collect_session_.file().decl_context(context).kind) {
        case cir::DeclContextKind::TranslationUnit:
            return collect::ScopeFlags::FileScope;
        case cir::DeclContextKind::Namespace:
            return collect::ScopeFlags::NamespaceScope |
                   collect::ScopeFlags::FileScope;
        case cir::DeclContextKind::Record:
            return collect::ScopeFlags::RecordScope;
        case cir::DeclContextKind::Enum:
            return collect::ScopeFlags::EnumScope;
        case cir::DeclContextKind::Function:
            return collect::ScopeFlags::FunctionScope;
        case cir::DeclContextKind::Prototype:
            return collect::ScopeFlags::PrototypeScope;
        case cir::DeclContextKind::TemplateParameter:
            return collect::ScopeFlags::TemplateParameterScope;
        case cir::DeclContextKind::Block:
            return collect::ScopeFlags::BlockScope;
        case cir::DeclContextKind::Invalid:
            return collect::ScopeFlags::None;
        }
        return collect::ScopeFlags::None;
    };
    cir::DeclContextId replay_context =
        replay_info.declaration_context.valid()
            ? replay_info.declaration_context
            : default_argument->declaration_context;
    collect::ScopeFlags default_scope_flags =
        scope_flags_for_context(replay_context);
    size_t saved_cursor = cursor_;
    size_t saved_last_end = last_consumed_raw_end_;
    int saved_template_closes = pending_template_closes_;
    cursor_ = default_argument->token_begin;
    pending_template_closes_ = 0;
    auto restore_default_argument_parse_state = [&] {
        cursor_ = saved_cursor;
        last_consumed_raw_end_ = saved_last_end;
        pending_template_closes_ = saved_template_closes;
    };
    struct DefaultTemplateInstantiationScopeExit {
        collect::Session* session = nullptr;
        collect::Session::DefaultArgumentInstantiationScope scope;
        ~DefaultTemplateInstantiationScopeExit() {
            if (session) {
                session->finish_default_argument_instantiation(
                    std::move(scope));
            }
        }
    } default_template_scope;
    if (selected_template_info) {
        default_template_scope.scope =
            collect_session_.begin_default_argument_instantiation(
                *selected_template_info,
                replay_info.arguments,
                selected_template_point,
                selected_template_point_generation);
        if (!default_template_scope.scope.active) {
            restore_default_argument_parse_state();
            return result;
        }
        default_template_scope.session = &collect_session_;
    }
    collect::Session::LookupGenerationCeilingScope ceiling(
        collect_session_, default_argument->lookup_generation);
    struct DefaultArgumentScopeExit {
        collect::Session* session = nullptr;
        ~DefaultArgumentScopeExit() {
            if (session) {
                session->leave_scope();
            }
        }
    } default_argument_scope;
    bool should_enter_default_context =
        replay_context.valid() &&
        default_scope_flags != collect::ScopeFlags::None;
    if (should_enter_default_context && selected_template_info &&
        collect_session_.file().valid(replay_context)) {
        cir::DeclContextKind context_kind =
            collect_session_.file()
                .decl_context(replay_context)
                .kind;
        should_enter_default_context =
            context_kind != cir::DeclContextKind::TemplateParameter &&
            context_kind != cir::DeclContextKind::Prototype;
    }
    if (should_enter_default_context) {
        collect::ScopeEnterResult entered =
            collect_session_.enter_existing_context(
                replay_context,
                default_scope_flags);
        if (entered.scope != collect::InvalidScopeId) {
            default_argument_scope.session = &collect_session_;
        }
    }
    cir::EntityId declaration_record =
        collect_session_.enclosing_record_for_context(replay_context);
    cir::EntityId caller_record{};
    if (declaration_record.valid()) {
        caller_record =
            collect_session_.override_member_access_record(declaration_record);
    }
    cir::EntityId caller_function =
        collect_session_.override_member_access_function(selected);
    collect_session_.set_in_default_argument_replay(true, loc);
    ParsedExpr default_expr = parse_assignment_expression();
    collect_session_.set_in_default_argument_replay(false);

    const cir::Entity& selected_entity =
        collect_session_.file().entity(selected);
    cir::TypeId selected_type =
        collect_session_.file().resolved_type(selected_entity.type);
    const auto* selected_payload =
        collect_session_.file().valid(selected_type)
            ? std::get_if<cir::FunctionTypePayload>(
                  &collect_session_.file().type_payload(selected_type))
            : nullptr;
    const cir::RecordMethodFact* selected_method =
        collect_session_.file().method_fact(selected);
    size_t hidden_parameters =
        selected_method && !selected_method->is_static ? 1 : 0;
    size_t payload_parameter_index = hidden_parameters + parameter_index;
    if (selected_payload &&
        payload_parameter_index < selected_payload->parameters.size()) {
        default_expr.sem =
            collect_session_.initialize_default_argument(
                std::move(default_expr.sem),
                selected_payload->parameters[payload_parameter_index].type,
                default_argument->loc);
    }
    collect_session_.override_member_access_function(caller_function);
    if (declaration_record.valid()) {
        collect_session_.override_member_access_record(caller_record);
    }
    restore_default_argument_parse_state();
    return default_expr.sem;
}

void Parser::append_default_call_arguments(collect::ExprResult& callee,
                                           std::vector<collect::ExprResult>& args,
                                           SrcLoc loc) {
    if (!lang_opts_.is_cxx_mode() ||
        callee.category != collect::ValueCategory::FunctionDesignator) {
        return;
    }
    bool type_dependent_call =
        collect_session_.expr_is_dependent(callee);
    for (const collect::ExprResult& argument : args) {
        type_dependent_call =
            type_dependent_call ||
            collect_session_.expr_is_dependent(argument);
    }
    auto template_argument_is_dependent =
        [&](const cir::TemplateArgument& argument) {
            return argument.is_dependent ||
                (argument.kind == cir::TemplateArgumentKind::Type &&
                 argument.type.type.valid() &&
                 collect_session_.is_dependent_type(argument.type.type)) ||
                (argument.kind == cir::TemplateArgumentKind::Value &&
                 (argument.dependent_value_expr.valid() ||
                  (argument.value_type.type.valid() &&
                   collect_session_.is_dependent_type(
                       argument.value_type.type)))) ||
                (argument.kind == cir::TemplateArgumentKind::Template &&
                 !argument.template_entity.valid());
        };
    for (const cir::TemplateArgument& argument :
         callee.explicit_template_arguments) {
        type_dependent_call =
            type_dependent_call ||
            template_argument_is_dependent(argument);
    }
    for (const collect::CandidateExplicitTemplateArguments& candidate :
         callee.candidate_explicit_template_arguments) {
        if (!candidate.viable) {
            continue;
        }
        for (const cir::TemplateArgument& argument :
             candidate.arguments) {
            type_dependent_call =
                type_dependent_call ||
                template_argument_is_dependent(argument);
        }
    }
    if (type_dependent_call) {

        return;
    }
    auto candidate_can_use_defaults = [&](cir::EntityId candidate) {
        if (!candidate.valid() || !collect_session_.file().valid(candidate)) {
            return false;
        }
        cir::EntityKind kind =
            collect_session_.file().entity(candidate).kind;
        if (kind != cir::EntityKind::Function &&
            kind != cir::EntityKind::Method) {
            return false;
        }
        const cir::RecordMethodFact* method_fact =
            collect_session_.file().method_fact(candidate);
        size_t hidden_parameters =
            method_fact && !method_fact->is_static ? 1 : 0;
        return collect_session_.callable_can_use_default_arguments(
            candidate, args.size(), hidden_parameters);
    };
    bool may_use_defaults = false;
    if (callee.candidates.empty()) {
        may_use_defaults = candidate_can_use_defaults(callee.entity);
    } else {
        for (cir::EntityId candidate : callee.candidates) {
            may_use_defaults =
                may_use_defaults || candidate_can_use_defaults(candidate);
        }
    }
    if (!may_use_defaults) {
        return;
    }

    cir::EntityId selected =
        collect_session_.resolve_call_overload(callee, args, loc);
    if (!selected.valid() || !collect_session_.file().valid(selected)) {
        return;
    }
    cir::EntityKind selected_kind =
        collect_session_.file().entity(selected).kind;
    if (selected_kind != cir::EntityKind::Function &&
        selected_kind != cir::EntityKind::Method) {
        return;
    }
    callee.entity = selected;
    callee.type = collect_session_.file().entity(selected).type;
    callee.candidates.clear();

    const auto* payload = std::get_if<cir::FunctionTypePayload>(
        &collect_session_.file().type_payload(
            collect_session_.file().resolved_type(
                collect_session_.file().entity(selected).type)));
    if (!payload || payload->is_variadic) {
        return;
    }
    const cir::RecordMethodFact* method_fact =
        collect_session_.file().method_fact(selected);
    size_t hidden_parameters =
        method_fact && !method_fact->is_static ? 1 : 0;
    if (hidden_parameters > payload->parameters.size()) {
        return;
    }
    size_t visible_parameters =
        payload->parameters.size() - hidden_parameters;
    while (args.size() < visible_parameters) {
        if (!collect_session_.callable_default_argument(selected,
                                                        args.size())) {
            break;
        }
        args.push_back(
            routed_default_argument_replay(selected, args.size(), loc));
    }
}

collect::ExprResult Parser::routed_default_argument_replay(
    cir::EntityId selected,
    size_t parameter_index,
    SrcLoc loc) {
    cir::EntityId route = module_pattern_identity(selected);
    if (!route.valid()) {
        route = selected;
    }
    if (Parser* owner = module_unit_parser_for(route)) {
        collect::Session::ModuleVisibilityOverride visibility(
            collect_session_,
            collect_session_.file().entity(route).origin_unit);
        return owner->replay_default_argument(selected, parameter_index,
                                              loc);
    }
    return replay_default_argument(selected, parameter_index, loc);
}

Parser::ParsedExpr Parser::parse_postfix_expression() {
    ParsedExpr expr;
    if (std::optional<ParsedExpr> named_cast = parse_cxx_named_cast_expression()) {
        expr = std::move(*named_cast);
    } else {
        expr = parse_primary_expression();
    }

    return parse_postfix_suffixes(std::move(expr));
}

Parser::ParsedExpressionList
Parser::parse_expression_list(TokenType terminator) {
    ParsedExpressionList result;
    while (!at_end() && !check(terminator)) {
        std::optional<PackExpansionPattern> pack_pattern =
            lang_opts_.is_cxx_mode()
                ? try_parse_expression_pack_expansion(terminator)
                : std::nullopt;
        if (pack_pattern.has_value()) {
            result.syntax.push_back(pack_pattern->syntax);
            result.has_dependent_pack_expansion =
                expand_expression_pack(*pack_pattern, result.sem) ||
                result.has_dependent_pack_expansion;
        } else {
            bool nested_dependent_pack_expansion = false;
            ParsedExpr argument = check(TokenType::LEFT_BRACE)
                ? parse_init_list_expression(
                      &nested_dependent_pack_expansion)
                : parse_assignment_expression();
            result.syntax.push_back(argument.syntax);
            result.sem.push_back(std::move(argument.sem));
            result.has_dependent_pack_expansion =
                result.has_dependent_pack_expansion ||
                nested_dependent_pack_expansion;
        }
        if (!match(TokenType::COMMA)) {
            break;
        }
    }
    return result;
}

Parser::ParsedExpr Parser::parse_postfix_suffixes(ParsedExpr expr) {
    while (!at_end()) {
        if (constraint_expression_replay_end_ != SIZE_MAX &&
            current_raw_index() >= constraint_expression_replay_end_) {
            break;
        }
        if (declaration_attributes_terminate_template_head_constraint()) {
            break;
        }
        if (match(TokenType::LEFT_PAREN)) {
            size_t begin = tree_.node(expr.syntax).tokens.begin;
            SrcLoc loc = last_consumed_loc();
            std::vector<NodeId> children{expr.syntax};
            ParsedExpressionList arguments =
                parse_expression_list(TokenType::RIGHT_PAREN);
            children.insert(children.end(), arguments.syntax.begin(),
                            arguments.syntax.end());
            std::vector<collect::ExprResult> sem_args =
                std::move(arguments.sem);
            if (!match(TokenType::RIGHT_PAREN)) {
                diagnose(DiagnosticLevel::Error, "expected ')' after call arguments", current_loc());
            }
            NodeId syntax = make_node(NodeKind::CallExpr, begin, last_consumed_raw_end(), children);
            if (lang_opts_.is_cxx_mode() &&
                expr.sem.category == collect::ValueCategory::Type &&
                !expr.sem.type.valid() && expr.sem.entity.valid()) {
                const collect::Session::TemplateInfo* placeholder =
                    collect_session_.template_info(expr.sem.entity);
                if (placeholder &&
                    (placeholder->is_class_template ||
                     placeholder->is_alias_template)) {
                    cir::TypeId deduced =
                        deduce_class_template_initialization_type(
                            *placeholder,
                            sem_args,
                            loc,
                            CtadInitializationKind::Direct);
                    collect::ExprResult sem;
                    if (deduced.valid()) {
                        (void)collect_session_.require_complete_class_type(
                            deduced,
                            loc,
                            cir::InstantiationDemandKind::CompleteClass);
                        sem = collect_session_.collect_functional_cast(
                            deduced, std::move(sem_args), loc);
                    } else {
                        sem.has_error = true;
                    }
                    expr = ParsedExpr{syntax, std::move(sem)};
                    continue;
                }
            }
            if (lang_opts_.is_cxx_mode() &&
                expr.sem.category == collect::ValueCategory::Type &&
                expr.sem.type.valid()) {

                collect::ExprResult sem =
                    collect_session_.collect_functional_cast(
                        expr.sem.type, std::move(sem_args), loc);
                expr = ParsedExpr{syntax, std::move(sem)};
                continue;
            }

            if (lang_opts_.is_cxx_mode()) {
                std::vector<const collect::Session::TemplateInfo*> placeholders;
                std::vector<cir::EntityId> others;
                std::string template_name;

                std::vector<cir::EntityId> pot;
                if (expr.sem.candidates.empty()) {
                    if (expr.sem.entity.valid()) {
                        pot.push_back(expr.sem.entity);
                    }
                } else {
                    pot = expr.sem.candidates;
                }
                if (!expr.sem.qualified_name &&
                    !expr.sem.suppress_argument_dependent_lookup &&
                    !expr.sem.name.empty()) {
                    collect_session_.add_adl_candidates(expr.sem.name,
                                                        sem_args,
                                                        pot);
                }
                auto sort_candidate = [&](cir::EntityId candidate) {
                    if (!candidate.valid()) {
                        return;
                    }
                    const collect::Session::TemplateInfo* info =
                        collect_session_.template_info(candidate);
                    if (info &&
                        !info->is_class_template &&
                        !info->is_alias_template &&
                        !info->is_variable_template &&
                        !info->is_concept) {
                        placeholders.push_back(info);
                        template_name = info->name;
                    } else {
                        others.push_back(candidate);
                    }
                };
                for (cir::EntityId candidate : pot) {
                    sort_candidate(candidate);
                }
                if (!placeholders.empty()) {
                    std::vector<cir::EntityId> mixed = std::move(others);
                    auto mark_template_call_dependent = [&] {
                        expr.sem.type =
                            collect_session_.file().dependent_type(
                                "dependent function template call");
                        expr.sem.category =
                            collect::ValueCategory::Dependent;
                        expr.sem.unresolved_unqualified_name = false;
                        expr.sem.has_error = false;
                    };
                    auto argument_is_unresolved_template_designator =
                        [&](const collect::ExprResult& argument) {
                            if (argument.category !=
                                collect::ValueCategory::FunctionDesignator) {
                                return false;
                            }
                            if (argument.entity.valid() &&
                                collect_session_.template_info(
                                    argument.entity)) {
                                return true;
                            }
                            return std::any_of(
                                argument.candidates.begin(),
                                argument.candidates.end(),
                                [&](cir::EntityId designator) {
                                    return collect_session_.template_info(
                                               designator) != nullptr;
                                });
                        };
                    bool call_has_dependent_argument = std::any_of(
                        expr.sem.explicit_template_arguments.begin(),
                        expr.sem.explicit_template_arguments.end(),
                        [&](const collect::Session::TemplateArgument& argument) {
                            return template_argument_is_dependent(
                                collect_session_, argument);
                        });
                    for (const collect::CandidateExplicitTemplateArguments&
                             candidate :
                         expr.sem.candidate_explicit_template_arguments) {
                        if (!candidate.viable) {
                            continue;
                        }
                        call_has_dependent_argument =
                            call_has_dependent_argument ||
                            std::any_of(
                                candidate.arguments.begin(),
                                candidate.arguments.end(),
                                [&](const collect::Session::TemplateArgument&
                                        argument) {
                                    return template_argument_is_dependent(
                                        collect_session_, argument);
                                });
                    }
                    for (const collect::ExprResult& argument : sem_args) {

                        bool unresolved_function_template_designator =
                            argument_is_unresolved_template_designator(
                                argument);
                        if (argument.category ==
                                collect::ValueCategory::Dependent ||
                            (!unresolved_function_template_designator &&
                             (collect_session_.expr_is_dependent(argument) ||
                              (argument.type.valid() &&
                               collect_session_.type_contains_type_param(
                                   argument.type))))) {
                            call_has_dependent_argument = true;
                            break;
                        }
                    }
                    if (call_has_dependent_argument) {
                        mark_template_call_dependent();
                    } else {
                        bool deduction_remains_dependent = false;
                        for (const collect::Session::TemplateInfo* info :
                             placeholders) {

                            ConstraintSubstitutionFailureIsolation
                                candidate_failure(*this);
                            std::vector<collect::Session::TemplateArgument>
                                deduced;
                            collect::Session::TemplateArgumentBindings
                                deduced_bindings;
                            const std::vector<
                                collect::Session::TemplateArgument>*
                                explicit_arguments = nullptr;
                            if (expr.sem
                                    .has_explicit_template_arguments) {
                                explicit_arguments =
                                    &expr.sem
                                         .explicit_template_arguments;
                                auto candidate_arguments =
                                    std::find_if(
                                        expr.sem
                                            .candidate_explicit_template_arguments
                                            .begin(),
                                        expr.sem
                                            .candidate_explicit_template_arguments
                                            .end(),
                                        [&](const collect::
                                                CandidateExplicitTemplateArguments&
                                                candidate) {
                                            return candidate
                                                       .template_entity ==
                                                info->entity;
                                        });
                                if (candidate_arguments !=
                                    expr.sem
                                        .candidate_explicit_template_arguments
                                        .end()) {
                                    if (!candidate_arguments->viable) {
                                        continue;
                                    }
                                    explicit_arguments =
                                        &candidate_arguments->arguments;
                                }
                            }
                            collect::Session::PatternInstantiationCallbacks
                                callbacks;
                            configure_pattern_instantiation_callbacks(
                                callbacks, loc);
                            if (!collect_session_.deduce_template_arguments(
                                    *info,
                                    sem_args,
                                    deduced,
                                    explicit_arguments,
                                    &callbacks,
                                    &deduced_bindings)) {
                                continue;
                            }
                            // Defaults can bind a member-template parameter
                            // to an enclosing class-template parameter even
                            // when the call has no written arguments. Such a
                            // candidate cannot participate in definition-time
                            // overload resolution: its SFINAE surface changes
                            // with the enclosing specialization.
                            if (std::any_of(
                                    deduced.begin(),
                                    deduced.end(),
                                    [&](const collect::Session::
                                            TemplateArgument& argument) {
                                        return template_argument_is_dependent(
                                            collect_session_, argument);
                                    })) {
                                deduction_remains_dependent = true;
                                continue;
                            }

                            cir::TypeId pattern_resolved =
                                collect_session_.file().resolved_type(
                                    info->pattern_type);
                            const auto* pattern_function =
                                collect_session_.file().valid(
                                    pattern_resolved) &&
                                        collect_session_.file().type(
                                            pattern_resolved).kind ==
                                            cir::TypeKind::Function
                                    ? std::get_if<cir::FunctionTypePayload>(
                                          &collect_session_.file()
                                               .type_payload(pattern_resolved))
                                    : nullptr;
                            if (pattern_function &&
                                (collect_session_.is_dependent_type(
                                     pattern_function->return_type.type) ||
                                 collect_session_
                                     .type_contains_dependent_alias_specialization(
                                         pattern_function->return_type.type))) {
                                // This probe only decides whether the candidate
                                // signature remains dependent. A class in the
                                // substituted return type is not otherwise
                                // required to be complete, and the candidate
                                // might never be selected by overload
                                // resolution.
                                callbacks.materialize_type_template_definition =
                                    false;
                                cir::TypeId substituted_pattern_type =
                                    collect_session_.substitute_pattern_type(
                                        info->pattern_type,
                                        deduced_bindings,
                                        callbacks);
                                cir::TypeId substituted_resolved =
                                    collect_session_.file().resolved_type(
                                        substituted_pattern_type);
                                const auto* substituted_function =
                                    substituted_pattern_type.valid() &&
                                            collect_session_.file().valid(
                                                substituted_resolved) &&
                                            collect_session_.file().type(
                                                substituted_resolved).kind ==
                                                cir::TypeKind::Function
                                        ? std::get_if<
                                              cir::FunctionTypePayload>(
                                              &collect_session_.file()
                                                   .type_payload(
                                                       substituted_resolved))
                                        : nullptr;
                                if (substituted_function &&
                                    (collect_session_.is_dependent_type(
                                         substituted_function->return_type
                                             .type) ||
                                     collect_session_
                                         .type_contains_dependent_alias_specialization(
                                             substituted_function->return_type
                                                 .type))) {
                                    deduction_remains_dependent = true;
                                    continue;
                                }
                            }
                            if (!check_template_associated_constraints(
                                    *info,
                                    deduced,
                                    loc,
                                    callbacks.point_lookup_generation,
                                    /*diagnose_unsatisfied=*/false,
                                    &deduced_bindings)) {
                                continue;
                            }
                            cir::EntityId instantiated =
                                form_function_template_candidate(
                                    *info,
                                    deduced_bindings,
                                    loc,
                                    callbacks.point_lookup_generation);
                            if (instantiated.valid()) {
                                mixed.push_back(instantiated);
                            }
                        }
                        if (deduction_remains_dependent) {
                            mark_template_call_dependent();
                        } else if (mixed.empty()) {

                            std::string message =
                                "no matching function for call to '" +
                                template_name +
                                "': template argument deduction failed";
                            if (expr.sem.has_explicit_template_arguments) {
                                for (const collect::Session::TemplateInfo*
                                         info : placeholders) {
                                    const auto* candidate_arguments =
                                        &expr.sem
                                             .explicit_template_arguments;
                                    auto candidate = std::find_if(
                                        expr.sem
                                            .candidate_explicit_template_arguments
                                            .begin(),
                                        expr.sem
                                            .candidate_explicit_template_arguments
                                            .end(),
                                        [&](const collect::
                                                CandidateExplicitTemplateArguments&
                                                entry) {
                                            return entry.template_entity ==
                                                info->entity;
                                        });
                                    if (candidate !=
                                        expr.sem
                                            .candidate_explicit_template_arguments
                                            .end()) {
                                        if (!candidate->viable) {
                                            continue;
                                        }
                                        candidate_arguments =
                                            &candidate->arguments;
                                    }
                                    collect::Session::TemplateArgumentBindings
                                        bindings;
                                    collect::Session::
                                        TemplateArgumentBindingFailure failure;
                                    if (!collect_session_
                                             .bind_explicit_template_arguments_prefix_to_parameters(
                                                 info->parameters,
                                                 *candidate_arguments,
                                                 bindings,
                                                 &failure,
                                                 collect::Session::
                                                     TemplateArgumentBindingMode::
                                                         FunctionExplicitPrefix)) {
                                        message =
                                            format_template_argument_binding_failure(
                                                *info,
                                                failure);
                                        break;
                                    }
                                }
                            }
                            diagnose(DiagnosticLevel::Error,
                                     std::move(message),
                                     loc);
                            collect::ExprResult error_sem;
                            error_sem.has_error = true;
                            expr = ParsedExpr{syntax, std::move(error_sem)};
                            continue;
                        } else {
                            if (!expr.sem.entity.valid()) {

                                expr.sem.fragment = {};
                                expr.sem.value = {};
                            }
                            expr.sem.entity = mixed.back();
                            expr.sem.type =
                                collect_session_.file().entity(mixed.back())
                                    .type;
                            expr.sem.category =
                                collect::ValueCategory::FunctionDesignator;
                            expr.sem.candidates =
                                mixed.size() > 1
                                    ? std::move(mixed)
                                    : std::vector<cir::EntityId>{};
                        }
                    }
                } else if (!others.empty() &&
                           (expr.sem.category ==
                                collect::ValueCategory::FunctionDesignator ||
                            expr.sem.unresolved_unqualified_name)) {

                    if (!expr.sem.entity.valid()) {
                        expr.sem.fragment = {};
                        expr.sem.value = {};
                    }
                    expr.sem.entity = others.back();
                    expr.sem.type = collect_session_.file()
                                            .entity(others.back())
                                            .type;
                    expr.sem.category =
                        collect::ValueCategory::FunctionDesignator;
                    expr.sem.candidates = others.size() > 1
                        ? std::move(others)
                        : std::vector<cir::EntityId>{};
                }
            }
            append_default_call_arguments(expr.sem, sem_args, loc);
            collect::ExprResult sem =
                collect_session_.collect_call_expr(std::move(expr.sem), std::move(sem_args), loc);
            expr = ParsedExpr{syntax, std::move(sem)};
            continue;
        }
        if (lang_opts_.is_cxx_mode() &&
            expr.sem.category == collect::ValueCategory::Type &&
            check(TokenType::LEFT_BRACE)) {
            size_t begin = tree_.node(expr.syntax).tokens.begin;
            SrcLoc loc = current_loc();
            ParsedExpr initializer = parse_init_list_expression();
            NodeId syntax = make_node(NodeKind::CallExpr,
                                      begin,
                                      last_consumed_raw_end(),
                                      {expr.syntax, initializer.syntax});
            std::vector<collect::ExprResult> args;
            args.push_back(std::move(initializer.sem));
            cir::TypeId target_type = expr.sem.type;
            if (!target_type.valid() && lang_opts_.is_cxx_mode() &&
                expr.sem.entity.valid()) {
                const collect::Session::TemplateInfo* placeholder =
                    collect_session_.template_info(expr.sem.entity);
                if (placeholder &&
                    (placeholder->is_class_template ||
                     placeholder->is_alias_template)) {
                    std::vector<collect::ExprResult> deduction_arguments;
                    if (args.front().init_list) {
                        for (const collect::InitElementInput& element :
                             args.front().init_list->elements) {
                            if (element.designators.empty()) {
                                deduction_arguments.push_back(element.value);
                            }
                        }
                    }
                    target_type = deduce_class_template_initialization_type(
                        *placeholder,
                        deduction_arguments,
                        loc,
                        CtadInitializationKind::Direct,
                        &args.front());
                    if (target_type.valid()) {
                        (void)collect_session_.require_complete_class_type(
                            target_type,
                            loc,
                            cir::InstantiationDemandKind::CompleteClass);
                    }
                }
            }
            collect::ExprResult sem =
                collect_session_.collect_functional_cast(target_type,
                                                         std::move(args),
                                                         loc,
                                                         collect::InitListSyntax::Braced);
            expr = ParsedExpr{syntax, std::move(sem)};
            continue;
        }
        if (match(TokenType::LEFT_BRACKET)) {
            size_t begin = tree_.node(expr.syntax).tokens.begin;
            SrcLoc loc = last_consumed_loc();
            ParsedExpr index = parse_expression();
            if (!match(TokenType::RIGHT_BRACKET)) {
                diagnose(DiagnosticLevel::Error, "expected ']' after array subscript", current_loc());
            }
            NodeId syntax = make_node(NodeKind::ArraySubscriptExpr,
                                      begin,
                                      last_consumed_raw_end(),
                                      {expr.syntax, index.syntax});
            collect::ExprResult sem =
                collect_session_.collect_array_subscript_expr(std::move(expr.sem),
                                                              std::move(index.sem),
                                                              loc);
            expr = ParsedExpr{syntax, std::move(sem)};
            continue;
        }
        if (check(TokenType::DOT) || check(TokenType::ARROW)) {
            bool is_arrow = check(TokenType::ARROW);
            Token op = current();
            size_t begin = tree_.node(expr.syntax).tokens.begin;
            consume();
            bool has_template_keyword = false;
            if (lang_opts_.is_cxx_mode() && check(TokenType::TEMPLATE)) {
                has_template_keyword = true;
                consume();
            }
            auto parse_explicit_destructor_call =
                [&](cir::TypeId qualifier_type,
                    bool is_qualified) -> bool {
                    if (!lang_opts_.is_cxx_mode() ||
                        !match(TokenType::BITWISE_NOT)) {
                        return false;
                    }
                    SrcLoc destructor_loc = last_consumed_loc();
                    size_t destructor_begin = last_consumed_raw_index();
                    if (has_template_keyword) {
                        diagnose(DiagnosticLevel::Error,
                                 "template disambiguator cannot precede a destructor name",
                                 destructor_loc);
                    }
                    if (!is_identifier_token(current().type)) {
                        diagnose(DiagnosticLevel::Error,
                                 "expected type name after '~'",
                                 current_loc());
                        return true;
                    }
                    Token type_name = current();
                    consume();
                    cir::TypeId named_type{};
                    if (check(TokenType::LESS_THAN)) {
                        const collect::Session::TemplateInfo* info =
                            collect_session_.template_info_for_name(
                                type_name.value);
                        if (info && info->is_class_template) {
                            cir::EntityId specialization =
                                instantiate_template(*info, type_name.loc);
                            if (specialization.valid() &&
                                collect_session_.file().valid(
                                    specialization)) {
                                named_type = collect_session_.file()
                                    .entity(specialization).type;
                            }
                        } else {
                            diagnose(DiagnosticLevel::Error,
                                     "destructor template-id does not name a class template",
                                     type_name.loc);
                            (void)parse_dependent_expression_template_argument_list(
                                type_name.loc);
                        }
                    } else {
                        named_type = collect_session_.lookup_type_name(
                            type_name.value);
                    }
                    if (!named_type.valid() && qualifier_type.valid()) {
                        cir::EntityId record = collect_session_.file()
                            .record_entity(qualifier_type);
                        if (record.valid() &&
                            collect_session_.file().entity(record).name.valid() &&
                            collect_session_.file().name(
                                collect_session_.file().entity(record).name) ==
                                type_name.value) {
                            named_type = qualifier_type;
                        }
                    }
                    if (!named_type.valid()) {
                        diagnose(DiagnosticLevel::Error,
                                 "unknown type name in explicit destructor call",
                                 type_name.loc);
                    }
                    bool syntax_error = false;
                    if (!match(TokenType::LEFT_PAREN)) {
                        diagnose(DiagnosticLevel::Error,
                                 "expected '(' after destructor name",
                                 current_loc());
                        syntax_error = true;
                    } else if (!check(TokenType::RIGHT_PAREN)) {
                        diagnose(DiagnosticLevel::Error,
                                 "destructor call cannot have arguments",
                                 current_loc());
                        syntax_error = true;
                        int depth = 1;
                        while (!at_end() && depth > 0) {
                            TokenType type = current().type;
                            consume();
                            if (type == TokenType::LEFT_PAREN) ++depth;
                            if (type == TokenType::RIGHT_PAREN) --depth;
                        }
                    } else {
                        consume();
                    }
                    collect::ExprResult sem =
                        collect_session_.collect_explicit_destructor_call(
                            std::move(expr.sem), named_type, qualifier_type,
                            is_arrow, is_qualified, destructor_loc);
                    sem.has_error = sem.has_error || syntax_error ||
                        !named_type.valid();
                    NodeId name = make_node(
                        NodeKind::Name, destructor_begin,
                        last_consumed_raw_end(), {},
                        text_payload("~" + std::string(type_name.value)),
                        sem.has_error ? NodeFlagHasError : NodeFlagNone);
                    NodeId syntax = make_node(
                        NodeKind::CallExpr, begin, last_consumed_raw_end(),
                        {expr.syntax, name},
                        text_payload(std::string(op.value) +
                                     "~" + std::string(type_name.value)),
                        sem.has_error ? NodeFlagHasError : NodeFlagNone,
                        is_arrow ? 1 : 0);
                    expr = ParsedExpr{syntax, std::move(sem)};
                    return true;
                };
            if (parse_explicit_destructor_call({}, false)) {
                continue;
            }
            if (lang_opts_.is_cxx_mode() &&
                check(TokenType::OPERATOR_KW)) {
                size_t member_begin = current_raw_index();
                if (starts_conversion_function_id()) {
                    ParsedConversionFunctionId conversion_id =
                        *parse_conversion_function_id();
                    bool has_error = conversion_id.has_error;
                    if (has_template_keyword) {
                        diagnose(
                            DiagnosticLevel::Error,
                            "template disambiguator cannot precede a conversion-function-id",
                            conversion_id.loc);
                        has_error = true;
                    }
                    collect::ExprResult sem = collect_session_
                        .collect_conversion_function_id_access_expr(
                            std::move(expr.sem),
                            conversion_id.target_type,
                            is_arrow,
                            op.loc);
                    sem.has_error = sem.has_error || has_error;
                    sem.unparenthesized_id_or_member = true;
                    NodeId member = make_node(
                        NodeKind::Name,
                        member_begin,
                        last_consumed_raw_end(),
                        conversion_id.type_syntax != InvalidNodeId
                            ? std::vector<NodeId>{conversion_id.type_syntax}
                            : std::vector<NodeId>{},
                        text_payload(conversion_id.name),
                        sem.has_error ? NodeFlagHasError : NodeFlagNone);
                    NodeId syntax = make_node(
                        NodeKind::MemberExpr,
                        begin,
                        last_consumed_raw_end(),
                        {expr.syntax, member},
                        text_payload(std::string(op.value) +
                                     conversion_id.name),
                        sem.has_error ? NodeFlagHasError : NodeFlagNone,
                        is_arrow ? 1 : 0);
                    expr = ParsedExpr{syntax, std::move(sem)};
                    continue;
                }
                ParsedOperatorFunctionId operator_id =
                    *parse_operator_function_id();
                collect::ExprResult sem;
                bool has_error = operator_id.has_error;
                if (has_template_keyword &&
                    !check(TokenType::LESS_THAN)) {
                    diagnose(
                        DiagnosticLevel::Error,
                        "template disambiguator requires a template argument list",
                        operator_id.loc);
                    has_error = true;
                }

                if (check(TokenType::LESS_THAN)) {
                    const collect::Session::TemplateInfo* info =
                        collect_session_.member_template_info_for_access(
                            expr.sem, operator_id.name, is_arrow);
                    if (info) {
                        std::vector<collect::Session::TemplateArgument>
                            arguments;
                        cir::DeclContextId context =
                            info->entity.valid() &&
                                    collect_session_.file().valid(info->entity)
                                ? collect_session_.file()
                                      .entity(info->entity)
                                      .semantic_context
                                : cir::DeclContextId{};
                        std::vector<const collect::Session::TemplateInfo*>
                            candidates =
                                collect_session_.function_template_infos_for_name(
                                    context,
                                    operator_id.name,
                                    /*include_parents=*/false);
                        std::vector<
                            collect::CandidateExplicitTemplateArguments>
                            candidate_arguments;
                        bool parsed =
                            parse_function_template_argument_list_for_candidates(
                                *info,
                                candidates,
                                arguments,
                                candidate_arguments,
                                operator_id.loc);
                        std::vector<cir::EntityId> candidate_entities;
                        for (const auto* candidate : candidates) {
                            auto replayed = candidate
                                ? std::find_if(
                                      candidate_arguments.begin(),
                                      candidate_arguments.end(),
                                      [&](const collect::
                                              CandidateExplicitTemplateArguments&
                                              entry) {
                                          return entry.template_entity ==
                                              candidate->entity;
                                      })
                                : candidate_arguments.end();
                            if (candidate && candidate->entity.valid() &&
                                (replayed == candidate_arguments.end() ||
                                 replayed->viable)) {
                                candidate_entities.push_back(
                                    candidate->entity);
                            }
                        }
                        sem = collect_session_
                                  .collect_resolved_member_function_access_expr(
                                      std::move(expr.sem),
                                      std::move(candidate_entities),
                                      operator_id.name,
                                      is_arrow,
                                      op.loc);
                        sem.has_explicit_template_arguments = true;
                        sem.explicit_template_arguments =
                            std::move(arguments);
                        sem.candidate_explicit_template_arguments =
                            std::move(candidate_arguments);
                        sem.has_error = sem.has_error || has_error || !parsed;
                    } else if (collect_session_.expr_is_dependent(expr.sem)) {
                        if (!has_template_keyword) {
                            diagnose(
                                DiagnosticLevel::Error,
                                "missing 'template' disambiguator before dependent template name",
                                operator_id.loc);
                            has_error = true;
                        }
                        bool parsed =
                            parse_dependent_expression_template_argument_list(
                                operator_id.loc);
                        collect::ExprResult dependent = std::move(expr.sem);
                        dependent.type = collect_session_.file().dependent_type(
                            "dependent member operator template-id");
                        dependent.name = operator_id.name;
                        dependent.category =
                            collect::ValueCategory::Dependent;
                        dependent.has_error =
                            dependent.has_error || has_error || !parsed;
                        sem = collect_session_.make_dependent_expr(
                            std::move(dependent), operator_id.loc);
                    } else {
                        diagnose(DiagnosticLevel::Error,
                                 "operator template-id names a non-template member",
                                 operator_id.loc);
                        (void)parse_dependent_expression_template_argument_list(
                            operator_id.loc);
                        sem = collect_session_.collect_member_access_expr(
                            std::move(expr.sem),
                            operator_id.name,
                            is_arrow,
                            op.loc);
                        sem.has_error = true;
                    }
                } else {
                    sem = collect_session_.collect_member_access_expr(
                        std::move(expr.sem),
                        operator_id.name,
                        is_arrow,
                        op.loc);
                    sem.has_error = sem.has_error || has_error;
                }
                sem.unparenthesized_id_or_member = true;
                NodeId member = make_node(
                    NodeKind::Name,
                    member_begin,
                    last_consumed_raw_end(),
                    {},
                    text_payload(operator_id.name),
                    sem.has_error ? NodeFlagHasError : NodeFlagNone);
                NodeId syntax = make_node(
                    NodeKind::MemberExpr,
                    begin,
                    last_consumed_raw_end(),
                    {expr.syntax, member},
                    text_payload(std::string(op.value) + operator_id.name),
                    sem.has_error ? NodeFlagHasError : NodeFlagNone,
                    is_arrow ? 1 : 0);
                expr = ParsedExpr{syntax, std::move(sem)};
                continue;
            }
            if (!is_identifier_token(current().type)) {
                diagnose(DiagnosticLevel::Error, "expected member name", current_loc());
                break;
            }
            auto finish_invalid_template_member =
                [&](Token terminal,
                    size_t member_begin,
                    std::string message,
                    bool consume_template_arguments) {
                    if (!expr.sem.has_error) {
                        diagnose(DiagnosticLevel::Error,
                                 std::move(message),
                                 terminal.loc);
                    }
                    consume();
                    if (consume_template_arguments) {
                        (void)parse_dependent_expression_template_argument_list(
                            terminal.loc);
                    }
                    collect::ExprResult sem = std::move(expr.sem);
                    sem.type = collect_session_.file().unknown_type();
                    sem.name = std::string(terminal.value);
                    sem.category = collect::ValueCategory::Dependent;
                    sem.qualified_name = true;
                    sem.has_error = true;
                    sem.unparenthesized_id_or_member = true;
                    NodeId member = make_node(
                        NodeKind::Name, member_begin, last_consumed_raw_end(),
                        {}, text_payload(std::string(terminal.value)),
                        NodeFlagHasError);
                    NodeId syntax = make_node(
                        NodeKind::MemberExpr, begin, last_consumed_raw_end(),
                        {expr.syntax, member},
                        text_payload(std::string(op.value) + std::string(terminal.value)),
                        NodeFlagHasError,
                        is_arrow ? 1 : 0);
                    expr = ParsedExpr{syntax, std::move(sem)};
                };
            if (has_template_keyword &&
                peek(1).type != TokenType::LESS_THAN) {
                size_t member_begin = current_raw_index();
                Token terminal = current();
                finish_invalid_template_member(
                    terminal,
                    member_begin,
                    "template disambiguator requires a template argument list",
                    /*consume_template_arguments=*/false);
                continue;
            }
            if (lang_opts_.is_cxx_mode() &&
                peek(1).type == TokenType::LESS_THAN) {
                size_t member_begin = current_raw_index();
                Token terminal = current();
                const collect::Session::TemplateInfo* info =
                    collect_session_.member_template_info_for_access(
                        expr.sem, terminal.value, is_arrow);
                if (info) {
                    consume();
                    std::vector<collect::Session::TemplateArgument> arguments;
                    cir::DeclContextId context =
                        info->entity.valid() &&
                                collect_session_.file().valid(info->entity)
                            ? collect_session_.file()
                                  .entity(info->entity)
                                  .semantic_context
                            : cir::DeclContextId{};
                    std::vector<const collect::Session::TemplateInfo*>
                        candidates =
                            collect_session_.function_template_infos_for_name(
                                context,
                                terminal.value,
                                /*include_parents=*/false);
                    std::vector<
                        collect::CandidateExplicitTemplateArguments>
                        candidate_arguments;
                    bool parsed =
                        parse_function_template_argument_list_for_candidates(
                            *info,
                            candidates,
                            arguments,
                            candidate_arguments,
                            terminal.loc);
                    std::vector<cir::EntityId> candidate_entities;
                    for (const auto* candidate : candidates) {
                        auto replayed = candidate
                            ? std::find_if(
                                  candidate_arguments.begin(),
                                  candidate_arguments.end(),
                                  [&](const collect::
                                          CandidateExplicitTemplateArguments&
                                          entry) {
                                      return entry.template_entity ==
                                          candidate->entity;
                                  })
                            : candidate_arguments.end();
                        if (candidate && candidate->entity.valid() &&
                            (replayed == candidate_arguments.end() ||
                             replayed->viable)) {
                            candidate_entities.push_back(
                                candidate->entity);
                        }
                    }
                    collect::ExprResult sem =
                        collect_session_
                            .collect_resolved_member_function_access_expr(
                                std::move(expr.sem),
                                std::move(candidate_entities),
                                terminal.value, is_arrow, op.loc);
                    sem.has_explicit_template_arguments = true;
                    sem.explicit_template_arguments = std::move(arguments);
                    sem.candidate_explicit_template_arguments =
                        std::move(candidate_arguments);
                    sem.has_error = sem.has_error || !parsed;
                    sem.unparenthesized_id_or_member = true;
                    NodeId member = make_node(
                        NodeKind::Name, member_begin, last_consumed_raw_end(), {},
                        text_payload(std::string(terminal.value)),
                        sem.has_error ? NodeFlagHasError : NodeFlagNone);
                    NodeId syntax = make_node(
                        NodeKind::MemberExpr, begin, last_consumed_raw_end(),
                        {expr.syntax, member},
                        text_payload(std::string(op.value) + std::string(terminal.value)),
                        sem.has_error ? NodeFlagHasError : NodeFlagNone,
                        is_arrow ? 1 : 0);
                    expr = ParsedExpr{syntax, std::move(sem)};
                    continue;
                }
                if (has_template_keyword &&
                    collect_session_.expr_is_dependent(expr.sem)) {
                    consume();
                    bool parsed =
                        parse_dependent_expression_template_argument_list(
                            terminal.loc);
                    collect::ExprResult dependent = std::move(expr.sem);
                    dependent.type = collect_session_.file().dependent_type(
                        "dependent member template-id");
                    dependent.name = std::string(terminal.value);
                    dependent.category = collect::ValueCategory::Dependent;
                    dependent.has_error = dependent.has_error || !parsed;
                    collect::ExprResult sem =
                        collect_session_.make_dependent_expr(
                            std::move(dependent), terminal.loc);
                    sem.unparenthesized_id_or_member = true;
                    NodeId member = make_node(
                        NodeKind::Name, member_begin, last_consumed_raw_end(), {},
                        text_payload(std::string(terminal.value)),
                        sem.has_error ? NodeFlagHasError : NodeFlagNone);
                    NodeId syntax = make_node(
                        NodeKind::MemberExpr, begin, last_consumed_raw_end(),
                        {expr.syntax, member},
                        text_payload(std::string(op.value) + std::string(terminal.value)),
                        sem.has_error ? NodeFlagHasError : NodeFlagNone,
                        is_arrow ? 1 : 0);
                    expr = ParsedExpr{syntax, std::move(sem)};
                    continue;
                }
                if (has_template_keyword) {
                    finish_invalid_template_member(
                        terminal,
                        member_begin,
                        "template disambiguator names a non-template",
                        /*consume_template_arguments=*/true);
                    continue;
                }
                if (!has_template_keyword &&
                    collect_session_.expr_is_dependent(expr.sem) &&
                    template_id_precedes_call(0)) {
                    diagnose(DiagnosticLevel::Error,
                             "missing 'template' disambiguator before dependent template name",
                             terminal.loc);
                    consume();
                    bool parsed =
                        parse_dependent_expression_template_argument_list(
                            terminal.loc);
                    (void)parsed;
                    collect::ExprResult dependent = std::move(expr.sem);
                    dependent.type = collect_session_.file().dependent_type(
                        "dependent member template-id");
                    dependent.name = std::string(terminal.value);
                    dependent.category = collect::ValueCategory::Dependent;
                    dependent.has_error = true;
                    collect::ExprResult sem =
                        collect_session_.make_dependent_expr(
                            std::move(dependent), terminal.loc);
                    sem.unparenthesized_id_or_member = true;
                    NodeId member = make_node(
                        NodeKind::Name, member_begin, last_consumed_raw_end(), {},
                        text_payload(std::string(terminal.value)),
                        NodeFlagHasError);
                    NodeId syntax = make_node(
                        NodeKind::MemberExpr, begin, last_consumed_raw_end(),
                        {expr.syntax, member},
                        text_payload(std::string(op.value) + std::string(terminal.value)),
                        NodeFlagHasError,
                        is_arrow ? 1 : 0);
                    expr = ParsedExpr{syntax, std::move(sem)};
                    continue;
                }
            }

            if (lang_opts_.is_cxx_mode() &&
                ((peek(1).type == TokenType::SCOPE_RESOLUTION &&
                  peek(2).type == TokenType::BITWISE_NOT) ||
                 (peek(1).type == TokenType::LESS_THAN &&
                  template_id_precedes_scope(0)))) {
                cir::TypeId qualifier_type =
                    collect_session_.lookup_type_name(current().value);
                if (peek(1).type == TokenType::LESS_THAN) {
                    ParsedNestedName nested = parse_nested_name_specifier();
                    qualifier_type = nested.scope.entity.valid()
                        ? collect_session_.file()
                              .entity(nested.scope.entity).type
                        : cir::TypeId{};
                } else if (qualifier_type.valid()) {
                    consume();
                    consume();
                }
                if (qualifier_type.valid() &&
                    parse_explicit_destructor_call(qualifier_type, true)) {
                    continue;
                }
            }
            if (lang_opts_.is_cxx_mode() &&
                peek(1).type == TokenType::SCOPE_RESOLUTION &&
                peek(2).type != TokenType::MULTIPLY) {
                ParsedNestedName nested = parse_nested_name_specifier();
                std::string member_name = "<member>";
                collect::ExprResult sem;
                cir::TypeId qualifier_type =
                    nested.scope.entity.valid()
                        ? collect_session_.file()
                              .entity(nested.scope.entity).type
                        : nested.scope.dependent_type.type;
                if (parse_explicit_destructor_call(qualifier_type, true)) {
                    continue;
                }
                if (check(TokenType::OPERATOR_KW)) {
                    if (starts_conversion_function_id()) {
                        ParsedConversionFunctionId conversion_id =
                            *parse_conversion_function_id();
                        member_name = conversion_id.name;
                        sem = collect_session_
                            .collect_conversion_function_id_access_expr(
                                std::move(expr.sem),
                                conversion_id.target_type,
                                is_arrow,
                                op.loc,
                                qualifier_type);
                        sem.has_error = sem.has_error || nested.has_error ||
                                        conversion_id.has_error;
                        sem.unparenthesized_id_or_member = true;
                    } else {
                        ParsedOperatorFunctionId operator_id =
                            *parse_operator_function_id();
                        member_name = std::move(operator_id.name);
                        const collect::Session::TemplateInfo* info = nullptr;
                        if (check(TokenType::LESS_THAN) &&
                            qualifier_type.valid()) {
                            cir::EntityId qualifier_record =
                                collect_session_.file().record_entity(
                                    qualifier_type);
                            if (qualifier_record.valid() &&
                                collect_session_.file().valid(
                                    qualifier_record)) {
                                info =
                                    collect_session_.template_info_in_context(
                                        collect_session_.file()
                                            .entity(qualifier_record)
                                            .semantic_context,
                                        member_name,
                                        /*include_parents=*/false);
                            }
                        }
                        std::vector<collect::Session::TemplateArgument>
                            arguments;
                        std::vector<
                            collect::CandidateExplicitTemplateArguments>
                            candidate_arguments;
                        bool parsed_arguments = true;
                        bool template_lookup_error = false;
                        if (info) {
                            cir::DeclContextId context =
                                info->entity.valid() &&
                                        collect_session_.file().valid(
                                            info->entity)
                                    ? collect_session_.file()
                                          .entity(info->entity)
                                          .semantic_context
                                    : cir::DeclContextId{};
                            std::vector<const collect::Session::TemplateInfo*>
                                candidates = collect_session_
                                    .function_template_infos_for_name(
                                        context,
                                        member_name,
                                        /*include_parents=*/false);
                            parsed_arguments =
                                parse_function_template_argument_list_for_candidates(
                                    *info,
                                    candidates,
                                    arguments,
                                    candidate_arguments,
                                    operator_id.loc);
                        } else if (check(TokenType::LESS_THAN)) {
                            diagnose(
                                DiagnosticLevel::Error,
                                "operator template-id names a non-template member",
                                operator_id.loc);
                            parsed_arguments =
                                parse_dependent_expression_template_argument_list(
                                    operator_id.loc);
                            template_lookup_error = true;
                        }
                        sem = collect_session_
                            .collect_qualified_member_access_expr(
                                std::move(expr.sem), qualifier_type,
                                member_name, is_arrow, op.loc);
                        sem.has_error =
                            sem.has_error || nested.has_error ||
                            operator_id.has_error || !parsed_arguments ||
                            template_lookup_error;
                        if (info) {
                            sem.has_explicit_template_arguments = true;
                            sem.explicit_template_arguments =
                                std::move(arguments);
                            sem.candidate_explicit_template_arguments =
                                std::move(candidate_arguments);
                            auto rejected = [&](cir::EntityId entity) {
                                auto found = std::find_if(
                                    sem.candidate_explicit_template_arguments
                                        .begin(),
                                    sem.candidate_explicit_template_arguments
                                        .end(),
                                    [&](const collect::
                                            CandidateExplicitTemplateArguments&
                                            entry) {
                                        return entry.template_entity ==
                                            entity;
                                    });
                                return found !=
                                        sem.candidate_explicit_template_arguments
                                            .end() &&
                                    !found->viable;
                            };
                            std::erase_if(sem.candidates, rejected);
                            if (rejected(sem.entity) &&
                                !sem.candidates.empty()) {
                                sem.entity = sem.candidates.back();
                                sem.type = collect_session_.file()
                                               .entity(sem.entity)
                                               .type;
                            }
                        }
                        sem.unparenthesized_id_or_member = true;
                    }
                } else if (!is_identifier_token(current().type)) {
                    diagnose(DiagnosticLevel::Error, "expected member name",
                             current_loc());
                    sem.has_error = true;
                } else {
                    Token terminal = current();
                    consume();
                    member_name = std::string(terminal.value);
                    sem = collect_session_.collect_qualified_member_access_expr(
                        std::move(expr.sem), qualifier_type, member_name,
                        is_arrow, op.loc);
                    sem.has_error = sem.has_error || nested.has_error;
                    if (sem.entity.valid()) {
                        materialize_deferred_static_data_member_expr(sem);
                    }
                    if (sem.has_error &&
                        sem.type_originates_from_template_parameter &&
                        in_constraint_substitution_failure_context()) {
                        note_constraint_substitution_failure();
                    }
                    sem.unparenthesized_id_or_member = true;
                }
                NodeId qualified_syntax = make_node(
                    NodeKind::MemberExpr, begin, last_consumed_raw_end(),
                    {expr.syntax}, text_payload(std::string(op.value) + member_name),
                    sem.has_error ? NodeFlagHasError : NodeFlagNone,
                    is_arrow ? 1 : 0);
                expr = ParsedExpr{qualified_syntax, std::move(sem)};
                continue;
            }
            NodeId member = parse_name_node(NodeKind::Name);
            std::string member_name = node_text(tree_.node(member));
            NodeId syntax = make_node(NodeKind::MemberExpr,
                                      begin,
                                      last_consumed_raw_end(),
                                      {expr.syntax, member},
                                      text_payload(op.value),
                                      NodeFlagNone,
                                      is_arrow ? 1 : 0);
            collect::ExprResult sem =
                collect_session_.collect_member_access_expr(std::move(expr.sem),
                                                            member_name,
                                                            is_arrow,
                                                            op.loc);
            if (sem.entity.valid()) {
                materialize_deferred_static_data_member_expr(sem);
            }
            if (sem.has_error && sem.type_originates_from_template_parameter &&
                in_constraint_substitution_failure_context()) {
                note_constraint_substitution_failure();
            }
            sem.unparenthesized_id_or_member = true;
            expr = ParsedExpr{syntax, std::move(sem)};
            continue;
        }
        if (check(TokenType::INCREMENT) || check(TokenType::DECREMENT)) {
            bool is_increment = check(TokenType::INCREMENT);
            Token op = current();
            size_t begin = tree_.node(expr.syntax).tokens.begin;
            consume();
            UnaryOperator sem_op = is_increment
                ? UnaryOperator::PostfixIncrement
                : UnaryOperator::PostfixDecrement;
            NodeId syntax = make_node(NodeKind::UnaryExpr,
                                      begin,
                                      last_consumed_raw_end(),
                                      {expr.syntax},
                                      text_payload(op.value),
                                      NodeFlagNone,
                                      static_cast<uint16_t>(sem_op));
            collect::ExprResult sem =
                collect_session_.collect_unary_expr(sem_op, std::move(expr.sem), op.loc);
            expr = ParsedExpr{syntax, std::move(sem)};
            continue;
        }
        break;
    }
    return expr;
}

Parser::ParsedExpr Parser::parse_statement_expression() {
    size_t begin = current_raw_index();
    SrcLoc loc = current().loc;
    match(TokenType::LEFT_PAREN);
    collect_session_.enter_statement_expression();
    ParsedStmt body = parse_compound_statement();
    collect_session_.leave_statement_expression();
    if (!match(TokenType::RIGHT_PAREN)) {
        diagnose(DiagnosticLevel::Error, "expected ')' after statement expression", current_loc());
    }
    NodeId syntax = make_node(NodeKind::StmtExpr,
                              begin,
                              last_consumed_raw_end(),
                              {body.syntax},
                              text_payload("({})"));
    collect::ExprResult sem =
        collect_session_.collect_statement_expr(std::move(body.sem), loc);
    return {syntax, std::move(sem)};
}

Parser::ParsedExpr Parser::parse_block_literal_expression() {
    size_t begin = current_raw_index();
    SrcLoc loc = current().loc;
    consume();
    std::vector<NodeId> children;

    std::vector<collect::ParamInput> params;
    if (check(TokenType::LEFT_PAREN)) {
        consume();
        if (check(TokenType::VOID) && peek(1).type == TokenType::RIGHT_PAREN) {
            consume();
        } else {
            while (!at_end() && !check(TokenType::RIGHT_PAREN)) {
                DeclarationParser param_parser(*this);
                cir::TypeRef param_type = param_parser.parse_declaration(true, true);
                collect::ParamInput param;
                param.name = param_parser.name;
                param.type = param_type;
                param.loc = current_loc();
                params.push_back(std::move(param));
                if (!match(TokenType::COMMA)) {
                    break;
                }
            }
        }
        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ')' after block literal parameters", current_loc());
        }
    }

    std::vector<std::string> body_identifiers;
    if (check(TokenType::LEFT_BRACE)) {
        size_t offset = 1;
        int depth = 1;
        while (depth > 0) {
            const Token& token = peek(offset);
            if (token.type == TokenType::Eof) {
                break;
            }
            if (token.type == TokenType::LEFT_BRACE) {
                ++depth;
            } else if (token.type == TokenType::RIGHT_BRACE) {
                --depth;
            } else if (token.type == TokenType::IDENTIFIER) {
                body_identifiers.push_back(std::string(token.value));
            }
            ++offset;
        }
    } else {
        diagnose(DiagnosticLevel::Error, "expected block literal body", current_loc());
    }

    collect::BlockLiteralStart start =
        collect_session_.begin_block_literal(std::move(params),
                                             body_identifiers,
                                             loc);
    ParsedStmt body = parse_compound_statement();
    children.push_back(body.syntax);
    collect::ExprResult sem =
        collect_session_.finish_block_literal(std::move(start),
                                              std::move(body.sem),
                                              loc);

    NodeId syntax = make_node(NodeKind::BlockExpr,
                              begin,
                              last_consumed_raw_end(),
                              children,
                              TextPayload{"block"});
    return {syntax, std::move(sem)};
}

Parser::ParsedExpr Parser::parse_lambda_expression() {
    size_t begin = current_raw_index();
    SrcLoc loc = current().loc;
    consume();

    collect::LambdaCaptureDefault capture_default =
        collect::LambdaCaptureDefault::None;
    std::vector<collect::LambdaCaptureItem> captures;
    auto skip_capture_item = [&] {
        int depth = 0;
        while (!at_end()) {
            if (depth == 0 && (check(TokenType::COMMA) ||
                               check(TokenType::RIGHT_BRACKET))) {
                break;
            }
            if (check(TokenType::LEFT_BRACKET) ||
                check(TokenType::LEFT_PAREN) ||
                check(TokenType::LEFT_BRACE)) {
                ++depth;
            } else if (check(TokenType::RIGHT_BRACKET) ||
                       check(TokenType::RIGHT_PAREN) ||
                       check(TokenType::RIGHT_BRACE)) {
                --depth;
            }
            consume();
        }
    };
    if (!check(TokenType::RIGHT_BRACKET)) {
        if (check(TokenType::ASSIGN) &&
            (peek(1).type == TokenType::COMMA ||
             peek(1).type == TokenType::RIGHT_BRACKET)) {
            capture_default = collect::LambdaCaptureDefault::ByCopy;
            consume();
            match(TokenType::COMMA);
        } else if (check(TokenType::BITWISE_AND) &&
                   (peek(1).type == TokenType::COMMA ||
                    peek(1).type == TokenType::RIGHT_BRACKET)) {
            capture_default = collect::LambdaCaptureDefault::ByRef;
            consume();
            match(TokenType::COMMA);
        }
        bool saw_this_capture = false;
        while (!at_end() && !check(TokenType::RIGHT_BRACKET)) {
            SrcLoc item_loc = current_loc();
            if (check(TokenType::THIS_KW) ||
                (check(TokenType::MULTIPLY) &&
                 peek(1).type == TokenType::THIS_KW)) {
                bool star_this = match(TokenType::MULTIPLY);
                consume();
                if (saw_this_capture) {
                    diagnose(DiagnosticLevel::Error,
                             "'this' appears more than once in the capture "
                             "list",
                             item_loc);
                } else {
                    saw_this_capture = true;
                    collect::LambdaCaptureItem item;
                    item.is_this = !star_this;
                    item.is_star_this = star_this;
                    item.loc = item_loc;
                    captures.push_back(std::move(item));
                }
            } else if (check(TokenType::ELLIPSIS) ||
                       (check(TokenType::BITWISE_AND) &&
                        peek(1).type == TokenType::ELLIPSIS)) {

                bool by_ref = match(TokenType::BITWISE_AND);
                consume();
                if (!check(TokenType::IDENTIFIER)) {
                    diagnose(DiagnosticLevel::Error,
                             "expected a capture name in the lambda-introducer",
                             current_loc());
                    skip_capture_item();
                } else {
                    std::string name(current().value);
                    consume();
                    bool duplicate = false;
                    for (const collect::LambdaCaptureItem& prior : captures) {
                        if (!prior.name.empty() && prior.name == name) {
                            diagnose(DiagnosticLevel::Error,
                                     "'" + name +
                                         "' appears more than once in the "
                                         "capture list",
                                     item_loc);
                            duplicate = true;
                            break;
                        }
                    }
                    if (!match(TokenType::ASSIGN)) {
                        diagnose(DiagnosticLevel::Error,
                                 "an init-capture pack requires an "
                                 "'= pattern' initializer",
                                 current_loc());
                        skip_capture_item();
                    } else {
                        std::optional<PackExpansionPattern> pattern =
                            try_parse_pack_expansion_pattern(
                                [&] {
                                    (void)parse_expression(
                                        PrecLevel::ASSIGNMENT);
                                },
                                /*expect_trailing_ellipsis=*/false);
                        if (!pattern.has_value() ||
                            !pattern->has_pack_names()) {
                            diagnose(DiagnosticLevel::Error,
                                     "init-capture pack initializer does not "
                                     "contain an unexpanded pack",
                                     item_loc);
                            (void)parse_expression(PrecLevel::ASSIGNMENT);
                        } else {
                            collect::LambdaCaptureItem item;
                            item.name = std::move(name);
                            item.by_ref = by_ref;
                            item.is_pack = true;
                            item.is_init_pack = true;
                            item.loc = item_loc;
                            bool arity_dependent = false;
                            std::optional<size_t> element_count =
                                resolve_pack_expansion_element_count(
                                    *pattern, &arity_dependent);
                            if (arity_dependent) {

                                parse_pack_expansion_pattern_deferred([&] {
                                    item.init =
                                        parse_expression(PrecLevel::ASSIGNMENT)
                                            .sem;
                                });
                            } else {
                                replay_pack_expansion_elements(
                                    *pattern,
                                    element_count.value_or(0),
                                    [&](size_t) {
                                        item.pack_inits.push_back(
                                            parse_expression(
                                                PrecLevel::ASSIGNMENT)
                                                .sem);
                                    });
                            }
                            if (!duplicate) {
                                captures.push_back(std::move(item));
                            }
                        }
                    }
                }
            } else {
                bool by_ref = match(TokenType::BITWISE_AND);
                if (!check(TokenType::IDENTIFIER)) {
                    diagnose(DiagnosticLevel::Error,
                             "expected a capture name in the lambda-introducer",
                             current_loc());
                    skip_capture_item();
                } else {
                    std::string name(current().value);
                    consume();
                    bool duplicate = false;
                    for (const collect::LambdaCaptureItem& prior : captures) {
                        if (!prior.name.empty() && prior.name == name) {
                            diagnose(DiagnosticLevel::Error,
                                     "'" + name +
                                         "' appears more than once in the "
                                         "capture list",
                                     item_loc);
                            duplicate = true;
                            break;
                        }
                    }
                    if (check(TokenType::ELLIPSIS)) {
                        consume();
                        if (!duplicate) {
                            collect::LambdaCaptureItem item;
                            item.name = std::move(name);
                            item.by_ref = by_ref;
                            item.is_pack = true;
                            item.loc = item_loc;
                            captures.push_back(std::move(item));
                        }
                    } else if (check(TokenType::ASSIGN)) {

                        consume();
                        ParsedExpr init =
                            parse_expression(PrecLevel::ASSIGNMENT);
                        if (!duplicate) {
                            collect::LambdaCaptureItem item;
                            item.name = std::move(name);
                            item.by_ref = by_ref;
                            item.init = std::move(init.sem);
                            item.loc = item_loc;
                            captures.push_back(std::move(item));
                        }
                    } else if (check(TokenType::LEFT_BRACE) ||
                               check(TokenType::LEFT_PAREN)) {
                        diagnose(DiagnosticLevel::Error,
                                 "brace- and paren-initialized init-captures "
                                 "are not supported yet",
                                 current_loc());
                        skip_capture_item();
                    } else if (capture_default ==
                                   collect::LambdaCaptureDefault::ByCopy &&
                               !by_ref) {
                        diagnose(DiagnosticLevel::Error,
                                 "'" + name +
                                     "' is already captured by the "
                                     "by-copy capture default",
                                 item_loc);
                    } else if (capture_default ==
                                   collect::LambdaCaptureDefault::ByRef &&
                               by_ref) {
                        diagnose(DiagnosticLevel::Error,
                                 "'&" + name +
                                     "' is redundant with the by-reference "
                                     "capture default",
                                 item_loc);
                    } else if (!duplicate) {
                        collect::LambdaCaptureItem item;
                        item.name = std::move(name);
                        item.by_ref = by_ref;
                        item.loc = item_loc;
                        captures.push_back(std::move(item));
                    }
                }
            }
            if (!match(TokenType::COMMA)) {
                break;
            }
        }
    }
    if (!match(TokenType::RIGHT_BRACKET)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ']' to close the lambda capture list",
                 current_loc());
    }

    collect::LambdaSpecifiers specifiers;
    auto parse_lambda_attributes = [&] {
        ParsedAttributes attrs = try_parse_standard_or_gnu_attributes();
        specifiers.attrs.append(std::move(attrs.attrs));
    };
    parse_lambda_attributes();

    collect::Session::TemplateInfo template_info;
    std::optional<collect::Session::InstantiationScope> template_header_scope;
    if (check(TokenType::LESS_THAN)) {
        if (parse_cxx_template_head(template_info,
                                    loc,
                                    /*parameter_depth=*/0,
                                    /*lambda_template_head=*/true)) {
            template_header_scope.emplace(
                collect_session_.begin_template_header(template_info, loc));
        }
        parse_lambda_attributes();
    }

    DeclarationParser lambda_invention(*this);
    lambda_invention.abbreviated_template_target = &template_info;

    std::vector<ParsedParam> parsed_params;
    bool entered_prototype_scope = false;
    if (match(TokenType::LEFT_PAREN)) {
        collect_session_.enter_scope(collect::ScopeFlags::PrototypeScope);
        entered_prototype_scope = true;

        parsed_params = parse_parameter_list(
            /*instantiate_default_arguments=*/true,
            TypeParseContext::type_only(
                TypeParseContext::Origin::LambdaParameter),
            /*is_variadic_out=*/nullptr,
            [&](ParsedParam& param, uint32_t parameter_index) {
                ParsedDeclarator parameter;
                parameter.type = param.type;
                parameter.type_ref = param.type_ref;
                parameter.loc = param.loc;
                rewrite_abbreviated_function_parameter(
                    lambda_invention,
                    parameter,
                    param.is_parameter_pack,
                    parameter_index,
                    param.abbreviated_type_constraints,
                    param.loc);
                param.type = parameter.type;
                param.type_ref = parameter.type_ref;
                if (param.name != "<anonymous>" &&
                    !param.is_parameter_pack_expansion_sentinel) {
                    param.prototype_entity =
                        collect_session_.bind_prototype_parameter(
                            param.name,
                            param.type_ref,
                            param.loc,
                            param.type_originates_from_template_parameter);
                }
            });
    }

    while (true) {
        if (check(TokenType::MUTABLE_KW)) {
            consume();
            specifiers.is_mutable = true;
            continue;
        }
        if (check(TokenType::STATIC)) {
            consume();
            specifiers.is_static = true;
            continue;
        }
        if (check(TokenType::CONSTEXPR_KW)) {
            consume();
            specifiers.is_constexpr = true;
            continue;
        }
        if (check(TokenType::CONSTEVAL_KW)) {
            consume();
            specifiers.is_consteval = true;
            continue;
        }
        if (check(TokenType::NOEXCEPT_KW)) {
            consume();
            specifiers.exception_spec =
                cir::FunctionExceptionSpecKind::NonThrowing;
            if (match(TokenType::LEFT_PAREN)) {
                ParsedExpr operand = parse_conditional_expression();
                if (!match(TokenType::RIGHT_PAREN)) {
                    diagnose(DiagnosticLevel::Error,
                             "expected ')' after lambda noexcept specifier",
                             current_loc());
                }
                specifiers.exception_spec =
                    collect_session_.evaluate_noexcept_spec(
                        operand.sem, last_consumed_loc());
            }
            continue;
        }
        if (check(TokenType::ATTRIBUTE_KW) ||
            (check(TokenType::LEFT_BRACKET) &&
             peek(1).type == TokenType::LEFT_BRACKET)) {
            parse_lambda_attributes();
            continue;
        }
        break;
    }
    if (specifiers.is_constexpr && specifiers.is_consteval) {
        diagnose(DiagnosticLevel::Error,
                 "a lambda cannot be both 'constexpr' and 'consteval'",
                 loc);
        specifiers.is_consteval = false;
    }

    cir::TypeId trailing_return{};
    if (match(TokenType::ARROW)) {
        parse_type_name(
            &trailing_return,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            TypeParseContext::type_only(
                TypeParseContext::Origin::TrailingReturnType));
        if (!trailing_return.valid()) {
            diagnose(DiagnosticLevel::Error,
                     "expected trailing return type after '->'",
                     current_loc());
        }
    }
    bool is_generic = !template_info.parameters.empty();
    if (match(TokenType::REQUIRES_KW)) {
        SrcLoc requires_loc = last_consumed_loc();
        size_t constraint_begin = 0;
        size_t constraint_end = 0;
        collect::Session::NormalizedConstraint normal_form;
        bool valid = parse_and_validate_constraint_expression(
            requires_loc,
            constraint_begin,
            constraint_end,
            nullptr,
            &normal_form);
        if (!is_generic) {
            diagnose(DiagnosticLevel::Error,
                     "a requires-clause on a lambda requires a generic lambda",
                     requires_loc);
        } else if (valid) {
            record_trailing_function_requires_clause(
                template_info,
                constraint_begin,
                constraint_end,
                std::move(normal_form));
        }
    }
    if (entered_prototype_scope) {
        collect_session_.leave_scope();
    }
    if (template_header_scope) {
        collect_session_.finish_template_header(
            std::move(*template_header_scope));
        template_header_scope.reset();
    }

    record_function_constraint_parameters(template_info, parsed_params);

    std::vector<collect::ParamInput> params =
        param_inputs_from_parsed_params(parsed_params,
                                        /*move_runtime_fragments=*/true);

    if (is_generic) {
        collect::LambdaClosureStart start =
            collect_session_.begin_generic_lambda_closure(std::move(params),
                                                          trailing_return,
                                                          specifiers,
                                                          capture_default,
                                                          std::move(captures),
                                                          template_info,
                                                          loc);
        if (module_replay_unit_.valid()) {

            collect_session_.file().entity_mut(start.call_operator)
                .origin_unit = module_replay_unit_;
            collect_session_.file().entity_mut(start.record.entity)
                .origin_unit = module_replay_unit_;
        }
        std::vector<NodeId> children;
        if (!check(TokenType::LEFT_BRACE)) {
            diagnose(DiagnosticLevel::Error, "expected lambda body",
                     current_loc());
            collect::ExprResult sem =
                collect_session_.finish_generic_lambda_closure(
                    std::move(start), std::move(template_info),
                    last_consumed_loc());
            sem.has_error = true;
            NodeId syntax = make_node(NodeKind::LambdaExpr,
                                      begin,
                                      last_consumed_raw_end(),
                                      children,
                                      TextPayload{"lambda"},
                                      NodeFlagHasError);
            return {syntax, std::move(sem)};
        }

        PendingMemberBody body;
        body.method_index = 0;
        body.body_begin = current_raw_index();
        body.body_end = skip_balanced_until_semicolon_or_brace();
        body.params = parsed_params;

        validate_member_template_body(template_info,
                                      start.call_operator,
                                      body,
                                      loc);
        if (!template_info.has_definition) {
            start.has_error = true;
        }
        uint64_t body_key = static_cast<uint64_t>(start.call_operator.index);
        member_template_bodies_[body_key] = body;
        collect_session_.track_speculative_rollback(
            [this, body_key] { member_template_bodies_.erase(body_key); });
        collect::ExprResult sem =
            collect_session_.finish_generic_lambda_closure(
                std::move(start), std::move(template_info),
                last_consumed_loc());
        NodeId syntax = make_node(NodeKind::LambdaExpr,
                                  begin,
                                  last_consumed_raw_end(),
                                  children,
                                  TextPayload{"lambda"});
        return {syntax, std::move(sem)};
    }

    collect::LambdaClosureStart start =
        collect_session_.begin_lambda_closure(std::move(params),
                                              trailing_return,
                                              specifiers,
                                              capture_default,
                                              std::move(captures),
                                              loc);

    std::vector<NodeId> children;
    if (check(TokenType::LEFT_BRACE)) {
        ParsedStmt body = parse_compound_statement();
        children.push_back(body.syntax);
        collect::ExprResult sem =
            collect_session_.finish_lambda_closure(std::move(start),
                                                   std::move(body.sem),
                                                   last_consumed_loc());
        NodeId syntax = make_node(NodeKind::LambdaExpr,
                                  begin,
                                  last_consumed_raw_end(),
                                  children,
                                  TextPayload{"lambda"});
        return {syntax, std::move(sem)};
    }

    diagnose(DiagnosticLevel::Error, "expected lambda body", current_loc());
    collect::StmtResult empty_body;
    collect::ExprResult sem =
        collect_session_.finish_lambda_closure(std::move(start),
                                               std::move(empty_body),
                                               loc);
    sem.has_error = true;
    NodeId syntax = make_node(NodeKind::LambdaExpr,
                              begin,
                              last_consumed_raw_end(),
                              children,
                              TextPayload{"lambda"},
                              NodeFlagHasError);
    return {syntax, std::move(sem)};
}

bool Parser::is_init_designator_start() const {
    if (check(TokenType::DOT) ||
        (check(TokenType::IDENTIFIER) &&
         peek(1).type == TokenType::COLON)) {
        return true;
    }
    if (!check(TokenType::LEFT_BRACKET)) {
        return false;
    }
    if (!lang_opts_.is_cxx_mode()) {
        return true;
    }

    int bracket_depth = 0;
    int paren_depth = 0;
    int brace_depth = 0;
    for (size_t offset = 0; offset < 4096; ++offset) {
        TokenType type = peek(offset).type;
        if (type == TokenType::LEFT_BRACKET) {
            ++bracket_depth;
        } else if (type == TokenType::RIGHT_BRACKET) {
            --bracket_depth;
            if (bracket_depth == 0 &&
                paren_depth == 0 && brace_depth == 0) {
                TokenType next = peek(offset + 1).type;
                return next == TokenType::ASSIGN ||
                       next == TokenType::DOT ||
                       next == TokenType::LEFT_BRACKET;
            }
        } else if (type == TokenType::LEFT_PAREN) {
            ++paren_depth;
        } else if (type == TokenType::RIGHT_PAREN) {
            if (paren_depth > 0) {
                --paren_depth;
            }
        } else if (type == TokenType::LEFT_BRACE) {
            ++brace_depth;
        } else if (type == TokenType::RIGHT_BRACE) {
            if (brace_depth > 0) {
                --brace_depth;
            }
        } else if (type == TokenType::Eof ||
                   type == TokenType::SEMICOLON) {
            break;
        }
    }
    return false;
}

Parser::ParsedDesignatorList Parser::parse_designator_list() {
    ParsedDesignatorList designators;
    while (is_init_designator_start()) {
        size_t begin = current_raw_index();
        SrcLoc loc = current_loc();
        if (match(TokenType::DOT)) {
            if (!is_identifier_token(current().type)) {
                diagnose(DiagnosticLevel::Error, "expected field name in initializer designator", current_loc());
                break;
            }
            NodeId field = parse_name_node(NodeKind::Name);
            designators.syntax.push_back(make_node(NodeKind::Designator,
                                                   begin,
                                                   last_consumed_raw_end(),
                                                   {field},
                                                   text_payload(".")));
            collect::InitDesignator sem;
            sem.kind = collect::InitDesignatorKind::Field;
            sem.field_name = node_text(tree_.node(field));
            sem.loc = loc;
            designators.sem.push_back(std::move(sem));
            continue;
        }
        if (match(TokenType::LEFT_BRACKET)) {
            ParsedExpr start = parse_assignment_expression();
            std::vector<NodeId> children{start.syntax};
            std::string spelling = "[]";
            collect::InitDesignator sem;
            sem.kind = collect::InitDesignatorKind::Index;
            sem.index = std::move(start.sem);
            sem.loc = loc;
            if (match(TokenType::ELLIPSIS)) {
                ParsedExpr end = parse_assignment_expression();
                children.push_back(end.syntax);
                spelling = "[...]";
                sem.kind = collect::InitDesignatorKind::Range;
                sem.range_end = std::move(end.sem);
            }
            if (!match(TokenType::RIGHT_BRACKET)) {
                diagnose(DiagnosticLevel::Error, "expected ']' after initializer designator", current_loc());
            }
            designators.syntax.push_back(make_node(NodeKind::Designator,
                                                   begin,
                                                   last_consumed_raw_end(),
                                                   children,
                                                   text_payload(std::move(spelling))));
            designators.sem.push_back(std::move(sem));
            continue;
        }

        NodeId field = parse_name_node(NodeKind::Name);
        if (!match(TokenType::COLON)) {
            diagnose(DiagnosticLevel::Error, "expected ':' after initializer designator", current_loc());
        }
        designators.syntax.push_back(make_node(NodeKind::Designator,
                                               begin,
                                               last_consumed_raw_end(),
                                               {field},
                                               text_payload(":")));
        collect::InitDesignator sem;
        sem.kind = collect::InitDesignatorKind::Field;
        sem.field_name = node_text(tree_.node(field));
        sem.loc = loc;
        designators.sem.push_back(std::move(sem));
    }
    return designators;
}

Parser::ParsedDesignatorList Parser::parse_offsetof_designator_list() {
    ParsedDesignatorList designators;
    auto append_field = [&](size_t begin, SrcLoc loc, bool had_dot) {
        if (!is_identifier_token(current().type)) {
            diagnose(DiagnosticLevel::Error,
                     "expected member name in __builtin_offsetof",
                     current_loc());
            return;
        }
        NodeId field = parse_name_node(NodeKind::Name);
        designators.syntax.push_back(make_node(NodeKind::Designator,
                                               begin,
                                               last_consumed_raw_end(),
                                               {field},
                                               text_payload(had_dot ? "." : "field")));
        collect::InitDesignator sem;
        sem.kind = collect::InitDesignatorKind::Field;
        sem.field_name = node_text(tree_.node(field));
        sem.loc = loc;
        designators.sem.push_back(std::move(sem));
    };

    append_field(current_raw_index(), current_loc(), false);
    while (!at_end() && !check(TokenType::RIGHT_PAREN)) {
        if (match(TokenType::LEFT_BRACKET)) {
            size_t begin = last_consumed_raw_index();
            SrcLoc loc = last_consumed_loc();
            ParsedExpr index = parse_expression();
            if (!match(TokenType::RIGHT_BRACKET)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ']' in __builtin_offsetof designator",
                         current_loc());
            }
            designators.syntax.push_back(make_node(NodeKind::Designator,
                                                   begin,
                                                   last_consumed_raw_end(),
                                                   {index.syntax},
                                                   text_payload("[]")));
            collect::InitDesignator sem;
            sem.kind = collect::InitDesignatorKind::Index;
            sem.index = std::move(index.sem);
            sem.loc = loc;
            designators.sem.push_back(std::move(sem));
            continue;
        }
        if (match(TokenType::DOT)) {
            append_field(last_consumed_raw_index(), last_consumed_loc(), true);
            continue;
        }
        break;
    }
    return designators;
}

Parser::ParsedExpr Parser::parse_init_list_expression(
    bool* has_dependent_pack_expansion) {
    size_t begin = current_raw_index();
    Token brace = current();
    if (!match(TokenType::LEFT_BRACE)) {
        diagnose(DiagnosticLevel::Error, "expected initializer list", current_loc());
        collect::ExprResult sem;
        sem.has_error = true;
        return {make_node(NodeKind::Error, begin, last_consumed_raw_end(), {}, {}, NodeFlagHasError),
                std::move(sem)};
    }

    std::vector<NodeId> children;
    std::vector<collect::InitElementInput> element_semantics;
    bool dependent_pack_expansion = false;
    while (!at_end() && !check(TokenType::RIGHT_BRACE)) {
        size_t element_begin = current_raw_index();
        SrcLoc element_loc = current_loc();

        if (lang_opts_.is_cxx_mode() && !is_init_designator_start()) {
            std::optional<PackExpansionPattern> pack_pattern =
                try_parse_expression_pack_expansion(TokenType::RIGHT_BRACE);
            if (pack_pattern.has_value()) {
                std::vector<collect::ExprResult> expanded;
                dependent_pack_expansion =
                    expand_expression_pack(*pack_pattern, expanded) ||
                    dependent_pack_expansion;
                children.push_back(pack_pattern->syntax);
                for (collect::ExprResult& element : expanded) {
                    collect::InitElementInput input;
                    input.value = std::move(element);
                    input.loc = element_loc;
                    element_semantics.push_back(std::move(input));
                }
                if (check(TokenType::RIGHT_BRACE)) {
                    break;
                }
                if (!match(TokenType::COMMA)) {
                    diagnose(DiagnosticLevel::Error,
                             "expected ',' or '}' in initializer list",
                             current_loc());
                    break;
                }
                continue;
            }
        }
        std::vector<NodeId> element_children;
        std::vector<collect::InitDesignator> designator_semantics;
        if (is_init_designator_start()) {
            ParsedDesignatorList designators = parse_designator_list();
            element_children.insert(element_children.end(),
                                    designators.syntax.begin(),
                                    designators.syntax.end());
            designator_semantics = std::move(designators.sem);
            match(TokenType::ASSIGN);
        }

        bool nested_dependent_pack_expansion = false;
        ParsedExpr value = check(TokenType::LEFT_BRACE)
            ? parse_init_list_expression(&nested_dependent_pack_expansion)
            : parse_assignment_expression();
        dependent_pack_expansion = dependent_pack_expansion ||
            nested_dependent_pack_expansion;
        element_children.push_back(value.syntax);
        collect::InitElementInput element;
        element.designators = std::move(designator_semantics);
        element.value = std::move(value.sem);
        element.loc = element_loc;
        element_semantics.push_back(std::move(element));
        children.push_back(make_node(NodeKind::InitElementExpr,
                                     element_begin,
                                     tree_.node(value.syntax).tokens.end,
                                     element_children));

        if (check(TokenType::RIGHT_BRACE)) {
            break;
        }
        if (!match(TokenType::COMMA)) {
            diagnose(DiagnosticLevel::Error, "expected ',' or '}' in initializer list", current_loc());
            break;
        }
    }

    if (!match(TokenType::RIGHT_BRACE)) {
        diagnose(DiagnosticLevel::Error, "expected '}' after initializer list", current_loc());
    }

    NodeId syntax = make_node(NodeKind::InitListExpr,
                              begin,
                              last_consumed_raw_end(),
                              children);
    collect::ExprResult sem =
        collect_session_.collect_init_list_expr(std::move(element_semantics), brace.loc);
    if (has_dependent_pack_expansion) {
        *has_dependent_pack_expansion =
            *has_dependent_pack_expansion || dependent_pack_expansion;
    }
    return {syntax, std::move(sem)};
}

std::optional<Parser::ParsedExpr> Parser::parse_builtin_primary_expression() {
    if (!is_identifier_token(current().type)) {
        return std::nullopt;
    }

    const Token builtin_token = current();
    const BuiltinInfo* builtin_info =
        BuiltinRegistry::instance().lookup(builtin_token.value);
    if (!builtin_info || !builtin_info->supported) {
        return std::nullopt;
    }

    switch (builtin_info->syntax) {
        case BuiltinSyntaxKind::Available: {

            size_t begin = current_raw_index();
            consume();
            if (!match(TokenType::LEFT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "expected '(' after __builtin_available",
                         current_loc());
            } else {
                int depth = 1;
                while (!at_end() && depth > 0) {
                    TokenType type = current().type;
                    consume();
                    if (type == TokenType::LEFT_PAREN) ++depth;
                    if (type == TokenType::RIGHT_PAREN) --depth;
                }
            }
            NodeId syntax = make_node(NodeKind::CallExpr,
                                      begin,
                                      last_consumed_raw_end(),
                                      {},
                                      text_payload("__builtin_available"));
            collect::ExprResult sem =
                collect_session_.make_integer_literal(1, "1", builtin_token.loc);
            return ParsedExpr{syntax, std::move(sem)};
        }
        case BuiltinSyntaxKind::TypePredicate: {
            size_t begin = current_raw_index();
            consume();
            if (!match(TokenType::LEFT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "expected '(' after builtin name",
                         current_loc());
            }
            cir::TypeId lhs_type{};
            NodeId lhs_syntax = parse_type_name(&lhs_type);
            if (!match(TokenType::COMMA)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ',' between builtin type operands",
                         current_loc());
            }
            cir::TypeId rhs_type{};
            NodeId rhs_syntax = parse_type_name(&rhs_type);
            if (!match(TokenType::RIGHT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ')' after builtin type operands",
                         current_loc());
            }
            NodeId syntax = make_node(NodeKind::CallExpr,
                                      begin,
                                      last_consumed_raw_end(),
                                      {lhs_syntax, rhs_syntax},
                                      text_payload(std::string(builtin_info->name)));
            collect::ExprResult sem =
                collect_session_.collect_builtin_types_compatible_expr(lhs_type,
                                                                       rhs_type,
                                                                       builtin_token.loc);
            return ParsedExpr{syntax, std::move(sem)};
        }
        case BuiltinSyntaxKind::ChooseExpr: {
            size_t begin = current_raw_index();
            consume();
            if (!match(TokenType::LEFT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "expected '(' after builtin name",
                         current_loc());
            }
            ParsedExpr condition = parse_assignment_expression();
            if (!match(TokenType::COMMA)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ',' after __builtin_choose_expr condition",
                         current_loc());
            }
            ParsedExpr true_expr = parse_assignment_expression();
            if (!match(TokenType::COMMA)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ',' after __builtin_choose_expr true operand",
                         current_loc());
            }
            ParsedExpr false_expr = parse_assignment_expression();
            if (!match(TokenType::RIGHT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ')' after __builtin_choose_expr operands",
                         current_loc());
            }
            NodeId syntax = make_node(NodeKind::CallExpr,
                                      begin,
                                      last_consumed_raw_end(),
                                      {condition.syntax, true_expr.syntax, false_expr.syntax},
                                      text_payload(std::string(builtin_info->name)));
            collect::ExprResult sem =
                collect_session_.collect_builtin_choose_expr(std::move(condition.sem),
                                                             std::move(true_expr.sem),
                                                             std::move(false_expr.sem),
                                                             builtin_token.loc);
            return ParsedExpr{syntax, std::move(sem)};
        }
        case BuiltinSyntaxKind::Offsetof: {
            size_t begin = current_raw_index();
            consume();
            if (!match(TokenType::LEFT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "expected '(' after builtin name",
                         current_loc());
            }
            cir::TypeId type{};
            NodeId type_syntax = parse_type_name(&type);
            if (!match(TokenType::COMMA)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ',' after __builtin_offsetof type operand",
                         current_loc());
            }
            ParsedDesignatorList designators = parse_offsetof_designator_list();
            if (!match(TokenType::RIGHT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ')' after __builtin_offsetof designator",
                         current_loc());
            }

            std::vector<NodeId> children{type_syntax};
            children.insert(children.end(),
                            designators.syntax.begin(),
                            designators.syntax.end());
            NodeId syntax = make_node(NodeKind::CallExpr,
                                      begin,
                                      last_consumed_raw_end(),
                                      children,
                                      text_payload(std::string(builtin_info->name)));
            collect::ExprResult sem =
                collect_session_.collect_offsetof_expr(type,
                                                       std::move(designators.sem),
                                                       builtin_token.loc);
            return ParsedExpr{syntax, std::move(sem)};
        }
        case BuiltinSyntaxKind::VaArg: {
            size_t begin = current_raw_index();
            consume();
            if (!match(TokenType::LEFT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "expected '(' after builtin name",
                         current_loc());
            }
            ParsedExpr va_list = parse_assignment_expression();
            if (!match(TokenType::COMMA)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ',' after __builtin_va_arg list operand",
                         current_loc());
            }
            cir::TypeId arg_type{};
            NodeId type_syntax = parse_type_name(&arg_type);
            if (!match(TokenType::RIGHT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ')' after __builtin_va_arg type operand",
                         current_loc());
            }
            NodeId syntax = make_node(NodeKind::CallExpr,
                                      begin,
                                      last_consumed_raw_end(),
                                      {va_list.syntax, type_syntax},
                                      text_payload(std::string(builtin_info->name)));
            collect::ExprResult sem =
                collect_session_.collect_va_arg_expr(std::move(va_list.sem),
                                                     arg_type,
                                                     builtin_token.loc);
            return ParsedExpr{syntax, std::move(sem)};
        }
        case BuiltinSyntaxKind::BitCast: {
            size_t begin = current_raw_index();
            consume();
            if (!match(TokenType::LEFT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "expected '(' after __builtin_bit_cast",
                         current_loc());
            }
            cir::TypeId target_type{};
            cir::TypeRef target_ref{};
            NodeId type_syntax = parse_type_name(
                &target_type, nullptr, nullptr, &target_ref);
            if (!match(TokenType::COMMA)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ',' after __builtin_bit_cast type operand",
                         current_loc());
            }
            ParsedExpr source = parse_assignment_expression();
            if (!match(TokenType::RIGHT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ')' after __builtin_bit_cast operands",
                         current_loc());
            }
            NodeId syntax = make_node(NodeKind::CallExpr,
                                      begin,
                                      last_consumed_raw_end(),
                                      {type_syntax, source.syntax},
                                      text_payload(std::string(builtin_info->name)));
            collect::ExprResult sem =
                collect_session_.collect_builtin_bit_cast_expr(
                    target_ref.type.valid()
                        ? target_ref
                        : collect_session_.type_ref(target_type),
                    std::move(source.sem), builtin_token.loc);
            return ParsedExpr{syntax, std::move(sem)};
        }
        case BuiltinSyntaxKind::ConvertVector: {
            size_t begin = current_raw_index();
            consume();
            if (!match(TokenType::LEFT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "expected '(' after builtin name",
                         current_loc());
            }
            ParsedExpr vector = parse_assignment_expression();
            if (!match(TokenType::COMMA)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ',' after __builtin_convertvector value operand",
                         current_loc());
            }
            cir::TypeId target_type{};
            cir::TypeRef target_ref{};
            NodeId type_syntax = parse_type_name(
                &target_type, nullptr, nullptr, &target_ref);
            if (!match(TokenType::RIGHT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ')' after __builtin_convertvector type operand",
                         current_loc());
            }
            NodeId syntax = make_node(NodeKind::CallExpr,
                                      begin,
                                      last_consumed_raw_end(),
                                      {vector.syntax, type_syntax},
                                      text_payload(std::string(builtin_info->name)));
            collect::ExprResult sem =
                collect_session_.collect_builtin_convertvector_expr(std::move(vector.sem),
                                                                    target_ref.type.valid()
                                                                        ? target_ref
                                                                        : collect_session_.type_ref(
                                                                              target_type),
                                                                    builtin_token.loc);
            return ParsedExpr{syntax, std::move(sem)};
        }
        case BuiltinSyntaxKind::TypeTrait: {
            size_t begin = current_raw_index();
            consume();
            bool opened = match(TokenType::LEFT_PAREN);
            if (!opened) {
                diagnose(DiagnosticLevel::Error,
                         "expected '(' after builtin type trait name",
                         current_loc());
            }

            std::vector<cir::TypeRef> types;
            std::vector<bool> pack_expansions;
            std::vector<NodeId> type_syntax;
            auto append_type_operand = [&](bool expands_pack) {
                cir::TypeId type{};
                cir::TypeRef type_ref{};
                type_syntax.push_back(parse_type_name(
                    &type, nullptr, nullptr, &type_ref));
                if (type.valid()) {
                    types.push_back(type_ref.type.valid()
                        ? type_ref
                        : collect_session_.type_ref(type));
                    pack_expansions.push_back(expands_pack);
                }
            };
            while (opened && !at_end() &&
                   !check(TokenType::RIGHT_PAREN)) {
                std::optional<PackExpansionPattern> pattern =
                    try_parse_pack_expansion_pattern(
                        [&] {
                            cir::TypeId ignored_type{};
                            cir::TypeRef ignored_ref{};
                            (void)parse_type_name(
                                &ignored_type, nullptr, nullptr,
                                &ignored_ref);
                        });
                if (pattern.has_value()) {
                    if (!pattern->has_pack_names()) {
                        diagnose(
                            DiagnosticLevel::Error,
                            "pack expansion does not contain an unexpanded "
                            "type parameter pack",
                            pattern->ellipsis_loc);
                        cursor_ = pattern->after_ellipsis_cursor;
                        last_consumed_raw_end_ =
                            pattern->after_ellipsis_last_consumed_raw_end;
                    } else {
                        bool arity_dependent = false;
                        std::optional<size_t> element_count =
                            resolve_pack_expansion_element_count(
                                *pattern, &arity_dependent);
                        if (arity_dependent) {
                            parse_pack_expansion_pattern_deferred(
                                [&] { append_type_operand(true); });
                            cursor_ = pattern->after_ellipsis_cursor;
                            last_consumed_raw_end_ =
                                pattern
                                    ->after_ellipsis_last_consumed_raw_end;
                        } else {
                            replay_pack_expansion_elements(
                                *pattern, element_count.value_or(0),
                                [&](size_t) {
                                    append_type_operand(false);
                                });
                        }
                    }
                } else {
                    append_type_operand(false);
                }
                if (!match(TokenType::COMMA)) {
                    break;
                }
            }
            if (!match(TokenType::RIGHT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ')' after builtin type trait operands",
                         current_loc());
            }

            bool valid_arity =
                static_cast<int>(types.size()) >= builtin_info->min_args &&
                (builtin_info->max_args < 0 ||
                 static_cast<int>(types.size()) <= builtin_info->max_args);
            if (!valid_arity) {
                std::string count = builtin_info->min_args ==
                        builtin_info->max_args
                    ? std::to_string(builtin_info->min_args)
                    : std::to_string(builtin_info->min_args) +
                          (builtin_info->max_args < 0
                               ? " or more"
                               : " to " +
                                     std::to_string(builtin_info->max_args));
                diagnose(DiagnosticLevel::Error,
                         std::string(builtin_info->name) + " requires " +
                             count + " type operand" +
                             (count == "1" ? "" : "s"),
                         builtin_token.loc);
            }

            NodeId syntax = make_node(NodeKind::CallExpr,
                                      begin,
                                      last_consumed_raw_end(),
                                      type_syntax,
                                      text_payload(std::string(builtin_info->name)));
            collect::ExprResult sem;
            if (valid_arity) {
                sem = collect_session_.collect_builtin_type_trait_expr(
                    builtin_info->kind, std::move(types),
                    std::move(pack_expansions), builtin_token.loc);
            } else {
                sem = collect_session_.make_boolean_literal(
                    false, "false", builtin_token.loc);
                sem.has_error = true;
            }
            return ParsedExpr{syntax, std::move(sem)};
        }
        case BuiltinSyntaxKind::TypeTransform:
        case BuiltinSyntaxKind::IntegerSequenceType:
        case BuiltinSyntaxKind::PackElementType:
            return std::nullopt;
        case BuiltinSyntaxKind::Call:
            return std::nullopt;
    }
    return std::nullopt;
}

std::optional<Parser::ParsedExpr>
Parser::parse_replayed_unary_left_fold_expression() {
    if (!check(TokenType::LEFT_PAREN) ||
        peek(1).type != TokenType::ELLIPSIS) {
        return std::nullopt;
    }
    BinaryOperator sem_op = binary_operator_for(peek(2).type);
    if (!is_fold_operator(sem_op)) {
        return std::nullopt;
    }

    size_t begin = current_raw_index();
    size_t replay_cursor = cursor_;
    size_t replay_last_consumed_raw_end = last_consumed_raw_end_;
    size_t replay_end_cursor = cursor_;
    size_t after_fold_cursor = cursor_;
    size_t after_fold_last_consumed_raw_end = last_consumed_raw_end_;
    SrcLoc ellipsis_loc = peek(1).loc;
    Token op = peek(2);
    std::vector<collect::Session::ParameterPackIdentity> packs;
    bool parsed_fold = false;
    {
        RevertingTentativeParsingAction tentative(*this);
        consume();
        consume();
        op = current();
        consume();
        replay_cursor = cursor_;
        replay_last_consumed_raw_end = last_consumed_raw_end_;
        auto capture_scope =
            collect_session_.begin_parameter_pack_pattern_capture();
        (void)parse_cast_expression();
        replay_end_cursor = cursor_;
        if (check(TokenType::RIGHT_PAREN)) {
            consume();
            after_fold_cursor = cursor_;
            after_fold_last_consumed_raw_end = last_consumed_raw_end_;
            parsed_fold = true;
        }
        packs = collect_session_.finish_parameter_pack_pattern_capture(
            capture_scope);
        tentative.revert();
    }
    if (!parsed_fold) {
        return std::nullopt;
    }

    std::vector<NodeId> retained_children;
    if (collect_session_.collecting_pattern() &&
        retain_constraint_normal_form_syntax_) {
        retained_children.push_back(retain_replayed_fold_operand_syntax(
            replay_cursor,
            replay_last_consumed_raw_end,
            replay_end_cursor,
            ellipsis_loc));
    }
    cursor_ = after_fold_cursor;
    last_consumed_raw_end_ = after_fold_last_consumed_raw_end;
    NodeId syntax = make_node(NodeKind::AmbiguousSyntax,
                              begin,
                              last_consumed_raw_end(),
                              retained_children,
                              text_payload("unary-left-fold"));

    auto make_error_fold = [&]() {
        collect::ExprResult error;
        error.has_error = true;
        error.type = collect_session_.file().unknown_type();
        return error;
    };

    if (packs.empty()) {
        diagnose(DiagnosticLevel::Error,
                 "fold expression pattern does not contain an unexpanded pack",
                 ellipsis_loc);
        return ParsedExpr{syntax, make_error_fold()};
    }

    auto retain_dependent_fold = [&](const auto& discovered_packs) {
        std::vector<collect::Session::ParameterPackIdentity> retained_packs;
        ParsedExpr retained = retain_replayed_fold_operand_semantics(
            replay_cursor,
            replay_last_consumed_raw_end,
            replay_end_cursor,
            after_fold_cursor,
            after_fold_last_consumed_raw_end,
            ellipsis_loc,
            &retained_packs);
        const auto& identities = retained_packs.empty()
            ? discovered_packs
            : retained_packs;
        std::vector<cir::TemplateValuePackReference> references;
        references.reserve(identities.size());
        for (const auto& pack : identities) {
            references.push_back(retained_pack_reference(pack));
        }
        return collect_session_.make_dependent_fold_expression(
            cir::TemplateValueFoldKind::UnaryLeft,
            sem_op,
            std::move(retained.sem),
            std::nullopt,
            std::move(references),
            op.loc);
    };

    if (should_retain_dependent_fold_pattern(
            collect_session_, retain_constraint_normal_form_syntax_)) {
        return ParsedExpr{syntax, retain_dependent_fold(packs)};
    }

    PackExpansionPattern fold_pattern;
    fold_pattern.packs = std::move(packs);
    fold_pattern.replay_cursor = replay_cursor;
    fold_pattern.replay_last_consumed_raw_end = replay_last_consumed_raw_end;
    fold_pattern.replay_end_cursor = replay_end_cursor;
    fold_pattern.after_ellipsis_cursor = after_fold_cursor;
    fold_pattern.after_ellipsis_last_consumed_raw_end =
        after_fold_last_consumed_raw_end;
    fold_pattern.ellipsis_loc = ellipsis_loc;
    bool dependent = false;
    std::optional<size_t> element_count =
        resolve_pack_expansion_element_count(fold_pattern, &dependent);
    if (dependent) {
        return ParsedExpr{syntax,
                          retain_dependent_fold(fold_pattern.packs)};
    }

    size_t count = element_count.value_or(0);
    if (count == 0) {
        if (std::optional<collect::ExprResult> identity =
                empty_unary_fold_identity(collect_session_, sem_op, op.loc)) {
            return ParsedExpr{syntax, std::move(*identity)};
        }
        diagnose(DiagnosticLevel::Error,
                 "empty unary fold expression has no identity for this operator",
                 op.loc);
        return ParsedExpr{syntax, make_error_fold()};
    }

    std::vector<collect::ExprResult> arguments;
    arguments.reserve(count);
    replay_pack_expansion_elements(
        fold_pattern,
        count,
        [&](size_t) { arguments.push_back(parse_cast_expression().sem); });

    collect::ExprResult folded = std::move(arguments.front());
    for (size_t i = 1; i < arguments.size(); ++i) {
        folded = collect_session_.collect_binary_expr(
            sem_op,
            std::move(folded),
            std::move(arguments[i]),
            op.loc);
    }
    return ParsedExpr{syntax, std::move(folded)};
}

std::optional<Parser::ParsedExpr>
Parser::parse_direct_unary_left_fold_expression() {
    if (!check(TokenType::LEFT_PAREN) ||
        peek(1).type != TokenType::ELLIPSIS ||
        !is_identifier_token(peek(3).type) ||
        peek(4).type != TokenType::RIGHT_PAREN) {
        return std::nullopt;
    }
    BinaryOperator sem_op = binary_operator_for(peek(2).type);
    if (!is_fold_operator(sem_op)) {
        return std::nullopt;
    }

    size_t begin = current_raw_index();
    consume();
    consume();
    Token op = current();
    consume();
    Token name_token = current();
    NodeId name = parse_name_node(NodeKind::Identifier);
    if (!match(TokenType::RIGHT_PAREN)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ')' after fold expression",
                 current_loc());
    }

    NodeId syntax = make_node(NodeKind::AmbiguousSyntax,
                              begin,
                              last_consumed_raw_end(),
                              {name},
                              text_payload("unary-left-fold"));

    auto make_dependent_fold = [&]() {
        collect_session_.bump_pattern_taint();
        collect::ExprResult dependent;
        dependent.type =
            collect_session_.file().dependent_type("fold expression");
        dependent.category = collect::ValueCategory::Dependent;
        return dependent;
    };

    if (!collect_session_.function_parameter_pack_name(name_token.value)) {
        diagnose(DiagnosticLevel::Error,
                 "fold expression pattern does not contain an unexpanded pack",
                 name_token.loc);
        collect::ExprResult error;
        error.has_error = true;
        error.type = collect_session_.file().unknown_type();
        return ParsedExpr{syntax, std::move(error)};
    }

    if (should_retain_dependent_fold_pattern(
            collect_session_, retain_constraint_normal_form_syntax_)) {
        return ParsedExpr{syntax, make_dependent_fold()};
    }

    std::optional<std::vector<collect::ExprResult>> arguments =
        collect_session_.function_parameter_pack_arguments(name_token.value,
                                                          name_token.loc);
    if (!arguments.has_value()) {
        return ParsedExpr{syntax, make_dependent_fold()};
    }
    if (arguments->empty()) {
        if (std::optional<collect::ExprResult> identity =
                empty_unary_fold_identity(collect_session_, sem_op, op.loc)) {
            return ParsedExpr{syntax, std::move(*identity)};
        }
        diagnose(DiagnosticLevel::Error,
                 "empty unary fold expression has no identity for this operator",
                 op.loc);
        collect::ExprResult error;
        error.has_error = true;
        error.type = collect_session_.file().unknown_type();
        return ParsedExpr{syntax, std::move(error)};
    }

    collect::ExprResult folded = std::move(arguments->front());
    for (size_t i = 1; i < arguments->size(); ++i) {
        folded = collect_session_.collect_binary_expr(
            sem_op,
            std::move(folded),
            std::move((*arguments)[i]),
            op.loc);
    }
    return ParsedExpr{syntax, std::move(folded)};
}

std::optional<Parser::ParsedExpr>
Parser::parse_direct_unary_right_fold_expression() {
    if (!check(TokenType::LEFT_PAREN) ||
        !is_identifier_token(peek(1).type) ||
        peek(3).type != TokenType::ELLIPSIS ||
        peek(4).type != TokenType::RIGHT_PAREN) {
        return std::nullopt;
    }
    BinaryOperator sem_op = binary_operator_for(peek(2).type);
    if (!is_fold_operator(sem_op)) {
        return std::nullopt;
    }

    size_t begin = current_raw_index();
    consume();
    Token name_token = current();
    NodeId name = parse_name_node(NodeKind::Identifier);
    Token op = current();
    consume();
    consume();
    if (!match(TokenType::RIGHT_PAREN)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ')' after fold expression",
                 current_loc());
    }

    NodeId syntax = make_node(NodeKind::AmbiguousSyntax,
                              begin,
                              last_consumed_raw_end(),
                              {name},
                              text_payload("unary-right-fold"));

    auto make_dependent_fold = [&]() {
        collect_session_.bump_pattern_taint();
        collect::ExprResult dependent;
        dependent.type =
            collect_session_.file().dependent_type("fold expression");
        dependent.category = collect::ValueCategory::Dependent;
        return dependent;
    };

    if (!collect_session_.function_parameter_pack_name(name_token.value)) {
        diagnose(DiagnosticLevel::Error,
                 "fold expression pattern does not contain an unexpanded pack",
                 name_token.loc);
        collect::ExprResult error;
        error.has_error = true;
        error.type = collect_session_.file().unknown_type();
        return ParsedExpr{syntax, std::move(error)};
    }

    if (should_retain_dependent_fold_pattern(
            collect_session_, retain_constraint_normal_form_syntax_)) {
        return ParsedExpr{syntax, make_dependent_fold()};
    }

    std::optional<std::vector<collect::ExprResult>> arguments =
        collect_session_.function_parameter_pack_arguments(name_token.value,
                                                          name_token.loc);
    if (!arguments.has_value()) {
        return ParsedExpr{syntax, make_dependent_fold()};
    }
    if (arguments->empty()) {
        if (std::optional<collect::ExprResult> identity =
                empty_unary_fold_identity(collect_session_, sem_op, op.loc)) {
            return ParsedExpr{syntax, std::move(*identity)};
        }
        diagnose(DiagnosticLevel::Error,
                 "empty unary fold expression has no identity for this operator",
                 op.loc);
        collect::ExprResult error;
        error.has_error = true;
        error.type = collect_session_.file().unknown_type();
        return ParsedExpr{syntax, std::move(error)};
    }

    collect::ExprResult folded = std::move(arguments->back());
    for (size_t i = arguments->size() - 1; i > 0; --i) {
        folded = collect_session_.collect_binary_expr(
            sem_op,
            std::move((*arguments)[i - 1]),
            std::move(folded),
            op.loc);
    }
    return ParsedExpr{syntax, std::move(folded)};
}

std::optional<Parser::ParsedExpr>
Parser::parse_replayed_unary_right_fold_expression() {
    if (!check(TokenType::LEFT_PAREN)) {
        return std::nullopt;
    }

    std::optional<size_t> ellipsis_offset;
    int paren_depth = 0;
    int bracket_depth = 0;
    int brace_depth = 0;
    for (size_t offset = 1; true; ++offset) {
        TokenType type = peek(offset).type;
        if (type == TokenType::Eof) {
            return std::nullopt;
        }
        if (paren_depth == 0 && bracket_depth == 0 && brace_depth == 0 &&
            type == TokenType::RIGHT_PAREN) {
            return std::nullopt;
        }
        if (paren_depth == 0 && bracket_depth == 0 && brace_depth == 0 &&
            type == TokenType::ELLIPSIS && offset >= 2 &&
            is_fold_operator(
                binary_operator_for(peek(offset - 1).type)) &&
            peek(offset + 1).type == TokenType::RIGHT_PAREN) {
            ellipsis_offset = offset;
            break;
        }
        switch (type) {
            case TokenType::LEFT_PAREN:
                ++paren_depth;
                break;
            case TokenType::RIGHT_PAREN:
                if (paren_depth > 0) {
                    --paren_depth;
                }
                break;
            case TokenType::LEFT_BRACKET:
                ++bracket_depth;
                break;
            case TokenType::RIGHT_BRACKET:
                if (bracket_depth > 0) {
                    --bracket_depth;
                }
                break;
            case TokenType::LEFT_BRACE:
                ++brace_depth;
                break;
            case TokenType::RIGHT_BRACE:
                if (brace_depth > 0) {
                    --brace_depth;
                }
                break;
            default:
                break;
        }
    }
    if (!ellipsis_offset.has_value() || *ellipsis_offset < 3 ||
        peek(*ellipsis_offset + 1).type != TokenType::RIGHT_PAREN) {
        return std::nullopt;
    }
    BinaryOperator sem_op =
        binary_operator_for(peek(*ellipsis_offset - 1).type);
    if (!is_fold_operator(sem_op)) {
        return std::nullopt;
    }

    size_t begin = current_raw_index();
    size_t replay_cursor = cursor_;
    size_t replay_last_consumed_raw_end = last_consumed_raw_end_;
    size_t replay_end_cursor = cursor_;
    size_t after_fold_cursor = cursor_;
    size_t after_fold_last_consumed_raw_end = last_consumed_raw_end_;
    Token op;
    SrcLoc ellipsis_loc{};
    std::vector<collect::Session::ParameterPackIdentity> packs;
    bool parsed_fold = false;
    {
        RevertingTentativeParsingAction tentative(*this);
        consume();
        replay_cursor = cursor_;
        replay_last_consumed_raw_end = last_consumed_raw_end_;
        auto capture_scope =
            collect_session_.begin_parameter_pack_pattern_capture();
        (void)parse_cast_expression();
        replay_end_cursor = cursor_;
        op = current();
        if (binary_operator_for(op.type) == sem_op) {
            consume();
            if (check(TokenType::ELLIPSIS)) {
                ellipsis_loc = current().loc;
                consume();
                if (check(TokenType::RIGHT_PAREN)) {
                    consume();
                    after_fold_cursor = cursor_;
                    after_fold_last_consumed_raw_end =
                        last_consumed_raw_end_;
                    parsed_fold = true;
                }
            }
        }
        packs = collect_session_.finish_parameter_pack_pattern_capture(
            capture_scope);
        tentative.revert();
    }
    if (!parsed_fold) {
        return std::nullopt;
    }

    std::vector<NodeId> retained_children;
    if (collect_session_.collecting_pattern() &&
        retain_constraint_normal_form_syntax_) {
        retained_children.push_back(retain_replayed_fold_operand_syntax(
            replay_cursor,
            replay_last_consumed_raw_end,
            replay_end_cursor,
            ellipsis_loc));
    }
    cursor_ = after_fold_cursor;
    last_consumed_raw_end_ = after_fold_last_consumed_raw_end;
    NodeId syntax = make_node(NodeKind::AmbiguousSyntax,
                              begin,
                              last_consumed_raw_end(),
                              retained_children,
                              text_payload("unary-right-fold"));

    auto make_error_fold = [&]() {
        collect::ExprResult error;
        error.has_error = true;
        error.type = collect_session_.file().unknown_type();
        return error;
    };

    if (packs.empty()) {
        diagnose(DiagnosticLevel::Error,
                 "fold expression pattern does not contain an unexpanded pack",
                 ellipsis_loc);
        return ParsedExpr{syntax, make_error_fold()};
    }

    auto retain_dependent_fold = [&](const auto& discovered_packs) {
        std::vector<collect::Session::ParameterPackIdentity> retained_packs;
        ParsedExpr retained = retain_replayed_fold_operand_semantics(
            replay_cursor,
            replay_last_consumed_raw_end,
            replay_end_cursor,
            after_fold_cursor,
            after_fold_last_consumed_raw_end,
            ellipsis_loc,
            &retained_packs);
        const auto& identities = retained_packs.empty()
            ? discovered_packs
            : retained_packs;
        std::vector<cir::TemplateValuePackReference> references;
        references.reserve(identities.size());
        for (const auto& pack : identities) {
            references.push_back(retained_pack_reference(pack));
        }
        return collect_session_.make_dependent_fold_expression(
            cir::TemplateValueFoldKind::UnaryRight,
            sem_op,
            std::move(retained.sem),
            std::nullopt,
            std::move(references),
            op.loc);
    };

    if (should_retain_dependent_fold_pattern(
            collect_session_, retain_constraint_normal_form_syntax_)) {
        return ParsedExpr{syntax, retain_dependent_fold(packs)};
    }

    PackExpansionPattern fold_pattern;
    fold_pattern.packs = std::move(packs);
    fold_pattern.replay_cursor = replay_cursor;
    fold_pattern.replay_last_consumed_raw_end = replay_last_consumed_raw_end;
    fold_pattern.replay_end_cursor = replay_end_cursor;
    fold_pattern.after_ellipsis_cursor = after_fold_cursor;
    fold_pattern.after_ellipsis_last_consumed_raw_end =
        after_fold_last_consumed_raw_end;
    fold_pattern.ellipsis_loc = ellipsis_loc;
    bool dependent = false;
    std::optional<size_t> element_count =
        resolve_pack_expansion_element_count(fold_pattern, &dependent);
    if (dependent) {
        return ParsedExpr{syntax,
                          retain_dependent_fold(fold_pattern.packs)};
    }

    size_t count = element_count.value_or(0);
    if (count == 0) {
        if (std::optional<collect::ExprResult> identity =
                empty_unary_fold_identity(collect_session_, sem_op, op.loc)) {
            return ParsedExpr{syntax, std::move(*identity)};
        }
        diagnose(DiagnosticLevel::Error,
                 "empty unary fold expression has no identity for this operator",
                 op.loc);
        return ParsedExpr{syntax, make_error_fold()};
    }

    std::vector<collect::ExprResult> arguments;
    arguments.reserve(count);
    replay_pack_expansion_elements(
        fold_pattern,
        count,
        [&](size_t) { arguments.push_back(parse_cast_expression().sem); });

    collect::ExprResult folded = std::move(arguments.back());
    for (size_t i = arguments.size() - 1; i > 0; --i) {
        folded = collect_session_.collect_binary_expr(
            sem_op,
            std::move(arguments[i - 1]),
            std::move(folded),
            op.loc);
    }
    return ParsedExpr{syntax, std::move(folded)};
}

std::optional<Parser::ParsedExpr>
Parser::parse_replayed_binary_right_fold_expression() {
    if (!check(TokenType::LEFT_PAREN)) {
        return std::nullopt;
    }

    std::optional<size_t> ellipsis_offset;
    int paren_depth = 0;
    int bracket_depth = 0;
    int brace_depth = 0;
    for (size_t offset = 1; true; ++offset) {
        TokenType type = peek(offset).type;
        if (type == TokenType::Eof) {
            return std::nullopt;
        }
        if (paren_depth == 0 && bracket_depth == 0 && brace_depth == 0 &&
            type == TokenType::RIGHT_PAREN) {
            return std::nullopt;
        }
        if (paren_depth == 0 && bracket_depth == 0 && brace_depth == 0 &&
            type == TokenType::ELLIPSIS && offset >= 2 &&
            is_fold_operator(
                binary_operator_for(peek(offset - 1).type)) &&
            is_fold_operator(
                binary_operator_for(peek(offset + 1).type))) {
            ellipsis_offset = offset;
            break;
        }
        switch (type) {
            case TokenType::LEFT_PAREN:
                ++paren_depth;
                break;
            case TokenType::RIGHT_PAREN:
                if (paren_depth > 0) {
                    --paren_depth;
                }
                break;
            case TokenType::LEFT_BRACKET:
                ++bracket_depth;
                break;
            case TokenType::RIGHT_BRACKET:
                if (bracket_depth > 0) {
                    --bracket_depth;
                }
                break;
            case TokenType::LEFT_BRACE:
                ++brace_depth;
                break;
            case TokenType::RIGHT_BRACE:
                if (brace_depth > 0) {
                    --brace_depth;
                }
                break;
            default:
                break;
        }
    }
    if (!ellipsis_offset.has_value() || *ellipsis_offset < 3 ||
        peek(*ellipsis_offset + 1).type == TokenType::RIGHT_PAREN) {
        return std::nullopt;
    }
    BinaryOperator sem_op =
        binary_operator_for(peek(*ellipsis_offset - 1).type);
    BinaryOperator sem_op2 =
        binary_operator_for(peek(*ellipsis_offset + 1).type);
    if (!is_fold_operator(sem_op) ||
        !is_fold_operator(sem_op2)) {
        return std::nullopt;
    }

    size_t begin = current_raw_index();
    size_t replay_cursor = cursor_;
    size_t replay_last_consumed_raw_end = last_consumed_raw_end_;
    size_t replay_end_cursor = cursor_;
    size_t init_cursor = cursor_;
    size_t init_last_consumed_raw_end = last_consumed_raw_end_;
    size_t init_end_cursor = cursor_;
    size_t after_fold_cursor = cursor_;
    size_t after_fold_last_consumed_raw_end = last_consumed_raw_end_;
    Token op;
    Token op2;
    SrcLoc ellipsis_loc{};
    std::vector<collect::Session::ParameterPackIdentity> packs;
    std::vector<collect::Session::ParameterPackIdentity> init_packs;
    bool parsed_fold = false;
    {
        RevertingTentativeParsingAction tentative(*this);
        consume();
        replay_cursor = cursor_;
        replay_last_consumed_raw_end = last_consumed_raw_end_;
        auto capture_scope =
            collect_session_.begin_parameter_pack_pattern_capture();
        (void)parse_cast_expression();
        replay_end_cursor = cursor_;
        packs = collect_session_.finish_parameter_pack_pattern_capture(
            capture_scope);
        op = current();
        if (binary_operator_for(op.type) == sem_op) {
            consume();
            if (check(TokenType::ELLIPSIS)) {
                ellipsis_loc = current().loc;
                consume();
                op2 = current();
                if (binary_operator_for(op2.type) == sem_op2) {
                    consume();
                    init_cursor = cursor_;
                    init_last_consumed_raw_end = last_consumed_raw_end_;
                    auto init_capture_scope =
                        collect_session_.begin_parameter_pack_pattern_capture();
                    (void)parse_cast_expression();
                    init_end_cursor = cursor_;
                    init_packs =
                        collect_session_.finish_parameter_pack_pattern_capture(
                            init_capture_scope);
                    if (check(TokenType::RIGHT_PAREN)) {
                        consume();
                        after_fold_cursor = cursor_;
                        after_fold_last_consumed_raw_end =
                            last_consumed_raw_end_;
                        parsed_fold = true;
                    }
                }
            }
        }
        tentative.revert();
    }
    if (!parsed_fold) {
        return std::nullopt;
    }
    if (packs.empty()) {
        return std::nullopt;
    }

    std::vector<NodeId> retained_children;
    if (collect_session_.collecting_pattern() &&
        retain_constraint_normal_form_syntax_) {
        retained_children.push_back(retain_replayed_fold_operand_syntax(
            replay_cursor,
            replay_last_consumed_raw_end,
            replay_end_cursor,
            ellipsis_loc));
        retained_children.push_back(retain_replayed_fold_operand_syntax(
            init_cursor,
            init_last_consumed_raw_end,
            init_end_cursor,
            ellipsis_loc));
    }
    cursor_ = after_fold_cursor;
    last_consumed_raw_end_ = after_fold_last_consumed_raw_end;
    NodeId syntax = make_node(NodeKind::AmbiguousSyntax,
                              begin,
                              last_consumed_raw_end(),
                              retained_children,
                              text_payload("binary-right-fold"));

    auto make_error_fold = [&]() {
        collect::ExprResult error;
        error.has_error = true;
        error.type = collect_session_.file().unknown_type();
        return error;
    };

    if (sem_op != sem_op2) {
        diagnose(DiagnosticLevel::Error,
                 "binary fold operators must match",
                 op2.loc);
    }
    if (!init_packs.empty()) {
        diagnose(DiagnosticLevel::Error,
                 "binary fold expression contains unexpanded packs on both sides",
                 ellipsis_loc);
        return ParsedExpr{syntax, make_error_fold()};
    }

    auto retain_dependent_fold = [&](const auto& discovered_packs) {
        std::vector<collect::Session::ParameterPackIdentity> retained_packs;
        ParsedExpr retained_pattern =
            retain_replayed_fold_operand_semantics(
                replay_cursor,
                replay_last_consumed_raw_end,
                replay_end_cursor,
                after_fold_cursor,
                after_fold_last_consumed_raw_end,
                ellipsis_loc,
                &retained_packs);
        ParsedExpr retained_initializer =
            retain_replayed_fold_operand_semantics(
                init_cursor,
                init_last_consumed_raw_end,
                init_end_cursor,
                after_fold_cursor,
                after_fold_last_consumed_raw_end,
                ellipsis_loc);
        const auto& identities = retained_packs.empty()
            ? discovered_packs
            : retained_packs;
        std::vector<cir::TemplateValuePackReference> references;
        references.reserve(identities.size());
        for (const auto& pack : identities) {
            references.push_back(retained_pack_reference(pack));
        }
        return collect_session_.make_dependent_fold_expression(
            cir::TemplateValueFoldKind::BinaryRight,
            sem_op,
            std::move(retained_pattern.sem),
            std::optional<collect::ExprResult>(
                std::move(retained_initializer.sem)),
            std::move(references),
            op.loc);
    };

    if (should_retain_dependent_fold_pattern(
            collect_session_, retain_constraint_normal_form_syntax_)) {
        return ParsedExpr{syntax, retain_dependent_fold(packs)};
    }

    PackExpansionPattern fold_pattern;
    fold_pattern.packs = std::move(packs);
    fold_pattern.replay_cursor = replay_cursor;
    fold_pattern.replay_last_consumed_raw_end = replay_last_consumed_raw_end;
    fold_pattern.replay_end_cursor = replay_end_cursor;
    fold_pattern.after_ellipsis_cursor = after_fold_cursor;
    fold_pattern.after_ellipsis_last_consumed_raw_end =
        after_fold_last_consumed_raw_end;
    fold_pattern.ellipsis_loc = ellipsis_loc;
    bool dependent = false;
    std::optional<size_t> element_count =
        resolve_pack_expansion_element_count(fold_pattern, &dependent);
    if (dependent) {
        return ParsedExpr{syntax,
                          retain_dependent_fold(fold_pattern.packs)};
    }

    cursor_ = init_cursor;
    last_consumed_raw_end_ = init_last_consumed_raw_end;
    ParsedExpr init = parse_cast_expression();
    if (cursor_ != init_end_cursor) {
        diagnose(DiagnosticLevel::Error,
                 "could not replay fold expression init",
                 ellipsis_loc);
        cursor_ = init_end_cursor;
    }

    std::vector<collect::ExprResult> arguments;
    size_t count = element_count.value_or(0);
    arguments.reserve(count);
    replay_pack_expansion_elements(
        fold_pattern,
        count,
        [&](size_t) { arguments.push_back(parse_cast_expression().sem); });

    collect::ExprResult folded = std::move(init.sem);
    for (size_t i = arguments.size(); i > 0; --i) {
        folded = collect_session_.collect_binary_expr(
            sem_op,
            std::move(arguments[i - 1]),
            std::move(folded),
            op.loc);
    }
    return ParsedExpr{syntax, std::move(folded)};
}

std::optional<Parser::ParsedExpr>
Parser::parse_direct_binary_right_fold_expression() {
    if (!check(TokenType::LEFT_PAREN) ||
        !is_identifier_token(peek(1).type) ||
        peek(3).type != TokenType::ELLIPSIS) {
        return std::nullopt;
    }
    if (!collect_session_.function_parameter_pack_name(peek(1).value)) {
        return std::nullopt;
    }
    BinaryOperator sem_op = binary_operator_for(peek(2).type);
    BinaryOperator sem_op2 = binary_operator_for(peek(4).type);
    if (!is_fold_operator(sem_op) ||
        !is_fold_operator(sem_op2)) {
        return std::nullopt;
    }

    size_t begin = current_raw_index();
    consume();
    Token name_token = current();
    NodeId name = parse_name_node(NodeKind::Identifier);
    Token op = current();
    consume();
    consume();
    Token op2 = current();
    consume();
    if (sem_op != sem_op2) {
        diagnose(DiagnosticLevel::Error,
                 "binary fold operators must match",
                 op2.loc);
    }
    bool init_is_direct_function_pack =
        is_identifier_token(current().type) &&
        collect_session_.function_parameter_pack_name(current().value) &&
        peek(1).type == TokenType::RIGHT_PAREN;
    SrcLoc init_loc = current().loc;
    ParsedExpr init = parse_cast_expression();
    if (init_is_direct_function_pack) {
        diagnose(DiagnosticLevel::Error,
                 "binary fold expression contains unexpanded packs on both sides",
                 init_loc);
    }
    if (!match(TokenType::RIGHT_PAREN)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ')' after fold expression",
                 current_loc());
    }

    NodeId syntax = make_node(NodeKind::AmbiguousSyntax,
                              begin,
                              last_consumed_raw_end(),
                              {name, init.syntax},
                              text_payload("binary-right-fold"));

    auto make_dependent_fold = [&]() {
        collect_session_.bump_pattern_taint();
        collect::ExprResult dependent;
        dependent.type =
            collect_session_.file().dependent_type("fold expression");
        dependent.category = collect::ValueCategory::Dependent;
        return dependent;
    };

    if (should_retain_dependent_fold_pattern(
            collect_session_, retain_constraint_normal_form_syntax_)) {
        return ParsedExpr{syntax, make_dependent_fold()};
    }

    std::optional<std::vector<collect::ExprResult>> arguments =
        collect_session_.function_parameter_pack_arguments(name_token.value,
                                                          name_token.loc);
    if (!arguments.has_value()) {
        return ParsedExpr{syntax, make_dependent_fold()};
    }
    collect::ExprResult folded = std::move(init.sem);
    for (size_t i = arguments->size(); i > 0; --i) {
        folded = collect_session_.collect_binary_expr(
            sem_op,
            std::move((*arguments)[i - 1]),
            std::move(folded),
            op.loc);
    }
    return ParsedExpr{syntax, std::move(folded)};
}

std::optional<Parser::ParsedExpr>
Parser::parse_replayed_binary_left_fold_expression() {
    if (!check(TokenType::LEFT_PAREN)) {
        return std::nullopt;
    }

    std::optional<size_t> ellipsis_offset;
    int paren_depth = 0;
    int bracket_depth = 0;
    int brace_depth = 0;
    for (size_t offset = 1; true; ++offset) {
        TokenType type = peek(offset).type;
        if (type == TokenType::Eof) {
            return std::nullopt;
        }
        if (paren_depth == 0 && bracket_depth == 0 && brace_depth == 0 &&
            type == TokenType::RIGHT_PAREN) {
            return std::nullopt;
        }
        if (paren_depth == 0 && bracket_depth == 0 && brace_depth == 0 &&
            type == TokenType::ELLIPSIS && offset >= 2 &&
            is_fold_operator(
                binary_operator_for(peek(offset - 1).type)) &&
            is_fold_operator(
                binary_operator_for(peek(offset + 1).type))) {
            ellipsis_offset = offset;
            break;
        }
        switch (type) {
            case TokenType::LEFT_PAREN:
                ++paren_depth;
                break;
            case TokenType::RIGHT_PAREN:
                if (paren_depth > 0) {
                    --paren_depth;
                }
                break;
            case TokenType::LEFT_BRACKET:
                ++bracket_depth;
                break;
            case TokenType::RIGHT_BRACKET:
                if (bracket_depth > 0) {
                    --bracket_depth;
                }
                break;
            case TokenType::LEFT_BRACE:
                ++brace_depth;
                break;
            case TokenType::RIGHT_BRACE:
                if (brace_depth > 0) {
                    --brace_depth;
                }
                break;
            default:
                break;
        }
    }
    if (!ellipsis_offset.has_value() || *ellipsis_offset < 3 ||
        peek(*ellipsis_offset + 1).type == TokenType::RIGHT_PAREN) {
        return std::nullopt;
    }
    BinaryOperator sem_op =
        binary_operator_for(peek(*ellipsis_offset - 1).type);
    BinaryOperator sem_op2 =
        binary_operator_for(peek(*ellipsis_offset + 1).type);
    if (!is_fold_operator(sem_op) ||
        !is_fold_operator(sem_op2)) {
        return std::nullopt;
    }

    size_t begin = current_raw_index();
    size_t init_cursor = cursor_;
    size_t init_last_consumed_raw_end = last_consumed_raw_end_;
    size_t init_end_cursor = cursor_;
    size_t replay_cursor = cursor_;
    size_t replay_last_consumed_raw_end = last_consumed_raw_end_;
    size_t replay_end_cursor = cursor_;
    size_t after_fold_cursor = cursor_;
    size_t after_fold_last_consumed_raw_end = last_consumed_raw_end_;
    Token op;
    Token op2;
    SrcLoc ellipsis_loc{};
    std::vector<collect::Session::ParameterPackIdentity> init_packs;
    std::vector<collect::Session::ParameterPackIdentity> packs;
    bool parsed_fold = false;
    {
        RevertingTentativeParsingAction tentative(*this);
        consume();
        init_cursor = cursor_;
        init_last_consumed_raw_end = last_consumed_raw_end_;
        auto init_capture_scope =
            collect_session_.begin_parameter_pack_pattern_capture();
        (void)parse_cast_expression();
        init_end_cursor = cursor_;
        init_packs = collect_session_.finish_parameter_pack_pattern_capture(
            init_capture_scope);
        op = current();
        if (binary_operator_for(op.type) == sem_op) {
            consume();
            if (check(TokenType::ELLIPSIS)) {
                ellipsis_loc = current().loc;
                consume();
                op2 = current();
                if (binary_operator_for(op2.type) == sem_op2) {
                    consume();
                    replay_cursor = cursor_;
                    replay_last_consumed_raw_end = last_consumed_raw_end_;
                    auto capture_scope =
                        collect_session_.begin_parameter_pack_pattern_capture();
                    (void)parse_cast_expression();
                    replay_end_cursor = cursor_;
                    packs =
                        collect_session_.finish_parameter_pack_pattern_capture(
                            capture_scope);
                    if (check(TokenType::RIGHT_PAREN)) {
                        consume();
                        after_fold_cursor = cursor_;
                        after_fold_last_consumed_raw_end =
                            last_consumed_raw_end_;
                        parsed_fold = true;
                    }
                }
            }
        }
        tentative.revert();
    }
    if (!parsed_fold) {
        return std::nullopt;
    }
    bool init_has_packs = !init_packs.empty();
    bool pattern_has_packs = !packs.empty();
    if (init_has_packs && !pattern_has_packs) {
        return std::nullopt;
    }

    std::vector<NodeId> retained_children;
    if (collect_session_.collecting_pattern() &&
        retain_constraint_normal_form_syntax_) {
        retained_children.push_back(retain_replayed_fold_operand_syntax(
            init_cursor,
            init_last_consumed_raw_end,
            init_end_cursor,
            ellipsis_loc));
        retained_children.push_back(retain_replayed_fold_operand_syntax(
            replay_cursor,
            replay_last_consumed_raw_end,
            replay_end_cursor,
            ellipsis_loc));
    }
    cursor_ = after_fold_cursor;
    last_consumed_raw_end_ = after_fold_last_consumed_raw_end;
    NodeId syntax = make_node(NodeKind::AmbiguousSyntax,
                              begin,
                              last_consumed_raw_end(),
                              retained_children,
                              text_payload("binary-left-fold"));

    auto make_error_fold = [&]() {
        collect::ExprResult error;
        error.has_error = true;
        error.type = collect_session_.file().unknown_type();
        return error;
    };

    if (sem_op != sem_op2) {
        diagnose(DiagnosticLevel::Error,
                 "binary fold operators must match",
                 op2.loc);
    }
    if (init_has_packs && pattern_has_packs) {
        diagnose(DiagnosticLevel::Error,
                 "binary fold expression contains unexpanded packs on both sides",
                 ellipsis_loc);
        return ParsedExpr{syntax, make_error_fold()};
    }
    if (!pattern_has_packs) {
        diagnose(DiagnosticLevel::Error,
                 "fold expression pattern does not contain an unexpanded pack",
                 ellipsis_loc);
        return ParsedExpr{syntax, make_error_fold()};
    }

    auto retain_dependent_fold = [&](const auto& discovered_packs) {
        ParsedExpr retained_initializer =
            retain_replayed_fold_operand_semantics(
                init_cursor,
                init_last_consumed_raw_end,
                init_end_cursor,
                after_fold_cursor,
                after_fold_last_consumed_raw_end,
                ellipsis_loc);
        std::vector<collect::Session::ParameterPackIdentity> retained_packs;
        ParsedExpr retained_pattern =
            retain_replayed_fold_operand_semantics(
                replay_cursor,
                replay_last_consumed_raw_end,
                replay_end_cursor,
                after_fold_cursor,
                after_fold_last_consumed_raw_end,
                ellipsis_loc,
                &retained_packs);
        const auto& identities = retained_packs.empty()
            ? discovered_packs
            : retained_packs;
        std::vector<cir::TemplateValuePackReference> references;
        references.reserve(identities.size());
        for (const auto& pack : identities) {
            references.push_back(retained_pack_reference(pack));
        }
        return collect_session_.make_dependent_fold_expression(
            cir::TemplateValueFoldKind::BinaryLeft,
            sem_op,
            std::move(retained_pattern.sem),
            std::optional<collect::ExprResult>(
                std::move(retained_initializer.sem)),
            std::move(references),
            op.loc);
    };

    if (should_retain_dependent_fold_pattern(
            collect_session_, retain_constraint_normal_form_syntax_)) {
        return ParsedExpr{syntax, retain_dependent_fold(packs)};
    }

    PackExpansionPattern fold_pattern;
    fold_pattern.packs = std::move(packs);
    fold_pattern.replay_cursor = replay_cursor;
    fold_pattern.replay_last_consumed_raw_end = replay_last_consumed_raw_end;
    fold_pattern.replay_end_cursor = replay_end_cursor;
    fold_pattern.after_ellipsis_cursor = after_fold_cursor;
    fold_pattern.after_ellipsis_last_consumed_raw_end =
        after_fold_last_consumed_raw_end;
    fold_pattern.ellipsis_loc = ellipsis_loc;
    bool dependent = false;
    std::optional<size_t> element_count =
        resolve_pack_expansion_element_count(fold_pattern, &dependent);
    if (dependent) {
        return ParsedExpr{syntax,
                          retain_dependent_fold(fold_pattern.packs)};
    }

    cursor_ = init_cursor;
    last_consumed_raw_end_ = init_last_consumed_raw_end;
    ParsedExpr init = parse_cast_expression();
    if (cursor_ != init_end_cursor) {
        diagnose(DiagnosticLevel::Error,
                 "could not replay fold expression init",
                 ellipsis_loc);
        cursor_ = init_end_cursor;
    }

    std::vector<collect::ExprResult> arguments;
    size_t count = element_count.value_or(0);
    arguments.reserve(count);
    replay_pack_expansion_elements(
        fold_pattern,
        count,
        [&](size_t) { arguments.push_back(parse_cast_expression().sem); });

    collect::ExprResult folded = std::move(init.sem);
    for (collect::ExprResult& argument : arguments) {
        folded = collect_session_.collect_binary_expr(
            sem_op,
            std::move(folded),
            std::move(argument),
            op.loc);
    }
    return ParsedExpr{syntax, std::move(folded)};
}

std::optional<Parser::ParsedExpr>
Parser::parse_direct_binary_left_fold_expression() {
    if (!check(TokenType::LEFT_PAREN)) {
        return std::nullopt;
    }

    std::optional<size_t> ellipsis_offset;
    int paren_depth = 0;
    int bracket_depth = 0;
    for (size_t offset = 1; true; ++offset) {
        TokenType type = peek(offset).type;
        if (type == TokenType::Eof) {
            return std::nullopt;
        }
        if (paren_depth == 0 && bracket_depth == 0 &&
            type == TokenType::RIGHT_PAREN) {
            return std::nullopt;
        }
        if (paren_depth == 0 && bracket_depth == 0 &&
            type == TokenType::ELLIPSIS && offset >= 2 &&
            is_fold_operator(
                binary_operator_for(peek(offset - 1).type)) &&
            is_fold_operator(
                binary_operator_for(peek(offset + 1).type)) &&
            is_identifier_token(peek(offset + 2).type) &&
            peek(offset + 3).type == TokenType::RIGHT_PAREN) {
            ellipsis_offset = offset;
            break;
        }
        switch (type) {
            case TokenType::LEFT_PAREN:
                ++paren_depth;
                break;
            case TokenType::RIGHT_PAREN:
                if (paren_depth > 0) {
                    --paren_depth;
                }
                break;
            case TokenType::LEFT_BRACKET:
                ++bracket_depth;
                break;
            case TokenType::RIGHT_BRACKET:
                if (bracket_depth > 0) {
                    --bracket_depth;
                }
                break;
            default:
                break;
        }
    }
    if (!ellipsis_offset.has_value() || *ellipsis_offset < 3 ||
        !is_identifier_token(peek(*ellipsis_offset + 2).type) ||
        peek(*ellipsis_offset + 3).type != TokenType::RIGHT_PAREN) {
        return std::nullopt;
    }
    BinaryOperator sem_op =
        binary_operator_for(peek(*ellipsis_offset - 1).type);
    BinaryOperator sem_op2 =
        binary_operator_for(peek(*ellipsis_offset + 1).type);
    if (!is_fold_operator(sem_op) ||
        !is_fold_operator(sem_op2)) {
        return std::nullopt;
    }

    size_t begin = current_raw_index();
    consume();
    ParsedExpr init = parse_cast_expression();
    Token op = current();
    if (binary_operator_for(op.type) != sem_op) {
        return std::nullopt;
    }
    consume();
    if (!match(TokenType::ELLIPSIS)) {
        return std::nullopt;
    }
    Token op2 = current();
    consume();
    if (sem_op != sem_op2) {
        diagnose(DiagnosticLevel::Error,
                 "binary fold operators must match",
                 op2.loc);
    }
    Token name_token = current();
    NodeId name = parse_name_node(NodeKind::Identifier);
    if (!match(TokenType::RIGHT_PAREN)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ')' after fold expression",
                 current_loc());
    }

    NodeId syntax = make_node(NodeKind::AmbiguousSyntax,
                              begin,
                              last_consumed_raw_end(),
                              {init.syntax, name},
                              text_payload("binary-left-fold"));

    auto make_dependent_fold = [&]() {
        collect_session_.bump_pattern_taint();
        collect::ExprResult dependent;
        dependent.type =
            collect_session_.file().dependent_type("fold expression");
        dependent.category = collect::ValueCategory::Dependent;
        return dependent;
    };

    if (!collect_session_.function_parameter_pack_name(name_token.value)) {
        diagnose(DiagnosticLevel::Error,
                 "fold expression pattern does not contain an unexpanded pack",
                 name_token.loc);
        collect::ExprResult error;
        error.has_error = true;
        error.type = collect_session_.file().unknown_type();
        return ParsedExpr{syntax, std::move(error)};
    }

    if (should_retain_dependent_fold_pattern(
            collect_session_, retain_constraint_normal_form_syntax_)) {
        return ParsedExpr{syntax, make_dependent_fold()};
    }

    std::optional<std::vector<collect::ExprResult>> arguments =
        collect_session_.function_parameter_pack_arguments(name_token.value,
                                                          name_token.loc);
    if (!arguments.has_value()) {
        return ParsedExpr{syntax, make_dependent_fold()};
    }
    collect::ExprResult folded = std::move(init.sem);
    for (collect::ExprResult& argument : *arguments) {
        folded = collect_session_.collect_binary_expr(
            sem_op,
            std::move(folded),
            std::move(argument),
            op.loc);
    }
    return ParsedExpr{syntax, std::move(folded)};
}

std::optional<Parser::ParsedExpr>
Parser::parse_invalid_fold_expression() {
    if (!check(TokenType::LEFT_PAREN)) {
        return std::nullopt;
    }

    std::optional<size_t> ellipsis_offset;
    std::optional<size_t> right_paren_offset;
    int paren_depth = 0;
    int bracket_depth = 0;
    int brace_depth = 0;
    for (size_t offset = 1; true; ++offset) {
        TokenType type = peek(offset).type;
        if (type == TokenType::Eof) {
            return std::nullopt;
        }
        if (paren_depth == 0 && bracket_depth == 0 && brace_depth == 0 &&
            type == TokenType::RIGHT_PAREN) {
            right_paren_offset = offset;
            break;
        }
        if (paren_depth == 0 && bracket_depth == 0 && brace_depth == 0 &&
            type == TokenType::ELLIPSIS) {
            ellipsis_offset = offset;
        }
        switch (type) {
            case TokenType::LEFT_PAREN:
                ++paren_depth;
                break;
            case TokenType::RIGHT_PAREN:
                if (paren_depth > 0) {
                    --paren_depth;
                }
                break;
            case TokenType::LEFT_BRACKET:
                ++bracket_depth;
                break;
            case TokenType::RIGHT_BRACKET:
                if (bracket_depth > 0) {
                    --bracket_depth;
                }
                break;
            case TokenType::LEFT_BRACE:
                ++brace_depth;
                break;
            case TokenType::RIGHT_BRACE:
                if (brace_depth > 0) {
                    --brace_depth;
                }
                break;
            default:
                break;
        }
    }
    if (!ellipsis_offset.has_value() || !right_paren_offset.has_value()) {
        return std::nullopt;
    }

    auto token_is_fold_operator = [&](size_t offset) {
        return is_fold_operator(binary_operator_for(peek(offset).type));
    };
    auto token_is_operator_like = [&](size_t offset) {
        if (token_is_fold_operator(offset)) {
            return true;
        }
        switch (peek(offset).type) {
            case TokenType::THREE_WAY_COMPARE:
            case TokenType::DOT:
            case TokenType::ARROW:
                return true;
            default:
                return false;
        }
    };

    std::optional<size_t> bad_operator_offset;
    if (*ellipsis_offset == 1) {
        size_t operator_offset = *ellipsis_offset + 1;
        if (operator_offset >= *right_paren_offset) {
            return std::nullopt;
        }
        if (!token_is_operator_like(operator_offset)) {
            return std::nullopt;
        }
        if (!token_is_fold_operator(operator_offset)) {
            bad_operator_offset = operator_offset;
        }
    } else if (*ellipsis_offset + 1 == *right_paren_offset) {
        if (*ellipsis_offset < 2) {
            return std::nullopt;
        }
        size_t operator_offset = *ellipsis_offset - 1;
        if (!token_is_operator_like(operator_offset)) {
            return std::nullopt;
        }
        if (!token_is_fold_operator(operator_offset)) {
            bad_operator_offset = operator_offset;
        }
    } else {
        if (*ellipsis_offset < 2 ||
            *ellipsis_offset + 1 >= *right_paren_offset) {
            return std::nullopt;
        }
        size_t left_operator_offset = *ellipsis_offset - 1;
        size_t right_operator_offset = *ellipsis_offset + 1;
        if (!token_is_operator_like(left_operator_offset) ||
            !token_is_operator_like(right_operator_offset)) {
            return std::nullopt;
        }
        if (!token_is_fold_operator(left_operator_offset)) {
            bad_operator_offset = left_operator_offset;
        } else if (!token_is_fold_operator(right_operator_offset)) {
            bad_operator_offset = right_operator_offset;
        }
    }
    if (!bad_operator_offset.has_value()) {
        return std::nullopt;
    }

    size_t begin = current_raw_index();
    diagnose(DiagnosticLevel::Error,
             "unsupported fold operator",
             peek(*bad_operator_offset).loc);
    for (size_t consumed = 0;
         consumed <= *right_paren_offset && !at_end();
         ++consumed) {
        consume();
    }
    collect::ExprResult sem;
    sem.has_error = true;
    sem.type = collect_session_.file().unknown_type();
    NodeId syntax = make_node(NodeKind::Error,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              text_payload("fold expression"),
                              NodeFlagHasError);
    return ParsedExpr{syntax, std::move(sem)};
}

Parser::ParsedExpr Parser::parse_primary_expression() {
    size_t begin = current_raw_index();
    auto consume_literal_suffix = [&]() {
        std::string suffix;
        if (check(TokenType::LITERAL_SUFFIX)) {
            suffix = std::string(current().value);
            consume();
        }
        return suffix;
    };
    if (check(TokenType::BITWISE_XOR) &&
        (peek(1).type == TokenType::LEFT_BRACE ||
         peek(1).type == TokenType::LEFT_PAREN)) {
        return parse_block_literal_expression();
    }
    if (lang_opts_.is_objc()) {
        if (check(TokenType::AT)) {
            return parse_objc_at_expression();
        }

        if (check(TokenType::LEFT_BRACKET) && !lang_opts_.is_cxx_mode()) {
            return parse_objc_message_expression();
        }
    }

    if (check(TokenType::TEMPLATE) &&
        peek(1).type == TokenType::SPLICE_OPEN) {
        Token template_token = current();
        consume();
        Token open = current();
        consume();
        ParsedExpr operand = parse_expression(PrecLevel::ASSIGNMENT);
        cir::Fragment operand_fragment = operand.sem.fragment;
        if (!match(TokenType::SPLICE_CLOSE)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ':]' after splice operand",
                     current_loc());
        }
        collect::Session::SpliceTemplateResolution resolution =
            collect_session_.resolve_splice_template_operand(
                std::move(operand.sem), open.loc);
        std::vector<collect::Session::TemplateArgument> arguments;
        bool has_arguments = check(TokenType::LESS_THAN);
        const collect::Session::TemplateInfo* info =
            resolution.template_entity.valid()
                ? collect_session_.template_info(
                      resolution.template_entity)
                : nullptr;
        bool parsed_arguments = true;
        if (has_arguments) {
            if (resolution.dependent || !info) {
                parsed_arguments =
                    parse_dependent_expression_template_argument_list(
                        open.loc);
            } else {
                std::vector<const collect::Session::TemplateInfo*>
                    function_candidates;
                if (!info->is_class_template && !info->is_alias_template &&
                    !info->is_variable_template && !info->is_concept) {
                    function_candidates =
                        collect_session_.function_template_infos_for_name(
                            info->lexical_context,
                            info->name,
                            /*include_parents=*/false);
                }
                parsed_arguments = function_candidates.size() > 1
                    ? parse_candidate_neutral_template_argument_list(
                          *info, arguments, open.loc)
                    : parse_template_argument_list(
                          *info, arguments, open.loc);
            }
        }
        collect::ExprResult sem;
        if (resolution.dependent) {
            sem.fragment = std::move(operand_fragment);
            sem.type = collect_session_.file().dependent_type(
                "dependent template splice");
            sem.category = collect::ValueCategory::Dependent;
            sem.has_error = !parsed_arguments;
            sem = collect_session_.make_dependent_expr(
                std::move(sem), template_token.loc);
        } else if (resolution.has_error || !info || !parsed_arguments) {
            sem.has_error = true;
        } else if (check(TokenType::SCOPE_RESOLUTION)) {
            if (!has_arguments ||
                (!info->is_class_template && !info->is_alias_template)) {
                diagnose(DiagnosticLevel::Error,
                         "spliced template scope must designate a class or alias template specialization",
                         open.loc);
                sem.has_error = true;
            } else {
                cir::EntityId instantiated = instantiate_template_with_args(
                    *info, std::move(arguments), open.loc);
                cir::DeclContextId context =
                    instantiated.valid() &&
                            collect_session_.file().valid(instantiated)
                        ? collect_session_.file()
                              .entity(instantiated)
                              .semantic_context
                        : cir::DeclContextId{};
                while (context.valid() &&
                       check(TokenType::SCOPE_RESOLUTION)) {
                    consume();
                    bool has_template = match(TokenType::TEMPLATE);
                    if (!is_identifier_token(current().type)) {
                        diagnose(DiagnosticLevel::Error,
                                 "expected name after spliced template scope",
                                 current_loc());
                        sem.has_error = true;
                        break;
                    }
                    Token component = current();
                    consume();
                    if (check(TokenType::LESS_THAN)) {
                        const collect::Session::TemplateInfo* component_info =
                            collect_session_.template_info_in_context(
                                context,
                                component.value,
                                /*include_parents=*/false);
                        if (!component_info ||
                            (!component_info->is_class_template &&
                             !component_info->is_alias_template)) {
                            diagnose(DiagnosticLevel::Error,
                                     "spliced scope component is not a type template",
                                     component.loc);
                            sem.has_error = true;
                            break;
                        }
                        std::vector<collect::Session::TemplateArgument>
                            component_arguments;
                        if (!parse_and_canonicalize_template_argument_list(
                                *component_info,
                                component_arguments,
                                component.loc)) {
                            sem.has_error = true;
                            break;
                        }
                        cir::EntityId component_entity =
                            instantiate_template_with_args(
                                *component_info,
                                std::move(component_arguments),
                                component.loc,
                                0,
                                false,
                                true);
                        context = component_entity.valid() &&
                                  collect_session_.file().valid(
                                      component_entity)
                            ? collect_session_.file()
                                  .entity(component_entity)
                                  .semantic_context
                            : cir::DeclContextId{};
                        continue;
                    }
                    if (has_template) {
                        diagnose(DiagnosticLevel::Error,
                                 "template disambiguator requires a template argument list",
                                 component.loc);
                        sem.has_error = true;
                        break;
                    }
                    if (check(TokenType::SCOPE_RESOLUTION)) {
                        collect::Session::QualifierResolution next =
                            collect_session_.resolve_qualifier_component(
                                context, component.value, component.loc);
                        if (next.has_error || !next.context.valid()) {
                            sem.has_error = true;
                            break;
                        }
                        context = next.context;
                    } else {
                        sem = collect_session_.lookup_qualified_name(
                            context, component.value, component.loc);
                    }
                }
                if (!context.valid() && !sem.has_error) {
                    sem.has_error = true;
                }
            }
        } else if (!info->is_class_template && !info->is_alias_template &&
                   !info->is_concept) {
            if (!has_arguments && info->is_variable_template) {
                diagnose(DiagnosticLevel::Error,
                         "a variable-template splice requires a template argument list",
                         open.loc);
                sem.has_error = true;
            } else {
                sem = instantiate_template_id_expression_result(
                    *info,
                    std::move(arguments),
                    open.loc,
                    /*qualified_name=*/false);
            }
        } else {
            diagnose(DiagnosticLevel::Error,
                     "template splice is not valid in an expression",
                     open.loc);
            sem.has_error = true;
        }
        return {make_node(NodeKind::SpliceExpr,
                          begin,
                          last_consumed_raw_end(),
                          {operand.syntax},
                          text_payload("template [:") ,
                          sem.has_error ? NodeFlagHasError : NodeFlagNone),
                std::move(sem)};
    }

    if (check(TokenType::SPLICE_OPEN)) {
        size_t begin = current_raw_index();
        Token open = current();
        consume();
        ParsedExpr operand = parse_expression(PrecLevel::ASSIGNMENT);
        if (!match(TokenType::SPLICE_CLOSE)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ':]' after splice operand",
                     current_loc());
        }
        collect::ExprResult sem;
        if (check(TokenType::SCOPE_RESOLUTION) &&
            peek(1).type == TokenType::TEMPLATE) {
            cir::Fragment operand_fragment = operand.sem.fragment;
            bool dependent_scope = false;
            collect::Session::QualifierResolution scope =
                collect_session_.resolve_splice_scope_operand(
                    std::move(operand.sem), open.loc, &dependent_scope);
            bool parsed_suffix = true;
            if (dependent_scope) {
                while (check(TokenType::SCOPE_RESOLUTION)) {
                    consume();
                    (void)match(TokenType::TEMPLATE);
                    if (!is_identifier_token(current().type)) {
                        diagnose(DiagnosticLevel::Error,
                                 "expected name after spliced scope",
                                 current_loc());
                        parsed_suffix = false;
                        break;
                    }
                    Token component = current();
                    consume();
                    if (check(TokenType::LESS_THAN) &&
                        !parse_dependent_expression_template_argument_list(
                            component.loc)) {
                        parsed_suffix = false;
                        break;
                    }
                }
                collect::ExprResult dependent;
                dependent.fragment = std::move(operand_fragment);
                dependent.type = collect_session_.file().dependent_type(
                    "dependent spliced qualified name");
                dependent.category = collect::ValueCategory::Dependent;
                dependent.has_error = !parsed_suffix;
                sem = collect_session_.make_dependent_expr(
                    std::move(dependent), open.loc);
            } else if (!scope.has_error) {
                cir::DeclContextId context = scope.context;
                while (check(TokenType::SCOPE_RESOLUTION)) {
                    consume();
                    bool has_template = match(TokenType::TEMPLATE);
                    if (!is_identifier_token(current().type)) {
                        diagnose(DiagnosticLevel::Error,
                                 "expected name after spliced scope",
                                 current_loc());
                        sem.has_error = true;
                        break;
                    }
                    Token component = current();
                    consume();
                    if (check(TokenType::LESS_THAN)) {
                        const collect::Session::TemplateInfo* info =
                            collect_session_.template_info_in_context(
                                context,
                                component.value,
                                /*include_parents=*/false);
                        if (!info ||
                            (!info->is_class_template &&
                             !info->is_alias_template)) {
                            diagnose(DiagnosticLevel::Error,
                                     has_template
                                         ? "template disambiguator names a non-template"
                                         : "spliced scope component is not a template",
                                     component.loc);
                            sem.has_error = true;
                            break;
                        }
                        std::vector<collect::Session::TemplateArgument>
                            arguments;
                        uint64_t point_lookup_generation = 0;
                        if (!parse_and_canonicalize_template_argument_list(
                                *info,
                                arguments,
                                component.loc,
                                &point_lookup_generation)) {
                            sem.has_error = true;
                            break;
                        }
                        cir::EntityId instantiated =
                            instantiate_template_with_args(
                                *info,
                                std::move(arguments),
                                component.loc,
                                point_lookup_generation,
                                /*replay_guard_entered=*/false,
                                /*arguments_are_canonical=*/true);
                        if (!instantiated.valid() ||
                            !collect_session_.file().valid(instantiated)) {
                            sem.has_error = true;
                            break;
                        }
                        context = collect_session_.file()
                                      .entity(instantiated)
                                      .semantic_context;
                        if (!context.valid()) {
                            sem.has_error = true;
                            break;
                        }
                        continue;
                    }
                    if (has_template) {
                        diagnose(DiagnosticLevel::Error,
                                 "template disambiguator requires a template argument list",
                                 component.loc);
                        sem.has_error = true;
                        break;
                    }
                    if (check(TokenType::SCOPE_RESOLUTION)) {
                        collect::Session::QualifierResolution next =
                            collect_session_.resolve_qualifier_component(
                                context, component.value, component.loc);
                        if (next.has_error || !next.context.valid()) {
                            sem.has_error = true;
                            break;
                        }
                        context = next.context;
                        continue;
                    }
                    sem = collect_session_.lookup_qualified_name(
                        context, component.value, component.loc);
                    break;
                }
            } else {
                sem.has_error = true;
            }
        } else if (check(TokenType::SCOPE_RESOLUTION) &&
            is_identifier_token(peek(1).type)) {

            std::vector<std::string> path;
            do {
                consume();
                path.push_back(std::string(current().value));
                consume();
            } while (check(TokenType::SCOPE_RESOLUTION) &&
                     is_identifier_token(peek(1).type));
            sem = collect_session_.collect_splice_qualified_expr(
                std::move(operand.sem), path, open.loc);
        } else {
            sem = collect_session_.collect_splice_expr(std::move(operand.sem),
                                                       open.loc);
        }
        return {make_node(NodeKind::SpliceExpr,
                          begin,
                          last_consumed_raw_end(),
                          {operand.syntax},
                          text_payload("[:"),
                          sem.has_error ? NodeFlagHasError : NodeFlagNone),
                std::move(sem)};
    }

    if (lang_opts_.is_cxx_mode() && check(TokenType::LEFT_BRACKET) &&
        peek(1).type != TokenType::LEFT_BRACKET) {
        return parse_lambda_expression();
    }
    if (auto builtin = parse_builtin_primary_expression()) {
        return *std::move(builtin);
    }
    if (check(TokenType::GENERIC)) {
        return parse_generic_selection_expression();
    }
    if (lang_opts_.is_cxx_mode() && check(TokenType::REQUIRES_KW)) {
        return parse_requires_expression();
    }
    if (lang_opts_.is_cxx_mode() &&
        decltype_specifier_precedes_scope()) {
        return parse_cxx_qualified_id_expression();
    }
    if (lang_opts_.is_cxx_mode() &&
        check(TokenType::SCOPE_RESOLUTION)) {

        return parse_cxx_qualified_id_expression();
    }

    if (lang_opts_.is_cxx_mode() && is_type_start(current().type) &&
        !is_identifier_token(current().type)) {
        TokenType first_type_token = current().type;
        auto is_single_token_fundamental_specifier = [](TokenType token) {
            switch (token) {
                case TokenType::VOID:
                case TokenType::CHAR:
                case TokenType::SHORT:
                case TokenType::INT:
                case TokenType::LONG:
                case TokenType::FLOAT:
                case TokenType::DOUBLE:
                case TokenType::SIGNED:
                case TokenType::UNSIGNED:
                case TokenType::BOOL:
                case TokenType::WCHAR_T:
                case TokenType::CHAR8_T:
                case TokenType::CHAR16_T:
                case TokenType::CHAR32_T:
                case TokenType::INT128:
                case TokenType::FLOAT16:
                    return true;
                default:
                    return false;
            }
        };
        DeclarationParser type_parser(*this);
        cir::TypeRef type = type_parser.parse_declaration(false, true);
        if (is_single_token_fundamental_specifier(first_type_token) &&
            current_raw_index() != begin + 1) {
            diagnose(DiagnosticLevel::Error,
                     "functional cast type must be a single simple-type-specifier",
                     loc_for_index(begin));
            collect::ExprResult sem;
            sem.has_error = true;
            return {make_node(NodeKind::Error,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              {},
                              NodeFlagHasError),
                    std::move(sem)};
        }
        if (type.type.valid() &&
            (check(TokenType::LEFT_PAREN) ||
             check(TokenType::LEFT_BRACE))) {
            collect::ExprResult sem;
            sem.type = type.type;
            sem.category = collect::ValueCategory::Type;
            NodeId syntax = type_parser.type_syntax != InvalidNodeId
                ? type_parser.type_syntax
                : make_node(NodeKind::TypeName,
                            begin,
                            last_consumed_raw_end(),
                            {},
                            text_payload(
                                collect_session_.file().format_type(type)));
            return {syntax, std::move(sem)};
        }
        diagnose(DiagnosticLevel::Error,
                 "expected '(' or '{' after type name in expression",
                 current_loc());
        collect::ExprResult sem;
        sem.has_error = true;
        return {make_node(NodeKind::Error,
                          begin,
                          last_consumed_raw_end(),
                          {},
                          {},
                          NodeFlagHasError),
                std::move(sem)};
    }
    if (is_integer_token(current().type)) {
        Token token = current();
        SrcLoc loc = token.loc;
        consume();
        std::string suffix = consume_literal_suffix();
        std::string spelling = aburi::token_spelling_for_output(token);
        int64_t value = 0;
        if (auto parsed = parse_integer_literal_info(spelling)) {
            value = static_cast<int64_t>(parsed->value);
        } else {
            diagnose(DiagnosticLevel::Error, "invalid integer literal", loc);
        }
        IntegerLiteralPayload payload{value, spelling, suffix};
        NodeId syntax = make_node(NodeKind::IntegerLiteral, begin, last_consumed_raw_end(), {}, std::move(payload));
        collect::ExprResult sem =
            collect_session_.make_integer_literal(value, spelling, token.type, loc);
        if (!suffix.empty()) {
            sem = collect_session_.collect_user_defined_literal(
                std::move(sem),
                collect::UserDefinedLiteralKind::Integer,
                std::move(suffix),
                std::move(spelling),
                loc);
        }
        return {syntax, std::move(sem)};
    }
    if (is_imaginary_token(current().type)) {
        Token token = current();
        SrcLoc loc = token.loc;
        consume();
        std::string spelling = aburi::token_spelling_for_output(token);
        FloatingLiteralKind literal_kind =
            token.type == TokenType::IMAG_FLOAT_CONST ? FloatingLiteralKind::Float
            : token.type == TokenType::IMAG_LONG_DOUBLE_CONST
                ? FloatingLiteralKind::LongDouble
                : FloatingLiteralKind::Double;
        FloatingLiteralPayload payload{literal_kind, spelling};
        NodeId syntax = make_node(NodeKind::FloatingLiteral, begin, last_consumed_raw_end(), {}, std::move(payload));
        collect::ExprResult sem =
            collect_session_.make_imaginary_literal(literal_kind, std::move(spelling), loc);
        return {syntax, std::move(sem)};
    }
    if (is_floating_token(current().type)) {
        Token token = current();
        SrcLoc loc = token.loc;
        consume();
        std::string suffix = consume_literal_suffix();
        std::string spelling = aburi::token_spelling_for_output(token);
        FloatingLiteralKind literal_kind = floating_literal_kind_for(token.type);
        FloatingLiteralPayload payload{literal_kind, spelling, suffix};
        NodeId syntax = make_node(NodeKind::FloatingLiteral, begin, last_consumed_raw_end(), {}, std::move(payload));
        collect::ExprResult sem =
            collect_session_.make_floating_literal(literal_kind, spelling, loc);
        if (!suffix.empty()) {
            sem = collect_session_.collect_user_defined_literal(
                std::move(sem),
                collect::UserDefinedLiteralKind::Floating,
                std::move(suffix),
                std::move(spelling),
                loc);
        }
        return {syntax, std::move(sem)};
    }
    if (check(TokenType::TRUE_KW) || check(TokenType::FALSE_KW)) {
        SrcLoc loc = current().loc;
        bool value = check(TokenType::TRUE_KW);
        std::string spelling = current().value.empty()
            ? std::string(value ? "true" : "false")
            : std::string(current().value);
        consume();
        BooleanLiteralPayload payload{value, spelling};
        NodeId syntax = make_node(NodeKind::BooleanLiteral, begin, last_consumed_raw_end(), {}, std::move(payload));
        collect::ExprResult sem =
            collect_session_.make_boolean_literal(value, std::move(spelling), loc);
        return {syntax, std::move(sem)};
    }
    if (check(TokenType::NULLPTR_KW)) {
        Token token = current();
        consume();
        NodeId syntax = make_node(NodeKind::Identifier,
                                  begin,
                                  last_consumed_raw_end(),
                                  {},
                                  text_payload("nullptr"));
        collect::ExprResult sem = collect_session_.make_nullptr_literal(token.loc);
        return {syntax, std::move(sem)};
    }
    if (check(TokenType::THIS_KW)) {
        Token token = current();
        consume();
        NodeId syntax = make_node(NodeKind::Identifier,
                                  begin,
                                  last_consumed_raw_end(),
                                  {},
                                  text_payload("this"));
        collect::ExprResult sem = collect_session_.collect_this_expr(token.loc);
        return {syntax, std::move(sem)};
    }
    if (check(TokenType::CHAR_LITERAL)) {
        Token token = current();
        SrcLoc loc = token.loc;
        consume();
        std::string suffix = consume_literal_suffix();
        std::string spelling = aburi::token_spelling_for_output(token);
        std::string decoded = std::string(token.value);
        int64_t value = character_literal_value(decoded);
        CharacterLiteralPayload payload{
            value, token.literal_prefix, decoded, spelling, suffix
        };
        NodeId syntax = make_node(NodeKind::CharacterLiteral, begin, last_consumed_raw_end(), {}, std::move(payload));
        collect::ExprResult sem =
            collect_session_.make_character_literal(std::move(decoded), token.literal_prefix,
                spelling, loc);
        if (!suffix.empty()) {
            sem = collect_session_.collect_user_defined_literal(
                std::move(sem),
                collect::UserDefinedLiteralKind::Character,
                std::move(suffix),
                std::move(spelling),
                loc);
        }
        return {syntax, std::move(sem)};
    }
    if (check(TokenType::STRING_LITERAL)) {
        Token token = current();
        SrcLoc loc = token.loc;
        consume();
        std::string suffix = consume_literal_suffix();
        std::string spelling = aburi::token_spelling_for_output(token);
        std::string decoded = std::string(token.value);
        StringLiteralPayload payload{
            token.literal_prefix, decoded, spelling, suffix
        };
        NodeId syntax = make_node(NodeKind::StringLiteral, begin, last_consumed_raw_end(), {}, std::move(payload));
        collect::ExprResult sem =
            collect_session_.make_string_literal(std::move(decoded), spelling, loc,
                                                 token.literal_prefix);
        if (!suffix.empty()) {
            sem = collect_session_.collect_user_defined_literal(
                std::move(sem),
                collect::UserDefinedLiteralKind::String,
                std::move(suffix),
                std::move(spelling),
                loc);
        }
        return {syntax, std::move(sem)};
    }
    if (lang_opts_.is_cxx_mode() &&
        is_identifier_token(current().type) &&
        peek(1).type == TokenType::ELLIPSIS &&
        peek(2).type == TokenType::LEFT_BRACKET) {
        Token pack_name = current();
        consume();
        consume();
        consume();
        ParsedExpr index = parse_conditional_expression();
        if (!match(TokenType::RIGHT_BRACKET)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ']' after pack index",
                     current_loc());
        }
        if (!lang_opts_.is_cxx26_or_later()) {
            diagnose(DiagnosticLevel::Error,
                     "pack indexing is a C++26 feature",
                     pack_name.loc);
        }
        collect::ExprResult sem = collect_session_.collect_pack_index_expr(
            pack_name.value, std::move(index.sem), pack_name.loc);
        if (!lang_opts_.is_cxx26_or_later()) {
            sem.has_error = true;
        }
        NodeId syntax = make_node(
            NodeKind::PackIndexExpr,
            begin,
            last_consumed_raw_end(),
            {index.syntax},
            text_payload(pack_name.value),
            sem.has_error ? NodeFlagHasError : NodeFlagNone);
        return {syntax, std::move(sem)};
    }
    if (lang_opts_.is_cxx_mode() &&
        collect_session_.in_pack_pattern_capture() &&
        is_identifier_token(current().type)) {

        (void)collect_session_.capture_any_parameter_pack_name(
            current().value);
    }
    if (lang_opts_.is_cxx_mode() &&
        (check(TokenType::SCOPE_RESOLUTION) ||
         (is_identifier_token(current().type) &&
          peek(1).type == TokenType::SCOPE_RESOLUTION &&
          peek(2).type != TokenType::MULTIPLY) ||
         (is_identifier_token(current().type) &&
          peek(1).type == TokenType::LESS_THAN &&
          template_id_precedes_scope(0)))) {
        return parse_cxx_qualified_id_expression();
    }
    if (lang_opts_.is_cxx_mode() && is_identifier_token(current().type) &&
        peek(1).type == TokenType::LESS_THAN) {
        if (const collect::Session::TemplateInfo* info =
                collect_session_.template_info_for_name(current().value)) {
            Token name_token = current();
            consume();
            return parse_unqualified_template_id_expression(
                *info,
                std::string(name_token.value),
                name_token.loc,
                begin);
        }

        if (template_id_precedes_call(0)) {
            Token name_token = current();
            consume();
            collect::Session::TemplateInfo unresolved_info;
            unresolved_info.name = std::string(name_token.value);
            std::vector<collect::Session::TemplateArgument> arguments;
            bool parsed = parse_candidate_neutral_template_argument_list(
                unresolved_info, arguments, name_token.loc);
            collect::ExprResult sem;
            sem.name = unresolved_info.name;
            sem.unresolved_unqualified_name = true;
            sem.category = collect::ValueCategory::FunctionDesignator;
            sem.has_explicit_template_arguments = true;
            sem.explicit_template_arguments = std::move(arguments);
            sem.unparenthesized_id_or_member = true;
            sem.unparenthesized_identifier = true;
            sem.possibly_parenthesized_identifier = true;
            sem.has_error = !parsed;
            NodeId syntax = make_node(
                NodeKind::Identifier,
                begin,
                last_consumed_raw_end(),
                {},
                text_payload(unresolved_info.name),
                sem.has_error ? NodeFlagHasError : NodeFlagNone);
            return {syntax, std::move(sem)};
        }
    }
    if (lang_opts_.is_cxx_mode() &&
        is_identifier_token(current().type) &&
        (peek(1).type == TokenType::LEFT_PAREN ||
         peek(1).type == TokenType::LEFT_BRACE)) {
        const collect::Session::TemplateInfo* info =
            collect_session_.template_info_for_name(current().value);
        bool is_primary_class = info && info->is_class_template &&
            !info->is_partial_specialization;
        bool is_deducible_alias = info && info->is_alias_template &&
            info->alias_deduction_projection.has_value();
        if (is_primary_class || is_deducible_alias) {
            Token name = current();
            consume();
            collect::ExprResult sem;
            cir::TypeRef visible_type =
                collect_session_.lookup_type_name_ref_checked(name.value,
                                                              name.loc);
            if (visible_type.valid()) {

                sem.type = visible_type.type;
            } else {
                sem.name = info->name;
                sem.entity = info->entity;
            }
            sem.category = collect::ValueCategory::Type;
            sem.unparenthesized_id_or_member = true;
            return {make_node(NodeKind::Identifier,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              text_payload(name.value)),
                    std::move(sem)};
        }
    }
    if (lang_opts_.is_cxx_mode() && check(TokenType::OPERATOR_KW)) {
        if (starts_conversion_function_id()) {
            ParsedConversionFunctionId conversion_id =
                *parse_conversion_function_id();
            collect::ExprResult object = collect_session_.collect_this_expr(
                conversion_id.loc);
            collect::ExprResult sem;
            if (!object.place.valid() &&
                !collect_session_.expr_is_dependent(object)) {
                diagnose(DiagnosticLevel::Error,
                         "an unqualified conversion-function-id requires a member function context",
                         conversion_id.loc);
                sem = std::move(object);
                sem.has_error = true;
            } else {
                sem = collect_session_
                    .collect_conversion_function_id_access_expr(
                        std::move(object),
                        conversion_id.target_type,
                        /*is_arrow=*/false,
                        conversion_id.loc);
            }
            sem.has_error = sem.has_error || conversion_id.has_error;
            sem.unparenthesized_id_or_member = true;
            NodeId syntax = make_node(
                NodeKind::Identifier,
                begin,
                last_consumed_raw_end(),
                conversion_id.type_syntax != InvalidNodeId
                    ? std::vector<NodeId>{conversion_id.type_syntax}
                    : std::vector<NodeId>{},
                text_payload(conversion_id.name),
                sem.has_error ? NodeFlagHasError : NodeFlagNone);
            return {syntax, std::move(sem)};
        }
        std::optional<ParsedOperatorFunctionId> operator_id =
            parse_operator_function_id();
        if (!operator_id) {
            collect::ExprResult sem;
            sem.has_error = true;
            return {make_node(NodeKind::Error,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              {},
                              NodeFlagHasError),
                    std::move(sem)};
        }
        if (!operator_id->has_error && check(TokenType::LESS_THAN)) {
            if (const collect::Session::TemplateInfo* info =
                    collect_session_.template_info_for_name(
                        operator_id->name)) {
                return parse_unqualified_template_id_expression(
                    *info,
                    operator_id->name,
                    operator_id->loc,
                    begin);
            }
        }
        collect::ExprResult sem = collect_session_.lookup_name(
            operator_id->name,
            operator_id->loc,
            check(TokenType::LEFT_PAREN));
        sem.has_error = sem.has_error || operator_id->has_error;
        sem.unparenthesized_id_or_member = true;
        sem.unparenthesized_identifier = true;
        sem.possibly_parenthesized_identifier = true;
        NodeId syntax = make_node(
            NodeKind::Identifier,
            begin,
            last_consumed_raw_end(),
            {},
            text_payload(operator_id->name),
            sem.has_error ? NodeFlagHasError : NodeFlagNone);
        return {syntax, std::move(sem)};
    }
    if (is_identifier_token(current().type)) {
        bool allow_unresolved_call_name = peek(1).type == TokenType::LEFT_PAREN;
        NodeId syntax = parse_name_node(NodeKind::Identifier);
        collect::ExprResult sem =
            collect_session_.lookup_name(node_text(tree_.node(syntax)),
                                         tree_.node(syntax).loc,
                                         allow_unresolved_call_name);
        if (sem.entity.valid()) {
            materialize_deferred_static_data_member_expr(sem);
        }
        sem.unparenthesized_id_or_member = true;
        sem.unparenthesized_identifier = true;
        sem.possibly_parenthesized_identifier = true;
        return {syntax, std::move(sem)};
    }
    if (check(TokenType::LEFT_BRACE)) {
        return parse_init_list_expression();
    }
    if (auto fold = parse_replayed_unary_left_fold_expression()) {
        return *std::move(fold);
    }
    if (auto fold = parse_direct_unary_left_fold_expression()) {
        return *std::move(fold);
    }
    if (auto fold = parse_replayed_binary_right_fold_expression()) {
        return *std::move(fold);
    }
    if (auto fold = parse_direct_binary_right_fold_expression()) {
        return *std::move(fold);
    }
    if (auto fold = parse_replayed_unary_right_fold_expression()) {
        return *std::move(fold);
    }
    if (auto fold = parse_direct_unary_right_fold_expression()) {
        return *std::move(fold);
    }
    if (auto fold = parse_replayed_binary_left_fold_expression()) {
        return *std::move(fold);
    }
    if (auto fold = parse_direct_binary_left_fold_expression()) {
        return *std::move(fold);
    }
    if (auto fold = parse_invalid_fold_expression()) {
        return *std::move(fold);
    }
    if (match(TokenType::LEFT_PAREN)) {
        size_t paren_begin = begin;
        ParsedExpr inner = parse_expression();
        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error, "expected ')'", current_loc());
        }
        NodeId syntax = make_node(NodeKind::ParenExpr,
                                  paren_begin,
                                  last_consumed_raw_end(),
                                  {inner.syntax},
                                  text_payload("paren"));
        inner.sem.unparenthesized_id_or_member = false;
        inner.sem.unparenthesized_identifier = false;
        return {syntax, std::move(inner.sem)};
    }

    diagnose(DiagnosticLevel::Error, "expected expression", current_loc());
    consume();
    collect::ExprResult sem;
    sem.has_error = true;
    return {make_node(NodeKind::Error, begin, last_consumed_raw_end(), {}, {}, NodeFlagHasError), std::move(sem)};
}

Parser::ParsedExpr Parser::parse_generic_selection_expression() {

    size_t begin = current_raw_index();
    SrcLoc loc = current().loc;
    consume();
    if (!match(TokenType::LEFT_PAREN)) {
        diagnose(DiagnosticLevel::Error, "expected '(' after '_Generic'", current_loc());
    }
    ParsedExpr controlling = parse_assignment_expression();
    std::vector<NodeId> children{controlling.syntax};
    if (!match(TokenType::COMMA)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ',' after _Generic controlling expression",
                 current_loc());
    }
    std::vector<collect::GenericAssociation> associations;
    do {
        collect::GenericAssociation assoc;
        assoc.loc = current_loc();
        if (check(TokenType::DEFAULT)) {
            consume();
            assoc.is_default = true;
        } else {
            children.push_back(parse_type_name(nullptr, nullptr, nullptr, &assoc.type));
        }
        if (!match(TokenType::COLON)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ':' in generic association",
                     current_loc());
        }
        ParsedExpr assoc_expr = parse_assignment_expression();
        children.push_back(assoc_expr.syntax);
        assoc.expr = std::move(assoc_expr.sem);
        associations.push_back(std::move(assoc));
    } while (match(TokenType::COMMA));
    if (!match(TokenType::RIGHT_PAREN)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ')' after generic associations",
                 current_loc());
    }
    collect::ExprResult sem =
        collect_session_.collect_generic_selection(std::move(controlling.sem),
                                                   std::move(associations),
                                                   loc);
    NodeId syntax = make_node(NodeKind::GenericSelectionExpr,
                              begin,
                              last_consumed_raw_end(),
                              children,
                              text_payload("_Generic"));
    return {syntax, std::move(sem)};
}

cir::TypeRef Parser::parse_splice_type_specifier() {
    Token open = current();
    consume();
    ParsedExpr operand = parse_expression(PrecLevel::ASSIGNMENT);
    cir::TemplateValueExpression splice_operand =
        operand.sem.template_value_expr;
    if (!match(TokenType::SPLICE_CLOSE)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ':]' after splice operand",
                 current_loc());
    }
    auto parse_dependent_scope_tail =
        [&](cir::TypeRef qualifier) -> cir::TypeRef {
        while (match(TokenType::SCOPE_RESOLUTION)) {
            bool has_template = match(TokenType::TEMPLATE);
            if (!is_identifier_token(current().type)) {
                diagnose(DiagnosticLevel::Error,
                         "expected type name after spliced scope",
                         current_loc());
                return collect_session_.type_ref(
                    collect_session_.file().unknown_type());
            }
            Token component = current();
            consume();
            std::vector<collect::Session::TemplateArgument> arguments;
            if (check(TokenType::LESS_THAN)) {
                collect::Session::TemplateInfo neutral;
                if (!parse_candidate_neutral_template_argument_list(
                        neutral, arguments, component.loc)) {
                    return collect_session_.type_ref(
                        collect_session_.file().unknown_type());
                }
            } else if (has_template) {
                diagnose(DiagnosticLevel::Error,
                         "template disambiguator requires a template argument list",
                         component.loc);
                return collect_session_.type_ref(
                    collect_session_.file().unknown_type());
            }
            qualifier = collect_session_.type_ref(
                collect_session_.file().dependent_name_type(
                    qualifier,
                    component.value,
                    std::move(arguments),
                    false));
        }
        return qualifier;
    };
    auto parse_concrete_scope_tail =
        [&](cir::DeclContextId context) -> cir::TypeRef {
        while (match(TokenType::SCOPE_RESOLUTION)) {
            bool has_template = match(TokenType::TEMPLATE);
            if (!is_identifier_token(current().type)) {
                diagnose(DiagnosticLevel::Error,
                         "expected type name after spliced scope",
                         current_loc());
                return collect_session_.type_ref(
                    collect_session_.file().unknown_type());
            }
            Token component = current();
            consume();
            if (check(TokenType::LESS_THAN)) {
                const collect::Session::TemplateInfo* component_info =
                    collect_session_.template_info_in_context(
                        context,
                        component.value,
                        /*include_parents=*/false);
                if (!component_info ||
                    (!component_info->is_class_template &&
                     !component_info->is_alias_template)) {
                    diagnose(DiagnosticLevel::Error,
                             has_template
                                 ? "template disambiguator names a non-template"
                                 : "spliced scope component is not a template",
                             component.loc);
                    return collect_session_.type_ref(
                        collect_session_.file().unknown_type());
                }
                std::vector<collect::Session::TemplateArgument> arguments;
                if (!parse_and_canonicalize_template_argument_list(
                        *component_info, arguments, component.loc)) {
                    return collect_session_.type_ref(
                        collect_session_.file().unknown_type());
                }
                cir::EntityId instantiated = instantiate_template_with_args(
                    *component_info,
                    std::move(arguments),
                    component.loc,
                    0,
                    false,
                    true);
                if (!instantiated.valid() ||
                    !collect_session_.file().valid(instantiated)) {
                    return collect_session_.type_ref(
                        collect_session_.file().unknown_type());
                }
                if (check(TokenType::SCOPE_RESOLUTION)) {
                    context = collect_session_.file()
                                  .entity(instantiated)
                                  .semantic_context;
                    continue;
                }
                return collect_session_.type_ref(
                    collect_session_.file().entity(instantiated).type);
            }
            if (has_template) {
                diagnose(DiagnosticLevel::Error,
                         "template disambiguator requires a template argument list",
                         component.loc);
                return collect_session_.type_ref(
                    collect_session_.file().unknown_type());
            }
            if (check(TokenType::SCOPE_RESOLUTION)) {
                collect::Session::QualifierResolution next =
                    collect_session_.resolve_qualifier_component(
                        context, component.value, component.loc);
                if (next.has_error) {
                    return collect_session_.type_ref(
                        collect_session_.file().unknown_type());
                }
                if (next.dependent_type.valid()) {
                    return parse_dependent_scope_tail(next.dependent_type);
                }
                context = next.context;
                continue;
            }
            cir::TypeId type = collect_session_.lookup_qualified_type_name(
                context, component.value);
            if (!type.valid()) {
                diagnose(DiagnosticLevel::Error,
                         "spliced scope does not contain type '" +
                             std::string(component.value) + "'",
                         component.loc);
                type = collect_session_.file().unknown_type();
            }
            return collect_session_.type_ref(type);
        }
        return collect_session_.type_ref(
            collect_session_.file().unknown_type());
    };
    if (check(TokenType::LESS_THAN)) {
        collect::Session::SpliceTemplateResolution resolution =
            collect_session_.resolve_splice_template_operand(
                std::move(operand.sem), open.loc);
        std::vector<collect::Session::TemplateArgument> arguments;
        uint64_t point_lookup_generation = 0;
        if (resolution.dependent) {
            collect::Session::TemplateInfo neutral;
            if (!parse_candidate_neutral_template_argument_list(
                    neutral, arguments, open.loc)) {
                return collect_session_.type_ref(
                    collect_session_.file().unknown_type());
            }
            cir::NameId display = collect_session_.file().intern_name(
                "[:splice:]");
            cir::TypeRef dependent = collect_session_.type_ref(
                collect_session_.file().template_specialization_type(
                    display,
                    resolution.template_entity,
                    std::move(arguments),
                    /*is_dependent=*/true,
                    /*is_class_template_placeholder=*/false,
                    std::move(splice_operand)));
            return check(TokenType::SCOPE_RESOLUTION)
                ? parse_dependent_scope_tail(dependent)
                : dependent;
        }
        const collect::Session::TemplateInfo* info =
            collect_session_.template_info(resolution.template_entity);
        if (resolution.has_error || !info ||
            (!info->is_class_template && !info->is_alias_template)) {
            if (!resolution.has_error) {
                diagnose(DiagnosticLevel::Error,
                         "splice type specialization must designate a class or alias template",
                         open.loc);
            }
            collect::Session::TemplateInfo neutral;
            (void)parse_candidate_neutral_template_argument_list(
                neutral, arguments, open.loc);
            return collect_session_.type_ref(
                collect_session_.file().unknown_type());
        }
        if (!parse_and_canonicalize_template_argument_list(
                *info,
                arguments,
                open.loc,
                &point_lookup_generation)) {
            return collect_session_.type_ref(
                collect_session_.file().unknown_type());
        }
        cir::EntityId instantiated = instantiate_template_with_args(
            *info,
            std::move(arguments),
            open.loc,
            point_lookup_generation,
            /*replay_guard_entered=*/false,
            /*arguments_are_canonical=*/true);
        if (!instantiated.valid() ||
            !collect_session_.file().valid(instantiated)) {
            return collect_session_.type_ref(
                collect_session_.file().unknown_type());
        }
        if (check(TokenType::SCOPE_RESOLUTION)) {
            return parse_concrete_scope_tail(
                collect_session_.file().entity(instantiated).semantic_context);
        }
        return collect_session_.type_ref(
            collect_session_.file().entity(instantiated).type);
    }
    if (check(TokenType::SCOPE_RESOLUTION)) {
        bool dependent = false;
        collect::Session::QualifierResolution scope =
            collect_session_.resolve_splice_scope_operand(
                std::move(operand.sem), open.loc, &dependent);
        if (dependent) {
            return parse_dependent_scope_tail(
                scope.dependent_type.valid()
                    ? scope.dependent_type
                    : collect_session_.type_ref(
                          collect_session_.file().dependent_type(
                              "[:splice-scope:]")));
        }
        if (scope.has_error || !scope.context.valid()) {
            return collect_session_.type_ref(
                collect_session_.file().unknown_type());
        }
        return parse_concrete_scope_tail(scope.context);
    }
    return collect_session_.splice_type_operand(std::move(operand.sem),
                                                open.loc);
}

} // namespace aburi::syntax
