#include "parser.h"

#include <algorithm>
#include <iterator>
#include <optional>
#include <unordered_set>
#include <utility>
#include <vector>

#include "../cir/layout.h"
#include "../perf_stats.h"

namespace aburi::syntax {

namespace {

TextPayload text_payload(std::string_view text) {
    return TextPayload{std::string(text)};
}

cir::RecordKind class_key_record_kind(TokenType token) {
    if (token == TokenType::UNION) {
        return cir::RecordKind::Union;
    }
    return token == TokenType::CLASS ? cir::RecordKind::Class
                                     : cir::RecordKind::Struct;
}

bool class_template_keys_agree(cir::RecordKind lhs, cir::RecordKind rhs) {

    return (lhs == cir::RecordKind::Union) ==
           (rhs == cir::RecordKind::Union);
}

bool has_forbidden_explicit_instantiation_attributes(
    const AttributeList& attrs) {
    return std::any_of(
        attrs.attrs.begin(),
        attrs.attrs.end(),
        [](const ParsedAttribute& attr) {

            return attr.syntax != AttributeSyntax::GNU;
        });
}

class ExplicitInstantiationReplayOutcomeScope {
public:
    ExplicitInstantiationReplayOutcomeScope(
        collect::Session& session,
        collect::Session::TemplateReplayOutcome& outcome)
        : session_(session),
          outcome_(outcome),
          previous_(session_.set_template_replay_outcome(&outcome_)) {}

    ExplicitInstantiationReplayOutcomeScope(
        const ExplicitInstantiationReplayOutcomeScope&) = delete;
    ExplicitInstantiationReplayOutcomeScope& operator=(
        const ExplicitInstantiationReplayOutcomeScope&) = delete;

    ~ExplicitInstantiationReplayOutcomeScope() {
        session_.set_template_replay_outcome(previous_);
        if (!previous_) {
            return;
        }
        if (outcome_.hard_error()) {
            previous_->note_hard_error();
        } else if (outcome_.unavailable()) {
            previous_->note_unavailable(outcome_.blocker);
        } else if (outcome_.substitution_failure()) {
            previous_->note_substitution_failure();
        }
    }

private:
    collect::Session& session_;
    collect::Session::TemplateReplayOutcome& outcome_;
    collect::Session::TemplateReplayOutcome* previous_ = nullptr;
};

bool type_contains_lambda_closure(const cir::File& file,
                                  cir::TypeId type,
                                  std::unordered_set<uint32_t>& visiting) {
    type = file.resolved_type(type);
    if (!file.valid(type) || !visiting.insert(type.index).second) {
        return false;
    }
    auto contains_ref = [&](cir::TypeRef ref) {
        return ref.type.valid() &&
            type_contains_lambda_closure(file, ref.type, visiting);
    };
    auto contains_argument = [&](const cir::TemplateArgument& argument) {
        return contains_ref(argument.type) ||
            contains_ref(argument.value_type) ||
            contains_ref(argument.dependent_value_qualifier) ||
            contains_ref(argument.dependent_template_qualifier);
    };
    const cir::TypePayload& payload = file.type_payload(type);
    switch (file.type(type).kind) {
        case cir::TypeKind::Record: {
            cir::EntityId entity = file.record_entity(type);
            const cir::RecordFacts* facts = file.record_facts(entity);
            if (facts && facts->is_lambda_closure) {
                return true;
            }
            const cir::TemplateSpecializationFact* specialization =
                file.template_specialization(entity);
            if (!specialization) {
                return false;
            }
            std::vector<cir::TemplateArgument> arguments =
                specialization->template_arguments();
            return std::any_of(arguments.begin(),
                               arguments.end(),
                               contains_argument);
        }
        case cir::TypeKind::Pointer:
            return contains_ref(
                std::get<cir::PointerTypePayload>(payload).pointee);
        case cir::TypeKind::BlockPointer:
            return contains_ref(
                std::get<cir::BlockPointerTypePayload>(payload).pointee);
        case cir::TypeKind::MemberPointer: {
            const auto& member =
                std::get<cir::MemberPointerTypePayload>(payload);
            return contains_ref(member.class_type) ||
                contains_ref(member.member_type);
        }
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference:
            return contains_ref(
                std::get<cir::ReferenceTypePayload>(payload).referred_type);
        case cir::TypeKind::Array:
            return contains_ref(
                std::get<cir::ArrayTypePayload>(payload).element_type);
        case cir::TypeKind::Function: {
            const auto& function =
                std::get<cir::FunctionTypePayload>(payload);
            return contains_ref(function.return_type) ||
                std::any_of(function.parameters.begin(),
                            function.parameters.end(),
                            contains_ref);
        }
        case cir::TypeKind::Vector:
            return contains_ref(
                std::get<cir::VectorTypePayload>(payload).element_type);
        case cir::TypeKind::Complex:
            return contains_ref(
                std::get<cir::ComplexTypePayload>(payload).element_type);
        case cir::TypeKind::Typedef:
            return contains_ref(
                std::get<cir::TypedefTypePayload>(payload).underlying_type);
        case cir::TypeKind::TemplateSpecialization: {
            const auto& specialization =
                std::get<cir::TemplateSpecializationTypePayload>(payload);
            return std::any_of(specialization.arguments.begin(),
                               specialization.arguments.end(),
                               contains_argument);
        }
        case cir::TypeKind::DependentName: {
            const auto& dependent =
                std::get<cir::DependentNameTypePayload>(payload);
            return contains_ref(dependent.qualifier_type) ||
                std::any_of(dependent.template_arguments.begin(),
                            dependent.template_arguments.end(),
                            contains_argument);
        }
        case cir::TypeKind::DecltypeExpr: {
            const auto& decltype_expr =
                std::get<cir::DecltypeExprTypePayload>(payload);
            return contains_ref(decltype_expr.operand_type) ||
                contains_ref(decltype_expr.dependent_value_qualifier);
        }
        case cir::TypeKind::BuiltinTransform:
            return contains_ref(
                std::get<cir::BuiltinTypeTransformTypePayload>(payload)
                    .operand_type);
        case cir::TypeKind::BuiltinPackElement: {
            const auto& pack =
                std::get<cir::BuiltinPackElementTypePayload>(payload);
            return std::any_of(pack.arguments.begin(),
                               pack.arguments.end(),
                               contains_argument);
        }
        case cir::TypeKind::PackIndex: {
            const auto& pack = std::get<cir::PackIndexTypePayload>(payload);
            return contains_ref(pack.pack_type) ||
                std::any_of(pack.expansions.begin(),
                            pack.expansions.end(),
                            contains_ref);
        }
        case cir::TypeKind::Place:
            return contains_ref(
                std::get<cir::PlaceTypePayload>(payload).object_type);
        default:
            return false;
    }
}

bool type_contains_lambda_closure(const cir::File& file, cir::TypeId type) {
    std::unordered_set<uint32_t> visiting;
    return type_contains_lambda_closure(file, type, visiting);
}

struct TemplateArgumentAccessExemptionScope {
    collect::Session& session;
    bool active = false;

    explicit TemplateArgumentAccessExemptionScope(collect::Session& session,
                                                   bool active = true)
        : session(session), active(active) {
        if (active) {
            session.enter_template_argument_access_exemption();
        }
    }

    ~TemplateArgumentAccessExemptionScope() {
        if (active) {
            session.leave_template_argument_access_exemption();
        }
    }

    void finish() {
        if (active) {
            session.leave_template_argument_access_exemption();
            active = false;
        }
    }
};

bool declaration_context_encloses(const cir::File& file,
                                  cir::DeclContextId enclosing,
                                  cir::DeclContextId nested) {
    for (cir::DeclContextId current = nested;
         current.valid() && file.valid(current);
         current = file.decl_context(current).parent) {
        if (current == enclosing) {
            return true;
        }
    }
    return false;
}

cir::DeclContextId enclosing_namespace_context(const cir::File& file,
                                               cir::DeclContextId context) {
    for (cir::DeclContextId current = context;
         current.valid() && file.valid(current);
         current = file.decl_context(current).parent) {
        cir::DeclContextKind kind = file.decl_context(current).kind;
        if (kind == cir::DeclContextKind::Namespace ||
            kind == cir::DeclContextKind::TranslationUnit) {
            return current;
        }
    }
    return {};
}

std::optional<collect::Session::TemplateArgumentBindings>
canonical_template_argument_bindings(
    const collect::Session& session,
    const std::vector<collect::Session::TemplateParameter>& parameters,
    const std::vector<collect::Session::TemplateArgument>& arguments) {
    collect::Session::TemplateArgumentBindings bindings;
    if (!session.bind_template_arguments_to_parameters(parameters,
                                                       arguments,
                                                       bindings)) {
        return std::nullopt;
    }
    session.canonicalize_template_argument_bindings(bindings);
    return bindings;
}

bool constant_template_parameter_type_is_supported(
    const collect::Session& session,
    cir::TypeId type) {
    return session.constant_template_parameter_type_is_supported(type);
}

struct TypeParamRemap {
    cir::TypeId from{};
    cir::TypeId to{};
    uint32_t value_from = cir::ArrayTypePayload::no_extent_param;
    uint32_t value_to = cir::ArrayTypePayload::no_extent_param;
    uint32_t template_from = cir::ArrayTypePayload::no_extent_param;
    uint32_t template_to = cir::ArrayTypePayload::no_extent_param;
    cir::EntityId template_entity{};
    std::string template_name;
    std::vector<collect::Session::TemplateParameter> template_parameters;
    bool template_is_parameter_pack = false;
};

cir::TypeRef remap_type_params_in_ref(
    collect::Session& session,
    cir::TypeRef ref,
    const std::vector<TypeParamRemap>& remaps);

cir::TypeId remap_type_params_in_type(
    collect::Session& session,
    cir::TypeId type,
    const std::vector<TypeParamRemap>& remaps) {
    cir::File& file = session.file();
    if (!type.valid() || !file.valid(type)) {
        return type;
    }
    cir::TypeId resolved = file.resolved_type(type);
    if (!file.valid(resolved)) {
        return type;
    }
    for (const TypeParamRemap& remap : remaps) {
        if (file.resolved_type(remap.from) == resolved) {
            return remap.to;
        }
    }

    switch (file.type(resolved).kind) {
        case cir::TypeKind::Pointer: {
            const auto& pointer =
                std::get<cir::PointerTypePayload>(file.type_payload(resolved));
            return file.pointer_type(
                remap_type_params_in_ref(session, pointer.pointee, remaps));
        }
        case cir::TypeKind::BlockPointer: {
            const auto& pointer =
                std::get<cir::BlockPointerTypePayload>(
                    file.type_payload(resolved));
            return file.block_pointer_type(
                remap_type_params_in_ref(session, pointer.pointee, remaps));
        }
        case cir::TypeKind::MemberPointer: {
            const auto& member =
                std::get<cir::MemberPointerTypePayload>(
                    file.type_payload(resolved));
            return file.member_pointer_type(
                remap_type_params_in_ref(session, member.class_type, remaps),
                remap_type_params_in_ref(session, member.member_type, remaps));
        }
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference: {
            const auto& reference =
                std::get<cir::ReferenceTypePayload>(
                    file.type_payload(resolved));
            return file.reference_type(
                remap_type_params_in_ref(session,
                                         reference.referred_type,
                                         remaps),
                reference.reference_kind);
        }
        case cir::TypeKind::Array: {
            const auto& array =
                std::get<cir::ArrayTypePayload>(file.type_payload(resolved));
            uint32_t extent_param = array.extent_param;
            for (const TypeParamRemap& remap : remaps) {
                if (remap.value_from != cir::ArrayTypePayload::no_extent_param &&
                    remap.value_from == extent_param) {
                    extent_param = remap.value_to;
                    break;
                }
            }
            cir::TemplateValueExpression dependent_size_expr =
                array.dependent_size_expr;
            for (cir::TemplateValueExprNode& node :
                 dependent_size_expr.nodes) {
                for (const TypeParamRemap& remap : remaps) {
                    if (remap.value_from !=
                            cir::ArrayTypePayload::no_extent_param &&
                        remap.value_from == node.parameter_index) {
                        node.parameter_index = remap.value_to;
                        break;
                    }
                }
                if (node.type.valid()) {
                    node.type = remap_type_params_in_type(session,
                                                          node.type,
                                                          remaps);
                }
                node.result_type = remap_type_params_in_ref(
                    session, node.result_type, remaps);
                node.qualifier_type = remap_type_params_in_ref(
                    session, node.qualifier_type, remaps);
            }
            return file.array_type(
                remap_type_params_in_ref(session, array.element_type, remaps),
                array.size_kind,
                array.size,
                array.size_expr,
                array.size_expr_is_dependent,
                extent_param,
                std::move(dependent_size_expr));
        }
        case cir::TypeKind::Function: {
            const auto& function =
                std::get<cir::FunctionTypePayload>(
                    file.type_payload(resolved));
            std::vector<cir::TypeRef> parameters;
            parameters.reserve(function.parameters.size());
            for (cir::TypeRef parameter : function.parameters) {
                parameters.push_back(
                    remap_type_params_in_ref(session, parameter, remaps));
            }
            return file.function_type(
                remap_type_params_in_ref(session,
                                         function.return_type,
                                         remaps),
                parameters,
                function.is_variadic,
                function.has_prototype,
                function.member_is_const,
                function.exception_spec,
                function.parameter_pack_flags,
                function.member_ref_qualifier,
                function.member_is_volatile);
        }
        case cir::TypeKind::Complex: {
            const auto& complex =
                std::get<cir::ComplexTypePayload>(file.type_payload(resolved));
            return file.complex_type(
                remap_type_params_in_ref(session, complex.element_type, remaps));
        }
        case cir::TypeKind::Vector: {
            const auto& vector =
                std::get<cir::VectorTypePayload>(file.type_payload(resolved));
            return file.vector_type(
                remap_type_params_in_ref(session, vector.element_type, remaps),
                vector.element_count,
                vector.size_bytes);
        }
        case cir::TypeKind::Record: {
            cir::EntityId record = file.record_entity(resolved);
            const cir::TemplateSpecializationFact* fact =
                file.template_specialization(record);
            if (!fact || !fact->template_entity.valid()) {
                return type;
            }
            std::vector<cir::TemplateArgument> fact_arguments =
                fact->template_arguments();
            std::vector<cir::TemplateArgument> arguments;
            arguments.reserve(fact_arguments.size());
            bool changed = false;
            for (cir::TemplateArgument argument : fact_arguments) {
                if (argument.kind == cir::TemplateArgumentKind::Type) {
                    cir::TypeId original = argument.type.type;
                    argument.type = remap_type_params_in_ref(session,
                                                             argument.type,
                                                             remaps);
                    changed = changed || argument.type.type != original;
                } else if (argument.kind == cir::TemplateArgumentKind::Value) {
                    cir::TypeId original_type = argument.value_type.type;
                    uint32_t original_index = argument.value_param_index;
                    argument.value_type =
                        remap_type_params_in_ref(session,
                                                 argument.value_type,
                                                 remaps);
                    for (const TypeParamRemap& remap : remaps) {
                        if (remap.value_from !=
                                cir::ArrayTypePayload::no_extent_param &&
                            remap.value_from == argument.value_param_index) {
                            argument.value_param_index = remap.value_to;
                            argument.is_dependent = true;
                            break;
                        }
                    }
                    changed = changed ||
                              argument.value_type.type != original_type ||
                              argument.value_param_index != original_index;
                } else if (argument.kind ==
                           cir::TemplateArgumentKind::Template) {
                    uint32_t original_index = argument.template_param_index;
                    for (const TypeParamRemap& remap : remaps) {
                        if (remap.template_from !=
                                cir::ArrayTypePayload::no_extent_param &&
                            remap.template_from ==
                                argument.template_param_index) {
                            argument.template_param_index = remap.template_to;
                            argument.is_dependent = true;
                            break;
                        }
                    }
                    changed = changed ||
                              argument.template_param_index != original_index;
                }
                arguments.push_back(std::move(argument));
            }
            if (fact->template_param_index !=
                cir::ArrayTypePayload::no_extent_param) {
                for (const TypeParamRemap& remap : remaps) {
                    if (remap.template_from !=
                            cir::ArrayTypePayload::no_extent_param &&
                        remap.template_from == fact->template_param_index) {
                        collect::Session::TemplateInfo placeholder;
                        placeholder.entity = fact->template_entity;
                        placeholder.name = remap.template_name;
                        placeholder.template_parameter_index =
                            remap.template_to;
                        placeholder.is_class_template = true;
                        placeholder.is_template_parameter_pack =
                            remap.template_is_parameter_pack;
                        placeholder.parameters = remap.template_parameters;
                        cir::EntityId specialization =
                            session.create_dependent_record_specialization(
                                placeholder,
                                arguments,
                                SrcLoc());
                        return specialization.valid() &&
                                file.valid(specialization)
                            ? file.entity(specialization).type
                            : type;
                    }
                }
            }
            const collect::Session::TemplateInfo* target =
                session.template_info(fact->template_entity);
            if (!target || !target->is_class_template) {
                return type;
            }
            if (!changed) {
                return type;
            }
            cir::EntityId specialization =
                session.create_dependent_record_specialization(*target,
                                                               arguments,
                                                               SrcLoc());
            return specialization.valid() && file.valid(specialization)
                ? file.entity(specialization).type
                : type;
        }
        default:
            return type;
    }
}

cir::TypeRef remap_type_params_in_ref(
    collect::Session& session,
    cir::TypeRef ref,
    const std::vector<TypeParamRemap>& remaps) {
    ref.type = remap_type_params_in_type(session, ref.type, remaps);
    return ref;
}

cir::TemplateArgument remap_template_argument_placeholders(
    collect::Session& session,
    cir::TemplateArgument argument,
    const std::vector<TypeParamRemap>& remaps) {
    if (argument.kind == cir::TemplateArgumentKind::Type) {
        argument.type = remap_type_params_in_ref(session,
                                                 argument.type,
                                                 remaps);
    } else if (argument.kind == cir::TemplateArgumentKind::Value) {
        argument.value_type = remap_type_params_in_ref(session,
                                                       argument.value_type,
                                                       remaps);
        argument.dependent_value_qualifier =
            remap_type_params_in_ref(session,
                                     argument.dependent_value_qualifier,
                                     remaps);
        for (cir::TemplateValueExprNode& node :
             argument.dependent_value_expr.nodes) {
            for (const TypeParamRemap& remap : remaps) {
                if (remap.value_from !=
                        cir::ArrayTypePayload::no_extent_param &&
                    remap.value_from == node.parameter_index) {
                    node.parameter_index = remap.value_to;
                    break;
                }
            }
            if (node.type.valid()) {
                node.type = remap_type_params_in_type(session,
                                                      node.type,
                                                      remaps);
            }
            node.result_type = remap_type_params_in_ref(
                session, node.result_type, remaps);
            node.qualifier_type = remap_type_params_in_ref(
                session, node.qualifier_type, remaps);
        }
        for (const TypeParamRemap& remap : remaps) {
            if (remap.value_from != cir::ArrayTypePayload::no_extent_param &&
                remap.value_from == argument.value_param_index) {
                argument.value_param_index = remap.value_to;
                argument.is_dependent = true;
                break;
            }
        }
    } else if (argument.kind == cir::TemplateArgumentKind::Template) {
        argument.dependent_template_qualifier =
            remap_type_params_in_ref(session,
                                     argument.dependent_template_qualifier,
                                     remaps);
        for (const TypeParamRemap& remap : remaps) {
            if (remap.template_from !=
                    cir::ArrayTypePayload::no_extent_param &&
                remap.template_from == argument.template_param_index) {
                argument.template_param_index = remap.template_to;
                argument.is_dependent = true;
                break;
            }
        }
    }
    return argument;
}

struct TemplateReplayGuardExit {
    collect::Session* session = nullptr;
    bool active = false;

    ~TemplateReplayGuardExit() {
        if (active && session) {
            session->leave_template_replay_guard();
        }
    }
};

} // namespace

Parser::ParsedExplicitSpecifier Parser::parse_explicit_specifier() {
    ParsedExplicitSpecifier result;
    if (!match(TokenType::EXPLICIT_KW)) {
        return result;
    }
    result.kind = cir::ExplicitSpecifierKind::True;
    result.loc = last_consumed_loc();
    result.declaration_context = collect_session_.current_decl_context();
    result.lookup_generation = collect_session_.lookup_generation();
    if (!match(TokenType::LEFT_PAREN)) {
        return result;
    }
    if (!lang_opts_.is_cxx20_or_later()) {
        diagnose(DiagnosticLevel::Error,
                 "conditional explicit specifiers require C++20",
                 result.loc);
        result.has_error = true;
    }

    result.expression_begin = current_raw_index();
    collect_session_.begin_pattern_collection();
    uint64_t taint_before = collect_session_.pattern_taint();
    ParsedExpr operand = parse_conditional_expression();
    bool pattern_dependent =
        collect_session_.pattern_taint() != taint_before;
    (void)collect_session_.finish_pattern_collection();
    result.expression_end = current_raw_index();
    if (!match(TokenType::RIGHT_PAREN)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ')' after explicit specifier",
                 current_loc());
        result.has_error = true;
    }

    if (operand.sem.has_error) {
        result.kind = cir::ExplicitSpecifierKind::Invalid;
        result.has_error = true;
        return result;
    }
    if (pattern_dependent ||
        collect_session_.expr_is_dependent(operand.sem) ||
        operand.sem.references_template_value_parameter) {
        result.kind = cir::ExplicitSpecifierKind::Dependent;
        result.value_expression = std::move(operand.sem.template_value_expr);
        collect_session_.file().canonicalize_template_value_expression(
            result.value_expression);
        return result;
    }

    collect::Session::TemplateValueConstant constant;
    cir::TypeId bool_type =
        collect_session_.file().builtin_type(cir::BuiltinTypeKind::Bool);
    if (!collect_session_.evaluate_template_value_constant(
            std::move(operand.sem),
            bool_type,
            constant,
            result.loc,
            "explicit specifier is not a contextually converted constant expression of type bool")) {
        result.kind = cir::ExplicitSpecifierKind::Invalid;
        result.has_error = true;
        return result;
    }
    result.kind = !constant.integer_value.is_zero()
        ? cir::ExplicitSpecifierKind::True
        : cir::ExplicitSpecifierKind::False;
    return result;
}

std::optional<bool> Parser::replay_explicit_specifier(
    const collect::Session::TemplateInfo& info,
    const std::vector<collect::Session::TemplateArgument>& arguments,
    SrcLoc use_loc,
    const collect::Session::TemplateArgumentBindings* exact_bindings) {
    if (info.explicit_specifier == cir::ExplicitSpecifierKind::True) {
        return true;
    }
    if (info.explicit_specifier == cir::ExplicitSpecifierKind::False ||
        info.explicit_specifier == cir::ExplicitSpecifierKind::Absent) {
        return false;
    }
    if (info.explicit_specifier != cir::ExplicitSpecifierKind::Dependent ||
        info.explicit_expression_begin >= info.explicit_expression_end) {
        return std::nullopt;
    }

    if (info.explicit_value_expression.valid()) {
        collect::Session::TemplateArgumentBindings bindings;
        bool bindings_valid = false;
        if (exact_bindings) {
            bindings = *exact_bindings;
            bindings_valid = true;
        } else {
            bindings_valid =
                collect_session_.bind_template_arguments_to_parameters(
                    info.parameters, arguments, bindings);
        }
        if (bindings_valid) {
            std::string graph_error;
            std::optional<bool> value =
                collect_session_.evaluate_dependent_boolean_expression(
                    info.explicit_value_expression,
                    bindings,
                    &graph_error);
            if (value.has_value()) {
                return value;
            }
        }
    }

    struct ScopeExit {
        collect::Session* session = nullptr;
        collect::Session::InstantiationScope scope;
        ~ScopeExit() {
            if (session) {
                session->finish_template_instantiation(std::move(scope));
            }
        }
    } scope_exit;
    scope_exit.scope = collect_session_.begin_template_instantiation(
        info,
        arguments,
        use_loc,
        info.definition_generation,
        {},
        exact_bindings);
    if (!scope_exit.scope.active) {
        return std::nullopt;
    }
    scope_exit.session = &collect_session_;

    size_t saved_cursor = cursor_;
    size_t saved_last_end = last_consumed_raw_end_;
    int saved_closes = pending_template_closes_;
    cursor_ = info.explicit_expression_begin;
    pending_template_closes_ = 0;
    ParsedExpr operand = parse_conditional_expression();
    bool consumed_recipe = current_raw_index() == info.explicit_expression_end;
    cursor_ = saved_cursor;
    last_consumed_raw_end_ = saved_last_end;
    pending_template_closes_ = saved_closes;
    if (!consumed_recipe || operand.sem.has_error) {
        return std::nullopt;
    }

    collect::Session::TemplateValueConstant constant;
    cir::TypeId bool_type =
        collect_session_.file().builtin_type(cir::BuiltinTypeKind::Bool);
    if (!collect_session_.evaluate_template_value_constant(
            std::move(operand.sem),
            bool_type,
            constant,
            use_loc,
            "explicit specifier is not a contextually converted constant expression of type bool")) {
        return std::nullopt;
    }
    return !constant.integer_value.is_zero();
}

std::optional<bool>
Parser::resolve_member_specialization_explicit_specifier(
    const collect::Session::TemplateInfo& info,
    const std::vector<collect::Session::TemplateArgument>& arguments,
    cir::EntityId specialization,
    SrcLoc use_loc,
    const collect::Session::TemplateArgumentBindings* exact_bindings) {
    std::optional<bool> value = replay_explicit_specifier(
        info, arguments, use_loc, exact_bindings);
    if (!value.has_value() ||
        info.explicit_specifier != cir::ExplicitSpecifierKind::Dependent) {
        return value;
    }

    cir::File& file = collect_session_.file();
    if (!specialization.valid() || !file.valid(specialization)) {
        return std::nullopt;
    }
    cir::EntityId owner = file.entity(specialization).parent;
    const cir::RecordFacts* existing = file.record_facts(owner);
    if (!existing) {
        return std::nullopt;
    }
    cir::RecordFacts updated = *existing;
    bool found = false;
    for (cir::RecordMethodFact& method : updated.methods) {
        if (method.entity != specialization) {
            continue;
        }
        method.is_explicit = *value;
        method.explicit_specifier = *value
            ? cir::ExplicitSpecifierKind::True
            : cir::ExplicitSpecifierKind::False;
        found = true;
        break;
    }
    if (!found) {
        return std::nullopt;
    }
    file.set_record_facts(owner, std::move(updated));
    return value;
}

void Parser::record_trailing_function_requires_clause(
    collect::Session::TemplateInfo& info,
    const ParsedDeclarator& declarator) {
    if (!declarator.has_trailing_requires_clause) {
        return;
    }
    record_function_constraint_parameters(info, declarator.params);
    record_trailing_function_requires_clause(
        info,
        declarator.trailing_requires_constraint_begin,
        declarator.trailing_requires_constraint_end,
        declarator.trailing_requires_normal_form);
}

void Parser::record_function_constraint_parameters(
    collect::Session::TemplateInfo& info,
    const std::vector<ParsedParam>& parameters) {
    info.function_constraint_parameters.clear();
    info.function_constraint_parameters.reserve(parameters.size());
    for (const ParsedParam& parameter : parameters) {
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
        info.function_constraint_parameters.push_back(std::move(recipe));
    }
}

void Parser::record_trailing_function_requires_clause(
    collect::Session::TemplateInfo& info,
    size_t constraint_begin,
    size_t constraint_end,
    std::optional<collect::Session::NormalizedConstraint> normal_form) {
    collect::Session::TemplateInfo::IntroducedConstraint constraint{
        collect::Session::TemplateInfo::IntroducedConstraintKind::
            FunctionTrailingRequires,
        constraint_begin,
        constraint_end};
    if (normal_form.has_value()) {
        stamp_constraint_declaration_keys(*normal_form, info.parameters);
        collect_session_.record_constraint_parameter_provenance(
            *normal_form);
    }
    constraint.normal_form = std::move(normal_form);
    info.introduced_constraints.push_back(std::move(constraint));
}

std::optional<Parser::ParsedTypeConstraint>
Parser::try_parse_type_constraint() {
    size_t offset = 0;
    bool global_qualifier = false;
    if (peek(offset).type == TokenType::SCOPE_RESOLUTION) {
        global_qualifier = true;
        ++offset;
    }

    std::vector<std::string_view> qualifiers;
    while (is_identifier_token(peek(offset).type) &&
           peek(offset + 1).type == TokenType::SCOPE_RESOLUTION &&
           peek(offset + 2).type != TokenType::MULTIPLY) {
        qualifiers.push_back(peek(offset).value);
        offset += 2;
    }

    if (!is_identifier_token(peek(offset).type)) {
        return std::nullopt;
    }

    Token concept_token = peek(offset);
    const collect::Session::TemplateInfo* concept_info = nullptr;
    if (qualifiers.empty() && !global_qualifier) {
        concept_info =
            collect_session_.template_info_for_name(concept_token.value);
    } else {
        concept_info = collect_session_.peek_qualified_template_info(
            global_qualifier,
            qualifiers,
            concept_token.value);
    }
    if (!concept_info || !concept_info->is_concept) {
        return std::nullopt;
    }

    for (size_t i = 0; i <= offset; ++i) {
        consume();
    }

    ParsedTypeConstraint result;
    result.concept_info = concept_info;
    result.loc = concept_token.loc;
    result.qualified_name = global_qualifier || !qualifiers.empty();

    if (concept_info->parameters.empty() ||
        concept_info->parameters.front().kind !=
            collect::Session::TemplateParameterKind::Type) {
        diagnose(DiagnosticLevel::Error,
                 "type-constraint shall designate a type concept",
                 concept_token.loc);
        result.has_error = true;
    }

    if (check(TokenType::LESS_THAN)) {
        collect::Session::TemplateInfo tail_info = *concept_info;
        if (!tail_info.parameters.empty()) {
            tail_info.parameters.erase(tail_info.parameters.begin());
        }
        if (!parse_template_argument_list_with_request(tail_info,
                                                       result.arguments,
                                                       concept_token.loc)) {
            result.has_error = true;
        }
    }

    return result;
}

bool Parser::starts_type_constraint_placeholder(size_t offset) const {
    size_t cursor = offset;
    bool global_qualifier = false;
    if (peek(cursor).type == TokenType::SCOPE_RESOLUTION) {
        global_qualifier = true;
        ++cursor;
    }

    std::vector<std::string_view> qualifiers;
    while (is_identifier_token(peek(cursor).type) &&
           peek(cursor + 1).type == TokenType::SCOPE_RESOLUTION &&
           peek(cursor + 2).type != TokenType::MULTIPLY) {
        qualifiers.push_back(peek(cursor).value);
        cursor += 2;
    }
    if (!is_identifier_token(peek(cursor).type)) {
        return false;
    }
    std::string_view name = peek(cursor).value;
    const collect::Session::TemplateInfo* constraint_info =
        qualifiers.empty() && !global_qualifier
            ? collect_session_.template_info_for_name(name)
            : collect_session_.peek_qualified_template_info(
                  global_qualifier, qualifiers, name);
    if (!constraint_info || !constraint_info->is_concept) {
        return false;
    }
    ++cursor;
    if (peek(cursor).type == TokenType::LESS_THAN) {
        int depth = 0;
        do {
            TokenType type = peek(cursor).type;
            if (type == TokenType::Eof) {
                return false;
            }
            if (type == TokenType::LESS_THAN) {
                ++depth;
            } else if (type == TokenType::GREATER_THAN) {
                --depth;
            } else if (type == TokenType::RIGHT_SHIFT) {
                depth -= 2;
            }
            ++cursor;
        } while (depth > 0);
        if (depth < 0) {
            return false;
        }
    }
    return peek(cursor).type == TokenType::AUTO;
}

std::optional<collect::Session::NormalizedConstraint>
Parser::build_type_constraint_normal_form(
    const collect::Session::TemplateInfo& info,
    const collect::Session::TemplateParameter& parameter,
    const ParsedTypeConstraint& type_constraint) {
    (void)info;
    if (!type_constraint.concept_info ||
        !type_constraint.concept_info->is_concept ||
        (parameter.kind != collect::Session::TemplateParameterKind::Type &&
         (parameter.kind !=
              collect::Session::TemplateParameterKind::NonType ||
          !collect_session_.contains_auto_type(parameter.non_type_type))) ||
        (parameter.kind == collect::Session::TemplateParameterKind::Type &&
         !parameter.type_param_type.valid())) {
        return std::nullopt;
    }

    std::vector<collect::Session::TemplateArgument> concept_arguments;
    concept_arguments.reserve(type_constraint.arguments.size() + 1);
    collect::Session::TemplateArgument constrained_argument;
    constrained_argument.kind = cir::TemplateArgumentKind::Type;
    if (parameter.kind == collect::Session::TemplateParameterKind::Type) {
        constrained_argument.type =
            collect_session_.type_ref(parameter.type_param_type);
    } else {

        constrained_argument.type =
            collect_session_.type_ref(parameter.non_type_type);
        constrained_argument.value_param_index = parameter.index;
    }
    constrained_argument.is_dependent = true;
    if (!build_type_constraint_concept_arguments(
            *type_constraint.concept_info,
            constrained_argument,
            type_constraint.arguments,
            type_constraint.loc,
            concept_arguments)) {
        return std::nullopt;
    }

    collect::Session::NormalizedConstraint normal_form;
    uint32_t root = collect::Session::NormalizedConstraint::no_node;
    if (type_constraint.concept_info->constraint_normal_form.has_value()) {
        root = normal_form.append_copy_of(
            *type_constraint.concept_info->constraint_normal_form);
        if (!normal_form.valid_node(root)) {
            return std::nullopt;
        }

        collect::Session::PatternInstantiationCallbacks callbacks;
        configure_pattern_instantiation_callbacks(callbacks,
                                                  type_constraint.loc);
        std::string substitution_error;
        auto concept_argument_bindings = canonical_template_argument_bindings(
            collect_session_,
            type_constraint.concept_info->parameters,
            concept_arguments);
        if (!concept_argument_bindings.has_value()) {
            return std::nullopt;
        }
        if (!collect_session_.compose_constraint_parameter_mappings(
                normal_form,
                root,
                *concept_argument_bindings,
                callbacks,
                &substitution_error)) {
            return std::nullopt;
        }
    } else {
        collect::Session::ConstraintAtomIdentity atom;
        uint32_t dependent = normal_form.add_concept_dependent(std::move(atom));
        normal_form.nodes[dependent].concept_id_entity =
            type_constraint.concept_info->entity;
        normal_form.nodes[dependent].concept_id_template_parameter_index =
            type_constraint.concept_info->entity.valid() &&
                    collect_session_.file().valid(
                        type_constraint.concept_info->entity) &&
                    collect_session_.file()
                            .entity(type_constraint.concept_info->entity)
                            .kind == cir::EntityKind::TemplateParam
                ? type_constraint.concept_info->template_parameter_index
                : cir::ArrayTypePayload::no_extent_param;
        normal_form.nodes[dependent].concept_id_name =
            type_constraint.concept_info->name.empty()
                ? cir::NameId{}
                : collect_session_.file().intern_name(
                      type_constraint.concept_info->name);
        normal_form.nodes[dependent].concept_id_qualified_name =
            type_constraint.qualified_name;
        normal_form.nodes[dependent].concept_id_argument_list_begin = 0;
        normal_form.nodes[dependent].concept_id_argument_list_end = 0;
        normal_form.nodes[dependent].concept_id_arguments =
            std::move(concept_arguments);
        root = dependent;
    }

    if (parameter.is_parameter_pack) {
        root = normal_form.add_fold_expanded(
            collect::Session::ConstraintFoldOperator::LogicalAnd,
            root);
    }
    root = expand_concept_pack_fold_constraints(normal_form,
                                                root,
                                                type_constraint.loc);
    if (!normal_form.valid_node(root)) {
        return std::nullopt;
    }
    normal_form.root = root;
    return normal_form;
}

bool Parser::evaluate_type_constraint_for_constrained_type(
    const ParsedTypeConstraint& type_constraint,
    cir::TypeRef constrained_type,
    SrcLoc loc,
    bool& dependent,
    bool& satisfied) {
    dependent = false;
    satisfied = false;
    if (type_constraint.has_error || !type_constraint.concept_info ||
        !type_constraint.concept_info->is_concept ||
        !constrained_type.type.valid()) {
        return false;
    }

    collect::Session::TemplateArgument constrained_argument;
    constrained_argument.kind = cir::TemplateArgumentKind::Type;
    constrained_argument.type = constrained_type;
    constrained_argument.is_dependent =
        collect_session_.type_contains_type_param(constrained_type.type);

    if (constrained_argument.is_dependent) {
        dependent = true;
        satisfied = true;
        return true;
    }
    if (template_arguments_are_dependent(type_constraint.arguments)) {
        dependent = true;
        satisfied = true;
        return true;
    }
    if (!type_constraint.concept_info->has_definition) {
        dependent = true;
        satisfied = true;
        return true;
    }

    std::vector<collect::Session::TemplateArgument> concept_arguments;
    if (!build_type_constraint_concept_arguments(
            *type_constraint.concept_info,
            constrained_argument,
            type_constraint.arguments,
            type_constraint.loc.isInvalid() ? loc : type_constraint.loc,
            concept_arguments)) {
        return false;
    }

    uint64_t taint_before = collect_session_.pattern_taint();
    collect::ExprResult concept_result =
        evaluate_concept_id_expression(*type_constraint.concept_info,
                                       std::move(concept_arguments),
                                       type_constraint.loc.isInvalid()
                                           ? loc
                                           : type_constraint.loc,
                                       type_constraint.qualified_name);
    if (concept_result.has_error) {
        return false;
    }

    bool value_dependent =
        collect_session_.pattern_taint() != taint_before ||
        collect_session_.expr_is_dependent(concept_result) ||
        concept_result.references_template_value_parameter;
    std::optional<bool> value;
    if (!collect_session_.evaluate_constraint_expression(
            std::move(concept_result),
            value_dependent,
            value,
            type_constraint.loc.isInvalid() ? loc : type_constraint.loc)) {
        return false;
    }
    if (!value.has_value()) {
        dependent = true;
        satisfied = true;
        return true;
    }

    satisfied = *value;
    return true;
}

bool Parser::validate_placeholder_type_constraint(
    size_t constraint_begin,
    size_t constraint_end,
    SrcLoc constraint_loc,
    cir::TypeRef constrained_type,
    std::string_view diagnostic_subject) {
    if (constraint_begin >= constraint_end) {
        return true;
    }

    size_t saved_cursor = cursor_;
    size_t saved_last_consumed = last_consumed_raw_end_;
    int saved_template_closes = pending_template_closes_;
    cursor_ = constraint_begin;
    pending_template_closes_ = 0;
    std::optional<ParsedTypeConstraint> constraint =
        try_parse_type_constraint();
    bool consumed_range =
        constraint.has_value() && cursor_ == constraint_end;
    cursor_ = saved_cursor;
    last_consumed_raw_end_ = saved_last_consumed;
    pending_template_closes_ = saved_template_closes;

    if (!consumed_range) {
        diagnose(DiagnosticLevel::Error,
                 "could not replay placeholder type constraint",
                 constraint_loc);
        return false;
    }

    bool dependent = false;
    bool satisfied = false;
    if (!evaluate_type_constraint_for_constrained_type(
            *constraint,
            constrained_type,
            constraint_loc,
            dependent,
            satisfied)) {
        return false;
    }
    if (!dependent && !satisfied) {
        diagnose(DiagnosticLevel::Error,
                 std::string(diagnostic_subject) + " type '" +
                     collect_session_.file().format_type(constrained_type) +
                     "' does not satisfy its type constraint",
                 constraint_loc);
        return false;
    }
    return true;
}

bool Parser::validate_placeholder_return_type_constraint(
    cir::EntityId function,
    size_t constraint_begin,
    size_t constraint_end,
    SrcLoc constraint_loc) {
    const cir::File& file = collect_session_.file();
    if (!function.valid() || !file.valid(function)) {
        return false;
    }
    cir::PlaceholderResultFactId fact_id =
        file.entity(function).placeholder_result;
    if (!file.valid(fact_id)) {
        return false;
    }
    const cir::PlaceholderResultFact& fact =
        file.placeholder_result_fact(fact_id);
    cir::TypeRef result = fact.result.type.valid()
        ? fact.result
        : fact.candidate;
    if (!result.type.valid()) {
        return false;
    }
    return validate_placeholder_type_constraint(
        constraint_begin,
        constraint_end,
        constraint_loc,
        result,
        "deduced return");
}

Parser::ParsedDecl Parser::parse_cxx_using_declaration() {
    size_t begin = current_raw_index();
    Token using_token = current();
    consume();

    if (match(TokenType::ENUM)) {
        bool has_error = false;
        std::string name = "<enum>";
        bool qualified = check(TokenType::SCOPE_RESOLUTION) ||
            (is_identifier_token(current().type) &&
             (peek(1).type == TokenType::SCOPE_RESOLUTION ||
              (peek(1).type == TokenType::LESS_THAN &&
               template_id_precedes_scope(0))));
        if (qualified) {
            std::optional<cir::TypeRef> enum_type =
                parse_cxx_qualified_type_name(
                    TypeParseContext::type_only(
                        TypeParseContext::Origin::UsingEnumDeclarator));
            has_error = !enum_type.has_value() || !enum_type->valid();
            if (enum_type.has_value() && enum_type->valid()) {
                name = collect_session_.file().format_type(*enum_type);
                cir::TypeId resolved = collect_session_.file().resolved_type(
                    enum_type->type);
                if (collect_session_.file().valid(resolved) &&
                    collect_session_.file().type(resolved).kind ==
                        cir::TypeKind::DependentName) {

                } else if (collect_session_.file().valid(resolved) &&
                           collect_session_.file().type(resolved).kind ==
                               cir::TypeKind::Enum) {
                    const auto& payload =
                        std::get<cir::EnumTypePayload>(
                            collect_session_.file().type_payload(resolved));
                    cir::DeclContextId enum_context =
                        payload.entity.valid() &&
                                collect_session_.file().valid(payload.entity)
                            ? collect_session_.file()
                                  .entity(payload.entity)
                                  .semantic_context
                            : cir::DeclContextId{};
                    has_error = !collect_session_
                                     .collect_using_enum_declaration(
                                         enum_context, using_token.loc);
                } else {
                    diagnose(DiagnosticLevel::Error,
                             "using-enum declaration does not name an enumeration",
                             using_token.loc);
                    has_error = true;
                }
            }
        } else if (!is_identifier_token(current().type)) {
            diagnose(DiagnosticLevel::Error,
                     "expected enumeration name after 'using enum'",
                     current_loc());
            has_error = true;
        } else {
            Token target = current();
            consume();
            name = std::string(target.value);
            collect::Session::QualifierResolution resolved =
                collect_session_.resolve_qualifier_component(
                    {}, target.value, target.loc);
            has_error = resolved.has_error ||
                !collect_session_.collect_using_enum_declaration(
                    resolved.context, target.loc);
        }
        if (!match(TokenType::SEMICOLON)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ';' after using-enum-declaration",
                     current_loc());
            skip_until_statement_boundary();
            has_error = true;
        }
        collect::DeclResult decl;
        decl.has_error = has_error;
        return {make_node(NodeKind::UnknownDecl,
                          begin,
                          last_consumed_raw_end(),
                          {},
                          text_payload("using enum " + name),
                          has_error ? NodeFlagHasError : NodeFlagNone),
                std::move(decl)};
    }

    if (match(TokenType::NAMESPACE)) {
        if (check(TokenType::SPLICE_OPEN)) {
            Token open = current();
            consume();
            ParsedExpr operand = parse_expression(PrecLevel::ASSIGNMENT);
            bool has_error = false;
            if (!match(TokenType::SPLICE_CLOSE)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ':]' after using-directive splice",
                         current_loc());
                has_error = true;
            }
            bool dependent = false;
            collect::Session::QualifierResolution target =
                collect_session_.resolve_splice_scope_operand(
                    std::move(operand.sem), open.loc, &dependent);
            if (dependent) {
                diagnose(DiagnosticLevel::Error,
                         "using-directive splice cannot be dependent",
                         open.loc);
                has_error = true;
            } else if (!target.has_error) {
                if (!target.is_namespace || !target.entity.valid() ||
                    !collect_session_.file().valid(target.entity) ||
                    collect_session_.file().entity(target.entity).kind ==
                        cir::EntityKind::TranslationUnit) {
                    diagnose(DiagnosticLevel::Error,
                             "using-directive splice must designate a non-global namespace",
                             open.loc);
                    has_error = true;
                } else {
                    has_error =
                        !collect_session_.collect_using_directive(
                            target.context, using_token.loc) ||
                        has_error;
                }
            } else {
                has_error = true;
            }
            if (!match(TokenType::SEMICOLON)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ';' after using-directive",
                         current_loc());
                skip_until_statement_boundary();
                has_error = true;
            }
            collect::DeclResult decl;
            decl.has_error = has_error;
            return {make_node(NodeKind::UnknownDecl,
                              begin,
                              last_consumed_raw_end(),
                              {operand.syntax},
                              text_payload("using namespace [:splice:]"),
                              has_error ? NodeFlagHasError : NodeFlagNone),
                    std::move(decl)};
        }
        ParsedNestedName nested = parse_nested_name_specifier();
        std::string display = "using namespace";
        bool has_error = nested.has_error;
        if (!is_identifier_token(current().type)) {
            diagnose(DiagnosticLevel::Error,
                     "expected namespace name after 'using namespace'",
                     current_loc());
            has_error = true;
        } else {
            Token target = current();
            consume();
            display += " " + std::string(target.value);
            if (!has_error) {
                collect::Session::QualifierResolution resolved =
                    collect_session_.resolve_qualifier_component(
                        nested.scope.context, target.value, target.loc);
                has_error = resolved.has_error;
                if (!has_error) {
                    collect_session_.collect_using_directive(resolved.context,
                                                             using_token.loc);
                }
            }
        }
        if (!match(TokenType::SEMICOLON)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ';' after using-directive",
                     current_loc());
            skip_until_statement_boundary();
        }
        return {make_node(NodeKind::UnknownDecl,
                          begin,
                          last_consumed_raw_end(),
                          {},
                          text_payload(std::move(display)),
                          has_error ? NodeFlagHasError : NodeFlagNone),
                {}};
    }

    if (!is_identifier_token(current().type) &&
        !check(TokenType::TYPENAME) &&
        !check(TokenType::SCOPE_RESOLUTION)) {
        size_t end = skip_balanced_until_semicolon_or_brace();
        diagnose(DiagnosticLevel::Error, "expected name after 'using'", using_token.loc);
        return {make_node(NodeKind::UnknownDecl, begin, end, {}, {}, NodeFlagHasError), {}};
    }

    const bool starts_alias_declaration =
        is_identifier_token(current().type) &&
        (peek(1).type == TokenType::ASSIGN ||
         peek(1).type == TokenType::ATTRIBUTE_KW ||
         (peek(1).type == TokenType::LEFT_BRACKET &&
          peek(2).type == TokenType::LEFT_BRACKET));
    if (starts_alias_declaration) {
        NodeId name_node = parse_name_node(NodeKind::Name);
        std::string name = node_text(tree_.node(name_node));
        std::vector<NodeId> children{name_node};
        ParsedAttributes alias_attributes =
            try_parse_standard_or_gnu_attributes();
        children.insert(children.end(),
                        alias_attributes.syntax.begin(),
                        alias_attributes.syntax.end());
        if (!match(TokenType::ASSIGN)) {
            diagnose(DiagnosticLevel::Error,
                     "expected '=' in alias declaration",
                     current_loc());
            skip_until_statement_boundary();
            collect::DeclResult decl;
            decl.has_error = true;
            return {make_node(NodeKind::UnknownDecl,
                              begin,
                              last_consumed_raw_end(),
                              children,
                              text_payload("using " + name),
                              NodeFlagHasError),
                    std::move(decl)};
        }
        cir::TypeRef aliased_type{};
        NodeId type_name = parse_type_name(
            nullptr,
            nullptr,
            nullptr,
            &aliased_type,
            nullptr,
            nullptr,
            TypeParseContext::type_only(
                TypeParseContext::Origin::DefiningTypeId));
        children.push_back(type_name);
        if (!match(TokenType::SEMICOLON)) {
            diagnose(DiagnosticLevel::Error, "expected ';' after using alias", current_loc());
            skip_until_statement_boundary();
        }
        collect::DeclFlags flags;
        flags.attrs = std::move(alias_attributes.attrs);
        flags.type_qualifiers = aliased_type.qualifiers;
        collect::DeclResult decl = collect_session_.declare_typedef(
            name, aliased_type.type, using_token.loc, std::move(flags));
        return {make_node(NodeKind::VarDecl,
                          begin,
                          last_consumed_raw_end(),
                          children,
                          text_payload("using " + name)),
                std::move(decl)};
    }

    bool has_error = false;
    std::string name = "<name>";
    auto parse_using_declarator = [&]() -> bool {
        bool uses_typename = match(TokenType::TYPENAME);
        ParsedNestedName nested = parse_nested_name_specifier();
        bool declarator_error = nested.has_error;
        if (!nested.consumed_any) {
            diagnose(DiagnosticLevel::Error,
                     "using-declaration requires a qualified name",
                     using_token.loc);
            declarator_error = true;
            if (is_identifier_token(current().type)) {
                consume();
            }
        } else if (check(TokenType::BITWISE_NOT)) {
            SrcLoc destructor_loc = current_loc();
            consume();
            if (is_identifier_token(current().type)) {
                consume();
            }
            diagnose(DiagnosticLevel::Error,
                     "a using-declaration cannot name a destructor",
                     destructor_loc);
            declarator_error = true;
        } else if (starts_conversion_function_id()) {
            ParsedConversionFunctionId conversion_id =
                *parse_conversion_function_id();
            declarator_error = declarator_error || conversion_id.has_error;
            name = conversion_id.name;
            if (!declarator_error) {
                declarator_error =
                    !collect_session_.collect_using_declaration(
                        nested.scope.context,
                        conversion_id.name,
                        conversion_id.loc,
                        uses_typename,
                        nested.scope.dependent_type);
            }
        } else if (check(TokenType::OPERATOR_KW)) {

            ParsedOperatorFunctionId operator_id = *parse_operator_function_id();
            declarator_error = declarator_error || operator_id.has_error;
            name = operator_id.name;
            if (!declarator_error) {
                declarator_error = !collect_session_.collect_using_declaration(
                    nested.scope.context,
                    operator_id.name,
                    operator_id.loc,
                    uses_typename,
                    nested.scope.dependent_type);
            }
        } else if (!is_identifier_token(current().type)) {
            diagnose(DiagnosticLevel::Error,
                     "expected a name after the nested name specifier",
                     current_loc());
            declarator_error = true;
        } else {
            Token target = current();
            consume();
            name = std::string(target.value);
            if (check(TokenType::LESS_THAN)) {
                SrcLoc template_id_loc = current_loc();
                consume();
                int depth = 1;
                while (!at_end() && depth > 0) {
                    TokenType type = current().type;
                    consume();
                    if (type == TokenType::LESS_THAN) {
                        ++depth;
                    } else if (type == TokenType::GREATER_THAN) {
                        --depth;
                    } else if (type == TokenType::RIGHT_SHIFT) {
                        depth -= 2;
                    }
                }
                diagnose(DiagnosticLevel::Error,
                         "a using-declaration cannot name a template-id",
                         template_id_loc);
                declarator_error = true;
            }
            if (!declarator_error) {
                // The [namespace.udecl] lookup invariant treats the terminal
                // injected class name in using Base::Base as constructors.
                const cir::File& file = collect_session_.file();
                cir::EntityId scope_owner = nested.scope.context.valid()
                    ? file.decl_context(nested.scope.context).owner
                    : cir::EntityId{};
                bool names_concrete_constructor = scope_owner.valid() &&
                    file.valid(scope_owner) &&
                    file.entity(scope_owner).kind == cir::EntityKind::Record &&
                    file.entity(scope_owner).name.valid() &&
                    (file.name(file.entity(scope_owner).name) == target.value ||
                     nested.last_component_name == target.value);
                bool names_dependent_constructor =
                    !scope_owner.valid() &&
                    nested.scope.dependent_type.type.valid() &&
                    nested.last_component_name == target.value;
                bool names_constructor = names_concrete_constructor ||
                    names_dependent_constructor;
                if (names_constructor && !uses_typename) {
                    declarator_error =
                        !collect_session_
                             .collect_inherited_constructor_nomination(
                                 nested.scope.context,
                                 nested.scope.dependent_type,
                                 target.loc);
                } else {
                    declarator_error =
                        !collect_session_.collect_using_declaration(
                            nested.scope.context,
                            target.value,
                            target.loc,
                            uses_typename,
                            nested.scope.dependent_type);
                }
            }
        }
        return !declarator_error;
    };
    do {
        bool parsed_declarator = false;
        if (lang_opts_.is_cxx_mode() &&
            expression_list_element_has_pack_ellipsis(TokenType::COMMA,
                                                      TokenType::SEMICOLON)) {

            std::optional<PackExpansionPattern> pattern =
                try_parse_pack_expansion_pattern(
                    [&] { (void)parse_using_declarator(); });
            if (pattern.has_value() && pattern->has_pack_names()) {
                bool pack_arity_dependent = false;
                std::optional<size_t> element_count =
                    resolve_pack_expansion_element_count(
                        *pattern, &pack_arity_dependent);
                if (pack_arity_dependent) {
                    parse_pack_expansion_pattern_deferred([&] {
                        has_error = !parse_using_declarator() || has_error;
                    });
                    if (!match(TokenType::ELLIPSIS)) {
                        diagnose(
                            DiagnosticLevel::Error,
                            "expected '...' after using-declarator pattern",
                            current_loc());
                        has_error = true;
                    }
                } else {
                    replay_pack_expansion_elements(
                        *pattern,
                        element_count.value_or(0),
                        [&](size_t) {
                            has_error = !parse_using_declarator() ||
                                has_error;
                        });
                }
                parsed_declarator = true;
            } else if (pattern.has_value()) {
                diagnose(
                    DiagnosticLevel::Error,
                    "pack expansion pattern does not contain a template parameter pack",
                    pattern->ellipsis_loc);
                has_error = true;
                cursor_ = pattern->after_ellipsis_cursor;
                last_consumed_raw_end_ =
                    pattern->after_ellipsis_last_consumed_raw_end;
                parsed_declarator = true;
            }
        }
        if (!parsed_declarator) {
            has_error = !parse_using_declarator() || has_error;
        }
    } while (match(TokenType::COMMA));
    if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ';' after using-declaration",
                 current_loc());
        skip_until_statement_boundary();
    }
    collect::DeclResult decl;
    decl.has_error = has_error;
    return {make_node(NodeKind::UnknownDecl,
                      begin,
                      last_consumed_raw_end(),
                      {},
                      text_payload("using " + name),
                      has_error ? NodeFlagHasError : NodeFlagNone),
            std::move(decl)};
}

Parser::ParsedDecl Parser::parse_cxx_namespace_declaration(bool is_inline) {
    size_t begin = current_raw_index();
    Token namespace_token = current();
    consume();

    // Namespace attributes appear between the namespace keyword and the
    // optional name. libc++ uses the GNU spelling here for its visibility
    // annotation, while standard C++ attributes use the same position.
    ParsedAttributes namespace_attributes =
        try_parse_standard_or_gnu_attributes();
    const bool has_namespace_attributes = !namespace_attributes.syntax.empty();

    // Namespace alias: namespace A = B::C ;
    if (!has_namespace_attributes &&
        is_identifier_token(current().type) &&
        peek(1).type == TokenType::ASSIGN) {
        Token alias = current();
        consume();
        consume();
        if (check(TokenType::SPLICE_OPEN)) {
            Token open = current();
            consume();
            ParsedExpr operand = parse_expression(PrecLevel::ASSIGNMENT);
            bool has_error = false;
            if (!match(TokenType::SPLICE_CLOSE)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ':]' after namespace-alias splice",
                         current_loc());
                has_error = true;
            }
            bool dependent = false;
            collect::Session::QualifierResolution target =
                collect_session_.resolve_splice_scope_operand(
                    std::move(operand.sem), open.loc, &dependent);
            if (is_inline) {
                diagnose(DiagnosticLevel::Error,
                         "namespace alias cannot be inline",
                         namespace_token.loc);
                has_error = true;
            }
            if (dependent && !has_error) {
                collect_session_.collect_dependent_namespace_alias(
                    alias.value, alias.loc);
            } else if (!dependent && !target.has_error) {
                cir::EntityId target_entity = target.entity;
                if (!target.is_namespace || !target_entity.valid() ||
                    !collect_session_.file().valid(target_entity) ||
                    collect_session_.file().entity(target_entity).kind ==
                        cir::EntityKind::TranslationUnit) {
                    diagnose(DiagnosticLevel::Error,
                             "namespace alias splice must designate a non-global namespace",
                             open.loc);
                    has_error = true;
                } else {
                    has_error =
                        !collect_session_.collect_namespace_alias(
                            alias.value, target.context, alias.loc) ||
                        has_error;
                }
            } else {
                has_error = true;
            }
            if (!match(TokenType::SEMICOLON)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ';' after namespace alias",
                         current_loc());
                skip_until_statement_boundary();
                has_error = true;
            }
            collect::DeclResult decl;
            decl.has_error = has_error;
            return {make_node(
                        NodeKind::NamespaceDecl,
                        begin,
                        last_consumed_raw_end(),
                        std::move(namespace_attributes.syntax),
                        text_payload("namespace " +
                                     std::string(alias.value) + " = [:splice:]"),
                        has_error ? NodeFlagHasError : NodeFlagNone),
                    std::move(decl)};
        }
        ParsedNestedName nested = parse_nested_name_specifier();
        bool has_error = nested.has_error;
        if (is_inline) {
            diagnose(DiagnosticLevel::Error,
                     "namespace alias cannot be inline",
                     namespace_token.loc);
            has_error = true;
        }
        if (!is_identifier_token(current().type)) {
            diagnose(DiagnosticLevel::Error,
                     "expected namespace name in namespace alias",
                     current_loc());
            has_error = true;
        } else {
            Token target = current();
            consume();
            if (!has_error) {
                collect::Session::QualifierResolution resolved =
                    collect_session_.resolve_qualifier_component(
                        nested.scope.context, target.value, target.loc);
                has_error = resolved.has_error;
                if (!has_error) {
                    collect_session_.collect_namespace_alias(alias.value,
                                                             resolved.context,
                                                             alias.loc);
                }
            }
        }
        if (!match(TokenType::SEMICOLON)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ';' after namespace alias",
                     current_loc());
            skip_until_statement_boundary();
        }
        collect::DeclResult decl;
        decl.has_error = has_error;
        return {make_node(NodeKind::NamespaceDecl,
                          begin,
                          last_consumed_raw_end(),
                          std::move(namespace_attributes.syntax),
                          text_payload("namespace " + std::string(alias.value) + " ="),
                          has_error ? NodeFlagHasError : NodeFlagNone),
                std::move(decl)};
    }

    std::vector<std::string> names;
    std::vector<bool> inline_components;
    std::vector<NodeId> children = std::move(namespace_attributes.syntax);
    std::string display = is_inline ? "inline namespace" : "namespace";
    bool next_component_is_inline = is_inline;
    while (is_identifier_token(current().type)) {
        NodeId name_node = parse_name_node(NodeKind::Name);
        names.push_back(node_text(tree_.node(name_node)));
        inline_components.push_back(next_component_is_inline);
        next_component_is_inline = false;
        children.push_back(name_node);
        display += (names.size() == 1 ? " " : "::") + names.back();
        if (check(TokenType::SCOPE_RESOLUTION)) {
            consume();
            if (match(TokenType::INLINE)) {
                next_component_is_inline = true;
                display += "::inline";
            }
            if (!is_identifier_token(current().type)) {
                diagnose(DiagnosticLevel::Error,
                         "expected namespace name after '::'",
                         current_loc());
                break;
            }
            continue;
        }
        break;
    }

    // GCC accepts GNU attributes after the namespace name
    while (check(TokenType::ATTRIBUTE_KW)) {
        ParsedAttributes trailing = parse_gnu_attribute_list();
        namespace_attributes.attrs.append(std::move(trailing.attrs));
        children.insert(children.end(), trailing.syntax.begin(),
                        trailing.syntax.end());
    }

    bool nested_inline_prefix_error = is_inline && names.size() > 1;
    if (nested_inline_prefix_error) {
        diagnose(DiagnosticLevel::Error,
                 "nested namespace definition cannot be 'inline'",
                 namespace_token.loc);
    }

    if (!match(TokenType::LEFT_BRACE)) {
        size_t end = skip_balanced_until_semicolon_or_brace();
        diagnose(DiagnosticLevel::Error, "expected namespace body", namespace_token.loc);
        collect::DeclResult decl;
        decl.has_error = true;
        return {make_node(NodeKind::UnknownDecl, begin, end, children, {}, NodeFlagHasError),
                std::move(decl)};
    }

    size_t entered = 0;
    bool enter_error = nested_inline_prefix_error;
    if (names.empty()) {
        collect::Session::NamespaceEnterResult entered_namespace =
            collect_session_.enter_anonymous_namespace(namespace_token.loc);
        enter_error = entered_namespace.has_error;
        entered = 1;
        display += " <anonymous>";
    } else {
        for (size_t i = 0; i < names.size(); ++i) {
            collect::Session::NamespaceEnterResult entered_namespace =
                collect_session_.enter_named_namespace(names[i],
                                                       namespace_token.loc,
                                                       inline_components[i]);
            enter_error = enter_error || entered_namespace.has_error;
            ++entered;
        }
    }

    std::vector<collect::DeclResult> declarations;
    while (!at_end() && !check(TokenType::RIGHT_BRACE)) {
        ParsedDecl decl = parse_external_declaration();
        if (decl.syntax != InvalidNodeId) {
            children.push_back(decl.syntax);
        }
        declarations.push_back(std::move(decl.sem));
    }
    if (!match(TokenType::RIGHT_BRACE)) {
        diagnose(DiagnosticLevel::Error, "expected '}' after namespace body", current_loc());
    }
    for (size_t i = 0; i < entered; ++i) {
        collect_session_.leave_namespace();
    }

    collect::DeclResult decl =
        collect_session_.collect_decl_sequence(std::move(declarations), namespace_token.loc);
    decl.has_error = decl.has_error || enter_error;
    return {make_node(NodeKind::NamespaceDecl,
                      begin,
                      last_consumed_raw_end(),
                      children,
                      text_payload(std::move(display)),
                      decl.has_error ? NodeFlagHasError : NodeFlagNone),
            std::move(decl)};
}

Parser::ParsedDecl Parser::parse_cxx_linkage_specification() {
    size_t begin = current_raw_index();
    Token extern_token = current();
    consume();

    std::string language;
    size_t language_begin = current_raw_index();
    while (check(TokenType::STRING_LITERAL)) {
        language += current().value;
        consume();
    }
    std::vector<NodeId> children;
    children.push_back(make_node(NodeKind::StringLiteral,
                                 language_begin,
                                 last_consumed_raw_end(),
                                 {},
                                 text_payload(language)));

    bool is_extern_c = language == "C";
    if (!is_extern_c && language != "C++") {
        diagnose(DiagnosticLevel::Error,
                 "unknown linkage language \"" + language +
                     "\" in linkage specification, expected \"C\" or \"C++\"",
                 extern_token.loc);
    }

    bool braced = check(TokenType::LEFT_BRACE);
    collect_session_.enter_linkage_spec(is_extern_c,
                                        /*implies_extern_storage=*/!braced);
    std::vector<collect::DeclResult> declarations;
    if (match(TokenType::LEFT_BRACE)) {

        while (!at_end() && !check(TokenType::RIGHT_BRACE)) {
            ParsedDecl decl = parse_external_declaration();
            if (decl.syntax != InvalidNodeId) {
                children.push_back(decl.syntax);
            }
            declarations.push_back(std::move(decl.sem));
        }
        if (!match(TokenType::RIGHT_BRACE)) {
            diagnose(DiagnosticLevel::Error,
                     "expected '}' after linkage specification",
                     current_loc());
        }
    } else {
        ParsedDecl decl = parse_external_declaration();
        if (decl.syntax != InvalidNodeId) {
            children.push_back(decl.syntax);
        }
        declarations.push_back(std::move(decl.sem));
    }
    collect_session_.leave_linkage_spec();

    collect::DeclResult decl =
        collect_session_.collect_decl_sequence(std::move(declarations),
                                               extern_token.loc);
    return {make_node(NodeKind::LinkageSpecDecl,
                      begin,
                      last_consumed_raw_end(),
                      children,
                      text_payload("extern \"" + language + "\"")),
            std::move(decl)};
}

bool Parser::parse_cxx_template_head(collect::Session::TemplateInfo& info,
                                     SrcLoc template_loc,
                                     uint32_t parameter_depth,
                                     bool lambda_template_head) {
    bool header_error = false;
    if (!info.lexical_context.valid()) {
        info.lexical_context = collect_session_.current_decl_context();
    }
    info.complete_class_head_begin = current_raw_index();
    std::unordered_set<std::string> parameter_names;
    collect::Session::InstantiationScope parameter_scope;
    bool parameter_scope_active = false;
    if (match(TokenType::LESS_THAN)) {
        parameter_scope = collect_session_.begin_template_parameter_scope();
        parameter_scope_active = true;
        auto skip_constraint_template_arguments = [&](size_t& offset) -> bool {
            if (peek(offset).type != TokenType::LESS_THAN) {
                return true;
            }
            int depth = 0;
            while (true) {
                TokenType type = peek(offset).type;
                if (type == TokenType::Eof) {
                    return false;
                }
                if (type == TokenType::LESS_THAN) {
                    ++depth;
                } else if (type == TokenType::GREATER_THAN) {
                    --depth;
                    if (depth == 0) {
                        ++offset;
                        return true;
                    }
                } else if (type == TokenType::RIGHT_SHIFT) {
                    depth -= 2;
                    ++offset;
                    return depth <= 0;
                }
                ++offset;
            }
        };
        auto constrained_placeholder_parameter_ahead = [&]() -> bool {
            size_t offset = 0;
            if (peek(offset).type != TokenType::IDENTIFIER &&
                peek(offset).type != TokenType::SCOPE_RESOLUTION) {
                return false;
            }
            bool saw_name = false;
            while (true) {
                if (peek(offset).type == TokenType::SCOPE_RESOLUTION) {
                    ++offset;
                }
                if (peek(offset).type != TokenType::IDENTIFIER) {
                    return false;
                }
                saw_name = true;
                ++offset;
                if (!skip_constraint_template_arguments(offset)) {
                    return false;
                }
                if (peek(offset).type != TokenType::SCOPE_RESOLUTION) {
                    break;
                }
                ++offset;
            }
            return saw_name && peek(offset).type == TokenType::AUTO;
        };
        auto parse_template_template_parameter =
            [&](collect::Session::TemplateParameter& parameter) -> bool {
                SrcLoc parameter_loc = current_loc();
                if (!match(TokenType::TEMPLATE)) {
                    return false;
                }
                auto nested_head =
                    std::make_shared<collect::Session::TemplateInfo>();
                if (!parse_cxx_template_head(*nested_head,
                                             parameter_loc,
                                             parameter_depth + 1)) {
                    return false;
                }
                if (match(TokenType::TYPENAME) ||
                    match(TokenType::CLASS)) {
                    parameter.template_template_parameter_kind =
                        collect::Session::TemplateTemplateParameterKind::Type;
                } else if (match(TokenType::AUTO)) {
                    if (!lang_opts_.is_cxx26_or_later()) {
                        diagnose(DiagnosticLevel::Error,
                                 "variable template template parameters require C++26",
                                 parameter_loc);
                        return false;
                    }
                    parameter.template_template_parameter_kind =
                        collect::Session::TemplateTemplateParameterKind::
                            Variable;
                } else if (match(TokenType::CONCEPT_KW)) {
                    parameter.template_template_parameter_kind =
                        collect::Session::TemplateTemplateParameterKind::
                            Concept;
                } else {
                    diagnose(DiagnosticLevel::Error,
                             "expected 'class', 'typename', or 'concept' after template template parameter list",
                             current_loc());
                    return false;
                }
                parameter.kind =
                    collect::Session::TemplateParameterKind::Template;
                parameter.nested_head = std::move(nested_head);
                if (is_identifier_token(current().type)) {
                    parameter.name = current().value;
                    parameter.loc = current().loc;
                    consume();
                }
                return true;
            };
        if (!check(TokenType::GREATER_THAN)) {
            do {
                collect::Session::TemplateParameter parameter;
                std::optional<ParsedTypeConstraint> type_constraint;
                parameter.index =
                    static_cast<uint32_t>(info.parameters.size());
                parameter.depth = parameter_depth;
                parameter.loc = current_loc();
                bool typename_starts_qualified_parameter_type =
                    check(TokenType::TYPENAME) &&
                    (peek(1).type == TokenType::SCOPE_RESOLUTION ||
                     (is_identifier_token(peek(1).type) &&
                      peek(2).type == TokenType::SCOPE_RESOLUTION));
                if (check(TokenType::TEMPLATE)) {
                    if (!parse_template_template_parameter(parameter)) {
                        header_error = true;
                        break;
                    }
                } else if (constrained_placeholder_parameter_ahead()) {
                    type_constraint = try_parse_type_constraint();
                    if (!type_constraint.has_value() ||
                        type_constraint->has_error ||
                        !check(TokenType::AUTO)) {
                        diagnose(DiagnosticLevel::Error,
                                 "expected 'auto' after template parameter type-constraint",
                                 current_loc());
                        header_error = true;
                        break;
                    }
                    parameter.kind =
                        collect::Session::TemplateParameterKind::NonType;
                    DeclarationParser parameter_parser(
                        *this,
                        TypeParseContext::type_only(
                            TypeParseContext::Origin::ConstantTemplateParameter));
                    cir::TypeRef parameter_type =
                        parameter_parser.parse_declaration(true, false);
                    if (!parameter_type.valid() ||
                        !collect_session_.contains_auto_type(
                            parameter_type.type,
                            cir::AutoTypeFlavor::Cxx)) {
                        diagnose(DiagnosticLevel::Error,
                                 "expected constrained auto template parameter declaration",
                                 current_loc());
                        header_error = true;
                        break;
                    }
                    adjust_function_parameter_type(parameter_type);
                    parameter.non_type_type = parameter_type.type;
                    parameter.name = parameter_parser.name;
                    parameter.loc = parameter_parser.loc.isInvalid()
                        ? parameter.loc
                        : parameter_parser.loc;
                } else if ((type_constraint =
                                try_parse_type_constraint()).has_value()) {
                    parameter.kind =
                        collect::Session::TemplateParameterKind::Type;
                    parameter.loc = type_constraint->loc;
                } else if (!typename_starts_qualified_parameter_type &&
                           (match(TokenType::TYPENAME) ||
                            match(TokenType::CLASS))) {
                    parameter.kind =
                        collect::Session::TemplateParameterKind::Type;
                } else if (is_type_start(current().type) ||
                           starts_cxx_qualified_name()) {
                    parameter.kind =
                        collect::Session::TemplateParameterKind::NonType;
                    DeclarationParser parameter_parser(
                        *this,
                        TypeParseContext::type_only(
                            TypeParseContext::Origin::ConstantTemplateParameter));
                    cir::TypeRef parameter_type =
                        parameter_parser.parse_declaration(true, false);
                    if (const collect::Session::TemplateInfo* placeholder =
                            parameter_parser.deduced_class_template_info) {
                        cir::File& file = collect_session_.file();
                        cir::NameId name =
                            placeholder->entity.valid() &&
                                    file.valid(placeholder->entity) &&
                                    file.entity(placeholder->entity)
                                        .name.valid()
                                ? file.entity(placeholder->entity).name
                                : file.intern_name(placeholder->name);
                        parameter_type = collect_session_.type_ref(
                            file.template_specialization_type(
                                name,
                                placeholder->entity,
                                {},
                                /*is_dependent=*/true,
                                /*is_class_template_placeholder=*/true));
                    }
                    if (!parameter_type.valid()) {
                        diagnose(DiagnosticLevel::Error,
                                 "expected non-type template parameter declaration",
                                 current_loc());
                        header_error = true;
                        break;
                    }
                    adjust_function_parameter_type(parameter_type);
                    parameter.non_type_type = parameter_type.type;
                    if (!constant_template_parameter_type_is_supported(
                            collect_session_,
                            parameter.non_type_type)) {
                        diagnose(DiagnosticLevel::Error,
                                 "constant template parameter type is not structural",
                                 parameter.loc);
                        header_error = true;
                        break;
                    }
                    parameter.name = parameter_parser.name;
                    parameter.loc = parameter_parser.loc.isInvalid()
                        ? parameter.loc
                        : parameter_parser.loc;
                } else {
                    diagnose(DiagnosticLevel::Error,
                             "expected template parameter",
                             current_loc());
                    header_error = true;
                    break;
                }
                if (check(TokenType::ELLIPSIS)) {
                    parameter.is_parameter_pack = true;
                    consume();
                }
                if (parameter.kind ==
                        collect::Session::TemplateParameterKind::Type &&
                    is_identifier_token(current().type)) {
                    parameter.name = current().value;
                    consume();
                } else if (parameter.kind ==
                               collect::Session::TemplateParameterKind::NonType &&
                           parameter.is_parameter_pack &&
                           parameter.name.empty() &&
                           is_identifier_token(current().type)) {
                    parameter.name = current().value;
                    parameter.loc = current().loc;
                    consume();
                } else if (parameter.kind ==
                               collect::Session::TemplateParameterKind::Template &&
                           parameter.is_parameter_pack &&
                           parameter.name.empty() &&
                           is_identifier_token(current().type)) {
                    parameter.name = current().value;
                    parameter.loc = current().loc;
                    consume();
                }
                if (!parameter.name.empty()) {
                    auto [_, inserted] = parameter_names.insert(parameter.name);
                    if (!inserted) {
                        diagnose(DiagnosticLevel::Error,
                                 "template parameter name shadows an earlier template parameter",
                                 parameter.loc);
                        header_error = true;
                        break;
                    }
                }
                if (type_constraint.has_value() &&
                    type_constraint->has_error) {
                    header_error = true;
                    break;
                }
                if (parameter.is_parameter_pack && check(TokenType::ASSIGN)) {
                    diagnose(DiagnosticLevel::Error,
                             "template parameter pack cannot have a default argument",
                             current_loc());
                    header_error = true;
                    break;
                }
                if (match(TokenType::ASSIGN)) {
                    if (should_defer_complete_class_region()) {
                        parameter.requires_complete_class_default_replay =
                            true;
                        parameter.default_argument_token_begin =
                            current_raw_index();
                        parameter.default_argument_context =
                            collect_session_.current_decl_context();
                        parameter.default_argument_lookup_generation =
                            collect_session_.lookup_generation();
                        info.has_complete_class_default_recipes = true;

                        int angle_depth = 0;
                        int paren_depth = 0;
                        int bracket_depth = 0;
                        int brace_depth = 0;
                        while (!at_end()) {
                            TokenType type = current().type;
                            bool grouped = paren_depth > 0 ||
                                bracket_depth > 0 || brace_depth > 0;
                            if (!grouped && angle_depth == 0 &&
                                (type == TokenType::COMMA ||
                                 type == TokenType::GREATER_THAN ||
                                 type == TokenType::RIGHT_SHIFT)) {
                                break;
                            }
                            if (!grouped &&
                                type == TokenType::RIGHT_SHIFT &&
                                angle_depth == 1) {

                                ++pending_template_closes_;
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
                            case TokenType::LESS_THAN:
                                if (!grouped) {
                                    ++angle_depth;
                                }
                                break;
                            case TokenType::GREATER_THAN:
                                if (!grouped && angle_depth > 0) {
                                    --angle_depth;
                                }
                                break;
                            case TokenType::RIGHT_SHIFT:
                                if (!grouped && angle_depth > 0) {
                                    angle_depth = std::max(0,
                                                           angle_depth - 2);
                                }
                                break;
                            default:
                                break;
                            }
                            consume();
                        }
                        parameter.default_argument_token_end =
                            current_raw_index();
                        collect::Session::TemplateArgument placeholder;
                        placeholder.kind = parameter.kind ==
                                collect::Session::TemplateParameterKind::Type
                            ? cir::TemplateArgumentKind::Type
                            : parameter.kind == collect::Session::
                                      TemplateParameterKind::Template
                                ? cir::TemplateArgumentKind::Template
                                : cir::TemplateArgumentKind::Value;
                        placeholder.is_defaulted = true;
                        placeholder.is_dependent = true;
                        if (parameter.kind == collect::Session::
                                TemplateParameterKind::NonType) {
                            placeholder.value_type = collect_session_.type_ref(
                                parameter.non_type_type.valid()
                                    ? parameter.non_type_type
                                    : collect_session_.file().builtin_type(
                                          cir::BuiltinTypeKind::Int));
                        }
                        parameter.default_argument =
                            std::move(placeholder);
                    } else {
                    collect::Session::TemplateArgument default_argument;
                    if (parameter.kind ==
                        collect::Session::TemplateParameterKind::Type) {
                        default_argument.kind =
                            cir::TemplateArgumentKind::Type;
                        cir::TypeId default_type{};
                        cir::TypeRef default_type_ref{};
                        parse_type_name(&default_type,
                                        nullptr,
                                        nullptr,
                                        &default_type_ref,
                                        nullptr,
                                        nullptr,
                                        TypeParseContext::type_only(
                                            TypeParseContext::Origin::TypeParameterDefault));
                        if (!default_type.valid()) {
                            diagnose(DiagnosticLevel::Error,
                                     "expected a type template default argument",
                                     current_loc());
                            header_error = true;
                            break;
                        }
                        default_argument.type = default_type_ref;
                        default_argument.is_dependent =
                            collect_session_.is_dependent_type(default_type);
                    } else if (parameter.kind ==
                               collect::Session::TemplateParameterKind::Template) {
                        if (!parse_template_template_argument_name(
                                default_argument,
                                parameter.template_template_parameter_kind,
                                "expected a template template default argument",
                                parameter.template_template_parameter_kind ==
                                        collect::Session::
                                            TemplateTemplateParameterKind::
                                                Concept
                                    ? "template template default argument must name a concept template"
                                    : "template template default argument must name a class or alias template")) {
                            header_error = true;
                            break;
                        }
                    } else {
                        cir::TypeId expected_type =
                            parameter.non_type_type.valid()
                                ? parameter.non_type_type
                                : collect_session_.file().builtin_type(
                                      cir::BuiltinTypeKind::Int);
                        bool default_argument_built = false;
                        auto starts_qualified_id_expression = [&]() {
                            return check(TokenType::SCOPE_RESOLUTION) ||
                                   (is_identifier_token(current().type) &&
                                    peek(1).type ==
                                        TokenType::SCOPE_RESOLUTION &&
                                    peek(2).type != TokenType::MULTIPLY) ||
                                   (lang_opts_.is_cxx_mode() &&
                                    is_identifier_token(current().type) &&
                                    peek(1).type == TokenType::LESS_THAN &&
                                    template_id_precedes_scope(0));
                        };
                        bool starts_type_conversion_expression =
                            is_type_start(current().type) &&
                            (peek(1).type == TokenType::LEFT_PAREN ||
                             peek(1).type == TokenType::LEFT_BRACE);
                        if (is_type_start(current().type) &&
                            !starts_type_conversion_expression &&
                            !starts_qualified_id_expression()) {
                            diagnose(DiagnosticLevel::Error,
                                     "expected a non-type template default argument",
                                     current_loc());
                            header_error = true;
                            break;
                        }

                        ParsedExpr value =
                            parse_template_argument_constant_expression();
                        uint32_t value_param_index =
                            collect_session_.template_value_param_index(
                                value.sem.entity);
                        if (value_param_index !=
                            cir::ArrayTypePayload::no_extent_param) {
                            default_argument.kind =
                                cir::TemplateArgumentKind::Value;
                            default_argument.value_type =
                                collect_session_.type_ref(expected_type);
                            default_argument.value_param_index =
                                value_param_index;
                            if (value.sem.template_value_expr.valid()) {
                                default_argument.dependent_value_expr =
                                    std::move(value.sem.template_value_expr);
                            }
                            default_argument.value_spelling = value.sem.name;
                            default_argument.is_dependent = true;
                            default_argument_built = true;
                        }
                        if (!default_argument_built &&
                            collect_session_.expr_is_value_dependent(
                                value.sem) &&
                            value.sem.template_value_expr.valid()) {
                            default_argument.kind =
                                cir::TemplateArgumentKind::Value;
                            default_argument.value_type =
                                collect_session_.type_ref(expected_type);
                            default_argument.dependent_value_expr =
                                std::move(value.sem.template_value_expr);
                            default_argument.value_spelling = value.sem.name;
                            default_argument.is_dependent = true;
                            default_argument_built = true;
                        }
                        if (!default_argument_built &&
                            value.sem.dependent_value_name.valid() &&
                            value.sem.dependent_value_qualifier.type.valid()) {
                            default_argument.kind =
                                cir::TemplateArgumentKind::Value;
                            default_argument.value_type =
                                collect_session_.type_ref(expected_type);
                            default_argument.dependent_value_qualifier =
                                value.sem.dependent_value_qualifier;
                            default_argument.dependent_value_name =
                                value.sem.dependent_value_name;
                            const cir::File& file = collect_session_.file();
                            default_argument.value_spelling =
                                file.format_type(
                                    default_argument
                                        .dependent_value_qualifier) +
                                "::" +
                                file.name(
                                    default_argument.dependent_value_name);
                            default_argument.is_dependent = true;
                            default_argument_built = true;
                        }
                        if (!default_argument_built) {
                            bool is_class_template_placeholder =
                                collect_session_
                                    .class_template_placeholder_info(
                                        expected_type) != nullptr;
                            if (collect_session_.contains_auto_type(
                                    expected_type,
                                    cir::AutoTypeFlavor::Cxx)) {
                                cir::TypeId deduced_type =
                                    collect_session_.deduce_auto_type(
                                        expected_type,
                                        value.sem,
                                        parameter.loc);
                                if (!deduced_type.valid()) {
                                    diagnose(DiagnosticLevel::Error,
                                             "cannot deduce auto template parameter type",
                                             parameter.loc);
                                    header_error = true;
                                    break;
                                }
                                expected_type = deduced_type;
                            } else if (!is_class_template_placeholder &&
                                       collect_session_.is_dependent_type(
                                           expected_type) &&
                                       value.sem.type.valid() &&
                                       !collect_session_.expr_is_dependent(
                                           value.sem)) {
                                expected_type = value.sem.type;
                            }
                            cir::TypeId resolved_expected =
                                collect_session_.file().resolved_type(
                                    expected_type);
                            bool is_class_value =
                                is_class_template_placeholder ||
                                (collect_session_.file().valid(
                                     resolved_expected) &&
                                 collect_session_.file()
                                         .type(resolved_expected)
                                         .kind == cir::TypeKind::Record);
                            if (is_class_value) {
                                std::string value_error;
                                if (!collect_session_
                                         .form_class_template_value_argument(
                                    expected_type,
                                    std::move(value.sem),
                                    default_argument,
                                    parameter.loc,
                                    "default template argument is not a constant expression",
                                    &value_error)) {
                                    if (!value_error.empty()) {
                                        diagnose(DiagnosticLevel::Error,
                                                 value_error,
                                                 parameter.loc);
                                    }
                                    header_error = true;
                                    break;
                                }
                            } else {
                                collect::Session::TemplateValueConstant
                                    constant;
                                if (!collect_session_
                                         .evaluate_template_value_constant(
                                             std::move(value.sem),
                                             expected_type,
                                             constant,
                                             parameter.loc,
                                             "default template argument is not a constant expression")) {
                                    header_error = true;
                                    break;
                                }
                                std::string value_error;
                                if (!collect_session_
                                         .build_template_value_argument(
                                             expected_type,
                                             constant,
                                             default_argument,
                                             &value_error)) {
                                    diagnose(DiagnosticLevel::Error,
                                             value_error,
                                             parameter.loc);
                                    header_error = true;
                                    break;
                                }
                            }
                        }
                    }
                    if (parameter.kind ==
                            collect::Session::TemplateParameterKind::NonType &&
                        parameter.non_type_type.valid() &&
                        collect_session_.is_dependent_type(
                            parameter.non_type_type) &&
                        collect_session_.class_template_placeholder_info(
                            parameter.non_type_type) == nullptr) {
                        default_argument.is_dependent = true;
                    }
                    default_argument.is_defaulted = true;
                    parameter.default_argument =
                        std::move(default_argument);
                    }
                }
                collect_session_.declare_template_parameter_binding(
                    info,
                    parameter,
                    template_loc);
                if (type_constraint.has_value()) {
                    size_t diagnostic_watermark = diagnostics_.size();
                    size_t error_watermark =
                        collect_session_.file().errors().size();
                    std::optional<collect::Session::NormalizedConstraint>
                        normal_form =
                            build_type_constraint_normal_form(info,
                                                              parameter,
                                                              *type_constraint);
                    if (!normal_form.has_value() &&
                        (diagnostics_.size() != diagnostic_watermark ||
                         collect_session_.file().errors().size() !=
                             error_watermark)) {
                        header_error = true;
                        break;
                    }
                    collect::Session::TemplateInfo::IntroducedConstraint
                        constraint{
                            collect::Session::TemplateInfo::
                                IntroducedConstraintKind::
                                    TemplateParameterTypeConstraint,
                            0,
                            0,
                            parameter.index,
                            type_constraint->concept_info->entity,
                            std::move(type_constraint->arguments),
                            type_constraint->loc};
                    constraint.normal_form = std::move(normal_form);
                    info.introduced_constraints.push_back(
                        std::move(constraint));
                }
                info.parameters.push_back(std::move(parameter));
            } while (match(TokenType::COMMA));
        }
        bool closed_template_head = match(TokenType::GREATER_THAN);
        if (!closed_template_head &&
            check(TokenType::RIGHT_SHIFT) &&
            pending_template_closes_ > 0) {

            --pending_template_closes_;
            consume();
            closed_template_head = true;
        }
        if (!closed_template_head) {
            pending_template_closes_ = 0;
            diagnose(DiagnosticLevel::Error,
                     "expected '>' after template parameters",
                     current_loc());
            header_error = true;
        }
        if (!header_error && parameter_depth > 0) {
            for (size_t i = 0; i + 1 < info.parameters.size(); ++i) {
                if (!info.parameters[i].is_parameter_pack) {
                    continue;
                }
                diagnose(
                    DiagnosticLevel::Error,
                    "template parameter pack must be the last template parameter",
                    info.parameters[i].loc);
                header_error = true;
                break;
            }
        }
        if (!header_error && match(TokenType::REQUIRES_KW)) {
            SrcLoc requires_loc = last_consumed_loc();
            size_t constraint_begin = 0;
            size_t constraint_end = 0;
            collect::Session::NormalizedConstraint normal_form;
            size_t saved_constraint_replay_end =
                constraint_expression_replay_end_;
            if (lambda_template_head) {

                auto starts_lambda_suffix = [](TokenType type) {
                    return type == TokenType::MUTABLE_KW ||
                        type == TokenType::STATIC ||
                        type == TokenType::CONSTEXPR_KW ||
                        type == TokenType::CONSTEVAL_KW ||
                        type == TokenType::NOEXCEPT_KW ||
                        type == TokenType::ARROW ||
                        type == TokenType::REQUIRES_KW ||
                        type == TokenType::LEFT_BRACE;
                };
                for (size_t candidate = cursor_;
                     candidate < cooked_to_raw_.size();
                     ++candidate) {
                    if (tokens_[cooked_to_raw_[candidate]].type !=
                        TokenType::LEFT_PAREN) {
                        continue;
                    }
                    TokenType previous = candidate == 0
                        ? TokenType::Eof
                        : tokens_[cooked_to_raw_[candidate - 1]].type;
                    if (previous == TokenType::REQUIRES_KW) {
                        continue;
                    }
                    size_t depth = 1;
                    size_t close = candidate + 1;
                    for (; close < cooked_to_raw_.size(); ++close) {
                        TokenType type = tokens_[cooked_to_raw_[close]].type;
                        if (type == TokenType::LEFT_PAREN) {
                            ++depth;
                        } else if (type == TokenType::RIGHT_PAREN &&
                                   --depth == 0) {
                            break;
                        }
                    }
                    if (depth != 0 || close + 1 >= cooked_to_raw_.size()) {
                        continue;
                    }
                    TokenType next = tokens_[cooked_to_raw_[close + 1]].type;
                    if (!starts_lambda_suffix(next)) {
                        continue;
                    }
                    constraint_expression_replay_end_ =
                        cooked_to_raw_[candidate];
                    break;
                }
            }
            bool was_in_template_definition =
                collect_session_.in_template_definition();
            collect_session_.set_in_template_definition(true);
            if (!lambda_template_head) {
                ++template_head_constraint_attribute_boundary_depth_;
            }

            collect::Session::ActiveTemplateHeaderScope header_scope(
                collect_session_, info);
            bool valid = parse_and_validate_constraint_expression(
                requires_loc,
                constraint_begin,
                constraint_end,
                nullptr,
                &normal_form);
            if (!lambda_template_head) {
                --template_head_constraint_attribute_boundary_depth_;
            }
            collect_session_.set_in_template_definition(
                was_in_template_definition);
            constraint_expression_replay_end_ =
                saved_constraint_replay_end;
            if (!valid) {
                header_error = true;
            } else {
                collect::Session::TemplateInfo::IntroducedConstraint
                    constraint{
                        collect::Session::TemplateInfo::
                            IntroducedConstraintKind::TemplateHeadRequires,
                        constraint_begin,
                        constraint_end};
                stamp_constraint_declaration_keys(normal_form,
                                                  info.parameters);
                constraint.normal_form = std::move(normal_form);
                info.introduced_constraints.push_back(std::move(constraint));
            }
        }
    } else {
        diagnose(DiagnosticLevel::Error, "expected template parameter list",
                 template_loc);
        header_error = true;
    }
    if (parameter_scope_active) {
        collect_session_.finish_template_parameter_scope(
            std::move(parameter_scope));
    }
    info.complete_class_head_end = current_raw_index();
    return !header_error;
}

std::optional<Parser::ParsedDecl>
Parser::try_parse_cxx_deduction_guide_declaration(
    const collect::Session::TemplateInfo* guide_template_info,
    SrcLoc template_loc,
    std::optional<size_t> declaration_begin) {
    if (!lang_opts_.is_cxx_mode()) {
        return std::nullopt;
    }
    size_t guide_offset = is_attribute_start()
        ? skip_attribute_specifier_sequence_offset(0)
        : 0;
    if (peek(guide_offset).type != TokenType::EXPLICIT_KW &&
        !is_identifier_token(peek(guide_offset).type)) {
        return std::nullopt;
    }

    size_t begin = declaration_begin.value_or(current_raw_index());
    TentativeParsingAction tentative(*this, TentativeMode::CollectBacked);
    std::optional<collect::Session::InstantiationScope> guide_template_scope;
    collect::Session::TemplateInfo scoped_guide_info;
    if (guide_template_info) {
        scoped_guide_info = *guide_template_info;
        guide_template_scope.emplace(
            collect_session_.begin_template_header(scoped_guide_info,
                                                   template_loc));
    }
    auto finish_guide_template_scope = [&]() {
        if (guide_template_scope.has_value()) {
            collect_session_.finish_template_header(
                std::move(*guide_template_scope));
            guide_template_scope.reset();
        }
    };

    (void)try_parse_standard_or_gnu_attributes();
    ParsedExplicitSpecifier explicit_specifier = parse_explicit_specifier();
    bool guide_is_explicit = explicit_specifier.effective_value();
    bool explicit_specifier_error = explicit_specifier.has_error;

    if (!is_identifier_token(current().type) ||
        peek(1).type != TokenType::LEFT_PAREN) {
        finish_guide_template_scope();
        return std::nullopt;
    }

    const collect::Session::TemplateInfo* primary =
        collect_session_.template_info_for_name(current().value);
    if (!primary || !primary->is_class_template ||
        primary->is_partial_specialization) {
        finish_guide_template_scope();
        return std::nullopt;
    }

    auto guide_has_requires_clause = [&]() {
        size_t offset = 0;
        int paren_depth = 0;
        int bracket_depth = 0;
        int brace_depth = 0;
        int angle_depth = 0;
        while (!at_end()) {
            TokenType type = peek(offset).type;
            if (type == TokenType::Eof ||
                (type == TokenType::SEMICOLON && paren_depth == 0 &&
                 bracket_depth == 0 && brace_depth == 0 && angle_depth == 0)) {
                return false;
            }
            if (type == TokenType::REQUIRES_KW && paren_depth == 0 &&
                bracket_depth == 0 && brace_depth == 0 && angle_depth == 0) {
                return true;
            }
            switch (type) {
                case TokenType::LEFT_PAREN: ++paren_depth; break;
                case TokenType::RIGHT_PAREN:
                    if (paren_depth > 0) --paren_depth;
                    break;
                case TokenType::LEFT_BRACKET: ++bracket_depth; break;
                case TokenType::RIGHT_BRACKET:
                    if (bracket_depth > 0) --bracket_depth;
                    break;
                case TokenType::LEFT_BRACE: ++brace_depth; break;
                case TokenType::RIGHT_BRACE:
                    if (brace_depth > 0) --brace_depth;
                    break;
                case TokenType::LESS_THAN: ++angle_depth; break;
                case TokenType::GREATER_THAN:
                    if (angle_depth > 0) --angle_depth;
                    break;
                case TokenType::RIGHT_SHIFT:
                    if (angle_depth > 1) {
                        angle_depth -= 2;
                    } else {
                        angle_depth = 0;
                    }
                    break;
                default:
                    break;
            }
            ++offset;
        }
        return false;
    };
    bool has_requires_clause = guide_has_requires_clause();

    Token guide_name = current();
    DeclarationParser guide_parser(*this);
    cir::TypeRef synthetic_auto =
        collect_session_.type_ref(
            collect_session_.auto_type(cir::AutoTypeFlavor::Cxx));
    ParsedDeclarator declarator =
        guide_parser.parse_declarator(synthetic_auto, false);

    bool candidate =
        declarator.has_name &&
        declarator.name == primary->name &&
        declarator.is_function &&
        declarator.has_trailing_return_type &&
        check(TokenType::SEMICOLON);
    if (!candidate) {
        finish_guide_template_scope();
        return std::nullopt;
    }

    finish_guide_template_scope();
    tentative.commit();

    collect::DeclResult decl;
    decl.type = declarator.type;
    bool has_error =
        declarator.has_unsupported_semantics || explicit_specifier_error;
    if (has_requires_clause && !lang_opts_.is_cxx26_or_later()) {
        diagnose(DiagnosticLevel::Error,
                 "a trailing requires-clause on a deduction guide requires C++26",
                 guide_name.loc);
        has_error = true;
    }

    const cir::File& file = collect_session_.file();
    cir::TypeId guide_type = file.resolved_type(declarator.type);
    const auto* function =
        file.valid(guide_type)
            ? std::get_if<cir::FunctionTypePayload>(
                  &file.type_payload(guide_type))
            : nullptr;
    if (!function) {
        diagnose(DiagnosticLevel::Error,
                 "deduction guide must have a function type",
                 guide_name.loc);
        has_error = true;
    }

    std::vector<collect::Session::TemplateArgument> return_arguments;
    if (function) {
        cir::TypeId return_type =
            file.resolved_type(function->return_type.type);
        cir::EntityId return_entity =
            file.valid(return_type) ? file.record_entity(return_type)
                                    : cir::EntityId{};
        const cir::TemplateSpecializationFact* specialization =
            return_entity.valid() ? file.template_specialization(return_entity)
                                  : nullptr;
        if (!specialization ||
            specialization->template_entity != primary->entity) {
            diagnose(DiagnosticLevel::Error,
                     "deduction guide return type must name the same class template",
                     guide_name.loc);
            has_error = true;
        } else {
            return_arguments = specialization->template_arguments();
        }
        if (declarator.abbreviated_template_info.has_value()) {
            diagnose(DiagnosticLevel::Error,
                     "deduction guide parameters cannot use auto",
                     guide_name.loc);
            has_error = true;
        }
        for (const cir::TypeRef& parameter : function->parameters) {
            if (collect_session_.contains_auto_type(parameter.type,
                                                    cir::AutoTypeFlavor::Cxx)) {
                diagnose(DiagnosticLevel::Error,
                         "deduction guide parameters cannot use auto",
                         guide_name.loc);
                has_error = true;
                break;
            }
        }
    }

    cir::DeclContextId current_context =
        collect_session_.current_decl_context();
    if (primary->lexical_context.valid() &&
        primary->lexical_context != current_context) {
        diagnose(DiagnosticLevel::Error,
                 "deduction guide must be declared in the same scope as the class template",
                 guide_name.loc);
        has_error = true;
    }
    if (function && !has_error) {
        cir::TypeRef void_type =
            collect_session_.type_ref(
                collect_session_.file().builtin_type(
                    cir::BuiltinTypeKind::Void));
        cir::TypeId pattern_type =
            collect_session_.function_type(void_type,
                                           function->parameters,
                                           function->is_variadic,
                                           function->has_prototype,
                                           false,
                                           {},
                                           function->parameter_pack_flags);
        collect::Session::TemplateInfo::DeductionGuide guide;
        guide.pattern_type = pattern_type;
        guide.parameter_default_argument_flags.reserve(
            declarator.params.size());
        for (const ParsedParam& parameter : declarator.params) {
            guide.parameter_default_argument_flags.push_back(
                parameter.has_default_argument ? 1 : 0);
        }
        if (guide_template_info) {
            guide.parameters = guide_template_info->parameters;
            guide.introduced_constraints =
                guide_template_info->introduced_constraints;
        }
        if (!has_error) {
            if (declarator.has_trailing_requires_clause) {
                collect::Session::TemplateInfo constraint_owner;
                constraint_owner.parameters = guide.parameters;
                constraint_owner.introduced_constraints =
                    std::move(guide.introduced_constraints);
                record_trailing_function_requires_clause(constraint_owner,
                                                         declarator);
                guide.introduced_constraints =
                    std::move(constraint_owner.introduced_constraints);
            }
            guide.return_arguments = std::move(return_arguments);
            guide.loc = guide_name.loc;
            guide.declaration_context = current_context;
            guide.declaration_generation =
                collect_session_.lookup_generation();
            guide.declared_member_access =
                collect_session_.current_record_member_access();
            if (guide.declared_member_access.has_value() &&
                primary->entity.valid() && file.valid(primary->entity) &&
                file.entity(primary->entity).is_record_member &&
                file.entity(primary->entity).declared_member_access !=
                    *guide.declared_member_access) {
                diagnose(DiagnosticLevel::Error,
                         "deduction guide must have the same access as the class template",
                         guide_name.loc);
                has_error = true;
            }
        }
        guide.is_explicit = guide_is_explicit;
        guide.explicit_specifier = explicit_specifier.kind;
        guide.explicit_expression_begin =
            explicit_specifier.expression_begin;
        guide.explicit_expression_end = explicit_specifier.expression_end;
        guide.explicit_value_expression =
            explicit_specifier.value_expression;
        guide.explicit_declaration_context =
            explicit_specifier.declaration_context;
        guide.explicit_lookup_generation =
            explicit_specifier.lookup_generation;
        if (!has_error &&
            !collect_session_.add_deduction_guide(primary->entity,
                                                  std::move(guide),
                                                  guide_name.loc)) {
            has_error = true;
        }
    }

    if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ';' after deduction guide",
                 current_loc());
        skip_until_statement_boundary();
        has_error = true;
    }
    decl.has_error = has_error;
    return ParsedDecl{
        make_node(has_error ? NodeKind::UnknownDecl : NodeKind::FunctionDecl,
                  begin,
                  last_consumed_raw_end(),
                  {},
                  text_payload("deduction guide"),
                  has_error ? NodeFlagHasError : NodeFlagNone),
        std::move(decl)};
}

void Parser::retain_static_data_member_initializer_tokens(
    collect::Session::TemplateInfo& info,
    size_t definition_begin,
    size_t definition_end) {
    size_t body_begin = definition_begin;
    while (body_begin < definition_end &&
           body_begin < tokens_.size() &&
           tokens_[body_begin].type != TokenType::LEFT_BRACE) {
        ++body_begin;
    }
    if (body_begin >= definition_end || body_begin >= tokens_.size()) {
        return;
    }

    int braces = 1;
    int parens = 0;
    int brackets = 0;
    bool saw_static = false;
    size_t candidate_name = tokens_.size();
    auto less_than_has_matching_close =
        [&](size_t less_than) {
        int angle_depth = 1;
        int group_depth = 0;
        for (size_t look = less_than + 1;
             look < definition_end && look < tokens_.size();
             ++look) {
            TokenType look_type = tokens_[look].type;
            if (group_depth == 0 &&
                look_type == TokenType::SEMICOLON) {
                return false;
            }
            if (look_type == TokenType::LEFT_PAREN ||
                look_type == TokenType::LEFT_BRACKET ||
                look_type == TokenType::LEFT_BRACE) {
                ++group_depth;
                continue;
            }
            if (look_type == TokenType::RIGHT_PAREN ||
                look_type == TokenType::RIGHT_BRACKET ||
                look_type == TokenType::RIGHT_BRACE) {
                if (group_depth > 0) {
                    --group_depth;
                    continue;
                }
                return false;
            }
            if (group_depth != 0) {
                continue;
            }
            if (look_type == TokenType::LESS_THAN) {
                ++angle_depth;
            } else if (look_type == TokenType::GREATER_THAN) {
                if (--angle_depth == 0) {
                    return true;
                }
            } else if (look_type == TokenType::RIGHT_SHIFT) {
                angle_depth -= 2;
                if (angle_depth <= 0) {
                    return true;
                }
            }
        }
        return false;
    };
    for (size_t index = body_begin + 1;
         index < definition_end && index < tokens_.size();
         ++index) {
        TokenType type = tokens_[index].type;
        bool direct_member_level =
            braces == 1 && parens == 0 && brackets == 0;
        if (direct_member_level && type == TokenType::SEMICOLON) {
            saw_static = false;
            candidate_name = tokens_.size();
            continue;
        }
        if (direct_member_level && type == TokenType::COMMA &&
            saw_static) {
            candidate_name = tokens_.size();
            continue;
        }
        if (direct_member_level && type == TokenType::STATIC) {
            saw_static = true;
            candidate_name = tokens_.size();
            continue;
        }
        if (direct_member_level && saw_static &&
            is_identifier_token(type)) {
            candidate_name = index;
            continue;
        }
        if (direct_member_level && saw_static &&
            candidate_name < tokens_.size() &&
            type == TokenType::ASSIGN) {
            int initializer_parens = 0;
            int initializer_brackets = 0;
            int initializer_braces = 0;
            int initializer_angles = 0;
            size_t end = index + 1;
            for (; end < definition_end && end < tokens_.size(); ++end) {
                TokenType current = tokens_[end].type;
                if (current == TokenType::LEFT_PAREN) ++initializer_parens;
                if (current == TokenType::RIGHT_PAREN) --initializer_parens;
                if (current == TokenType::LEFT_BRACKET) ++initializer_brackets;
                if (current == TokenType::RIGHT_BRACKET) --initializer_brackets;
                if (current == TokenType::LEFT_BRACE) ++initializer_braces;
                if (current == TokenType::RIGHT_BRACE &&
                    initializer_braces > 0) {
                    --initializer_braces;
                }
                bool grouped = initializer_parens > 0 ||
                    initializer_brackets > 0 ||
                    initializer_braces > 0;
                if (!grouped &&
                    current == TokenType::LESS_THAN &&
                    less_than_has_matching_close(end)) {
                    ++initializer_angles;
                } else if (!grouped &&
                           current == TokenType::GREATER_THAN &&
                           initializer_angles > 0) {
                    --initializer_angles;
                } else if (!grouped &&
                           current == TokenType::RIGHT_SHIFT &&
                           initializer_angles > 0) {
                    initializer_angles =
                        std::max(0, initializer_angles - 2);
                }
                if (initializer_parens == 0 &&
                    initializer_brackets == 0 &&
                    initializer_braces == 0 &&
                    ((current == TokenType::COMMA &&
                      initializer_angles == 0) ||
                     current == TokenType::SEMICOLON)) {
                    break;
                }
            }
            if (end < definition_end && end < tokens_.size()) {
                collect::Session::TemplateInfo::
                    StaticDataMemberInitializer initializer;
                initializer.name =
                    std::string(tokens_[candidate_name].value);
                initializer.begin = index;
                initializer.end = end;
                initializer.loc = tokens_[candidate_name].loc;
                initializer.declaration_context = info.lexical_context;
                initializer.lookup_generation =
                    collect_session_.lookup_generation();
                bool duplicate = std::any_of(
                    info.static_data_member_initializers.begin(),
                    info.static_data_member_initializers.end(),
                    [&](const auto& existing) {
                        return existing.name == initializer.name &&
                            existing.begin == initializer.begin;
                    });
                if (!duplicate) {
                    info.static_data_member_initializers.push_back(
                        std::move(initializer));
                }

                index = end - 1;
                continue;
            }
        }

        if (type == TokenType::LEFT_PAREN) ++parens;
        if (type == TokenType::RIGHT_PAREN && parens > 0) --parens;
        if (type == TokenType::LEFT_BRACKET) ++brackets;
        if (type == TokenType::RIGHT_BRACKET && brackets > 0) --brackets;
        if (type == TokenType::LEFT_BRACE) ++braces;
        if (type == TokenType::RIGHT_BRACE) {
            --braces;
            if (braces == 0) {
                break;
            }
        }
    }
}

std::optional<Parser::ParsedDecl>
Parser::try_parse_class_template_partial_specialization(
    collect::Session::TemplateInfo& info,
    size_t begin,
    SrcLoc template_loc) {
    if (!(check(TokenType::STRUCT) || check(TokenType::CLASS) ||
          check(TokenType::UNION))) {
        return std::nullopt;
    }

    const size_t class_head_name_offset =
        skip_attribute_specifier_sequence_offset(1);
    bool has_template_id_qualifier = false;
    for (size_t offset = class_head_name_offset; offset < 256; ++offset) {
        TokenType type = peek(offset).type;
        if (type == TokenType::Eof || type == TokenType::LEFT_BRACE ||
            type == TokenType::SEMICOLON) {
            break;
        }
        if (is_identifier_token(type) &&
            peek(offset + 1).type == TokenType::LESS_THAN) {
            if (template_id_precedes_scope(offset)) {
                has_template_id_qualifier = true;
            }
            break;
        }
    }
    if (has_template_id_qualifier) {
        RevertingTentativeParsingAction tentative(
            *this,
            TentativeMode::CollectBacked);
        size_t class_begin = current_raw_index();
        Token class_key = current();
        cir::RecordKind record_kind = class_key_record_kind(current().type);
        consume();
        for (size_t offset = 1; offset < class_head_name_offset; ++offset) {
            consume();
        }

        bool has_error = false;
        Token name_token;
        const collect::Session::TemplateInfo* primary = nullptr;
        std::vector<collect::Session::TemplateArgument> arguments;
        collect::Session::InstantiationScope header_scope =
            collect_session_.begin_template_header(info, template_loc);
        ParsedNestedName nested = parse_nested_name_specifier();
        if (!nested.consumed_any || nested.has_error ||
            !nested.scope.context.valid() ||
            !is_identifier_token(current().type) ||
            peek(1).type != TokenType::LESS_THAN ||
            template_id_precedes_scope(0)) {
            collect_session_.finish_template_header(std::move(header_scope));
            return std::nullopt;
        }
        tentative.commit();
        name_token = current();
        primary = collect_session_.template_info_in_context(
            nested.scope.context,
            name_token.value,
            /*include_parents=*/false);
        consume();
        if (!primary || !primary->is_class_template) {
            diagnose(DiagnosticLevel::Error,
                     "class template partial specialization requires a prior class template primary",
                     name_token.loc);
            has_error = true;
            (void)parse_dependent_expression_template_argument_list(
                name_token.loc);
        } else {
            TemplateArgumentAccessExemptionScope access_exemption(
                collect_session_);
            if (!parse_template_argument_list_with_request(*primary,
                                                           arguments,
                                                           name_token.loc) ||
                !canonicalize_template_arguments(*primary,
                                                 arguments,
                                                 name_token.loc)) {
                has_error = true;
            }
        }
        collect_session_.finish_template_header(std::move(header_scope));

        if (primary &&
            !class_template_keys_agree(record_kind, primary->record_kind)) {
            diagnose(DiagnosticLevel::Error,
                     "class-key does not agree with the original class template",
                     class_key.loc);
            has_error = true;
        }
        for (collect::Session::TemplateParameter& parameter : info.parameters) {
            if (!parameter.default_argument.has_value()) {
                continue;
            }
            diagnose(DiagnosticLevel::Error,
                     "default template arguments are not allowed in class template partial specializations",
                     parameter.loc.isInvalid() ? template_loc : parameter.loc);
            parameter.default_argument.reset();
            has_error = true;
        }

        bool has_definition = false;
        size_t definition_end = current_raw_index();
        if (match(TokenType::SEMICOLON)) {
            definition_end = current_raw_index();
        } else {
            has_definition = true;
            definition_end = skip_balanced_until_semicolon_or_brace();
            match(TokenType::SEMICOLON);
        }
        info.is_class_template = true;
        info.is_partial_specialization = true;
        info.record_kind = record_kind;
        info.name = primary ? primary->name : std::string(name_token.value);
        info.definition_begin = class_begin;
        info.definition_end = definition_end;
        info.has_definition = has_definition;
        if (!has_error && primary && has_definition) {
            retain_static_data_member_initializer_tokens(
                info, class_begin, definition_end);
            validate_template_definition(info, class_key.loc);
        }
        if (!has_error && primary) {
            collect_session_.register_template_partial_specialization(
                *primary,
                std::move(info),
                std::move(arguments),
                class_key.loc);
        }
        collect::DeclResult decl;
        decl.has_error = has_error;
        return ParsedDecl{make_node(has_error ? NodeKind::UnknownDecl
                                              : NodeKind::RecordDecl,
                                    begin,
                                    last_consumed_raw_end(),
                                    {},
                                    text_payload("template"),
                                    has_error ? NodeFlagHasError
                                              : NodeFlagNone),
                          std::move(decl)};
    }

    size_t terminal_offset = class_head_name_offset;
    bool global_qualifier = false;
    if (peek(terminal_offset).type == TokenType::SCOPE_RESOLUTION) {
        global_qualifier = true;
        ++terminal_offset;
    }
    std::vector<std::string_view> qualifiers;
    while (is_identifier_token(peek(terminal_offset).type) &&
           peek(terminal_offset + 1).type == TokenType::SCOPE_RESOLUTION &&
           peek(terminal_offset + 2).type != TokenType::MULTIPLY) {
        qualifiers.push_back(peek(terminal_offset).value);
        terminal_offset += 2;
    }
    if (!is_identifier_token(peek(terminal_offset).type) ||
        peek(terminal_offset + 1).type != TokenType::LESS_THAN) {
        return std::nullopt;
    }
    if (template_id_precedes_scope(terminal_offset)) {
        return std::nullopt;
    }

    size_t class_begin = current_raw_index();
    Token class_key = current();
    cir::RecordKind record_kind = class_key_record_kind(current().type);
    Token name_token = peek(terminal_offset);
    std::string primary_name = std::string(name_token.value);
    const collect::Session::TemplateInfo* primary =
        qualifiers.empty() && !global_qualifier
            ? collect_session_.template_info_for_name(primary_name)
            : collect_session_.peek_qualified_template_info(
                  global_qualifier,
                  qualifiers,
                  primary_name);
    if (!primary || !primary->is_class_template) {
        diagnose(DiagnosticLevel::Error,
                 "class template partial specialization requires a prior class template primary",
                 name_token.loc);
        skip_balanced_until_semicolon_or_brace();
        match(TokenType::SEMICOLON);
        collect::DeclResult decl;
        decl.has_error = true;
        return ParsedDecl{make_node(NodeKind::UnknownDecl,
                                    begin,
                                    last_consumed_raw_end(),
                                    {},
                                    text_payload("template"),
                                    NodeFlagHasError),
                          std::move(decl)};
    }

    consume();
    for (size_t offset = 1; offset < class_head_name_offset; ++offset) {
        consume();
    }
    if (global_qualifier) {
        consume();
    }
    for (size_t i = 0; i < qualifiers.size(); ++i) {
        consume();
        consume();
    }
    consume();

    bool has_error = false;
    if (!class_template_keys_agree(record_kind, primary->record_kind)) {
        diagnose(DiagnosticLevel::Error,
                 "class-key does not agree with the original class template",
                 class_key.loc);
        has_error = true;
    }
    for (collect::Session::TemplateParameter& parameter : info.parameters) {
        if (!parameter.default_argument.has_value()) {
            continue;
        }
        diagnose(DiagnosticLevel::Error,
                 "default template arguments are not allowed in class template partial specializations",
                 parameter.loc.isInvalid() ? template_loc : parameter.loc);
        parameter.default_argument.reset();
        has_error = true;
    }

    std::vector<collect::Session::TemplateArgument> arguments;
    {
        collect::Session::InstantiationScope header_scope =
            collect_session_.begin_template_header(info, template_loc);
        TemplateArgumentAccessExemptionScope access_exemption(
            collect_session_);
        if (!parse_template_argument_list_with_request(*primary,
                                                       arguments,
                                                       name_token.loc) ||
            !canonicalize_template_arguments(*primary,
                                             arguments,
                                             name_token.loc)) {
            has_error = true;
        }
        collect_session_.finish_template_header(std::move(header_scope));
    }

    bool has_definition = false;
    size_t definition_end = current_raw_index();
    if (match(TokenType::SEMICOLON)) {
        definition_end = current_raw_index();
    } else {
        has_definition = true;
        definition_end = skip_balanced_until_semicolon_or_brace();
        match(TokenType::SEMICOLON);
    }

    info.is_class_template = true;
    info.is_partial_specialization = true;
    info.record_kind = record_kind;
    info.name = primary->name;
    info.definition_begin = class_begin;
    info.definition_end = definition_end;
    info.has_definition = has_definition;

    if (!has_error && has_definition) {
        retain_static_data_member_initializer_tokens(
            info, class_begin, definition_end);
        validate_template_definition(info, class_key.loc);
    }
    if (!has_error) {
        collect_session_.register_template_partial_specialization(
            *primary,
            std::move(info),
            std::move(arguments),
            class_key.loc);
    }

    collect::DeclResult decl;
    decl.has_error = has_error;
    return ParsedDecl{make_node(has_error ? NodeKind::UnknownDecl
                                          : NodeKind::RecordDecl,
                                begin,
                                last_consumed_raw_end(),
                                {},
                                text_payload("template"),
                                has_error ? NodeFlagHasError
                                          : NodeFlagNone),
                      std::move(decl)};
}

std::optional<Parser::ParsedDecl>
Parser::try_parse_explicit_class_template_specialization(
    size_t begin,
    SrcLoc template_loc) {
    if (!(check(TokenType::STRUCT) || check(TokenType::CLASS) ||
          check(TokenType::UNION))) {
        return std::nullopt;
    }

    Token class_key = current();
    cir::RecordKind record_kind = class_key_record_kind(class_key.type);
    const collect::Session::TemplateInfo* primary = nullptr;
    std::string primary_name;
    const size_t class_head_name_offset =
        skip_attribute_specifier_sequence_offset(1);
    bool has_template_id_qualifier = false;
    for (size_t offset = class_head_name_offset; offset < 256; ++offset) {
        TokenType type = peek(offset).type;
        if (type == TokenType::Eof || type == TokenType::LEFT_BRACE ||
            type == TokenType::SEMICOLON) {
            break;
        }
        if (is_identifier_token(type) &&
            peek(offset + 1).type == TokenType::LESS_THAN) {
            if (template_id_precedes_scope(offset)) {
                has_template_id_qualifier = true;
            }
            break;
        }
    }
    if (has_template_id_qualifier) {
        size_t saved_cursor = cursor_;
        size_t saved_last_end = last_consumed_raw_end_;
        consume();
        for (size_t offset = 1; offset < class_head_name_offset; ++offset) {
            consume();
        }
        ParsedNestedName nested = parse_nested_name_specifier();
        bool candidate = nested.consumed_any && !nested.has_error &&
                         nested.scope.context.valid() &&
                         is_identifier_token(current().type) &&
                         peek(1).type == TokenType::LESS_THAN &&
                         !template_id_precedes_scope(0);
        if (candidate) {
            primary_name = current().value;
            primary = collect_session_.template_info_in_context(
                nested.scope.context,
                primary_name,
                /*include_parents=*/false);
        }
        cursor_ = saved_cursor;
        last_consumed_raw_end_ = saved_last_end;
        if (!candidate) {
            return std::nullopt;
        }
    }

    size_t terminal_offset = class_head_name_offset;
    bool global_qualifier = false;
    std::vector<std::string_view> qualifiers;
    if (!has_template_id_qualifier) {
        if (peek(terminal_offset).type == TokenType::SCOPE_RESOLUTION) {
            global_qualifier = true;
            ++terminal_offset;
        }
        while (is_identifier_token(peek(terminal_offset).type) &&
               peek(terminal_offset + 1).type ==
                   TokenType::SCOPE_RESOLUTION &&
               peek(terminal_offset + 2).type != TokenType::MULTIPLY) {
            qualifiers.push_back(peek(terminal_offset).value);
            terminal_offset += 2;
        }
        if (!is_identifier_token(peek(terminal_offset).type) ||
            peek(terminal_offset + 1).type != TokenType::LESS_THAN) {
            return std::nullopt;
        }
        primary_name = std::string(peek(terminal_offset).value);
        primary = qualifiers.empty() && !global_qualifier
            ? collect_session_.template_info_for_name(primary_name)
            : collect_session_.peek_qualified_template_info(
                  global_qualifier,
                  qualifiers,
                  primary_name);
    }
    if (!primary || !primary->is_class_template) {
        diagnose(DiagnosticLevel::Error,
                 "no matching class template for explicit specialization",
                 has_template_id_qualifier ? class_key.loc
                                           : peek(terminal_offset).loc);
        skip_balanced_until_semicolon_or_brace();
        match(TokenType::SEMICOLON);
        collect::DeclResult decl;
        decl.has_error = true;
        return {ParsedDecl{make_node(NodeKind::UnknownDecl,
                                     begin,
                                     last_consumed_raw_end(),
                                     {},
                                     text_payload("template"),
                                     NodeFlagHasError),
                           std::move(decl)}};
    }

    bool class_key_error = false;
    if (!class_template_keys_agree(record_kind, primary->record_kind)) {
        diagnose(DiagnosticLevel::Error,
                 "class-key does not agree with the original class template",
                 class_key.loc);
        class_key_error = true;
    }

    ExplicitClassTemplateSpecializationParse specialization_parse;
    specialization_parse.template_entity = primary->entity;
    struct ExplicitClassTemplateSpecializationParseExit {
        Parser& parser;
        ExplicitClassTemplateSpecializationParse* previous = nullptr;

        ~ExplicitClassTemplateSpecializationParseExit() {
            parser.explicit_class_template_specialization_parse_ = previous;
        }
    } specialization_parse_exit{
        *this,
        explicit_class_template_specialization_parse_};
    explicit_class_template_specialization_parse_ = &specialization_parse;

    cir::TypeId type{};
    NodeId syntax = parse_record_specifier(&type);
    collect::DeclResult decl;
    decl.type = type;
    decl.has_error = class_key_error || specialization_parse.has_error ||
                     !specialization_parse.matched;

    const cir::File& file = collect_session_.file();
    cir::EntityId specialization;
    if (type.valid()) {
        specialization =
            file.record_entity(file.resolved_type(type));
    }

    if (specialization_parse.matched && specialization.valid()) {
        std::string memo_key =
            collect_session_.template_memo_key(primary->entity,
                                               specialization_parse.arguments);
        cir::EntityId cached =
            collect_session_.cached_instantiation(memo_key);
        bool cached_implicit = false;
        bool cached_definition = false;
        if (cached.valid() && file.valid(cached)) {
            const cir::TemplateSpecializationFact* fact =
                file.template_specialization(cached);
            if (const cir::RecordFacts* facts = file.record_facts(cached)) {
                cached_definition = !facts->is_incomplete;
            }

            cached_implicit =
                cached != specialization && cached_definition && fact &&
                !fact->point_of_instantiation.isInvalid();
        }
        bool specialization_is_definition = false;
        if (const cir::RecordFacts* facts =
                file.record_facts(specialization)) {
            specialization_is_definition = !facts->is_incomplete;
        }

        auto note_implicit_instantiation_point =
            [&](cir::EntityId instantiated) {
                const cir::TemplateSpecializationFact* fact =
                    file.template_specialization(instantiated);
                if (fact &&
                    !fact->point_of_instantiation.isInvalid()) {
                    diagnose(DiagnosticLevel::Note,
                             "implicit instantiation first required here",
                             fact->point_of_instantiation);
                }
            };

        bool duplicate_definition =
            cached.valid() && cached != specialization &&
            cached_definition && specialization_is_definition;
        if (cached_implicit) {
            diagnose(DiagnosticLevel::Error,
                     "explicit specialization of class template after implicit instantiation",
                     template_loc);
            note_implicit_instantiation_point(cached);
            decl.has_error = true;
        } else if (duplicate_definition) {
            diagnose(DiagnosticLevel::Error,
                     "redefinition of explicit class template specialization",
                     template_loc);
            decl.has_error = true;
        }

        if (!cached_implicit && !duplicate_definition) {
            if (!cached.valid()) {
                collect_session_.remember_instantiation(memo_key,
                                                        specialization);
            } else if (cached != specialization) {
                const cir::RecordFacts* previous_facts =
                    file.record_facts(cached);
                if (specialization_is_definition &&
                    previous_facts && previous_facts->is_incomplete) {
                    collect_session_.replace_instantiation(memo_key,
                                                           specialization);
                }
            }
            collect_session_.remember_template_specialization(
                specialization,
                *primary,
                specialization_parse.arguments);
        }
    }

    if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ';' after explicit class template specialization",
                 current_loc());
        skip_until_statement_boundary();
        decl.has_error = true;
    }
    if (specialization.valid() && !decl.has_error) {
        collect_session_.mark_explicit_template_specialization(specialization);
    }

    return {ParsedDecl{make_node(decl.has_error ? NodeKind::UnknownDecl
                                                : NodeKind::RecordDecl,
                                 begin,
                                 last_consumed_raw_end(),
                                 syntax != InvalidNodeId
                                     ? std::vector<NodeId>{syntax}
                                     : std::vector<NodeId>{},
                                 text_payload("template"),
                                 decl.has_error ? NodeFlagHasError
                                                : NodeFlagNone),
                       std::move(decl)}};
}

bool Parser::reject_explicit_specialization_of_member_of_explicit_class(
    const collect::Session::TemplateInfo& owner_info,
    const std::vector<collect::Session::TemplateArgument>& owner_arguments,
    SrcLoc template_loc) {
    cir::EntityId owner;
    if (!collect_session_.explicit_template_specialization_declared(
            owner_info, owner_arguments, &owner)) {
        return false;
    }

    diagnose(
        DiagnosticLevel::Error,
        "extraneous 'template<>' in declaration of a member of an explicitly "
        "specialized class",
        template_loc);
    if (owner.valid() && collect_session_.file().valid(owner)) {
        diagnose(DiagnosticLevel::Note,
                 "explicit class template specialization declared here",
                 collect_session_.file().entity(owner).loc);
    }
    return true;
}

std::optional<Parser::ParsedDecl>
Parser::try_parse_explicit_member_function_specialization(
    size_t begin,
    SrcLoc template_loc) {
    struct DeferTemplateQualifierInstantiation {
        Parser& parser;
        bool previous = false;

        explicit DeferTemplateQualifierInstantiation(Parser& parser)
            : parser(parser),
              previous(parser.defer_class_template_qualifier_instantiation_) {
            parser.defer_class_template_qualifier_instantiation_ = true;
        }

        ~DeferTemplateQualifierInstantiation() {
            parser.defer_class_template_qualifier_instantiation_ = previous;
        }
    };

    bool candidate = false;
    {
        RevertingTentativeParsingAction tentative(*this,
                                                  TentativeMode::CollectBacked);
        DeferTemplateQualifierInstantiation defer(*this);
        DeclarationParser specialization_parser(
            *this,
            TypeParseContext::type_only(
                TypeParseContext::Origin::NamespaceDeclSpecifier));

        defer_class_template_qualifier_instantiation_ = defer.previous;
        cir::TypeRef base =
            specialization_parser.parse_declaration(false, true);
        defer_class_template_qualifier_instantiation_ = true;
        ParsedDeclarator declarator =
            specialization_parser.parse_declarator(base, false);
        candidate = declarator.has_name && declarator.is_function &&
                    declarator.qualified_context.valid() &&
                    declarator.template_qualifier_info &&
                    declarator.template_qualifier_info->is_class_template;
        if (candidate) {
            const cir::File& file = collect_session_.file();
            candidate =
                file.decl_context(declarator.qualified_context).kind ==
                cir::DeclContextKind::Record;
        }
    }
    if (!candidate) {
        return std::nullopt;
    }

    DeferTemplateQualifierInstantiation defer(*this);
    DeclarationParser specialization_parser(
        *this,
        TypeParseContext::type_only(
            TypeParseContext::Origin::NamespaceDeclSpecifier));

    defer_class_template_qualifier_instantiation_ = defer.previous;
    cir::TypeRef base = specialization_parser.parse_declaration(false, true);
    defer_class_template_qualifier_instantiation_ = true;

    collect::DeclFlags flags;
    flags.is_constexpr = specialization_parser.is_constexpr;
    flags.is_consteval = specialization_parser.is_consteval;
    flags.is_constinit = specialization_parser.is_constinit;
    flags.is_inline = specialization_parser.is_inline;
    flags.is_thread_local = specialization_parser.is_thread_local;
    flags.is_extern =
        specialization_parser.storage_class == StorageClass::Extern;
    flags.is_static =
        specialization_parser.storage_class == StorageClass::Static;
    flags.is_auto_storage =
        specialization_parser.storage_class == StorageClass::Auto;
    flags.is_register =
        specialization_parser.storage_class == StorageClass::Register;
    flags.is_mutable = specialization_parser.is_mutable;
    flags.is_friend = specialization_parser.is_friend;
    flags.is_block_byref = specialization_parser.is_block_byref;
    flags.attrs = specialization_parser.leading_attrs;

    std::vector<NodeId> children;
    if (specialization_parser.type_syntax != InvalidNodeId) {
        children.push_back(specialization_parser.type_syntax);
    }

    ParsedDeclarator declarator =
        specialization_parser.parse_declarator(base, false);
    if (declarator.syntax != InvalidNodeId) {
        children.push_back(declarator.syntax);
    }
    ParsedAttributes trailing_attrs = try_parse_attributes();
    declarator.attrs.append(std::move(trailing_attrs.attrs));
    children.insert(children.end(),
                    trailing_attrs.syntax.begin(),
                    trailing_attrs.syntax.end());

    AttributeList merged_attrs = flags.attrs;
    merged_attrs.append(declarator.attrs);
    declarator.attrs = std::move(merged_attrs);
    flags.attrs = declarator.attrs;
    flags.vla_bounds = std::move(declarator.vla_bounds);
    flags.type_qualifiers = declarator.type_ref.qualifiers;

    bool specialization_has_error = false;
    if (specialization_parser.storage_class != StorageClass::None) {
        diagnose(DiagnosticLevel::Error,
                 "explicit specialization cannot use a storage class specifier",
                 specialization_parser.begin_loc);
        specialization_has_error = true;
    }
    if (specialization_parser.is_friend) {
        diagnose(DiagnosticLevel::Error,
                 "explicit specialization declaration shall not be a friend declaration",
                 specialization_parser.begin_loc);
        specialization_has_error = true;
    }
    for (ParsedParam& param : declarator.params) {
        if (!param.has_default_argument) {
            continue;
        }
        diagnose(DiagnosticLevel::Error,
                 "default function argument is not allowed in explicit member function specialization",
                 param.default_argument_loc.isInvalid()
                     ? param.loc
                     : param.default_argument_loc);
        param.has_default_argument = false;
        specialization_has_error = true;
    }

    const collect::Session::TemplateInfo* owner_info =
        declarator.template_qualifier_info;
    defer_class_template_qualifier_instantiation_ = defer.previous;
    if (!owner_info) {
        collect::DeclResult decl;
        decl.has_error = true;
        skip_balanced_until_semicolon_or_brace();
        return ParsedDecl{make_node(NodeKind::UnknownDecl,
                                    begin,
                                    last_consumed_raw_end(),
                                    children,
                                    text_payload("template"),
                                    NodeFlagHasError),
                          std::move(decl)};
    }
    if (reject_explicit_specialization_of_member_of_explicit_class(
            *owner_info,
            declarator.template_qualifier_arguments,
            template_loc)) {
        collect::DeclResult decl;
        decl.has_error = true;
        skip_balanced_until_semicolon_or_brace();
        return ParsedDecl{make_node(NodeKind::UnknownDecl,
                                    begin,
                                    last_consumed_raw_end(),
                                    children,
                                    text_payload("template"),
                                    NodeFlagHasError),
                          std::move(decl)};
    }

    SrcLoc first_required =
        collect_session_
            .register_explicit_member_function_specialization_declaration(
                *owner_info,
                declarator.template_qualifier_arguments,
                declarator.name,
                collect_session_.type_ref(declarator.type),
                declarator.loc);
    if (!first_required.isInvalid()) {
        diagnose(DiagnosticLevel::Error,
                 "explicit specialization of member function after implicit instantiation",
                 template_loc);
        diagnose(DiagnosticLevel::Note,
                 "member function first required here",
                 first_required);
        specialization_has_error = true;
    }

    cir::EntityId owner = instantiate_template_with_args(
        *owner_info,
        declarator.template_qualifier_arguments,
        declarator.template_qualifier_loc.isInvalid()
            ? declarator.loc
            : declarator.template_qualifier_loc);
    if (owner.valid()) {
        const cir::Entity& owner_entity = collect_session_.file().entity(owner);
        declarator.qualified_context = owner_entity.semantic_context;
    } else {
        collect::DeclResult decl;
        decl.has_error = true;
        skip_balanced_until_semicolon_or_brace();
        return ParsedDecl{make_node(NodeKind::UnknownDecl,
                                    begin,
                                    last_consumed_raw_end(),
                                    children,
                                    text_payload("template"),
                                    NodeFlagHasError),
                          std::move(decl)};
    }

    bool has_definition_syntax =
        check(TokenType::LEFT_BRACE) || check(TokenType::COLON);
    FunctionDeclaratorResult result;
    {
        struct ExplicitMemberFunctionSpecializationDeclarationExit {
            Parser& parser;
            bool previous = false;

            ~ExplicitMemberFunctionSpecializationDeclarationExit() {
                parser.explicit_member_function_specialization_declaration_ =
                    previous;
            }
        } declaration_scope{
            *this,
            explicit_member_function_specialization_declaration_};
        explicit_member_function_specialization_declaration_ =
            !has_definition_syntax;
        result = handle_function_declarator(declarator, children, flags);
    }

    result.decl.has_error =
        result.decl.has_error || specialization_has_error;
    if (result.parsed_definition) {
        if (result.decl.entity.valid() && !result.decl.has_error) {
            collect_session_.mark_explicit_template_specialization(
                result.decl.entity);
        }
        return ParsedDecl{make_node(result.decl.has_error
                                        ? NodeKind::UnknownDecl
                                        : NodeKind::FunctionDecl,
                                    begin,
                                    last_consumed_raw_end(),
                                    children,
                                    text_payload("template"),
                                    result.decl.has_error ? NodeFlagHasError
                                                          : NodeFlagNone),
                          std::move(result.decl)};
    }
    if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ';' after explicit member function specialization",
                 current_loc());
        skip_until_statement_boundary();
        result.decl.has_error = true;
    }
    if (result.decl.entity.valid() && !result.decl.has_error) {
        collect_session_.mark_explicit_template_specialization(
            result.decl.entity);
    }
    return ParsedDecl{make_node(result.decl.has_error ? NodeKind::UnknownDecl
                                                      : NodeKind::FunctionDecl,
                                begin,
                                last_consumed_raw_end(),
                                children,
                                text_payload("template"),
                                result.decl.has_error ? NodeFlagHasError
                                                      : NodeFlagNone),
                      std::move(result.decl)};
}

std::optional<Parser::ParsedDecl>
Parser::try_parse_explicit_static_data_member_specialization(
    size_t begin,
    SrcLoc template_loc) {
    struct DeferTemplateQualifierInstantiation {
        Parser& parser;
        bool previous = false;

        explicit DeferTemplateQualifierInstantiation(Parser& parser)
            : parser(parser),
              previous(parser.defer_class_template_qualifier_instantiation_) {
            parser.defer_class_template_qualifier_instantiation_ = true;
        }

        ~DeferTemplateQualifierInstantiation() {
            parser.defer_class_template_qualifier_instantiation_ = previous;
        }
    };

    bool candidate = false;
    {
        RevertingTentativeParsingAction tentative(*this,
                                                  TentativeMode::CollectBacked);
        DeferTemplateQualifierInstantiation defer(*this);
        DeclarationParser specialization_parser(
            *this,
            TypeParseContext::type_only(
                TypeParseContext::Origin::NamespaceDeclSpecifier));

        defer_class_template_qualifier_instantiation_ = defer.previous;
        cir::TypeRef base =
            specialization_parser.parse_declaration(false, true);
        defer_class_template_qualifier_instantiation_ = true;
        ParsedDeclarator declarator =
            specialization_parser.parse_declarator(base, false);
        candidate = declarator.has_name && !declarator.is_function &&
                    declarator.type_ref.valid() &&
                    declarator.qualified_context.valid() &&
                    declarator.template_qualifier_info &&
                    declarator.template_qualifier_info->is_class_template &&
                    !check(TokenType::LESS_THAN);
        if (candidate) {
            const cir::File& file = collect_session_.file();
            candidate =
                file.decl_context(declarator.qualified_context).kind ==
                cir::DeclContextKind::Record;
        }
    }
    if (!candidate) {
        return std::nullopt;
    }

    DeferTemplateQualifierInstantiation defer(*this);
    DeclarationParser specialization_parser(
        *this,
        TypeParseContext::type_only(
            TypeParseContext::Origin::NamespaceDeclSpecifier));

    defer_class_template_qualifier_instantiation_ = defer.previous;
    cir::TypeRef base = specialization_parser.parse_declaration(false, true);
    defer_class_template_qualifier_instantiation_ = true;

    collect::DeclFlags flags;
    flags.is_constexpr = specialization_parser.is_constexpr;
    flags.is_consteval = specialization_parser.is_consteval;
    flags.is_constinit = specialization_parser.is_constinit;
    flags.is_inline = specialization_parser.is_inline;
    flags.is_thread_local = specialization_parser.is_thread_local;
    flags.is_extern =
        specialization_parser.storage_class == StorageClass::Extern;
    flags.is_static =
        specialization_parser.storage_class == StorageClass::Static;
    flags.is_auto_storage =
        specialization_parser.storage_class == StorageClass::Auto;
    flags.is_register =
        specialization_parser.storage_class == StorageClass::Register;
    flags.is_mutable = specialization_parser.is_mutable;
    flags.is_friend = specialization_parser.is_friend;
    flags.is_block_byref = specialization_parser.is_block_byref;
    flags.attrs = specialization_parser.leading_attrs;

    std::vector<NodeId> children;
    if (specialization_parser.type_syntax != InvalidNodeId) {
        children.push_back(specialization_parser.type_syntax);
    }

    ParsedDeclarator declarator =
        specialization_parser.parse_declarator(base, false);
    if (declarator.syntax != InvalidNodeId) {
        children.push_back(declarator.syntax);
    }

    std::string asm_label;
    if (check(TokenType::ASM_KW)) {
        children.push_back(parse_asm_label_syntax(&asm_label));
    }
    ParsedAttributes trailing_attrs = try_parse_attributes();
    declarator.attrs.append(std::move(trailing_attrs.attrs));
    children.insert(children.end(),
                    trailing_attrs.syntax.begin(),
                    trailing_attrs.syntax.end());

    AttributeList merged_attrs = flags.attrs;
    merged_attrs.append(declarator.attrs);
    declarator.attrs = std::move(merged_attrs);
    flags.attrs = declarator.attrs;
    flags.asm_label = std::move(asm_label);
    flags.vla_bounds = std::move(declarator.vla_bounds);
    flags.type_qualifiers = declarator.type_ref.qualifiers;
    declarator.type_ref =
        collect_session_.apply_type_attributes(declarator.type_ref,
                                               declarator.attrs,
                                               declarator.loc);
    declarator.type = declarator.type_ref.type;

    bool specialization_has_error = false;
    if (specialization_parser.storage_class != StorageClass::None) {
        diagnose(DiagnosticLevel::Error,
                 "explicit specialization cannot use a storage class specifier",
                 specialization_parser.begin_loc);
        specialization_has_error = true;
    }
    if (specialization_parser.is_friend) {
        diagnose(DiagnosticLevel::Error,
                 "explicit specialization declaration shall not be a friend declaration",
                 specialization_parser.begin_loc);
        specialization_has_error = true;
    }

    bool has_initializer_syntax =
        check(TokenType::ASSIGN) ||
        check(TokenType::LEFT_BRACE) ||
        (lang_opts_.is_cxx_mode() && check(TokenType::LEFT_PAREN));

    const collect::Session::TemplateInfo* owner_info =
        declarator.template_qualifier_info;
    defer_class_template_qualifier_instantiation_ = defer.previous;
    if (!owner_info) {
        collect::DeclResult decl;
        decl.has_error = true;
        skip_balanced_until_semicolon_or_brace();
        return ParsedDecl{make_node(NodeKind::UnknownDecl,
                                    begin,
                                    last_consumed_raw_end(),
                                    children,
                                    text_payload("template"),
                                    NodeFlagHasError),
                          std::move(decl)};
    }
    if (reject_explicit_specialization_of_member_of_explicit_class(
            *owner_info,
            declarator.template_qualifier_arguments,
            template_loc)) {
        collect::DeclResult decl;
        decl.has_error = true;
        skip_balanced_until_semicolon_or_brace();
        return ParsedDecl{make_node(NodeKind::UnknownDecl,
                                    begin,
                                    last_consumed_raw_end(),
                                    children,
                                    text_payload("template"),
                                    NodeFlagHasError),
                          std::move(decl)};
    }
    SrcLoc previous_primary_definition =
        collect_session_
            .register_explicit_static_data_member_specialization_declaration(
                *owner_info,
                declarator.template_qualifier_arguments,
                declarator.name,
                declarator.type_ref,
                declarator.loc);
    if (!previous_primary_definition.isInvalid()) {
        diagnose(DiagnosticLevel::Error,
                 "explicit specialization of static data member after implicit instantiation",
                 template_loc);
        diagnose(DiagnosticLevel::Note,
                 "static data member first defined here",
                 previous_primary_definition);
        specialization_has_error = true;
    }

    cir::EntityId owner = instantiate_template_with_args(
        *owner_info,
        declarator.template_qualifier_arguments,
        declarator.template_qualifier_loc.isInvalid()
            ? declarator.loc
            : declarator.template_qualifier_loc);
    if (!owner.valid()) {
        collect::DeclResult decl;
        decl.has_error = true;
        skip_balanced_until_semicolon_or_brace();
        return ParsedDecl{make_node(NodeKind::UnknownDecl,
                                    begin,
                                    last_consumed_raw_end(),
                                    children,
                                    text_payload("template"),
                                    NodeFlagHasError),
                          std::move(decl)};
    }
    const cir::Entity& owner_entity = collect_session_.file().entity(owner);
    declarator.qualified_context = owner_entity.semantic_context;

    cir::EntityId member =
        collect_session_.find_record_static_data_member(
            declarator.qualified_context,
            declarator.name,
            declarator.type_ref);
    collect::DeclResult decl;
    if (!member.valid()) {
        diagnose(DiagnosticLevel::Error,
                 "explicit specialization of static data member does not match any declaration",
                 declarator.loc);
        skip_balanced_until_semicolon_or_brace();
        decl.has_error = true;
        return ParsedDecl{make_node(NodeKind::UnknownDecl,
                                    begin,
                                    last_consumed_raw_end(),
                                    children,
                                    text_payload("template"),
                                    NodeFlagHasError),
                          std::move(decl)};
    }

    decl.entity = member;
    decl.type = declarator.type;
    decl.has_error = specialization_has_error;
    collect::ConstructorInitializationKind constructor_init_kind =
        check(TokenType::ASSIGN)
            ? (peek(1).type == TokenType::LEFT_BRACE
                   ? collect::ConstructorInitializationKind::CopyList
                   : collect::ConstructorInitializationKind::Copy)
            : collect::ConstructorInitializationKind::Direct;
    std::optional<collect::ExprResult> initializer;
    if (match(TokenType::ASSIGN)) {
        ParsedExpr init = parse_expression(PrecLevel::ASSIGNMENT);
        initializer = std::move(init.sem);
        children.push_back(init.syntax);
    } else if (check(TokenType::LEFT_BRACE)) {
        ParsedExpr init = parse_init_list_expression();
        initializer = std::move(init.sem);
        children.push_back(init.syntax);
    } else if (lang_opts_.is_cxx_mode() && match(TokenType::LEFT_PAREN)) {
        size_t init_begin = current_raw_index();
        std::vector<NodeId> init_children;
        if (!check(TokenType::RIGHT_PAREN)) {
            ParsedExpr init = parse_expression(PrecLevel::ASSIGNMENT);
            init_children.push_back(init.syntax);
            initializer = std::move(init.sem);
            while (match(TokenType::COMMA)) {
                ParsedExpr extra = parse_expression(PrecLevel::ASSIGNMENT);
                init_children.push_back(extra.syntax);
                diagnose(DiagnosticLevel::Error,
                         "direct initializers with multiple arguments require a class with a matching constructor",
                         loc_for_index(init_begin));
                specialization_has_error = true;
            }
        }
        if (!match(TokenType::RIGHT_PAREN)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ')' after initializer",
                     current_loc());
            specialization_has_error = true;
        }
        children.push_back(make_node(NodeKind::InitListExpr,
                                     init_begin,
                                     last_consumed_raw_end(),
                                     init_children));
    }

    if (initializer.has_value()) {
        cir::Entity& entity = collect_session_.file().entity_mut(member);
        if (entity.is_definition && entity.has_static_initializer) {
            diagnose(DiagnosticLevel::Error,
                     "redefinition of explicit static data member specialization",
                     declarator.loc);
            specialization_has_error = true;
        }
        entity.is_definition = true;
        entity.linkage = cir::LinkageKind::External;
        entity.qualifiers = flags.type_qualifiers;
        cir::TypeId completed_type =
            collect_session_.complete_initializer_type(declarator.type,
                                                       *initializer,
                                                       declarator.loc);
        decl = collect_session_.finish_variable_declaration(
            std::move(decl),
            completed_type,
            std::move(initializer),
            declarator.loc,
            flags,
            {},
            constructor_init_kind);
        decl.has_error = decl.has_error || specialization_has_error;
    }

    if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ';' after explicit static data member specialization",
                 current_loc());
        skip_until_statement_boundary();
        decl.has_error = true;
    }
    if (decl.entity.valid() && !decl.has_error) {
        collect_session_.mark_explicit_template_specialization(decl.entity);
    }

    return ParsedDecl{make_node(decl.has_error ? NodeKind::UnknownDecl
                                               : NodeKind::VarDecl,
                                begin,
                                last_consumed_raw_end(),
                                children,
                                text_payload("template"),
                                decl.has_error ? NodeFlagHasError
                                               : NodeFlagNone),
                      std::move(decl)};
}

std::optional<Parser::ParsedDecl>
Parser::try_parse_explicit_function_template_specialization(
    size_t begin,
    SrcLoc template_loc,
    bool has_member_template_head) {
    TemplateArgumentAccessExemptionScope access_exemption(collect_session_);
    ParserCheckpoint checkpoint = capture_parser_checkpoint();
    size_t saved_cursor = cursor_;
    size_t saved_last_end = last_consumed_raw_end_;

    DeclarationParser specialization_parser(
        *this,
        TypeParseContext::type_only(
            TypeParseContext::Origin::NamespaceDeclSpecifier));
    cir::TypeRef base = specialization_parser.parse_declaration(false, true);
    ParsedDeclarator declarator =
        specialization_parser.parse_declarator(base, false);
    if (!declarator.has_name) {
        cursor_ = saved_cursor;
        last_consumed_raw_end_ = saved_last_end;
        restore_parser_checkpoint(checkpoint);
        return std::nullopt;
    }

    std::vector<NodeId> children;
    if (specialization_parser.type_syntax != InvalidNodeId) {
        children.push_back(specialization_parser.type_syntax);
    }
    if (declarator.syntax != InvalidNodeId) {
        children.push_back(declarator.syntax);
    }

    auto explicit_template_id_is_followed_by_parameter_list = [&]() {
        if (!check(TokenType::LESS_THAN)) {
            return false;
        }
        int angle_depth = 0;
        size_t offset = 0;
        while (true) {
            TokenType type = peek(offset).type;
            if (type == TokenType::Eof || type == TokenType::SEMICOLON ||
                type == TokenType::LEFT_BRACE) {
                return false;
            }
            if (type == TokenType::LESS_THAN) {
                ++angle_depth;
            } else if (type == TokenType::GREATER_THAN) {
                --angle_depth;
                if (angle_depth == 0) {
                    return peek(offset + 1).type == TokenType::LEFT_PAREN;
                }
            } else if (type == TokenType::RIGHT_SHIFT) {
                if (angle_depth <= 2) {
                    return peek(offset + 1).type == TokenType::LEFT_PAREN;
                }
                angle_depth -= 2;
            }
            ++offset;
        }
    };

    std::vector<const collect::Session::TemplateInfo*> candidates =
        collect_session_.function_template_infos_for_name(
            declarator.qualified_context,
            declarator.name,
            !declarator.qualified_context.valid());

    bool has_explicit_template_arguments = false;
    std::vector<collect::Session::TemplateArgument> explicit_arguments;
    std::vector<collect::CandidateExplicitTemplateArguments>
        candidate_explicit_arguments;
    if (check(TokenType::LESS_THAN)) {
        if (!explicit_template_id_is_followed_by_parameter_list()) {
            cursor_ = saved_cursor;
            last_consumed_raw_end_ = saved_last_end;
            restore_parser_checkpoint(checkpoint);
            return std::nullopt;
        }
        has_explicit_template_arguments = true;
        bool parsed_arguments = false;
        if (!candidates.empty()) {
            parsed_arguments =
                parse_function_template_argument_list_for_candidates(
                    *candidates.front(),
                    candidates,
                    explicit_arguments,
                    candidate_explicit_arguments,
                    declarator.loc);
        } else {
            parsed_arguments =
                parse_dependent_expression_template_argument_list(
                    declarator.loc);
        }
        if (!parsed_arguments) {
            collect::DeclResult decl;
            decl.has_error = true;
            skip_balanced_until_semicolon_or_brace();
            return {ParsedDecl{make_node(NodeKind::UnknownDecl,
                                         begin,
                                         last_consumed_raw_end(),
                                         children,
                                         text_payload("template"),
                                         NodeFlagHasError),
                               std::move(decl)}};
        }

        ParsedDeclarator suffix =
            specialization_parser.parse_declarator(declarator.type_ref,
                                                   true,
                                                   &declarator);
        if (suffix.syntax != InvalidNodeId) {
            children.push_back(suffix.syntax);
        }
        if (!suffix.is_function) {
            cursor_ = saved_cursor;
            last_consumed_raw_end_ = saved_last_end;
            restore_parser_checkpoint(checkpoint);
            return std::nullopt;
        }
        declarator.type = suffix.type;
        declarator.type_ref = suffix.type_ref;
        declarator.is_function = suffix.is_function;
        declarator.is_variadic = suffix.is_variadic;
        declarator.has_prototype = suffix.has_prototype;
        declarator.is_kr_style = suffix.is_kr_style;
        declarator.has_trailing_return_type =
            suffix.has_trailing_return_type;
        declarator.has_noexcept_specifier =
            suffix.has_noexcept_specifier;
        declarator.has_unsupported_semantics =
            declarator.has_unsupported_semantics ||
            suffix.has_unsupported_semantics;
        declarator.kr_param_names = std::move(suffix.kr_param_names);
        declarator.params = std::move(suffix.params);
        declarator.vla_bounds =
            collect_session_.chain(std::move(declarator.vla_bounds),
                                   std::move(suffix.vla_bounds),
                                   declarator.loc);
        declarator.attrs.append(std::move(suffix.attrs));
    } else if (!declarator.is_function) {
        cursor_ = saved_cursor;
        last_consumed_raw_end_ = saved_last_end;
        restore_parser_checkpoint(checkpoint);
        return std::nullopt;
    }

    ParsedAttributes trailing_attrs = try_parse_attributes();
    declarator.attrs.append(std::move(trailing_attrs.attrs));
    children.insert(children.end(),
                    trailing_attrs.syntax.begin(),
                    trailing_attrs.syntax.end());

    struct Match {
        const collect::Session::TemplateInfo* info = nullptr;
        std::vector<collect::Session::TemplateArgument> arguments;
        uint64_t point_lookup_generation = 0;
    };
    std::vector<Match> matches;
    for (const collect::Session::TemplateInfo* candidate : candidates) {
        const std::vector<collect::Session::TemplateArgument>*
            candidate_arguments = &explicit_arguments;
        auto replayed = std::find_if(
            candidate_explicit_arguments.begin(),
            candidate_explicit_arguments.end(),
            [&](const collect::CandidateExplicitTemplateArguments& entry) {
                return entry.template_entity == candidate->entity;
            });
        if (replayed != candidate_explicit_arguments.end()) {
            if (!replayed->viable) {
                continue;
            }
            candidate_arguments = &replayed->arguments;
        }
        std::vector<collect::Session::TemplateArgument> deduced;
        collect::Session::PatternInstantiationCallbacks callbacks;
        configure_pattern_instantiation_callbacks(callbacks, declarator.loc);
        if (deduce_function_template_declaration_match(
                *candidate,
                declarator.type,
                deduced,
                has_explicit_template_arguments ? candidate_arguments
                                                : nullptr,
                callbacks,
                declarator.loc)) {
            matches.push_back(Match{candidate,
                                    std::move(deduced),
                                    callbacks.point_lookup_generation});
        }
    }

    auto more_specialized = [&](const Match& lhs, const Match& rhs) {
        if (!lhs.info || !rhs.info) {
            return false;
        }
        return collect_session_.function_template_more_specialized(*lhs.info,
                                                                   *rhs.info,
                                                                   collect::Session::FunctionTemplateOrderingContext::declaration());
    };
    auto diagnose_ambiguous_match_notes = [&](const Match& lhs,
                                              const Match& rhs) {
        auto note_candidate = [&](const Match& match) {
            if (match.info && match.info->entity.valid() &&
                collect_session_.file().valid(match.info->entity)) {
                diagnose(DiagnosticLevel::Note,
                         "candidate function template declared here",
                         collect_session_.file().entity(match.info->entity).loc);
            }
        };
        note_candidate(lhs);
        note_candidate(rhs);
        if (lhs.info && rhs.info &&
            collect_session_.function_template_unordered_constraints_tie(
                *lhs.info,
                *rhs.info,
                collect::Session::FunctionTemplateOrderingContext::declaration())) {
            diagnose(
                DiagnosticLevel::Note,
                "candidate associated constraints are not ordered by subsumption",
                declarator.loc);
        }
    };

    bool specialization_has_error = false;
    Match selected;
    if (matches.empty()) {
        diagnose(DiagnosticLevel::Error,
                 "no matching function template for explicit specialization",
                 declarator.loc);
        specialization_has_error = true;
    } else {
        size_t best = 0;
        for (size_t i = 1; i < matches.size(); ++i) {
            if (more_specialized(matches[i], matches[best])) {
                best = i;
            }
        }
        std::optional<size_t> ambiguous_index;
        for (size_t i = 0; i < matches.size(); ++i) {
            if (i != best && !more_specialized(matches[best], matches[i])) {
                ambiguous_index = i;
                break;
            }
        }
        if (ambiguous_index.has_value()) {
            diagnose(DiagnosticLevel::Error,
                     "ambiguous explicit function template specialization",
                     declarator.loc);
            diagnose_ambiguous_match_notes(matches[best],
                                           matches[*ambiguous_index]);
            specialization_has_error = true;
        } else {
            selected = std::move(matches[best]);
        }
    }

    if (specialization_parser.storage_class != StorageClass::None) {
        diagnose(DiagnosticLevel::Error,
                 "explicit specialization cannot use a storage class specifier",
                 specialization_parser.begin_loc);
        specialization_has_error = true;
    }
    if (specialization_parser.is_friend) {
        diagnose(DiagnosticLevel::Error,
                 "explicit specialization declaration shall not be a friend declaration",
                 specialization_parser.begin_loc);
        specialization_has_error = true;
    }
    for (ParsedParam& param : declarator.params) {
        if (param.has_default_argument) {
            diagnose(DiagnosticLevel::Error,
                     "default function argument is not allowed in explicit function template specialization",
                     param.default_argument_loc.isInvalid()
                         ? param.loc
                         : param.default_argument_loc);
            param.has_default_argument = false;
            specialization_has_error = true;
        }
    }

    auto make_invalid_specialization_decl = [&]() {
        collect::DeclResult decl;
        decl.has_error = true;
        skip_balanced_until_semicolon_or_brace();
        return ParsedDecl{make_node(NodeKind::UnknownDecl,
                                    begin,
                                    last_consumed_raw_end(),
                                    children,
                                    text_payload("template"),
                                    NodeFlagHasError),
                          std::move(decl)};
    };
    if (!selected.info) {
        return make_invalid_specialization_decl();
    }

    std::string asm_label;
    if (check(TokenType::ASM_KW)) {
        children.push_back(parse_asm_label_syntax(&asm_label));
    }

    collect::DeclFlags flags;
    flags.is_constexpr = specialization_parser.is_constexpr;
    flags.is_consteval = specialization_parser.is_consteval;
    flags.is_constinit = specialization_parser.is_constinit;
    flags.is_inline = specialization_parser.is_inline;
    flags.is_thread_local = specialization_parser.is_thread_local;
    flags.is_extern =
        specialization_parser.storage_class == StorageClass::Extern;
    flags.is_static =
        specialization_parser.storage_class == StorageClass::Static;
    flags.is_auto_storage =
        specialization_parser.storage_class == StorageClass::Auto;
    flags.is_register =
        specialization_parser.storage_class == StorageClass::Register;
    flags.is_mutable = specialization_parser.is_mutable;
    flags.is_friend = specialization_parser.is_friend;
    flags.is_block_byref = specialization_parser.is_block_byref;
    flags.attrs = specialization_parser.leading_attrs;
    AttributeList merged_attrs = flags.attrs;
    merged_attrs.append(declarator.attrs);
    declarator.attrs = std::move(merged_attrs);
    flags.attrs = declarator.attrs;
    flags.asm_label = std::move(asm_label);
    flags.vla_bounds = std::move(declarator.vla_bounds);
    flags.type_qualifiers = declarator.type_ref.qualifiers;

    const cir::File& file = collect_session_.file();
    const auto* function_payload = std::get_if<cir::FunctionTypePayload>(
        &file.type_payload(file.resolved_type(declarator.type)));
    cir::TypeRef result_type = function_payload
        ? function_payload->return_type
        : collect_session_.type_ref(collect_session_.file().unknown_type());

    bool specialization_is_definition = check(TokenType::LEFT_BRACE);
    std::string memo_key;
    cir::EntityId cached;
    bool cached_implicit = false;
    bool cached_definition = false;
    if (selected.info) {
        memo_key = collect_session_.template_memo_key(selected.info->entity,
                                                      selected.arguments);
        cached = collect_session_.cached_instantiation(memo_key);
        if (cached.valid() && file.valid(cached)) {
            const cir::Entity& previous = file.entity(cached);
            const cir::TemplateSpecializationFact* previous_fact =
                file.template_specialization(cached);

            cached_implicit =
                !previous.is_explicit_template_specialization &&
                previous_fact &&
                !previous_fact->point_of_instantiation.isInvalid();
            cached_definition = previous.is_definition;
        }
    }

    auto note_implicit_instantiation_point = [&](cir::EntityId specialization) {
        const cir::TemplateSpecializationFact* fact =
            collect_session_.file().template_specialization(specialization);
        if (fact && !fact->point_of_instantiation.isInvalid()) {
            diagnose(DiagnosticLevel::Note,
                     "implicit instantiation first required here",
                     fact->point_of_instantiation);
        }
    };
    if (cached_implicit) {
        diagnose(DiagnosticLevel::Error,
                 "explicit specialization of function template after implicit instantiation",
                 declarator.loc);
        note_implicit_instantiation_point(cached);
        specialization_has_error = true;
    } else if (cached_definition && specialization_is_definition) {
        diagnose(DiagnosticLevel::Error,
                 "redefinition of explicit function template specialization",
                 declarator.loc);
        specialization_has_error = true;
    }

    if (selected.info) {
        declarator.name =
            collect_session_.template_display_name(*selected.info,
                                                   selected.arguments);
        declarator.explicit_function_template_specialization_info =
            selected.info;
        declarator.explicit_function_template_specialization_arguments =
            selected.arguments;
    }

    cir::DeclContextId explicit_context = declarator.qualified_context;
    bool member_template_specialization = false;
    if (explicit_context.valid() &&
        file.decl_context(explicit_context).kind == cir::DeclContextKind::Record) {
        member_template_specialization =
            selected.info->entity.valid() &&
            file.valid(selected.info->entity) &&
            (file.entity(selected.info->entity).kind ==
                 cir::EntityKind::Method ||
             file.entity(selected.info->entity).kind ==
                 cir::EntityKind::Constructor ||
             file.entity(selected.info->entity).kind ==
                 cir::EntityKind::Destructor);
        bool function_carried_member_template =
            selected.info->entity.valid() &&
            file.valid(selected.info->entity) &&
            file.entity(selected.info->entity).kind ==
                cir::EntityKind::Function;
        cir::EntityId explicit_owner =
            file.decl_context(explicit_context).owner;
        bool owner_is_class_template_specialization =
            explicit_owner.valid() && file.valid(explicit_owner) &&
            file.template_specialization(explicit_owner) != nullptr;
        if (owner_is_class_template_specialization &&
            !has_member_template_head) {
            diagnose(DiagnosticLevel::Error,
                     "explicit specialization of member template of class template requires 'template<>'",
                     declarator.loc);
            specialization_has_error = true;
            return make_invalid_specialization_decl();
        }
        if (!owner_is_class_template_specialization &&
            has_member_template_head) {
            diagnose(DiagnosticLevel::Error,
                     "unexpected 'template<>' in explicit member function template specialization",
                     declarator.loc);
            specialization_has_error = true;
            return make_invalid_specialization_decl();
        }
        if (!member_template_specialization &&
            !function_carried_member_template) {
            diagnose(DiagnosticLevel::Error,
                     "explicit function template specialization has an invalid member owner",
                     declarator.loc);
            specialization_has_error = true;
            return make_invalid_specialization_decl();
        }

        if (member_template_specialization) {
            cir::EntityId member_specialization = cached;
            if (!member_specialization.valid() ||
                !file.valid(member_specialization)) {
                member_specialization =
                    collect_session_.create_member_template_specialization(
                        *selected.info,
                        selected.arguments,
                        declarator.type,
                        declarator.loc,
                        &flags);
            }
            if (!member_specialization.valid()) {
                diagnose(DiagnosticLevel::Error,
                         "could not create explicit member function template specialization",
                         declarator.loc);
                specialization_has_error = true;
                return make_invalid_specialization_decl();
            }
            declarator.explicit_member_function_template_specialization =
                member_specialization;
        }
    }

    struct ExplicitSpecializationContextExit {
        collect::Session* session = nullptr;
        ~ExplicitSpecializationContextExit() {
            if (session) {
                session->leave_scope();
            }
        }
    } explicit_scope;
    if (explicit_context.valid() && !member_template_specialization) {
        cir::DeclContextKind context_kind =
            file.decl_context(explicit_context).kind;
        collect::ScopeFlags scope_flags =
            context_kind == cir::DeclContextKind::Namespace
                ? collect::ScopeFlags::NamespaceScope |
                      collect::ScopeFlags::FileScope
                : collect::ScopeFlags::FileScope;
        collect_session_.enter_existing_context(explicit_context,
                                                scope_flags);
        explicit_scope.session = &collect_session_;
        declarator.qualified_context = {};
    }

    struct ExplicitMemberTemplateSpecializationDeclarationExit {
        Parser& parser;
        bool previous = false;
        ~ExplicitMemberTemplateSpecializationDeclarationExit() {
            parser.explicit_member_function_specialization_declaration_ =
                previous;
        }
    } member_declaration_scope{
        *this,
        explicit_member_function_specialization_declaration_};
    if (member_template_specialization) {
        explicit_member_function_specialization_declaration_ =
            !specialization_is_definition;
    }

    access_exemption.finish();
    FunctionDeclaratorResult result =
        handle_function_declarator(declarator, children, flags);
    collect::DeclResult decl = std::move(result.decl);
    decl.has_error = decl.has_error || specialization_has_error;

    if (decl.entity.valid() && selected.info) {
        if (!cached_implicit &&
            !(cached_definition && specialization_is_definition)) {
            if (cached.valid()) {
                const cir::Entity& previous = file.entity(cached);
                const cir::Entity& current = file.entity(decl.entity);
                if (!previous.is_definition && current.is_definition) {
                    collect_session_.replace_instantiation(memo_key,
                                                           decl.entity);
                }
            } else {
                collect_session_.remember_instantiation(memo_key,
                                                        decl.entity);
            }
        }
        collect_session_.remember_template_specialization(decl.entity,
                                                        *selected.info,
                                                        selected.arguments);
    }

    if (!result.parsed_definition) {
        if (match(TokenType::COMMA)) {
            diagnose(DiagnosticLevel::Error,
                     "explicit function template specialization declaration may only declare one entity",
                     last_consumed_loc());
            skip_until_statement_boundary();
            decl.has_error = true;
        } else if (!match(TokenType::SEMICOLON)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ';' after explicit function template specialization",
                     current_loc());
            skip_until_statement_boundary();
            decl.has_error = true;
        }
    }
    if (decl.entity.valid() && !decl.has_error) {
        collect_session_.mark_explicit_template_specialization(decl.entity);
    }

    return {ParsedDecl{make_node(decl.has_error ? NodeKind::UnknownDecl
                                                : NodeKind::FunctionDecl,
                                 begin,
                                 last_consumed_raw_end(),
                                 children,
                                 text_payload("template"),
                                 decl.has_error ? NodeFlagHasError
                                                : NodeFlagNone),
                          std::move(decl)}};
}

Parser::ParsedDecl Parser::parse_cxx_explicit_instantiation_declaration() {
    size_t begin = current_raw_index();
    Token extern_token = current();
    consume();
    Token template_token = current();
    if (!match(TokenType::TEMPLATE)) {
        diagnose(DiagnosticLevel::Error,
                 "expected 'template' after 'extern' in explicit instantiation declaration",
                 extern_token.loc);
        skip_until_statement_boundary();
        collect::DeclResult decl;
        decl.has_error = true;
        return {make_node(NodeKind::UnknownDecl,
                          begin,
                          last_consumed_raw_end(),
                          {},
                          text_payload("extern template"),
                          NodeFlagHasError),
                std::move(decl)};
    }

    TemplateArgumentAccessExemptionScope access_exemption(collect_session_);

    if (std::optional<ParsedDecl> class_template =
            try_parse_class_template_explicit_instantiation_declaration(
                begin,
                extern_token.loc,
                template_token.loc)) {
        return std::move(*class_template);
    }

    if (std::optional<ParsedDecl> member_class =
            try_parse_member_class_explicit_instantiation_declaration(
                begin,
                extern_token.loc,
                template_token.loc)) {
        return std::move(*member_class);
    }

    if (std::optional<ParsedDecl> conversion =
            try_parse_conversion_function_template_explicit_instantiation(
                begin,
                extern_token.loc,
                template_token.loc,
                /*is_declaration=*/true)) {
        return std::move(*conversion);
    }

    if (std::optional<ParsedDecl> function =
            try_parse_function_template_explicit_instantiation_declaration(
                begin,
                extern_token.loc,
                template_token.loc)) {
        return std::move(*function);
    }

    if (std::optional<ParsedDecl> static_member_template =
            try_parse_static_data_member_template_explicit_instantiation_declaration(
                begin,
                extern_token.loc,
                template_token.loc)) {
        return std::move(*static_member_template);
    }

    if (std::optional<ParsedDecl> variable_template =
            try_parse_variable_template_explicit_instantiation_declaration(
                begin,
                extern_token.loc,
                template_token.loc)) {
        return std::move(*variable_template);
    }

    if (std::optional<ParsedDecl> static_member =
            try_parse_static_data_member_explicit_instantiation_declaration(
                begin,
                extern_token.loc,
                template_token.loc)) {
        return std::move(*static_member);
    }

    diagnose(DiagnosticLevel::Error,
             "unsupported explicit instantiation declaration form",
             current_loc());
    skip_balanced_until_semicolon_or_brace();
    collect::DeclResult decl;
    decl.has_error = true;
    return {make_node(NodeKind::UnknownDecl,
                      begin,
                      last_consumed_raw_end(),
                      {},
                      text_payload("extern template"),
                      NodeFlagHasError),
            std::move(decl)};
}

Parser::ParsedDecl Parser::parse_cxx_explicit_instantiation_definition() {
    size_t begin = current_raw_index();
    Token template_token = current();
    if (!match(TokenType::TEMPLATE)) {
        diagnose(DiagnosticLevel::Error,
                 "expected 'template' in explicit instantiation definition",
                 template_token.loc);
        skip_until_statement_boundary();
        collect::DeclResult decl;
        decl.has_error = true;
        return {make_node(NodeKind::UnknownDecl,
                          begin,
                          last_consumed_raw_end(),
                          {},
                          text_payload("template"),
                          NodeFlagHasError),
                std::move(decl)};
    }

    TemplateArgumentAccessExemptionScope access_exemption(collect_session_);

    if (std::optional<ParsedDecl> class_template =
            try_parse_class_template_explicit_instantiation_definition(
                begin,
                template_token.loc)) {
        return std::move(*class_template);
    }

    if (std::optional<ParsedDecl> member_class =
            try_parse_member_class_explicit_instantiation_definition(
                begin,
                template_token.loc)) {
        return std::move(*member_class);
    }

    if (std::optional<ParsedDecl> conversion =
            try_parse_conversion_function_template_explicit_instantiation(
                begin,
                template_token.loc,
                template_token.loc,
                /*is_declaration=*/false)) {
        return std::move(*conversion);
    }

    if (std::optional<ParsedDecl> function =
            try_parse_function_template_explicit_instantiation_definition(
                begin,
                template_token.loc)) {
        return std::move(*function);
    }

    if (std::optional<ParsedDecl> static_member_template =
            try_parse_static_data_member_template_explicit_instantiation_definition(
                begin,
                template_token.loc)) {
        return std::move(*static_member_template);
    }

    if (std::optional<ParsedDecl> variable_template =
            try_parse_variable_template_explicit_instantiation_definition(
                begin,
                template_token.loc)) {
        return std::move(*variable_template);
    }

    if (std::optional<ParsedDecl> static_member =
            try_parse_static_data_member_explicit_instantiation_definition(
                begin,
                template_token.loc)) {
        return std::move(*static_member);
    }

    diagnose(DiagnosticLevel::Error,
             "unsupported explicit instantiation definition form",
             current_loc());
    skip_balanced_until_semicolon_or_brace();
    collect::DeclResult decl;
    decl.has_error = true;
    return {make_node(NodeKind::UnknownDecl,
                      begin,
                      last_consumed_raw_end(),
                      {},
                      text_payload("template"),
                      NodeFlagHasError),
            std::move(decl)};
}

std::optional<Parser::ParsedDecl>
Parser::try_parse_class_template_explicit_instantiation_declaration(
    size_t begin,
    SrcLoc extern_loc,
    SrcLoc template_loc) {
    if (!(check(TokenType::STRUCT) || check(TokenType::CLASS) ||
          check(TokenType::UNION))) {
        return std::nullopt;
    }

    TentativeParsingAction tentative(*this, TentativeMode::CollectBacked);
    Token class_key = current();
    consume();

    bool has_error = false;
    std::vector<NodeId> children;
    ParsedAttributes leading_attrs = try_parse_attributes();
    children.insert(children.end(),
                    leading_attrs.syntax.begin(),
                    leading_attrs.syntax.end());

    bool global_qualifier = false;
    if (match(TokenType::SCOPE_RESOLUTION)) {
        global_qualifier = true;
    }

    std::vector<std::string_view> qualifiers;
    while (is_identifier_token(current().type) &&
           peek(1).type == TokenType::SCOPE_RESOLUTION &&
           peek(2).type != TokenType::MULTIPLY) {
        qualifiers.push_back(current().value);
        consume();
        consume();
    }

    if (is_identifier_token(current().type) &&
        peek(1).type == TokenType::LESS_THAN &&
        template_id_precedes_scope(0)) {
        return std::nullopt;
    }

    Token name_token = current();
    if (!is_identifier_token(name_token.type)) {
        diagnose(DiagnosticLevel::Error,
                 "expected class template name in explicit instantiation declaration",
                 current_loc());
        skip_balanced_until_semicolon_or_brace();
        collect::DeclResult decl;
        decl.has_error = true;
        tentative.commit();
        return ParsedDecl{make_node(NodeKind::UnknownDecl,
                                    begin,
                                    last_consumed_raw_end(),
                                    children,
                                    text_payload("extern template"),
                                    NodeFlagHasError),
                          std::move(decl)};
    }
    consume();

    const cir::File& file = collect_session_.file();
    const collect::Session::TemplateInfo* primary =
        qualifiers.empty() && !global_qualifier
            ? collect_session_.template_info_for_name(name_token.value)
            : collect_session_.peek_qualified_template_info(
                  global_qualifier,
                  qualifiers,
                  name_token.value);
    if (primary && primary->is_class_template &&
        !class_template_keys_agree(class_key_record_kind(class_key.type),
                                   primary->record_kind)) {
        diagnose(DiagnosticLevel::Error,
                 "class-key does not agree with the original class template",
                 class_key.loc);
        has_error = true;
    }
    auto qualifier_names_a_record = [&]() {
        if (qualifiers.empty()) {
            return false;
        }
        std::vector<std::string_view> owner_qualifiers(
            qualifiers.begin(),
            qualifiers.end() - 1);
        cir::TypeRef owner_type =
            owner_qualifiers.empty() && !global_qualifier
                ? collect_session_.lookup_type_name_ref(qualifiers.back())
                : collect_session_.peek_qualified_type_ref(
                      global_qualifier,
                      owner_qualifiers,
                      qualifiers.back());
        if (!owner_type.valid()) {
            return false;
        }
        cir::TypeId resolved = file.resolved_type(owner_type.type);
        return file.valid(resolved) &&
               file.type(resolved).kind == cir::TypeKind::Record;
    };
    if (!primary && qualifier_names_a_record()) {
        return std::nullopt;
    }
    if (primary && primary->lexical_context.valid()) {
        if (file.valid(primary->lexical_context) &&
            file.decl_context(primary->lexical_context).kind ==
                cir::DeclContextKind::Record) {
            return std::nullopt;
        }
    }

    std::vector<collect::Session::TemplateArgument> arguments;
    if (!check(TokenType::LESS_THAN)) {
        diagnose(DiagnosticLevel::Error,
                 "class explicit instantiation declaration requires a template argument list",
                 name_token.loc);
        has_error = true;
    } else if (!primary || !primary->is_class_template) {
        diagnose(DiagnosticLevel::Error,
                 "no matching class template for explicit instantiation declaration",
                 name_token.loc);
        if (!parse_dependent_expression_template_argument_list(name_token.loc)) {
            skip_balanced_until_semicolon_or_brace();
        }
        has_error = true;
    } else if (!parse_and_canonicalize_template_argument_list(*primary,
                                                             arguments,
                                                             name_token.loc)) {
        has_error = true;
    }
    bool prior_explicit_specialization =
        !has_error && primary && primary->is_class_template &&
        collect_session_.explicit_template_specialization_declared(
            *primary, arguments);

    ParsedAttributes trailing_attrs = try_parse_attributes();
    children.insert(children.end(),
                    trailing_attrs.syntax.begin(),
                    trailing_attrs.syntax.end());
    AttributeList explicit_instantiation_attrs = leading_attrs.attrs;
    explicit_instantiation_attrs.append(trailing_attrs.attrs);
    if (has_forbidden_explicit_instantiation_attributes(
            explicit_instantiation_attrs)) {
        diagnose(DiagnosticLevel::Error,
                 "attributes cannot appertain to an explicit instantiation",
                 leading_attrs.attrs.empty() ? class_key.loc : extern_loc);
        has_error = true;
    }
    if (primary && primary->is_class_template && !primary->has_definition &&
        !prior_explicit_specialization) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation declaration requires a class template definition",
                 name_token.loc);
        has_error = true;
    }
    if (primary && primary->is_class_template &&
        !prior_explicit_specialization) {
        SrcLoc prior_definition_loc;
        if (collect_session_.explicit_instantiation_definition_declared(
                *primary,
                arguments,
                &prior_definition_loc)) {
            diagnose(DiagnosticLevel::Error,
                     "explicit instantiation declaration must precede explicit instantiation definition",
                     name_token.loc);
            if (!prior_definition_loc.isInvalid()) {
                diagnose(DiagnosticLevel::Note,
                         "explicit instantiation definition is here",
                         prior_definition_loc);
            }
            has_error = true;
        }
    }

    if (match(TokenType::COMMA)) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation declaration may only declare one entity",
                 last_consumed_loc());
        skip_until_statement_boundary();
        has_error = true;
    } else if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ';' after explicit instantiation declaration",
                 current_loc());
        skip_until_statement_boundary();
        has_error = true;
    }

    collect::DeclResult decl;
    decl.has_error = has_error;
    if (primary && primary->is_class_template && !has_error) {
        if (!collect_session_.declare_explicit_instantiation_declaration(
                *primary,
                arguments,
                template_loc,
                explicit_instantiation_attrs)) {
            has_error = true;
            decl.has_error = true;
        } else {
            cir::EntityId cached = collect_session_.cached_instantiation(
                collect_session_.template_memo_key(primary->entity, arguments));
            collect_session_
                .apply_explicit_instantiation_declaration_suppression(
                    cached,
                    *primary,
                    arguments);
            collect_session_
                .apply_class_explicit_instantiation_declaration_suppression(
                    cached,
                    *primary,
                    arguments);
        }
    }

    tentative.commit();
    return ParsedDecl{
        make_node(has_error ? NodeKind::UnknownDecl : NodeKind::RecordDecl,
                  begin,
                  last_consumed_raw_end(),
                  children,
                  text_payload("extern template"),
                  has_error ? NodeFlagHasError : NodeFlagNone),
        std::move(decl)};
}

std::optional<Parser::ParsedDecl>
Parser::try_parse_class_template_explicit_instantiation_definition(
    size_t begin,
    SrcLoc template_loc) {
    if (!(check(TokenType::STRUCT) || check(TokenType::CLASS) ||
          check(TokenType::UNION))) {
        return std::nullopt;
    }

    TentativeParsingAction tentative(*this, TentativeMode::CollectBacked);
    Token class_key = current();
    consume();

    bool has_error = false;
    std::vector<NodeId> children;
    ParsedAttributes leading_attrs = try_parse_attributes();
    children.insert(children.end(),
                    leading_attrs.syntax.begin(),
                    leading_attrs.syntax.end());

    bool global_qualifier = false;
    if (match(TokenType::SCOPE_RESOLUTION)) {
        global_qualifier = true;
    }

    std::vector<std::string_view> qualifiers;
    while (is_identifier_token(current().type) &&
           peek(1).type == TokenType::SCOPE_RESOLUTION &&
           peek(2).type != TokenType::MULTIPLY) {
        qualifiers.push_back(current().value);
        consume();
        consume();
    }

    if (is_identifier_token(current().type) &&
        peek(1).type == TokenType::LESS_THAN &&
        template_id_precedes_scope(0)) {
        return std::nullopt;
    }

    Token name_token = current();
    if (!is_identifier_token(name_token.type)) {
        diagnose(DiagnosticLevel::Error,
                 "expected class template name in explicit instantiation definition",
                 current_loc());
        skip_balanced_until_semicolon_or_brace();
        collect::DeclResult decl;
        decl.has_error = true;
        tentative.commit();
        return ParsedDecl{make_node(NodeKind::UnknownDecl,
                                    begin,
                                    last_consumed_raw_end(),
                                    children,
                                    text_payload("template"),
                                    NodeFlagHasError),
                          std::move(decl)};
    }
    consume();

    const cir::File& file = collect_session_.file();
    const collect::Session::TemplateInfo* primary =
        qualifiers.empty() && !global_qualifier
            ? collect_session_.template_info_for_name(name_token.value)
            : collect_session_.peek_qualified_template_info(
                  global_qualifier,
                  qualifiers,
                  name_token.value);
    if (primary && primary->is_class_template &&
        !class_template_keys_agree(class_key_record_kind(class_key.type),
                                   primary->record_kind)) {
        diagnose(DiagnosticLevel::Error,
                 "class-key does not agree with the original class template",
                 class_key.loc);
        has_error = true;
    }
    auto qualifier_names_a_record = [&]() {
        if (qualifiers.empty()) {
            return false;
        }
        std::vector<std::string_view> owner_qualifiers(
            qualifiers.begin(),
            qualifiers.end() - 1);
        cir::TypeRef owner_type =
            owner_qualifiers.empty() && !global_qualifier
                ? collect_session_.lookup_type_name_ref(qualifiers.back())
                : collect_session_.peek_qualified_type_ref(
                      global_qualifier,
                      owner_qualifiers,
                      qualifiers.back());
        if (!owner_type.valid()) {
            return false;
        }
        cir::TypeId resolved = file.resolved_type(owner_type.type);
        return file.valid(resolved) &&
               file.type(resolved).kind == cir::TypeKind::Record;
    };
    if (!primary && qualifier_names_a_record()) {
        return std::nullopt;
    }
    if (primary && primary->lexical_context.valid()) {
        if (file.valid(primary->lexical_context) &&
            file.decl_context(primary->lexical_context).kind ==
                cir::DeclContextKind::Record) {
            return std::nullopt;
        }
    }

    std::vector<collect::Session::TemplateArgument> arguments;
    if (!check(TokenType::LESS_THAN)) {
        diagnose(DiagnosticLevel::Error,
                 "class explicit instantiation definition requires a template argument list",
                 name_token.loc);
        has_error = true;
    } else if (!primary || !primary->is_class_template) {
        diagnose(DiagnosticLevel::Error,
                 "no matching class template for explicit instantiation definition",
                 name_token.loc);
        if (!parse_dependent_expression_template_argument_list(name_token.loc)) {
            skip_balanced_until_semicolon_or_brace();
        }
        has_error = true;
    } else if (!parse_and_canonicalize_template_argument_list(*primary,
                                                             arguments,
                                                             name_token.loc)) {
        has_error = true;
    }
    cir::EntityId prior_specialization_entity;
    bool prior_explicit_specialization =
        !has_error && primary && primary->is_class_template &&
        collect_session_.explicit_template_specialization_declared(
            *primary, arguments, &prior_specialization_entity);

    ParsedAttributes trailing_attrs = try_parse_attributes();
    children.insert(children.end(),
                    trailing_attrs.syntax.begin(),
                    trailing_attrs.syntax.end());
    AttributeList explicit_instantiation_attrs = leading_attrs.attrs;
    explicit_instantiation_attrs.append(trailing_attrs.attrs);
    if (has_forbidden_explicit_instantiation_attributes(
            explicit_instantiation_attrs)) {
        diagnose(DiagnosticLevel::Error,
                 "attributes cannot appertain to an explicit instantiation",
                 leading_attrs.attrs.empty() ? class_key.loc : template_loc);
        has_error = true;
    }
    if (primary && primary->is_class_template && !primary->has_definition &&
        !prior_explicit_specialization) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation definition requires a class template definition",
                 name_token.loc);
        has_error = true;
    }
    if (primary && primary->is_class_template &&
        !prior_explicit_specialization) {
        SrcLoc prior_definition_loc;
        if (collect_session_.explicit_instantiation_definition_declared(
                *primary,
                arguments,
                &prior_definition_loc)) {
            diagnose(DiagnosticLevel::Error,
                     "redefinition of explicit class template instantiation",
                     name_token.loc);
            if (!prior_definition_loc.isInvalid()) {
                diagnose(DiagnosticLevel::Note,
                         "previous explicit instantiation definition is here",
                         prior_definition_loc);
            }
            has_error = true;
        }
    }

    if (match(TokenType::COMMA)) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation definition may only declare one entity",
                 last_consumed_loc());
        skip_until_statement_boundary();
        has_error = true;
    } else if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ';' after explicit instantiation definition",
                 current_loc());
        skip_until_statement_boundary();
        has_error = true;
    }

    collect::DeclResult decl;
    decl.has_error = has_error;
    if (primary && primary->is_class_template && !has_error) {
        if (prior_explicit_specialization) {
            decl.entity = prior_specialization_entity;
            tentative.commit();
            return ParsedDecl{
                make_node(NodeKind::RecordDecl,
                          begin,
                          last_consumed_raw_end(),
                          children,
                          text_payload("template"),
                          NodeFlagNone),
                std::move(decl)};
        }
        collect_session_.declare_explicit_instantiation_definition(
            *primary,
            arguments,
            template_loc,
            explicit_instantiation_attrs);
        cir::EntityId instantiated =
            instantiate_template_with_args(*primary,
                                           arguments,
                                           template_loc);
        decl.entity = instantiated;
        if (!instantiated.valid()) {
            decl.has_error = true;
        } else {
            collect_session_.apply_explicit_instantiation_definition_emission(
                instantiated,
                *primary,
                arguments);
            force_class_explicit_instantiation_definition_members(
                instantiated,
                template_loc);
        }
    }

    tentative.commit();
    return ParsedDecl{
        make_node(decl.has_error ? NodeKind::UnknownDecl : NodeKind::RecordDecl,
                  begin,
                  last_consumed_raw_end(),
                  children,
                  text_payload("template"),
                  decl.has_error ? NodeFlagHasError : NodeFlagNone),
        std::move(decl)};
}

std::optional<Parser::ParsedDecl>
Parser::try_parse_member_class_explicit_instantiation_declaration(
    size_t begin,
    SrcLoc extern_loc,
    SrcLoc template_loc) {
    if (!(check(TokenType::STRUCT) || check(TokenType::CLASS) ||
          check(TokenType::UNION))) {
        return std::nullopt;
    }

    TentativeParsingAction tentative(*this, TentativeMode::CollectBacked);
    ParserCheckpoint checkpoint = capture_parser_checkpoint();
    size_t saved_cursor = cursor_;
    size_t saved_last_end = last_consumed_raw_end_;

    Token class_key = current();
    consume();

    bool has_error = false;
    std::vector<NodeId> children;
    ParsedAttributes leading_attrs = try_parse_attributes();
    children.insert(children.end(),
                    leading_attrs.syntax.begin(),
                    leading_attrs.syntax.end());

    ParsedNestedName nested = parse_nested_name_specifier();
    const cir::File& file = collect_session_.file();
    if (!nested.consumed_any) {
        cursor_ = saved_cursor;
        last_consumed_raw_end_ = saved_last_end;
        restore_parser_checkpoint(checkpoint);
        return std::nullopt;
    }
    if (nested.has_error || !nested.scope.context.valid() ||
        file.decl_context(nested.scope.context).kind !=
            cir::DeclContextKind::Record) {
        diagnose(DiagnosticLevel::Error,
                 "member class explicit instantiation declaration qualifier does not name a class",
                 class_key.loc);
        skip_balanced_until_semicolon_or_brace();
        collect::DeclResult decl;
        decl.has_error = true;
        tentative.commit();
        return ParsedDecl{make_node(NodeKind::UnknownDecl,
                                    begin,
                                    last_consumed_raw_end(),
                                    children,
                                    text_payload("extern template"),
                                    NodeFlagHasError),
                          std::move(decl)};
    }

    bool has_template_keyword = false;
    if (match(TokenType::TEMPLATE)) {
        has_template_keyword = true;
    }

    Token name_token = current();
    if (!is_identifier_token(name_token.type)) {
        diagnose(DiagnosticLevel::Error,
                 "expected member class name in explicit instantiation declaration",
                 current_loc());
        skip_balanced_until_semicolon_or_brace();
        collect::DeclResult decl;
        decl.has_error = true;
        tentative.commit();
        return ParsedDecl{make_node(NodeKind::UnknownDecl,
                                    begin,
                                    last_consumed_raw_end(),
                                    children,
                                    text_payload("extern template"),
                                    NodeFlagHasError),
                          std::move(decl)};
    }
    consume();

    const collect::Session::TemplateInfo* primary = nullptr;
    cir::EntityId member_record;
    std::vector<collect::Session::TemplateArgument> arguments;
    bool terminal_template_id = check(TokenType::LESS_THAN);
    if (terminal_template_id) {
        const cir::Binding* binding =
            file.lookup_template_name_binding(nested.scope.context,
                                              name_token.value,
                                              /*include_parents=*/false);
        if (binding) {
            for (auto it = binding->entities.rbegin();
                 it != binding->entities.rend();
                 ++it) {
                const collect::Session::TemplateInfo* candidate =
                    collect_session_.template_info(*it);
                if (candidate && candidate->is_class_template) {
                    primary = candidate;
                    break;
                }
            }
        }
        if (!primary) {
            diagnose(DiagnosticLevel::Error,
                     "no matching member class template for explicit instantiation declaration",
                     name_token.loc);
            if (!parse_dependent_expression_template_argument_list(
                    name_token.loc)) {
                skip_balanced_until_semicolon_or_brace();
            }
            has_error = true;
        } else if (!parse_and_canonicalize_template_argument_list(
                       *primary,
                       arguments,
                       name_token.loc)) {
            has_error = true;
        }
        bool prior_explicit_specialization =
            primary && primary->is_class_template && !has_error &&
            collect_session_.explicit_template_specialization_declared(
                *primary, arguments);
        if (primary && primary->is_class_template &&
            !primary->has_definition && !prior_explicit_specialization) {
            diagnose(DiagnosticLevel::Error,
                     "explicit instantiation declaration requires a member class template definition",
                     name_token.loc);
            has_error = true;
        }
        if (primary && primary->is_class_template &&
            !prior_explicit_specialization) {
            SrcLoc prior_definition_loc;
            if (collect_session_.explicit_instantiation_definition_declared(
                    *primary,
                    arguments,
                    &prior_definition_loc)) {
                diagnose(DiagnosticLevel::Error,
                         "explicit instantiation declaration must precede explicit instantiation definition",
                         name_token.loc);
                if (!prior_definition_loc.isInvalid()) {
                    diagnose(DiagnosticLevel::Note,
                             "explicit instantiation definition is here",
                             prior_definition_loc);
                }
                has_error = true;
            }
        }
    } else {
        if (has_template_keyword) {
            diagnose(DiagnosticLevel::Error,
                     "template disambiguator requires a template argument list",
                     name_token.loc);
            has_error = true;
        }
        cir::EntityId owner = nested.scope.entity;
        if (!owner.valid() || !file.valid(owner) ||
            !file.template_specialization(owner)) {
            diagnose(DiagnosticLevel::Error,
                     "member class explicit instantiation declaration must name a member of a class template specialization",
                     name_token.loc);
            has_error = true;
        }
        cir::TypeId member_type =
            collect_session_.lookup_qualified_type_name_checked(
                nested.scope.context, name_token.value, name_token.loc);
        if (!member_type.valid()) {
            diagnose(DiagnosticLevel::Error,
                     "no matching member class for explicit instantiation declaration",
                     name_token.loc);
            has_error = true;
        } else {
            member_record =
                file.record_entity(file.resolved_type(member_type));
            if (!member_record.valid() || !file.valid(member_record) ||
                file.entity(member_record).kind != cir::EntityKind::Record) {
                diagnose(DiagnosticLevel::Error,
                         "explicit instantiation declaration does not name a member class",
                         name_token.loc);
                has_error = true;
            } else {
                (void)collect_session_.request_class_member_instantiation(
                    member_record,
                    cir::InstantiationDemandKind::CompleteClass,
                    name_token.loc);
            }
            if (!has_error && member_record.valid()) {
                if (const cir::RecordFacts* facts =
                           file.record_facts(member_record);
                       (!facts || facts->is_incomplete) &&
                       !collect_session_.is_explicit_template_specialization(
                           member_record)) {
                    diagnose(DiagnosticLevel::Error,
                             "explicit instantiation declaration requires a member class definition",
                             name_token.loc);
                    has_error = true;
                }
            }
        }
        if (member_record.valid() &&
            !collect_session_.is_explicit_template_specialization(
                member_record)) {
            SrcLoc prior_definition_loc;
            if (collect_session_.explicit_entity_instantiation_definition_declared(
                    member_record,
                    &prior_definition_loc)) {
                diagnose(DiagnosticLevel::Error,
                         "explicit instantiation declaration must precede explicit instantiation definition",
                         name_token.loc);
                if (!prior_definition_loc.isInvalid()) {
                    diagnose(DiagnosticLevel::Note,
                             "explicit instantiation definition is here",
                             prior_definition_loc);
                }
                has_error = true;
            }
        }
    }

    ParsedAttributes trailing_attrs = try_parse_attributes();
    children.insert(children.end(),
                    trailing_attrs.syntax.begin(),
                    trailing_attrs.syntax.end());
    AttributeList explicit_instantiation_attrs = leading_attrs.attrs;
    explicit_instantiation_attrs.append(trailing_attrs.attrs);
    if (has_forbidden_explicit_instantiation_attributes(
            explicit_instantiation_attrs)) {
        diagnose(DiagnosticLevel::Error,
                 "attributes cannot appertain to an explicit instantiation",
                 leading_attrs.attrs.empty() ? class_key.loc : extern_loc);
        has_error = true;
    }

    if (match(TokenType::COMMA)) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation declaration may only declare one entity",
                 last_consumed_loc());
        skip_until_statement_boundary();
        has_error = true;
    } else if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ';' after explicit instantiation declaration",
                 current_loc());
        skip_until_statement_boundary();
        has_error = true;
    }

    collect::DeclResult decl;
    decl.has_error = has_error;
    if (primary && primary->is_class_template && !has_error) {
        if (!collect_session_.declare_explicit_instantiation_declaration(
                *primary,
                arguments,
                template_loc,
                explicit_instantiation_attrs)) {
            has_error = true;
            decl.has_error = true;
        } else {
            cir::EntityId cached = collect_session_.cached_instantiation(
                collect_session_.template_memo_key(primary->entity, arguments));
            collect_session_
                .apply_explicit_instantiation_declaration_suppression(
                    cached,
                    *primary,
                    arguments);
            collect_session_
                .apply_class_explicit_instantiation_declaration_suppression(
                    cached,
                    *primary,
                    arguments);
        }
    } else if (member_record.valid() && !has_error) {
        if (!collect_session_.declare_explicit_entity_instantiation_declaration(
                member_record,
                template_loc,
                explicit_instantiation_attrs)) {
            has_error = true;
            decl.has_error = true;
        }
    }

    tentative.commit();
    return ParsedDecl{
        make_node(has_error ? NodeKind::UnknownDecl : NodeKind::RecordDecl,
                  begin,
                  last_consumed_raw_end(),
                  children,
                  text_payload("extern template"),
                  has_error ? NodeFlagHasError : NodeFlagNone),
        std::move(decl)};
}

std::optional<Parser::ParsedDecl>
Parser::try_parse_member_class_explicit_instantiation_definition(
    size_t begin,
    SrcLoc template_loc) {
    if (!(check(TokenType::STRUCT) || check(TokenType::CLASS) ||
          check(TokenType::UNION))) {
        return std::nullopt;
    }

    TentativeParsingAction tentative(*this, TentativeMode::CollectBacked);
    ParserCheckpoint checkpoint = capture_parser_checkpoint();
    size_t saved_cursor = cursor_;
    size_t saved_last_end = last_consumed_raw_end_;

    Token class_key = current();
    consume();

    bool has_error = false;
    std::vector<NodeId> children;
    ParsedAttributes leading_attrs = try_parse_attributes();
    children.insert(children.end(),
                    leading_attrs.syntax.begin(),
                    leading_attrs.syntax.end());

    ParsedNestedName nested = parse_nested_name_specifier();
    const cir::File& file = collect_session_.file();
    if (!nested.consumed_any) {
        cursor_ = saved_cursor;
        last_consumed_raw_end_ = saved_last_end;
        restore_parser_checkpoint(checkpoint);
        return std::nullopt;
    }
    if (nested.has_error || !nested.scope.context.valid() ||
        file.decl_context(nested.scope.context).kind !=
            cir::DeclContextKind::Record) {
        diagnose(DiagnosticLevel::Error,
                 "member class explicit instantiation definition qualifier does not name a class",
                 class_key.loc);
        skip_balanced_until_semicolon_or_brace();
        collect::DeclResult decl;
        decl.has_error = true;
        tentative.commit();
        return ParsedDecl{make_node(NodeKind::UnknownDecl,
                                    begin,
                                    last_consumed_raw_end(),
                                    children,
                                    text_payload("template"),
                                    NodeFlagHasError),
                          std::move(decl)};
    }

    bool has_template_keyword = false;
    if (match(TokenType::TEMPLATE)) {
        has_template_keyword = true;
    }

    Token name_token = current();
    if (!is_identifier_token(name_token.type)) {
        diagnose(DiagnosticLevel::Error,
                 "expected member class name in explicit instantiation definition",
                 current_loc());
        skip_balanced_until_semicolon_or_brace();
        collect::DeclResult decl;
        decl.has_error = true;
        tentative.commit();
        return ParsedDecl{make_node(NodeKind::UnknownDecl,
                                    begin,
                                    last_consumed_raw_end(),
                                    children,
                                    text_payload("template"),
                                    NodeFlagHasError),
                          std::move(decl)};
    }
    consume();

    const collect::Session::TemplateInfo* primary = nullptr;
    cir::EntityId member_record;
    std::vector<collect::Session::TemplateArgument> arguments;
    bool terminal_template_id = check(TokenType::LESS_THAN);
    if (terminal_template_id) {
        const cir::Binding* binding =
            file.lookup_template_name_binding(nested.scope.context,
                                              name_token.value,
                                              /*include_parents=*/false);
        if (binding) {
            for (auto it = binding->entities.rbegin();
                 it != binding->entities.rend();
                 ++it) {
                const collect::Session::TemplateInfo* candidate =
                    collect_session_.template_info(*it);
                if (candidate && candidate->is_class_template) {
                    primary = candidate;
                    break;
                }
            }
        }
        if (!primary) {
            diagnose(DiagnosticLevel::Error,
                     "no matching member class template for explicit instantiation definition",
                     name_token.loc);
            if (!parse_dependent_expression_template_argument_list(
                    name_token.loc)) {
                skip_balanced_until_semicolon_or_brace();
            }
            has_error = true;
        } else if (!parse_and_canonicalize_template_argument_list(
                       *primary,
                       arguments,
                       name_token.loc)) {
            has_error = true;
        }
        bool prior_explicit_specialization =
            primary && primary->is_class_template && !has_error &&
            collect_session_.explicit_template_specialization_declared(
                *primary, arguments);
        if (primary && primary->is_class_template &&
            !primary->has_definition && !prior_explicit_specialization) {
            diagnose(DiagnosticLevel::Error,
                     "explicit instantiation definition requires a member class template definition",
                     name_token.loc);
            has_error = true;
        }
        if (primary && primary->is_class_template &&
            !prior_explicit_specialization) {
            SrcLoc prior_definition_loc;
            if (collect_session_.explicit_instantiation_definition_declared(
                    *primary,
                    arguments,
                    &prior_definition_loc)) {
                diagnose(DiagnosticLevel::Error,
                         "redefinition of explicit member class template instantiation",
                         name_token.loc);
                if (!prior_definition_loc.isInvalid()) {
                    diagnose(DiagnosticLevel::Note,
                             "previous explicit instantiation definition is here",
                             prior_definition_loc);
                }
                has_error = true;
            }
        }
    } else {
        if (has_template_keyword) {
            diagnose(DiagnosticLevel::Error,
                     "template disambiguator requires a template argument list",
                     name_token.loc);
            has_error = true;
        }
        cir::EntityId owner = nested.scope.entity;
        if (!owner.valid() || !file.valid(owner) ||
            !file.template_specialization(owner)) {
            diagnose(DiagnosticLevel::Error,
                     "member class explicit instantiation definition must name a member of a class template specialization",
                     name_token.loc);
            has_error = true;
        }
        cir::TypeId member_type =
            collect_session_.lookup_qualified_type_name_checked(
                nested.scope.context, name_token.value, name_token.loc);
        if (!member_type.valid()) {
            diagnose(DiagnosticLevel::Error,
                     "no matching member class for explicit instantiation definition",
                     name_token.loc);
            has_error = true;
        } else {
            member_record =
                file.record_entity(file.resolved_type(member_type));
            if (!member_record.valid() || !file.valid(member_record) ||
                file.entity(member_record).kind != cir::EntityKind::Record) {
                diagnose(DiagnosticLevel::Error,
                         "explicit instantiation definition does not name a member class",
                         name_token.loc);
                has_error = true;
            } else {
                (void)collect_session_.request_class_member_instantiation(
                    member_record,
                    cir::InstantiationDemandKind::CompleteClass,
                    name_token.loc);
            }
            if (!has_error && member_record.valid()) {
                if (const cir::RecordFacts* facts =
                           file.record_facts(member_record);
                       (!facts || facts->is_incomplete) &&
                       !collect_session_.is_explicit_template_specialization(
                           member_record)) {
                    diagnose(DiagnosticLevel::Error,
                             "explicit instantiation definition requires a member class definition",
                             name_token.loc);
                    has_error = true;
                }
            }
        }
        if (member_record.valid() &&
            !collect_session_.is_explicit_template_specialization(
                member_record)) {
            SrcLoc prior_definition_loc;
            if (collect_session_.explicit_entity_instantiation_definition_declared(
                    member_record,
                    &prior_definition_loc)) {
                diagnose(DiagnosticLevel::Error,
                         "redefinition of explicit member class instantiation",
                         name_token.loc);
                if (!prior_definition_loc.isInvalid()) {
                    diagnose(DiagnosticLevel::Note,
                             "previous explicit instantiation definition is here",
                             prior_definition_loc);
                }
                has_error = true;
            }
        }
    }

    ParsedAttributes trailing_attrs = try_parse_attributes();
    children.insert(children.end(),
                    trailing_attrs.syntax.begin(),
                    trailing_attrs.syntax.end());
    AttributeList explicit_instantiation_attrs = leading_attrs.attrs;
    explicit_instantiation_attrs.append(trailing_attrs.attrs);
    if (has_forbidden_explicit_instantiation_attributes(
            explicit_instantiation_attrs)) {
        diagnose(DiagnosticLevel::Error,
                 "attributes cannot appertain to an explicit instantiation",
                 leading_attrs.attrs.empty() ? class_key.loc : template_loc);
        has_error = true;
    }

    if (match(TokenType::COMMA)) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation definition may only declare one entity",
                 last_consumed_loc());
        skip_until_statement_boundary();
        has_error = true;
    } else if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ';' after explicit instantiation definition",
                 current_loc());
        skip_until_statement_boundary();
        has_error = true;
    }

    collect::DeclResult decl;
    decl.has_error = has_error;
    if (primary && primary->is_class_template && !has_error) {
        cir::EntityId prior_specialization;
        if (collect_session_.explicit_template_specialization_declared(
                *primary, arguments, &prior_specialization)) {
            decl.entity = prior_specialization;
            tentative.commit();
            return ParsedDecl{
                make_node(NodeKind::RecordDecl,
                          begin,
                          last_consumed_raw_end(),
                          children,
                          text_payload("template"),
                          NodeFlagNone),
                std::move(decl)};
        }
        collect_session_.declare_explicit_instantiation_definition(
            *primary,
            arguments,
            template_loc,
            explicit_instantiation_attrs);
        cir::EntityId instantiated =
            instantiate_template_with_args(*primary,
                                           arguments,
                                           template_loc);
        decl.entity = instantiated;
        if (!instantiated.valid()) {
            decl.has_error = true;
        } else {
            collect_session_.apply_explicit_instantiation_definition_emission(
                instantiated,
                *primary,
                arguments);
            force_class_explicit_instantiation_definition_members(
                instantiated,
                template_loc);
        }
    } else if (member_record.valid() && !has_error) {
        if (collect_session_.is_explicit_template_specialization(
                member_record)) {
            decl.entity = member_record;
            tentative.commit();
            return ParsedDecl{
                make_node(NodeKind::RecordDecl,
                          begin,
                          last_consumed_raw_end(),
                          children,
                          text_payload("template"),
                          NodeFlagNone),
                std::move(decl)};
        }
        collect_session_.declare_explicit_entity_instantiation_definition(
            member_record,
            template_loc,
            explicit_instantiation_attrs);
        collect_session_.apply_record_explicit_instantiation_definition_emission(
            member_record);
        force_class_explicit_instantiation_definition_members(member_record,
                                                              template_loc);
        collect_session_.apply_record_explicit_instantiation_definition_emission(
            member_record);
        decl.entity = member_record;
    }

    tentative.commit();
    return ParsedDecl{
        make_node(decl.has_error ? NodeKind::UnknownDecl : NodeKind::RecordDecl,
                  begin,
                  last_consumed_raw_end(),
                  children,
                  text_payload("template"),
                  decl.has_error ? NodeFlagHasError : NodeFlagNone),
        std::move(decl)};
}

std::optional<Parser::ParsedDecl>
Parser::try_parse_conversion_function_template_explicit_instantiation(
    size_t begin,
    SrcLoc introducer_loc,
    SrcLoc template_loc,
    bool is_declaration) {
    if (!starts_qualified_conversion_function_id()) {
        return std::nullopt;
    }

    TentativeParsingAction tentative(*this, TentativeMode::CollectBacked);
    std::optional<ParsedConversionFunctionDeclarator> parsed =
        parse_conversion_function_declarator(/*require_qualified=*/true);
    if (!parsed) {
        return std::nullopt;
    }

    ParsedDeclarator declarator = std::move(parsed->declarator);
    std::vector<NodeId> children;
    if (parsed->target_syntax != InvalidNodeId) {
        children.push_back(parsed->target_syntax);
    }
    if (declarator.syntax != InvalidNodeId) {
        children.push_back(declarator.syntax);
    }
    bool has_error = parsed->has_error;

    const cir::File& file = collect_session_.file();
    const cir::RecordFacts* facts = nullptr;
    if (declarator.qualified_context.valid() &&
        file.valid(declarator.qualified_context) &&
        file.decl_context(declarator.qualified_context).kind ==
            cir::DeclContextKind::Record) {
        facts = file.record_facts(
            file.decl_context(declarator.qualified_context).owner);
    }

    struct ConversionInstantiationMatch {
        const collect::Session::TemplateInfo* info = nullptr;
        std::vector<collect::Session::TemplateArgument> arguments;
        uint64_t point_lookup_generation = 0;
    };
    std::vector<ConversionInstantiationMatch> matches;
    if (facts) {
        for (const cir::RecordMethodFact& method : facts->methods) {
            if (!method.is_conversion_function ||
                !method.is_function_template) {
                continue;
            }
            const collect::Session::TemplateInfo* candidate =
                collect_session_.template_info(method.entity);
            if (!candidate) {
                continue;
            }
            std::vector<collect::Session::TemplateArgument> deduced;
            collect::Session::PatternInstantiationCallbacks callbacks;
            configure_pattern_instantiation_callbacks(callbacks,
                                                        declarator.loc);
            if (deduce_function_template_declaration_match(
                    *candidate,
                    declarator.type,
                    deduced,
                    nullptr,
                    callbacks,
                    declarator.loc,
                    !declarator.has_noexcept_specifier)) {
                matches.push_back(ConversionInstantiationMatch{
                    candidate,
                    std::move(deduced),
                    callbacks.point_lookup_generation});
            }
        }
    }

    ConversionInstantiationMatch selected;
    if (matches.empty()) {
        diagnose(
            DiagnosticLevel::Error,
            is_declaration
                ? "no matching conversion function template for explicit instantiation declaration"
                : "no matching conversion function template for explicit instantiation definition",
            declarator.loc);
        has_error = true;
    } else {
        auto more_specialized = [&](size_t lhs, size_t rhs) {
            return collect_session_.function_template_more_specialized(
                *matches[lhs].info,
                *matches[rhs].info,
                collect::Session::FunctionTemplateOrderingContext::declaration());
        };
        size_t best = 0;
        for (size_t index = 1; index < matches.size(); ++index) {
            if (more_specialized(index, best)) {
                best = index;
            }
        }
        bool ambiguous = false;
        for (size_t index = 0; index < matches.size(); ++index) {
            if (index != best && !more_specialized(best, index)) {
                ambiguous = true;
                break;
            }
        }
        if (ambiguous) {
            diagnose(
                DiagnosticLevel::Error,
                is_declaration
                    ? "ambiguous explicit conversion function template instantiation declaration"
                    : "ambiguous explicit conversion function template instantiation definition",
                declarator.loc);
            has_error = true;
        } else {
            selected = std::move(matches[best]);
        }
    }

    cir::EntityId explicit_specialization;
    bool is_explicit_specialization =
        selected.info &&
        collect_session_.explicit_template_specialization_declared(
            *selected.info,
            selected.arguments,
            &explicit_specialization);
    if (selected.info && !is_explicit_specialization) {
        SrcLoc prior_definition_loc;
        if (is_declaration &&
            collect_session_.explicit_instantiation_definition_declared(
                *selected.info,
                selected.arguments,
                &prior_definition_loc)) {
            diagnose(
                DiagnosticLevel::Error,
                "explicit instantiation declaration must precede explicit instantiation definition",
                declarator.loc);
            if (!prior_definition_loc.isInvalid()) {
                diagnose(DiagnosticLevel::Note,
                         "explicit instantiation definition is here",
                         prior_definition_loc);
            }
            has_error = true;
        } else if (!is_declaration && !selected.info->has_definition) {
            diagnose(
                DiagnosticLevel::Error,
                "explicit instantiation definition requires a conversion function template definition",
                declarator.loc);
            has_error = true;
        } else if (!is_declaration &&
                   collect_session_.explicit_instantiation_definition_declared(
                       *selected.info,
                       selected.arguments,
                       &prior_definition_loc)) {
            diagnose(
                DiagnosticLevel::Error,
                "redefinition of explicit conversion function template instantiation",
                declarator.loc);
            if (!prior_definition_loc.isInvalid()) {
                diagnose(DiagnosticLevel::Note,
                         "previous explicit instantiation definition is here",
                         prior_definition_loc);
            }
            has_error = true;
        }
    }

    if (has_forbidden_explicit_instantiation_attributes(
            declarator.attrs)) {
        diagnose(DiagnosticLevel::Error,
                 "attributes cannot appertain to an explicit instantiation",
                 introducer_loc);
        has_error = true;
    }
    if (check(TokenType::LEFT_BRACE)) {
        diagnose(
            DiagnosticLevel::Error,
            is_declaration
                ? "explicit instantiation declaration cannot be a function definition"
                : "explicit instantiation definition cannot be a function definition",
            current_loc());
        skip_balanced_until_semicolon_or_brace();
        has_error = true;
    } else if (match(TokenType::COMMA)) {
        diagnose(
            DiagnosticLevel::Error,
            is_declaration
                ? "explicit instantiation declaration may only declare one entity"
                : "explicit instantiation definition may only declare one entity",
            last_consumed_loc());
        skip_until_statement_boundary();
        has_error = true;
    } else if (!match(TokenType::SEMICOLON)) {
        diagnose(
            DiagnosticLevel::Error,
            is_declaration
                ? "expected ';' after explicit instantiation declaration"
                : "expected ';' after explicit instantiation definition",
            current_loc());
        skip_until_statement_boundary();
        has_error = true;
    }

    collect::DeclResult decl;
    decl.type = declarator.type;
    decl.has_error = has_error;
    if (selected.info && !has_error) {
        if (is_explicit_specialization) {
            decl.entity = explicit_specialization;
        } else if (is_declaration) {
            if (!collect_session_.declare_explicit_instantiation_declaration(
                    *selected.info,
                    selected.arguments,
                    template_loc,
                    declarator.attrs)) {
                decl.has_error = true;
            }
        } else {
            collect_session_.declare_explicit_instantiation_definition(
                *selected.info,
                selected.arguments,
                template_loc,
                declarator.attrs);
            cir::EntityId instantiated = instantiate_template_with_args(
                *selected.info,
                selected.arguments,
                template_loc,
                selected.point_lookup_generation);
            collect_session_.apply_explicit_instantiation_definition_emission(
                instantiated,
                *selected.info,
                selected.arguments);
            decl.entity = instantiated;
            if (!instantiated.valid()) {
                decl.has_error = true;
            }
        }
    }

    tentative.commit();
    std::string_view payload =
        is_declaration ? "extern template conversion"
                       : "template conversion";
    return ParsedDecl{
        make_node(decl.has_error ? NodeKind::UnknownDecl
                                 : NodeKind::FunctionDecl,
                  begin,
                  last_consumed_raw_end(),
                  children,
                  text_payload(payload),
                  decl.has_error ? NodeFlagHasError : NodeFlagNone),
        std::move(decl)};
}

std::optional<Parser::ParsedDecl>
Parser::try_parse_function_template_explicit_instantiation_declaration(
    size_t begin,
    SrcLoc extern_loc,
    SrcLoc template_loc) {
    TentativeParsingAction tentative(*this, TentativeMode::CollectBacked);
    ParserCheckpoint checkpoint = capture_parser_checkpoint();
    size_t saved_cursor = cursor_;
    size_t saved_last_end = last_consumed_raw_end_;

    DeclarationParser declaration_parser(
        *this,
        TypeParseContext::type_only(
            TypeParseContext::Origin::NamespaceDeclSpecifier));
    collect::Session::TemplateReplayOutcome declarator_replay_outcome;
    cir::TypeRef base;
    ParsedDeclarator declarator;
    {
        ExplicitInstantiationReplayOutcomeScope replay_outcome_scope(
            collect_session_,
            declarator_replay_outcome);
        base = declaration_parser.parse_declaration(false, true);
        declarator = declaration_parser.parse_declarator(base, false);
    }
    if (declarator_replay_outcome.hard_error() ||
        declarator_replay_outcome.unavailable()) {
        if (declarator_replay_outcome.unavailable()) {
            diagnose(
                DiagnosticLevel::Error,
                "explicit instantiation declaration owner is unavailable",
                declarator.loc.isInvalid() ? extern_loc : declarator.loc);
        }
        skip_balanced_until_semicolon_or_brace();
        collect::DeclResult decl;
        decl.has_error = true;
        tentative.commit();
        return ParsedDecl{
            make_node(NodeKind::UnknownDecl,
                      begin,
                      last_consumed_raw_end(),
                      {},
                      text_payload("extern template"),
                      NodeFlagHasError),
            std::move(decl)};
    }
    if (!declarator.has_name) {
        cursor_ = saved_cursor;
        last_consumed_raw_end_ = saved_last_end;
        restore_parser_checkpoint(checkpoint);
        return std::nullopt;
    }

    std::vector<NodeId> children;
    if (declaration_parser.type_syntax != InvalidNodeId) {
        children.push_back(declaration_parser.type_syntax);
    }
    if (declarator.syntax != InvalidNodeId) {
        children.push_back(declarator.syntax);
    }

    auto explicit_template_id_is_followed_by_parameter_list = [&]() {
        if (!check(TokenType::LESS_THAN)) {
            return false;
        }
        int angle_depth = 0;
        size_t offset = 0;
        while (true) {
            TokenType type = peek(offset).type;
            if (type == TokenType::Eof || type == TokenType::SEMICOLON ||
                type == TokenType::LEFT_BRACE) {
                return false;
            }
            if (type == TokenType::LESS_THAN) {
                ++angle_depth;
            } else if (type == TokenType::GREATER_THAN) {
                --angle_depth;
                if (angle_depth == 0) {
                    return peek(offset + 1).type == TokenType::LEFT_PAREN;
                }
            } else if (type == TokenType::RIGHT_SHIFT) {
                if (angle_depth <= 2) {
                    return peek(offset + 1).type == TokenType::LEFT_PAREN;
                }
                angle_depth -= 2;
            }
            ++offset;
        }
    };

    std::vector<const collect::Session::TemplateInfo*> candidates =
        collect_session_.function_template_infos_for_name(
            declarator.qualified_context,
            declarator.name,
            !declarator.qualified_context.valid());

    bool has_explicit_template_arguments = false;
    std::vector<collect::Session::TemplateArgument> explicit_arguments;
    std::vector<collect::CandidateExplicitTemplateArguments>
        candidate_explicit_arguments;
    if (check(TokenType::LESS_THAN)) {
        if (!explicit_template_id_is_followed_by_parameter_list()) {
            cursor_ = saved_cursor;
            last_consumed_raw_end_ = saved_last_end;
            restore_parser_checkpoint(checkpoint);
            return std::nullopt;
        }
        has_explicit_template_arguments = true;
        bool parsed_arguments = false;
        if (!candidates.empty()) {
            parsed_arguments =
                parse_function_template_argument_list_for_candidates(
                    *candidates.front(),
                    candidates,
                    explicit_arguments,
                    candidate_explicit_arguments,
                    declarator.loc);
        } else {
            parsed_arguments =
                parse_dependent_expression_template_argument_list(
                    declarator.loc);
        }
        if (!parsed_arguments) {
            collect::DeclResult decl;
            decl.has_error = true;
            skip_balanced_until_semicolon_or_brace();
            tentative.commit();
            return ParsedDecl{make_node(NodeKind::UnknownDecl,
                                        begin,
                                        last_consumed_raw_end(),
                                        children,
                                        text_payload("extern template"),
                                        NodeFlagHasError),
                              std::move(decl)};
        }

        ParsedDeclarator suffix =
            declaration_parser.parse_declarator(declarator.type_ref, true);
        if (suffix.syntax != InvalidNodeId) {
            children.push_back(suffix.syntax);
        }
        if (!suffix.is_function) {
            cursor_ = saved_cursor;
            last_consumed_raw_end_ = saved_last_end;
            restore_parser_checkpoint(checkpoint);
            return std::nullopt;
        }
        declarator.type = suffix.type;
        declarator.type_ref = suffix.type_ref;
        declarator.is_function = suffix.is_function;
        declarator.is_variadic = suffix.is_variadic;
        declarator.has_prototype = suffix.has_prototype;
        declarator.is_kr_style = suffix.is_kr_style;
        declarator.has_trailing_return_type =
            suffix.has_trailing_return_type;
        declarator.has_noexcept_specifier =
            suffix.has_noexcept_specifier;
        declarator.has_unsupported_semantics =
            declarator.has_unsupported_semantics ||
            suffix.has_unsupported_semantics;
        declarator.kr_param_names = std::move(suffix.kr_param_names);
        declarator.params = std::move(suffix.params);
        declarator.vla_bounds =
            collect_session_.chain(std::move(declarator.vla_bounds),
                                   std::move(suffix.vla_bounds),
                                   declarator.loc);
        declarator.attrs.append(std::move(suffix.attrs));
    } else if (!declarator.is_function) {
        cursor_ = saved_cursor;
        last_consumed_raw_end_ = saved_last_end;
        restore_parser_checkpoint(checkpoint);
        return std::nullopt;
    }

    ParsedAttributes trailing_attrs = try_parse_attributes();
    declarator.attrs.append(std::move(trailing_attrs.attrs));
    children.insert(children.end(),
                    trailing_attrs.syntax.begin(),
                    trailing_attrs.syntax.end());

    const cir::File& file = collect_session_.file();
    bool record_qualified =
        declarator.qualified_context.valid() &&
        file.decl_context(declarator.qualified_context).kind ==
            cir::DeclContextKind::Record;
    bool try_direct_member_instantiation =
        record_qualified && !has_explicit_template_arguments;
    bool has_error = false;
    cir::EntityId selected_member;
    bool direct_member_owner_is_class_template_specialization = false;
    if (try_direct_member_instantiation) {
        cir::EntityId owner =
            file.decl_context(declarator.qualified_context).owner;
        direct_member_owner_is_class_template_specialization =
            owner.valid() && file.valid(owner) &&
            file.template_specialization(owner);
        if (direct_member_owner_is_class_template_specialization) {
            selected_member = collect_session_.corresponding_record_method(
                declarator.qualified_context,
                declarator.name,
                collect_session_.type_ref(declarator.type),
                !declarator.has_noexcept_specifier);
        }
    }

    struct Match {
        const collect::Session::TemplateInfo* info = nullptr;
        std::vector<collect::Session::TemplateArgument> arguments;
        uint64_t point_lookup_generation = 0;
    };
    std::vector<Match> matches;
    if (!selected_member.valid()) {
        for (const collect::Session::TemplateInfo* candidate : candidates) {
            const std::vector<collect::Session::TemplateArgument>*
                candidate_arguments = &explicit_arguments;
            auto replayed = std::find_if(
                candidate_explicit_arguments.begin(),
                candidate_explicit_arguments.end(),
                [&](const collect::CandidateExplicitTemplateArguments&
                        entry) {
                    return entry.template_entity == candidate->entity;
                });
            if (replayed != candidate_explicit_arguments.end()) {
                if (!replayed->viable) {
                    continue;
                }
                candidate_arguments = &replayed->arguments;
            }
            std::vector<collect::Session::TemplateArgument> deduced;
            collect::Session::PatternInstantiationCallbacks callbacks;
            configure_pattern_instantiation_callbacks(callbacks, declarator.loc);
            if (deduce_function_template_declaration_match(
                    *candidate,
                    declarator.type,
                    deduced,
                    has_explicit_template_arguments ? candidate_arguments
                                                    : nullptr,
                    callbacks,
                    declarator.loc,
                    !declarator.has_noexcept_specifier)) {
                matches.push_back(Match{candidate,
                                        std::move(deduced),
                                        callbacks.point_lookup_generation});
            }
        }
    }

    auto more_specialized = [&](const Match& lhs, const Match& rhs) {
        if (!lhs.info || !rhs.info) {
            return false;
        }
        return collect_session_.function_template_more_specialized(*lhs.info,
                                                                   *rhs.info,
                                                                   collect::Session::FunctionTemplateOrderingContext::declaration());
    };
    auto diagnose_ambiguous_match_notes = [&](const Match& lhs,
                                              const Match& rhs) {
        auto note_candidate = [&](const Match& match) {
            if (match.info && match.info->entity.valid() &&
                collect_session_.file().valid(match.info->entity)) {
                diagnose(DiagnosticLevel::Note,
                         "candidate function template declared here",
                         collect_session_.file().entity(match.info->entity).loc);
            }
        };
        note_candidate(lhs);
        note_candidate(rhs);
        if (lhs.info && rhs.info &&
            collect_session_.function_template_unordered_constraints_tie(
                *lhs.info,
                *rhs.info,
                collect::Session::FunctionTemplateOrderingContext::declaration())) {
            diagnose(
                DiagnosticLevel::Note,
                "candidate associated constraints are not ordered by subsumption",
                declarator.loc);
        }
    };

    Match selected;
    if (selected_member.valid()) {

    } else if (matches.empty()) {
        if (try_direct_member_instantiation && candidates.empty()) {
            if (!direct_member_owner_is_class_template_specialization) {
                diagnose(DiagnosticLevel::Error,
                         "member function explicit instantiation declaration must name a member of a class template specialization",
                         declarator.loc);
            } else {
                diagnose(DiagnosticLevel::Error,
                         "no matching member function for explicit instantiation declaration",
                         declarator.loc);
            }
        } else {
            diagnose(DiagnosticLevel::Error,
                     "no matching function template for explicit instantiation declaration",
                     declarator.loc);
        }
        has_error = true;
    } else {
        size_t best = 0;
        for (size_t i = 1; i < matches.size(); ++i) {
            if (more_specialized(matches[i], matches[best])) {
                best = i;
            }
        }
        std::optional<size_t> ambiguous_index;
        for (size_t i = 0; i < matches.size(); ++i) {
            if (i != best && !more_specialized(matches[best], matches[i])) {
                ambiguous_index = i;
                break;
            }
        }
        if (ambiguous_index.has_value()) {
            diagnose(DiagnosticLevel::Error,
                     "ambiguous explicit function template instantiation declaration",
                     declarator.loc);
            diagnose_ambiguous_match_notes(matches[best],
                                           matches[*ambiguous_index]);
            has_error = true;
        } else {
            selected = std::move(matches[best]);
        }
    }

    bool selected_template_is_explicit_specialization =
        selected.info &&
        collect_session_.explicit_template_specialization_declared(
            *selected.info, selected.arguments);
    bool selected_member_is_explicit_specialization =
        collect_session_.is_explicit_template_specialization(selected_member);
    if (selected.info &&
        !selected_template_is_explicit_specialization) {
        SrcLoc prior_definition_loc;
        if (collect_session_.explicit_instantiation_definition_declared(
                *selected.info,
                selected.arguments,
                &prior_definition_loc)) {
            diagnose(DiagnosticLevel::Error,
                     "explicit instantiation declaration must precede explicit instantiation definition",
                     declarator.loc);
            if (!prior_definition_loc.isInvalid()) {
                diagnose(DiagnosticLevel::Note,
                         "explicit instantiation definition is here",
                         prior_definition_loc);
            }
            has_error = true;
        }
    }
    if (selected_member.valid() &&
        !selected_member_is_explicit_specialization) {
        SrcLoc prior_definition_loc;
        if (collect_session_.explicit_entity_instantiation_definition_declared(
                selected_member,
                &prior_definition_loc)) {
            diagnose(DiagnosticLevel::Error,
                     "explicit instantiation declaration must precede explicit instantiation definition",
                     declarator.loc);
            if (!prior_definition_loc.isInvalid()) {
                diagnose(DiagnosticLevel::Note,
                         "explicit instantiation definition is here",
                         prior_definition_loc);
            }
            has_error = true;
        }
    }

    if (declaration_parser.storage_class != StorageClass::None) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation shall not use a storage class specifier",
                 declaration_parser.begin_loc);
        has_error = true;
    }
    if (declaration_parser.is_inline || declaration_parser.is_constexpr ||
        declaration_parser.is_consteval) {
        diagnose(DiagnosticLevel::Error,
                 "function template explicit instantiation shall not use inline, constexpr, or consteval",
                 declaration_parser.begin_loc);
        has_error = true;
    }
    AttributeList explicit_instantiation_attrs =
        declaration_parser.leading_attrs;
    explicit_instantiation_attrs.append(declarator.attrs);
    if (has_forbidden_explicit_instantiation_attributes(
            explicit_instantiation_attrs)) {
        diagnose(DiagnosticLevel::Error,
                 "attributes cannot appertain to an explicit instantiation",
                 declaration_parser.begin_loc.isInvalid() ? extern_loc
                                                          : declaration_parser.begin_loc);
        has_error = true;
    }
    for (ParsedParam& param : declarator.params) {
        if (param.has_default_argument) {
            diagnose(DiagnosticLevel::Error,
                     "explicit instantiation does not use default function arguments",
                     param.default_argument_loc.isInvalid()
                         ? param.loc
                         : param.default_argument_loc);
            param.has_default_argument = false;
            has_error = true;
        }
    }

    if (check(TokenType::LEFT_BRACE)) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation declaration cannot be a function definition",
                 current_loc());
        skip_balanced_until_semicolon_or_brace();
        has_error = true;
    } else if (match(TokenType::COMMA)) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation declaration may only declare one entity",
                 last_consumed_loc());
        skip_until_statement_boundary();
        has_error = true;
    } else if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ';' after explicit instantiation declaration",
                 current_loc());
        skip_until_statement_boundary();
        has_error = true;
    }

    collect::DeclResult decl;
    decl.has_error = has_error;
    if (selected.info && !has_error) {
        if (!collect_session_.declare_explicit_instantiation_declaration(
                *selected.info,
                selected.arguments,
                template_loc,
                explicit_instantiation_attrs)) {
            has_error = true;
            decl.has_error = true;
        }
    } else if (selected_member.valid() && !has_error) {
        if (!collect_session_.declare_explicit_entity_instantiation_declaration(
                selected_member,
                template_loc,
                explicit_instantiation_attrs)) {
            has_error = true;
            decl.has_error = true;
        }
    }

    tentative.commit();
    return ParsedDecl{
        make_node(has_error ? NodeKind::UnknownDecl : NodeKind::FunctionDecl,
                  begin,
                  last_consumed_raw_end(),
                  children,
                  text_payload("extern template"),
                  has_error ? NodeFlagHasError : NodeFlagNone),
        std::move(decl)};
}

std::optional<Parser::ParsedDecl>
Parser::try_parse_function_template_explicit_instantiation_definition(
    size_t begin,
    SrcLoc template_loc) {
    TentativeParsingAction tentative(*this, TentativeMode::CollectBacked);
    ParserCheckpoint checkpoint = capture_parser_checkpoint();
    size_t saved_cursor = cursor_;
    size_t saved_last_end = last_consumed_raw_end_;

    DeclarationParser declaration_parser(
        *this,
        TypeParseContext::type_only(
            TypeParseContext::Origin::NamespaceDeclSpecifier));
    collect::Session::TemplateReplayOutcome declarator_replay_outcome;
    cir::TypeRef base;
    ParsedDeclarator declarator;
    {
        ExplicitInstantiationReplayOutcomeScope replay_outcome_scope(
            collect_session_,
            declarator_replay_outcome);
        base = declaration_parser.parse_declaration(false, true);
        declarator = declaration_parser.parse_declarator(base, false);
    }
    if (declarator_replay_outcome.hard_error() ||
        declarator_replay_outcome.unavailable()) {
        if (declarator_replay_outcome.unavailable()) {
            diagnose(
                DiagnosticLevel::Error,
                "explicit instantiation definition owner is unavailable",
                declarator.loc.isInvalid() ? template_loc : declarator.loc);
        }
        skip_balanced_until_semicolon_or_brace();
        collect::DeclResult decl;
        decl.has_error = true;
        tentative.commit();
        return ParsedDecl{
            make_node(NodeKind::UnknownDecl,
                      begin,
                      last_consumed_raw_end(),
                      {},
                      text_payload("template"),
                      NodeFlagHasError),
            std::move(decl)};
    }
    if (!declarator.has_name) {
        cursor_ = saved_cursor;
        last_consumed_raw_end_ = saved_last_end;
        restore_parser_checkpoint(checkpoint);
        return std::nullopt;
    }

    std::vector<NodeId> children;
    if (declaration_parser.type_syntax != InvalidNodeId) {
        children.push_back(declaration_parser.type_syntax);
    }
    if (declarator.syntax != InvalidNodeId) {
        children.push_back(declarator.syntax);
    }

    auto explicit_template_id_is_followed_by_parameter_list = [&]() {
        if (!check(TokenType::LESS_THAN)) {
            return false;
        }
        int angle_depth = 0;
        size_t offset = 0;
        while (true) {
            TokenType type = peek(offset).type;
            if (type == TokenType::Eof || type == TokenType::SEMICOLON ||
                type == TokenType::LEFT_BRACE) {
                return false;
            }
            if (type == TokenType::LESS_THAN) {
                ++angle_depth;
            } else if (type == TokenType::GREATER_THAN) {
                --angle_depth;
                if (angle_depth == 0) {
                    return peek(offset + 1).type == TokenType::LEFT_PAREN;
                }
            } else if (type == TokenType::RIGHT_SHIFT) {
                if (angle_depth <= 2) {
                    return peek(offset + 1).type == TokenType::LEFT_PAREN;
                }
                angle_depth -= 2;
            }
            ++offset;
        }
    };

    std::vector<const collect::Session::TemplateInfo*> candidates =
        collect_session_.function_template_infos_for_name(
            declarator.qualified_context,
            declarator.name,
            !declarator.qualified_context.valid());

    bool has_explicit_template_arguments = false;
    std::vector<collect::Session::TemplateArgument> explicit_arguments;
    std::vector<collect::CandidateExplicitTemplateArguments>
        candidate_explicit_arguments;
    if (check(TokenType::LESS_THAN)) {
        if (!explicit_template_id_is_followed_by_parameter_list()) {
            cursor_ = saved_cursor;
            last_consumed_raw_end_ = saved_last_end;
            restore_parser_checkpoint(checkpoint);
            return std::nullopt;
        }
        has_explicit_template_arguments = true;
        bool parsed_arguments = false;
        if (!candidates.empty()) {
            parsed_arguments =
                parse_function_template_argument_list_for_candidates(
                    *candidates.front(),
                    candidates,
                    explicit_arguments,
                    candidate_explicit_arguments,
                    declarator.loc);
        } else {
            parsed_arguments =
                parse_dependent_expression_template_argument_list(
                    declarator.loc);
        }
        if (!parsed_arguments) {
            collect::DeclResult decl;
            decl.has_error = true;
            skip_balanced_until_semicolon_or_brace();
            tentative.commit();
            return ParsedDecl{make_node(NodeKind::UnknownDecl,
                                        begin,
                                        last_consumed_raw_end(),
                                        children,
                                        text_payload("template"),
                                        NodeFlagHasError),
                              std::move(decl)};
        }

        ParsedDeclarator suffix =
            declaration_parser.parse_declarator(declarator.type_ref, true);
        if (suffix.syntax != InvalidNodeId) {
            children.push_back(suffix.syntax);
        }
        if (!suffix.is_function) {
            cursor_ = saved_cursor;
            last_consumed_raw_end_ = saved_last_end;
            restore_parser_checkpoint(checkpoint);
            return std::nullopt;
        }
        declarator.type = suffix.type;
        declarator.type_ref = suffix.type_ref;
        declarator.is_function = suffix.is_function;
        declarator.is_variadic = suffix.is_variadic;
        declarator.has_prototype = suffix.has_prototype;
        declarator.is_kr_style = suffix.is_kr_style;
        declarator.has_trailing_return_type =
            suffix.has_trailing_return_type;
        declarator.has_noexcept_specifier =
            suffix.has_noexcept_specifier;
        declarator.has_unsupported_semantics =
            declarator.has_unsupported_semantics ||
            suffix.has_unsupported_semantics;
        declarator.kr_param_names = std::move(suffix.kr_param_names);
        declarator.params = std::move(suffix.params);
        declarator.vla_bounds =
            collect_session_.chain(std::move(declarator.vla_bounds),
                                   std::move(suffix.vla_bounds),
                                   declarator.loc);
        declarator.attrs.append(std::move(suffix.attrs));
    } else if (!declarator.is_function) {
        cursor_ = saved_cursor;
        last_consumed_raw_end_ = saved_last_end;
        restore_parser_checkpoint(checkpoint);
        return std::nullopt;
    }

    ParsedAttributes trailing_attrs = try_parse_attributes();
    declarator.attrs.append(std::move(trailing_attrs.attrs));
    children.insert(children.end(),
                    trailing_attrs.syntax.begin(),
                    trailing_attrs.syntax.end());

    const cir::File& file = collect_session_.file();
    bool record_qualified =
        declarator.qualified_context.valid() &&
        file.decl_context(declarator.qualified_context).kind ==
            cir::DeclContextKind::Record;

    bool has_error = false;
    bool try_direct_member_instantiation =
        record_qualified && !has_explicit_template_arguments;
    cir::EntityId selected_member;
    bool direct_member_owner_is_class_template_specialization = false;
    if (try_direct_member_instantiation) {
        cir::EntityId owner =
            file.decl_context(declarator.qualified_context).owner;
        direct_member_owner_is_class_template_specialization =
            owner.valid() && file.valid(owner) &&
            file.template_specialization(owner);
        if (direct_member_owner_is_class_template_specialization) {
            selected_member = collect_session_.corresponding_record_method(
                declarator.qualified_context,
                declarator.name,
                collect_session_.type_ref(declarator.type),
                !declarator.has_noexcept_specifier);
        }
    }

    struct Match {
        const collect::Session::TemplateInfo* info = nullptr;
        std::vector<collect::Session::TemplateArgument> arguments;
        uint64_t point_lookup_generation = 0;
    };
    std::vector<Match> matches;
    if (!selected_member.valid()) {
        for (const collect::Session::TemplateInfo* candidate : candidates) {
            const std::vector<collect::Session::TemplateArgument>*
                candidate_arguments = &explicit_arguments;
            auto replayed = std::find_if(
                candidate_explicit_arguments.begin(),
                candidate_explicit_arguments.end(),
                [&](const collect::CandidateExplicitTemplateArguments&
                        entry) {
                    return entry.template_entity == candidate->entity;
                });
            if (replayed != candidate_explicit_arguments.end()) {
                if (!replayed->viable) {
                    continue;
                }
                candidate_arguments = &replayed->arguments;
            }
            std::vector<collect::Session::TemplateArgument> deduced;
            collect::Session::PatternInstantiationCallbacks callbacks;
            configure_pattern_instantiation_callbacks(callbacks, declarator.loc);
            if (deduce_function_template_declaration_match(
                    *candidate,
                    declarator.type,
                    deduced,
                    has_explicit_template_arguments ? candidate_arguments
                                                    : nullptr,
                    callbacks,
                    declarator.loc,
                    !declarator.has_noexcept_specifier)) {
                matches.push_back(Match{candidate,
                                        std::move(deduced),
                                        callbacks.point_lookup_generation});
            }
        }
    }

    auto more_specialized = [&](const Match& lhs, const Match& rhs) {
        if (!lhs.info || !rhs.info) {
            return false;
        }
        return collect_session_.function_template_more_specialized(*lhs.info,
                                                                   *rhs.info,
                                                                   collect::Session::FunctionTemplateOrderingContext::declaration());
    };
    auto diagnose_ambiguous_match_notes = [&](const Match& lhs,
                                              const Match& rhs) {
        auto note_candidate = [&](const Match& match) {
            if (match.info && match.info->entity.valid() &&
                collect_session_.file().valid(match.info->entity)) {
                diagnose(DiagnosticLevel::Note,
                         "candidate function template declared here",
                         collect_session_.file().entity(match.info->entity).loc);
            }
        };
        note_candidate(lhs);
        note_candidate(rhs);
        if (lhs.info && rhs.info &&
            collect_session_.function_template_unordered_constraints_tie(
                *lhs.info,
                *rhs.info,
                collect::Session::FunctionTemplateOrderingContext::declaration())) {
            diagnose(
                DiagnosticLevel::Note,
                "candidate associated constraints are not ordered by subsumption",
                declarator.loc);
        }
    };

    Match selected;
    if (selected_member.valid()) {

    } else if (matches.empty()) {
        if (try_direct_member_instantiation && candidates.empty()) {
            if (!direct_member_owner_is_class_template_specialization) {
                diagnose(DiagnosticLevel::Error,
                         "member function explicit instantiation definition must name a member of a class template specialization",
                         declarator.loc);
            } else {
                diagnose(DiagnosticLevel::Error,
                         "no matching member function for explicit instantiation definition",
                         declarator.loc);
            }
        } else {
            diagnose(DiagnosticLevel::Error,
                     "no matching function template for explicit instantiation definition",
                     declarator.loc);
        }
        has_error = true;
    } else {
        size_t best = 0;
        for (size_t i = 1; i < matches.size(); ++i) {
            if (more_specialized(matches[i], matches[best])) {
                best = i;
            }
        }
        std::optional<size_t> ambiguous_index;
        for (size_t i = 0; i < matches.size(); ++i) {
            if (i != best && !more_specialized(matches[best], matches[i])) {
                ambiguous_index = i;
                break;
            }
        }
        if (ambiguous_index.has_value()) {
            diagnose(DiagnosticLevel::Error,
                     "ambiguous explicit function template instantiation definition",
                     declarator.loc);
            diagnose_ambiguous_match_notes(matches[best],
                                           matches[*ambiguous_index]);
            has_error = true;
        } else {
            selected = std::move(matches[best]);
        }
    }

    bool selected_template_is_explicit_specialization =
        selected.info &&
        collect_session_.explicit_template_specialization_declared(
            *selected.info, selected.arguments);
    bool selected_member_is_explicit_specialization =
        collect_session_.is_explicit_template_specialization(selected_member);
    if (selected_member.valid() &&
        !selected_member_is_explicit_specialization) {
        SrcLoc prior_definition_loc;
        if (collect_session_.explicit_entity_instantiation_definition_declared(
                selected_member,
                &prior_definition_loc)) {
            diagnose(DiagnosticLevel::Error,
                     "redefinition of explicit member function instantiation",
                     declarator.loc);
            if (!prior_definition_loc.isInvalid()) {
                diagnose(DiagnosticLevel::Note,
                         "previous explicit instantiation definition is here",
                         prior_definition_loc);
            }
            has_error = true;
        }
    }
    if (selected.info && !selected.info->has_definition &&
        !selected_template_is_explicit_specialization) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation definition requires a function template definition",
                 declarator.loc);
        has_error = true;
    }
    if (selected.info &&
        !selected_template_is_explicit_specialization) {
        SrcLoc prior_definition_loc;
        if (collect_session_.explicit_instantiation_definition_declared(
                *selected.info,
                selected.arguments,
                &prior_definition_loc)) {
            diagnose(DiagnosticLevel::Error,
                     "redefinition of explicit function template instantiation",
                     declarator.loc);
            if (!prior_definition_loc.isInvalid()) {
                diagnose(DiagnosticLevel::Note,
                         "previous explicit instantiation definition is here",
                         prior_definition_loc);
            }
            has_error = true;
        }
    }

    if (declaration_parser.storage_class != StorageClass::None) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation shall not use a storage class specifier",
                 declaration_parser.begin_loc);
        has_error = true;
    }
    if (declaration_parser.is_inline || declaration_parser.is_constexpr ||
        declaration_parser.is_consteval) {
        diagnose(DiagnosticLevel::Error,
                 "function template explicit instantiation shall not use inline, constexpr, or consteval",
                 declaration_parser.begin_loc);
        has_error = true;
    }
    AttributeList explicit_instantiation_attrs =
        declaration_parser.leading_attrs;
    explicit_instantiation_attrs.append(declarator.attrs);
    if (has_forbidden_explicit_instantiation_attributes(
            explicit_instantiation_attrs)) {
        diagnose(DiagnosticLevel::Error,
                 "attributes cannot appertain to an explicit instantiation",
                 declaration_parser.begin_loc.isInvalid()
                     ? template_loc
                     : declaration_parser.begin_loc);
        has_error = true;
    }
    for (ParsedParam& param : declarator.params) {
        if (param.has_default_argument) {
            diagnose(DiagnosticLevel::Error,
                     "explicit instantiation does not use default function arguments",
                     param.default_argument_loc.isInvalid()
                         ? param.loc
                         : param.default_argument_loc);
            param.has_default_argument = false;
            has_error = true;
        }
    }

    if (check(TokenType::LEFT_BRACE)) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation definition cannot be a function definition",
                 current_loc());
        skip_balanced_until_semicolon_or_brace();
        has_error = true;
    } else if (match(TokenType::COMMA)) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation definition may only declare one entity",
                 last_consumed_loc());
        skip_until_statement_boundary();
        has_error = true;
    } else if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ';' after explicit instantiation definition",
                 current_loc());
        skip_until_statement_boundary();
        has_error = true;
    }

    collect::DeclResult decl;
    decl.type = declarator.type;
    decl.has_error = has_error;
    if (selected_member.valid() && !has_error) {
        if (selected_member_is_explicit_specialization) {
            decl.entity = selected_member;
            tentative.commit();
            return ParsedDecl{
                make_node(NodeKind::FunctionDecl,
                          begin,
                          last_consumed_raw_end(),
                          children,
                          text_payload("template"),
                          NodeFlagNone),
                std::move(decl)};
        }
        (void)collect_session_.request_class_member_instantiation(
            selected_member,
            cir::InstantiationDemandKind::MemberDefinition,
            template_loc);
        decl.entity = selected_member;
        if (!collect_session_.file().entity(selected_member).is_definition) {
            diagnose(DiagnosticLevel::Error,
                     "explicit instantiation definition requires a member function definition",
                     declarator.loc);
            decl.has_error = true;
        } else {
            collect_session_.declare_explicit_entity_instantiation_definition(
                selected_member,
                template_loc,
                explicit_instantiation_attrs);
            collect_session_
                .apply_explicit_entity_instantiation_definition_emission(
                    selected_member);
        }
    } else if (selected.info && !has_error) {
        collect_session_.declare_explicit_instantiation_definition(
            *selected.info,
            selected.arguments,
            template_loc,
            explicit_instantiation_attrs);
        cir::EntityId instantiated =
            instantiate_template_with_args(*selected.info,
                                           selected.arguments,
                                           template_loc,
                                           selected.point_lookup_generation);
        collect_session_.apply_explicit_instantiation_definition_emission(
            instantiated,
            *selected.info,
            selected.arguments);
        decl.entity = instantiated;
        if (!instantiated.valid()) {
            decl.has_error = true;
        }
    }

    tentative.commit();
    return ParsedDecl{
        make_node(decl.has_error ? NodeKind::UnknownDecl
                                 : NodeKind::FunctionDecl,
                  begin,
                  last_consumed_raw_end(),
                  children,
                  text_payload("template"),
                  decl.has_error ? NodeFlagHasError : NodeFlagNone),
        std::move(decl)};
}

void Parser::parse_explicit_variable_declarator_suffix(
    ParsedDeclarator& declarator,
    std::vector<NodeId>& children) {
    if (!check(TokenType::LEFT_BRACKET)) {
        return;
    }
    ParsedDeclarator suffix = parse_declarator(declarator.type_ref, true);
    if (suffix.syntax != InvalidNodeId) {
        children.push_back(suffix.syntax);
    }
    declarator.type_ref = suffix.type_ref;
    declarator.type = suffix.type;
    declarator.attrs.append(std::move(suffix.attrs.attrs));
    declarator.has_unsupported_semantics =
        declarator.has_unsupported_semantics ||
        suffix.has_unsupported_semantics;
}

bool Parser::validate_variable_template_explicit_instantiation_type(
    const collect::Session::TemplateInfo& primary,
    const std::vector<collect::Session::TemplateArgument>& arguments,
    cir::TypeRef written_type,
    SrcLoc loc) {
    collect::Session::PatternInstantiationCallbacks callbacks;
    configure_pattern_instantiation_callbacks(callbacks, loc);
    cir::TypeRef primary_type = primary.variable_type_ref.valid()
        ? primary.variable_type_ref
        : collect_session_.type_ref(primary.variable_type);
    auto argument_bindings = canonical_template_argument_bindings(
        collect_session_, primary.parameters, arguments);
    cir::TypeId expected_type =
        argument_bindings.has_value()
            ? collect_session_.substitute_pattern_type(primary_type.type,
                                                       *argument_bindings,
                                                       callbacks)
            : cir::TypeId{};
    if (!expected_type.valid()) {
        diagnose(DiagnosticLevel::Error,
                 "variable template specialization type substitution failed",
                 loc);
        return false;
    }

    cir::TypeRef expected_ref{expected_type,
                              primary_type.qualifiers,
                              primary_type.memory_space};

    if (collect_session_.contains_auto_type(expected_type)) {
        cir::EntityId specialization =
            instantiate_template_with_args(primary, arguments, loc);
        if (!specialization.valid() ||
            !collect_session_.file().valid(specialization)) {
            return false;
        }
        const cir::Entity& entity =
            collect_session_.file().entity(specialization);
        expected_ref = cir::TypeRef{entity.type,
                                    entity.qualifiers,
                                    entity.memory_space};
    }
    if (!collect_session_.types_compatible(expected_ref, written_type)) {
        diagnose(DiagnosticLevel::Error,
                 "explicit variable template specialization has incompatible type",
                 loc);
        return false;
    }
    return true;
}

std::optional<Parser::ParsedDecl>
Parser::try_parse_static_data_member_template_explicit_instantiation_declaration(
    size_t begin,
    SrcLoc extern_loc,
    SrcLoc template_loc) {
    TentativeParsingAction tentative(*this, TentativeMode::CollectBacked);
    ParserCheckpoint checkpoint = capture_parser_checkpoint();
    size_t saved_cursor = cursor_;
    size_t saved_last_end = last_consumed_raw_end_;

    DeclarationParser declaration_parser(
        *this,
        TypeParseContext::type_only(
            TypeParseContext::Origin::NamespaceDeclSpecifier));
    cir::TypeRef base = declaration_parser.parse_declaration(false, true);
    ParsedDeclarator declarator =
        declaration_parser.parse_declarator(base, false);
    bool candidate =
        declarator.has_name && !declarator.is_function &&
        declarator.qualified_context.valid() && check(TokenType::LESS_THAN);
    const cir::File& file = collect_session_.file();
    if (candidate) {
        candidate =
            file.decl_context(declarator.qualified_context).kind ==
            cir::DeclContextKind::Record;
    }
    if (!candidate) {
        cursor_ = saved_cursor;
        last_consumed_raw_end_ = saved_last_end;
        restore_parser_checkpoint(checkpoint);
        return std::nullopt;
    }

    std::vector<NodeId> children;
    if (declaration_parser.type_syntax != InvalidNodeId) {
        children.push_back(declaration_parser.type_syntax);
    }
    if (declarator.syntax != InvalidNodeId) {
        children.push_back(declarator.syntax);
    }

    const cir::Binding* binding =
        file.lookup_template_name_binding(declarator.qualified_context,
                                          declarator.name,
                                          /*include_parents=*/false);
    const collect::Session::TemplateInfo* primary =
        binding && !binding->entities.empty()
            ? collect_session_.template_info(binding->entities.back())
            : nullptr;

    bool has_error = false;
    std::vector<collect::Session::TemplateArgument> arguments;
    if (!primary || !primary->is_variable_template) {
        diagnose(DiagnosticLevel::Error,
                 "no matching static data member template for explicit instantiation declaration",
                 declarator.loc);
        if (!parse_dependent_expression_template_argument_list(
                declarator.loc)) {
            skip_balanced_until_semicolon_or_brace();
        }
        has_error = true;
    } else if (!parse_and_canonicalize_template_argument_list(
                   *primary,
                   arguments,
                   declarator.loc)) {
        has_error = true;
    }

    parse_explicit_variable_declarator_suffix(declarator, children);

    ParsedAttributes trailing_attrs = try_parse_attributes();
    declarator.attrs.append(std::move(trailing_attrs.attrs));
    children.insert(children.end(),
                    trailing_attrs.syntax.begin(),
                    trailing_attrs.syntax.end());

    AttributeList attrs = declaration_parser.leading_attrs;
    attrs.append(declarator.attrs);
    declarator.attrs = std::move(attrs);
    declarator.type_ref =
        collect_session_.apply_type_attributes(declarator.type_ref,
                                               declarator.attrs,
                                               declarator.loc);
    declarator.type = declarator.type_ref.type;

    if (declaration_parser.storage_class != StorageClass::None) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation shall not use a storage class specifier",
                 declaration_parser.begin_loc);
        has_error = true;
    }
    if (declaration_parser.is_inline || declaration_parser.is_constexpr ||
        declaration_parser.is_consteval) {
        diagnose(DiagnosticLevel::Error,
                 "variable template explicit instantiation shall not use inline, constexpr, or consteval",
                 declaration_parser.begin_loc);
        has_error = true;
    }
    if (has_forbidden_explicit_instantiation_attributes(
            declarator.attrs)) {
        diagnose(DiagnosticLevel::Error,
                 "attributes cannot appertain to an explicit instantiation",
                 declaration_parser.begin_loc.isInvalid() ? extern_loc
                                                          : declaration_parser.begin_loc);
        has_error = true;
    }
    bool prior_explicit_specialization =
        primary && primary->is_variable_template && !has_error &&
        collect_session_.explicit_template_specialization_declared(
            *primary, arguments);
    if (primary && primary->is_variable_template &&
        !prior_explicit_specialization) {
        SrcLoc prior_definition_loc;
        if (collect_session_.explicit_instantiation_definition_declared(
                *primary,
                arguments,
                &prior_definition_loc)) {
            diagnose(DiagnosticLevel::Error,
                     "explicit instantiation declaration must precede explicit instantiation definition",
                     declarator.loc);
            if (!prior_definition_loc.isInvalid()) {
                diagnose(DiagnosticLevel::Note,
                         "explicit instantiation definition is here",
                         prior_definition_loc);
            }
            has_error = true;
        }
    }

    if (primary && primary->is_variable_template && !has_error &&
        !validate_variable_template_explicit_instantiation_type(
            *primary, arguments, declarator.type_ref, declarator.loc)) {
        has_error = true;
    }

    bool has_initializer_syntax =
        check(TokenType::ASSIGN) ||
        check(TokenType::LEFT_BRACE) ||
        (lang_opts_.is_cxx_mode() && check(TokenType::LEFT_PAREN));
    if (has_initializer_syntax) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation declaration cannot have an initializer",
                 current_loc());
        skip_until_statement_boundary();
        has_error = true;
    } else if (match(TokenType::COMMA)) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation declaration may only declare one entity",
                 last_consumed_loc());
        skip_until_statement_boundary();
        has_error = true;
    } else if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ';' after explicit instantiation declaration",
                 current_loc());
        skip_until_statement_boundary();
        has_error = true;
    }

    collect::DeclResult decl;
    decl.has_error = has_error;
    if (primary && primary->is_variable_template && !has_error) {
        if (!collect_session_.declare_explicit_instantiation_declaration(
                *primary,
                arguments,
                template_loc,
                declarator.attrs)) {
            has_error = true;
            decl.has_error = true;
        } else {
            cir::EntityId cached = collect_session_.cached_instantiation(
                collect_session_.template_memo_key(primary->entity, arguments));
            collect_session_.apply_explicit_instantiation_declaration_suppression(
                cached,
                *primary,
                arguments);
        }
    }

    tentative.commit();
    return ParsedDecl{
        make_node(decl.has_error ? NodeKind::UnknownDecl : NodeKind::VarDecl,
                  begin,
                  last_consumed_raw_end(),
                  children,
                  text_payload("extern template"),
                  has_error ? NodeFlagHasError : NodeFlagNone),
        std::move(decl)};
}

std::optional<Parser::ParsedDecl>
Parser::try_parse_static_data_member_template_explicit_instantiation_definition(
    size_t begin,
    SrcLoc template_loc) {
    TentativeParsingAction tentative(*this, TentativeMode::CollectBacked);
    ParserCheckpoint checkpoint = capture_parser_checkpoint();
    size_t saved_cursor = cursor_;
    size_t saved_last_end = last_consumed_raw_end_;

    DeclarationParser declaration_parser(
        *this,
        TypeParseContext::type_only(
            TypeParseContext::Origin::NamespaceDeclSpecifier));
    cir::TypeRef base = declaration_parser.parse_declaration(false, true);
    ParsedDeclarator declarator =
        declaration_parser.parse_declarator(base, false);
    bool candidate =
        declarator.has_name && !declarator.is_function &&
        declarator.qualified_context.valid() && check(TokenType::LESS_THAN);
    const cir::File& file = collect_session_.file();
    if (candidate) {
        candidate =
            file.decl_context(declarator.qualified_context).kind ==
            cir::DeclContextKind::Record;
    }
    if (!candidate) {
        cursor_ = saved_cursor;
        last_consumed_raw_end_ = saved_last_end;
        restore_parser_checkpoint(checkpoint);
        return std::nullopt;
    }

    std::vector<NodeId> children;
    if (declaration_parser.type_syntax != InvalidNodeId) {
        children.push_back(declaration_parser.type_syntax);
    }
    if (declarator.syntax != InvalidNodeId) {
        children.push_back(declarator.syntax);
    }

    const cir::Binding* binding =
        file.lookup_template_name_binding(declarator.qualified_context,
                                          declarator.name,
                                          /*include_parents=*/false);
    const collect::Session::TemplateInfo* primary =
        binding && !binding->entities.empty()
            ? collect_session_.template_info(binding->entities.back())
            : nullptr;

    bool has_error = false;
    std::vector<collect::Session::TemplateArgument> arguments;
    if (!primary || !primary->is_variable_template) {
        diagnose(DiagnosticLevel::Error,
                 "no matching static data member template for explicit instantiation definition",
                 declarator.loc);
        if (!parse_dependent_expression_template_argument_list(
                declarator.loc)) {
            skip_balanced_until_semicolon_or_brace();
        }
        has_error = true;
    } else if (!parse_and_canonicalize_template_argument_list(
                   *primary,
                   arguments,
                   declarator.loc)) {
        has_error = true;
    }

    parse_explicit_variable_declarator_suffix(declarator, children);

    ParsedAttributes trailing_attrs = try_parse_attributes();
    declarator.attrs.append(std::move(trailing_attrs.attrs));
    children.insert(children.end(),
                    trailing_attrs.syntax.begin(),
                    trailing_attrs.syntax.end());

    AttributeList attrs = declaration_parser.leading_attrs;
    attrs.append(declarator.attrs);
    declarator.attrs = std::move(attrs);
    declarator.type_ref =
        collect_session_.apply_type_attributes(declarator.type_ref,
                                               declarator.attrs,
                                               declarator.loc);
    declarator.type = declarator.type_ref.type;

    if (declaration_parser.storage_class != StorageClass::None) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation shall not use a storage class specifier",
                 declaration_parser.begin_loc);
        has_error = true;
    }
    if (declaration_parser.is_inline || declaration_parser.is_constexpr ||
        declaration_parser.is_consteval) {
        diagnose(DiagnosticLevel::Error,
                 "variable template explicit instantiation shall not use inline, constexpr, or consteval",
                 declaration_parser.begin_loc);
        has_error = true;
    }
    if (has_forbidden_explicit_instantiation_attributes(
            declarator.attrs)) {
        diagnose(DiagnosticLevel::Error,
                 "attributes cannot appertain to an explicit instantiation",
                 declaration_parser.begin_loc.isInvalid()
                     ? template_loc
                     : declaration_parser.begin_loc);
        has_error = true;
    }
    bool prior_explicit_specialization =
        primary && primary->is_variable_template && !has_error &&
        collect_session_.explicit_template_specialization_declared(
            *primary, arguments);
    if (primary && primary->is_variable_template &&
        !primary->has_definition && !prior_explicit_specialization) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation definition requires a static data member template definition",
                 declarator.loc);
        has_error = true;
    }
    if (primary && primary->is_variable_template &&
        !prior_explicit_specialization) {
        SrcLoc prior_definition_loc;
        if (collect_session_.explicit_instantiation_definition_declared(
                *primary,
                arguments,
                &prior_definition_loc)) {
            diagnose(DiagnosticLevel::Error,
                     "redefinition of explicit static data member template instantiation",
                     declarator.loc);
            if (!prior_definition_loc.isInvalid()) {
                diagnose(DiagnosticLevel::Note,
                         "previous explicit instantiation definition is here",
                         prior_definition_loc);
            }
            has_error = true;
        }
    }

    if (primary && primary->is_variable_template && !has_error &&
        !validate_variable_template_explicit_instantiation_type(
            *primary, arguments, declarator.type_ref, declarator.loc)) {
        has_error = true;
    }

    bool has_initializer_syntax =
        check(TokenType::ASSIGN) ||
        check(TokenType::LEFT_BRACE) ||
        (lang_opts_.is_cxx_mode() && check(TokenType::LEFT_PAREN));
    if (has_initializer_syntax) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation definition cannot have an initializer",
                 current_loc());
        skip_until_statement_boundary();
        has_error = true;
    } else if (match(TokenType::COMMA)) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation definition may only declare one entity",
                 last_consumed_loc());
        skip_until_statement_boundary();
        has_error = true;
    } else if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ';' after explicit instantiation definition",
                 current_loc());
        skip_until_statement_boundary();
        has_error = true;
    }

    collect::DeclResult decl;
    decl.type = declarator.type;
    decl.has_error = has_error;
    if (primary && primary->is_variable_template && !has_error) {
        collect_session_.declare_explicit_instantiation_definition(
            *primary,
            arguments,
            template_loc,
            declarator.attrs);
        cir::EntityId instantiated =
            instantiate_template_with_args(*primary,
                                           arguments,
                                           template_loc);
        collect_session_.apply_explicit_instantiation_definition_emission(
            instantiated,
            *primary,
            arguments);
        decl.entity = instantiated;
        if (!instantiated.valid()) {
            decl.has_error = true;
        }
    }

    tentative.commit();
    return ParsedDecl{
        make_node(decl.has_error ? NodeKind::UnknownDecl : NodeKind::VarDecl,
                  begin,
                  last_consumed_raw_end(),
                  children,
                  text_payload("template"),
                  decl.has_error ? NodeFlagHasError : NodeFlagNone),
        std::move(decl)};
}

std::optional<Parser::ParsedDecl>
Parser::try_parse_variable_template_explicit_instantiation_declaration(
    size_t begin,
    SrcLoc extern_loc,
    SrcLoc template_loc) {
    TentativeParsingAction tentative(*this, TentativeMode::CollectBacked);
    ParserCheckpoint checkpoint = capture_parser_checkpoint();
    size_t saved_cursor = cursor_;
    size_t saved_last_end = last_consumed_raw_end_;

    DeclarationParser declaration_parser(
        *this,
        TypeParseContext::type_only(
            TypeParseContext::Origin::NamespaceDeclSpecifier));
    cir::TypeRef base = declaration_parser.parse_declaration(false, true);
    ParsedDeclarator declarator =
        declaration_parser.parse_declarator(base, false);
    bool candidate =
        declarator.has_name && !declarator.is_function &&
        declarator.type_ref.valid() && check(TokenType::LESS_THAN);
    const cir::File& file = collect_session_.file();
    if (candidate && declarator.qualified_context.valid() &&
        file.decl_context(declarator.qualified_context).kind ==
            cir::DeclContextKind::Record) {
        candidate = false;
    }
    if (!candidate) {
        cursor_ = saved_cursor;
        last_consumed_raw_end_ = saved_last_end;
        restore_parser_checkpoint(checkpoint);
        return std::nullopt;
    }

    std::vector<NodeId> children;
    if (declaration_parser.type_syntax != InvalidNodeId) {
        children.push_back(declaration_parser.type_syntax);
    }
    if (declarator.syntax != InvalidNodeId) {
        children.push_back(declarator.syntax);
    }

    const collect::Session::TemplateInfo* primary = nullptr;
    if (declarator.qualified_context.valid()) {
        const cir::Binding* binding =
            file.lookup_template_name_binding(declarator.qualified_context,
                                              declarator.name,
                                              /*include_parents=*/false);
        if (binding) {
            for (auto it = binding->entities.rbegin();
                 it != binding->entities.rend();
                 ++it) {
                const collect::Session::TemplateInfo* candidate_info =
                    collect_session_.template_info(*it);
                if (candidate_info && candidate_info->is_variable_template) {
                    primary = candidate_info;
                    break;
                }
            }
        }
    } else {
        primary = collect_session_.template_info_for_name(declarator.name);
    }

    bool has_error = false;
    std::vector<collect::Session::TemplateArgument> arguments;
    if (!primary || !primary->is_variable_template ||
        (primary->lexical_context.valid() &&
         file.valid(primary->lexical_context) &&
         file.decl_context(primary->lexical_context).kind ==
             cir::DeclContextKind::Record)) {
        diagnose(DiagnosticLevel::Error,
                 "no matching variable template for explicit instantiation declaration",
                 declarator.loc);
        if (!parse_dependent_expression_template_argument_list(
                declarator.loc)) {
            skip_balanced_until_semicolon_or_brace();
        }
        has_error = true;
    } else if (!parse_and_canonicalize_template_argument_list(
                   *primary,
                   arguments,
                   declarator.loc)) {
        has_error = true;
    }

    parse_explicit_variable_declarator_suffix(declarator, children);

    ParsedAttributes trailing_attrs = try_parse_attributes();
    declarator.attrs.append(std::move(trailing_attrs.attrs));
    children.insert(children.end(),
                    trailing_attrs.syntax.begin(),
                    trailing_attrs.syntax.end());

    AttributeList attrs = declaration_parser.leading_attrs;
    attrs.append(declarator.attrs);
    declarator.attrs = std::move(attrs);
    declarator.type_ref =
        collect_session_.apply_type_attributes(declarator.type_ref,
                                               declarator.attrs,
                                               declarator.loc);
    declarator.type = declarator.type_ref.type;

    if (declaration_parser.storage_class != StorageClass::None) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation shall not use a storage class specifier",
                 declaration_parser.begin_loc);
        has_error = true;
    }
    if (declaration_parser.is_inline || declaration_parser.is_constexpr ||
        declaration_parser.is_consteval) {
        diagnose(DiagnosticLevel::Error,
                 "variable template explicit instantiation shall not use inline, constexpr, or consteval",
                 declaration_parser.begin_loc);
        has_error = true;
    }
    if (has_forbidden_explicit_instantiation_attributes(
            declarator.attrs)) {
        diagnose(DiagnosticLevel::Error,
                 "attributes cannot appertain to an explicit instantiation",
                 declaration_parser.begin_loc.isInvalid() ? extern_loc
                                                          : declaration_parser.begin_loc);
        has_error = true;
    }
    bool prior_explicit_specialization =
        primary && primary->is_variable_template && !has_error &&
        collect_session_.explicit_template_specialization_declared(
            *primary, arguments);
    if (primary && primary->is_variable_template &&
        !prior_explicit_specialization) {
        SrcLoc prior_definition_loc;
        if (collect_session_.explicit_instantiation_definition_declared(
                *primary,
                arguments,
                &prior_definition_loc)) {
            diagnose(DiagnosticLevel::Error,
                     "explicit instantiation declaration must precede explicit instantiation definition",
                     declarator.loc);
            if (!prior_definition_loc.isInvalid()) {
                diagnose(DiagnosticLevel::Note,
                         "explicit instantiation definition is here",
                         prior_definition_loc);
            }
            has_error = true;
        }
    }

    if (primary && primary->is_variable_template && !has_error &&
        !validate_variable_template_explicit_instantiation_type(
            *primary, arguments, declarator.type_ref, declarator.loc)) {
        has_error = true;
    }

    bool has_initializer_syntax =
        check(TokenType::ASSIGN) ||
        check(TokenType::LEFT_BRACE) ||
        (lang_opts_.is_cxx_mode() && check(TokenType::LEFT_PAREN));
    if (has_initializer_syntax) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation declaration cannot have an initializer",
                 current_loc());
        skip_until_statement_boundary();
        has_error = true;
    } else if (match(TokenType::COMMA)) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation declaration may only declare one entity",
                 last_consumed_loc());
        skip_until_statement_boundary();
        has_error = true;
    } else if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ';' after explicit instantiation declaration",
                 current_loc());
        skip_until_statement_boundary();
        has_error = true;
    }

    collect::DeclResult decl;
    decl.has_error = has_error;
    if (primary && primary->is_variable_template && !has_error) {
        if (!collect_session_.declare_explicit_instantiation_declaration(
                *primary,
                arguments,
                template_loc,
                declarator.attrs)) {
            has_error = true;
            decl.has_error = true;
        } else {
            cir::EntityId cached = collect_session_.cached_instantiation(
                collect_session_.template_memo_key(primary->entity, arguments));
            collect_session_.apply_explicit_instantiation_declaration_suppression(
                cached,
                *primary,
                arguments);
        }
    }

    tentative.commit();
    return ParsedDecl{
        make_node(has_error ? NodeKind::UnknownDecl : NodeKind::VarDecl,
                  begin,
                  last_consumed_raw_end(),
                  children,
                  text_payload("extern template"),
                  has_error ? NodeFlagHasError : NodeFlagNone),
        std::move(decl)};
}

std::optional<Parser::ParsedDecl>
Parser::try_parse_variable_template_explicit_instantiation_definition(
    size_t begin,
    SrcLoc template_loc) {
    TentativeParsingAction tentative(*this, TentativeMode::CollectBacked);
    ParserCheckpoint checkpoint = capture_parser_checkpoint();
    size_t saved_cursor = cursor_;
    size_t saved_last_end = last_consumed_raw_end_;

    DeclarationParser declaration_parser(
        *this,
        TypeParseContext::type_only(
            TypeParseContext::Origin::NamespaceDeclSpecifier));
    cir::TypeRef base = declaration_parser.parse_declaration(false, true);
    ParsedDeclarator declarator =
        declaration_parser.parse_declarator(base, false);
    bool candidate =
        declarator.has_name && !declarator.is_function &&
        declarator.type_ref.valid() && check(TokenType::LESS_THAN);
    const cir::File& file = collect_session_.file();
    if (candidate && declarator.qualified_context.valid() &&
        file.decl_context(declarator.qualified_context).kind ==
            cir::DeclContextKind::Record) {
        candidate = false;
    }
    if (!candidate) {
        cursor_ = saved_cursor;
        last_consumed_raw_end_ = saved_last_end;
        restore_parser_checkpoint(checkpoint);
        return std::nullopt;
    }

    std::vector<NodeId> children;
    if (declaration_parser.type_syntax != InvalidNodeId) {
        children.push_back(declaration_parser.type_syntax);
    }
    if (declarator.syntax != InvalidNodeId) {
        children.push_back(declarator.syntax);
    }

    const collect::Session::TemplateInfo* primary = nullptr;
    if (declarator.qualified_context.valid()) {
        const cir::Binding* binding =
            file.lookup_template_name_binding(declarator.qualified_context,
                                              declarator.name,
                                              /*include_parents=*/false);
        if (binding) {
            for (auto it = binding->entities.rbegin();
                 it != binding->entities.rend();
                 ++it) {
                const collect::Session::TemplateInfo* candidate_info =
                    collect_session_.template_info(*it);
                if (candidate_info && candidate_info->is_variable_template) {
                    primary = candidate_info;
                    break;
                }
            }
        }
    } else {
        primary = collect_session_.template_info_for_name(declarator.name);
    }

    bool has_error = false;
    std::vector<collect::Session::TemplateArgument> arguments;
    if (!primary || !primary->is_variable_template ||
        (primary->lexical_context.valid() &&
         file.valid(primary->lexical_context) &&
         file.decl_context(primary->lexical_context).kind ==
             cir::DeclContextKind::Record)) {
        diagnose(DiagnosticLevel::Error,
                 "no matching variable template for explicit instantiation definition",
                 declarator.loc);
        if (!parse_dependent_expression_template_argument_list(
                declarator.loc)) {
            skip_balanced_until_semicolon_or_brace();
        }
        has_error = true;
    } else if (!parse_and_canonicalize_template_argument_list(
                   *primary,
                   arguments,
                   declarator.loc)) {
        has_error = true;
    }

    parse_explicit_variable_declarator_suffix(declarator, children);

    ParsedAttributes trailing_attrs = try_parse_attributes();
    declarator.attrs.append(std::move(trailing_attrs.attrs));
    children.insert(children.end(),
                    trailing_attrs.syntax.begin(),
                    trailing_attrs.syntax.end());

    AttributeList attrs = declaration_parser.leading_attrs;
    attrs.append(declarator.attrs);
    declarator.attrs = std::move(attrs);
    declarator.type_ref =
        collect_session_.apply_type_attributes(declarator.type_ref,
                                               declarator.attrs,
                                               declarator.loc);
    declarator.type = declarator.type_ref.type;

    if (declaration_parser.storage_class != StorageClass::None) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation shall not use a storage class specifier",
                 declaration_parser.begin_loc);
        has_error = true;
    }
    if (declaration_parser.is_inline || declaration_parser.is_constexpr ||
        declaration_parser.is_consteval) {
        diagnose(DiagnosticLevel::Error,
                 "variable template explicit instantiation shall not use inline, constexpr, or consteval",
                 declaration_parser.begin_loc);
        has_error = true;
    }
    if (has_forbidden_explicit_instantiation_attributes(
            declarator.attrs)) {
        diagnose(DiagnosticLevel::Error,
                 "attributes cannot appertain to an explicit instantiation",
                 declaration_parser.begin_loc.isInvalid()
                     ? template_loc
                     : declaration_parser.begin_loc);
        has_error = true;
    }
    bool prior_explicit_specialization =
        primary && primary->is_variable_template && !has_error &&
        collect_session_.explicit_template_specialization_declared(
            *primary, arguments);
    if (primary && primary->is_variable_template &&
        !primary->has_definition && !prior_explicit_specialization) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation definition requires a variable template definition",
                 declarator.loc);
        has_error = true;
    }
    if (primary && primary->is_variable_template &&
        !prior_explicit_specialization) {
        SrcLoc prior_definition_loc;
        if (collect_session_.explicit_instantiation_definition_declared(
                *primary,
                arguments,
                &prior_definition_loc)) {
            diagnose(DiagnosticLevel::Error,
                     "redefinition of explicit variable template instantiation",
                     declarator.loc);
            if (!prior_definition_loc.isInvalid()) {
                diagnose(DiagnosticLevel::Note,
                         "previous explicit instantiation definition is here",
                         prior_definition_loc);
            }
            has_error = true;
        }
    }

    if (primary && primary->is_variable_template && !has_error &&
        !validate_variable_template_explicit_instantiation_type(
            *primary, arguments, declarator.type_ref, declarator.loc)) {
        has_error = true;
    }

    bool has_initializer_syntax =
        check(TokenType::ASSIGN) ||
        check(TokenType::LEFT_BRACE) ||
        (lang_opts_.is_cxx_mode() && check(TokenType::LEFT_PAREN));
    if (has_initializer_syntax) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation definition cannot have an initializer",
                 current_loc());
        skip_until_statement_boundary();
        has_error = true;
    } else if (match(TokenType::COMMA)) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation definition may only declare one entity",
                 last_consumed_loc());
        skip_until_statement_boundary();
        has_error = true;
    } else if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ';' after explicit instantiation definition",
                 current_loc());
        skip_until_statement_boundary();
        has_error = true;
    }

    collect::DeclResult decl;
    decl.type = declarator.type;
    decl.has_error = has_error;
    if (primary && primary->is_variable_template && !has_error) {
        collect_session_.declare_explicit_instantiation_definition(
            *primary,
            arguments,
            template_loc,
            declarator.attrs);
        cir::EntityId instantiated =
            instantiate_template_with_args(*primary,
                                           arguments,
                                           template_loc);
        collect_session_.apply_explicit_instantiation_definition_emission(
            instantiated,
            *primary,
            arguments);
        decl.entity = instantiated;
        if (!instantiated.valid()) {
            decl.has_error = true;
        }
    }

    tentative.commit();
    return ParsedDecl{
        make_node(decl.has_error ? NodeKind::UnknownDecl : NodeKind::VarDecl,
                  begin,
                  last_consumed_raw_end(),
                  children,
                  text_payload("template"),
                  decl.has_error ? NodeFlagHasError : NodeFlagNone),
        std::move(decl)};
}

std::optional<Parser::ParsedDecl>
Parser::try_parse_static_data_member_explicit_instantiation_declaration(
    size_t begin,
    SrcLoc extern_loc,
    SrcLoc template_loc) {
    return try_parse_static_data_member_explicit_instantiation(begin,
                                                              extern_loc,
                                                              template_loc,
                                                              true);
}

std::optional<Parser::ParsedDecl>
Parser::try_parse_static_data_member_explicit_instantiation_definition(
    size_t begin,
    SrcLoc template_loc) {
    return try_parse_static_data_member_explicit_instantiation(begin,
                                                              template_loc,
                                                              template_loc,
                                                              false);
}

std::optional<Parser::ParsedDecl>
Parser::try_parse_static_data_member_explicit_instantiation(
    size_t begin,
    SrcLoc introducer_loc,
    SrcLoc template_loc,
    bool is_declaration) {
    TentativeParsingAction tentative(*this, TentativeMode::CollectBacked);

    DeclarationParser declaration_parser(
        *this,
        TypeParseContext::type_only(
            TypeParseContext::Origin::NamespaceDeclSpecifier));
    cir::TypeRef base = declaration_parser.parse_declaration(false, true);
    ParsedDeclarator declarator =
        declaration_parser.parse_declarator(base, false);
    if (!declarator.has_name || declarator.is_function ||
        !declarator.qualified_context.valid() ||
        check(TokenType::LESS_THAN)) {
        return std::nullopt;
    }

    const cir::File& file = collect_session_.file();
    if (file.decl_context(declarator.qualified_context).kind !=
        cir::DeclContextKind::Record) {
        return std::nullopt;
    }

    std::vector<NodeId> children;
    if (declaration_parser.type_syntax != InvalidNodeId) {
        children.push_back(declaration_parser.type_syntax);
    }
    if (declarator.syntax != InvalidNodeId) {
        children.push_back(declarator.syntax);
    }

    ParsedAttributes trailing_attrs = try_parse_attributes();
    declarator.attrs.append(std::move(trailing_attrs.attrs));
    children.insert(children.end(),
                    trailing_attrs.syntax.begin(),
                    trailing_attrs.syntax.end());

    AttributeList attrs = declaration_parser.leading_attrs;
    attrs.append(declarator.attrs);
    declarator.attrs = std::move(attrs);
    declarator.type_ref =
        collect_session_.apply_type_attributes(declarator.type_ref,
                                               declarator.attrs,
                                               declarator.loc);
    declarator.type = declarator.type_ref.type;

    bool has_error = false;
    cir::EntityId owner =
        file.decl_context(declarator.qualified_context).owner;
    if (!owner.valid() || !file.valid(owner) ||
        !file.template_specialization(owner)) {
        diagnose(
            DiagnosticLevel::Error,
            is_declaration
                ? "static data member explicit instantiation declaration must name a member of a class template specialization"
                : "static data member explicit instantiation definition must name a member of a class template specialization",
            declarator.loc);
        has_error = true;
    }

    cir::EntityId member;
    if (!has_error) {
        member = collect_session_.find_record_static_data_member(
            declarator.qualified_context,
            declarator.name,
            declarator.type_ref);
        if (!member.valid()) {
            diagnose(DiagnosticLevel::Error,
                     is_declaration
                         ? "no matching static data member for explicit instantiation declaration"
                         : "no matching static data member for explicit instantiation definition",
                     declarator.loc);
            has_error = true;
        }
    }

    bool member_is_explicit_specialization =
        collect_session_.is_explicit_template_specialization(member);
    if (member.valid() && !member_is_explicit_specialization) {
        SrcLoc prior_definition_loc;
        if (collect_session_.explicit_entity_instantiation_definition_declared(
                member,
                &prior_definition_loc)) {
            diagnose(DiagnosticLevel::Error,
                     is_declaration
                         ? "explicit instantiation declaration must precede explicit instantiation definition"
                         : "redefinition of explicit static data member instantiation",
                     declarator.loc);
            if (!prior_definition_loc.isInvalid()) {
                diagnose(DiagnosticLevel::Note,
                         is_declaration
                             ? "explicit instantiation definition is here"
                             : "previous explicit instantiation definition is here",
                         prior_definition_loc);
            }
            has_error = true;
        }
    }

    if (declaration_parser.storage_class != StorageClass::None) {
        diagnose(DiagnosticLevel::Error,
                 "explicit instantiation shall not use a storage class specifier",
                 declaration_parser.begin_loc);
        has_error = true;
    }
    if (declaration_parser.is_constexpr ||
        declaration_parser.is_consteval) {
        diagnose(
            DiagnosticLevel::Error,
            "constexpr or consteval cannot be applied to a non-defining variable declaration",
            declaration_parser.begin_loc);
        has_error = true;
    }
    if (has_forbidden_explicit_instantiation_attributes(
            declarator.attrs)) {
        diagnose(DiagnosticLevel::Error,
                 "attributes cannot appertain to an explicit instantiation",
                 declaration_parser.begin_loc.isInvalid() ? introducer_loc
                                                          : declaration_parser.begin_loc);
        has_error = true;
    }

    if (check(TokenType::ASSIGN) || check(TokenType::LEFT_BRACE) ||
        check(TokenType::LEFT_PAREN)) {
        diagnose(DiagnosticLevel::Error,
                 is_declaration
                     ? "explicit instantiation declaration cannot have an initializer"
                     : "explicit instantiation definition cannot have an initializer",
                 current_loc());
        skip_balanced_until_semicolon_or_brace();
        has_error = true;
    } else if (match(TokenType::COMMA)) {
        diagnose(DiagnosticLevel::Error,
                 is_declaration
                     ? "explicit instantiation declaration may only declare one entity"
                     : "explicit instantiation definition may only declare one entity",
                 last_consumed_loc());
        skip_until_statement_boundary();
        has_error = true;
    } else if (!match(TokenType::SEMICOLON)) {
        diagnose(DiagnosticLevel::Error,
                 is_declaration
                     ? "expected ';' after explicit instantiation declaration"
                     : "expected ';' after explicit instantiation definition",
                 current_loc());
        skip_until_statement_boundary();
        has_error = true;
    }

    collect::DeclResult decl;
    decl.has_error = has_error;
    if (member.valid()) {
        decl.entity = member;
        decl.type = declarator.type;
        if (!has_error) {
            if (member_is_explicit_specialization) {

            } else if (is_declaration) {
                if (!collect_session_
                         .declare_explicit_entity_instantiation_declaration(
                             member,
                             template_loc,
                             declarator.attrs)) {
                    has_error = true;
                    decl.has_error = true;
                }
            } else if (collect_session_.request_class_member_instantiation(
                           member,
                           cir::InstantiationDemandKind::MemberDefinition,
                           template_loc) !=
                       collect::Session::InstantiationDemandResult::Satisfied) {
                diagnose(DiagnosticLevel::Error,
                         "explicit instantiation definition requires a static data member definition",
                         declarator.loc);
                decl.has_error = true;
            } else {
                collect_session_
                    .declare_explicit_entity_instantiation_definition(
                        member,
                        template_loc,
                        declarator.attrs);
                collect_session_
                    .apply_explicit_entity_instantiation_definition_emission(
                        member);
            }
        }
    }

    tentative.commit();
    return ParsedDecl{
        make_node(has_error ? NodeKind::UnknownDecl : NodeKind::VarDecl,
                  begin,
                  last_consumed_raw_end(),
                  children,
                  text_payload(is_declaration ? "extern template"
                                              : "template"),
                  decl.has_error ? NodeFlagHasError : NodeFlagNone),
        std::move(decl)};
}

size_t Parser::capture_out_of_line_member_end(
    size_t declarator_tail,
    size_t declarator_last_end,
    bool is_function) {
    cursor_ = declarator_tail;
    last_consumed_raw_end_ = declarator_last_end;
    if (!is_function) {

        return skip_balanced_until_semicolon();
    }
    if (check(TokenType::TRY_KW)) {
        return skip_function_try_block_tokens();
    }
    if (!match(TokenType::COLON)) {
        return skip_balanced_until_semicolon_or_brace();
    }

    int depth = 0;
    TokenType previous = TokenType::COLON;
    while (!at_end()) {
        TokenType type = current().type;
        if (depth == 0 &&
            (type == TokenType::SEMICOLON ||
             type == TokenType::RIGHT_BRACE)) {
            break;
        }
        if (depth == 0 && type == TokenType::LEFT_BRACE &&
            !is_identifier_token(previous) &&
            previous != TokenType::GREATER_THAN) {
            break;
        }
        if (type == TokenType::LEFT_PAREN ||
            type == TokenType::LEFT_BRACE) {
            ++depth;
        } else if (type == TokenType::RIGHT_PAREN ||
                   type == TokenType::RIGHT_BRACE) {
            --depth;
        }
        previous = type;
        consume();
    }
    return check(TokenType::LEFT_BRACE)
        ? skip_balanced_until_semicolon_or_brace()
        : skip_balanced_until_semicolon();
}

Parser::ParsedDecl Parser::parse_cxx_template_declaration() {
    size_t begin = current_raw_index();
    Token template_token = current();
    consume();

    collect::Session::TemplateInfo info;
    if (!parse_cxx_template_head(info, template_token.loc)) {
        skip_balanced_until_semicolon_or_brace();
        collect::DeclResult decl;
        decl.has_error = true;
        return {make_node(NodeKind::UnknownDecl, begin, last_consumed_raw_end(),
                          {}, text_payload("template"), NodeFlagHasError),
                std::move(decl)};
    }
    info.is_member_template_specialization_overlay =
        explicit_member_template_overlay_head_depth_ != 0 &&
        !info.parameters.empty();
    if (info.is_member_template_specialization_overlay) {

        explicit_member_template_overlay_head_depth_ = 0;
    }
    if (collect_session_.in_extern_c_linkage()) {
        diagnose(DiagnosticLevel::Error,
                 "templates shall not have C language linkage",
                 template_token.loc);
    }
    cir::DeclContextId template_declaration_context =
        collect_session_.current_decl_context();
    bool template_declaration_is_record_member =
        template_declaration_context.valid() &&
        collect_session_.file().valid(template_declaration_context) &&
        collect_session_.file()
                .decl_context(template_declaration_context)
                .kind == cir::DeclContextKind::Record;
    TypeParseContext template_declaration_type_context =
        TypeParseContext::type_only(
            template_declaration_is_record_member
                ? TypeParseContext::Origin::MemberDeclSpecifier
                : TypeParseContext::Origin::NamespaceDeclSpecifier);

    if (info.parameters.empty() && check(TokenType::TEMPLATE) &&
        peek(1).type == TokenType::LESS_THAN) {
        bool inner_head_is_nonempty =
            peek(2).type != TokenType::GREATER_THAN;
        bool another_head_follows_empty =
            !inner_head_is_nonempty &&
            peek(3).type == TokenType::TEMPLATE;
        if (inner_head_is_nonempty || another_head_follows_empty) {
            struct OverlayHeadDepthExit {
                Parser& parser;
                unsigned previous_depth = 0;
                ~OverlayHeadDepthExit() {
                    parser.explicit_member_template_overlay_head_depth_ =
                        previous_depth;
                }
            } overlay_depth{*this,
                            explicit_member_template_overlay_head_depth_};
            ++explicit_member_template_overlay_head_depth_;
            ParsedDecl inner = parse_cxx_template_declaration();
            return {make_node(inner.sem.has_error ? NodeKind::UnknownDecl
                                                   : NodeKind::RecordDecl,
                              begin,
                              last_consumed_raw_end(),
                              {inner.syntax},
                              text_payload("template<>"),
                              inner.sem.has_error ? NodeFlagHasError
                                                  : NodeFlagNone),
                    std::move(inner.sem)};
        }
    }

    auto syntactically_starts_qualified_conversion = [&]() {
        int angle_depth = 0;
        bool saw_scope = false;
        for (size_t offset = 0; offset < 4096; ++offset) {
            TokenType type = peek(offset).type;
            if (type == TokenType::Eof || type == TokenType::SEMICOLON ||
                type == TokenType::LEFT_BRACE ||
                (type == TokenType::LEFT_PAREN && angle_depth == 0)) {
                return false;
            }
            if (type == TokenType::LESS_THAN) {
                ++angle_depth;
            } else if (type == TokenType::GREATER_THAN) {
                --angle_depth;
            } else if (type == TokenType::RIGHT_SHIFT) {
                angle_depth -= 2;
            } else if (angle_depth == 0 &&
                       type == TokenType::SCOPE_RESOLUTION) {
                saw_scope = true;
            } else if (angle_depth == 0 &&
                       type == TokenType::OPERATOR_KW) {
                TokenType target = peek(offset + 1).type;
                return saw_scope &&
                    (is_identifier_token(target) ||
                     is_type_start(target) ||
                     target == TokenType::SCOPE_RESOLUTION);
            }
        }
        return false;
    };

    if (!info.parameters.empty() && !check(TokenType::TEMPLATE) &&
        syntactically_starts_qualified_conversion()) {
        collect::Session::TemplateInfo definition_info = info;
        collect::Session::InstantiationScope header_scope =
            collect_session_.begin_template_header(definition_info,
                                                   template_token.loc);
        bool saved_template_head_precedence =
            qualified_declarator_template_head_wins_;
        qualified_declarator_template_head_wins_ = true;
        std::optional<ParsedConversionFunctionDeclarator> parsed =
            parse_conversion_function_declarator(
                /*require_qualified=*/true);
        qualified_declarator_template_head_wins_ =
            saved_template_head_precedence;
        collect_session_.finish_template_header(std::move(header_scope));

        collect::DeclResult decl;
        bool has_error = !parsed.has_value() || parsed->has_error;
        ParsedDeclarator declarator = parsed
            ? std::move(parsed->declarator)
            : ParsedDeclarator{};
        decl.type = declarator.type;

        const cir::File& file = collect_session_.file();
        bool record_qualified =
            declarator.qualified_context.valid() &&
            file.valid(declarator.qualified_context) &&
            file.decl_context(declarator.qualified_context).kind ==
                cir::DeclContextKind::Record;
        if (!record_qualified) {
            diagnose(DiagnosticLevel::Error,
                     "conversion function template definition does not name a record member",
                     declarator.loc.isInvalid() ? template_token.loc
                                                : declarator.loc);
            has_error = true;
        }

        definition_info.name = declarator.name;
        definition_info.operator_function = declarator.operator_function;
        definition_info.pattern_type = declarator.type;
        record_trailing_function_requires_clause(definition_info,
                                                 declarator);

        cir::EntityId method_entity{};
        const collect::Session::TemplateInfo* existing_info = nullptr;
        bool ambiguous = false;
        const cir::RecordFacts* facts = nullptr;
        if (record_qualified) {
            cir::EntityId owner =
                file.decl_context(declarator.qualified_context).owner;
            facts = file.record_facts(owner);
        }
        if (facts) {
            for (const cir::RecordMethodFact& method : facts->methods) {
                if (!method.is_conversion_function ||
                    !method.is_function_template) {
                    continue;
                }
                const collect::Session::TemplateInfo* candidate =
                    collect_session_.template_info(method.entity);
                if (!candidate ||
                    !collect_session_.function_template_declarations_correspond(
                        *candidate, definition_info)) {
                    continue;
                }
                if (method_entity.valid()) {
                    ambiguous = true;
                    break;
                }
                method_entity = method.entity;
                existing_info = candidate;
            }
        }
        if (ambiguous) {
            diagnose(DiagnosticLevel::Error,
                     "out-of-line conversion function template definition is ambiguous",
                     declarator.loc);
            has_error = true;
        } else if (!method_entity.valid() || !existing_info) {
            diagnose(DiagnosticLevel::Error,
                     "out-of-line conversion function template definition has no matching declaration",
                     declarator.loc);
            has_error = true;
        }
        if (!check(TokenType::LEFT_BRACE)) {
            diagnose(DiagnosticLevel::Error,
                     "expected a body for out-of-line conversion function template definition",
                     current_loc());
            has_error = true;
        }

        size_t body_begin = current_raw_index();
        size_t body_end = skip_balanced_until_semicolon_or_brace();
        match(TokenType::SEMICOLON);
        if (!has_error) {
            size_t method_index = 0;
            for (size_t index = 0; index < facts->methods.size(); ++index) {
                if (facts->methods[index].entity == method_entity) {
                    method_index = index;
                    break;
                }
            }
            PendingMemberBody pending;
            pending.method_index = method_index;
            pending.body_begin = body_begin;
            pending.body_end = body_end;
            pending.params = std::move(declarator.params);

            definition_info.has_definition = true;
            definition_info.definition_begin = body_begin;
            definition_info.definition_end = body_end;
            if (definition_info
                    .is_member_template_specialization_overlay) {
                definition_info.definition_generation =
                    collect_session_.lookup_generation();
            }
            if (!definition_info
                     .is_member_template_specialization_overlay &&
                !collect_session_.collecting_pattern() &&
                !collect_session_.is_instantiating()) {
                validate_member_template_body(definition_info,
                                              method_entity,
                                              pending,
                                              template_token.loc);
            }
            uint64_t body_key =
                static_cast<uint64_t>(method_entity.index);
            member_template_bodies_[body_key] = pending;
            collect_session_.track_speculative_rollback(
                [this, body_key] { member_template_bodies_.erase(body_key); });
            if (!collect_session_.define_member_template_entity(
                    std::move(definition_info),
                    method_entity,
                    declarator.loc)) {
                has_error = true;
            }
            decl.entity = method_entity;
        }
        decl.has_error = has_error;
        return {make_node(has_error ? NodeKind::UnknownDecl
                                    : NodeKind::FunctionDecl,
                          begin,
                          last_consumed_raw_end(),
                          {},
                          text_payload("template conversion"),
                          has_error ? NodeFlagHasError : NodeFlagNone),
                std::move(decl)};
    }

    if (info.parameters.empty() && !check(TokenType::TEMPLATE) &&
        syntactically_starts_qualified_conversion()) {
        TemplateArgumentAccessExemptionScope access_exemption(
            collect_session_);
        std::optional<ParsedConversionFunctionDeclarator> parsed =
            parse_conversion_function_declarator(
                /*require_qualified=*/true);
        collect::DeclResult invalid_decl;
        if (!parsed) {
            invalid_decl.has_error = true;
            skip_balanced_until_semicolon_or_brace();
            return {make_node(NodeKind::UnknownDecl,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              text_payload("template<> conversion"),
                              NodeFlagHasError),
                    std::move(invalid_decl)};
        }
        ParsedDeclarator declarator = std::move(parsed->declarator);
        const cir::File& file = collect_session_.file();
        bool has_error = parsed->has_error;
        bool record_qualified =
            declarator.qualified_context.valid() &&
            file.valid(declarator.qualified_context) &&
            file.decl_context(declarator.qualified_context).kind ==
                cir::DeclContextKind::Record;
        const cir::RecordFacts* facts = nullptr;
        if (record_qualified) {
            facts = file.record_facts(
                file.decl_context(declarator.qualified_context).owner);
        }

        struct ConversionSpecializationMatch {
            const collect::Session::TemplateInfo* info = nullptr;
            std::vector<collect::Session::TemplateArgument> arguments;
            uint64_t point_lookup_generation = 0;
        } selected;
        std::vector<ConversionSpecializationMatch> matches;
        if (facts) {
            for (const cir::RecordMethodFact& method : facts->methods) {
                if (!method.is_conversion_function ||
                    !method.is_function_template) {
                    continue;
                }
                const collect::Session::TemplateInfo* candidate =
                    collect_session_.template_info(method.entity);
                if (!candidate) {
                    continue;
                }
                std::vector<collect::Session::TemplateArgument> deduced;
                collect::Session::PatternInstantiationCallbacks callbacks;
                configure_pattern_instantiation_callbacks(callbacks,
                                                            declarator.loc);
                if (!deduce_function_template_declaration_match(
                        *candidate,
                        declarator.type,
                        deduced,
                        nullptr,
                        callbacks,
                        declarator.loc,
                        !declarator.has_noexcept_specifier)) {
                    continue;
                }
                matches.push_back(ConversionSpecializationMatch{
                    candidate,
                    std::move(deduced),
                    callbacks.point_lookup_generation});
            }
        }
        if (matches.empty()) {
            diagnose(DiagnosticLevel::Error,
                     "no matching conversion function template for explicit specialization",
                     declarator.loc);
            has_error = true;
        } else {
            auto more_specialized = [&](size_t lhs, size_t rhs) {
                return collect_session_.function_template_more_specialized(
                    *matches[lhs].info,
                    *matches[rhs].info,
                    collect::Session::FunctionTemplateOrderingContext::declaration());
            };
            size_t best = 0;
            for (size_t index = 1; index < matches.size(); ++index) {
                if (more_specialized(index, best)) {
                    best = index;
                }
            }
            bool ambiguous = false;
            for (size_t index = 0; index < matches.size(); ++index) {
                if (index != best && !more_specialized(best, index)) {
                    ambiguous = true;
                    break;
                }
            }
            if (ambiguous) {
                diagnose(
                    DiagnosticLevel::Error,
                    "ambiguous explicit conversion function template specialization",
                    declarator.loc);
                has_error = true;
            } else {
                selected = std::move(matches[best]);
            }
        }

        collect::DeclFlags flags;
        cir::EntityId specialization{};
        std::string memo_key;
        if (selected.info) {
            memo_key = collect_session_.template_memo_key(
                selected.info->entity, selected.arguments);
            cir::EntityId cached =
                collect_session_.cached_instantiation(memo_key);
            if (cached.valid() && file.valid(cached) &&
                file.entity(cached).linkage == cir::LinkageKind::LinkOnceODR) {
                diagnose(
                    DiagnosticLevel::Error,
                    "explicit specialization of conversion function template after implicit instantiation",
                    declarator.loc);
                has_error = true;
            } else if (cached.valid() && file.valid(cached)) {
                specialization = cached;
                if (file.entity(cached).is_definition &&
                    check(TokenType::LEFT_BRACE)) {
                    diagnose(
                        DiagnosticLevel::Error,
                        "redefinition of explicit conversion function template specialization",
                        declarator.loc);
                    has_error = true;
                }
            }
            if (!specialization.valid() && !has_error) {
                specialization =
                    collect_session_.create_member_template_specialization(
                        *selected.info,
                        selected.arguments,
                        declarator.type,
                        declarator.loc,
                        &flags);
            }
        }

        collect::DeclResult decl;
        bool parsed_definition = false;
        if (!has_error && specialization.valid()) {
            declarator.explicit_function_template_specialization_info =
                selected.info;
            declarator.explicit_function_template_specialization_arguments =
                selected.arguments;
            declarator.explicit_member_function_template_specialization =
                specialization;
            declarator.name = collect_session_.template_display_name(
                *selected.info, selected.arguments);
            access_exemption.finish();
            std::vector<NodeId> specialization_children;
            FunctionDeclaratorResult result =
                handle_function_declarator(declarator,
                                           specialization_children,
                                           flags);
            decl = std::move(result.decl);
            parsed_definition = result.parsed_definition;
            if (!collect_session_.cached_instantiation(memo_key).valid()) {
                collect_session_.remember_instantiation(memo_key,
                                                        specialization);
            }
            collect_session_.mark_explicit_template_specialization(
                specialization);
        } else {
            decl.has_error = true;
            skip_balanced_until_semicolon_or_brace();
        }
        if (!parsed_definition && !match(TokenType::SEMICOLON)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ';' after explicit conversion function template specialization",
                     current_loc());
            skip_until_statement_boundary();
            decl.has_error = true;
        }
        return {make_node(decl.has_error ? NodeKind::UnknownDecl
                                         : NodeKind::FunctionDecl,
                          begin,
                          last_consumed_raw_end(),
                          {},
                          text_payload("template<> conversion"),
                          decl.has_error ? NodeFlagHasError : NodeFlagNone),
                std::move(decl)};
    }

    enum class OwnerHeadMappingResult : uint8_t {
        Unchanged,
        Renamed,
        Invalid,
    };
    auto map_owner_head =
        [&](const collect::Session::TemplateInfo& written_head,
            const collect::Session::TemplateInfo& owner,
            const std::vector<collect::Session::TemplateArgument>& written,
            std::vector<collect::Session::TemplateParameter>& mapped_parameters,
            std::vector<uint32_t>& owner_slots) {
        mapped_parameters.clear();
        owner_slots.clear();
        if (written_head.parameters.empty() ||
            written.size() != written_head.parameters.size() ||
            owner.parameters.size() != written.size() ||
            !collect_session_.template_parameter_lists_match(
                owner.parameters,
                written_head.parameters)) {
            return OwnerHeadMappingResult::Invalid;
        }
        std::vector<uint32_t> slots(written_head.parameters.size(),
                                    UINT32_MAX);
        for (size_t slot = 0; slot < written.size(); ++slot) {
            const collect::Session::TemplateArgument& argument = written[slot];
            bool matched = false;
            for (size_t j = 0; j < written_head.parameters.size(); ++j) {
                const collect::Session::TemplateParameter& parameter =
                    written_head.parameters[j];
                if (parameter.is_parameter_pack || slots[j] != UINT32_MAX) {
                    continue;
                }
                bool names_parameter = false;
                if (parameter.kind ==
                        collect::Session::TemplateParameterKind::Type) {
                    names_parameter =
                        argument.kind == cir::TemplateArgumentKind::Type &&
                        argument.type.type.valid() &&
                        argument.type.qualifiers == cir::QualNone &&
                        argument.type.type == parameter.type_param_type;
                } else if (parameter.kind ==
                           collect::Session::TemplateParameterKind::NonType) {
                    names_parameter =
                        argument.kind == cir::TemplateArgumentKind::Value &&
                        argument.value_param_index == parameter.index;
                } else {
                    names_parameter =
                        argument.kind == cir::TemplateArgumentKind::Template &&
                        argument.template_param_index == parameter.index;
                }
                if (names_parameter) {
                    slots[j] = static_cast<uint32_t>(slot);
                    matched = true;
                    break;
                }
            }
            if (!matched) {
                return OwnerHeadMappingResult::Invalid;
            }
        }
        bool renamed = false;
        for (size_t j = 0; j < slots.size(); ++j) {
            if (slots[j] != j) {
                return OwnerHeadMappingResult::Invalid;
            }
            renamed = renamed ||
                      written_head.parameters[j].name !=
                          owner.parameters[j].name;
        }
        if (!renamed) {
            return OwnerHeadMappingResult::Unchanged;
        }
        mapped_parameters = written_head.parameters;
        owner_slots = std::move(slots);
        return OwnerHeadMappingResult::Renamed;
    };
    auto replay_owner_member_for_existing_specializations =
        [&](const collect::Session::TemplateInfo& owner,
            size_t member_begin,
            bool is_template_declaration,
            const std::vector<collect::Session::TemplateParameter>&
                mapped_parameters,
            const std::vector<uint32_t>& mapped_slots) {
        const cir::File& file = collect_session_.file();
        std::vector<cir::EntityId> existing_entities = file.entity_ids();
        size_t saved_cursor = cursor_;
        size_t saved_last_end = last_consumed_raw_end_;
        for (cir::EntityId entity : existing_entities) {
            if (!entity.valid() || !file.valid(entity) ||
                file.entity(entity).kind != cir::EntityKind::Record) {
                continue;
            }
            const cir::TemplateSpecializationFact* fact =
                file.template_specialization(entity);
            if (!fact || !fact->selected_template_entity.valid() ||
                fact->selected_template_entity != owner.entity) {
                continue;
            }
            std::vector<collect::Session::TemplateArgument> fact_arguments =
                fact->selected_template_arguments();
            if (template_arguments_are_dependent(fact_arguments)) {

                continue;
            }
            const cir::RecordFacts* record_facts =
                file.record_facts(entity);
            if (!record_facts || record_facts->is_incomplete) {

                continue;
            }
            const auto* exact_bindings =
                fact->selected_argument_bindings.empty()
                ? nullptr
                : &fact->selected_argument_bindings;
            collect::Session::InstantiationScope replay_scope =
                collect_session_.begin_template_instantiation(
                    owner,
                    fact_arguments,
                    file.entity(entity).loc,
                    fact->point_lookup_generation,
                    {},
                    exact_bindings);
            if (!replay_scope.active) {
                continue;
            }
            collect::Session::OutOfLineHeadRebinding head_rebinding;
            bool shadow_head = !mapped_parameters.empty() &&
                               mapped_parameters.size() == mapped_slots.size();
            std::vector<collect::Session::TemplateArgument> reordered;
            if (shadow_head) {
                reordered.reserve(mapped_slots.size());
                for (uint32_t slot : mapped_slots) {
                    if (slot >=
                        fact->selected_argument_bindings.size()) {
                        shadow_head = false;
                        break;
                    }
                    const collect::Session::TemplateArgumentBinding&
                        slot_binding =
                            fact->selected_argument_bindings[slot];
                    reordered.insert(reordered.end(),
                                     slot_binding.arguments.begin(),
                                     slot_binding.arguments.end());
                }
            }
            if (shadow_head) {
                collect::Session::TemplateInfo head;
                head.parameters = mapped_parameters;
                head_rebinding = collect_session_.bind_out_of_line_member_head(
                    head,
                    reordered,
                    file.entity(entity).loc);
            }
            cursor_ = member_begin;
            (void)(is_template_declaration
                       ? parse_cxx_template_declaration()
                       : parse_declaration(true));
            if (shadow_head) {
                collect_session_.restore_out_of_line_member_head(
                    head_rebinding);
            }
            collect_session_.finish_template_instantiation(
                std::move(replay_scope));
        }
        cursor_ = saved_cursor;
        last_consumed_raw_end_ = saved_last_end;
    };

    if (check(TokenType::TEMPLATE) &&
        !(peek(1).type == TokenType::LESS_THAN &&
          peek(2).type == TokenType::GREATER_THAN)) {
        std::vector<collect::Session::TemplateParameter>
            stacked_head_parameters;
        std::vector<uint32_t> stacked_head_owner_slots;
        bool stacked_head_invalid = false;
        SrcLoc stacked_head_loc = template_token.loc;
        size_t stacked_member_tail = SIZE_MAX;
        size_t stacked_member_tail_last_end = 0;
        bool stacked_member_is_function = false;
        struct DeferTemplateQualifierInstantiation {
            Parser& parser;
            bool previous = false;
            bool previous_partial_selection = false;

            explicit DeferTemplateQualifierInstantiation(Parser& parser)
                : parser(parser),
                  previous(
                      parser.defer_class_template_qualifier_instantiation_),
                  previous_partial_selection(
                      parser
                          .select_partial_for_deferred_class_template_qualifier_) {
                parser.defer_class_template_qualifier_instantiation_ = true;
            }

            ~DeferTemplateQualifierInstantiation() {
                parser.defer_class_template_qualifier_instantiation_ =
                    previous;
                parser
                    .select_partial_for_deferred_class_template_qualifier_ =
                    previous_partial_selection;
            }
        };

        // `template <class T> template <class U> struct O<T>::I<U*> { ... }`
        // defines (or partially specializes) a member class template.  The
        // declarator probe below only accepts a function or variable, so this
        // form needs its own probe, mirroring the single-head branch that
        // already handles `template <class T> struct O<T>::I { ... }`.  The
        // qualifier's class template is the owner: it is what replays the
        // captured range, and the replay then sees an ordinary single-head
        // member declaration inside the instantiated enclosing class.
        auto parsed_member_class_owner =
            [&]() -> std::optional<cir::EntityId> {
            RevertingTentativeParsingAction tentative(
                *this,
                TentativeMode::CollectBacked);
            DeferTemplateQualifierInstantiation defer(*this);

            collect::Session::TemplateInfo outer_probe = info;
            collect::Session::InstantiationScope outer_scope =
                collect_session_.begin_template_header(outer_probe,
                                                       template_token.loc);
            Token inner_template = current();
            consume();
            collect::Session::TemplateInfo member_probe;
            if (!parse_cxx_template_head(member_probe, inner_template.loc)) {
                collect_session_.finish_template_header(std::move(outer_scope));
                return std::nullopt;
            }
            collect::Session::InstantiationScope member_scope =
                collect_session_.begin_template_header(member_probe,
                                                       inner_template.loc);

            std::optional<cir::EntityId> result;
            if (check(TokenType::STRUCT) || check(TokenType::CLASS) ||
                check(TokenType::UNION)) {
                consume();
                ParsedNestedName nested = parse_nested_name_specifier();
                if (nested.consumed_any && !nested.has_error &&
                    nested.template_qualifier_info &&
                    nested.template_qualifier_info->is_class_template &&
                    is_identifier_token(current().type)) {
                    result = nested.template_qualifier_info->entity;
                }
            }
            collect_session_.finish_template_header(std::move(member_scope));
            collect_session_.finish_template_header(std::move(outer_scope));
            return result;
        };

        auto parsed_member_template_owner =
            [&]() -> std::optional<cir::EntityId> {
            RevertingTentativeParsingAction tentative(
                *this,
                TentativeMode::CollectBacked);
            DeferTemplateQualifierInstantiation defer(*this);

            collect::Session::TemplateInfo outer_probe = info;
            collect::Session::InstantiationScope outer_scope =
                collect_session_.begin_template_header(outer_probe,
                                                       template_token.loc);

            Token inner_template = current();
            consume();
            collect::Session::TemplateInfo member_probe;
            if (!parse_cxx_template_head(member_probe, inner_template.loc)) {
                collect_session_.finish_template_header(std::move(outer_scope));
                return std::nullopt;
            }
            collect::Session::InstantiationScope member_scope =
                collect_session_.begin_template_header(member_probe,
                                                       inner_template.loc);

            ParsedDeclarator declarator;
            if (starts_qualified_conversion_function_id()) {
                std::optional<ParsedConversionFunctionDeclarator> conversion =
                    parse_conversion_function_declarator(
                        /*require_qualified=*/true);
                if (conversion) {
                    declarator = std::move(conversion->declarator);
                }
            } else {
                DeclarationParser probe_parser(
                    *this, template_declaration_type_context);

                select_partial_for_deferred_class_template_qualifier_ = true;
                cir::TypeRef base =
                    probe_parser.parse_declaration(false, true);
                select_partial_for_deferred_class_template_qualifier_ = false;
                defer_class_template_qualifier_instantiation_ = true;
                declarator = probe_parser.parse_declarator(base, false);
            }

            const collect::Session::TemplateInfo* owner =
                declarator.template_qualifier_info;
            bool candidate =
                declarator.has_name && owner && owner->is_class_template &&
                declarator.qualified_context.valid();
            if (candidate) {
                const cir::File& file = collect_session_.file();
                candidate =
                    file.decl_context(declarator.qualified_context).kind ==
                    cir::DeclContextKind::Record;
            }
            if (candidate) {
                stacked_member_tail = current_raw_index();
                stacked_member_tail_last_end = last_consumed_raw_end_;
                stacked_member_is_function = declarator.is_function;
            }
            const collect::Session::TemplateInfo* enclosing_owner = nullptr;
            if (candidate && owner->lexical_context.valid()) {
                const cir::File& file = collect_session_.file();
                const cir::DeclContext& lexical =
                    file.decl_context(owner->lexical_context);
                if (lexical.kind == cir::DeclContextKind::Record) {
                    const collect::Session::TemplateInfo* enclosing =
                        collect_session_.template_info_for_pattern_record(
                            lexical.owner);
                    if (enclosing && enclosing->is_class_template) {
                        enclosing_owner = enclosing;
                    }
                }
            }

            // The head/slot mapping below reconciles the outer head's
            // parameters against the qualifier arguments of `owner`.  When
            // the registration is redirected it describes the wrong level, so
            // leave it empty and let the replay derive the binding.
            if (candidate && !enclosing_owner &&
                !owner->is_partial_specialization) {
                collect::Session::PartialSpecializationSelection
                    selection =
                        select_template_partial_specialization(
                            *owner,
                            declarator.template_qualifier_arguments,
                            declarator.loc);
                if (selection.info) {
                    owner = selection.info;
                }
            }
            if (candidate && owner && !enclosing_owner &&
                !owner->is_partial_specialization) {
                const std::vector<collect::Session::TemplateArgument>&
                    written = declarator.template_qualifier_arguments;
                std::vector<uint32_t> slots(outer_probe.parameters.size(),
                                            UINT32_MAX);
                bool total = !outer_probe.parameters.empty() &&
                             written.size() == outer_probe.parameters.size() &&
                             owner->parameters.size() == written.size() &&
                             collect_session_.template_parameter_lists_match(
                                 owner->parameters,
                                 outer_probe.parameters);
                for (size_t slot = 0; total && slot < written.size(); ++slot) {
                    const collect::Session::TemplateArgument& argument =
                        written[slot];
                    bool matched = false;
                    for (size_t j = 0; j < outer_probe.parameters.size(); ++j) {
                        const collect::Session::TemplateParameter& parameter =
                            outer_probe.parameters[j];
                        if (parameter.is_parameter_pack ||
                            slots[j] != UINT32_MAX) {
                            continue;
                        }
                        bool names_parameter = false;
                        if (parameter.kind ==
                                collect::Session::TemplateParameterKind::Type) {
                            names_parameter =
                                argument.kind ==
                                    cir::TemplateArgumentKind::Type &&
                                argument.type.type.valid() &&
                                argument.type.qualifiers == cir::QualNone &&
                                argument.type.type == parameter.type_param_type;
                        } else if (parameter.kind ==
                                   collect::Session::TemplateParameterKind::
                                       NonType) {
                            names_parameter =
                                argument.kind ==
                                    cir::TemplateArgumentKind::Value &&
                                argument.value_param_index == parameter.index;
                        } else {
                            names_parameter =
                                argument.kind ==
                                    cir::TemplateArgumentKind::Template &&
                                argument.template_param_index == parameter.index;
                        }
                        if (names_parameter) {
                            slots[j] = static_cast<uint32_t>(slot);
                            matched = true;
                            break;
                        }
                    }
                    if (!matched) {
                        total = false;
                    }
                }
                bool positional = total;
                bool renamed = false;
                for (size_t j = 0; total && j < slots.size(); ++j) {
                    if (slots[j] == UINT32_MAX) {
                        total = false;
                    } else if (slots[j] != j) {
                        positional = false;
                    } else if (outer_probe.parameters[j].name !=
                               owner->parameters[j].name) {
                        renamed = true;
                    }
                }
                if (total && !positional) {
                    stacked_head_invalid = true;
                    stacked_head_loc = declarator.loc;
                } else if (total && renamed) {
                    stacked_head_parameters = outer_probe.parameters;
                    stacked_head_owner_slots = std::move(slots);
                }
            }
            collect_session_.finish_template_header(std::move(member_scope));
            collect_session_.finish_template_header(std::move(outer_scope));
            if (!candidate) {
                return std::nullopt;
            }
            return enclosing_owner ? enclosing_owner->entity : owner->entity;
        };

        if (std::optional<cir::EntityId> class_owner =
                parsed_member_class_owner()) {
            if (const collect::Session::TemplateInfo* class_member_owner =
                    collect_session_.template_info(*class_owner)) {
                // Capture from the inner `template` keyword so the replay
                // re-enters this function with the member's own head.
                size_t member_begin = current_raw_index();
                size_t member_end = skip_balanced_until_semicolon_or_brace();
                match(TokenType::SEMICOLON);
                collect_session_.add_template_out_of_line_member(
                    class_member_owner->entity,
                    member_begin,
                    member_end,
                    /*is_template_declaration=*/true,
                    /*is_static_data_member_definition=*/false);
                if (const collect::Session::TemplateInfo* retained_owner =
                        collect_session_.template_info(
                            class_member_owner->entity)) {
                    const collect::Session::TemplateInfo::OutOfLineMember&
                        member = retained_owner->out_of_line_members.back();
                    replay_owner_member_for_existing_specializations(
                        *retained_owner,
                        member_begin,
                        /*is_template_declaration=*/true,
                        member.head_parameters,
                        member.head_parameter_owner_slots);
                }
                return {make_node(NodeKind::UnknownDecl,
                                  begin,
                                  last_consumed_raw_end(),
                                  {},
                                  text_payload("template")),
                        {}};
            }
        }

        const collect::Session::TemplateInfo* owner = nullptr;
        std::optional<cir::EntityId> parsed_owner =
            parsed_member_template_owner();
        if (stacked_head_invalid) {
            diagnose(DiagnosticLevel::Error,
                     "out-of-line member definition template arguments must "
                     "name its template parameters in declaration order",
                     stacked_head_loc);
            skip_balanced_until_semicolon_or_brace();
            match(TokenType::SEMICOLON);
            collect::DeclResult decl;
            decl.has_error = true;
            return {make_node(NodeKind::UnknownDecl,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              text_payload("template"),
                              NodeFlagHasError),
                    std::move(decl)};
        }
        if (parsed_owner.has_value()) {
            owner = collect_session_.template_info(*parsed_owner);
        }
        if (!owner) {
            size_t offset = 0;
            while (!at_end()) {
                const Token& token = peek(offset);
                if (token.type == TokenType::LEFT_BRACE ||
                    token.type == TokenType::SEMICOLON ||
                    token.type == TokenType::Eof) {
                    break;
                }
                if (is_identifier_token(token.type) &&
                    peek(offset + 1).type == TokenType::LESS_THAN &&
                    template_id_precedes_scope(offset)) {
                    size_t scope_offset =
                        template_id_scope_offset(offset);
                    size_t terminal_offset = scope_offset + 1;
                    TokenType terminal_type =
                        peek(terminal_offset).type;
                    TokenType suffix_type =
                        peek(terminal_offset + 1).type;
                    bool declarator_qualifier =
                        is_identifier_token(terminal_type) &&
                        (suffix_type == TokenType::LEFT_PAREN ||
                         suffix_type == TokenType::LEFT_BRACKET ||
                         suffix_type == TokenType::ASSIGN ||
                         suffix_type == TokenType::LEFT_BRACE ||
                         suffix_type == TokenType::SEMICOLON);
                    const collect::Session::TemplateInfo* candidate =
                        collect_session_.template_info_for_name(token.value);
                    if (declarator_qualifier && candidate &&
                        candidate->is_class_template) {
                        owner = candidate;
                        break;
                    }
                }
                ++offset;
            }
        }
        if (owner) {
            size_t member_begin = current_raw_index();
            size_t member_end = member_begin;
            if (stacked_member_tail == SIZE_MAX) {

                member_end = skip_balanced_until_semicolon_or_brace();
            } else {
                member_end = capture_out_of_line_member_end(
                    stacked_member_tail,
                    stacked_member_tail_last_end,
                    stacked_member_is_function);
            }
            match(TokenType::SEMICOLON);
            collect_session_.add_template_out_of_line_member(
                owner->entity,
                member_begin,
                member_end,
                /*is_template_declaration=*/true,
                /*is_static_data_member_definition=*/false,
                std::move(stacked_head_parameters),
                std::move(stacked_head_owner_slots));
            const collect::Session::TemplateInfo* retained_owner =
                collect_session_.template_info(owner->entity);
            if (retained_owner) {
                const collect::Session::TemplateInfo::OutOfLineMember& member =
                    retained_owner->out_of_line_members.back();
                replay_owner_member_for_existing_specializations(
                    *retained_owner,
                    member_begin,
                    /*is_template_declaration=*/true,
                    member.head_parameters,
                    member.head_parameter_owner_slots);
            }
            return {make_node(NodeKind::UnknownDecl,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              text_payload("template")),
                    {}};
        }
    }

    if (!info.parameters.empty() &&
        (check(TokenType::STRUCT) || check(TokenType::CLASS) ||
         check(TokenType::UNION) || check(TokenType::ENUM))) {
        const collect::Session::TemplateInfo* owner = nullptr;
        std::vector<collect::Session::TemplateParameter> mapped_parameters;
        std::vector<uint32_t> mapped_slots;
        OwnerHeadMappingResult mapping = OwnerHeadMappingResult::Invalid;
        {
            RevertingTentativeParsingAction tentative(
                *this,
                TentativeMode::CollectBacked);
            struct DeferTemplateQualifierInstantiation {
                Parser& parser;
                bool previous = false;
                explicit DeferTemplateQualifierInstantiation(Parser& parser)
                    : parser(parser),
                      previous(
                          parser.defer_class_template_qualifier_instantiation_) {
                    parser.defer_class_template_qualifier_instantiation_ = true;
                }
                ~DeferTemplateQualifierInstantiation() {
                    parser.defer_class_template_qualifier_instantiation_ =
                        previous;
                }
            } defer(*this);

            collect::Session::TemplateInfo probe_info = info;
            collect::Session::InstantiationScope header_scope =
                collect_session_.begin_template_header(probe_info,
                                                       template_token.loc);
            bool enum_head = check(TokenType::ENUM);
            consume();
            if (enum_head &&
                (check(TokenType::CLASS) || check(TokenType::STRUCT))) {
                consume();
            }
            ParsedNestedName nested = parse_nested_name_specifier();
            bool candidate = nested.consumed_any && !nested.has_error &&
                             nested.template_qualifier_info &&
                             nested.template_qualifier_info->is_class_template &&
                             is_identifier_token(current().type);
            if (candidate) {
                owner = nested.template_qualifier_info;
                mapping = map_owner_head(probe_info,
                                         *owner,
                                         nested.template_qualifier_arguments,
                                         mapped_parameters,
                                         mapped_slots);
            }
            collect_session_.finish_template_header(std::move(header_scope));
            if (!candidate) {
                owner = nullptr;
            }
        }
        if (owner && mapping != OwnerHeadMappingResult::Invalid) {
            size_t member_begin = current_raw_index();
            size_t member_end = skip_balanced_until_semicolon_or_brace();
            match(TokenType::SEMICOLON);
            collect_session_.add_template_out_of_line_member(
                owner->entity,
                member_begin,
                member_end,
                /*is_template_declaration=*/false,
                /*is_static_data_member_definition=*/false,
                std::move(mapped_parameters),
                std::move(mapped_slots));
            const collect::Session::TemplateInfo* retained_owner =
                collect_session_.template_info(owner->entity);
            if (retained_owner) {
                const collect::Session::TemplateInfo::OutOfLineMember& member =
                    retained_owner->out_of_line_members.back();
                replay_owner_member_for_existing_specializations(
                    *retained_owner,
                    member_begin,
                    /*is_template_declaration=*/false,
                    member.head_parameters,
                    member.head_parameter_owner_slots);
            }
            return {make_node(NodeKind::UnknownDecl,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              text_payload("template")),
                    {}};
        }
    }

    if (info.parameters.empty()) {
        if (check(TokenType::STRUCT) || check(TokenType::CLASS) ||
            check(TokenType::UNION)) {
            size_t saved_cursor = cursor_;
            size_t saved_last_end = last_consumed_raw_end_;
            consume();
            ParsedNestedName nested = parse_nested_name_specifier();
            bool ordinary_member_class =
                nested.consumed_any && !nested.has_error &&
                nested.scope.context.valid() &&
                collect_session_.file().decl_context(nested.scope.context).kind ==
                    cir::DeclContextKind::Record &&
                is_identifier_token(current().type) &&
                peek(1).type != TokenType::LESS_THAN;
            cursor_ = saved_cursor;
            last_consumed_raw_end_ = saved_last_end;
            if (ordinary_member_class) {
                bool saved_explicit_member_record_specialization =
                    explicit_member_record_specialization_;
                explicit_member_record_specialization_ = true;
                ParsedDecl explicit_member_class = parse_declaration(true);
                explicit_member_record_specialization_ =
                    saved_explicit_member_record_specialization;
                return {make_node(explicit_member_class.sem.has_error
                                      ? NodeKind::UnknownDecl
                                      : NodeKind::RecordDecl,
                                  begin,
                                  last_consumed_raw_end(),
                                  {explicit_member_class.syntax},
                                  text_payload("template<>"),
                                  explicit_member_class.sem.has_error
                                      ? NodeFlagHasError
                                      : NodeFlagNone),
                        std::move(explicit_member_class.sem)};
            }
        }
        if (check(TokenType::TEMPLATE) &&
            peek(1).type == TokenType::LESS_THAN &&
            peek(2).type == TokenType::GREATER_THAN &&
            (peek(3).type == TokenType::STRUCT ||
             peek(3).type == TokenType::CLASS ||
             peek(3).type == TokenType::UNION)) {
            size_t saved_cursor = cursor_;
            size_t saved_last_end = last_consumed_raw_end_;
            consume();
            consume();
            consume();
            if (std::optional<ParsedDecl> explicit_member_class_template =
                    try_parse_explicit_class_template_specialization(
                        begin,
                        template_token.loc)) {
                return std::move(*explicit_member_class_template);
            }
            cursor_ = saved_cursor;
            last_consumed_raw_end_ = saved_last_end;
        }
        if (std::optional<ParsedDecl> explicit_class =
                try_parse_explicit_class_template_specialization(
                    begin,
                    template_token.loc)) {
            return std::move(*explicit_class);
        }
        if (check(TokenType::ENUM)) {

            ParsedDecl explicit_member_enum = parse_declaration(true);
            return {make_node(explicit_member_enum.sem.has_error
                                  ? NodeKind::UnknownDecl
                                  : NodeKind::RecordDecl,
                              begin,
                              last_consumed_raw_end(),
                              {explicit_member_enum.syntax},
                              text_payload("template<>"),
                              explicit_member_enum.sem.has_error
                                  ? NodeFlagHasError
                                  : NodeFlagNone),
                    std::move(explicit_member_enum.sem)};
        }
    }

    if (info.parameters.empty()) {
        TemplateArgumentAccessExemptionScope access_exemption(
            collect_session_);
        ParserCheckpoint checkpoint = capture_parser_checkpoint();
        size_t saved_cursor = cursor_;
        size_t saved_last_end = last_consumed_raw_end_;
        bool inner_explicit_template_head = false;
        if (check(TokenType::TEMPLATE) &&
            peek(1).type == TokenType::LESS_THAN &&
            peek(2).type == TokenType::GREATER_THAN) {
            consume();
            consume();
            consume();
            inner_explicit_template_head = true;
        }
        DeclarationParser specialization_parser(
            *this, template_declaration_type_context);
        cir::TypeRef base =
            specialization_parser.parse_declaration(false, true);
        ParsedDeclarator declarator =
            specialization_parser.parse_declarator(base, false);
        bool candidate =
            declarator.has_name && !declarator.is_function &&
            declarator.type_ref.valid() && check(TokenType::LESS_THAN);
        auto lookup_variable_template_primary =
            [&](const ParsedDeclarator& parsed)
                -> const collect::Session::TemplateInfo* {
            if (!candidate) {
                return nullptr;
            }
            const cir::Binding* binding = nullptr;
            if (parsed.qualified_context.valid()) {
                binding =
                    collect_session_.file().lookup_template_name_binding(
                        parsed.qualified_context,
                        parsed.name,
                        /*include_parents=*/false);
            } else {
                return collect_session_.template_info_for_name(parsed.name);
            }
            if (!binding || binding->entities.empty()) {
                return nullptr;
            }
            return collect_session_.template_info(binding->entities.back());
        };
        const collect::Session::TemplateInfo* primary =
            lookup_variable_template_primary(declarator);
        if (!primary || !primary->is_variable_template) {
            cursor_ = saved_cursor;
            last_consumed_raw_end_ = saved_last_end;
            restore_parser_checkpoint(checkpoint);
        } else {
            std::vector<NodeId> children;
            if (specialization_parser.type_syntax != InvalidNodeId) {
                children.push_back(specialization_parser.type_syntax);
            }
            if (declarator.syntax != InvalidNodeId) {
                children.push_back(declarator.syntax);
            }

            std::vector<collect::Session::TemplateArgument> arguments;
            if (!parse_and_canonicalize_template_argument_list(
                    *primary,
                    arguments,
                    declarator.loc)) {
                skip_balanced_until_semicolon_or_brace();
                collect::DeclResult decl;
                decl.has_error = true;
                return {make_node(NodeKind::UnknownDecl,
                                  begin,
                                  last_consumed_raw_end(),
                                  children,
                                  text_payload("template"),
                                  NodeFlagHasError),
                        std::move(decl)};
            }

            bool has_invalid_storage_class =
                specialization_parser.storage_class != StorageClass::None;
            bool specialization_has_error = has_invalid_storage_class;
            if (!check_non_function_template_associated_constraints(
                    *primary,
                    arguments,
                    declarator.loc,
                    collect_session_.lookup_generation())) {
                specialization_has_error = true;
            }
            if (has_invalid_storage_class) {
                diagnose(DiagnosticLevel::Error,
                         "explicit specialization cannot use a storage class specifier",
                         specialization_parser.begin_loc);
            }
            bool static_data_member_template_specialization =
                primary->lexical_context.valid() &&
                collect_session_.file()
                        .decl_context(primary->lexical_context)
                        .kind == cir::DeclContextKind::Record;
            bool owner_is_class_template_specialization = false;
            if (static_data_member_template_specialization &&
                declarator.qualified_context.valid()) {
                const cir::DeclContext& owner_context =
                    collect_session_.file()
                        .decl_context(declarator.qualified_context);
                owner_is_class_template_specialization =
                    owner_context.owner.valid() &&
                    collect_session_.file().template_specialization(
                        owner_context.owner) != nullptr;
            }
            if (inner_explicit_template_head &&
                !owner_is_class_template_specialization) {
                diagnose(DiagnosticLevel::Error,
                         "unexpected 'template<>' in explicit static data member template specialization",
                         declarator.loc);
                specialization_has_error = true;
            } else if (owner_is_class_template_specialization &&
                       !inner_explicit_template_head) {
                diagnose(DiagnosticLevel::Error,
                         "explicit specialization of member template of class template requires 'template<>'",
                         declarator.loc);
                specialization_has_error = true;
            }

            std::string asm_label;
            if (check(TokenType::ASM_KW)) {
                children.push_back(parse_asm_label_syntax(&asm_label));
            }
            ParsedAttributes trailing_attrs = try_parse_attributes();
            declarator.attrs.append(std::move(trailing_attrs.attrs));
            children.insert(children.end(),
                            trailing_attrs.syntax.begin(),
                            trailing_attrs.syntax.end());

            collect::DeclFlags flags;
            flags.is_constexpr = specialization_parser.is_constexpr;
            flags.is_consteval = specialization_parser.is_consteval;
            flags.is_constinit = specialization_parser.is_constinit;
            flags.is_inline = specialization_parser.is_inline;
            flags.is_thread_local = specialization_parser.is_thread_local;
            flags.is_extern =
                specialization_parser.storage_class == StorageClass::Extern;
            flags.is_static =
                specialization_parser.storage_class == StorageClass::Static;
            flags.is_auto_storage =
                specialization_parser.storage_class == StorageClass::Auto;
            flags.is_register =
                specialization_parser.storage_class == StorageClass::Register;
            flags.is_mutable = specialization_parser.is_mutable;
            flags.is_friend = specialization_parser.is_friend;
            flags.is_block_byref = specialization_parser.is_block_byref;
            flags.attrs = specialization_parser.leading_attrs;
            AttributeList merged_attrs = flags.attrs;
            merged_attrs.append(declarator.attrs);
            declarator.attrs = std::move(merged_attrs);
            flags.attrs = declarator.attrs;
            flags.asm_label = std::move(asm_label);
            flags.vla_bounds = std::move(declarator.vla_bounds);
            flags.type_qualifiers = declarator.type_ref.qualifiers;
            declarator.type_ref =
                collect_session_.apply_type_attributes(declarator.type_ref,
                                                       declarator.attrs,
                                                       declarator.loc);
            declarator.type = declarator.type_ref.type;

            collect::Session::PatternInstantiationCallbacks callbacks;
            callbacks.instantiate_type_template =
                [this, loc = declarator.loc](
                    cir::EntityId template_entity,
                    std::vector<collect::Session::TemplateArgument> args,
                    uint64_t point_lookup_generation,
                    bool materialize_type_template_definition,
                    collect::Session::TemplateArgumentCompletionMode
                        completion_mode)
                -> cir::TypeRef {
                const collect::Session::TemplateInfo* target =
                    collect_session_.template_info(template_entity);
                if (!target) {
                    return {};
                }
                cir::EntityId record =
                    instantiate_template_with_args(*target,
                                                   std::move(args),
                                                   loc,
                                                   point_lookup_generation,
                                                   false,
                                                   false,
                                                   materialize_type_template_definition,
                                                   true,
                                                   completion_mode);
                if (!record.valid()) {
                    return {};
                }
                const cir::Entity& entity =
                    collect_session_.file().entity(record);
                return {entity.type, entity.qualifiers, entity.memory_space};
            };
            cir::TypeRef primary_type = primary->variable_type_ref.valid()
                ? primary->variable_type_ref
                : collect_session_.type_ref(primary->variable_type);
            auto argument_bindings = canonical_template_argument_bindings(
                collect_session_, primary->parameters, arguments);
            cir::TypeId expected_type =
                argument_bindings.has_value()
                    ? collect_session_.substitute_pattern_type(
                          primary_type.type,
                          *argument_bindings,
                          callbacks)
                    : cir::TypeId{};
            if (!expected_type.valid()) {
                diagnose(DiagnosticLevel::Error,
                         "variable template specialization type substitution failed",
                         declarator.loc);
                specialization_has_error = true;
            } else {
                cir::TypeRef expected_ref{expected_type,
                                          primary_type.qualifiers,
                                          primary_type.memory_space};
                cir::TypeRef written_ref = declarator.type_ref;

                if (primary->variable_const_qualification_is_implicit) {
                    expected_ref.qualifiers = static_cast<uint8_t>(
                        expected_ref.qualifiers & ~cir::QualConst);
                }
                if (declarator.constexpr_const_is_implicit) {
                    written_ref.qualifiers = static_cast<uint8_t>(
                        written_ref.qualifiers & ~cir::QualConst);
                }
                if (!collect_session_.types_compatible(expected_ref,
                                                       written_ref)) {
                    diagnose(DiagnosticLevel::Error,
                             "explicit variable template specialization has incompatible type",
                             declarator.loc);
                    specialization_has_error = true;
                }
            }

            std::string memo_key =
                collect_session_.template_memo_key(primary->entity,
                                                   arguments);
            cir::EntityId cached =
                collect_session_.cached_instantiation(memo_key);
            bool cached_implicit = false;
            bool cached_definition = false;
            if (cached.valid() && collect_session_.file().valid(cached)) {
                const cir::Entity& previous =
                    collect_session_.file().entity(cached);
                cached_implicit =
                    previous.linkage == cir::LinkageKind::LinkOnceODR;
                cached_definition = previous.is_definition;
            }
            bool has_initializer_syntax =
                check(TokenType::ASSIGN) ||
                check(TokenType::LEFT_BRACE) ||
                (lang_opts_.is_cxx_mode() && check(TokenType::LEFT_PAREN));
            bool specialization_is_definition =
                static_data_member_template_specialization
                    ? has_initializer_syntax
                    : !(flags.is_extern && !has_initializer_syntax);
            if (static_data_member_template_specialization &&
                !has_initializer_syntax) {
                flags.is_declaration_only = true;
            }
            auto note_implicit_instantiation_point =
                [&](cir::EntityId specialization) {
                    const cir::TemplateSpecializationFact* fact =
                        collect_session_.file().template_specialization(
                            specialization);
                    if (fact &&
                        !fact->point_of_instantiation.isInvalid()) {
                        diagnose(DiagnosticLevel::Note,
                                 "implicit instantiation first required here",
                                 fact->point_of_instantiation);
                    }
                };
            if (cached_implicit) {
                diagnose(DiagnosticLevel::Error,
                         static_data_member_template_specialization
                             ? "explicit specialization of static data member template after implicit instantiation"
                             : "explicit specialization of variable template after implicit instantiation",
                         declarator.loc);
                note_implicit_instantiation_point(cached);
                specialization_has_error = true;
            } else if (cached_definition && specialization_is_definition) {
                diagnose(DiagnosticLevel::Error,
                         static_data_member_template_specialization
                             ? "redefinition of explicit static data member template specialization"
                             : "redefinition of explicit variable template specialization",
                         declarator.loc);
                specialization_has_error = true;
            }

            declarator.name =
                collect_session_.template_display_name(*primary, arguments);

            access_exemption.finish();
            collect::DeclResult decl =
                handle_variable_declarator(declarator,
                                           /*top_level=*/true,
                                           children,
                                           std::move(flags));
            decl.has_error = decl.has_error || specialization_has_error;
            if (decl.entity.valid()) {
                if (!cached_implicit &&
                    !(cached_definition && specialization_is_definition)) {
                    if (cached.valid()) {
                        const cir::Entity& previous =
                            collect_session_.file().entity(cached);
                        const cir::Entity& current =
                            collect_session_.file().entity(decl.entity);
                        if (!previous.is_definition &&
                            current.is_definition) {
                            collect_session_.replace_instantiation(memo_key,
                                                                   decl.entity);
                        }
                    } else {
                        collect_session_.remember_instantiation(memo_key,
                                                                decl.entity);
                    }
                }
                collect_session_.remember_template_specialization(decl.entity,
                                                                *primary,
                                                                arguments);
            }
            if (!match(TokenType::SEMICOLON)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ';' after explicit variable template specialization",
                         current_loc());
                skip_until_statement_boundary();
                decl.has_error = true;
            }
            if (decl.entity.valid() && !decl.has_error) {
                collect_session_.mark_explicit_template_specialization(
                    decl.entity);
            }
            return {make_node(decl.has_error ? NodeKind::UnknownDecl
                                             : NodeKind::VarDecl,
                              begin,
                              last_consumed_raw_end(),
                              children,
                              text_payload("template"),
                              decl.has_error ? NodeFlagHasError : 0),
                    std::move(decl)};
        }
    }

    if (info.parameters.empty()) {
        if (check(TokenType::TEMPLATE) &&
            peek(1).type == TokenType::LESS_THAN &&
            peek(2).type == TokenType::GREATER_THAN) {
            ParserCheckpoint checkpoint = capture_parser_checkpoint();
            size_t saved_cursor = cursor_;
            size_t saved_last_end = last_consumed_raw_end_;
            consume();
            consume();
            consume();
            if (std::optional<ParsedDecl> explicit_member_template =
                    try_parse_explicit_function_template_specialization(
                        begin,
                        template_token.loc,
                        /*has_member_template_head=*/true)) {
                return std::move(*explicit_member_template);
            }
            cursor_ = saved_cursor;
            last_consumed_raw_end_ = saved_last_end;
            restore_parser_checkpoint(checkpoint);
        }
        if (std::optional<ParsedDecl> explicit_member_function =
                try_parse_explicit_member_function_specialization(
                    begin,
                    template_token.loc)) {
            return std::move(*explicit_member_function);
        }
        if (std::optional<ParsedDecl> explicit_static_member =
                try_parse_explicit_static_data_member_specialization(
                    begin,
                    template_token.loc)) {
            return std::move(*explicit_static_member);
        }
        if (std::optional<ParsedDecl> explicit_function =
                try_parse_explicit_function_template_specialization(
                    begin,
                    template_token.loc)) {
            return std::move(*explicit_function);
        }
    }

    if (std::optional<ParsedDecl> deduction_guide =
            try_parse_cxx_deduction_guide_declaration(&info,
                                                      template_token.loc,
                                                      begin)) {
        return std::move(*deduction_guide);
    }

    if (check(TokenType::CONCEPT_KW)) {
        Token concept_token = current();
        consume();
        collect::DeclResult decl;
        bool has_error = false;

        if (!is_identifier_token(current().type)) {
            diagnose(DiagnosticLevel::Error,
                     "expected concept name after 'concept'",
                     concept_token.loc);
            skip_until_statement_boundary();
            decl.has_error = true;
            return {make_node(NodeKind::UnknownDecl,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              text_payload("template"),
                              NodeFlagHasError),
                    std::move(decl)};
        }

        info.is_concept = true;
        info.name = current().value;
        consume();
        ParsedAttributes concept_attrs = try_parse_attributes();
        info.declaration_attrs = std::move(concept_attrs.attrs);

        cir::DeclContextId current_context =
            collect_session_.current_decl_context();
        bool namespace_scope = false;
        if (current_context.valid()) {
            const cir::DeclContext& context =
                collect_session_.file().decl_context(current_context);
            namespace_scope =
                context.kind == cir::DeclContextKind::TranslationUnit ||
                context.kind == cir::DeclContextKind::Namespace;
        }
        if (!namespace_scope) {
            diagnose(DiagnosticLevel::Error,
                     "concept definition shall inhabit namespace scope",
                     concept_token.loc);
            has_error = true;
        }
        if (!info.introduced_constraints.empty()) {
            diagnose(DiagnosticLevel::Error,
                     "concept cannot have associated constraints",
                     concept_token.loc);
            has_error = true;
        }

        if (!match(TokenType::ASSIGN)) {
            diagnose(DiagnosticLevel::Error,
                     "expected '=' in concept definition",
                     current_loc());
            skip_until_statement_boundary();
            decl.has_error = true;
            return {make_node(NodeKind::UnknownDecl,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              text_payload("template"),
                              NodeFlagHasError),
                    std::move(decl)};
        }

        size_t constraint_begin = current_raw_index();
        bool saw_semicolon = false;
        auto skip_constraint_expression = [&]() {
            int parens = 0;
            int brackets = 0;
            int braces = 0;
            size_t end = current_raw_index();
            while (!at_end()) {
                TokenType type = current().type;
                if (type == TokenType::SEMICOLON && parens == 0 &&
                    brackets == 0 && braces == 0) {
                    end = current_raw_index();
                    consume();
                    saw_semicolon = true;
                    return end;
                }
                consume();
                end = last_consumed_raw_end();
                if (type == TokenType::LEFT_PAREN) ++parens;
                if (type == TokenType::RIGHT_PAREN && parens > 0) --parens;
                if (type == TokenType::LEFT_BRACKET) ++brackets;
                if (type == TokenType::RIGHT_BRACKET && brackets > 0) {
                    --brackets;
                }
                if (type == TokenType::LEFT_BRACE) ++braces;
                if (type == TokenType::RIGHT_BRACE && braces > 0) --braces;
            }
            return end;
        };
        size_t constraint_end = skip_constraint_expression();
        if (!saw_semicolon) {
            diagnose(DiagnosticLevel::Error,
                     "expected ';' after concept definition",
                     current_loc());
            has_error = true;
        }

        info.constraint_begin = constraint_begin;
        info.constraint_end = constraint_end;
        info.definition_begin = begin;
        info.definition_end = constraint_end;
        info.has_definition = true;
        std::optional<collect::Session::NormalizedConstraint>
            concept_normal_form;
        auto validate_constraint_expression = [&]() -> bool {
            size_t saved_cursor = cursor_;
            size_t saved_last_consumed_raw_end = last_consumed_raw_end_;
            bool was_in_template_definition =
                collect_session_.in_template_definition();

            collect::Session::InstantiationScope header_scope =
                collect_session_.begin_template_header(info, template_token.loc);
            collect_session_.set_in_template_definition(true);
            collect_session_.begin_template_validation(info);
            collect_session_.begin_pattern_collection();
            uint64_t taint_before = collect_session_.pattern_taint();

            seek_raw_index(constraint_begin);
            bool saved_retain_constraint_normal_form_syntax =
                retain_constraint_normal_form_syntax_;
            ++requires_expression_template_context_depth_;
            retain_constraint_normal_form_syntax_ = true;
            ParsedExpr expression = parse_constraint_expression();
            retain_constraint_normal_form_syntax_ =
                saved_retain_constraint_normal_form_syntax;
            --requires_expression_template_context_depth_;
            std::optional<collect::Session::NormalizedConstraint>
                parsed_normal_form;
            if (!expression.sem.has_error) {
                collect::Session::NormalizedConstraint normal_form;
                uint32_t root =
                    normalize_direct_constraint_expression_syntax(
                        expression.syntax,
                        normal_form);
                if (normal_form.valid_node(root)) {
                    normal_form.root = root;
                    normal_form.value_expression =
                        expression.sem.template_value_expr;
                    collect_session_.file()
                        .canonicalize_template_value_expression(
                            normal_form.value_expression);
                    parsed_normal_form = std::move(normal_form);
                }
            }
            bool value_dependent =
                collect_session_.pattern_taint() != taint_before ||
                collect_session_.expr_is_dependent(expression.sem) ||
                expression.sem.references_template_value_parameter;
            bool consumed_full_expression = current_raw_index() == constraint_end;
            SrcLoc expression_loc = loc_for_index(constraint_begin);
            bool valid = !expression.sem.has_error;
            if (!consumed_full_expression) {
                diagnose(DiagnosticLevel::Error,
                         "expected ';' after concept constraint-expression",
                         current_loc());
                valid = false;
            }
            if (valid) {
                std::optional<bool> value;
                valid =
                    collect_session_.evaluate_constraint_expression(
                        std::move(expression.sem),
                        value_dependent,
                        value,
                        expression_loc);
            }

            (void)collect_session_.finish_pattern_collection();
            collect_session_.finish_template_validation();
            collect_session_.set_in_template_definition(
                was_in_template_definition);
            collect_session_.finish_template_header(std::move(header_scope));
            cursor_ = saved_cursor;
            last_consumed_raw_end_ = saved_last_consumed_raw_end;
            if (valid && parsed_normal_form.has_value()) {
                concept_normal_form = std::move(parsed_normal_form);
            }
            return valid;
        };
        if (!has_error && !validate_constraint_expression()) {
            has_error = true;
        }
        if (!has_error) {
            info.constraint_normal_form = std::move(concept_normal_form);
        }
        if (!has_error) {
            collect_session_.declare_template(std::move(info),
                                              template_token.loc);
        }
        decl.has_error = has_error;
        return {make_node(NodeKind::UnknownDecl,
                          begin,
                          last_consumed_raw_end(),
                          {},
                          text_payload("template"),
                          has_error ? NodeFlagHasError : 0),
                std::move(decl)};
    }

    if (check(TokenType::USING)) {
        Token using_token = current();
        consume();
        if (!is_identifier_token(current().type)) {
            diagnose(DiagnosticLevel::Error,
                     "expected alias template name after 'using'",
                     using_token.loc);
            skip_until_statement_boundary();
            collect::DeclResult decl;
            decl.has_error = true;
            return {make_node(NodeKind::UnknownDecl,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              text_payload("template"),
                              NodeFlagHasError),
                    std::move(decl)};
        }
        info.is_alias_template = true;
        info.name = current().value;
        consume();
        size_t alias_attribute_begin = current_raw_index();
        collect::Session::InstantiationScope alias_scope =
            collect_session_.begin_template_header(info, template_token.loc);
        ParsedAttributes alias_attributes =
            try_parse_standard_or_gnu_attributes();
        size_t alias_attribute_end = current_raw_index();
        if (!match(TokenType::ASSIGN)) {
            collect_session_.finish_template_header(std::move(alias_scope));
            diagnose(DiagnosticLevel::Error,
                     "expected '=' in alias template declaration",
                     current_loc());
            skip_until_statement_boundary();
            collect::DeclResult decl;
            decl.has_error = true;
            return {make_node(NodeKind::UnknownDecl,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              text_payload("template"),
                              NodeFlagHasError),
                    std::move(decl)};
        }
        size_t alias_type_begin = current_raw_index();
        cir::TypeId target_type{};
        cir::TypeRef target_type_ref{};
        parse_type_name(
            &target_type,
            nullptr,
            nullptr,
            &target_type_ref,
            nullptr,
            nullptr,
            TypeParseContext::type_only(
                TypeParseContext::Origin::DefiningTypeId));
        collect_session_.finish_template_header(std::move(alias_scope));
        if (!target_type.valid()) {
            diagnose(DiagnosticLevel::Error,
                     "expected defining type-id in alias template declaration",
                     current_loc());
            skip_until_statement_boundary();
            collect::DeclResult decl;
            decl.has_error = true;
            return {make_node(NodeKind::UnknownDecl,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              text_payload("template"),
                              NodeFlagHasError),
                    std::move(decl)};
        }
        info.alias_target_type = target_type;
        info.alias_target_type_ref = target_type_ref;
        info.alias_type_attribute_begin = alias_attribute_begin;
        info.alias_type_attribute_end = alias_attribute_end;
        for (const ParsedAttribute& attr : alias_attributes.attrs.attrs) {
            if (attr.args.size() != 1 ||
                attr.args.front().dependent_value_param_index == UINT32_MAX) {
                continue;
            }
            using Transform =
                collect::Session::TemplateInfo::AliasTypeTransformKind;
            if (attr.kind == AttributeKind::VectorSize) {
                info.alias_type_transform_kind = Transform::VectorSize;
            } else if (attr.kind == AttributeKind::ExtVectorType) {
                info.alias_type_transform_kind = Transform::ExtVectorType;
            } else if (attr.kind == AttributeKind::NeonVectorType) {
                info.alias_type_transform_kind = Transform::NeonVectorType;
            } else {
                continue;
            }
            info.alias_type_transform_parameter =
                attr.args.front().dependent_value_param_index;
            break;
        }
        cir::TypeId resolved_alias_target =
            collect_session_.file().resolved_type(target_type);
        cir::EntityId projected_template{};
        std::vector<collect::Session::TemplateArgument>
            projected_arguments;
        if (collect_session_.file().valid(resolved_alias_target)) {
            if (collect_session_.file().type(resolved_alias_target).kind ==
                cir::TypeKind::Record) {
                cir::EntityId record =
                    collect_session_.file().record_entity(
                        resolved_alias_target);
                if (const cir::TemplateSpecializationFact* specialization =
                        collect_session_.file().template_specialization(record)) {
                    projected_template = specialization->template_entity;
                    projected_arguments =
                        specialization->template_arguments();
                }
            } else if (collect_session_.file()
                           .type(resolved_alias_target)
                           .kind == cir::TypeKind::TemplateSpecialization) {
                const auto* specialization =
                    std::get_if<cir::TemplateSpecializationTypePayload>(
                        &collect_session_.file().type_payload(
                            resolved_alias_target));
                if (specialization) {
                    projected_template = specialization->primary_template;
                    projected_arguments = specialization->arguments;
                }
            }
        }
        const collect::Session::TemplateInfo* projected_info =
            projected_template.valid()
                ? collect_session_.template_info(projected_template)
                : nullptr;
        if (projected_info && projected_info->is_class_template &&
            !projected_info->is_partial_specialization) {
            info.alias_deduction_projection =
                collect::Session::TemplateInfo::AliasDeductionProjection{
                    projected_template,
                    std::move(projected_arguments)};
        }
        info.definition_begin = alias_type_begin;
        info.definition_end = current_raw_index();
        info.has_definition = true;
        if (!match(TokenType::SEMICOLON)) {
            diagnose(DiagnosticLevel::Error,
                     "expected ';' after alias template declaration",
                     current_loc());
            skip_until_statement_boundary();
        }
        collect_session_.declare_template(std::move(info), template_token.loc);
        return {make_node(NodeKind::UnknownDecl,
                          begin,
                          last_consumed_raw_end(),
                          std::move(alias_attributes.syntax),
                          text_payload("template")),
                {}};
    }

    if (std::optional<ParsedDecl> partial =
            try_parse_class_template_partial_specialization(
                info,
                begin,
                template_token.loc)) {
        return std::move(*partial);
    }

    auto is_class_template_record_head = [&]() {
        if (!check(TokenType::STRUCT) && !check(TokenType::CLASS) &&
            !check(TokenType::UNION)) {
            return false;
        }
        auto tail_follows = [&](size_t offset) {
            while (is_identifier_token(peek(offset).type) &&
                   peek(offset).value == "final") {
                ++offset;
            }
            return peek(offset).type == TokenType::LEFT_BRACE ||
                   peek(offset).type == TokenType::COLON ||
                   peek(offset).type == TokenType::SEMICOLON;
        };

        size_t head = skip_attribute_specifier_sequence_offset(1);
        if (is_identifier_token(peek(head).type) && tail_follows(head + 1)) {
            return true;
        }
        size_t offset = head;
        int angle_depth = 0;
        bool saw_scope = false;
        while (!at_end()) {
            const Token& token = peek(offset);
            if (angle_depth == 0 &&
                (token.type == TokenType::LEFT_BRACE ||
                 token.type == TokenType::COLON ||
                 token.type == TokenType::SEMICOLON)) {
                return saw_scope;
            }
            if (angle_depth == 0 && token.value == "final" &&
                tail_follows(offset)) {
                return saw_scope;
            }
            if (token.type == TokenType::Eof ||
                token.type == TokenType::LEFT_PAREN) {
                return false;
            }
            if (angle_depth == 0 &&
                token.type == TokenType::SCOPE_RESOLUTION) {
                saw_scope = true;
            }
            if (token.type == TokenType::LESS_THAN) {
                ++angle_depth;
            } else if (token.type == TokenType::GREATER_THAN &&
                       angle_depth > 0) {
                --angle_depth;
            }
            ++offset;
        }
        return false;
    };

    if (is_class_template_record_head()) {
        info.is_class_template = true;
        info.record_kind = check(TokenType::UNION)
            ? cir::RecordKind::Union
            : (check(TokenType::CLASS) ? cir::RecordKind::Class
                                      : cir::RecordKind::Struct);
        info.definition_begin = current_raw_index();
        const size_t class_head_name_offset =
            skip_attribute_specifier_sequence_offset(1);
        consume();

        for (size_t offset = 1;
             offset < class_head_name_offset;
             ++offset) {
            consume();
        }
        cir::DeclContextId qualified_context{};
        bool saw_qualified_context = false;
        bool invalid_qualified_context = false;
        if (!is_identifier_token(current().type) ||
            (peek(1).type != TokenType::LEFT_BRACE &&
             peek(1).type != TokenType::COLON &&
             peek(1).type != TokenType::SEMICOLON)) {
            ParsedNestedName nested = parse_nested_name_specifier();
            saw_qualified_context = nested.consumed_any;
            if (nested.consumed_any && !nested.has_error &&
                nested.scope.context.valid()) {
                const cir::File& file = collect_session_.file();
                cir::DeclContextId resolved_context = nested.scope.context;
                if (file.decl_context(resolved_context).kind !=
                        cir::DeclContextKind::Record &&
                    nested.scope.entity.valid() &&
                    file.valid(nested.scope.entity)) {
                    cir::DeclContextId entity_context =
                        file.entity(nested.scope.entity).semantic_context;
                    if (entity_context.valid() &&
                        file.decl_context(entity_context).kind ==
                            cir::DeclContextKind::Record) {
                        resolved_context = entity_context;
                    }
                }
                if (file.decl_context(resolved_context).kind ==
                    cir::DeclContextKind::Record) {
                    qualified_context = resolved_context;
                } else {
                    invalid_qualified_context = true;
                }
            } else if (nested.consumed_any) {
                invalid_qualified_context = true;
            }
        }
        if (saw_qualified_context && invalid_qualified_context) {
            diagnose(DiagnosticLevel::Error,
                     "qualified member class template definition qualifier does not name a class",
                     current_loc());
            skip_balanced_until_semicolon_or_brace();
            collect::DeclResult decl;
            decl.has_error = true;
            return {make_node(NodeKind::UnknownDecl,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              text_payload("template"),
                              NodeFlagHasError),
                    std::move(decl)};
        }
        if (!is_identifier_token(current().type)) {
            diagnose(DiagnosticLevel::Error,
                     "expected class template name",
                     current_loc());
            skip_balanced_until_semicolon_or_brace();
            collect::DeclResult decl;
            decl.has_error = true;
            return {make_node(NodeKind::UnknownDecl,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              text_payload("template"),
                              NodeFlagHasError),
                    std::move(decl)};
        }
        info.name = current().value;
        consume();
        cir::EntityId qualified_template_entity{};
        if (qualified_context.valid()) {
            const cir::File& file = collect_session_.file();
            const cir::Binding* binding =
                file.lookup_template_name_binding(qualified_context,
                                                  info.name,
                                                  /*include_parents=*/false);
            if (binding) {
                for (auto it = binding->entities.rbegin();
                     it != binding->entities.rend();
                     ++it) {
                    const collect::Session::TemplateInfo* previous =
                        collect_session_.template_info(*it);
                    if (previous && previous->is_class_template) {
                        qualified_template_entity = *it;
                        break;
                    }
                }
            }
        }
        if (check(TokenType::SEMICOLON)) {

            consume();
            info.definition_end = current_raw_index();
            info.has_definition = false;
        } else {
            size_t body_end = skip_balanced_until_semicolon_or_brace();
            info.definition_end = body_end;
            info.has_definition = true;
            if (!match(TokenType::SEMICOLON)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ';' after class template definition",
                         current_loc());
            }
        }
        if (qualified_context.valid() && !qualified_template_entity.valid()) {
            diagnose(DiagnosticLevel::Error,
                     "out-of-class member class template definition has no matching declaration",
                     template_token.loc);
            collect::DeclResult decl;
            decl.has_error = true;
            return {make_node(NodeKind::UnknownDecl,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              text_payload("template"),
                              NodeFlagHasError),
                    std::move(decl)};
        }
        struct QualifiedTemplateContextExit {
            collect::Session* session = nullptr;
            ~QualifiedTemplateContextExit() {
                if (session) {
                    session->leave_scope();
                }
            }
        } qualified_template_context;
        if (qualified_context.valid()) {
            collect_session_.enter_existing_context(
                qualified_context,
                collect::ScopeFlags::RecordScope);
            qualified_template_context.session = &collect_session_;
        }
        info.lexical_context = collect_session_.current_decl_context();
        if (info.has_definition &&
            !info.is_member_template_specialization_overlay) {
            validate_template_definition(info, template_token.loc);
        }
        if (qualified_template_entity.valid()) {
            collect::DeclResult decl;
            if (!collect_session_.define_member_class_template_entity(
                    std::move(info),
                    qualified_template_entity,
                    template_token.loc)) {
                decl.has_error = true;
                return {make_node(NodeKind::UnknownDecl,
                                  begin,
                                  last_consumed_raw_end(),
                                  {},
                                  text_payload("template"),
                                  NodeFlagHasError),
                        std::move(decl)};
            }
        } else {
            collect_session_.declare_template(std::move(info),
                                              template_token.loc);
        }
        return {make_node(NodeKind::UnknownDecl, begin, last_consumed_raw_end(),
                          {}, text_payload("template")),
                {}};
    }

    {
        auto parsed_static_owner =
            [&]() -> std::optional<const collect::Session::TemplateInfo*> {
            RevertingTentativeParsingAction tentative(
                *this,
                TentativeMode::CollectBacked);
            struct DeferTemplateQualifierInstantiation {
                Parser& parser;
                bool previous = false;
                bool previous_partial_selection = false;

                explicit DeferTemplateQualifierInstantiation(Parser& parser)
                    : parser(parser),
                      previous(
                          parser.defer_class_template_qualifier_instantiation_),
                      previous_partial_selection(
                          parser
                              .select_partial_for_deferred_class_template_qualifier_) {
                    parser.defer_class_template_qualifier_instantiation_ = true;
                }

                ~DeferTemplateQualifierInstantiation() {
                    parser.defer_class_template_qualifier_instantiation_ =
                        previous;
                    parser
                        .select_partial_for_deferred_class_template_qualifier_ =
                        previous_partial_selection;
                }
            } defer(*this);

            collect::Session::TemplateInfo probe_info = info;
            collect::Session::InstantiationScope header_scope =
                collect_session_.begin_template_header(probe_info,
                                                       template_token.loc);
            DeclarationParser probe_parser(
                *this, template_declaration_type_context);

            select_partial_for_deferred_class_template_qualifier_ = true;
            cir::TypeRef base = probe_parser.parse_declaration(false, true);
            select_partial_for_deferred_class_template_qualifier_ = false;
            defer_class_template_qualifier_instantiation_ = true;
            ParsedDeclarator declarator =
                probe_parser.parse_declarator(base, false);

            const collect::Session::TemplateInfo* owner =
                declarator.template_qualifier_info;
            bool candidate =
                declarator.has_name && !declarator.is_function &&
                declarator.type.valid() && owner && owner->is_class_template &&
                declarator.qualified_context.valid();
            const cir::File& file = collect_session_.file();
            if (candidate) {
                candidate =
                    file.decl_context(declarator.qualified_context).kind ==
                    cir::DeclContextKind::Record;
            }
            if (candidate) {
                const cir::Binding* binding =
                    file.lookup_template_name_binding(
                        declarator.qualified_context,
                        declarator.name,
                        /*include_parents=*/false);
                const collect::Session::TemplateInfo* member_template =
                    binding && !binding->entities.empty()
                        ? collect_session_.template_info(
                              binding->entities.back())
                        : nullptr;
                if (member_template && member_template->is_variable_template) {
                    candidate = false;
                }
            }
            if (candidate &&
                !collect_session_
                     .find_record_static_data_member(
                         declarator.qualified_context,
                         declarator.name,
                         declarator.type_ref)
                     .valid()) {
                candidate = false;
            }
            if (candidate && !owner->is_partial_specialization) {
                collect::Session::PartialSpecializationSelection
                    selection =
                        select_template_partial_specialization(
                            *owner,
                            declarator.template_qualifier_arguments,
                            declarator.loc);
                if (selection.is_ambiguous) {
                    candidate = false;
                } else if (selection.info) {
                    owner = selection.info;
                }
            }
            collect_session_.finish_template_header(std::move(header_scope));
            if (!candidate) {
                return std::nullopt;
            }
            return owner;
        };

        if (std::optional<const collect::Session::TemplateInfo*> owner =
                parsed_static_owner()) {
            const cir::File& file = collect_session_.file();
            cir::DeclContextId definition_context =
                enclosing_namespace_context(
                    file,
                    collect_session_.current_decl_context());
            cir::DeclContextId owner_namespace =
                enclosing_namespace_context(file, (*owner)->lexical_context);
            if (!owner_namespace.valid() ||
                !declaration_context_encloses(file,
                                              definition_context,
                                              owner_namespace)) {
                diagnose(DiagnosticLevel::Error,
                         "static data member definition is not in a namespace enclosing its class template",
                         template_token.loc);
                skip_balanced_until_semicolon_or_brace();
                match(TokenType::SEMICOLON);
                collect::DeclResult decl;
                decl.has_error = true;
                return {make_node(NodeKind::UnknownDecl,
                                  begin,
                                  last_consumed_raw_end(),
                                  {},
                                  text_payload("template"),
                                  NodeFlagHasError),
                        std::move(decl)};
            }
            size_t member_begin = current_raw_index();
            size_t member_end = skip_balanced_until_semicolon_or_brace();
            match(TokenType::SEMICOLON);
            collect_session_.add_template_out_of_line_member(
                (*owner)->entity,
                member_begin,
                member_end,
                /*is_template_declaration=*/false,
                /*is_static_data_member_definition=*/true);
            return {make_node(NodeKind::UnknownDecl,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              text_payload("template")),
                    {}};
        }
    }

    // Namespace-scope variable template: capture the single wrapped
    // declaration and replay it per specialization. The probe uses the
    // ordinary declarator grammar under a template-header scope so
    // `T value`, `T* value`, and function-pointer variables are classified
    // by type structure rather than token spelling.
    {
        ParserCheckpoint checkpoint = capture_parser_checkpoint();
        size_t saved_cursor = cursor_;
        size_t saved_last_end = last_consumed_raw_end_;
        collect::Session::InstantiationScope header_scope =
            collect_session_.begin_template_header(info, template_token.loc);
        DeclarationParser variable_probe(
            *this, template_declaration_type_context);
        cir::TypeRef base = variable_probe.parse_declaration(false, true);
        ParsedDeclarator declarator =
            variable_probe.parse_declarator(base, false);
        bool has_variable_initializer =
            check(TokenType::ASSIGN) ||
            check(TokenType::LEFT_BRACE) ||
            (lang_opts_.is_cxx_mode() && check(TokenType::LEFT_PAREN));
        bool is_extern_declaration =
            variable_probe.storage_class == StorageClass::Extern &&
            !has_variable_initializer;
        bool is_variable_template =
            declarator.has_name && !declarator.name.empty() &&
            !declarator.is_function &&
            declarator.type.valid() &&
            !declarator.dependent_qualifier_type.type.valid();
        cursor_ = saved_cursor;
        last_consumed_raw_end_ = saved_last_end;
        collect_session_.finish_template_header(std::move(header_scope));
        restore_parser_checkpoint(checkpoint);

        if (is_variable_template) {
            const cir::File& file = collect_session_.file();
            cir::DeclContextId current_context =
                collect_session_.current_decl_context();
            bool current_context_is_record =
                current_context.valid() &&
                file.decl_context(current_context).kind ==
                    cir::DeclContextKind::Record;
            bool in_class_static_data_member_template =
                current_context_is_record &&
                !declarator.qualified_context.valid();
            bool out_of_class_static_data_member_template =
                declarator.qualified_context.valid() &&
                file.decl_context(declarator.qualified_context).kind ==
                    cir::DeclContextKind::Record;
            auto has_top_level_comma = [&]() {
                size_t offset = 0;
                int paren_depth = 0;
                int bracket_depth = 0;
                int brace_depth = 0;
                int angle_depth = 0;
                while (!at_end()) {
                    const Token& token = peek(offset);
                    if (token.type == TokenType::Eof ||
                        (token.type == TokenType::SEMICOLON &&
                         paren_depth == 0 && bracket_depth == 0 &&
                         brace_depth == 0 && angle_depth == 0)) {
                        return false;
                    }
                    if (token.type == TokenType::COMMA &&
                        paren_depth == 0 && bracket_depth == 0 &&
                        brace_depth == 0 && angle_depth == 0) {
                        return true;
                    }
                    switch (token.type) {
                        case TokenType::LEFT_PAREN: ++paren_depth; break;
                        case TokenType::RIGHT_PAREN:
                            if (paren_depth > 0) --paren_depth;
                            break;
                        case TokenType::LEFT_BRACKET: ++bracket_depth; break;
                        case TokenType::RIGHT_BRACKET:
                            if (bracket_depth > 0) --bracket_depth;
                            break;
                        case TokenType::LEFT_BRACE: ++brace_depth; break;
                        case TokenType::RIGHT_BRACE:
                            if (brace_depth > 0) --brace_depth;
                            break;
                        case TokenType::LESS_THAN: ++angle_depth; break;
                        case TokenType::GREATER_THAN:
                            if (angle_depth > 0) --angle_depth;
                            break;
                        default:
                            break;
                    }
                    ++offset;
                }
                return false;
            };

            bool multiple_declarators = has_top_level_comma();
            info.is_variable_template = true;
            info.name = declarator.name;
            info.variable_type = declarator.type;
            info.variable_type_ref = declarator.type_ref;
            info.variable_const_qualification_is_implicit =
                declarator.constexpr_const_is_implicit;
            info.variable_decl_flags = cir::DeclSemanticFlags{
                variable_probe.is_constexpr,
                variable_probe.is_consteval,
                variable_probe.is_constinit,
                variable_probe.is_inline,
                variable_probe.is_thread_local,
                variable_probe.storage_class == StorageClass::Register};
            info.variable_is_extern =
                variable_probe.storage_class == StorageClass::Extern;
            info.variable_is_static =
                variable_probe.storage_class == StorageClass::Static;
            info.declaration_attrs = variable_probe.leading_attrs;
            info.declaration_attrs.append(declarator.attrs);
            info.has_internal_linkage =
                variable_probe.storage_class == StorageClass::Static &&
                !current_context_is_record;
            info.definition_begin = current_raw_index();
            size_t definition_end = skip_balanced_until_semicolon();
            match(TokenType::SEMICOLON);
            info.definition_end = definition_end;
            info.has_definition =
                !is_extern_declaration && !in_class_static_data_member_template;
            if (multiple_declarators) {
                diagnose(DiagnosticLevel::Error,
                         "template declaration may only declare one entity",
                         template_token.loc);
                collect::DeclResult decl;
                decl.has_error = true;
                return {make_node(NodeKind::UnknownDecl,
                                  begin,
                                  last_consumed_raw_end(),
                                  {},
                                  text_payload("template"),
                                  NodeFlagHasError),
                        std::move(decl)};
            }
            if (in_class_static_data_member_template &&
                variable_probe.storage_class != StorageClass::Static) {
                diagnose(DiagnosticLevel::Error,
                         "class-scope variable template declaration must be static",
                         declarator.loc);
                collect::DeclResult decl;
                decl.has_error = true;
                return {make_node(NodeKind::UnknownDecl,
                                  begin,
                                  last_consumed_raw_end(),
                                  {},
                                  text_payload("template"),
                                  NodeFlagHasError),
                        std::move(decl)};
            }
            if (in_class_static_data_member_template &&
                has_variable_initializer) {
                diagnose(DiagnosticLevel::Error,
                         "in-class static data member template initializers are not supported yet",
                         declarator.loc);
                collect::DeclResult decl;
                decl.has_error = true;
                return {make_node(NodeKind::UnknownDecl,
                                  begin,
                                  last_consumed_raw_end(),
                                  {},
                                  text_payload("template"),
                                  NodeFlagHasError),
                        std::move(decl)};
            }
            if (out_of_class_static_data_member_template) {
                const cir::Binding* binding =
                    file.lookup_template_name_binding(
                        declarator.qualified_context,
                        declarator.name,
                        /*include_parents=*/false);
                const collect::Session::TemplateInfo* previous =
                    binding && !binding->entities.empty()
                        ? collect_session_.template_info(
                              binding->entities.back())
                        : nullptr;
                if (!previous || !previous->is_variable_template) {
                    diagnose(DiagnosticLevel::Error,
                             "out-of-class static data member template definition has no matching declaration",
                             declarator.loc);
                    collect::DeclResult decl;
                    decl.has_error = true;
                    return {make_node(NodeKind::UnknownDecl,
                                      begin,
                                      last_consumed_raw_end(),
                                      {},
                                      text_payload("template"),
                                      NodeFlagHasError),
                            std::move(decl)};
                }
                cir::DeclContextId owner_namespace =
                    enclosing_namespace_context(
                        file,
                        declarator.qualified_context);
                cir::DeclContextId definition_namespace =
                    enclosing_namespace_context(file, current_context);
                if (!owner_namespace.valid() ||
                    !definition_namespace.valid() ||
                    !declaration_context_encloses(file,
                                                  definition_namespace,
                                                  owner_namespace)) {
                    diagnose(DiagnosticLevel::Error,
                             "static data member template definition is not in a namespace enclosing its class",
                             declarator.loc);
                    collect::DeclResult decl;
                    decl.has_error = true;
                    return {make_node(NodeKind::UnknownDecl,
                                      begin,
                                      last_consumed_raw_end(),
                                      {},
                                      text_payload("template"),
                                      NodeFlagHasError),
                            std::move(decl)};
                }
            }

            // Variable-template partial specialization: the declarator is a
            // template-id of an existing variable template. This applies at
            // namespace scope and to static data member templates, both in
            // the class and through a qualified out-of-class definition.
            // Parse the written argument list under this head and register it
            // into the concrete primary's partial registry.
            {
                const collect::Session::TemplateInfo* variable_primary =
                    nullptr;
                cir::DeclContextId primary_context =
                    declarator.qualified_context.valid()
                        ? declarator.qualified_context
                        : (in_class_static_data_member_template
                               ? current_context
                               : cir::DeclContextId{});
                if (primary_context.valid()) {
                    const cir::Binding* binding =
                        file.lookup_template_name_binding(
                            primary_context,
                            declarator.name,
                            /*include_parents=*/false);
                    if (binding) {
                        for (auto it = binding->entities.rbegin();
                             it != binding->entities.rend(); ++it) {
                            const collect::Session::TemplateInfo* candidate =
                                collect_session_.template_info(*it);
                            if (candidate &&
                                candidate->is_variable_template &&
                                !candidate
                                     ->is_partial_specialization) {
                                variable_primary = candidate;
                                break;
                            }
                        }
                    }
                } else {
                    variable_primary =
                        collect_session_.template_info_for_name(
                            declarator.name);
                }
                if (variable_primary && variable_primary->is_variable_template &&
                    !variable_primary->is_partial_specialization) {
                    size_t name_index = info.definition_begin;
                    bool is_template_id_declarator = false;
                    for (size_t index = info.definition_begin;
                         index < info.definition_end; ++index) {
                        const Token& token = tokens_[cooked_to_raw_[index]];
                        if (is_identifier_token(token.type) &&
                            token.value == declarator.name) {
                            is_template_id_declarator =
                                index + 1 < info.definition_end &&
                                tokens_[cooked_to_raw_[index + 1]].type ==
                                    TokenType::LESS_THAN;
                            name_index = index;
                            break;
                        }
                    }
                    if (is_template_id_declarator) {
                        std::vector<collect::Session::TemplateArgument>
                            partial_arguments;
                        bool arguments_parsed = false;
                        {
                            size_t partial_cursor = cursor_;
                            size_t partial_last = last_consumed_raw_end_;
                            collect::Session::InstantiationScope partial_header =
                                collect_session_.begin_template_header(
                                    info, template_token.loc);
                            cursor_ = name_index + 1;
                            TemplateArgumentAccessExemptionScope access_exemption(
                                collect_session_);
                            arguments_parsed =
                                parse_template_argument_list_with_request(
                                    *variable_primary,
                                    partial_arguments,
                                    declarator.loc) &&
                                canonicalize_template_arguments(
                                    *variable_primary,
                                    partial_arguments,
                                    declarator.loc);
                            collect_session_.finish_template_header(
                                std::move(partial_header));
                            cursor_ = partial_cursor;
                            last_consumed_raw_end_ = partial_last;
                        }
                        if (arguments_parsed) {
                            collect_session_
                                .register_template_partial_specialization(
                                    *variable_primary,
                                    std::move(info),
                                    std::move(partial_arguments),
                                    declarator.loc);
                            return {make_node(NodeKind::UnknownDecl,
                                              begin,
                                              last_consumed_raw_end(),
                                              {},
                                              text_payload("template")),
                                    {}};
                        }
                    }
                }
            }
            struct TemplateDeclarationScopeExit {
                collect::Session* session = nullptr;
                ~TemplateDeclarationScopeExit() {
                    if (session) {
                        session->leave_scope();
                    }
                }
            } template_declaration_scope;
            if (out_of_class_static_data_member_template) {
                collect_session_.enter_existing_context(
                    declarator.qualified_context,
                    collect::ScopeFlags::RecordScope);
                template_declaration_scope.session = &collect_session_;
            }
            collect_session_.declare_template(std::move(info), template_token.loc);
            return {make_node(NodeKind::UnknownDecl,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              text_payload("template")),
                    {}};
        }
    }

    {
        ParserCheckpoint checkpoint = capture_parser_checkpoint();
        size_t saved_cursor = cursor_;
        size_t saved_last_end = last_consumed_raw_end_;

        collect::Session::TemplateInfo definition_info = info;
        collect::Session::InstantiationScope header_scope =
            collect_session_.begin_template_header(definition_info,
                                                   template_token.loc);
        bool saved_template_head_precedence =
            qualified_declarator_template_head_wins_;
        qualified_declarator_template_head_wins_ = true;
        ParsedDeclarator declarator;
        if (starts_qualified_conversion_function_id()) {
            std::optional<ParsedConversionFunctionDeclarator> conversion =
                parse_conversion_function_declarator(
                    /*require_qualified=*/true);
            if (conversion) {
                declarator = std::move(conversion->declarator);
                declarator.has_unsupported_semantics =
                    declarator.has_unsupported_semantics ||
                    conversion->has_error;
            }
        } else {
            DeclarationParser member_parser(
                *this, template_declaration_type_context);
            cir::TypeRef base = member_parser.parse_declaration(false, true);
            declarator = member_parser.parse_declarator(base, false);
        }
        qualified_declarator_template_head_wins_ =
            saved_template_head_precedence;
        ParsedAttributes trailing_attrs = try_parse_attributes();
        declarator.attrs.append(std::move(trailing_attrs.attrs));
        collect_session_.finish_template_header(std::move(header_scope));

        const cir::File& file = collect_session_.file();
        bool record_qualified =
            declarator.qualified_context.valid() &&
            file.decl_context(declarator.qualified_context).kind ==
                cir::DeclContextKind::Record;
        bool candidate =
            declarator.has_name && declarator.is_function &&
            declarator.type.valid() && record_qualified &&
            (check(TokenType::LEFT_BRACE) ||
             check(TokenType::COLON) ||
             check(TokenType::TRY_KW) ||
             check(TokenType::SEMICOLON));

        if (!candidate) {
            cursor_ = saved_cursor;
            last_consumed_raw_end_ = saved_last_end;
            restore_parser_checkpoint(checkpoint);
        } else {
            collect::Session::TemplateInfo definition_candidate =
                definition_info;
            definition_candidate.name = declarator.name;
            definition_candidate.pattern_type = declarator.type;
            record_trailing_function_requires_clause(definition_candidate,
                                                     declarator);
            auto signatures_equivalent =
                [&](const collect::Session::TemplateInfo& existing) {
                if (!existing.pattern_type.valid() ||
                    !declarator.type.valid()) {
                    return false;
                }

                if (!collect_session_.function_template_declarations_correspond(
                        existing.parameters,
                        existing.pattern_type,
                        definition_info.parameters,
                        declarator.type)) {
                    return false;
                }
                if (!collect_session_.associated_constraints_equivalent(
                        existing.introduced_constraints,
                        definition_candidate.introduced_constraints)) {
                    return false;
                }
                return true;
            };

            const cir::Binding* binding = file.lookup_callable_binding(
                declarator.qualified_context,
                declarator.name,
                /*include_parents=*/false);
            cir::EntityId method_entity{};
            const collect::Session::TemplateInfo* existing_info = nullptr;
            bool ambiguous = false;
            auto consider_method = [&](cir::EntityId candidate_entity) {
                if (!candidate_entity.valid() ||
                    candidate_entity == method_entity) {
                    return;
                }
                const collect::Session::TemplateInfo* candidate_info =
                    collect_session_.template_info(candidate_entity);
                if (!candidate_info ||
                    !signatures_equivalent(*candidate_info)) {
                    return;
                }
                if (method_entity.valid()) {
                    ambiguous = true;
                    return;
                }
                method_entity = candidate_entity;
                existing_info = candidate_info;
            };
            if (binding) {
                for (cir::EntityId candidate_entity : binding->entities) {
                    consider_method(candidate_entity);
                }
            }

            const cir::DeclContext& record_context =
                file.decl_context(declarator.qualified_context);
            const cir::RecordFacts* record_facts =
                record_context.owner.valid()
                    ? file.record_facts(record_context.owner)
                    : nullptr;
            if (record_facts) {
                for (const cir::RecordMethodFact& method :
                     record_facts->methods) {
                    if (!method.name.valid() ||
                        file.name(method.name) != declarator.name) {
                        continue;
                    }
                    consider_method(method.entity);
                }
            }

            collect::DeclResult decl;
            decl.type = declarator.type;
            bool has_error = false;
            if (ambiguous) {
                diagnose(DiagnosticLevel::Error,
                         "out-of-line member function template definition is ambiguous",
                         declarator.loc);
                has_error = true;
            } else if (!method_entity.valid() || !existing_info) {
                diagnose(DiagnosticLevel::Error,
                         "out-of-line member function template definition has no matching declaration",
                         declarator.loc);
                has_error = true;
            }

            size_t body_begin = current_raw_index();
            size_t body_end = body_begin;
            size_t init_begin = 0;
            size_t init_end = 0;
            bool is_constructor_function_try = false;
            cir::EntityKind method_kind = method_entity.valid()
                ? file.entity(method_entity).kind
                : cir::EntityKind::Invalid;
            bool is_constructor =
                method_kind == cir::EntityKind::Constructor;
            bool has_definition = false;
            if (check(TokenType::TRY_KW)) {
                body_begin = current_raw_index();
                body_end = skip_function_try_block_tokens();
                has_definition = true;
                is_constructor_function_try = is_constructor;
                if (!is_constructor) {
                    diagnose(
                        DiagnosticLevel::Error,
                        "function try blocks are supported only for constructors",
                        loc_for_index(body_begin));
                    has_error = true;
                }
            } else if (match(TokenType::COLON)) {

                init_begin = current_raw_index();
                int depth = 0;
                TokenType previous = TokenType::COLON;
                while (!at_end()) {
                    TokenType type = current().type;
                    if (depth == 0 &&
                        (type == TokenType::SEMICOLON ||
                         type == TokenType::RIGHT_BRACE)) {
                        break;
                    }
                    if (depth == 0 && type == TokenType::LEFT_BRACE &&
                        !is_identifier_token(previous) &&
                        previous != TokenType::GREATER_THAN) {
                        break;
                    }
                    if (type == TokenType::LEFT_PAREN ||
                        type == TokenType::LEFT_BRACE) {
                        ++depth;
                    }
                    if (type == TokenType::RIGHT_PAREN ||
                        type == TokenType::RIGHT_BRACE) {
                        --depth;
                    }
                    previous = type;
                    consume();
                }
                init_end = current_raw_index();
                if (!is_constructor) {
                    diagnose(
                        DiagnosticLevel::Error,
                        "only constructors take member initializer lists",
                        loc_for_index(init_begin));
                    has_error = true;
                }
                if (check(TokenType::LEFT_BRACE)) {
                    body_begin = current_raw_index();
                    body_end = skip_balanced_until_semicolon_or_brace();
                    has_definition = true;
                } else {
                    diagnose(DiagnosticLevel::Error,
                             "constructor member initializers require a body",
                             loc_for_index(init_begin));
                    has_error = true;
                }
            } else if (check(TokenType::LEFT_BRACE)) {
                body_begin = current_raw_index();
                body_end = skip_balanced_until_semicolon_or_brace();
                has_definition = true;
            } else {
                consume();
                body_end = current_raw_index();
            }
            match(TokenType::SEMICOLON);

            if (!has_error) {
                size_t method_index = 0;
                if (record_facts) {
                    for (size_t i = 0;
                         i < record_facts->methods.size(); ++i) {
                        if (record_facts->methods[i].entity ==
                            method_entity) {
                            method_index = i;
                            break;
                        }
                    }
                }

                definition_info = std::move(definition_candidate);
                definition_info.has_definition = has_definition;
                definition_info.definition_begin = body_begin;
                definition_info.definition_end = body_end;
                if (definition_info
                        .is_member_template_specialization_overlay) {
                    definition_info.definition_generation =
                        collect_session_.lookup_generation();
                }
                if (has_definition) {
                    PendingMemberBody pending;
                    pending.method_index = method_index;
                    pending.body_begin = body_begin;
                    pending.body_end = body_end;
                    pending.init_begin = init_begin;
                    pending.init_end = init_end;
                    pending.is_constructor_function_try =
                        is_constructor_function_try;
                    pending.params = std::move(declarator.params);

                    if (!definition_info
                             .is_member_template_specialization_overlay &&
                        !collect_session_.collecting_pattern() &&
                        !collect_session_.is_instantiating()) {
                        validate_member_template_body(definition_info,
                                                      method_entity,
                                                      pending,
                                                      template_token.loc);
                    }

                    uint64_t body_key =
                        static_cast<uint64_t>(method_entity.index);
                    member_template_bodies_[body_key] = pending;
                    collect_session_.track_speculative_rollback(
                        [this, body_key] {
                            member_template_bodies_.erase(body_key);
                        });
                }

                if (!collect_session_.define_member_template_entity(
                        std::move(definition_info),
                        method_entity,
                        declarator.loc)) {
                    has_error = true;
                }
                decl.entity = method_entity;
            }
            decl.has_error = has_error;
            return {make_node(has_error ? NodeKind::UnknownDecl
                                        : NodeKind::FunctionDecl,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              text_payload("template"),
                              has_error ? NodeFlagHasError : NodeFlagNone),
                    std::move(decl)};
        }
    }

    {
        bool parsed_member_signature_mismatch = false;
        SrcLoc parsed_member_signature_loc{};
        std::string parsed_member_signature_name;
        bool parsed_member_exception_mismatch = false;
        SrcLoc parsed_member_exception_loc{};
        std::string parsed_member_exception_name;

        std::vector<collect::Session::TemplateParameter>
            parsed_head_parameters;
        std::vector<uint32_t> parsed_head_owner_slots;
        bool parsed_head_order_invalid = false;
        SrcLoc parsed_head_order_loc{};
        size_t parsed_member_tail = SIZE_MAX;
        size_t parsed_member_tail_last_end = 0;
        bool parsed_member_is_function = false;
        auto parsed_member_owner =
            [&]() -> std::optional<const collect::Session::TemplateInfo*> {
            RevertingTentativeParsingAction tentative(
                *this,
                TentativeMode::CollectBacked);
            struct DeferTemplateQualifierInstantiation {
                Parser& parser;
                bool previous = false;
                bool previous_partial_selection = false;

                explicit DeferTemplateQualifierInstantiation(Parser& parser)
                    : parser(parser),
                      previous(
                          parser.defer_class_template_qualifier_instantiation_),
                      previous_partial_selection(
                          parser
                              .select_partial_for_deferred_class_template_qualifier_) {
                    parser.defer_class_template_qualifier_instantiation_ = true;
                }

                ~DeferTemplateQualifierInstantiation() {
                    parser.defer_class_template_qualifier_instantiation_ =
                        previous;
                    parser
                        .select_partial_for_deferred_class_template_qualifier_ =
                        previous_partial_selection;
                }
            } defer(*this);

            collect::Session::TemplateInfo probe_info = info;
            collect::Session::InstantiationScope header_scope =
                collect_session_.begin_template_header(probe_info,
                                                       template_token.loc);
            DeclarationParser probe_parser(
                *this, template_declaration_type_context);
            select_partial_for_deferred_class_template_qualifier_ = true;
            cir::TypeRef base = probe_parser.parse_declaration(false, true);
            select_partial_for_deferred_class_template_qualifier_ = false;
            defer_class_template_qualifier_instantiation_ = true;
            ParsedDeclarator declarator =
                probe_parser.parse_declarator(base, false);

            const collect::Session::TemplateInfo* owner =
                declarator.template_qualifier_info;
            const collect::Session::TemplateInfo* written_owner = owner;
            bool has_record_context = false;
            if (declarator.qualified_context.valid()) {
                const cir::File& file = collect_session_.file();
                has_record_context =
                    file.decl_context(declarator.qualified_context).kind ==
                    cir::DeclContextKind::Record;
            }
            bool has_deferred_template_context =
                declarator.dependent_qualifier_type.valid();
            bool candidate =
                declarator.has_name && owner &&
                owner->is_class_template &&
                (has_record_context || has_deferred_template_context);
            if (candidate) {
                parsed_member_tail = current_raw_index();
                parsed_member_tail_last_end = last_consumed_raw_end_;
                parsed_member_is_function = declarator.is_function;
            }
            if (candidate && !owner->is_partial_specialization) {
                collect::Session::PartialSpecializationSelection
                    selection =
                        select_template_partial_specialization(
                            *owner,
                            declarator.template_qualifier_arguments,
                            declarator.loc);
                if (selection.info) {
                    owner = selection.info;
                }
            }
            if (candidate && has_record_context &&
                declarator.is_function && !owner->is_partial_specialization) {
                const cir::File& file = collect_session_.file();
                bool declaration_matches = false;
                const cir::DeclContext& record_context =
                    file.decl_context(declarator.qualified_context);

                bool terminal_is_written_owner =
                    written_owner &&
                    written_owner->pattern_record.valid() &&
                    record_context.owner ==
                        written_owner->pattern_record;
                cir::EntityId declaration_owner =
                    terminal_is_written_owner &&
                            owner->pattern_record.valid()
                        ? owner->pattern_record
                        : record_context.owner;
                if (!terminal_is_written_owner) {
                    const cir::RecordFacts* terminal_facts =
                        declaration_owner.valid()
                            ? file.record_facts(declaration_owner)
                            : nullptr;
                    if (terminal_facts && terminal_facts->is_incomplete) {
                        (void)force_deferred_member_class_definition(
                            declaration_owner);
                    }
                }
                const cir::RecordFacts* facts =
                    declaration_owner.valid()
                        ? file.record_facts(declaration_owner)
                        : nullptr;
                const bool definition_is_constrained =
                    declarator.has_trailing_requires_clause;
                const std::optional<uint64_t> definition_fingerprint =
                    declarator.trailing_requires_normal_form.has_value()
                        ? std::optional<uint64_t>(
                              collect_session_
                                  .normalized_constraint_fingerprint(
                                      *declarator
                                           .trailing_requires_normal_form))
                        : std::nullopt;
                if (facts) {
                    for (const cir::RecordMethodFact& method :
                         facts->methods) {
                        if (!method.entity.valid() || !method.name.valid() ||
                            file.name(method.name) != declarator.name ||
                            method.is_implicitly_declared) {
                            continue;
                        }
                        collect::Session::PatternBindings
                            declaration_to_definition;
                        declaration_to_definition.types.resize(
                            owner->parameters.size());
                        collect::Session::PatternBindings
                            definition_to_declaration;
                        definition_to_declaration.types.resize(
                            info.parameters.size());
                        if (!collect_session_.unify_type_pattern(
                                method.type.type,
                                declarator.type,
                                declaration_to_definition,
                                collect::Session::
                                    TypePatternExceptionMatch::
                                        IgnoreAtCurrentFunction) ||
                            !collect_session_.unify_type_pattern(
                                declarator.type,
                                method.type.type,
                                definition_to_declaration,
                                collect::Session::
                                    TypePatternExceptionMatch::
                                        IgnoreAtCurrentFunction)) {
                            continue;
                        }
                        const bool declaration_is_constrained =
                            method.constraint_satisfaction !=
                            cir::ConstraintSatisfactionKind::Unconstrained;
                        if (definition_is_constrained !=
                            declaration_is_constrained) {
                            continue;
                        }
                        if (definition_is_constrained &&
                            (!definition_fingerprint.has_value() ||
                             *definition_fingerprint !=
                                 method.associated_constraint_fingerprint)) {
                            continue;
                        }
                        if ((method.has_explicit_exception_spec ||
                             declarator.has_noexcept_specifier) &&
                            !collect_session_
                                 .function_exception_specs_equivalent(
                                     method.type.type,
                                     declarator.type)) {
                            parsed_member_exception_mismatch = true;
                            parsed_member_exception_loc = declarator.loc;
                            parsed_member_exception_name = declarator.name;
                        }
                        declaration_matches = true;
                        break;
                    }
                }

                if (!declaration_matches && facts &&
                    !facts->is_incomplete) {
                    parsed_member_signature_mismatch = true;
                    parsed_member_signature_loc = declarator.loc;
                    parsed_member_signature_name = declarator.name;
                }
            }
            if (candidate && owner && !owner->is_partial_specialization) {

                const std::vector<collect::Session::TemplateArgument>&
                    written = declarator.template_qualifier_arguments;
                std::vector<uint32_t> slots(probe_info.parameters.size(),
                                            UINT32_MAX);
                bool total = !probe_info.parameters.empty() &&
                             written.size() == probe_info.parameters.size() &&
                             owner->parameters.size() == written.size() &&
                             collect_session_.template_parameter_lists_match(
                                 owner->parameters,
                                 probe_info.parameters);
                for (size_t slot = 0; total && slot < written.size(); ++slot) {
                    const collect::Session::TemplateArgument& argument =
                        written[slot];
                    bool matched = false;
                    for (size_t j = 0; j < probe_info.parameters.size(); ++j) {
                        const collect::Session::TemplateParameter& parameter =
                            probe_info.parameters[j];
                        if (parameter.is_parameter_pack ||
                            slots[j] != UINT32_MAX) {
                            continue;
                        }
                        bool names_parameter = false;
                        if (parameter.kind ==
                                collect::Session::TemplateParameterKind::Type) {
                            names_parameter =
                                argument.kind ==
                                    cir::TemplateArgumentKind::Type &&
                                argument.type.type.valid() &&
                                argument.type.qualifiers == cir::QualNone &&
                                argument.type.type == parameter.type_param_type;
                        } else if (parameter.kind ==
                                   collect::Session::TemplateParameterKind::
                                       NonType) {
                            names_parameter =
                                argument.kind ==
                                    cir::TemplateArgumentKind::Value &&
                                argument.value_param_index == parameter.index;
                        } else {
                            names_parameter =
                                argument.kind ==
                                    cir::TemplateArgumentKind::Template &&
                                argument.template_param_index == parameter.index;
                        }
                        if (names_parameter) {
                            slots[j] = static_cast<uint32_t>(slot);
                            matched = true;
                            break;
                        }
                    }
                    if (!matched) {
                        total = false;
                    }
                }
                bool positional = total;
                bool renamed = false;
                for (size_t j = 0; total && j < slots.size(); ++j) {
                    if (slots[j] == UINT32_MAX) {
                        total = false;
                    } else if (slots[j] != j) {

                        positional = false;
                    } else if (probe_info.parameters[j].name !=
                               owner->parameters[j].name) {
                        renamed = true;
                    }
                }
                if (total && !positional) {
                    parsed_head_order_invalid = true;
                    parsed_head_order_loc = declarator.loc;
                } else if (total && renamed) {
                    parsed_head_owner_slots = std::move(slots);
                    parsed_head_parameters = probe_info.parameters;
                }
            }
            collect_session_.finish_template_header(std::move(header_scope));
            if (!candidate) {
                return std::nullopt;
            }
            return owner;
        };

        std::optional<const collect::Session::TemplateInfo*> parsed_owner =
            parsed_member_owner();
        if (parsed_head_order_invalid) {
            diagnose(DiagnosticLevel::Error,
                     "out-of-line member definition template arguments must "
                     "name its template parameters in declaration order",
                     parsed_head_order_loc);
            skip_balanced_until_semicolon_or_brace();
            match(TokenType::SEMICOLON);
            collect::DeclResult decl;
            decl.has_error = true;
            return {make_node(NodeKind::UnknownDecl,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              text_payload("template"),
                              NodeFlagHasError),
                    std::move(decl)};
        }
        if (parsed_member_exception_mismatch) {
            diagnose(DiagnosticLevel::Error,
                     "exception specification of '" +
                         parsed_member_exception_name +
                         "' does not match the previous declaration",
                     parsed_member_exception_loc);
            skip_balanced_until_semicolon_or_brace();
            match(TokenType::SEMICOLON);
            collect::DeclResult decl;
            decl.has_error = true;
            return {make_node(NodeKind::UnknownDecl,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              text_payload("template"),
                              NodeFlagHasError),
                    std::move(decl)};
        }
        if (parsed_member_signature_mismatch) {
            diagnose(DiagnosticLevel::Error,
                     "out-of-line definition of '" +
                         parsed_member_signature_name +
                         "' does not match any declaration",
                     parsed_member_signature_loc);
            skip_balanced_until_semicolon_or_brace();
            match(TokenType::SEMICOLON);
            collect::DeclResult decl;
            decl.has_error = true;
            return {make_node(NodeKind::UnknownDecl,
                              begin,
                              last_consumed_raw_end(),
                              {},
                              text_payload("template"),
                              NodeFlagHasError),
                    std::move(decl)};
        }
        const collect::Session::TemplateInfo* owner =
            parsed_owner.value_or(nullptr);
        if (!owner) {
            size_t offset = 0;
            int paren_depth = 0;
            int bracket_depth = 0;
            while (!at_end()) {
                const Token& token = peek(offset);
                if ((paren_depth == 0 && bracket_depth == 0 &&
                     (token.type == TokenType::LEFT_BRACE ||
                      token.type == TokenType::SEMICOLON)) ||
                    token.type == TokenType::Eof) {
                    break;
                }
                if (paren_depth == 0 && bracket_depth == 0 &&
                    is_identifier_token(token.type) &&
                    peek(offset + 1).type == TokenType::LESS_THAN &&
                    template_id_precedes_scope(offset)) {
                    size_t scope_offset =
                        template_id_scope_offset(offset);
                    size_t terminal_offset = scope_offset + 1;
                    TokenType terminal_type =
                        peek(terminal_offset).type;
                    TokenType suffix_type =
                        peek(terminal_offset + 1).type;

                    bool declarator_qualifier =
                        is_identifier_token(terminal_type) &&
                        (suffix_type == TokenType::LEFT_PAREN ||
                         suffix_type == TokenType::LEFT_BRACKET ||
                         suffix_type == TokenType::ASSIGN ||
                         suffix_type == TokenType::LEFT_BRACE ||
                         suffix_type == TokenType::SEMICOLON);
                    const collect::Session::TemplateInfo* candidate =
                        collect_session_.template_info_for_name(token.value);
                    if (declarator_qualifier && candidate &&
                        candidate->is_class_template) {
                        owner = candidate;
                        break;
                    }
                }
                if (token.type == TokenType::LEFT_PAREN) {
                    ++paren_depth;
                } else if (token.type == TokenType::RIGHT_PAREN &&
                           paren_depth > 0) {
                    --paren_depth;
                } else if (token.type == TokenType::LEFT_BRACKET) {
                    ++bracket_depth;
                } else if (token.type == TokenType::RIGHT_BRACKET &&
                           bracket_depth > 0) {
                    --bracket_depth;
                }
                ++offset;
            }
        }
        if (owner) {
            size_t member_begin = current_raw_index();
            size_t member_end = parsed_member_tail != SIZE_MAX
                ? capture_out_of_line_member_end(
                      parsed_member_tail,
                      parsed_member_tail_last_end,
                      parsed_member_is_function)
                : skip_balanced_until_semicolon_or_brace();
            match(TokenType::SEMICOLON);
            collect_session_.add_template_out_of_line_member(
                owner->entity,
                member_begin,
                member_end,
                /*is_template_declaration=*/false,
                /*is_static_data_member_definition=*/false,
                std::move(parsed_head_parameters),
                std::move(parsed_head_owner_slots));
            (void)member_end;
            return {make_node(NodeKind::UnknownDecl, begin,
                              last_consumed_raw_end(),
                              {}, text_payload("template")),
                    {}};
        }
    }

    info.definition_begin = current_raw_index();

    collect::Session::InstantiationScope header_scope =
        collect_session_.begin_template_header(info, template_token.loc);
    size_t saved_cursor = cursor_;
    size_t saved_last_end = last_consumed_raw_end_;
    DeclarationParser header_parser(
        *this, template_declaration_type_context);
    header_parser.abbreviated_template_target = &info;
    cir::TypeRef base = header_parser.parse_declaration(false, true);
    ParsedDeclarator declarator =
        header_parser.parse_declarator(base, false);
    size_t parsed_declarator_end_cursor = cursor_;
    size_t parsed_declarator_last_end = last_consumed_raw_end_;
    cursor_ = saved_cursor;
    last_consumed_raw_end_ = saved_last_end;
    collect_session_.finish_template_header(std::move(header_scope));
    cir::TypeId declared_type =
        collect_session_.file().resolved_type(declarator.type);
    bool parsed_function_declarator =
        declarator.has_name &&
        collect_session_.file().valid(declared_type) &&
        collect_session_.file().type(declared_type).kind ==
            cir::TypeKind::Function;
    bool function_template_declaration_is_record_member = false;
    bool function_template_declaration_is_static_record_member = false;
    if (parsed_function_declarator) {
        info.name = declarator.name;
        info.operator_function = declarator.operator_function;
        info.pattern_type = declared_type;

        info.declaration_attrs = declarator.attrs;
        record_trailing_function_requires_clause(info, declarator);
        const cir::File& file = collect_session_.file();
        bool is_record_member =
            template_declaration_context.valid() &&
            file.decl_context(template_declaration_context).kind ==
                cir::DeclContextKind::Record;
        function_template_declaration_is_record_member = is_record_member;
        function_template_declaration_is_static_record_member =
            is_record_member &&
            header_parser.storage_class == StorageClass::Static;
        info.has_internal_linkage =
            header_parser.storage_class == StorageClass::Static &&
            !is_record_member;
        if (is_record_member &&
            header_parser.storage_class == StorageClass::Static) {
            collect_session_.validate_static_member_function_type(
                declared_type,
                declarator.loc.isInvalid() ? template_token.loc
                                           : declarator.loc);
        }
        if (info.operator_function.kind ==
            cir::OperatorFunctionKind::Literal) {
            validate_literal_operator_declaration(
                declarator, &info, header_parser.is_friend);
        }

        cursor_ = parsed_declarator_end_cursor;
        last_consumed_raw_end_ = parsed_declarator_last_end;
    }
    bool function_template_declaration_is_deleted = false;
    auto function_template_declaration_has_body = [&]() {
        int parens = 0;
        int brackets = 0;
        size_t offset = 0;
        while (!at_end()) {
            TokenType type = peek(offset).type;
            if (type == TokenType::Eof) {
                return false;
            }
            if (parens <= 0 && brackets <= 0) {
                if (type == TokenType::SEMICOLON) {
                    return false;
                }
                if (type == TokenType::ASSIGN &&
                    peek(offset + 1).type == TokenType::DELETE) {
                    function_template_declaration_is_deleted = true;
                    return false;
                }
                if (type == TokenType::LEFT_BRACE) {
                    return true;
                }
            }
            if (type == TokenType::LEFT_PAREN) {
                ++parens;
            } else if (type == TokenType::RIGHT_PAREN) {
                --parens;
            } else if (type == TokenType::LEFT_BRACKET) {
                ++brackets;
            } else if (type == TokenType::RIGHT_BRACKET) {
                --brackets;
            }
            ++offset;
        }
        return false;
    };
    bool has_function_template_definition =
        function_template_declaration_has_body();
    size_t definition_end = skip_balanced_until_semicolon_or_brace();
    match(TokenType::SEMICOLON);
    info.definition_end = definition_end;
    info.is_deleted = function_template_declaration_is_deleted;
    info.has_definition =
        has_function_template_definition || info.is_deleted;
    info.lexical_context = template_declaration_context;
    bool validate_function_template_definition =
        !function_template_declaration_is_record_member ||
        (!collect_session_.collecting_pattern() &&
         !collect_session_.is_instantiating());
    if (has_function_template_definition && !info.name.empty() &&
        validate_function_template_definition) {
        validate_template_definition(info, template_token.loc);
    }
    if (info.name.empty()) {
        diagnose(DiagnosticLevel::Error,
                 "could not determine the function template name",
                 template_token.loc);
        collect::DeclResult decl;
        decl.has_error = true;
        return {make_node(NodeKind::UnknownDecl, begin, last_consumed_raw_end(),
                          {}, text_payload("template"), NodeFlagHasError),
                std::move(decl)};
    }
    cir::EntityId template_entity =
        collect_session_.declare_template(std::move(info), template_token.loc);
    if (template_entity.valid() &&
        function_template_declaration_is_static_record_member) {

        collect_session_.file().entity_mut(template_entity)
            .is_static_member_function = true;
    }
    collect_session_.register_function_template_default_arguments(
        template_entity,
        param_inputs_from_parsed_params(declarator.params,
                                        /*move_runtime_fragments=*/false),
        template_token.loc);
    return {make_node(NodeKind::UnknownDecl, begin, last_consumed_raw_end(),
                      {}, text_payload("template")),
            {}};
}

void Parser::validate_template_definition(
    collect::Session::TemplateInfo& info,
    SrcLoc loc) {

    struct InheritedClassTemplateDefaults {
        collect::Session::TemplateInfo* info = nullptr;
        std::vector<size_t> indices;

        ~InheritedClassTemplateDefaults() {
            if (!info) {
                return;
            }
            for (size_t index : indices) {
                if (index < info->parameters.size()) {
                    info->parameters[index].default_argument.reset();
                }
            }
        }
    } inherited_defaults{
        &info,
        collect_session_
            .inherit_prior_class_template_defaults_for_validation(info)};

    size_t error_watermark = collect_session_.file().errors().size();
    collect_session_.begin_speculative_parse();
    ParserCheckpoint checkpoint = capture_parser_checkpoint();
    collect::Session::InstantiationScope scope =
        collect_session_.begin_template_header(info, loc);
    bool was_in_template_definition =
        collect_session_.in_template_definition();
    collect_session_.set_in_template_definition(true);
    collect_session_.begin_template_validation(info);
    collect_session_.begin_pattern_collection();

    std::vector<
        collect::Session::TemplateInfo::StaticDataMemberInitializer>
        static_data_member_initializers;
    auto* saved_static_initializer_capture =
        static_data_member_initializer_capture_;
    static_data_member_initializer_capture_ =
        info.is_class_template ? &static_data_member_initializers : nullptr;
    cursor_ = info.definition_begin;
    cir::EntityId pattern_entity{};
    if (info.is_class_template) {
        cir::TypeId type{};
        (void)parse_record_specifier(&type);
        pattern_entity = collect_session_.current_validation_record();
    } else {
        struct LiteralOperatorTemplateValidationExit {
            Parser& parser;
            bool saved = false;
            ~LiteralOperatorTemplateValidationExit() {
                parser.validating_literal_operator_template_definition_ =
                    saved;
            }
        } literal_operator_validation{
            *this,
            validating_literal_operator_template_definition_};
        validating_literal_operator_template_definition_ =
            info.operator_function.kind ==
                cir::OperatorFunctionKind::Literal;
        ParsedDecl declaration = parse_declaration(true);
        pattern_entity = declaration.sem.entity;
    }
    static_data_member_initializer_capture_ =
        saved_static_initializer_capture;

    collect::Session::PatternCollection pattern =
        collect_session_.finish_pattern_collection();
    collect_session_.finish_template_validation();
    collect_session_.set_in_template_definition(was_in_template_definition);
    collect_session_.finish_template_header(std::move(scope));

    bool parse_clean =
        pattern.usable &&
        collect_session_.file().errors().size() == error_watermark &&
        diagnostics_.size() == checkpoint.diagnostics_size &&
        pattern_entity.valid();
    if (!parse_clean) {

        for (auto& initializer : static_data_member_initializers) {
            initializer.declaration_context = info.lexical_context;
            initializer.lookup_generation =
                collect_session_.lookup_generation();
            initializer.value_expression = {};
        }
    }
    if (!static_data_member_initializers.empty()) {
        info.static_data_member_initializers =
            std::move(static_data_member_initializers);
    }
    cir::FunctionId pattern_function{};
    bool commit_record = false;
    if (parse_clean && !info.is_class_template &&
        collect_session_.file().entity(pattern_entity).kind ==
            cir::EntityKind::Function &&
        collect_session_.file().entity(pattern_entity).is_definition) {
        std::vector<cir::FunctionId> functions =
            collect_session_.file().function_ids();
        for (auto it = functions.rbegin(); it != functions.rend(); ++it) {
            if (collect_session_.file().function(*it).entity ==
                pattern_entity) {
                pattern_function = *it;
                break;
            }
        }
    } else if (parse_clean && info.is_class_template &&
               collect_session_.file().entity(pattern_entity).kind ==
                   cir::EntityKind::Record) {
        commit_record = true;
    }
    if (pattern_function.valid() || commit_record) {

        collect_session_.commit_speculative_parse();
        restore_parser_checkpoint(checkpoint);
        info.definition_generation = collect_session_.lookup_generation();
        if (pattern_function.valid()) {
            info.pattern_function = pattern_function;
            info.pattern_usable = true;
            info.pattern_holes = std::move(pattern.holes);
            info.pattern_events = std::move(pattern.events);
        } else {

            info.pattern_record = pattern_entity;
            info.member_patterns = std::move(pattern.members);
        }
        return;
    }
    std::vector<std::pair<SrcLoc, std::string>> captured(
        collect_session_.file().errors().begin() + error_watermark,
        collect_session_.file().errors().end());
    std::vector<Diagnostic> parser_diagnostics(
        diagnostics_.begin() + checkpoint.diagnostics_size,
        diagnostics_.end());
    collect_session_.rollback_speculative_parse();
    restore_parser_checkpoint(checkpoint);
    for (auto& [error_loc, message] : captured) {
        collect_session_.file().add_error(std::move(message), error_loc);
    }
    diagnostics_.insert(diagnostics_.end(),
                        parser_diagnostics.begin(),
                        parser_diagnostics.end());
}

bool Parser::is_deduced_class_template_declaration_start() {
    if (!lang_opts_.is_cxx_mode() ||
        current().type != TokenType::IDENTIFIER) {
        return false;
    }
    const collect::Session::TemplateInfo* info =
        collect_session_.template_info_for_name(current().value);
    bool is_primary_class = info && info->is_class_template &&
        !info->is_partial_specialization;
    bool is_deducible_alias = info && info->is_alias_template &&
        info->alias_deduction_projection.has_value();
    if (!is_primary_class && !is_deducible_alias) {
        return false;
    }

    switch (peek(1).type) {
        case TokenType::IDENTIFIER:
        case TokenType::MULTIPLY:
        case TokenType::BITWISE_AND:
        case TokenType::LOGICAL_AND:
            return true;
        default:
            return false;
    }
}

cir::TypeId Parser::deduce_class_template_initialization_type(
    const collect::Session::TemplateInfo& requested_info,
    const std::vector<collect::ExprResult>& arguments,
    SrcLoc loc,
    CtadInitializationKind initialization_kind,
    const collect::ExprResult* braced_initializer,
    bool* selected_aggregate_candidate) {
    if (selected_aggregate_candidate) {
        *selected_aggregate_candidate = false;
    }
    const collect::Session::TemplateInfo* deduction_info = &requested_info;
    const collect::Session::TemplateInfo::AliasDeductionProjection*
        alias_projection = nullptr;
    if (requested_info.is_alias_template) {
        if (!lang_opts_.is_cxx20_or_later()) {
            diagnose(DiagnosticLevel::Error,
                     "alias template argument deduction requires C++20",
                     loc);
            return {};
        }
        if (requested_info.alias_deduction_projection.has_value()) {
            alias_projection =
                &*requested_info.alias_deduction_projection;
            deduction_info = collect_session_.template_info(
                alias_projection->target_template);
        }
        if (!alias_projection || !deduction_info ||
            !deduction_info->is_class_template ||
            deduction_info->is_partial_specialization) {
            diagnose(DiagnosticLevel::Error,
                     "alias template argument deduction requires a deducible class template specialization",
                     loc);
            return {};
        }
    }
    if (!deduction_info || !deduction_info->is_class_template ||
        deduction_info->is_partial_specialization) {
        diagnose(DiagnosticLevel::Error,
                 "class template argument deduction requires a primary class template",
                 loc);
        return {};
    }

    const collect::Session::TemplateInfo& info = *deduction_info;
    const collect::Session::TemplateInfo& result_info = requested_info;

    if (collect_session_.collecting_pattern() &&
        !collect_session_.is_instantiating() &&
        std::any_of(arguments.begin(),
                    arguments.end(),
                    [&](const collect::ExprResult& argument) {
                        return collect_session_.expr_is_dependent(argument);
                    })) {
        return collect_session_.dependent_type(
            "dependent class template argument deduction");
    }

    const cir::File& file = collect_session_.file();
    const cir::RecordFacts* facts = nullptr;
    if (info.has_definition) {
        facts = info.pattern_record.valid()
            ? file.record_facts(info.pattern_record)
            : nullptr;
        if ((!facts || facts->is_incomplete) &&
            info.deduction_guides.empty()) {
            diagnose(DiagnosticLevel::Error,
                     "class template argument deduction requires a defined primary class template",
                     loc);
            return {};
        }
        if (facts && facts->is_incomplete) {
            facts = nullptr;
        }
    }

    auto hypothetical_empty_guide_type = [&]() -> cir::TypeId {
        cir::TypeRef void_type =
            collect_session_.type_ref(
                collect_session_.file().builtin_type(
                    cir::BuiltinTypeKind::Void));
        return collect_session_.function_type(void_type,
                                              {},
                                              false,
                                              true);
    };
    auto self_template_arguments =
        [&]() -> std::optional<
            std::vector<collect::Session::TemplateArgument>> {
        std::vector<collect::Session::TemplateArgument> self_arguments;
        self_arguments.reserve(info.parameters.size());
        for (size_t i = 0; i < info.parameters.size(); ++i) {
            const collect::Session::TemplateParameter& parameter =
                info.parameters[i];
            uint32_t parameter_index = parameter.index ==
                    cir::ArrayTypePayload::no_extent_param
                ? static_cast<uint32_t>(i)
                : parameter.index;
            collect::Session::TemplateArgument argument;
            switch (parameter.kind) {
                case collect::Session::TemplateParameterKind::Type: {
                    cir::TypeId type = parameter.type_param_type.valid()
                        ? parameter.type_param_type
                        : (i < info.param_types.size()
                               ? info.param_types[i]
                               : cir::TypeId{});
                    if (!type.valid()) {
                        type = collect_session_.file().type_param_type(
                            {},
                            parameter.name,
                            parameter_index,
                            parameter.depth,
                            parameter.is_parameter_pack);
                    }
                    argument.kind = cir::TemplateArgumentKind::Type;
                    argument.type = collect_session_.type_ref(type);
                    argument.is_dependent = true;
                    break;
                }
                case collect::Session::TemplateParameterKind::NonType: {
                    cir::TypeId value_type = parameter.non_type_type.valid()
                        ? parameter.non_type_type
                        : collect_session_.file().builtin_type(
                              cir::BuiltinTypeKind::Int);
                    argument.kind = cir::TemplateArgumentKind::Value;
                    argument.value_type =
                        collect_session_.type_ref(value_type);
                    argument.value_param_index = parameter_index;
                    argument.value_spelling = parameter.name;
                    argument.is_dependent = true;
                    break;
                }
                case collect::Session::TemplateParameterKind::Template:
                    argument.kind = cir::TemplateArgumentKind::Template;
                    argument.template_entity = parameter.entity;
                    argument.template_param_index = parameter_index;
                    if (!parameter.name.empty()) {
                        argument.template_name =
                            collect_session_.file().intern_name(
                                parameter.name);
                    }
                    argument.is_dependent = true;
                    break;
            }
            self_arguments.push_back(std::move(argument));
        }
        return self_arguments;
    };
    auto hypothetical_copy_guide_type = [&]() -> cir::TypeId {
        std::optional<std::vector<collect::Session::TemplateArgument>>
            self_arguments = self_template_arguments();
        if (!self_arguments.has_value()) {
            return {};
        }
        cir::EntityId self_specialization =
            instantiate_template_with_args(info,
                                           std::move(*self_arguments),
                                           loc);
        if (!self_specialization.valid() ||
            !collect_session_.file().valid(self_specialization)) {
            return {};
        }
        cir::TypeRef void_type =
            collect_session_.type_ref(
                collect_session_.file().builtin_type(
                    cir::BuiltinTypeKind::Void));
        cir::TypeRef parameter_type = collect_session_.type_ref(
            collect_session_.file().entity(self_specialization).type);
        return collect_session_.function_type(void_type,
                                              {parameter_type},
                                              false,
                                              true);
    };
    auto constructor_template_guide_type =
        [&](const collect::Session::TemplateInfo& constructor,
            std::vector<collect::Session::TemplateParameter>& guide_parameters)
        -> cir::TypeId {
        if (!constructor.pattern_type.valid()) {
            return {};
        }
        guide_parameters = info.parameters;
        std::vector<TypeParamRemap> remaps;
        remaps.reserve(constructor.parameters.size());
        auto class_has_non_type_index = [&](uint32_t index) {
            for (const collect::Session::TemplateParameter& parameter :
                 info.parameters) {
                if (parameter.kind ==
                        collect::Session::TemplateParameterKind::NonType &&
                    parameter.index == index) {
                    return true;
                }
            }
            return false;
        };
        auto class_has_template_index = [&](uint32_t index) {
            for (const collect::Session::TemplateParameter& parameter :
                 info.parameters) {
                if (parameter.kind ==
                        collect::Session::TemplateParameterKind::Template &&
                    parameter.index == index) {
                    return true;
                }
            }
            return false;
        };
        for (size_t i = 0; i < constructor.parameters.size(); ++i) {
            const collect::Session::TemplateParameter& parameter =
                constructor.parameters[i];
            if (parameter.is_parameter_pack) {
                return {};
            }
            collect::Session::TemplateParameter appended = parameter;
            appended.index = static_cast<uint32_t>(guide_parameters.size());
            if (parameter.kind ==
                collect::Session::TemplateParameterKind::Type) {
                cir::TypeId source = parameter.type_param_type.valid()
                    ? parameter.type_param_type
                    : (i < constructor.param_types.size()
                           ? constructor.param_types[i]
                           : cir::TypeId{});
                if (!source.valid()) {
                    return {};
                }
                appended.type_param_type =
                    collect_session_.file().type_param_type(
                        {},
                        appended.name,
                        appended.index,
                        appended.depth,
                        appended.is_parameter_pack);
                remaps.push_back(TypeParamRemap{source,
                                                appended.type_param_type});
            } else if (parameter.kind ==
                       collect::Session::TemplateParameterKind::NonType) {
                if (class_has_non_type_index(parameter.index)) {
                    return {};
                }
                remaps.push_back(TypeParamRemap{
                    {},
                    {},
                    parameter.index,
                    appended.index});
            } else if (parameter.kind ==
                       collect::Session::TemplateParameterKind::Template) {
                if (class_has_template_index(parameter.index)) {
                    return {};
                }
                TypeParamRemap remap;
                remap.template_from = parameter.index;
                remap.template_to = appended.index;
                remap.template_entity = parameter.entity;
                remap.template_name = appended.name;
                remap.template_parameters = appended.nested_parameters();
                remap.template_is_parameter_pack = appended.is_parameter_pack;
                remaps.push_back(std::move(remap));
            } else {
                return {};
            }
            if (appended.default_argument.has_value()) {
                appended.default_argument =
                    remap_template_argument_placeholders(
                        collect_session_,
                        std::move(*appended.default_argument),
                        remaps);
            }
            guide_parameters.push_back(std::move(appended));
        }
        return remap_type_params_in_type(collect_session_,
                                         constructor.pattern_type,
                                         remaps);
    };
    auto simple_aggregate_guide_type = [&]() -> cir::TypeId {
        if ((initialization_kind != CtadInitializationKind::Direct &&
             initialization_kind != CtadInitializationKind::CopyList) ||
            arguments.empty() ||
            !facts ||
            !info.deduction_guides.empty() ||
            facts->definition_data.has_user_declared_constructor ||
            facts->kind == cir::RecordKind::Union ||
            facts->is_polymorphic ||
            !facts->dependent_bases.empty() ||
            !facts->virtual_bases.empty()) {
            return {};
        }

        auto field_can_participate =
            [](const cir::RecordFieldFact& field) {
                if (field.declared_access != cir::RecordMemberAccess::Public ||
                    field.is_base_subobject ||
                    field.is_virtual_base_storage ||
                    field.is_flexible_array_member ||
                    field.is_bitfield ||
                    !field.type.type.valid()) {
                    return false;
                }
                return true;
            };
        auto argument_is_string_literal =
            [&](const collect::ExprResult& argument) {
                return argument.place.valid() &&
                       file.valid(argument.place) &&
                       file.inst(argument.place).kind ==
                           cir::InstKind::StringLiteral;
            };
        auto parameter_type_for_element =
            [&](cir::TypeRef element_type,
                const collect::ExprResult& argument) {
                cir::TypeRef parameter_type = element_type;
                cir::TypeId resolved_element_type =
                    file.resolved_type(element_type.type);
                if (file.valid(resolved_element_type) &&
                    file.type(resolved_element_type).kind ==
                        cir::TypeKind::Array) {
                    if (argument.category ==
                        collect::ValueCategory::InitList) {
                        parameter_type =
                            collect_session_.type_ref(
                                collect_session_.reference_type(
                                    element_type,
                                    cir::ReferenceKind::RValue));
                    } else if (argument_is_string_literal(argument)) {
                        cir::TypeRef const_array = element_type;
                        const_array.qualifiers |= cir::QualConst;
                        parameter_type =
                            collect_session_.type_ref(
                                collect_session_.reference_type(
                                    const_array,
                                    cir::ReferenceKind::LValue));
                    }
                }
                return parameter_type;
            };
        struct AggregateElement {
            cir::TypeRef type;
        };
        auto aggregate_element_children =
            [&](cir::TypeRef element_type)
                -> std::optional<std::vector<AggregateElement>> {
                cir::TypeId resolved =
                    file.resolved_type(element_type.type);
                if (!file.valid(resolved)) {
                    return std::nullopt;
                }
                const cir::Type& type = file.type(resolved);
                if (type.kind == cir::TypeKind::Array) {
                    const auto* array =
                        std::get_if<cir::ArrayTypePayload>(
                            &file.type_payload(resolved));
                    if (!array ||
                        array->size_kind !=
                            cir::ArraySizeKind::Constant ||
                        !array->size.has_value() ||
                        array->extent_param !=
                            cir::ArrayTypePayload::no_extent_param) {
                        return std::nullopt;
                    }
                    std::vector<AggregateElement> children;
                    children.reserve(*array->size);
                    for (size_t i = 0; i < *array->size; ++i) {
                        children.push_back(AggregateElement{
                            array->element_type});
                    }
                    return children;
                }
                if (type.kind != cir::TypeKind::Record ||
                    collect_session_.is_dependent_type(resolved)) {
                    return std::vector<AggregateElement>{};
                }
                const cir::RecordFacts* child_facts =
                    file.record_facts_for_type(resolved);
                if (!child_facts ||
                    child_facts->is_incomplete ||
                    child_facts->definition_data
                        .has_user_declared_constructor ||
                    child_facts->kind == cir::RecordKind::Union ||
                    child_facts->is_polymorphic ||
                    !child_facts->bases.empty() ||
                    !child_facts->dependent_bases.empty() ||
                    !child_facts->virtual_bases.empty()) {
                    return std::nullopt;
                }
                std::vector<AggregateElement> children;
                children.reserve(child_facts->fields.size());
                for (const cir::RecordFieldFact& field :
                     child_facts->fields) {
                    if (!field_can_participate(field)) {
                        return std::nullopt;
                    }
                    children.push_back(AggregateElement{field.type});
                }
                return children;
            };

        std::vector<const cir::RecordBaseFact*> base_elements;
        base_elements.reserve(facts->bases.size());
        for (const cir::RecordBaseFact& base : facts->bases) {
            if (base.declared_access !=
                    cir::RecordMemberAccess::Public ||
                base.is_virtual ||
                !base.has_non_virtual_offset ||
                !base.type.type.valid()) {
                return {};
            }
        }
        for (size_t index = 0; index < facts->bases.size(); ++index) {
            auto found = std::find_if(
                facts->bases.begin(),
                facts->bases.end(),
                [&](const cir::RecordBaseFact& base) {
                    return base.declaration_index == index;
                });
            if (found == facts->bases.end()) {
                return {};
            }
            base_elements.push_back(&*found);
        }

        std::vector<AggregateElement> pending_elements;
        pending_elements.reserve(base_elements.size() + facts->fields.size());
        for (const cir::RecordBaseFact* base : base_elements) {
            pending_elements.push_back(AggregateElement{base->type});
        }
        for (const cir::RecordFieldFact& field : facts->fields) {
            if (field.is_base_subobject ||
                field.is_virtual_base_storage) {
                continue;
            }
            if (!field_can_participate(field)) {
                return {};
            }
            pending_elements.push_back(AggregateElement{field.type});
        }

        std::vector<cir::TypeRef> parameter_types;
        parameter_types.reserve(arguments.size());
        for (const collect::ExprResult& argument : arguments) {
            for (;;) {
                if (pending_elements.empty()) {
                    return {};
                }
                AggregateElement element = pending_elements.front();
                pending_elements.erase(pending_elements.begin());
                bool begins_with_brace =
                    argument.category == collect::ValueCategory::InitList ||
                    argument.init_list != nullptr;
                cir::TypeId resolved_element =
                    file.resolved_type(element.type.type);
                bool is_array =
                    file.valid(resolved_element) &&
                    file.type(resolved_element).kind ==
                        cir::TypeKind::Array;
                bool is_record =
                    file.valid(resolved_element) &&
                    file.type(resolved_element).kind ==
                        cir::TypeKind::Record;
                bool is_aggregate_element = is_array || is_record;
                bool exact_expression_match =
                    !begins_with_brace &&
                    argument.type.valid() &&
                    file.resolved_type(element.type.type) ==
                        file.resolved_type(argument.type);
                bool whole_string_array =
                    is_array && argument_is_string_literal(argument);
                if (!is_aggregate_element ||
                    begins_with_brace ||
                    exact_expression_match ||
                    whole_string_array) {
                    parameter_types.push_back(
                        parameter_type_for_element(element.type, argument));
                    break;
                }

                std::optional<std::vector<AggregateElement>> children =
                    aggregate_element_children(element.type);
                if (!children.has_value()) {
                    return {};
                }
                if (children->empty()) {
                    parameter_types.push_back(
                        parameter_type_for_element(element.type, argument));
                    break;
                }
                pending_elements.insert(pending_elements.begin(),
                                        children->begin(),
                                        children->end());
            }
        }

        cir::TypeRef void_type =
            collect_session_.type_ref(
                collect_session_.file().builtin_type(
                    cir::BuiltinTypeKind::Void));
        return collect_session_.function_type(void_type,
                                              parameter_types,
                                              false,
                                              true);
    };

    enum class CtadCandidateSource : uint8_t {
        ConstructorTemplate,
        Aggregate,
        Constructor,
        Copy,
        UserGuide,
    };
    auto candidate_source_rank = [](CtadCandidateSource source) -> int {
        switch (source) {
            case CtadCandidateSource::UserGuide:
                return 3;
            case CtadCandidateSource::Copy:
                return 2;
            case CtadCandidateSource::Constructor:
                return 1;
            case CtadCandidateSource::Aggregate:
            case CtadCandidateSource::ConstructorTemplate:
                return 0;
        }
        return 0;
    };
    auto candidate_source_note = [](CtadCandidateSource source) {
        switch (source) {
            case CtadCandidateSource::UserGuide:
                return "user-written deduction guide considered here";
            case CtadCandidateSource::Copy:
                return "copy deduction candidate considered here";
            case CtadCandidateSource::Constructor:
                return "implicit constructor deduction guide considered here";
            case CtadCandidateSource::Aggregate:
                return "aggregate deduction candidate considered here";
            case CtadCandidateSource::ConstructorTemplate:
                return "implicit constructor-template deduction guide considered here";
        }
        return "candidate deduction guide considered here";
    };

    struct CtadConversion {
        collect::Session::ConversionRank rank =
            collect::Session::ConversionRank::Bad;
        collect::Session::ConversionDetail detail;
    };
    struct CtadCandidate {
        std::vector<collect::Session::TemplateArgument> class_arguments;
        std::string key;
        SrcLoc loc{};
        CtadCandidateSource source = CtadCandidateSource::Constructor;
        cir::TypeId pattern_type{};
        bool allow_partial_ordering = false;
        bool is_explicit = false;
        const collect::Session::TemplateInfo::DeductionGuide* user_guide =
            nullptr;
        std::vector<CtadConversion> conversions;
    };
    std::vector<CtadCandidate> viable_ctad_candidates;
    std::vector<CtadCandidate> phase_one_ctad_candidates;
    std::vector<CtadConversion> pending_conversions;
    auto add_class_arguments =
        [&](std::vector<collect::Session::TemplateArgument> class_arguments,
            SrcLoc guide_loc,
            bool is_explicit,
            CtadCandidateSource source,
            cir::TypeId pattern_type = {},
            bool allow_partial_ordering = false,
            bool list_phase_one = false,
            const collect::Session::TemplateInfo::DeductionGuide*
                user_guide = nullptr) {
        if (!canonicalize_template_arguments(result_info,
                                              class_arguments,
                                              loc)) {
            return;
        }
        CtadCandidate candidate;
        candidate.key = collect_session_.template_memo_key(
            result_info.entity, class_arguments);
        candidate.class_arguments = std::move(class_arguments);
        candidate.loc = guide_loc;
        candidate.source = source;
        candidate.pattern_type = pattern_type;
        candidate.allow_partial_ordering = allow_partial_ordering;
        candidate.is_explicit = is_explicit;
        candidate.user_guide = user_guide;
        candidate.conversions = std::move(pending_conversions);
        pending_conversions.clear();
        (list_phase_one ? phase_one_ctad_candidates
                        : viable_ctad_candidates)
            .push_back(std::move(candidate));
    };
    auto guide_has_initializer_list_parameter =
        [&](cir::TypeId guide_type) {
        cir::TypeId resolved = file.resolved_type(guide_type);
        const auto* function = file.valid(resolved)
            ? std::get_if<cir::FunctionTypePayload>(
                  &file.type_payload(resolved))
            : nullptr;
        return function && !function->parameters.empty() &&
            collect_session_.initializer_list_element_type(
                function->parameters.front().type).has_value();
    };
    bool use_list_phase_one =
        braced_initializer && braced_initializer->init_list;
    if (use_list_phase_one &&
        braced_initializer->init_list->elements.empty() && facts) {
        use_list_phase_one = !std::any_of(
            facts->methods.begin(), facts->methods.end(),
            [](const cir::RecordMethodFact& method) {
                return method.special_member_kind ==
                    cir::SpecialMemberKind::DefaultConstructor;
            });
    }
    auto project_implicit_alias_guide =
        [&](cir::TypeId guide_type,
            const std::vector<collect::Session::TemplateParameter>&
                guide_parameters,
            cir::TypeId& projected_type,
            std::vector<collect::Session::TemplateParameter>&
                projected_parameters) -> bool {
        if (!alias_projection) {
            projected_type = guide_type;
            projected_parameters = guide_parameters;
            return true;
        }
        if (guide_parameters.size() < info.parameters.size()) {
            return false;
        }

        if (guide_parameters.size() == info.parameters.size() &&
            result_info.parameters.size() == info.parameters.size() &&
            alias_projection->target_arguments.size() ==
                info.parameters.size()) {
            bool direct_parameter_projection = true;
            std::vector<TypeParamRemap> direct_remaps;
            direct_remaps.reserve(info.parameters.size());
            for (size_t i = 0; i < info.parameters.size(); ++i) {
                const auto& source = info.parameters[i];
                const auto& destination = result_info.parameters[i];
                const auto& argument =
                    alias_projection->target_arguments[i];
                if (source.kind != destination.kind) {
                    direct_parameter_projection = false;
                    break;
                }
                TypeParamRemap remap;
                if (source.kind ==
                    collect::Session::TemplateParameterKind::Type) {
                    cir::TypeId argument_type =
                        file.resolved_type(argument.type.type);
                    const auto* parameter = file.valid(argument_type)
                        ? std::get_if<cir::TypeParamTypePayload>(
                              &file.type_payload(argument_type))
                        : nullptr;
                    if (argument.kind !=
                            cir::TemplateArgumentKind::Type ||
                        !parameter ||
                        parameter->index != destination.index) {
                        direct_parameter_projection = false;
                        break;
                    }
                    remap.from = source.type_param_type;
                    remap.to = destination.type_param_type;
                } else if (source.kind ==
                           collect::Session::TemplateParameterKind::NonType) {
                    if (argument.kind !=
                            cir::TemplateArgumentKind::Value ||
                        argument.value_param_index != destination.index) {
                        direct_parameter_projection = false;
                        break;
                    }
                    remap.value_from = source.index;
                    remap.value_to = destination.index;
                } else {
                    if (argument.kind !=
                            cir::TemplateArgumentKind::Template ||
                        argument.template_param_index != destination.index) {
                        direct_parameter_projection = false;
                        break;
                    }
                    remap.template_from = source.index;
                    remap.template_to = destination.index;
                    remap.template_entity = destination.entity;
                    remap.template_name = destination.name;
                    remap.template_parameters =
                        destination.nested_parameters();
                    remap.template_is_parameter_pack =
                        destination.is_parameter_pack;
                }
                direct_remaps.push_back(std::move(remap));
            }
            if (direct_parameter_projection) {
                projected_parameters = result_info.parameters;
                projected_type = remap_type_params_in_type(
                    collect_session_, guide_type, direct_remaps);
                return projected_type.valid();
            }
        }

        collect::Session::TemplateArgumentBindings target_bindings;
        if (!collect_session_.bind_template_arguments_to_parameters(
                info.parameters,
                alias_projection->target_arguments,
                target_bindings)) {
            return false;
        }

        uint32_t maximum_index = 0;
        for (size_t i = 0; i < guide_parameters.size(); ++i) {
            uint32_t index = guide_parameters[i].index ==
                    cir::ArrayTypePayload::no_extent_param
                ? static_cast<uint32_t>(i)
                : guide_parameters[i].index;
            maximum_index = std::max(maximum_index, index);
        }
        collect::Session::TemplateArgumentBindings guide_bindings(
            static_cast<size_t>(maximum_index) + 1);
        for (size_t i = 0; i < info.parameters.size(); ++i) {
            uint32_t guide_index = guide_parameters[i].index ==
                    cir::ArrayTypePayload::no_extent_param
                ? static_cast<uint32_t>(i)
                : guide_parameters[i].index;
            uint32_t target_index = info.parameters[i].index ==
                    cir::ArrayTypePayload::no_extent_param
                ? static_cast<uint32_t>(i)
                : info.parameters[i].index;
            if (target_index >= target_bindings.size() ||
                guide_index >= guide_bindings.size()) {
                return false;
            }
            guide_bindings[guide_index] = target_bindings[target_index];
        }

        projected_parameters = result_info.parameters;
        std::vector<TypeParamRemap> remaps;
        remaps.reserve(guide_parameters.size() - info.parameters.size());
        for (size_t i = info.parameters.size();
             i < guide_parameters.size();
             ++i) {
            const collect::Session::TemplateParameter& original =
                guide_parameters[i];
            if (original.is_parameter_pack) {

                return false;
            }
            uint32_t original_index = original.index ==
                    cir::ArrayTypePayload::no_extent_param
                ? static_cast<uint32_t>(i)
                : original.index;
            if (original_index >= guide_bindings.size()) {
                return false;
            }
            collect::Session::TemplateParameter appended = original;
            appended.index =
                static_cast<uint32_t>(projected_parameters.size());

            collect::Session::TemplateArgument placeholder;
            placeholder.is_dependent = true;
            TypeParamRemap remap;
            if (original.kind ==
                collect::Session::TemplateParameterKind::Type) {
                cir::TypeId source = original.type_param_type;
                if (!source.valid()) {
                    return false;
                }
                appended.type_param_type =
                    collect_session_.file().type_param_type(
                        {},
                        appended.name,
                        appended.index,
                        appended.depth,
                        false);
                placeholder.kind = cir::TemplateArgumentKind::Type;
                placeholder.type = collect_session_.type_ref(
                    appended.type_param_type);
                remap.from = source;
                remap.to = appended.type_param_type;
            } else if (original.kind ==
                       collect::Session::TemplateParameterKind::NonType) {
                placeholder.kind = cir::TemplateArgumentKind::Value;
                placeholder.value_param_index = appended.index;
                placeholder.value_spelling = appended.name;
                placeholder.value_type = collect_session_.type_ref(
                    appended.non_type_type);
                remap.value_from = original_index;
                remap.value_to = appended.index;
            } else {
                placeholder.kind = cir::TemplateArgumentKind::Template;
                placeholder.template_entity = appended.entity;
                placeholder.template_param_index = appended.index;
                if (!appended.name.empty()) {
                    placeholder.template_name =
                        collect_session_.file().intern_name(appended.name);
                }
                remap.template_from = original_index;
                remap.template_to = appended.index;
                remap.template_entity = appended.entity;
                remap.template_name = appended.name;
                remap.template_parameters = appended.nested_parameters();
                remap.template_is_parameter_pack = false;
            }
            guide_bindings[original_index].kind =
                collect::Session::TemplateArgumentBindingKind::Single;
            guide_bindings[original_index].arguments = {
                std::move(placeholder)};
            remaps.push_back(std::move(remap));
            projected_parameters.push_back(std::move(appended));
        }

        for (size_t i = result_info.parameters.size();
             i < projected_parameters.size();
             ++i) {
            collect::Session::TemplateParameter& parameter =
                projected_parameters[i];
            if (parameter.default_argument.has_value()) {
                parameter.default_argument =
                    remap_template_argument_placeholders(
                        collect_session_,
                        std::move(*parameter.default_argument),
                        remaps);
            }
        }

        collect::Session::PatternInstantiationCallbacks callbacks;
        configure_pattern_instantiation_callbacks(callbacks, loc);
        projected_type = collect_session_.substitute_pattern_type(
            guide_type, guide_bindings, callbacks);
        return projected_type.valid();
    };

    auto guide_arguments_convert =
        [&](const collect::Session::TemplateInfo& guide,
            const std::vector<collect::ExprResult>& inputs,
            const collect::Session::TemplateArgumentBindings& bindings) {
        pending_conversions.clear();
        const cir::File& file = collect_session_.file();
        cir::TypeId pattern = file.resolved_type(guide.pattern_type);
        if (!file.valid(pattern) ||
            file.type(pattern).kind != cir::TypeKind::Function) {
            return true;
        }
        collect::Session::PatternInstantiationCallbacks callbacks;
        callbacks.access_loc = loc;
        configure_pattern_instantiation_callbacks(callbacks, loc);
        if (!collect_session_.populate_exact_template_parameter_bindings(
                guide, bindings, callbacks)) {
            return true;
        }
        cir::TypeId substituted = collect_session_.substitute_pattern_type(
            pattern, bindings, callbacks);
        cir::TypeId resolved = file.resolved_type(substituted);
        if (!file.valid(resolved) ||
            file.type(resolved).kind != cir::TypeKind::Function ||
            collect_session_.is_dependent_type(resolved)) {

            return true;
        }
        const auto* function = std::get_if<cir::FunctionTypePayload>(
            &file.type_payload(resolved));
        if (!function) {
            return true;
        }
        std::vector<CtadConversion> conversions;
        conversions.reserve(inputs.size());
        for (size_t i = 0;
             i < inputs.size() && i < function->parameters.size(); ++i) {
            const collect::ExprResult& input = inputs[i];
            if (!input.type.valid() ||
                collect_session_.expr_is_dependent(input) ||
                collect_session_.is_dependent_type(
                    function->parameters[i].type)) {
                conversions.clear();
                return true;
            }
            CtadConversion conversion;
            conversion.rank = collect_session_.conversion_rank(
                input,
                function->parameters[i],
                0,
                &conversion.detail,
                /*allow_user_defined=*/true);
            conversion.detail.standard.rank = conversion.rank;
            if (conversion.rank == collect::Session::ConversionRank::Bad) {
                return false;
            }
            conversions.push_back(std::move(conversion));
        }
        pending_conversions = std::move(conversions);
        return true;
    };
    auto consider_guide =
        [&](cir::TypeId guide_type,
            cir::EntityId guide_entity,
            SrcLoc guide_loc,
            const std::vector<collect::Session::TemplateParameter>&
                guide_parameters,
            CtadCandidateSource source,
            bool is_explicit = false) {
        if (!guide_type.valid()) {
            return;
        }
        cir::TypeId candidate_type{};
        std::vector<collect::Session::TemplateParameter>
            candidate_parameters;
        if (!project_implicit_alias_guide(guide_type,
                                          guide_parameters,
                                          candidate_type,
                                          candidate_parameters)) {
            return;
        }
        collect::Session::TemplateInfo guide;
        guide.name = result_info.name;
        guide.parameters = std::move(candidate_parameters);
        guide.pattern_type = candidate_type;
        guide.entity = guide_entity;
        auto deduce = [&](const std::vector<collect::ExprResult>& inputs,
                          bool list_phase_one) {
            std::vector<collect::Session::TemplateArgument> deduced;
            collect::Session::TemplateArgumentBindings argument_bindings;
            if (!collect_session_.deduce_template_arguments(guide,
                                                            inputs,
                                                            deduced,
                                                            nullptr,
                                                            nullptr,
                                                            &argument_bindings) ||
                argument_bindings.size() <
                    result_info.parameters.size()) {
                return;
            }
            if (!guide_arguments_convert(guide, inputs, argument_bindings)) {
                return;
            }
            collect::Session::TemplateArgumentBindings result_bindings(
                argument_bindings.begin(),
                argument_bindings.begin() +
                    result_info.parameters.size());
            std::vector<collect::Session::TemplateArgument> class_arguments =
                collect_session_.flatten_template_argument_bindings(
                    result_bindings);
            add_class_arguments(std::move(class_arguments),
                                guide_loc,
                                is_explicit,
                                source,
                                candidate_type,
                                false,
                                list_phase_one);
        };
        if (use_list_phase_one &&
            guide_has_initializer_list_parameter(candidate_type)) {
            deduce(std::vector<collect::ExprResult>{*braced_initializer},
                   true);
        }
        deduce(arguments, false);
    };
    auto substitute_user_guide_return_arguments =
        [&](const collect::Session::TemplateInfo::DeductionGuide& stored,
            const collect::Session::TemplateArgumentBindings&
                argument_bindings,
            std::vector<collect::Session::TemplateArgument>& class_arguments)
        -> bool {
        class_arguments.clear();
        collect::Session::PatternInstantiationCallbacks callbacks;
        configure_pattern_instantiation_callbacks(callbacks, loc);
        auto substitute_argument =
            [&](collect::Session::TemplateArgument argument,
                const collect::Session::TemplateArgumentBindings& bindings,
                collect::Session::PatternInstantiationCallbacks& active_callbacks)
            -> std::optional<collect::Session::TemplateArgument> {
            if (argument.kind == cir::TemplateArgumentKind::Type) {
                if (!argument.type.type.valid() ||
                    !collect_session_.is_dependent_type(argument.type.type)) {
                    argument.expands_parameter_pack = false;
                    argument.expands_pack_pattern = false;
                    return argument;
                }
                cir::TypeRef substituted =
                    collect_session_.substitute_pattern_type_ref(
                        argument.type, bindings, active_callbacks);
                if (!substituted.valid()) {
                    return std::nullopt;
                }
                argument.type = substituted;
                argument.is_dependent =
                    collect_session_.is_dependent_type(substituted.type);
            } else if (argument.kind == cir::TemplateArgumentKind::Value) {
                if (!argument.is_dependent &&
                    !argument.dependent_value_expr.valid()) {
                    argument.expands_parameter_pack = false;
                    argument.expands_pack_pattern = false;
                    return argument;
                }
                std::string error;
                if (!collect_session_.substitute_template_value_argument(
                        argument,
                        bindings,
                        active_callbacks,
                        &error)) {
                    return std::nullopt;
                }
            } else if (argument.kind ==
                       cir::TemplateArgumentKind::Template) {
                std::string error;
                if (!collect_session_.substitute_template_template_argument(
                        argument,
                        bindings,
                        active_callbacks,
                        &error)) {
                    return std::nullopt;
                }
            } else if (argument.is_dependent) {
                return std::nullopt;
            }
            argument.expands_parameter_pack = false;
            argument.expands_pack_pattern = false;
            return argument;
        };
        auto append_pack_index =
            [&](std::vector<uint32_t>& indices, uint32_t index) {
            if (index == cir::ArrayTypePayload::no_extent_param ||
                index >= stored.parameters.size() ||
                !stored.parameters[index].is_parameter_pack ||
                std::find(indices.begin(), indices.end(), index) !=
                    indices.end()) {
                return;
            }
            indices.push_back(index);
        };
        std::function<void(cir::TypeId, std::vector<uint32_t>&)>
            collect_type_pack_indices;
        std::function<void(const collect::Session::TemplateArgument&,
                           std::vector<uint32_t>&)>
            collect_argument_pack_indices;
        collect_argument_pack_indices =
            [&](const collect::Session::TemplateArgument& argument,
                std::vector<uint32_t>& indices) {
            if (argument.kind == cir::TemplateArgumentKind::Type) {
                collect_type_pack_indices(argument.type.type, indices);
                return;
            }
            if (argument.kind == cir::TemplateArgumentKind::Value) {
                append_pack_index(indices, argument.value_param_index);
                for (const cir::TemplateValueExprNode& node :
                     argument.dependent_value_expr.nodes) {
                    if (node.kind ==
                        cir::TemplateValueExprKind::Parameter) {
                        append_pack_index(indices, node.parameter_index);
                    }
                }
                collect_type_pack_indices(argument.value_type.type, indices);
                collect_type_pack_indices(
                    argument.dependent_value_qualifier.type, indices);
                return;
            }
            append_pack_index(indices, argument.template_param_index);
            collect_type_pack_indices(
                argument.dependent_template_qualifier.type, indices);
        };
        collect_type_pack_indices =
            [&](cir::TypeId type, std::vector<uint32_t>& indices) {
            cir::TypeId resolved = file.resolved_type(type);
            if (!file.valid(resolved)) {
                return;
            }
            const cir::TypePayload& payload = file.type_payload(resolved);
            switch (file.type(resolved).kind) {
                case cir::TypeKind::TypeParam: {
                    const auto& parameter =
                        std::get<cir::TypeParamTypePayload>(payload);
                    if (parameter.is_parameter_pack) {
                        append_pack_index(indices, parameter.index);
                    }
                    return;
                }
                case cir::TypeKind::Pointer:
                    collect_type_pack_indices(
                        std::get<cir::PointerTypePayload>(payload)
                            .pointee.type,
                        indices);
                    return;
                case cir::TypeKind::BlockPointer:
                    collect_type_pack_indices(
                        std::get<cir::BlockPointerTypePayload>(payload)
                            .pointee.type,
                        indices);
                    return;
                case cir::TypeKind::LValueReference:
                case cir::TypeKind::RValueReference:
                    collect_type_pack_indices(
                        std::get<cir::ReferenceTypePayload>(payload)
                            .referred_type.type,
                        indices);
                    return;
                case cir::TypeKind::Array:
                    collect_type_pack_indices(
                        std::get<cir::ArrayTypePayload>(payload)
                            .element_type.type,
                        indices);
                    append_pack_index(
                        indices,
                        std::get<cir::ArrayTypePayload>(payload).extent_param);
                    return;
                case cir::TypeKind::MemberPointer: {
                    const auto& member =
                        std::get<cir::MemberPointerTypePayload>(payload);
                    collect_type_pack_indices(member.class_type.type, indices);
                    collect_type_pack_indices(member.member_type.type, indices);
                    return;
                }
                case cir::TypeKind::TemplateSpecialization:
                    for (const auto& argument :
                         std::get<cir::TemplateSpecializationTypePayload>(
                             payload).arguments) {
                        collect_argument_pack_indices(argument, indices);
                    }
                    return;
                case cir::TypeKind::DependentName: {
                    const auto& dependent =
                        std::get<cir::DependentNameTypePayload>(payload);
                    collect_type_pack_indices(dependent.qualifier_type.type,
                                              indices);
                    for (const auto& argument :
                         dependent.template_arguments) {
                        collect_argument_pack_indices(argument, indices);
                    }
                    return;
                }
                case cir::TypeKind::Record: {
                    const cir::TemplateSpecializationFact* fact =
                        file.template_specialization(
                            file.record_entity(resolved));
                    if (fact) {
                        for (const auto& argument :
                             fact->template_arguments()) {
                            collect_argument_pack_indices(argument, indices);
                        }
                    }
                    return;
                }
                case cir::TypeKind::Function: {
                    const auto& function =
                        std::get<cir::FunctionTypePayload>(payload);
                    collect_type_pack_indices(function.return_type.type,
                                              indices);
                    for (const cir::TypeRef& parameter :
                         function.parameters) {
                        collect_type_pack_indices(parameter.type, indices);
                    }
                    return;
                }
                default:
                    return;
            }
        };
        for (const collect::Session::TemplateArgument& pattern_argument :
             stored.return_arguments) {
            if (!pattern_argument.expands_parameter_pack) {
                std::optional<collect::Session::TemplateArgument> substituted =
                    substitute_argument(pattern_argument,
                                        argument_bindings,
                                        callbacks);
                if (!substituted.has_value()) {
                    return false;
                }
                class_arguments.push_back(std::move(*substituted));
                continue;
            }

            std::vector<uint32_t> pack_indices;
            collect_argument_pack_indices(pattern_argument, pack_indices);
            if (pack_indices.empty()) {
                return false;
            }
            std::optional<size_t> expansion_size;
            for (uint32_t pack_index : pack_indices) {
                if (pack_index >= argument_bindings.size() ||
                    !argument_bindings[pack_index].is_pack()) {
                    return false;
                }
                size_t size =
                    argument_bindings[pack_index].arguments.size();
                if (expansion_size.has_value() && *expansion_size != size) {
                    return false;
                }
                expansion_size = size;
            }
            for (size_t element_index = 0;
                 element_index < expansion_size.value_or(0);
                 ++element_index) {
                collect::Session::TemplateArgumentBindings element_bindings =
                    argument_bindings;
                for (uint32_t pack_index : pack_indices) {
                    element_bindings[pack_index].kind =
                        collect::Session::TemplateArgumentBindingKind::Single;
                    element_bindings[pack_index].arguments = {
                        argument_bindings[pack_index]
                            .arguments[element_index]};
                }
                collect::Session::PatternInstantiationCallbacks
                    element_callbacks = callbacks;
                element_callbacks.allow_parameter_pack_element_substitution =
                    true;
                collect::Session::TemplateArgument element_pattern =
                    pattern_argument;
                element_pattern.expands_parameter_pack = false;
                element_pattern.expands_pack_pattern = false;
                std::optional<collect::Session::TemplateArgument> substituted =
                    substitute_argument(std::move(element_pattern),
                                        element_bindings,
                                        element_callbacks);
                if (!substituted.has_value()) {
                    return false;
                }
                class_arguments.push_back(std::move(*substituted));
            }
        }
        return true;
    };
    auto project_alias_return_arguments =
        [&](std::vector<collect::Session::TemplateArgument>&
                class_arguments) -> bool {
        if (!alias_projection) {
            return true;
        }
        std::vector<collect::Session::TemplateArgument> alias_arguments;
        if (!collect_session_
                 .deduce_template_arguments_from_argument_pattern(
                     result_info,
                     alias_projection->target_arguments,
                     class_arguments,
                     alias_arguments)) {
            return false;
        }
        class_arguments = std::move(alias_arguments);
        return true;
    };
    auto consider_user_guide =
        [&](const collect::Session::TemplateInfo::DeductionGuide& stored) {
        if (!stored.pattern_type.valid()) {
            return;
        }
        collect::Session::TemplateInfo guide;
        guide.name = result_info.name;
        guide.parameters = stored.parameters;
        guide.pattern_type = stored.pattern_type;
        guide.introduced_constraints = stored.introduced_constraints;
        guide.lexical_context = stored.declaration_context;
        guide.definition_generation = stored.declaration_generation;
        auto deduce = [&](const std::vector<collect::ExprResult>& inputs,
                          bool list_phase_one) {
            std::vector<collect::Session::TemplateArgument> deduced;
            collect::Session::TemplateArgumentBindings argument_bindings;
            if (!collect_session_.deduce_template_arguments(guide,
                                                            inputs,
                                                            deduced,
                                                            nullptr,
                                                            nullptr,
                                                            &argument_bindings,
                                                            stored.loc,
                                                            &stored.parameter_default_argument_flags)) {
                return;
            }
            if (!check_template_associated_constraints(
                    guide,
                    deduced,
                    stored.loc,
                    stored.declaration_generation,
                    /*diagnose_unsatisfied=*/false,
                    &argument_bindings)) {
                return;
            }
            if (!guide_arguments_convert(guide, inputs, argument_bindings)) {
                return;
            }
            std::vector<collect::Session::TemplateArgument> class_arguments;
            if (!substitute_user_guide_return_arguments(stored,
                                                        argument_bindings,
                                                        class_arguments)) {
                return;
            }
            if (!project_alias_return_arguments(class_arguments)) {
                return;
            }
            bool effective_explicit = stored.is_explicit;
            if (stored.explicit_specifier ==
                cir::ExplicitSpecifierKind::Dependent) {
                guide.entity = info.entity;
                guide.lexical_context = stored.explicit_declaration_context;
                guide.definition_generation =
                    stored.explicit_lookup_generation;
                guide.explicit_specifier = stored.explicit_specifier;
                guide.explicit_expression_begin =
                    stored.explicit_expression_begin;
                guide.explicit_expression_end = stored.explicit_expression_end;
                guide.explicit_value_expression =
                    stored.explicit_value_expression;
                std::optional<bool> resolved =
                    replay_explicit_specifier(guide,
                                              deduced,
                                              stored.loc,
                                              &argument_bindings);
                if (!resolved.has_value()) {
                    return;
                }
                effective_explicit = *resolved;
            }
            add_class_arguments(std::move(class_arguments),
                                stored.loc,
                                effective_explicit,
                                CtadCandidateSource::UserGuide,
                                stored.pattern_type,
                                !stored.parameters.empty(),
                                list_phase_one,
                                &stored);
        };
        if (use_list_phase_one &&
            guide_has_initializer_list_parameter(stored.pattern_type)) {
            deduce(std::vector<collect::ExprResult>{*braced_initializer},
                   true);
        }
        deduce(arguments, false);
    };

    if (facts) {
        for (const cir::RecordMethodFact& method : facts->methods) {
            if (!method.entity.valid() || !file.valid(method.entity) ||
                file.entity(method.entity).kind !=
                    cir::EntityKind::Constructor) {
                continue;
            }
            if (const collect::Session::TemplateInfo* constructor_template =
                    collect_session_.template_info(method.entity)) {
                std::vector<collect::Session::TemplateParameter>
                    guide_parameters;
                cir::TypeId guide_type =
                    constructor_template_guide_type(*constructor_template,
                                                    guide_parameters);
                consider_guide(guide_type,
                               method.entity,
                               file.entity(method.entity).loc,
                               guide_parameters,
                               CtadCandidateSource::ConstructorTemplate,
                               method.is_explicit);
                continue;
            }
            consider_guide(method.type.type,
                           method.entity,
                           file.entity(method.entity).loc,
                           info.parameters,
                           CtadCandidateSource::Constructor,
                           method.is_explicit);
        }
    }

    bool add_hypothetical_empty_guide =
        !info.has_definition ||
        (facts && !facts->definition_data.has_user_declared_constructor);
    if (add_hypothetical_empty_guide) {
        consider_guide(hypothetical_empty_guide_type(),
                       {},
                       loc,
                       info.parameters,
                       CtadCandidateSource::Constructor);
    }
    consider_guide(simple_aggregate_guide_type(),
                   {},
                   loc,
                   info.parameters,
                   CtadCandidateSource::Aggregate);
    consider_guide(hypothetical_copy_guide_type(),
                   {},
                   loc,
                   info.parameters,
                   CtadCandidateSource::Copy);
    for (const collect::Session::TemplateInfo::DeductionGuide& guide :
         info.deduction_guides) {
        consider_user_guide(guide);
    }

    if (!phase_one_ctad_candidates.empty()) {
        viable_ctad_candidates = std::move(phase_one_ctad_candidates);
    }

    auto guide_template_more_specialized =
        [&](const CtadCandidate& lhs, const CtadCandidate& rhs) {
        if (lhs.source != CtadCandidateSource::UserGuide ||
            rhs.source != CtadCandidateSource::UserGuide ||
            !lhs.allow_partial_ordering ||
            !rhs.allow_partial_ordering ||
            !lhs.pattern_type.valid() ||
            !rhs.pattern_type.valid() ||
            !lhs.user_guide || !rhs.user_guide) {
            return false;
        }
        auto candidate_info =
            [&](const collect::Session::TemplateInfo::DeductionGuide& stored) {
            collect::Session::TemplateInfo candidate;
            candidate.name = info.name;
            candidate.parameters = stored.parameters;
            candidate.pattern_type = stored.pattern_type;
            candidate.introduced_constraints =
                stored.introduced_constraints;
            candidate.lexical_context = stored.declaration_context;
            candidate.definition_generation =
                stored.declaration_generation;
            return candidate;
        };
        collect::Session::TemplateInfo lhs_info =
            candidate_info(*lhs.user_guide);
        collect::Session::TemplateInfo rhs_info =
            candidate_info(*rhs.user_guide);
        bool lhs_more = collect_session_.function_template_more_specialized(
            lhs.pattern_type,
            lhs_info,
            rhs.pattern_type,
            rhs_info,
            collect::Session::FunctionTemplateOrderingContext::call(
                arguments.size(), arguments.size()));
        bool rhs_more = collect_session_.function_template_more_specialized(
            rhs.pattern_type,
            rhs_info,
            lhs.pattern_type,
            lhs_info,
            collect::Session::FunctionTemplateOrderingContext::call(
                arguments.size(), arguments.size()));
        return lhs_more && !rhs_more;
    };

    auto conversion_sequences_compare = [&](const CtadCandidate& lhs,
                                            const CtadCandidate& rhs) -> int {
        if (lhs.conversions.empty() || rhs.conversions.empty() ||
            lhs.conversions.size() != rhs.conversions.size()) {
            return 0;
        }
        bool better = false;
        bool worse = false;
        for (size_t i = 0; i < lhs.conversions.size(); ++i) {
            int comparison =
                collect_session_.compare_implicit_conversion_sequences(
                    lhs.conversions[i].rank,
                    lhs.conversions[i].detail,
                    rhs.conversions[i].rank,
                    rhs.conversions[i].detail);
            if (comparison > 0) {
                better = true;
            } else if (comparison < 0) {
                worse = true;
            }
        }
        if (better && !worse) {
            return 1;
        }
        if (worse && !better) {
            return -1;
        }
        return 0;
    };
    auto candidate_better = [&](const CtadCandidate& lhs,
                                const CtadCandidate& rhs) {
        int sequences = conversion_sequences_compare(lhs, rhs);
        if (sequences != 0) {
            return sequences > 0;
        }
        int lhs_rank = candidate_source_rank(lhs.source);
        int rhs_rank = candidate_source_rank(rhs.source);
        if (lhs_rank != rhs_rank) {
            return lhs_rank > rhs_rank;
        }
        return guide_template_more_specialized(lhs, rhs);
    };

    std::optional<size_t> selected_index;
    for (size_t i = 0; i < viable_ctad_candidates.size(); ++i) {
        if (!selected_index.has_value() ||
            candidate_better(viable_ctad_candidates[i],
                             viable_ctad_candidates[*selected_index])) {
            selected_index = i;
        }
    }
    std::optional<size_t> conflicting_index;
    if (selected_index.has_value()) {
        for (size_t i = 0; i < viable_ctad_candidates.size(); ++i) {
            if (i == *selected_index ||
                viable_ctad_candidates[i].key ==
                    viable_ctad_candidates[*selected_index].key) {
                continue;
            }
            if (!candidate_better(viable_ctad_candidates[*selected_index],
                                  viable_ctad_candidates[i])) {
                conflicting_index = i;
                break;
            }
        }
    }

    bool ambiguous = conflicting_index.has_value();
    if (ambiguous) {
        diagnose(DiagnosticLevel::Error,
                 "class template argument deduction is ambiguous",
                 loc);
        const CtadCandidate& selected =
            viable_ctad_candidates[*selected_index];
        const CtadCandidate& conflicting =
            viable_ctad_candidates[*conflicting_index];
        if (!selected.loc.isInvalid()) {
            diagnose(DiagnosticLevel::Note,
                     candidate_source_note(selected.source),
                     selected.loc);
        }
        if (!conflicting.loc.isInvalid()) {
            diagnose(DiagnosticLevel::Note,
                     candidate_source_note(conflicting.source),
                     conflicting.loc);
        }
        return {};
    }
    if (!selected_index.has_value()) {
        diagnose(DiagnosticLevel::Error,
                 (info.deduction_guides.empty()
                      ? "no matching implicit deduction guide for class template '"
                      : "no matching deduction guide for class template '") +
                     result_info.name + "'",
                 loc);
        return {};
    }
    CtadCandidate& selected = viable_ctad_candidates[*selected_index];
    if (selected.is_explicit &&
        (initialization_kind == CtadInitializationKind::Copy ||
         initialization_kind == CtadInitializationKind::CopyList)) {
        diagnose(DiagnosticLevel::Error,
                 initialization_kind == CtadInitializationKind::CopyList
                     ? "explicit deduction guide selected in copy-list-initialization"
                     : "explicit deduction guide selected in copy-initialization",
                 selected.loc.isInvalid() ? loc : selected.loc);
        return {};
    }
    if (selected_aggregate_candidate) {
        *selected_aggregate_candidate =
            selected.source == CtadCandidateSource::Aggregate;
    }

    cir::EntityId specialization =
        instantiate_template_with_args(result_info,
                                       std::move(selected.class_arguments),
                                       loc,
                                       0,
                                       false,
                                       false,
                                       /*materialize_class_definition=*/false);
    if (!specialization.valid() || !file.valid(specialization)) {
        return {};
    }
    return file.entity(specialization).type;
}

cir::EntityId Parser::instantiate_template(
    const collect::Session::TemplateInfo& info,
    SrcLoc loc,
    bool record_point_of_instantiation) {
    if (info.is_template_parameter_pack &&
        !collect_session_.in_pack_pattern_capture()) {
        diagnose(DiagnosticLevel::Error,
                 "unexpanded template parameter pack '" + info.name +
                     "' is not supported yet",
                 loc);
        (void)parse_dependent_expression_template_argument_list(loc);
        return {};
    }
    if (info.is_template_parameter_pack) {
        collect_session_.capture_parameter_pack(
            collect::Session::ParameterPackKind::Template,
            info.name);
    }

    TemplateReplayGuardExit replay_guard{&collect_session_, false};
    if (!collect_session_.enter_template_replay_guard(loc)) {
        (void)parse_dependent_expression_template_argument_list(loc);
        return {};
    }
    replay_guard.active = true;

    std::vector<collect::Session::TemplateArgument> arguments;
    uint64_t point_lookup_generation = 0;
    if (!parse_and_canonicalize_template_argument_list(
            info,
            arguments,
            loc,
            &point_lookup_generation)) {
        return {};
    }
    return instantiate_template_with_args(info,
                                          std::move(arguments),
                                          loc,
                                          point_lookup_generation,
                                          /*replay_guard_entered=*/true,
                                           /*arguments_are_canonical=*/true,
                                           /*materialize_class_definition=*/
                                              !info.is_class_template,
                                           record_point_of_instantiation);
}

cir::TypeRef Parser::instantiate_or_defer_qualified_type_template(
    const collect::Session::TemplateInfo& info,
    cir::TypeRef qualifier,
    std::string_view member_name,
    SrcLoc loc) {
    TemplateReplayGuardExit replay_guard{&collect_session_, false};
    if (!collect_session_.enter_template_replay_guard(loc)) {
        (void)parse_dependent_expression_template_argument_list(loc);
        return {};
    }
    replay_guard.active = true;

    std::vector<collect::Session::TemplateArgument> arguments;
    uint64_t point_lookup_generation = 0;
    if (!parse_and_canonicalize_template_argument_list(
            info, arguments, loc, &point_lookup_generation)) {
        return {};
    }
    bool arity_is_dependent = std::any_of(
        arguments.begin(),
        arguments.end(),
        [](const collect::Session::TemplateArgument& argument) {
            return argument.expands_parameter_pack ||
                argument.expands_pack_pattern ||
                argument.generated_pack_kind !=
                    cir::TemplateGeneratedPackKind::None;
        });
    if (arity_is_dependent) {
        return collect_session_.type_ref(
            collect_session_.file().dependent_name_type(
                qualifier,
                member_name,
                std::move(arguments),
                false));
    }

    cir::EntityId instantiated = instantiate_template_with_args(
        info,
        std::move(arguments),
        loc,
        point_lookup_generation,
        /*replay_guard_entered=*/true,
        /*arguments_are_canonical=*/true,
        /*materialize_class_definition=*/!info.is_class_template);
    return instantiated.valid()
        ? collect_session_.file().entity_type_ref(instantiated)
        : cir::TypeRef{};
}

bool Parser::parse_template_template_argument_name(
    collect::Session::TemplateArgument& argument,
    collect::Session::TemplateTemplateParameterKind expected_kind,
    std::string expected_message,
    std::string must_name_message) {
    argument = collect::Session::TemplateArgument{};
    argument.kind = cir::TemplateArgumentKind::Template;

    bool starts_nested_name =
        check(TokenType::SCOPE_RESOLUTION) ||
        (is_identifier_token(current().type) &&
         peek(1).type == TokenType::SCOPE_RESOLUTION &&
         peek(2).type != TokenType::MULTIPLY) ||
        (lang_opts_.is_cxx_mode() &&
         is_identifier_token(current().type) &&
         peek(1).type == TokenType::LESS_THAN &&
         template_id_precedes_scope(0));
    ParsedNestedName nested;
    if (starts_nested_name) {
        nested = parse_nested_name_specifier();
    }

    if (nested.consumed_any && lang_opts_.is_cxx_mode() &&
        check(TokenType::TEMPLATE)) {
        consume();
    }

    if (!is_identifier_token(current().type)) {
        diagnose(DiagnosticLevel::Error,
                 std::move(expected_message),
                 current_loc());
        return false;
    }

    Token name_token = current();
    if (nested.consumed_any) {
        if (nested.has_error) {
            return false;
        }
        if (nested.scope.dependent_type.type.valid()) {
            argument.dependent_template_qualifier =
                nested.scope.dependent_type;
            argument.template_name =
                collect_session_.file().intern_name(name_token.value);
            argument.is_dependent = true;
            consume();
            return true;
        }
    }

    const collect::Session::TemplateInfo* argument_template = nullptr;
    if (nested.consumed_any) {
        argument_template = collect_session_.template_info_in_context(
            nested.scope.context,
            name_token.value,
            /*include_parents=*/false);
    } else {
        if (peek(1).type == TokenType::ELLIPSIS) {
            argument_template =
                collect_session_.template_parameter_pack_info_for_name(
                    name_token.value);
        }
        if (!argument_template) {
            argument_template =
                collect_session_.template_info_for_name(name_token.value);
        }
    }
    auto matches_expected_template_kind =
        [&](const collect::Session::TemplateInfo& info) {
        if (expected_kind ==
            collect::Session::TemplateTemplateParameterKind::Concept) {
            return info.is_concept;
        }
        if (expected_kind ==
            collect::Session::TemplateTemplateParameterKind::Variable) {
            return info.is_variable_template;
        }
        return info.is_class_template || info.is_alias_template;
    };

    if (!argument_template ||
        !matches_expected_template_kind(*argument_template)) {
        diagnose(DiagnosticLevel::Error,
                 std::move(must_name_message),
                 name_token.loc);
        return false;
    }
    if (argument_template->is_template_parameter_pack &&
        peek(1).type != TokenType::ELLIPSIS &&
        !collect_session_.in_pack_pattern_capture()) {
        diagnose(DiagnosticLevel::Error,
                 "unexpanded template parameter pack '" +
                     std::string(name_token.value) +
                     "' is not supported yet",
                 name_token.loc);
        consume();
        return false;
    }
    if (argument_template->is_template_parameter_pack) {
        collect_session_.capture_parameter_pack(
            collect::Session::ParameterPackKind::Template,
            name_token.value);
    }
    argument.template_entity = argument_template->entity;
    argument.template_name =
        collect_session_.file().intern_name(name_token.value);
    argument.template_param_index =
        argument_template->entity.valid() &&
                collect_session_.file().valid(argument_template->entity) &&
                collect_session_.file().entity(argument_template->entity).kind ==
                    cir::EntityKind::TemplateParam
            ? argument_template->template_parameter_index
            : cir::ArrayTypePayload::no_extent_param;
    argument.is_dependent =
        argument.template_param_index != cir::ArrayTypePayload::no_extent_param;
    consume();
    return true;
}

cir::TypeRef Parser::parse_builtin_type_pack_element_type(
    SrcLoc loc,
    std::vector<NodeId>& children) {
    (void)children;
    auto unknown_type = [&] {
        return collect_session_.type_ref(
            collect_session_.file().unknown_type());
    };
    if (!check(TokenType::LESS_THAN)) {
        diagnose(DiagnosticLevel::Error,
                 "expected '<' after __type_pack_element",
                 current_loc());
        return unknown_type();
    }

    collect::Session::TemplateInfo arguments_shape;
    arguments_shape.name = "__type_pack_element";

    collect::Session::TemplateParameter index_parameter;
    index_parameter.kind =
        collect::Session::TemplateParameterKind::NonType;
    index_parameter.non_type_type =
        collect_session_.file().builtin_type(
            cir::BuiltinTypeKind::USize);
    arguments_shape.parameters.push_back(std::move(index_parameter));

    collect::Session::TemplateParameter type_pack_parameter;
    type_pack_parameter.kind =
        collect::Session::TemplateParameterKind::Type;
    type_pack_parameter.is_parameter_pack = true;
    arguments_shape.parameters.push_back(
        std::move(type_pack_parameter));

    std::vector<collect::Session::TemplateArgument> arguments;
    if (!parse_template_argument_list(arguments_shape, arguments, loc)) {
        return unknown_type();
    }
    cir::TypeRef result =
        collect_session_.collect_builtin_pack_element_type(
            std::move(arguments), loc);
    return result.valid() ? result : unknown_type();
}

cir::TypeRef Parser::parse_builtin_make_integer_sequence_type(
    SrcLoc loc,
    std::vector<NodeId>& children,
    bool materialize_class_definition) {
    auto unknown_type = [&] {
        return collect_session_.type_ref(
            collect_session_.file().unknown_type());
    };
    if (!match(TokenType::LESS_THAN)) {
        diagnose(DiagnosticLevel::Error,
                 "expected '<' after __make_integer_seq",
                 current_loc());
        return unknown_type();
    }

    collect::Session::TemplateArgument target_argument;
    if (!parse_template_template_argument_name(
            target_argument,
            collect::Session::TemplateTemplateParameterKind::Type,
            "expected a template as the first __make_integer_seq argument",
            "first __make_integer_seq argument must name a class or alias template")) {
        return unknown_type();
    }
    if (!match(TokenType::COMMA)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ',' after __make_integer_seq template argument",
                 current_loc());
        return unknown_type();
    }

    cir::TypeRef value_type;
    NodeId value_type_syntax = parse_type_name(
        nullptr,
        nullptr,
        nullptr,
        &value_type,
        nullptr,
        nullptr,
        TypeParseContext::type_only(
            TypeParseContext::Origin::DefiningTypeId));
    children.push_back(value_type_syntax);
    if (!value_type.valid()) {
        diagnose(DiagnosticLevel::Error,
                 "expected an integral type as the second __make_integer_seq argument",
                 current_loc());
        return unknown_type();
    }
    if (!match(TokenType::COMMA)) {
        diagnose(DiagnosticLevel::Error,
                 "expected ',' after __make_integer_seq element type",
                 current_loc());
        return unknown_type();
    }

    ParsedExpr count = parse_template_argument_constant_expression();
    children.push_back(count.syntax);
    if (check(TokenType::GREATER_THAN)) {
        consume();
    } else if (check(TokenType::RIGHT_SHIFT)) {
        if (pending_template_closes_ > 0) {
            --pending_template_closes_;
            consume();
        } else {
            ++pending_template_closes_;
        }
    } else {
        pending_template_closes_ = 0;
        diagnose(DiagnosticLevel::Error,
                 "expected '>' after __make_integer_seq arguments",
                 current_loc());
        return unknown_type();
    }

    const collect::Session::TemplateInfo* target =
        collect_session_.template_info(target_argument.template_entity);
    if (!target || (!target->is_class_template && !target->is_alias_template)) {
        diagnose(DiagnosticLevel::Error,
                 "first __make_integer_seq argument must name a class or alias template",
                 loc);
        return unknown_type();
    }

    collect::Session::TemplateArgument generated_pack;
    std::vector<collect::Session::TemplateArgument> generated_arguments;
    std::string pack_error;
    if (!collect_session_.build_generated_integer_pack(
            value_type.type,
            std::move(count.sem),
            generated_pack,
            generated_arguments,
            loc,
            &pack_error)) {
        if (!pack_error.empty()) {
            diagnose(DiagnosticLevel::Error, pack_error, loc);
        }
        return unknown_type();
    }

    std::vector<collect::Session::TemplateArgument> arguments;
    arguments.reserve(1 + generated_arguments.size() +
                      (generated_pack.generated_pack_kind !=
                               cir::TemplateGeneratedPackKind::None
                           ? 1
                           : 0));
    collect::Session::TemplateArgument type_argument;
    type_argument.kind = cir::TemplateArgumentKind::Type;
    type_argument.type = value_type;
    type_argument.is_dependent =
        collect_session_.is_dependent_type(value_type.type);
    arguments.push_back(std::move(type_argument));
    if (generated_pack.generated_pack_kind !=
        cir::TemplateGeneratedPackKind::None) {
        arguments.push_back(std::move(generated_pack));
    } else {
        arguments.insert(
            arguments.end(),
            std::make_move_iterator(generated_arguments.begin()),
            std::make_move_iterator(generated_arguments.end()));
    }

    cir::EntityId specialization = instantiate_template_with_args(
        *target,
        std::move(arguments),
        loc,
        /*point_lookup_generation=*/0,
        /*replay_guard_entered=*/false,
        /*arguments_are_canonical=*/false,
        /*materialize_class_definition=*/
            !target->is_class_template || materialize_class_definition);
    if (!specialization.valid() ||
        !collect_session_.file().valid(specialization)) {
        return unknown_type();
    }
    return collect_session_.type_ref(
        collect_session_.file().entity(specialization).type);
}

Parser::ParsedExpr Parser::parse_template_argument_constant_expression() {
    template_argument_expression_begins_.push_back(cursor_);
    struct BoundaryExit {
        std::vector<size_t>& begins;
        ~BoundaryExit() {
            begins.pop_back();
        }
    } boundary_exit{template_argument_expression_begins_};
    return parse_conditional_expression();
}

bool Parser::at_template_argument_expression_close() const {
    if (template_argument_expression_begins_.empty() ||
        (current().type != TokenType::GREATER_THAN &&
         current().type != TokenType::RIGHT_SHIFT)) {
        return false;
    }

    int paren_depth = 0;
    int bracket_depth = 0;
    int brace_depth = 0;
    size_t begin = template_argument_expression_begins_.back();
    for (size_t index = begin;
         index < cursor_ && index < cooked_to_raw_.size();
         ++index) {
        switch (tokens_[cooked_to_raw_[index]].type) {
            case TokenType::LEFT_PAREN: ++paren_depth; break;
            case TokenType::RIGHT_PAREN: --paren_depth; break;
            case TokenType::LEFT_BRACKET: ++bracket_depth; break;
            case TokenType::RIGHT_BRACKET: --bracket_depth; break;
            case TokenType::LEFT_BRACE: ++brace_depth; break;
            case TokenType::RIGHT_BRACE: --brace_depth; break;
            default: break;
        }
    }
    return paren_depth == 0 && bracket_depth == 0 && brace_depth == 0;
}

bool Parser::parse_template_argument_list(
    const collect::Session::TemplateInfo& info,
    std::vector<collect::Session::TemplateArgument>& arguments,
    SrcLoc loc) {

    consume();
    if (!check(TokenType::GREATER_THAN) && !check(TokenType::RIGHT_SHIFT)) {
        size_t parameter_index = 0;
        const bool has_trailing_pack =
            !info.parameters.empty() && info.parameters.back().is_parameter_pack;
        const size_t trailing_pack_index =
            has_trailing_pack ? info.parameters.size() - 1
                              : info.parameters.size();
        auto argument_contains_unexpanded_pack =
            [&](const collect::Session::TemplateArgument& argument) {
            return collect_session_.template_argument_names_parameter_pack(
                argument);
        };
        auto begin_direct_pack_expansion_capture = [&] {
            collect::Session::ParameterPackPatternCaptureScope scope;
            if (is_identifier_token(current().type) &&
                peek(1).type == TokenType::ELLIPSIS) {

                scope = collect_session_
                    .begin_parameter_pack_pattern_capture();
            }
            return scope;
        };
        auto finish_direct_pack_expansion_capture =
            [&](collect::Session::ParameterPackPatternCaptureScope scope) {
            if (scope.active) {
                (void)collect_session_
                    .finish_parameter_pack_pattern_capture(scope);
            }
        };
        do {
            size_t effective_parameter_index = parameter_index;
            if (has_trailing_pack &&
                effective_parameter_index >= trailing_pack_index) {
                effective_parameter_index = trailing_pack_index;
            }
            collect::Session::TemplateArgument argument;
            bool append_argument = true;
            size_t argument_slot_count = 1;
            collect::Session::TemplateParameterKind parameter_kind =
                effective_parameter_index < info.parameters.size()
                    ? info.parameters[effective_parameter_index].kind
                    : collect::Session::TemplateParameterKind::Type;
            bool parsed_generated_pack = false;
            if (current().type == TokenType::IDENTIFIER &&
                current().value == "__integer_pack") {
                SrcLoc builtin_loc = current_loc();
                parsed_generated_pack = true;
                if (parameter_kind !=
                    collect::Session::TemplateParameterKind::NonType) {
                    diagnose(DiagnosticLevel::Error,
                             "__integer_pack must expand into non-type template arguments",
                             builtin_loc);
                    return false;
                }
                consume();
                if (!match(TokenType::LEFT_PAREN)) {
                    diagnose(DiagnosticLevel::Error,
                             "expected '(' after __integer_pack",
                             current_loc());
                    return false;
                }
                ParsedExpr count =
                    parse_template_argument_constant_expression();
                if (!match(TokenType::RIGHT_PAREN)) {
                    diagnose(DiagnosticLevel::Error,
                             "expected ')' after __integer_pack count",
                             current_loc());
                    return false;
                }
                if (!match(TokenType::ELLIPSIS)) {
                    diagnose(DiagnosticLevel::Error,
                             "__integer_pack must be followed by '...'",
                             current_loc());
                    return false;
                }
                std::vector<collect::Session::TemplateArgument> expanded;
                std::string pack_error;
                if (!collect_session_.build_generated_integer_pack(
                        count.sem.type,
                        std::move(count.sem),
                        argument,
                        expanded,
                        builtin_loc,
                        &pack_error)) {
                    if (!pack_error.empty()) {
                        diagnose(DiagnosticLevel::Error,
                                 pack_error,
                                 builtin_loc);
                    }
                    return false;
                }
                if (!expanded.empty() ||
                    argument.generated_pack_kind ==
                        cir::TemplateGeneratedPackKind::None) {
                    argument_slot_count = expanded.size();
                    arguments.insert(
                        arguments.end(),
                        std::make_move_iterator(expanded.begin()),
                        std::make_move_iterator(expanded.end()));
                    append_argument = false;
                }
            }
            if (!parsed_generated_pack) switch (parameter_kind) {
                case collect::Session::TemplateParameterKind::Type: {
                    argument.kind = cir::TemplateArgumentKind::Type;
                    auto parse_type_argument =
                        [&](cir::TypeId& parsed_type,
                            cir::TypeRef* parsed_type_ref = nullptr) {
                            cir::TypeRef type;

                            if (starts_cxx_qualified_name() &&
                                !peek_cxx_qualified_type().has_value()) {
                                if (std::optional<cir::TypeRef> qualified =
                                        parse_cxx_qualified_type_name(
                                            TypeParseContext{})) {
                                    type = *qualified;
                                }
                            }
                            if (!type.valid()) {
                                parse_type_name(&parsed_type,
                                                nullptr,
                                                nullptr,
                                                &type);
                            } else {
                                parsed_type = type.type;
                            }
                            if (parsed_type_ref) {
                                *parsed_type_ref = type;
                            }
                        };
                    bool parsed_direct_pack_name = false;

                    bool replays_type_pack_element =
                        is_identifier_token(current().type) &&
                        collect_session_.parameter_pack_replay_element(
                            collect::Session::ParameterPackKind::Type,
                            current().value) != nullptr;
                    if (is_identifier_token(current().type) &&
                        (peek(1).type == TokenType::ELLIPSIS ||
                         (!replays_type_pack_element &&
                          collect_session_.in_pack_pattern_capture() &&
                          (peek(1).type == TokenType::COMMA ||
                           peek(1).type == TokenType::GREATER_THAN ||
                           peek(1).type == TokenType::RIGHT_SHIFT)))) {
                        std::optional<cir::TypeId> pack_type =
                            collect_session_.type_parameter_pack_type(
                                current().value);
                        if (pack_type.has_value()) {
                            auto expansion_capture =
                                begin_direct_pack_expansion_capture();
                            collect_session_.capture_type_parameter_pack_name(
                                current().value);
                            finish_direct_pack_expansion_capture(
                                expansion_capture);
                            argument.type =
                                collect_session_.type_ref(*pack_type);
                            argument.is_dependent = true;
                            consume();
                            parsed_direct_pack_name = true;
                        }
                    }
                    if (!parsed_direct_pack_name) {
                        bool starts_unambiguous_value =
                            check(TokenType::INTEGER_CONST) ||
                            check(TokenType::UNSIGNED_INTEGER_CONST) ||
                            check(TokenType::LONG_CONST) ||
                            check(TokenType::UNSIGNED_LONG_CONST) ||
                            check(TokenType::LONG_LONG_CONST) ||
                            check(TokenType::UNSIGNED_LONG_LONG_CONST) ||
                            check(TokenType::CHAR_LITERAL) ||
                            check(TokenType::TRUE_KW) ||
                            check(TokenType::FALSE_KW) ||
                            check(TokenType::NULLPTR_KW);
                        if (starts_unambiguous_value) {
                            diagnose(DiagnosticLevel::Error,
                                     format_template_argument_kind_mismatch(
                                         static_cast<uint32_t>(
                                             effective_parameter_index),
                                         static_cast<uint32_t>(
                                             parameter_index),
                                         parameter_kind,
                                         cir::TemplateArgumentKind::Value),
                                     current_loc());
                            return false;
                        }
                        if (template_argument_has_pack_ellipsis()) {

                            std::optional<PackExpansionPattern> pattern =
                                try_parse_pack_expansion_pattern([&] {
                                    cir::TypeId pattern_type{};
                                    parse_type_argument(pattern_type);
                                });
                            if (pattern.has_value() &&
                                pattern->has_pack_names()) {
                                bool pack_arity_dependent = false;
                                std::optional<size_t> element_count =
                                    resolve_pack_expansion_element_count(
                                        *pattern, &pack_arity_dependent);
                                if (pack_arity_dependent) {
                                    cir::TypeId pattern_type{};
                                    cir::TypeRef pattern_type_ref{};
                                    parse_pack_expansion_pattern_deferred(
                                        [&] {
                                            parse_type_argument(
                                                pattern_type,
                                                &pattern_type_ref);
                                        });
                                    if (!pattern_type.valid()) {
                                        diagnose(
                                            DiagnosticLevel::Error,
                                            "template argument " +
                                                std::to_string(
                                                    parameter_index + 1) +
                                                " must be a type argument",
                                            current_loc());
                                        return false;
                                    }
                                    argument.type = pattern_type_ref;
                                    argument.is_dependent = true;
                                    argument.expands_pack_pattern = true;
                                    break;
                                }
                                replay_pack_expansion_elements(
                                    *pattern,
                                    element_count.value_or(0),
                                    [&](size_t) {
                                        cir::TypeId element_type{};
                                        cir::TypeRef element_type_ref{};
                                        parse_type_argument(
                                            element_type,
                                            &element_type_ref);
                                        if (!element_type.valid()) {
                                            return;
                                        }
                                        collect::Session::TemplateArgument
                                            element;
                                        element.kind =
                                            cir::TemplateArgumentKind::Type;
                                        element.type = element_type_ref;
                                        arguments.push_back(
                                            std::move(element));
                                    });
                                append_argument = false;
                                argument_slot_count = element_count.value_or(0);
                                break;
                            }
                        }
                        std::optional<Token> type_name_token;
                        if (is_identifier_token(current().type)) {
                            type_name_token = current();
                        }
                        cir::TypeId parsed_type{};
                        cir::TypeRef parsed_type_ref{};
                        parse_type_argument(parsed_type, &parsed_type_ref);
                        if (!parsed_type.valid()) {
                            std::string message =
                                "template argument " +
                                std::to_string(parameter_index + 1) +
                                " must be a type argument";
                            diagnose(DiagnosticLevel::Error,
                                     std::move(message),
                                     current_loc());
                            return false;
                        }
                        if (type_name_token.has_value() &&
                            collect_session_.type_contains_type_parameter_pack(
                                parsed_type)) {
                            collect_session_.capture_type_parameter_pack_name(
                                type_name_token->value);
                        }
                        argument.type = parsed_type_ref;
                    }
                    break;
                }
                case collect::Session::TemplateParameterKind::NonType: {
                    cir::TypeId expected_type =
                        effective_parameter_index < info.parameters.size() &&
                                info.parameters[effective_parameter_index]
                                    .non_type_type.valid()
                            ? info.parameters[effective_parameter_index]
                                  .non_type_type
                            : collect_session_.file().builtin_type(
                                  cir::BuiltinTypeKind::Int);
                    if (effective_parameter_index < info.parameters.size()) {
                        argument.value_type =
                            collect_session_.type_ref(expected_type);
                    }
                    bool parsed_direct_pack_name = false;

                    bool replays_value_pack_element =
                        is_identifier_token(current().type) &&
                        collect_session_.parameter_pack_replay_element(
                            collect::Session::ParameterPackKind::Value,
                            current().value) != nullptr;
                    if (is_identifier_token(current().type) &&
                        (peek(1).type == TokenType::ELLIPSIS ||
                         (!replays_value_pack_element &&
                          collect_session_.in_pack_pattern_capture() &&
                          (peek(1).type == TokenType::COMMA ||
                           peek(1).type == TokenType::GREATER_THAN ||
                           peek(1).type == TokenType::RIGHT_SHIFT)))) {
                        std::optional<uint32_t> value_param_index =
                            collect_session_
                                .template_value_pack_param_index_for_name(
                                    current().value);
                        if (value_param_index.has_value()) {
                            std::optional<
                                collect::Session::ParameterPackIdentity>
                                value_pack_identity =
                                    collect_session_.parameter_pack_identity(
                                        collect::Session::ParameterPackKind::
                                            Value,
                                        current().value);
                            auto expansion_capture =
                                begin_direct_pack_expansion_capture();
                            collect_session_.capture_parameter_pack(
                                collect::Session::ParameterPackKind::Value,
                                current().value);
                            finish_direct_pack_expansion_capture(
                                expansion_capture);
                            argument.kind = cir::TemplateArgumentKind::Value;
                            argument.value_type =
                                collect_session_.type_ref(expected_type);
                            argument.value_param_index = *value_param_index;
                            if (value_pack_identity.has_value()) {
                                argument.value_entity =
                                    value_pack_identity->declaration;
                            }
                            argument.dependent_value_name =
                                collect_session_.file().intern_name(
                                    current().value);
                            argument.value_spelling =
                                std::string(current().value);
                            argument.is_dependent = true;
                            consume();
                            parsed_direct_pack_name = true;
                        }
                    }
                    if (parsed_direct_pack_name) {
                        break;
                    }
                    if (template_argument_has_pack_ellipsis()) {

                        std::optional<PackExpansionPattern> pattern =
                            try_parse_pack_expansion_pattern([&] {
                                (void)
                                    parse_template_argument_constant_expression();
                            });
                        if (pattern.has_value() &&
                            pattern->has_pack_names()) {
                            bool pack_arity_dependent = false;
                            std::optional<size_t> element_count =
                                resolve_pack_expansion_element_count(
                                    *pattern, &pack_arity_dependent);
                            if (pack_arity_dependent) {
                                ParsedExpr pattern_value;
                                parse_pack_expansion_pattern_deferred([&] {
                                    pattern_value =
                                        parse_template_argument_constant_expression();
                                });
                                argument.kind =
                                    cir::TemplateArgumentKind::Value;
                                argument.value_type =
                                    collect_session_.type_ref(expected_type);
                                argument.value_spelling = node_text(
                                    tree_.node(pattern->syntax));
                                argument.is_dependent = true;
                                argument.expands_pack_pattern = true;
                                if (collect_session_.expr_is_value_dependent(
                                        pattern_value.sem)) {
                                    argument.dependent_value_expr =
                                        collect_session_
                                            .template_value_operand_expression(
                                                pattern_value.sem);
                                    if (argument.dependent_value_expr.valid()) {
                                        collect_session_.file()
                                            .canonicalize_template_value_expression(
                                                argument
                                                    .dependent_value_expr);
                                    }
                                }
                                break;
                            }
                            bool element_failed = false;
                            replay_pack_expansion_elements(
                                *pattern,
                                element_count.value_or(0),
                                [&](size_t) {
                                    ParsedExpr element_value =
                                        parse_template_argument_constant_expression();
                                    collect::Session::TemplateArgument
                                        element;
                                    element.kind =
                                        cir::TemplateArgumentKind::Value;
                                    element.value_type =
                                        collect_session_.type_ref(
                                            expected_type);
                                    if (element_value.sem.template_value_expr
                                                .valid() &&
                                        collect_session_
                                            .expr_is_value_dependent(
                                                element_value.sem) &&
                                        !collect_session_
                                             .in_pack_pattern_capture()) {
                                        const auto& expression =
                                            element_value.sem
                                                .template_value_expr;
                                        bool retains_unexpanded_pack =
                                            std::any_of(
                                                expression.nodes.begin(),
                                                expression.nodes.end(),
                                                [](const auto& node) {
                                                    return node
                                                               .expands_parameter_pack ||
                                                        !node.pack_references
                                                             .empty();
                                                });
                                        if (!retains_unexpanded_pack) {

                                            element.dependent_value_expr =
                                                std::move(
                                                    element_value.sem
                                                        .template_value_expr);
                                            element.value_spelling =
                                                element_value.sem.name;
                                            element.is_dependent = true;
                                            collect_session_.file()
                                                .canonicalize_template_value_expression(
                                                    element
                                                        .dependent_value_expr);
                                            arguments.push_back(
                                                std::move(element));
                                            return;
                                        }
                                    }
                                    if (element_value.sem
                                                .dependent_value_name.valid() &&
                                        element_value.sem
                                            .dependent_value_qualifier.type
                                            .valid() &&
                                        collect_session_
                                            .expr_is_value_dependent(
                                                element_value.sem)) {

                                        element.dependent_value_qualifier =
                                            element_value.sem
                                                .dependent_value_qualifier;
                                        element.dependent_value_name =
                                            element_value.sem
                                                .dependent_value_name;
                                        const cir::File& file =
                                            collect_session_.file();
                                        element.value_spelling =
                                            file.format_type(
                                                element
                                                    .dependent_value_qualifier) +
                                            "::" +
                                            std::string(file.name(
                                                element
                                                    .dependent_value_name));
                                        element.is_dependent = true;
                                        arguments.push_back(
                                            std::move(element));
                                        return;
                                    }
                                    collect::Session::TemplateValueConstant
                                        element_constant;
                                    if (!collect_session_
                                             .evaluate_template_value_constant(
                                                 std::move(element_value.sem),
                                                 expected_type,
                                                 element_constant,
                                                 loc,
                                                 "template argument is not a "
                                                 "constant expression")) {
                                        element_failed = true;
                                        return;
                                    }
                                    std::string element_error;
                                    if (!collect_session_
                                             .build_template_value_argument(
                                                 expected_type,
                                                 element_constant,
                                                 element,
                                                 &element_error)) {
                                        diagnose(DiagnosticLevel::Error,
                                                 element_error,
                                                 loc);
                                        element_failed = true;
                                        return;
                                    }
                                    arguments.push_back(std::move(element));
                                });
                            if (element_failed) {
                                return false;
                            }
                            append_argument = false;
                            argument_slot_count = element_count.value_or(0);
                            break;
                        }
                    }
                    auto starts_qualified_id_expression = [&]() {
                        return check(TokenType::SCOPE_RESOLUTION) ||
                               (is_identifier_token(current().type) &&
                                peek(1).type == TokenType::SCOPE_RESOLUTION &&
                                peek(2).type != TokenType::MULTIPLY) ||
                               (lang_opts_.is_cxx_mode() &&
                                is_identifier_token(current().type) &&
                                peek(1).type == TokenType::LESS_THAN &&
                                template_id_precedes_scope(0));
                    };
                    bool starts_type_conversion_expression =
                        is_type_start(current().type) &&
                        (peek(1).type == TokenType::LEFT_PAREN ||
                         peek(1).type == TokenType::LEFT_BRACE ||
                         (peek(1).type == TokenType::LESS_THAN &&
                          template_id_precedes_type_conversion(0)));
                    if (is_type_start(current().type) &&
                        !starts_type_conversion_expression &&
                        !starts_qualified_id_expression()) {
                        diagnose(DiagnosticLevel::Error,
                                 format_template_argument_kind_mismatch(
                                     static_cast<uint32_t>(
                                         effective_parameter_index),
                                     static_cast<uint32_t>(parameter_index),
                                     parameter_kind,
                                     cir::TemplateArgumentKind::Type),
                                 current_loc());
                        return false;
                    }
                    ParsedExpr value =
                        parse_template_argument_constant_expression();
                    if (info.is_candidate_neutral_argument_recipe &&
                        collect_session_.contains_auto_type(
                            expected_type, cir::AutoTypeFlavor::Cxx)) {
                        uint8_t source_qualifiers = cir::QualNone;
                        if (value.sem.entity.valid() &&
                            collect_session_.file().valid(
                                value.sem.entity)) {
                            source_qualifiers =
                                collect_session_.file()
                                    .entity(value.sem.entity)
                                    .qualifiers;
                        }
                        bool preserves_designator =
                            value.sem.category ==
                                collect::ValueCategory::LValue ||
                            value.sem.category ==
                                collect::ValueCategory::XValue ||
                            value.sem.category ==
                                collect::ValueCategory::FunctionDesignator;
                        if (preserves_designator &&
                            value.sem.type.valid()) {
                            expected_type =
                                collect_session_.reference_type(
                                    collect_session_.type_ref(
                                        value.sem.type,
                                        source_qualifiers),
                                    value.sem.category ==
                                            collect::ValueCategory::XValue
                                        ? cir::ReferenceKind::RValue
                                        : cir::ReferenceKind::LValue);
                        } else if (value.sem.type.valid() &&
                                   !collect_session_.is_dependent_type(
                                       value.sem.type)) {
                            expected_type = value.sem.type;
                        }
                        argument.value_type =
                            collect_session_.type_ref(expected_type);
                    }
                    if (value.sem.init_list &&
                        value.sem.category ==
                            collect::ValueCategory::InitList) {
                        if (collect_session_.contains_auto_type(
                                expected_type,
                                cir::AutoTypeFlavor::Cxx)) {
                            const auto& elements =
                                value.sem.init_list->elements;
                            if (elements.size() != 1 ||
                                !elements.front().designators.empty() ||
                                elements.front().value.init_list) {
                                diagnose(
                                    DiagnosticLevel::Error,
                                    "braced constant template argument for "
                                    "'auto' requires exactly one "
                                    "initializer-clause",
                                    loc);
                                return false;
                            }
                            expected_type =
                                collect_session_.deduce_auto_type(
                                    expected_type,
                                    elements.front().value,
                                    loc);
                            if (!expected_type.valid()) {
                                diagnose(
                                    DiagnosticLevel::Error,
                                    "cannot deduce auto template parameter "
                                    "type from braced argument",
                                    loc);
                                return false;
                            }
                            argument.value_type =
                                collect_session_.type_ref(expected_type);
                        }
                        if (!collect_session_.is_dependent_type(
                                expected_type)) {
                            value.sem = collect_session_
                                .materialize_list_initialization(
                                    std::move(value.sem),
                                    expected_type,
                                    collect::UseContext::Assignment,
                                    loc);
                        }
                    }
                    if (info.is_candidate_neutral_argument_recipe &&
                        value.sem.category == collect::ValueCategory::LValue &&
                        value.sem.entity.valid() &&
                        collect_session_.file().valid(value.sem.entity)) {
                        const cir::Entity& entity =
                            collect_session_.file().entity(value.sem.entity);
                        if (entity.storage_duration ==
                                cir::StorageDuration::Static ||
                            entity.storage_duration ==
                                cir::StorageDuration::Thread) {
                            argument.kind = cir::TemplateArgumentKind::Value;
                            argument.value_type =
                                collect_session_.type_ref(expected_type);
                            argument.value_kind =
                                cir::TemplateValueKind::Address;
                            argument.value_entity = value.sem.entity;
                            argument.value_spelling = value.sem.name;
                            collect::Session::TemplateValueConstant
                                alternative_constant;
                            cir::TypeId alternative_type = entity.type;
                            const cir::File& file =
                                collect_session_.file();
                            cir::TypeId resolved_alternative =
                                file.resolved_type(alternative_type);
                            if (file.valid(resolved_alternative) &&
                                (file.type(resolved_alternative).kind ==
                                     cir::TypeKind::LValueReference ||
                                 file.type(resolved_alternative).kind ==
                                     cir::TypeKind::RValueReference)) {
                                alternative_type =
                                    file.reference_referred_type(
                                        resolved_alternative);
                            }
                            if (alternative_type.valid() &&
                                collect_session_
                                    .template_value_constant_from_entity(
                                        value.sem.entity,
                                        alternative_constant)) {
                                auto alternative = std::make_shared<
                                    collect::Session::TemplateArgument>();
                                std::string alternative_error;
                                if (collect_session_
                                        .build_template_value_argument(
                                            alternative_type,
                                            alternative_constant,
                                            *alternative,
                                            &alternative_error)) {
                                    argument.unconverted_value_alternative =
                                        std::move(alternative);
                                }
                            }
                            break;
                        }
                    }
                    uint32_t value_param_index =
                        collect_session_.template_value_param_index(
                            value.sem.entity);
                    if (value_param_index !=
                        cir::ArrayTypePayload::no_extent_param) {
                        collect_session_.capture_parameter_pack(
                            collect::Session::ParameterPackKind::Value,
                            value.sem.name);
                        argument.kind = cir::TemplateArgumentKind::Value;
                        argument.value_type =
                            collect_session_.type_ref(expected_type);
                        argument.value_param_index = value_param_index;
                        argument.value_spelling = value.sem.name;
                        argument.is_dependent = true;
                        break;
                    }
                    if (value.sem.template_value_expr.valid() &&
                        collect_session_.expr_is_value_dependent(value.sem)) {
                        argument.kind = cir::TemplateArgumentKind::Value;
                        argument.value_type =
                            collect_session_.type_ref(expected_type);
                        argument.dependent_value_expr =
                            std::move(value.sem.template_value_expr);
                        argument.value_spelling = value.sem.name;
                        argument.is_dependent = true;
                        break;
                    }
                    if (value.sem.dependent_value_name.valid() &&
                        value.sem.dependent_value_qualifier.type.valid()) {
                        argument.kind = cir::TemplateArgumentKind::Value;
                        argument.value_type =
                            collect_session_.type_ref(expected_type);
                        argument.dependent_value_qualifier =
                            value.sem.dependent_value_qualifier;
                        argument.dependent_value_name =
                            value.sem.dependent_value_name;
                        const cir::File& file = collect_session_.file();
                        argument.value_spelling =
                            file.format_type(
                                argument.dependent_value_qualifier) +
                            "::" + file.name(argument.dependent_value_name);
                        argument.is_dependent = true;
                        break;
                    }
                    if (collect_session_.in_pack_pattern_capture() &&
                        collect_session_.expr_is_dependent(value.sem)) {

                        argument.kind = cir::TemplateArgumentKind::Value;
                        argument.value_type =
                            collect_session_.type_ref(expected_type);
                        argument.value_spelling = value.sem.name;
                        argument.is_dependent = true;
                        argument.expands_pack_pattern = true;
                        break;
                    }
                    if (collect_session_.contains_auto_type(
                            expected_type,
                            cir::AutoTypeFlavor::Cxx)) {
                        cir::TypeId deduced_type =
                            collect_session_.deduce_auto_type(expected_type,
                                                              value.sem,
                                                              loc);
                        if (!deduced_type.valid()) {
                            diagnose(DiagnosticLevel::Error,
                                     "cannot deduce auto template parameter type",
                                     loc);
                            return false;
                        }
                        expected_type = deduced_type;
                        argument.value_type =
                            collect_session_.type_ref(expected_type);
                    } else if (!collect_session_
                                    .class_template_placeholder_info(
                                        expected_type) &&
                               collect_session_.is_dependent_type(
                                   expected_type) &&
                               value.sem.type.valid() &&
                               !collect_session_.expr_is_dependent(value.sem)) {

                        expected_type = value.sem.type;
                        argument.value_type =
                            collect_session_.type_ref(expected_type);
                    }
                    cir::TypeId resolved_expected =
                        collect_session_.file().resolved_type(expected_type);
                    bool is_class_template_placeholder =
                        collect_session_.class_template_placeholder_info(
                            expected_type) != nullptr;
                    if (is_class_template_placeholder ||
                        (!info.is_candidate_neutral_argument_recipe &&
                         collect_session_.file().valid(resolved_expected) &&
                         collect_session_.file()
                                 .type(resolved_expected)
                                 .kind == cir::TypeKind::Record)) {
                        std::string value_error;
                        if (!collect_session_
                                 .form_class_template_value_argument(
                            expected_type,
                            std::move(value.sem),
                            argument,
                            loc,
                            "template argument is not a constant expression",
                            &value_error)) {
                            if (!value_error.empty()) {
                                diagnose(DiagnosticLevel::Error,
                                         value_error,
                                         loc);
                            }
                            return false;
                        }
                        break;
                    }
                    std::optional<collect::ExprResult> value_alternative;
                    cir::TypeId value_alternative_type{};
                    if (info.is_candidate_neutral_argument_recipe &&
                        value.sem.type.valid()) {
                        if (value.sem.category ==
                                collect::ValueCategory::LValue &&
                            value.sem.entity.valid() &&
                            collect_session_.file().valid(value.sem.entity) &&
                            collect_session_.file()
                                .entity(value.sem.entity)
                                .decl_flags.is_constexpr) {
                            value_alternative = value.sem;
                            value_alternative_type = value.sem.type;
                        } else if (value.sem.category ==
                                       collect::ValueCategory::
                                           FunctionDesignator &&
                                   value.sem.type.valid()) {
                            value_alternative = value.sem;
                            value_alternative_type =
                                collect_session_.pointer_type(
                                    collect_session_.type_ref(value.sem.type));
                        }
                    }
                    std::shared_ptr<collect::Session::TemplateArgument>
                        built_value_alternative;
                    if (value_alternative.has_value() &&
                        value_alternative_type.valid()) {
                        collect::Session::TemplateValueConstant
                            alternative_constant;
                        if (collect_session_.evaluate_template_value_constant(
                                std::move(*value_alternative),
                                value_alternative_type,
                                alternative_constant,
                                loc,
                                "candidate-neutral value interpretation is not a constant expression")) {
                            auto alternative = std::make_shared<
                                collect::Session::TemplateArgument>();
                            std::string alternative_error;
                            if (collect_session_.build_template_value_argument(
                                    value_alternative_type,
                                    alternative_constant,
                                    *alternative,
                                    &alternative_error)) {
                                built_value_alternative =
                                    std::move(alternative);
                            }
                        }
                    }
                    collect::Session::TemplateValueConstant constant;
                    if (!collect_session_.evaluate_template_value_constant(
                            std::move(value.sem),
                            expected_type,
                            constant,
                            loc,
                            "template argument is not a constant expression")) {
                        return false;
                    }
                    std::string value_error;
                    if (!collect_session_.build_template_value_argument(
                            expected_type,
                            constant,
                            argument,
                            &value_error)) {
                        diagnose(DiagnosticLevel::Error,
                                 value_error,
                                 loc);
                        return false;
                    }
                    argument.unconverted_value_alternative =
                        std::move(built_value_alternative);
                    break;
                }
                case collect::Session::TemplateParameterKind::Template: {
                    const collect::Session::TemplateParameter& parameter =
                        info.parameters[effective_parameter_index];
                    auto expansion_capture =
                        begin_direct_pack_expansion_capture();
                    bool parsed_template_argument =
                        parse_template_template_argument_name(
                            argument,
                            parameter.template_template_parameter_kind,
                            "expected a template template argument",
                            parameter.template_template_parameter_kind ==
                                    collect::Session::
                                        TemplateTemplateParameterKind::Concept
                                ? "template template argument must name a concept template"
                                : "template template argument must name a class or alias template");
                    finish_direct_pack_expansion_capture(expansion_capture);
                    if (!parsed_template_argument) {
                        return false;
                    }
                    break;
                }
            }
            if (!parsed_generated_pack && check(TokenType::ELLIPSIS)) {
                if (!argument_contains_unexpanded_pack(argument)) {
                    diagnose(DiagnosticLevel::Error,
                             "pack expansion pattern does not contain a template parameter pack",
                             current_loc());
                    return false;
                }
                consume();
                std::optional<
                    std::vector<collect::Session::TemplateArgument>>
                    concrete_pack =
                        collect_session_.template_argument_pack_arguments(
                            argument);
                if (concrete_pack.has_value()) {
                    argument_slot_count = concrete_pack->size();
                    arguments.insert(arguments.end(),
                                     std::make_move_iterator(
                                         concrete_pack->begin()),
                                     std::make_move_iterator(
                                         concrete_pack->end()));
                    append_argument = false;
                } else {
                    argument.expands_parameter_pack = true;
                }
            }
            if (append_argument) {
                collect_session_.file().canonicalize_template_value_expression(
                    argument.dependent_value_expr);
                arguments.push_back(argument);
            }
            parameter_index += argument_slot_count;
        } while (match(TokenType::COMMA));
    }
    if (check(TokenType::GREATER_THAN)) {
        consume();
    } else if (check(TokenType::RIGHT_SHIFT)) {

        if (pending_template_closes_ > 0) {
            --pending_template_closes_;
            consume();
        } else {
            ++pending_template_closes_;
        }
    } else {
        pending_template_closes_ = 0;
        diagnose(DiagnosticLevel::Error,
                 "expected '>' after template arguments",
                 current_loc());
        return false;
    }
    return true;
}

bool Parser::parse_candidate_neutral_template_argument_list(
    const collect::Session::TemplateInfo& request_info,
    std::vector<collect::Session::TemplateArgument>& arguments,
    SrcLoc loc) {
    struct Shape {
        collect::Session::TemplateParameterKind kind =
            collect::Session::TemplateParameterKind::NonType;
        collect::Session::TemplateTemplateParameterKind template_kind =
            collect::Session::TemplateTemplateParameterKind::Type;
        bool expands_pack = false;
    };
    std::vector<Shape> shapes;
    size_t saved_pending_template_closes = pending_template_closes_;
    auto classification_capture_checkpoint =
        collect_session_.checkpoint_parameter_pack_pattern_capture();

    {

        RevertingTentativeParsingAction classification(
            *this, TentativeMode::CollectBacked);
        if (!match(TokenType::LESS_THAN)) {
            collect_session_.restore_parameter_pack_pattern_capture(
                classification_capture_checkpoint);
            pending_template_closes_ = saved_pending_template_closes;
            return false;
        }
        while (!check(TokenType::GREATER_THAN) &&
               !check(TokenType::RIGHT_SHIFT) && !at_end()) {
            Shape shape;
            auto at_argument_end = [&]() {
                return check(TokenType::COMMA) ||
                       check(TokenType::GREATER_THAN) ||
                       check(TokenType::RIGHT_SHIFT) ||
                       check(TokenType::ELLIPSIS);
            };
            auto parse_candidate_type_id = [&]() {
                cir::TypeRef type;
                if (starts_cxx_qualified_name() &&
                    !peek_cxx_qualified_type().has_value()) {
                    if (std::optional<cir::TypeRef> qualified =
                            parse_cxx_qualified_type_name(
                                TypeParseContext{})) {
                        type = *qualified;
                    }
                }
                cir::TypeId type_id = type.type;
                if (!type.valid()) {
                    parse_type_name(&type_id, nullptr, nullptr, &type);
                }
                return type_id;
            };

            bool is_template_name = false;
            for (collect::Session::TemplateTemplateParameterKind kind : {
                     collect::Session::TemplateTemplateParameterKind::Type,
                     collect::Session::TemplateTemplateParameterKind::Variable,
                     collect::Session::TemplateTemplateParameterKind::Concept}) {
                bool accepted = false;
                {
                    RevertingTentativeParsingAction trial(
                        *this, TentativeMode::CollectBacked);
                    collect::Session::TemplateArgument ignored;
                    size_t diagnostics_before = diagnostics_.size();
                    size_t errors_before =
                        collect_session_.file().errors().size();
                    accepted = parse_template_template_argument_name(
                                   ignored, kind, "", "") &&
                               at_argument_end() &&
                               diagnostics_.size() == diagnostics_before &&
                               collect_session_.file().errors().size() ==
                                   errors_before;
                }
                if (accepted) {
                    shape.kind =
                        collect::Session::TemplateParameterKind::Template;
                    shape.template_kind = kind;
                    is_template_name = true;
                    break;
                }
            }

            bool is_type_id = false;
            if (!is_template_name) {
                RevertingTentativeParsingAction trial(
                    *this, TentativeMode::CollectBacked);
                size_t diagnostics_before = diagnostics_.size();
                size_t errors_before = collect_session_.file().errors().size();
                cir::TypeId type = parse_candidate_type_id();
                is_type_id = type.valid() && at_argument_end() &&
                             diagnostics_.size() == diagnostics_before &&
                             collect_session_.file().errors().size() ==
                                 errors_before;
            }

            if (is_template_name) {
                collect::Session::TemplateArgument ignored;
                (void)parse_template_template_argument_name(
                    ignored, shape.template_kind, "", "");
            } else if (is_type_id) {
                shape.kind = collect::Session::TemplateParameterKind::Type;
                (void)parse_candidate_type_id();
            } else {
                shape.kind = collect::Session::TemplateParameterKind::NonType;
                (void)parse_template_argument_constant_expression();
            }

            if (match(TokenType::ELLIPSIS)) {
                shape.expands_pack = true;
            }
            shapes.push_back(shape);
            if (!match(TokenType::COMMA)) {
                break;
            }
        }
    }

    collect_session_.restore_parameter_pack_pattern_capture(
        classification_capture_checkpoint);
    pending_template_closes_ = saved_pending_template_closes;

    collect::Session::TemplateInfo neutral = request_info;
    neutral.is_candidate_neutral_argument_recipe = true;
    neutral.parameters.clear();
    neutral.parameters.reserve(shapes.size());
    const bool request_has_trailing_pack =
        !request_info.parameters.empty() &&
        request_info.parameters.back().is_parameter_pack;
    for (size_t shape_index = 0; shape_index < shapes.size();
         ++shape_index) {
        const Shape& shape = shapes[shape_index];
        collect::Session::TemplateParameter parameter;
        parameter.kind = shape.kind;
        parameter.is_parameter_pack = shape.expands_pack;
        if (shape.kind ==
            collect::Session::TemplateParameterKind::NonType) {
            size_t request_parameter_index = shape_index;
            if (request_has_trailing_pack &&
                request_parameter_index >=
                    request_info.parameters.size() - 1) {
                request_parameter_index =
                    request_info.parameters.size() - 1;
            }
            const collect::Session::TemplateParameter* request_parameter =
                request_parameter_index < request_info.parameters.size()
                ? &request_info.parameters[request_parameter_index]
                : nullptr;
            cir::TypeId candidate_placeholder_type =
                request_parameter &&
                        request_parameter->kind ==
                            collect::Session::TemplateParameterKind::
                                NonType &&
                        collect_session_.class_template_placeholder_info(
                            request_parameter->non_type_type)
                    ? request_parameter->non_type_type
                    : cir::TypeId{};
            if (candidate_placeholder_type.valid()) {

                parameter.non_type_type = candidate_placeholder_type;
            } else {

                parameter.non_type_type =
                    collect_session_.auto_type(cir::AutoTypeFlavor::Cxx);
            }
        } else if (shape.kind ==
                   collect::Session::TemplateParameterKind::Template) {
            parameter.template_template_parameter_kind = shape.template_kind;
        }
        neutral.parameters.push_back(std::move(parameter));
    }
    return parse_template_argument_list(neutral, arguments, loc);
}

bool Parser::parse_dependent_type_template_argument_list(
    std::vector<collect::Session::TemplateArgument>& arguments,
    SrcLoc loc) {

    collect::Session::TemplateInfo neutral;
    return parse_candidate_neutral_template_argument_list(neutral,
                                                          arguments,
                                                          loc);
}

bool Parser::parse_dependent_expression_template_argument_list(
    SrcLoc loc,
    size_t* argument_list_begin,
    size_t* argument_list_end,
    std::vector<collect::Session::TemplateArgument>* arguments_out) {

    size_t begin = current_raw_index();
    if (arguments_out) {
        bool parsed = parse_dependent_type_template_argument_list(
            *arguments_out, loc);
        if (parsed) {
            if (argument_list_begin) {
                *argument_list_begin = begin;
            }
            if (argument_list_end) {
                *argument_list_end = current_raw_index();
            }
        }
        return parsed;
    }
    if (!match(TokenType::LESS_THAN)) {
        diagnose(DiagnosticLevel::Error,
                 "expected '<' after dependent template name",
                 loc);
        return false;
    }
    auto finish_success = [&]() {
        if (argument_list_begin) {
            *argument_list_begin = begin;
        }
        if (argument_list_end) {
            *argument_list_end = current_raw_index();
        }
        return true;
    };

    int angle_depth = 1;
    int paren_depth = 0;
    int bracket_depth = 0;
    int brace_depth = 0;
    size_t guard = 0;
    while (!at_end() && guard++ < 4096) {
        TokenType type = current().type;
        if (collect_session_.in_pack_pattern_capture() &&
            is_identifier_token(type)) {

            (void)collect_session_.capture_any_parameter_pack_name(
                current().value);
        }
        bool inside_group =
            paren_depth > 0 || bracket_depth > 0 || brace_depth > 0;
        switch (type) {
            case TokenType::LEFT_PAREN:
                ++paren_depth;
                consume();
                continue;
            case TokenType::RIGHT_PAREN:
                if (paren_depth > 0) {
                    --paren_depth;
                }
                consume();
                continue;
            case TokenType::LEFT_BRACKET:
                ++bracket_depth;
                consume();
                continue;
            case TokenType::RIGHT_BRACKET:
                if (bracket_depth > 0) {
                    --bracket_depth;
                }
                consume();
                continue;
            case TokenType::LEFT_BRACE:
                ++brace_depth;
                consume();
                continue;
            case TokenType::RIGHT_BRACE:
                if (brace_depth > 0) {
                    --brace_depth;
                    consume();
                    continue;
                }
                break;
            case TokenType::LESS_THAN:
                if (!inside_group) {
                    ++angle_depth;
                }
                consume();
                continue;
            case TokenType::GREATER_THAN:
                if (!inside_group) {
                    --angle_depth;
                    consume();
                    if (angle_depth == 0) {
                        return finish_success();
                    }
                    if (angle_depth < 0) {
                        break;
                    }
                    continue;
                }
                consume();
                continue;
            case TokenType::RIGHT_SHIFT:
                if (!inside_group) {
                    if (angle_depth > 1) {
                        angle_depth -= 2;
                        consume();
                        if (angle_depth == 0) {
                            return finish_success();
                        }
                        continue;
                    }
                    if (angle_depth == 1) {
                        if (pending_template_closes_ > 0) {
                            --pending_template_closes_;
                            consume();
                        } else {
                            ++pending_template_closes_;
                        }
                        return finish_success();
                    }
                    break;
                }
                consume();
                continue;
            case TokenType::Eof:
            case TokenType::SEMICOLON:
                break;
            default:
                consume();
                continue;
        }
        break;
    }

    pending_template_closes_ = 0;
    diagnose(DiagnosticLevel::Error,
             "expected '>' after template arguments",
             loc);
    return false;
}

Parser::TemplateArgumentListParsingRequest::
    TemplateArgumentListParsingRequest(
        collect::Session& session,
        collect::Session::TemplateArgumentListParsingScope scope)
    : session(&session), scope(scope) {}

Parser::TemplateArgumentListParsingRequest::
    TemplateArgumentListParsingRequest(
        TemplateArgumentListParsingRequest&& other) noexcept
    : session(std::exchange(other.session, nullptr)),
      scope(other.scope) {
    other.scope = {};
}

Parser::TemplateArgumentListParsingRequest&
Parser::TemplateArgumentListParsingRequest::operator=(
    TemplateArgumentListParsingRequest&& other) noexcept {
    if (this != &other) {
        finish();
        session = std::exchange(other.session, nullptr);
        scope = other.scope;
        other.scope = {};
    }
    return *this;
}

Parser::TemplateArgumentListParsingRequest::~TemplateArgumentListParsingRequest() {
    finish();
}

void Parser::TemplateArgumentListParsingRequest::finish() {
    if (session) {
        session->finish_template_argument_list_parsing(scope);
        session = nullptr;
        scope = {};
    }
}

Parser::TemplateArgumentListParsingRequest
Parser::begin_template_argument_list_parsing_request(
    const collect::Session::TemplateInfo& info,
    SrcLoc loc,
    uint64_t point_lookup_generation) {
    return TemplateArgumentListParsingRequest{
        collect_session_,
        collect_session_.begin_template_argument_list_parsing(
            info,
            loc,
            point_lookup_generation)};
}

bool Parser::parse_template_argument_list_with_request(
    const collect::Session::TemplateInfo& info,
    std::vector<collect::Session::TemplateArgument>& arguments,
    SrcLoc loc,
    uint64_t point_lookup_generation) {
    TemplateArgumentListParsingRequest request =
        begin_template_argument_list_parsing_request(info,
                                                     loc,
                                                     point_lookup_generation);
    if (!request.active()) {
        (void)parse_dependent_expression_template_argument_list(loc);
        return false;
    }
    return parse_template_argument_list(info, arguments, loc);
}

bool Parser::parse_candidate_neutral_template_argument_list_with_request(
    const collect::Session::TemplateInfo& info,
    std::vector<collect::Session::TemplateArgument>& arguments,
    SrcLoc loc,
    uint64_t point_lookup_generation) {
    TemplateArgumentListParsingRequest request =
        begin_template_argument_list_parsing_request(info,
                                                     loc,
                                                     point_lookup_generation);
    if (!request.active()) {
        (void)parse_dependent_expression_template_argument_list(loc);
        return false;
    }
    return parse_candidate_neutral_template_argument_list(info,
                                                          arguments,
                                                          loc);
}

bool Parser::parse_function_template_argument_list_for_candidates(
    const collect::Session::TemplateInfo& requested_info,
    const std::vector<const collect::Session::TemplateInfo*>& candidates,
    std::vector<collect::Session::TemplateArgument>& arguments,
    std::vector<collect::CandidateExplicitTemplateArguments>&
        candidate_arguments,
    SrcLoc loc,
    const collect::Session::TemplateInfo** selected_info) {
    if (selected_info) {
        *selected_info = &requested_info;
    }
    candidate_arguments.clear();
    std::vector<const collect::Session::TemplateInfo*>
        normalized_candidates;
    normalized_candidates.reserve(candidates.size() + 1);
    auto same_candidate =
        [](const collect::Session::TemplateInfo* lhs,
           const collect::Session::TemplateInfo* rhs) {
            if (lhs == rhs) {
                return true;
            }
            return lhs && rhs && lhs->entity.valid() &&
                rhs->entity.valid() && lhs->entity == rhs->entity;
        };
    for (const collect::Session::TemplateInfo* candidate : candidates) {
        if (!candidate ||
            std::any_of(normalized_candidates.begin(),
                        normalized_candidates.end(),
                        [&](const collect::Session::TemplateInfo* existing) {
                            return same_candidate(existing, candidate);
                        })) {
            continue;
        }
        normalized_candidates.push_back(candidate);
    }
    if (std::none_of(
            normalized_candidates.begin(),
            normalized_candidates.end(),
            [&](const collect::Session::TemplateInfo* candidate) {
                return same_candidate(candidate, &requested_info);
            })) {

        normalized_candidates.push_back(&requested_info);
    }
    auto has_class_template_placeholder =
        [&](const collect::Session::TemplateInfo& candidate) {
        return std::any_of(
            candidate.parameters.begin(),
            candidate.parameters.end(),
            [&](const collect::Session::TemplateParameter& parameter) {
                return parameter.kind ==
                           collect::Session::TemplateParameterKind::NonType &&
                    collect_session_.class_template_placeholder_info(
                        parameter.non_type_type) != nullptr;
            });
    };
    bool has_placeholder_candidate =
        normalized_candidates.size() > 1 &&
        std::any_of(
            normalized_candidates.begin(),
            normalized_candidates.end(),
            [&](const collect::Session::TemplateInfo* candidate) {
                return candidate &&
                    has_class_template_placeholder(*candidate);
            });
    if (!has_placeholder_candidate) {
        return normalized_candidates.size() > 1
            ? parse_candidate_neutral_template_argument_list_with_request(
                  requested_info, arguments, loc)
            : parse_template_argument_list_with_request(
                  requested_info, arguments, loc);
    }

    ParserCheckpoint argument_begin = capture_parser_checkpoint();
    const collect::Session::TemplateInfo* retained_candidate = nullptr;
    for (const collect::Session::TemplateInfo* candidate :
         normalized_candidates) {
        if (!candidate) {
            continue;
        }
        restore_parser_checkpoint(argument_begin);
        auto capture_checkpoint =
            collect_session_.checkpoint_parameter_pack_pattern_capture();
        TentativeParsingAction replay(
            *this, TentativeMode::CollectBacked);
        std::vector<collect::Session::TemplateArgument>
            replayed_arguments;
        bool replayed =
            parse_candidate_neutral_template_argument_list_with_request(
                *candidate, replayed_arguments, loc);
        collect_session_.restore_parameter_pack_pattern_capture(
            capture_checkpoint);
        if (!replayed) {
            collect::CandidateExplicitTemplateArguments rejected;
            rejected.template_entity = candidate->entity;
            rejected.viable = false;
            candidate_arguments.push_back(std::move(rejected));
            continue;
        }
        replay.commit();
        collect::CandidateExplicitTemplateArguments entry;
        entry.template_entity = candidate->entity;
        entry.arguments = std::move(replayed_arguments);
        candidate_arguments.push_back(std::move(entry));
        if (!retained_candidate ||
            candidate->entity == requested_info.entity) {
            retained_candidate = candidate;
        }
    }
    restore_parser_checkpoint(argument_begin);
    if (retained_candidate) {
        if (selected_info) {
            *selected_info = retained_candidate;
        }
        bool parsed =
            parse_candidate_neutral_template_argument_list_with_request(
                *retained_candidate, arguments, loc);
        if (parsed) {
            auto retained = std::find_if(
                candidate_arguments.begin(),
                candidate_arguments.end(),
                [&](const collect::CandidateExplicitTemplateArguments&
                        entry) {
                    return entry.template_entity ==
                        retained_candidate->entity;
                });
            if (retained != candidate_arguments.end()) {
                retained->arguments = arguments;
            }
        }
        return parsed;
    }

    const collect::Session::TemplateInfo* diagnostic_candidate =
        *std::find_if(
            normalized_candidates.begin(),
            normalized_candidates.end(),
            [&](const collect::Session::TemplateInfo* candidate) {
                return candidate &&
                    has_class_template_placeholder(*candidate);
            });
    if (selected_info) {
        *selected_info = diagnostic_candidate;
    }
    return parse_candidate_neutral_template_argument_list_with_request(
        *diagnostic_candidate, arguments, loc);
}

bool Parser::parse_and_canonicalize_template_argument_list(
    const collect::Session::TemplateInfo& info,
    std::vector<collect::Session::TemplateArgument>& arguments,
    SrcLoc loc,
    uint64_t* point_lookup_generation) {
    TemplateArgumentListParsingRequest request =
        begin_template_argument_list_parsing_request(
            info,
            loc,
            point_lookup_generation ? *point_lookup_generation : 0);
    if (!request.active()) {
        (void)parse_dependent_expression_template_argument_list(loc);
        return false;
    }
    if (point_lookup_generation) {
        *point_lookup_generation = request.point_lookup_generation();
    }
    if (!parse_template_argument_list(info, arguments, loc)) {
        return false;
    }
    return canonicalize_template_arguments(info,
                                           arguments,
                                           loc,
                                           point_lookup_generation);
}

bool Parser::build_type_constraint_concept_arguments(
    const collect::Session::TemplateInfo& concept_info,
    const collect::Session::TemplateArgument& constrained_argument,
    const std::vector<collect::Session::TemplateArgument>& tail_arguments,
    SrcLoc loc,
    std::vector<collect::Session::TemplateArgument>& concept_arguments,
    uint64_t* point_lookup_generation) {
    concept_arguments.clear();
    concept_arguments.reserve(tail_arguments.size() + 1);
    concept_arguments.push_back(constrained_argument);
    concept_arguments.insert(concept_arguments.end(),
                             tail_arguments.begin(),
                             tail_arguments.end());
    return canonicalize_template_arguments(concept_info,
                                           concept_arguments,
                                           loc,
                                           point_lookup_generation);
}

void Parser::configure_pattern_instantiation_callbacks(
    collect::Session::PatternInstantiationCallbacks& callbacks,
    SrcLoc loc) {
    callbacks.replay_outcome =
        collect_session_.current_template_replay_outcome();
    callbacks.instantiate_type_template =
        [this, loc](
            cir::EntityId template_entity,
            std::vector<collect::Session::TemplateArgument> args,
            uint64_t point_lookup_generation,
            bool materialize_type_template_definition,
            collect::Session::TemplateArgumentCompletionMode completion_mode)
        -> cir::TypeRef {
        const collect::Session::TemplateInfo* target =
            collect_session_.template_info(template_entity);
        if (!target) {
            return {};
        }
        cir::EntityId record =
            instantiate_template_with_args(*target,
                                           std::move(args),
                                           loc,
                                           point_lookup_generation,
                                           false,
                                           false,
                                           materialize_type_template_definition,
                                           /*record_point_of_instantiation=*/
                                               true,
                                           completion_mode);
        if (!record.valid()) {
            return {};
        }
        const cir::Entity& entity =
            collect_session_.file().entity(record);
        return {entity.type, entity.qualifiers, entity.memory_space};
    };
    callbacks.instantiate_value_entity =
        [this, loc, &callbacks](
            cir::EntityId template_entity,
            std::vector<collect::Session::TemplateArgument> args)
        -> cir::EntityId {
        const collect::Session::TemplateInfo* target =
            collect_session_.template_info(template_entity);
        if (!target || !target->is_variable_template) {
            return {};
        }
        return instantiate_template_with_args(
            *target,
            std::move(args),
            loc,
            callbacks.point_lookup_generation);
    };
    callbacks.instantiate_value =
        [this, loc, &callbacks](
            cir::EntityId template_entity,
            std::vector<collect::Session::TemplateArgument> args)
        -> std::optional<collect::Session::TemplateArgument> {
        const collect::Session::TemplateInfo* target =
            collect_session_.template_info(template_entity);
        if (!target || !target->is_variable_template) {
            return std::nullopt;
        }
        cir::EntityId entity = instantiate_template_with_args(
            *target,
            std::move(args),
            loc,
            callbacks.point_lookup_generation);
        if (!entity.valid() || !collect_session_.file().valid(entity)) {
            return std::nullopt;
        }
        const cir::Entity& record = collect_session_.file().entity(entity);
        collect::ExprResult reference = collect_session_.make_entity_reference(
            entity,
            record.name.valid()
                ? collect_session_.file().name(record.name)
                : std::string_view("<variable-template>"),
            loc,
            /*qualified_name=*/true);
        collect::Session::TemplateValueConstant constant;
        if (!collect_session_.evaluate_template_value_constant(
                std::move(reference),
                record.type,
                constant,
                loc)) {
            return std::nullopt;
        }
        collect::Session::TemplateArgument value;
        if (!collect_session_.build_template_value_argument(
                record.type,
                constant,
                value)) {
            return std::nullopt;
        }
        return value;
    };
    callbacks.evaluate_concept_id =
        [this, loc](
            cir::EntityId concept_entity,
            std::vector<collect::Session::TemplateArgument> args,
            uint64_t point_lookup_generation)
        -> collect::Session::ConceptValueEvaluationStatus {
        using Status =
            collect::Session::ConceptValueEvaluationStatus;
        const collect::Session::TemplateInfo* target =
            collect_session_.template_info(concept_entity);
        if (!target || !target->is_concept) {
            return Status::Invalid;
        }
        collect::ExprResult result =
            evaluate_concept_id_expression(*target,
                                           std::move(args),
                                           loc,
                                           /*qualified_name=*/true,
                                           nullptr,
                                           point_lookup_generation);
        if (result.has_error) {
            return Status::Invalid;
        }
        if (collect_session_.expr_is_dependent(result)) {
            return Status::StillDependent;
        }
        collect::Session::TemplateValueConstant constant;
        cir::TypeId bool_type =
            collect_session_.file().builtin_type(
                cir::BuiltinTypeKind::Bool);
        if (!collect_session_.evaluate_template_value_constant(
                std::move(result),
                bool_type,
                constant,
                loc) ||
            (constant.kind != cir::TemplateValueKind::Integer &&
             constant.kind != cir::TemplateValueKind::Boolean)) {
            return Status::Invalid;
        }
        return !constant.integer_value.is_zero() ? Status::Satisfied
                                   : Status::Unsatisfied;
    };
}

bool Parser::canonicalize_template_arguments(
    const collect::Session::TemplateInfo& info,
    std::vector<collect::Session::TemplateArgument>& arguments,
    SrcLoc loc,
    uint64_t* point_lookup_generation,
    collect::Session::TemplateArgumentCompletionMode completion_mode) {
    bool has_deferred_pack_expansion = false;
    for (const collect::Session::TemplateArgument& argument : arguments) {
        if (argument.expands_parameter_pack &&
            collect_session_.template_argument_names_parameter_pack(argument)) {
            has_deferred_pack_expansion = true;
            break;
        }
    }
    if (has_deferred_pack_expansion) {

        return true;
    }

    collect::Session::TemplateArgumentBindings bindings;
    collect::Session::TemplateArgumentBindingFailure binding_failure;
    collect::Session::PatternInstantiationCallbacks callbacks;
    if (point_lookup_generation) {
        callbacks.point_lookup_generation = *point_lookup_generation;
    }
    configure_pattern_instantiation_callbacks(callbacks, loc);
    if (!collect_session_.bind_explicit_template_arguments_prefix_to_parameters(
            info.parameters, arguments, bindings, &binding_failure) ||
        !collect_session_.complete_template_argument_bindings_with_defaults(
            info,
            bindings,
            &binding_failure,
            &callbacks,
            loc,
            completion_mode)) {
        if (binding_failure.kind ==
            collect::Session::TemplateArgumentBindingFailureKind::
                InstantiationDepth) {
            return false;
        }
        if (completion_mode ==
            collect::Session::TemplateArgumentCompletionMode::Required) {
            diagnose(DiagnosticLevel::Error,
                     format_template_argument_binding_failure(
                         info, binding_failure),
                     loc);
        }
        return false;
    }
    if (point_lookup_generation) {
        *point_lookup_generation = callbacks.point_lookup_generation;
    }
    arguments = collect_session_.flatten_template_argument_bindings(bindings);
    return true;
}

std::string Parser::format_template_argument_binding_failure(
    const collect::Session::TemplateInfo& info,
    const collect::Session::TemplateArgumentBindingFailure& failure) const {
    using Kind =
        collect::Session::TemplateArgumentBindingFailureKind;
    std::string prefix =
        "wrong number of template arguments for '" + info.name + "'";
    if (failure.kind == Kind::TooManyArguments) {
        std::string expected = "at most " +
            std::to_string(failure.maximum_argument_count);
        if (failure.maximum_argument_count !=
                collect::Session::TemplateArgumentBindingFailure::no_index &&
            failure.minimum_argument_count ==
                failure.maximum_argument_count) {
            expected = std::to_string(failure.maximum_argument_count);
        }
        return prefix + ": too many (expected " + expected + ", got " +
               std::to_string(failure.supplied_argument_count) + ")";
    }
    if (failure.kind == Kind::MissingRequiredArgument) {
        std::string expected =
            "at least " + std::to_string(failure.minimum_argument_count);
        if (failure.maximum_argument_count !=
                collect::Session::TemplateArgumentBindingFailure::no_index &&
            failure.minimum_argument_count ==
                failure.maximum_argument_count) {
            expected = std::to_string(failure.minimum_argument_count);
        }
        return prefix + ": too few (expected " + expected + ", got " +
               std::to_string(failure.supplied_argument_count) + ")";
    }
    if (failure.kind == Kind::ArgumentKindMismatch) {
        return format_template_argument_kind_mismatch(
            failure.parameter_index,
            failure.argument_index,
            failure.expected_parameter_kind,
            failure.actual_argument_kind);
    }
    if (failure.detail && !failure.detail->empty()) {
        return *failure.detail;
    }
    using Reason =
        collect::Session::TemplateArgumentBindingFailureReason;
    switch (failure.reason) {
        case Reason::None:
            break;
        case Reason::InternalBindingCountMismatch:
            return "internal error: template binding count does not match parameter count";
        case Reason::MultipleParameterPacksUnsupported:
            return "multiple template parameter packs are not supported by the current argument binder";
        case Reason::PackExpansionForNonPackUnsupported:
            return "template argument pack expansion for non-pack parameters is not supported yet";
        case Reason::PartialNonTrailingPackBinding:
            return "explicit template arguments cannot partially bind a non-trailing parameter pack";
        case Reason::TypeParameterRequiresTypeArgument:
            return "type template parameter requires a type argument";
        case Reason::NonTypeParameterRequiresValueArgument:
            return "non-type template parameter requires a value argument";
        case Reason::NonTypeArgumentNarrowing:
            return "non-type template argument conversion is narrowing";
        case Reason::TemplateParameterRequiresTemplateArgument:
            return "template template parameter requires a template argument";
        case Reason::TemplateArgumentMustNameTemplate:
            return "template template argument must name a template";
        case Reason::TemplateArgumentMustNameConceptTemplate:
            return "template template argument must name a concept template";
        case Reason::TemplateArgumentMustNameClassOrAliasTemplate:
            return "template template argument must name a class or alias template";
        case Reason::TemplateTemplateParameterListMismatch:
            return "template template argument parameter list does not match";
        case Reason::DependentDefaultArgumentSubstitution:
            return "dependent default template argument could not be substituted";
    }
    return prefix;
}

std::string Parser::format_template_argument_kind_mismatch(
    uint32_t parameter_index,
    uint32_t argument_index,
    collect::Session::TemplateParameterKind expected_kind,
    cir::TemplateArgumentKind actual_kind) const {
    using Failure =
        collect::Session::TemplateArgumentBindingFailure;
    if (parameter_index == Failure::no_index ||
        argument_index == Failure::no_index) {
        return "template argument kind does not match its template parameter";
    }

    auto argument_kind_spelling = [](cir::TemplateArgumentKind kind) {
        switch (kind) {
            case cir::TemplateArgumentKind::Type:
                return "a type";
            case cir::TemplateArgumentKind::Value:
                return "a value";
            case cir::TemplateArgumentKind::Template:
                return "a template";
        }
        return "an argument of the wrong kind";
    };
    auto required_kind_spelling =
        [](collect::Session::TemplateParameterKind kind) {
        switch (kind) {
            case collect::Session::TemplateParameterKind::Type:
                return "a type argument";
            case collect::Session::TemplateParameterKind::NonType:
                return "a constant argument";
            case collect::Session::TemplateParameterKind::Template:
                return "a template argument";
        }
        return "an argument of the matching kind";
    };

    return "template argument " + std::to_string(argument_index + 1) +
           " is " + argument_kind_spelling(actual_kind) +
           ", but template parameter " +
           std::to_string(parameter_index + 1) + " requires " +
           required_kind_spelling(expected_kind);
}

bool Parser::template_arguments_are_dependent(
    const std::vector<collect::Session::TemplateArgument>& arguments) {
    for (const collect::Session::TemplateArgument& argument : arguments) {
        if (argument.kind == cir::TemplateArgumentKind::Type &&
            (argument.is_dependent ||
             collect_session_.is_dependent_type(argument.type.type) ||
             collect_session_
                 .type_contains_dependent_alias_specialization(
                     argument.type.type))) {
            return true;
        }
        if (argument.kind == cir::TemplateArgumentKind::Value &&
            (argument.is_dependent ||
             collect_session_.type_contains_type_param(
                 argument.value_type.type) ||
             collect_session_
                 .type_contains_dependent_alias_specialization(
                     argument.value_type.type) ||
             collect_session_.type_contains_type_param(
                 argument.dependent_value_qualifier.type) ||
             collect_session_
                 .type_contains_dependent_alias_specialization(
                     argument.dependent_value_qualifier.type))) {
            return true;
        }
        if (argument.kind == cir::TemplateArgumentKind::Template &&
            argument.is_dependent) {
            return true;
        }
    }
    return false;
}

bool Parser::evaluate_introduced_type_constraint(
    const collect::Session::TemplateInfo& info,
    const collect::Session::TemplateInfo::IntroducedConstraint& constraint,
    const std::vector<collect::Session::TemplateArgument>& arguments,
    SrcLoc loc,
    uint64_t point_lookup_generation,
    std::optional<bool>& value,
    bool& substitution_failure) {
    value.reset();
    substitution_failure = false;
    SrcLoc constraint_loc = constraint.loc.isInvalid() ? loc : constraint.loc;

    const collect::Session::TemplateInfo* concept_info =
        collect_session_.template_info(constraint.type_constraint_concept);
    if (!concept_info || !concept_info->is_concept) {
        diagnose(DiagnosticLevel::Error,
                 "type-constraint concept is unavailable",
                 constraint_loc);
        return false;
    }
    std::optional<collect::Session::TemplateArgumentBindings>
        argument_bindings = constraint_argument_bindings_override_
        ? std::optional<collect::Session::TemplateArgumentBindings>(
              *constraint_argument_bindings_override_)
        : canonical_template_argument_bindings(collect_session_,
                                               info.parameters,
                                               arguments);
    if (!argument_bindings.has_value() ||
        constraint.constrained_parameter_index >=
            argument_bindings->size()) {
        diagnose(DiagnosticLevel::Error,
                 "type-constraint has no matching type parameter argument",
                 constraint_loc);
        return false;
    }
    const bool constrained_parameter_pack =
        constraint.constrained_parameter_index < info.parameters.size() &&
        info.parameters[constraint.constrained_parameter_index]
            .is_parameter_pack;
    const bool constrained_placeholder_value =
        constraint.constrained_parameter_index < info.parameters.size() &&
        info.parameters[constraint.constrained_parameter_index].kind ==
            collect::Session::TemplateParameterKind::NonType &&
        collect_session_.contains_auto_type(
            info.parameters[constraint.constrained_parameter_index]
                .non_type_type);
    const collect::Session::TemplateArgumentBinding& constrained_binding =
        (*argument_bindings)[constraint.constrained_parameter_index];
    if (!constrained_parameter_pack &&
        (!constrained_binding.is_single() ||
         constrained_binding.arguments.size() != 1 ||
         (constrained_placeholder_value
              ? constrained_binding.arguments.front().kind !=
                    cir::TemplateArgumentKind::Value
              : constrained_binding.arguments.front().kind !=
                    cir::TemplateArgumentKind::Type))) {
        diagnose(DiagnosticLevel::Error,
                 "type-constraint has no matching type parameter argument",
                 constraint_loc);
        return false;
    }
    if (constrained_parameter_pack && !constrained_binding.is_pack()) {
        diagnose(DiagnosticLevel::Error,
                 "type-constraint has no matching type parameter pack argument",
                 constraint_loc);
        return false;
    }

    collect::Session::PatternInstantiationCallbacks callbacks;
    callbacks.point_lookup_generation = point_lookup_generation;
    configure_pattern_instantiation_callbacks(callbacks, constraint_loc);

    auto substitute_argument =
        [&](collect::Session::TemplateArgument& argument) -> bool {
        std::string substitution_error;
        if (argument.kind == cir::TemplateArgumentKind::Type &&
            argument.type.type.valid() &&
            collect_session_.type_contains_type_param(argument.type.type)) {
            cir::TypeId substituted =
                collect_session_.substitute_pattern_type(argument.type.type,
                                                         *argument_bindings,
                                                         callbacks);
            if (!substituted.valid()) {
                substitution_failure = true;
                return false;
            }
            argument.type =
                collect_session_.type_ref(substituted,
                                          argument.type.qualifiers,
                                          argument.type.memory_space);
            argument.is_dependent =
                collect_session_.is_dependent_type(substituted);
        } else if (argument.kind == cir::TemplateArgumentKind::Value) {
            if (!collect_session_.substitute_template_value_argument(
                    argument,
                    *argument_bindings,
                    callbacks,
                    &substitution_error)) {
                substitution_failure = true;
                return false;
            }
        } else if (argument.kind == cir::TemplateArgumentKind::Template) {
            if (!collect_session_.substitute_template_template_argument(
                    argument,
                    *argument_bindings,
                    callbacks,
                    &substitution_error)) {
                substitution_failure = true;
                return false;
            }
        }
        return true;
    };

    auto evaluate_for_constrained_argument =
        [&](const collect::Session::TemplateArgument& bound_argument,
            std::optional<bool>& element_value) -> bool {
        element_value.reset();
        collect::Session::TemplateArgument constrained_argument =
            bound_argument;
        if (constrained_placeholder_value) {
            if (bound_argument.kind != cir::TemplateArgumentKind::Value ||
                !bound_argument.value_type.type.valid()) {
                substitution_failure = true;
                return true;
            }
            constrained_argument = {};
            constrained_argument.kind = cir::TemplateArgumentKind::Type;
            constrained_argument.type = bound_argument.value_type;
            constrained_argument.is_dependent =
                collect_session_.is_dependent_type(
                    bound_argument.value_type.type);
        }
        std::vector<collect::Session::TemplateArgument> tail_arguments;
        tail_arguments.reserve(constraint.type_constraint_arguments.size());
        for (collect::Session::TemplateArgument argument :
             constraint.type_constraint_arguments) {
            if (!substitute_argument(argument)) {
                return true;
            }
            tail_arguments.push_back(std::move(argument));
        }

        std::vector<collect::Session::TemplateArgument> concept_arguments;
        if (!build_type_constraint_concept_arguments(
                *concept_info,
                constrained_argument,
                tail_arguments,
                constraint_loc,
                concept_arguments,
                &callbacks.point_lookup_generation)) {
            return false;
        }

        collect_session_.begin_pattern_collection();
        uint64_t taint_before = collect_session_.pattern_taint();
        collect::ExprResult concept_result =
            evaluate_concept_id_expression(*concept_info,
                                           std::move(concept_arguments),
                                           constraint_loc,
                                           /*qualified_name=*/false);
        bool value_dependent =
            collect_session_.pattern_taint() != taint_before ||
            collect_session_.expr_is_dependent(concept_result) ||
            concept_result.references_template_value_parameter;
        bool valid = !concept_result.has_error;
        if (valid) {
            valid = collect_session_.evaluate_constraint_expression(
                std::move(concept_result),
                value_dependent,
                element_value,
                constraint_loc);
        }
        (void)collect_session_.finish_pattern_collection();
        return valid;
    };

    if (!constrained_parameter_pack) {
        return evaluate_for_constrained_argument(
            constrained_binding.arguments.front(),
            value);
    }

    bool saw_dependent_element = false;
    for (const collect::Session::TemplateArgument& argument :
         constrained_binding.arguments) {
        cir::TemplateArgumentKind expected_kind =
            constrained_placeholder_value
                ? cir::TemplateArgumentKind::Value
                : cir::TemplateArgumentKind::Type;
        if (argument.kind != expected_kind) {
            diagnose(DiagnosticLevel::Error,
                     "type-constraint has no matching type parameter pack argument",
                     constraint_loc);
            return false;
        }
        std::optional<bool> element_value;
        if (!evaluate_for_constrained_argument(argument,
                                               element_value)) {
            return false;
        }
        if (substitution_failure) {
            return true;
        }
        if (element_value.has_value()) {
            if (!*element_value) {
                value = false;
                return true;
            }
        } else {
            saw_dependent_element = true;
        }
    }
    if (!saw_dependent_element) {
        value = true;
    }
    return true;
}

Parser::NormalizedConstraintCheckResult
Parser::evaluate_normalized_direct_atom(
    const collect::Session::TemplateInfo& info,
    const collect::Session::NormalizedConstraintNode& node,
    SrcLoc loc) {
    if (node.kind != collect::Session::NormalizedConstraintKind::Atomic ||
        node.atom.appearance_owner.valid() ||
        !node.atom.parameter_mapping.empty() ||
        node.atom.expression_begin >= node.atom.expression_end) {
        return NormalizedConstraintCheckResult::Unsupported;
    }
    struct ConstraintSubstitutionFailureScope {
        Parser* parser = nullptr;
        size_t saved_depth = 0;
        bool saved_failure = false;

        explicit ConstraintSubstitutionFailureScope(Parser& parser)
            : parser(&parser),
              saved_depth(parser.constraint_substitution_failure_depth_),
              saved_failure(parser.constraint_substitution_failure_) {
            parser.constraint_substitution_failure_depth_ = saved_depth + 1;
            parser.constraint_substitution_failure_ = false;
        }

        bool failed() const {
            return parser && parser->constraint_substitution_failure_;
        }

        void restore() {
            if (!parser) {
                return;
            }
            parser->constraint_substitution_failure_depth_ = saved_depth;
            parser->constraint_substitution_failure_ = saved_failure;
            parser = nullptr;
        }

        ~ConstraintSubstitutionFailureScope() {
            restore();
        }
    } substitution_failure_scope(*this);

    ParserCheckpoint replay_checkpoint = capture_parser_checkpoint();
    size_t error_watermark = collect_session_.file().errors().size();
    size_t saved_cursor = cursor_;
    size_t saved_last_end = last_consumed_raw_end_;
    size_t saved_constraint_replay_end = constraint_expression_replay_end_;
    std::vector<size_t> saved_template_argument_expression_begins =
        template_argument_expression_begins_;
    collect_session_.begin_speculative_parse();

    seek_raw_index(node.atom.expression_begin);

    pending_template_closes_ = 0;
    template_argument_expression_begins_.clear();
    constraint_expression_replay_end_ = node.atom.expression_end;
    size_t parsed_begin = 0;
    size_t parsed_end = 0;
    std::optional<bool> value;
    bool valid = parse_and_validate_constraint_expression(
        loc_for_index(node.atom.expression_begin),
        parsed_begin,
        parsed_end,
        &value);
    if (valid && (parsed_begin != node.atom.expression_begin ||
                  parsed_end != node.atom.expression_end)) {
        diagnose(DiagnosticLevel::Error,
                 "unexpected tokens in atomic constraint-expression",
                 current_loc());
        valid = false;
    }

    bool substitution_failure = substitution_failure_scope.failed();
    std::vector<std::pair<SrcLoc, std::string>> captured_errors(
        collect_session_.file().errors().begin() + error_watermark,
        collect_session_.file().errors().end());
    std::vector<Diagnostic> captured_parser_diagnostics(
        diagnostics_.begin() + replay_checkpoint.diagnostics_size,
        diagnostics_.end());
    collect_session_.rollback_speculative_parse();
    restore_parser_checkpoint(replay_checkpoint);
    cursor_ = saved_cursor;
    last_consumed_raw_end_ = saved_last_end;
    constraint_expression_replay_end_ = saved_constraint_replay_end;
    template_argument_expression_begins_ =
        std::move(saved_template_argument_expression_begins);
    substitution_failure_scope.restore();

    if (substitution_failure) {
        return NormalizedConstraintCheckResult::Unsatisfied;
    }
    if (!valid) {
        for (auto& [error_loc, message] : captured_errors) {
            collect_session_.file().add_error(std::move(message), error_loc);
        }
        diagnostics_.insert(diagnostics_.end(),
                            captured_parser_diagnostics.begin(),
                            captured_parser_diagnostics.end());
        return NormalizedConstraintCheckResult::Invalid;
    }
    if (value.has_value() && !*value) {
        return NormalizedConstraintCheckResult::Unsatisfied;
    }
    return NormalizedConstraintCheckResult::Satisfied;
}

Parser::NormalizedConstraintCheckResult
Parser::evaluate_normalized_concept_owned_atom(
    const collect::Session::TemplateInfo& info,
    const std::vector<collect::Session::TemplateArgument>& arguments,
    const collect::Session::NormalizedConstraintNode& node,
    SrcLoc loc,
    uint64_t point_lookup_generation) {
    if (node.kind != collect::Session::NormalizedConstraintKind::Atomic ||
        !node.atom.appearance_owner.valid() ||
        node.atom.expression_begin >= node.atom.expression_end) {
        return NormalizedConstraintCheckResult::Unsupported;
    }
    std::optional<collect::Session::TemplateArgumentBindings>
        argument_bindings = constraint_argument_bindings_override_
        ? std::optional<collect::Session::TemplateArgumentBindings>(
              *constraint_argument_bindings_override_)
        : canonical_template_argument_bindings(collect_session_,
                                               info.parameters,
                                               arguments);
    if (!argument_bindings.has_value()) {
        return NormalizedConstraintCheckResult::Unsatisfied;
    }

    const collect::Session::TemplateInfo* concept_info =
        collect_session_.template_info(node.atom.appearance_owner);
    if (!concept_info || !concept_info->is_concept ||
        !concept_info->has_definition) {
        return NormalizedConstraintCheckResult::Unsupported;
    }

    auto parameter_key =
        [](const collect::Session::TemplateParameter& parameter) {
        collect::Session::ConstraintParameterMapping key;
        key.parameter_kind = parameter.kind;
        key.parameter_depth = parameter.depth;
        key.parameter_index = parameter.index;
        key.parameter_entity = parameter.entity;
        key.parameter_template_template_kind =
            parameter.template_template_parameter_kind;
        key.parameter_is_pack = parameter.is_parameter_pack;
        return key;
    };
    auto mapping_matches_parameter =
        [](const collect::Session::ConstraintParameterMapping& mapping,
           const collect::Session::ConstraintParameterMapping& key) {
        if (mapping.same_parameter_as(key)) {
            return true;
        }
        if (mapping.parameter_entity.valid() && key.parameter_entity.valid()) {
            return false;
        }
        return mapping.parameter_kind == key.parameter_kind &&
               mapping.parameter_depth == key.parameter_depth &&
               mapping.parameter_index == key.parameter_index &&
               (mapping.parameter_kind !=
                    collect::Session::TemplateParameterKind::Template ||
                mapping.parameter_template_template_kind ==
                    key.parameter_template_template_kind);
    };

    std::vector<collect::Session::TemplateArgument> concept_arguments;
    concept_arguments.reserve(concept_info->parameters.size());
    for (const collect::Session::TemplateParameter& parameter :
         concept_info->parameters) {
        if (parameter.is_parameter_pack) {
            return NormalizedConstraintCheckResult::Unsupported;
        }
        collect::Session::ConstraintParameterMapping key =
            parameter_key(parameter);
        const collect::Session::ConstraintParameterMapping* mapping = nullptr;
        for (const collect::Session::ConstraintParameterMapping& candidate :
             node.atom.parameter_mapping) {
            if (mapping_matches_parameter(candidate, key)) {
                mapping = &candidate;
                break;
            }
        }
        if (!mapping || mapping->argument_pack.has_value()) {
            return NormalizedConstraintCheckResult::Unsupported;
        }
        concept_arguments.push_back(mapping->argument);
    }

    collect::Session::PatternInstantiationCallbacks callbacks;
    callbacks.point_lookup_generation = point_lookup_generation;
    configure_pattern_instantiation_callbacks(callbacks, loc);

    auto substitute_argument =
        [&](collect::Session::TemplateArgument& argument) -> bool {
        std::string substitution_error;
        switch (argument.kind) {
            case cir::TemplateArgumentKind::Type: {
                if (argument.value_param_index !=
                    cir::ArrayTypePayload::no_extent_param &&
                    argument.value_param_index < argument_bindings->size()) {
                    const collect::Session::TemplateArgumentBinding& binding =
                        (*argument_bindings)[argument.value_param_index];
                    if (binding.is_single() &&
                        binding.arguments.size() == 1 &&
                        binding.arguments.front().kind ==
                            cir::TemplateArgumentKind::Value &&
                        binding.arguments.front().value_type.valid()) {
                        argument.type =
                            binding.arguments.front().value_type;
                        argument.value_param_index =
                            cir::ArrayTypePayload::no_extent_param;
                        argument.is_dependent =
                            collect_session_.is_dependent_type(
                                argument.type.type);
                        return true;
                    }
                    return false;
                }
                if (!argument.type.type.valid() ||
                    !collect_session_.type_contains_type_param(
                        argument.type.type)) {
                    return true;
                }
                cir::TypeId substituted =
                    collect_session_.substitute_pattern_type(
                        argument.type.type,
                        *argument_bindings,
                        callbacks);
                if (!substituted.valid()) {
                    return false;
                }
                argument.type =
                    collect_session_.type_ref(substituted,
                                              argument.type.qualifiers,
                                              argument.type.memory_space);
                argument.is_dependent =
                    collect_session_.is_dependent_type(substituted);
                return true;
            }
            case cir::TemplateArgumentKind::Value:
                return collect_session_.substitute_template_value_argument(
                    argument,
                    *argument_bindings,
                    callbacks,
                    &substitution_error);
            case cir::TemplateArgumentKind::Template:
                return collect_session_.substitute_template_template_argument(
                    argument,
                    *argument_bindings,
                    callbacks,
                    &substitution_error);
        }
        return true;
    };

    for (collect::Session::TemplateArgument& argument : concept_arguments) {
        if (!substitute_argument(argument)) {
            return NormalizedConstraintCheckResult::Unsatisfied;
        }
    }
    for (const collect::Session::TemplateArgument& argument :
         concept_arguments) {
        if (argument.kind != cir::TemplateArgumentKind::Type ||
            !argument.type.type.valid()) {
            continue;
        }
        cir::TypeId resolved =
            collect_session_.file().resolved_type(argument.type.type);
        if (!collect_session_.file().valid(resolved) ||
            collect_session_.file().type(resolved).kind !=
                cir::TypeKind::Record) {
            continue;
        }
        const cir::RecordFacts* facts =
            collect_session_.file().record_facts_for_type(resolved);
        if (facts && facts->is_incomplete) {

            return NormalizedConstraintCheckResult::Unsupported;
        }
    }

    std::optional<collect::Session::TemplateArgumentBindings>
        concept_argument_bindings =
            canonical_template_argument_bindings(
                collect_session_,
                concept_info->parameters,
                concept_arguments);
    if (!concept_argument_bindings.has_value()) {
        return NormalizedConstraintCheckResult::Unsatisfied;
    }
    using SatisfactionKind =
        collect::Session::ConstraintSatisfactionRequestKind;
    using SatisfactionResult =
        collect::Session::ConstraintSatisfactionResult;
    using SatisfactionState =
        collect::Session::ConstraintSatisfactionScope::State;
    collect::Session::ConstraintSatisfactionScope satisfaction_scope =
        collect_session_.begin_constraint_satisfaction(
            SatisfactionKind::AtomicConstraint,
            concept_info->entity,
            *concept_argument_bindings,
            point_lookup_generation,
            node.atom.expression_begin,
            node.atom.expression_end);
    if (satisfaction_scope.state == SatisfactionState::Cached) {
        return *satisfaction_scope.cached_result ==
                SatisfactionResult::Satisfied
            ? NormalizedConstraintCheckResult::Satisfied
            : NormalizedConstraintCheckResult::Unsatisfied;
    }
    if (satisfaction_scope.state == SatisfactionState::Recursive) {
        diagnose(DiagnosticLevel::Error,
                 "constraint satisfaction depends on itself",
                 loc);
        return NormalizedConstraintCheckResult::Invalid;
    }
    struct AtomicSatisfactionExit {
        collect::Session* session = nullptr;
        collect::Session::ConstraintSatisfactionScope scope;
        bool complete = false;

        ~AtomicSatisfactionExit() {
            if (session && !complete) {
                session->abandon_constraint_satisfaction(std::move(scope));
            }
        }

        void finish(SatisfactionResult result) {
            session->finish_constraint_satisfaction(std::move(scope), result);
            complete = true;
        }
    } satisfaction_exit{&collect_session_, std::move(satisfaction_scope)};

    ParserCheckpoint replay_checkpoint = capture_parser_checkpoint();
    size_t error_watermark = collect_session_.file().errors().size();
    size_t saved_cursor = cursor_;
    size_t saved_last_end = last_consumed_raw_end_;
    size_t saved_constraint_replay_end = constraint_expression_replay_end_;
    std::vector<size_t> saved_template_argument_expression_begins =
        template_argument_expression_begins_;
    collect_session_.begin_speculative_parse();

    uint64_t concept_point_lookup_generation = point_lookup_generation;
    bool canonicalized =
        canonicalize_template_arguments(*concept_info,
                                        concept_arguments,
                                        loc,
                                        &concept_point_lookup_generation);
    if (canonicalized && template_arguments_are_dependent(concept_arguments)) {
        collect_session_.rollback_speculative_parse();
        restore_parser_checkpoint(replay_checkpoint);
        cursor_ = saved_cursor;
        last_consumed_raw_end_ = saved_last_end;
        constraint_expression_replay_end_ = saved_constraint_replay_end;
        template_argument_expression_begins_ =
            std::move(saved_template_argument_expression_begins);
        return NormalizedConstraintCheckResult::Unsupported;
    }

    collect::Session::InstantiationScope scope;
    if (canonicalized) {
        scope = collect_session_.begin_template_instantiation(
            *concept_info,
            concept_arguments,
            loc,
            concept_point_lookup_generation);
    }

    struct ConstraintSubstitutionFailureScope {
        Parser* parser = nullptr;
        size_t saved_depth = 0;
        bool saved_failure = false;

        explicit ConstraintSubstitutionFailureScope(Parser& parser)
            : parser(&parser),
              saved_depth(parser.constraint_substitution_failure_depth_),
              saved_failure(parser.constraint_substitution_failure_) {
            parser.constraint_substitution_failure_depth_ = saved_depth + 1;
            parser.constraint_substitution_failure_ = false;
        }

        bool failed() const {
            return parser && parser->constraint_substitution_failure_;
        }

        void restore() {
            if (!parser) {
                return;
            }
            parser->constraint_substitution_failure_depth_ = saved_depth;
            parser->constraint_substitution_failure_ = saved_failure;
            parser = nullptr;
        }

        ~ConstraintSubstitutionFailureScope() {
            restore();
        }
    } substitution_failure_scope(*this);

    bool valid = canonicalized && scope.active;
    seek_raw_index(node.atom.expression_begin);

    pending_template_closes_ = 0;
    template_argument_expression_begins_.clear();
    constraint_expression_replay_end_ = node.atom.expression_end;
    size_t parsed_begin = 0;
    size_t parsed_end = 0;
    std::optional<bool> value;
    if (valid) {
        valid = parse_and_validate_constraint_expression(
            loc_for_index(node.atom.expression_begin),
            parsed_begin,
            parsed_end,
            &value);
        if (valid && (parsed_begin != node.atom.expression_begin ||
                      parsed_end != node.atom.expression_end)) {
            diagnose(DiagnosticLevel::Error,
                     "unexpected tokens in atomic constraint-expression",
                     current_loc());
            valid = false;
        }
    }

    bool substitution_failure = substitution_failure_scope.failed();
    if (scope.active) {
        collect_session_.finish_template_instantiation(std::move(scope));
    }
    std::vector<std::pair<SrcLoc, std::string>> captured_errors(
        collect_session_.file().errors().begin() + error_watermark,
        collect_session_.file().errors().end());
    std::vector<Diagnostic> captured_parser_diagnostics(
        diagnostics_.begin() + replay_checkpoint.diagnostics_size,
        diagnostics_.end());
    collect_session_.rollback_speculative_parse();
    restore_parser_checkpoint(replay_checkpoint);
    cursor_ = saved_cursor;
    last_consumed_raw_end_ = saved_last_end;
    constraint_expression_replay_end_ = saved_constraint_replay_end;
    template_argument_expression_begins_ =
        std::move(saved_template_argument_expression_begins);
    substitution_failure_scope.restore();

    if (substitution_failure || !canonicalized) {
        satisfaction_exit.finish(SatisfactionResult::Unsatisfied);
        return NormalizedConstraintCheckResult::Unsatisfied;
    }
    if (!valid) {
        for (auto& [error_loc, message] : captured_errors) {
            collect_session_.file().add_error(std::move(message), error_loc);
        }
        diagnostics_.insert(diagnostics_.end(),
                            captured_parser_diagnostics.begin(),
                            captured_parser_diagnostics.end());
        satisfaction_exit.finish(SatisfactionResult::Invalid);
        return NormalizedConstraintCheckResult::Invalid;
    }
    if (value.has_value() && !*value) {
        satisfaction_exit.finish(SatisfactionResult::Unsatisfied);
        return NormalizedConstraintCheckResult::Unsatisfied;
    }
    satisfaction_exit.finish(SatisfactionResult::Satisfied);
    return NormalizedConstraintCheckResult::Satisfied;
}

Parser::NormalizedConstraintCheckResult
Parser::evaluate_normalized_concept_dependent_constraint(
    const collect::Session::TemplateInfo& info,
    const std::vector<collect::Session::TemplateArgument>& arguments,
    const collect::Session::NormalizedConstraintNode& node,
    SrcLoc loc,
    uint64_t point_lookup_generation) {
    if (node.kind !=
        collect::Session::NormalizedConstraintKind::ConceptDependent) {
        return NormalizedConstraintCheckResult::Unsupported;
    }
    std::optional<collect::Session::TemplateArgumentBindings>
        argument_bindings = constraint_argument_bindings_override_
        ? std::optional<collect::Session::TemplateArgumentBindings>(
              *constraint_argument_bindings_override_)
        : canonical_template_argument_bindings(collect_session_,
                                               info.parameters,
                                               arguments);
    if (!argument_bindings.has_value()) {
        return NormalizedConstraintCheckResult::Unsatisfied;
    }

    ParserCheckpoint checkpoint = capture_parser_checkpoint();
    size_t error_watermark = collect_session_.file().errors().size();
    collect_session_.begin_speculative_parse();

    collect::Session::NormalizedConstraint substituted_form;
    uint32_t substituted =
        substituted_form.add_concept_dependent(node.atom);
    substituted_form.nodes[substituted].concept_id_entity =
        node.concept_id_entity;
    substituted_form.nodes[substituted].concept_id_template_parameter_index =
        node.concept_id_template_parameter_index;
    substituted_form.nodes[substituted].concept_id_dependent_qualifier =
        node.concept_id_dependent_qualifier;
    substituted_form.nodes[substituted].concept_id_name =
        node.concept_id_name;
    substituted_form.nodes[substituted].concept_id_qualified_name =
        node.concept_id_qualified_name;
    substituted_form.nodes[substituted].concept_id_argument_list_begin =
        node.concept_id_argument_list_begin;
    substituted_form.nodes[substituted].concept_id_argument_list_end =
        node.concept_id_argument_list_end;
    substituted_form.nodes[substituted].concept_id_arguments =
        node.concept_id_arguments;
    substituted_form.root = substituted;

    collect::Session::PatternInstantiationCallbacks callbacks;
    callbacks.point_lookup_generation = point_lookup_generation;
    configure_pattern_instantiation_callbacks(callbacks, loc);
    std::string substitution_error;
    bool substituted_ok =
        collect_session_.compose_constraint_parameter_mappings(
            substituted_form,
            substituted,
            *argument_bindings,
            callbacks,
            &substitution_error);

    auto finish_failed =
        [&](NormalizedConstraintCheckResult result) {
        collect_session_.rollback_speculative_parse();
        restore_parser_checkpoint(checkpoint);
        (void)error_watermark;
        return result;
    };

    if (!substituted_ok) {
        return finish_failed(NormalizedConstraintCheckResult::Unsatisfied);
    }

    const collect::Session::NormalizedConstraintNode& substituted_node =
        substituted_form.nodes[substituted];
    const collect::Session::TemplateInfo* target_concept = nullptr;
    std::vector<collect::Session::TemplateArgument> concept_arguments;
    uint64_t concept_point_lookup_generation =
        callbacks.point_lookup_generation;
    collect::Session::TemplateArgument concept_argument;

    auto entity_is_template_parameter = [&](cir::EntityId entity) {
        return entity.valid() && collect_session_.file().valid(entity) &&
               collect_session_.file().entity(entity).kind ==
                   cir::EntityKind::TemplateParam;
    };

    auto mapping_matches_concept_entity =
        [&](const collect::Session::ConstraintParameterMapping& mapping) {
        if (mapping.parameter_kind !=
            collect::Session::TemplateParameterKind::Template) {
            return false;
        }
        if (substituted_node.concept_id_template_parameter_index !=
            cir::ArrayTypePayload::no_extent_param) {
            return mapping.parameter_index ==
                   substituted_node.concept_id_template_parameter_index;
        }
        if (mapping.parameter_entity.valid() &&
            substituted_node.concept_id_entity.valid()) {
            return mapping.parameter_entity ==
                   substituted_node.concept_id_entity;
        }
        const collect::Session::TemplateInfo* placeholder_info =
            collect_session_.template_info(substituted_node
                                               .concept_id_entity);
        return placeholder_info &&
               mapping.parameter_index ==
                   placeholder_info->template_parameter_index;
    };
    auto concept_placeholder_argument_index = [&]() -> uint32_t {
        if (substituted_node.concept_id_template_parameter_index !=
            cir::ArrayTypePayload::no_extent_param) {
            return substituted_node.concept_id_template_parameter_index;
        }
        const collect::Session::TemplateInfo* placeholder_info =
            collect_session_.template_info(substituted_node
                                               .concept_id_entity);
        if (placeholder_info &&
            placeholder_info->template_parameter_index !=
                cir::ArrayTypePayload::no_extent_param) {
            return placeholder_info->template_parameter_index;
        }
        for (const collect::Session::TemplateParameter& parameter :
             info.parameters) {
            if (parameter.kind !=
                collect::Session::TemplateParameterKind::Template) {
                continue;
            }
            bool same_parameter_entity =
                parameter.entity == substituted_node.concept_id_entity;
            if (same_parameter_entity) {
                return parameter.index;
            }
        }
        return cir::ArrayTypePayload::no_extent_param;
    };

    auto parse_recorded_concept_arguments = [&]() -> bool {
        if (substituted_node.concept_id_argument_list_begin >=
            substituted_node.concept_id_argument_list_end) {
            return false;
        }
        int saved_template_closes = pending_template_closes_;
        seek_raw_index(substituted_node.concept_id_argument_list_begin);
        pending_template_closes_ = 0;
        concept_arguments.clear();
        bool parsed =
            parse_and_canonicalize_template_argument_list(
                *target_concept,
                concept_arguments,
                loc_for_index(
                    substituted_node.concept_id_argument_list_begin),
                &concept_point_lookup_generation);
        bool consumed_recorded_range =
            current_raw_index() ==
                substituted_node.concept_id_argument_list_end;
        pending_template_closes_ = saved_template_closes;
        return parsed && consumed_recorded_range;
    };

    if (substituted_node.concept_id_dependent_qualifier.type.valid()) {
        cir::TypeId qualifier = collect_session_.substitute_pattern_type(
            substituted_node.concept_id_dependent_qualifier.type,
            *argument_bindings,
            callbacks);
        if (!qualifier.valid()) {
            return finish_failed(NormalizedConstraintCheckResult::Unsatisfied);
        }
        if (collect_session_.is_dependent_type(qualifier)) {
            return finish_failed(NormalizedConstraintCheckResult::Unsupported);
        }

        const cir::File& file = collect_session_.file();
        cir::TypeId resolved_qualifier = file.resolved_type(qualifier);
        if (!file.valid(resolved_qualifier) ||
            file.type(resolved_qualifier).kind != cir::TypeKind::Record) {
            return finish_failed(NormalizedConstraintCheckResult::Unsatisfied);
        }
        cir::EntityId record = file.record_entity(resolved_qualifier);
        if (!record.valid() || !file.valid(record) ||
            !file.entity(record).semantic_context.valid() ||
            !substituted_node.concept_id_name.valid()) {
            return finish_failed(NormalizedConstraintCheckResult::Unsatisfied);
        }
        target_concept = collect_session_.template_info_in_context(
            file.entity(record).semantic_context,
            file.name(substituted_node.concept_id_name),
            /*include_parents=*/false);
        if (!target_concept || !target_concept->is_concept) {
            return finish_failed(NormalizedConstraintCheckResult::Unsatisfied);
        }
        if (!parse_recorded_concept_arguments()) {
            return finish_failed(NormalizedConstraintCheckResult::Unsatisfied);
        }
    } else if (substituted_node.concept_id_entity.valid() &&
        !entity_is_template_parameter(substituted_node.concept_id_entity)) {
        target_concept =
            collect_session_.template_info(substituted_node.concept_id_entity);
    } else if (substituted_node.concept_id_entity.valid() ||
               substituted_node.concept_id_template_parameter_index !=
                   cir::ArrayTypePayload::no_extent_param) {
        const collect::Session::ConstraintParameterMapping* mapping = nullptr;
        for (const collect::Session::ConstraintParameterMapping& candidate :
             substituted_node.atom.parameter_mapping) {
            if (mapping_matches_concept_entity(candidate)) {
                mapping = &candidate;
                break;
            }
        }
        if (mapping) {
            if (mapping->argument_pack.has_value()) {
                return finish_failed(
                    NormalizedConstraintCheckResult::Unsupported);
            }
            concept_argument = mapping->argument;
        } else {
            uint32_t argument_index = concept_placeholder_argument_index();
            if (argument_index == cir::ArrayTypePayload::no_extent_param ||
                argument_index >= argument_bindings->size()) {
                return finish_failed(
                    NormalizedConstraintCheckResult::Unsatisfied);
            }
            const collect::Session::TemplateArgumentBinding& binding =
                (*argument_bindings)[argument_index];
            if (!binding.is_single() || binding.arguments.size() != 1) {
                return finish_failed(
                    NormalizedConstraintCheckResult::Unsupported);
            }
            concept_argument = binding.arguments.front();
        }
        if (concept_argument.kind != cir::TemplateArgumentKind::Template) {
            return finish_failed(NormalizedConstraintCheckResult::Unsatisfied);
        }
        if (concept_argument.template_param_index !=
            cir::ArrayTypePayload::no_extent_param) {
            return finish_failed(NormalizedConstraintCheckResult::Unsupported);
        }
        target_concept =
            collect_session_.template_info(concept_argument.template_entity);
    }

    if (!target_concept || !target_concept->is_concept) {
        return finish_failed(NormalizedConstraintCheckResult::Unsatisfied);
    }
    if (!target_concept->constraint_normal_form.has_value()) {
        return finish_failed(NormalizedConstraintCheckResult::Unsupported);
    }

    if (!substituted_node.concept_id_dependent_qualifier.type.valid()) {
        concept_arguments = substituted_node.concept_id_arguments;
        if (!canonicalize_template_arguments(*target_concept,
                                             concept_arguments,
                                             loc,
                                             &concept_point_lookup_generation)) {
            return finish_failed(
                NormalizedConstraintCheckResult::Unsatisfied);
        }
    }
    if (template_arguments_are_dependent(concept_arguments)) {
        return finish_failed(NormalizedConstraintCheckResult::Unsupported);
    }

    collect::Session::NormalizedConstraint expanded_form;
    uint32_t expanded =
        expanded_form.append_copy_of(*target_concept->constraint_normal_form);
    auto concept_argument_bindings = canonical_template_argument_bindings(
        collect_session_, target_concept->parameters, concept_arguments);
    if (!expanded_form.valid_node(expanded) ||
        !concept_argument_bindings.has_value() ||
        !collect_session_.compose_constraint_parameter_mappings(
            expanded_form,
            expanded,
            *concept_argument_bindings,
            callbacks,
            &substitution_error)) {
        return finish_failed(NormalizedConstraintCheckResult::Unsatisfied);
    }
    expanded = expand_concept_pack_fold_constraints(expanded_form,
                                                    expanded,
                                                    loc);
    if (!expanded_form.valid_node(expanded)) {
        return finish_failed(NormalizedConstraintCheckResult::Unsatisfied);
    }
    expanded_form.root = expanded;

    restore_parser_checkpoint(checkpoint);
    collect_session_.commit_speculative_parse();
    return evaluate_normalized_associated_constraint(info,
                                                     arguments,
                                                     expanded_form,
                                                     expanded,
                                                     loc,
                                                     concept_point_lookup_generation);
}

Parser::NormalizedConstraintCheckResult
Parser::evaluate_normalized_fold_expanded_constraint(
    const collect::Session::TemplateInfo& info,
    const std::vector<collect::Session::TemplateArgument>& arguments,
    const collect::Session::NormalizedConstraint& form,
    const collect::Session::NormalizedConstraintNode& node,
    SrcLoc loc,
    uint64_t point_lookup_generation) {
    using Result = NormalizedConstraintCheckResult;
    using Fold = collect::Session::ConstraintFoldOperator;
    using PackKind =
        collect::Session::ConstraintFoldExpansionParameterKind;
    using FoldParameter =
        collect::Session::ConstraintFoldExpansionParameter;
    using TemplateArgument = collect::Session::TemplateArgument;

    if (node.kind != collect::Session::NormalizedConstraintKind::FoldExpanded ||
        !form.valid_node(node.lhs) ||
        node.fold_expansion_parameters.empty()) {
        return Result::Unsupported;
    }

    struct TemplatePackRun {
        const FoldParameter* parameter = nullptr;
        std::vector<TemplateArgument> elements;
    };
    struct FunctionPackRun {
        const FoldParameter* parameter = nullptr;
        std::vector<collect::ExprResult> elements;
    };

    std::vector<FunctionPackRun> function_pack_runs;
    std::vector<TemplatePackRun> type_pack_runs;
    std::vector<TemplatePackRun> value_pack_runs;
    std::vector<TemplatePackRun> template_pack_runs;
    std::optional<size_t> element_count;

    auto merge_element_count = [&](size_t count) -> Result {
        if (element_count.has_value() && *element_count != count) {
            return Result::Unsatisfied;
        }
        element_count = count;
        return Result::Satisfied;
    };
    auto argument_matches_parameter =
        [](const FoldParameter& parameter,
           const TemplateArgument& argument) {
        switch (parameter.kind) {
            case PackKind::Function:
                return false;
            case PackKind::Type:
                return argument.kind == cir::TemplateArgumentKind::Type &&
                       argument.type.type.valid();
            case PackKind::Value:
                return argument.kind == cir::TemplateArgumentKind::Value;
            case PackKind::Template:
                return argument.kind == cir::TemplateArgumentKind::Template &&
                       argument.template_entity.valid();
        }
        return false;
    };
    auto append_argument_elements =
        [&](const FoldParameter& parameter,
            const TemplateArgument& argument,
            std::vector<TemplateArgument>& elements) -> bool {
        if (!argument_matches_parameter(parameter, argument)) {
            return false;
        }
        if (collect_session_.template_argument_names_parameter_pack(
                argument)) {
            std::optional<std::vector<TemplateArgument>> expanded =
                collect_session_.template_argument_pack_arguments(argument);
            if (!expanded.has_value()) {
                return false;
            }
            for (TemplateArgument& element : *expanded) {
                if (!argument_matches_parameter(parameter, element)) {
                    return false;
                }
                elements.push_back(std::move(element));
            }
            return true;
        }
        elements.push_back(argument);
        return true;
    };
    auto template_argument_elements_for =
        [&](const FoldParameter& parameter)
        -> std::optional<std::vector<TemplateArgument>> {
        std::vector<TemplateArgument> elements;
        if (parameter.argument_pack.has_value()) {
            for (const TemplateArgument& argument :
                 *parameter.argument_pack) {
                if (!append_argument_elements(parameter,
                                              argument,
                                              elements)) {
                    return std::nullopt;
                }
            }
            return elements;
        }
        if (parameter.argument.kind == cir::TemplateArgumentKind::Type ||
            parameter.argument.kind == cir::TemplateArgumentKind::Value ||
            parameter.argument.kind ==
                cir::TemplateArgumentKind::Template) {
            if (collect_session_.template_argument_names_parameter_pack(
                    parameter.argument)) {
                std::optional<std::vector<TemplateArgument>> expanded =
                    collect_session_.template_argument_pack_arguments(
                        parameter.argument);
                if (!expanded.has_value()) {
                    return std::nullopt;
                }
                for (TemplateArgument& element : *expanded) {
                    if (!argument_matches_parameter(parameter, element)) {
                        return std::nullopt;
                    }
                }
                return expanded;
            }
        }
        switch (parameter.kind) {
            case PackKind::Type: {
                collect::Session::TypeParameterPackPattern pattern;
                pattern.name = parameter.name;
                pattern.template_entity =
                    parameter.owning_template_entity;
                pattern.depth = parameter.parameter_depth;
                pattern.index = parameter.parameter_index;
                pattern.type = parameter.type_parameter_pack_type;
                std::optional<std::vector<TemplateArgument>> expanded =
                    collect_session_.template_type_pack_arguments(pattern);
                if (!expanded.has_value()) {
                    return std::nullopt;
                }
                for (const TemplateArgument& element : *expanded) {
                    if (!argument_matches_parameter(parameter, element)) {
                        return std::nullopt;
                    }
                }
                return expanded;
            }
            case PackKind::Value:
            case PackKind::Template: {
                TemplateArgument marker = parameter.argument;
                if (parameter.kind == PackKind::Value) {
                    marker.kind = cir::TemplateArgumentKind::Value;
                    marker.value_param_index = parameter.parameter_index;
                } else {
                    marker.kind = cir::TemplateArgumentKind::Template;
                    marker.template_entity = parameter.parameter_entity;
                    marker.template_param_index =
                        parameter.parameter_index;
                }
                std::optional<std::vector<TemplateArgument>> expanded =
                    collect_session_.template_argument_pack_arguments(marker);
                if (!expanded.has_value()) {
                    return std::nullopt;
                }
                for (const TemplateArgument& element : *expanded) {
                    if (!argument_matches_parameter(parameter, element)) {
                        return std::nullopt;
                    }
                }
                return expanded;
            }
            case PackKind::Function:
                break;
        }
        return std::nullopt;
    };

    for (const FoldParameter& parameter : node.fold_expansion_parameters) {
        switch (parameter.kind) {
            case PackKind::Function: {
                std::optional<std::vector<collect::ExprResult>> elements =
                    collect_session_.function_parameter_pack_arguments(
                        parameter.name,
                        loc);
                if (!elements.has_value()) {
                    return Result::Unsupported;
                }
                Result merged = merge_element_count(elements->size());
                if (merged != Result::Satisfied) {
                    return merged;
                }
                function_pack_runs.push_back(
                    FunctionPackRun{&parameter, std::move(*elements)});
                break;
            }
            case PackKind::Type:
            case PackKind::Value:
            case PackKind::Template: {
                std::optional<std::vector<TemplateArgument>> elements =
                    template_argument_elements_for(parameter);
                if (!elements.has_value()) {
                    return Result::Unsupported;
                }
                Result merged = merge_element_count(elements->size());
                if (merged != Result::Satisfied) {
                    return merged;
                }
                TemplatePackRun run;
                run.parameter = &parameter;
                run.elements = std::move(*elements);
                if (parameter.kind == PackKind::Type) {
                    type_pack_runs.push_back(std::move(run));
                } else if (parameter.kind == PackKind::Value) {
                    value_pack_runs.push_back(std::move(run));
                } else {
                    template_pack_runs.push_back(std::move(run));
                }
                break;
            }
        }
    }

    size_t count = element_count.value_or(0);
    if (node.fold_operator == Fold::LogicalAnd && count == 0) {
        return Result::Satisfied;
    }
    if (node.fold_operator == Fold::LogicalOr && count == 0) {
        return Result::Unsatisfied;
    }

    for (size_t i = 0; i < count; ++i) {
        std::vector<collect::Session::ParameterPackElementBinding> bindings;

        auto make_pack_identity = [](const FoldParameter& parameter) {
            collect::Session::ParameterPackIdentity pack;
            switch (parameter.kind) {
                case PackKind::Function:
                    pack.kind = collect::Session::ParameterPackKind::Function;
                    break;
                case PackKind::Type:
                    pack.kind = collect::Session::ParameterPackKind::Type;
                    break;
                case PackKind::Value:
                    pack.kind = collect::Session::ParameterPackKind::Value;
                    break;
                case PackKind::Template:
                    pack.kind = collect::Session::ParameterPackKind::Template;
                    break;
            }
            pack.name = parameter.name;
            pack.declaration = parameter.parameter_entity;
            pack.owner = parameter.owning_template_entity;
            pack.depth = parameter.parameter_depth;
            pack.index = parameter.parameter_index;
            return pack;
        };

        for (const FunctionPackRun& run : function_pack_runs) {
            collect::Session::FunctionParameterPackElement element;
            element.entity = run.elements[i].entity;
            element.type = run.elements[i].type;
            element.place = run.elements[i].place;
            element.loc = loc;
            bindings.push_back(
                {make_pack_identity(*run.parameter), element});
        }

        for (const TemplatePackRun& run : type_pack_runs) {
            bindings.push_back({make_pack_identity(*run.parameter),
                                run.elements[i].type});
        }
        for (const TemplatePackRun& run : value_pack_runs) {
            bindings.push_back({make_pack_identity(*run.parameter),
                                run.elements[i]});
        }
        for (const TemplatePackRun& run : template_pack_runs) {
            bindings.push_back({make_pack_identity(*run.parameter),
                                run.elements[i]});
        }

        auto replay_scope =
            collect_session_.begin_parameter_pack_element_replay(bindings);

        struct ReplayScopeExit {
            collect::Session* session = nullptr;
            collect::Session::ParameterPackElementReplayScope replay_scope;
            ~ReplayScopeExit() {
                if (!session) {
                    return;
                }
                session->finish_parameter_pack_element_replay(replay_scope);
            }
        } replay_exit{&collect_session_, replay_scope};

        if (!replay_scope.active) {
            return Result::Unsupported;
        }

        collect::Session::NormalizedConstraint element_form;
        uint32_t element_root = element_form.append_copy_of(form, node.lhs);
        if (!element_form.valid_node(element_root)) {
            return Result::Unsupported;
        }
        collect::Session::TemplateArgumentBindings element_argument_bindings =
            node.fold_pattern_argument_bindings;
        if (element_argument_bindings.size() < info.parameters.size()) {
            element_argument_bindings.resize(info.parameters.size());
        }
        auto bind_element_argument = [&](const FoldParameter& parameter,
                                         TemplateArgument argument) {
            if (parameter.parameter_index ==
                    cir::ArrayTypePayload::no_extent_param ||
                parameter.parameter_index >=
                    element_argument_bindings.size()) {
                return;
            }
            argument.expands_parameter_pack = false;
            collect::Session::TemplateArgumentBinding& binding =
                element_argument_bindings[parameter.parameter_index];
            binding.kind =
                collect::Session::TemplateArgumentBindingKind::Pack;
            binding.arguments = {std::move(argument)};
        };
        for (const TemplatePackRun& run : type_pack_runs) {
            bind_element_argument(*run.parameter, run.elements[i]);
        }
        for (const TemplatePackRun& run : value_pack_runs) {
            bind_element_argument(*run.parameter, run.elements[i]);
        }
        for (const TemplatePackRun& run : template_pack_runs) {
            bind_element_argument(*run.parameter, run.elements[i]);
        }

        if (!element_argument_bindings.empty()) {
            collect::Session::PatternInstantiationCallbacks callbacks;
            callbacks.point_lookup_generation = point_lookup_generation;
            callbacks.allow_parameter_pack_element_substitution = true;
            configure_pattern_instantiation_callbacks(callbacks, loc);
            std::string substitution_error;
            if (!collect_session_.compose_constraint_parameter_mappings(
                    element_form,
                    element_root,
                    element_argument_bindings,
                    callbacks,
                    &substitution_error)) {
                return Result::Unsatisfied;
            }
        }

        Result element =
            evaluate_normalized_associated_constraint(info,
                                                      arguments,
                                                      element_form,
                                                      element_root,
                                                      loc,
                                                      point_lookup_generation);
        if (node.fold_operator == Fold::LogicalAnd) {
            if (element != Result::Satisfied) {
                return element;
            }
        } else {
            if (element == Result::Satisfied) {
                return Result::Satisfied;
            }
            if (element != Result::Unsatisfied) {
                return element;
            }
        }
    }

    return node.fold_operator == Fold::LogicalAnd ? Result::Satisfied
                                                  : Result::Unsatisfied;
}

Parser::NormalizedConstraintCheckResult
Parser::evaluate_normalized_associated_constraint(
    const collect::Session::TemplateInfo& info,
    const std::vector<collect::Session::TemplateArgument>& arguments,
    const collect::Session::NormalizedConstraint& form,
    uint32_t root,
    SrcLoc loc,
    uint64_t point_lookup_generation) {
    using Result = NormalizedConstraintCheckResult;
    using NodeKind = collect::Session::NormalizedConstraintKind;
    uint32_t index = root == collect::Session::NormalizedConstraint::no_node
        ? form.root
        : root;
    if (!form.valid_node(index)) {
        return Result::Unsupported;
    }

    bool graph_uses_direct_parameter_space = std::all_of(
        form.nodes.begin(),
        form.nodes.end(),
        [](const collect::Session::NormalizedConstraintNode& graph_node) {
            return graph_node.kind !=
                       collect::Session::NormalizedConstraintKind::
                           ConceptDependent &&
                   !graph_node.atom.appearance_owner.valid() &&
                   graph_node.atom.parameter_mapping.empty();
        });
    if (root == collect::Session::NormalizedConstraint::no_node &&
        form.value_expression.valid() && graph_uses_direct_parameter_space) {
        collect::Session::TemplateArgumentBindings bindings;
        if (collect_session_.bind_template_arguments_to_parameters(
                info.parameters, arguments, bindings)) {
            std::optional<bool> graph_value =
                collect_session_.evaluate_dependent_boolean_expression(
                    form.value_expression, bindings);
            if (graph_value.has_value()) {
                return *graph_value ? Result::Satisfied
                                    : Result::Unsatisfied;
            }
        }
    }

    const collect::Session::NormalizedConstraintNode& node =
        form.nodes[index];
    switch (node.kind) {
        case NodeKind::Atomic:
            if (node.atom.appearance_owner.valid()) {
                return evaluate_normalized_concept_owned_atom(
                    info,
                    arguments,
                    node,
                    loc,
                    point_lookup_generation);
            }
            return evaluate_normalized_direct_atom(info, node, loc);
        case NodeKind::ConceptDependent:
            return evaluate_normalized_concept_dependent_constraint(
                info,
                arguments,
                node,
                loc,
                point_lookup_generation);
        case NodeKind::FoldExpanded:
            return evaluate_normalized_fold_expanded_constraint(
                info,
                arguments,
                form,
                node,
                loc,
                point_lookup_generation);
        case NodeKind::Conjunction: {
            Result lhs =
                evaluate_normalized_associated_constraint(info,
                                                          arguments,
                                                          form,
                                                          node.lhs,
                                                          loc,
                                                          point_lookup_generation);
            if (lhs != Result::Satisfied) {
                return lhs;
            }
            return evaluate_normalized_associated_constraint(info,
                                                            arguments,
                                                            form,
                                                            node.rhs,
                                                            loc,
                                                            point_lookup_generation);
        }
        case NodeKind::Disjunction: {
            Result lhs =
                evaluate_normalized_associated_constraint(info,
                                                          arguments,
                                                          form,
                                                          node.lhs,
                                                          loc,
                                                          point_lookup_generation);
            if (lhs == Result::Satisfied) {
                return Result::Satisfied;
            }
            if (lhs != Result::Unsatisfied) {
                return lhs;
            }
            return evaluate_normalized_associated_constraint(info,
                                                            arguments,
                                                            form,
                                                            node.rhs,
                                                            loc,
                                                            point_lookup_generation);
        }
    }
    return Result::Unsupported;
}

bool Parser::check_template_associated_constraints(
    const collect::Session::TemplateInfo& info,
    const std::vector<collect::Session::TemplateArgument>& arguments,
    SrcLoc loc,
    uint64_t point_lookup_generation,
    bool diagnose_unsatisfied,
    const collect::Session::TemplateArgumentBindings* exact_bindings) {
    if (info.introduced_constraints.empty() ||
        template_arguments_are_dependent(arguments)) {
        return true;
    }

    if (Parser* owner = module_unit_parser_for(info.entity)) {
        collect::Session::ModuleVisibilityOverride visibility(
            collect_session_,
            collect_session_.file().entity(info.entity).origin_unit);
        return owner->check_template_associated_constraints(
            info, arguments, loc, point_lookup_generation,
            diagnose_unsatisfied, exact_bindings);
    }

    std::optional<collect::Session::TemplateArgumentBindings>
        owned_argument_bindings;
    if (exact_bindings) {
        owned_argument_bindings = *exact_bindings;
    } else {
        owned_argument_bindings = canonical_template_argument_bindings(
            collect_session_, info.parameters, arguments);
        if (!owned_argument_bindings.has_value()) {
            return false;
        }
    }
    collect_session_.canonicalize_template_argument_bindings(
        *owned_argument_bindings);
    const collect::Session::TemplateArgumentBindings* argument_bindings =
        &*owned_argument_bindings;

    using SatisfactionKind =
        collect::Session::ConstraintSatisfactionRequestKind;
    using SatisfactionResult =
        collect::Session::ConstraintSatisfactionResult;
    using SatisfactionState =
        collect::Session::ConstraintSatisfactionScope::State;
    collect::Session::ConstraintSatisfactionScope satisfaction_scope =
        collect_session_.begin_constraint_satisfaction(
            SatisfactionKind::AssociatedConstraints,
            info.entity,
            *argument_bindings,
            point_lookup_generation);
    if (satisfaction_scope.state == SatisfactionState::Cached) {
        bool satisfied =
            *satisfaction_scope.cached_result ==
            SatisfactionResult::Satisfied;
        if (!satisfied && diagnose_unsatisfied) {
            diagnose(DiagnosticLevel::Error,
                     "constraints not satisfied for template '" +
                         info.name + "'",
                         loc);
        }
        return satisfied;
    }
    if (satisfaction_scope.state == SatisfactionState::Recursive) {
        diagnose(DiagnosticLevel::Error,
                 "constraint satisfaction depends on itself",
                 loc);
        return false;
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
    auto finish_unsatisfied = [&]() {
        satisfaction_exit.finish(SatisfactionResult::Unsatisfied);
        if (diagnose_unsatisfied) {
            diagnose(DiagnosticLevel::Error,
                     "constraints not satisfied for template '" +
                         info.name + "'",
                     loc);
        }
        return false;
    };
    auto finish_invalid = [&]() {
        satisfaction_exit.finish(SatisfactionResult::Invalid);
        return false;
    };

    const collect::Session::TemplateArgumentBindings* saved_bindings =
        constraint_argument_bindings_override_;

    constraint_argument_bindings_override_ =
        exact_bindings ? argument_bindings : nullptr;
    struct ConstraintBindingsOverrideExit {
        Parser* parser = nullptr;
        const collect::Session::TemplateArgumentBindings* saved = nullptr;
        ~ConstraintBindingsOverrideExit() {
            if (parser) {
                parser->constraint_argument_bindings_override_ = saved;
            }
        }
    } bindings_exit{this, saved_bindings};

    std::vector<collect::Session::TemplateInfo::IntroducedConstraint>
        constraints = info.introduced_constraints;
    std::stable_sort(
        constraints.begin(),
        constraints.end(),
        collect::Session::TemplateInfo::associated_constraint_order_less);
    bool has_trailing_function_constraint = std::any_of(
        constraints.begin(),
        constraints.end(),
        [](const auto& constraint) {
            return constraint.kind == collect::Session::TemplateInfo::
                IntroducedConstraintKind::FunctionTrailingRequires;
        });
    auto is_introduced_type_constraint = [](const auto& constraint) {
        using Kind =
            collect::Session::TemplateInfo::IntroducedConstraintKind;
        return constraint.kind == Kind::TemplateParameterTypeConstraint ||
            constraint.kind == Kind::FunctionParameterTypeConstraint;
    };
    bool has_introduced_type_constraint = std::any_of(
        constraints.begin(),
        constraints.end(),
        is_introduced_type_constraint);

    struct ConstraintInstantiationScopeExit {
        collect::Session* session = nullptr;
        collect::Session::InstantiationScope scope;
        ~ConstraintInstantiationScopeExit() {
            if (session) {
                session->finish_template_instantiation(std::move(scope));
            }
        }
    } instantiation_scope;
    instantiation_scope.scope =
        collect_session_.begin_template_instantiation(info,
                                                      arguments,
                                                      loc,
                                                      point_lookup_generation,
                                                      {},
                                                      exact_bindings
                                                          ? argument_bindings
                                                          : nullptr);
    if (!instantiation_scope.scope.active) {
        return finish_invalid();
    }
    instantiation_scope.session = &collect_session_;

    std::vector<collect::Session::TemplateInfo::FunctionConstraintParameter>
        constraint_parameters;
    if (has_trailing_function_constraint &&
        !info.function_constraint_parameters.empty()) {
        collect::Session::PatternInstantiationCallbacks callbacks;
        callbacks.point_lookup_generation = point_lookup_generation;
        callbacks.access_loc = loc;
        configure_pattern_instantiation_callbacks(callbacks, loc);
        if (!collect_session_.populate_exact_template_parameter_bindings(
                info, *argument_bindings, callbacks)) {
            return finish_invalid();
        }
        for (const auto& recipe : info.function_constraint_parameters) {
            if (recipe.is_parameter_pack) {
                std::optional<std::vector<cir::TypeRef>> expanded =
                    collect_session_
                        .substitute_pattern_function_parameter_pack(
                            recipe.type, *argument_bindings, callbacks);
                if (!expanded.has_value()) {
                    return finish_invalid();
                }
                std::string source_name = recipe.name != "<anonymous>"
                    ? recipe.name
                    : recipe.source_parameter_pack_name;
                if (expanded->empty()) {
                    auto sentinel = recipe;
                    sentinel.name = source_name.empty()
                        ? "<anonymous>"
                        : source_name;
                    sentinel.is_parameter_pack = false;
                    sentinel.source_parameter_pack_name = source_name;
                    sentinel.is_parameter_pack_expansion_sentinel = true;
                    constraint_parameters.push_back(std::move(sentinel));
                    continue;
                }
                for (size_t i = 0; i < expanded->size(); ++i) {
                    auto element = recipe;
                    element.name = source_name.empty()
                        ? "<anonymous>"
                        : source_name + "." + std::to_string(i);
                    element.type = (*expanded)[i];
                    element.is_parameter_pack = false;
                    element.source_parameter_pack_name = source_name;
                    element.is_parameter_pack_expansion_sentinel = false;
                    constraint_parameters.push_back(std::move(element));
                }
                continue;
            }
            auto parameter = recipe;
            if (!parameter.is_parameter_pack_expansion_sentinel) {
                parameter.type =
                    collect_session_.substitute_pattern_type_ref(
                        recipe.type, *argument_bindings, callbacks);
                if (!parameter.type.valid()) {
                    return finish_invalid();
                }
            }
            constraint_parameters.push_back(std::move(parameter));
        }
    }

    size_t saved_cursor = cursor_;
    size_t saved_last_end = last_consumed_raw_end_;
    struct ConstraintCursorExit {
        Parser* parser = nullptr;
        size_t cursor = 0;
        size_t last_end = 0;
        ~ConstraintCursorExit() {
            if (parser) {
                parser->cursor_ = cursor;
                parser->last_consumed_raw_end_ = last_end;
            }
        }
    } cursor_exit{this, saved_cursor, saved_last_end};

    if (!has_introduced_type_constraint) {
        bool all_normal_forms_supported = true;
        for (const auto& constraint : constraints) {
            if (!constraint.normal_form.has_value()) {
                all_normal_forms_supported = false;
                break;
            }

            struct NormalizedConstraintParameterScopeExit {
                collect::Session* session = nullptr;
                collect::Session::PrototypeParameterScope scope;
                ~NormalizedConstraintParameterScopeExit() {
                    if (session) {
                        session->finish_function_constraint_parameter_scope(
                            std::move(scope));
                    }
                }
            } normalized_parameter_scope;
            if (constraint.kind == collect::Session::TemplateInfo::
                    IntroducedConstraintKind::FunctionTrailingRequires &&
                !constraint_parameters.empty()) {
                normalized_parameter_scope.scope =
                    collect_session_.begin_function_constraint_parameter_scope(
                        constraint_parameters);
                if (normalized_parameter_scope.scope.active) {
                    normalized_parameter_scope.session = &collect_session_;
                }
            }

            NormalizedConstraintCheckResult normal_result =
                evaluate_normalized_associated_constraint(
                    info,
                    arguments,
                    *constraint.normal_form,
                    collect::Session::NormalizedConstraint::no_node,
                    loc,
                    point_lookup_generation);
            switch (normal_result) {
                case NormalizedConstraintCheckResult::Satisfied:
                    break;
                case NormalizedConstraintCheckResult::Unsatisfied:
                    return finish_unsatisfied();
                case NormalizedConstraintCheckResult::Invalid:
                    return finish_invalid();
                case NormalizedConstraintCheckResult::Unsupported:
                    all_normal_forms_supported = false;
                    break;
            }
            if (!all_normal_forms_supported) {
                break;
            }
        }
        if (all_normal_forms_supported) {
            satisfaction_exit.finish(SatisfactionResult::Satisfied);
            return true;
        }
    }

    bool saw_dependent_constraint = false;
    for (const auto& constraint : constraints) {
        struct ConstraintParameterScopeExit {
            collect::Session* session = nullptr;
            collect::Session::PrototypeParameterScope scope;
            ~ConstraintParameterScopeExit() {
                if (session) {
                    session->finish_function_constraint_parameter_scope(
                        std::move(scope));
                }
            }
        } parameter_scope;
        if (constraint.kind == collect::Session::TemplateInfo::
                IntroducedConstraintKind::FunctionTrailingRequires &&
            !constraint_parameters.empty()) {
            parameter_scope.scope =
                collect_session_.begin_function_constraint_parameter_scope(
                    constraint_parameters);
            if (parameter_scope.scope.active) {
                parameter_scope.session = &collect_session_;
            }
        }
        struct ConstraintSubstitutionFailureScope {
            Parser* parser = nullptr;
            size_t saved_depth = 0;
            bool saved_failure = false;

            explicit ConstraintSubstitutionFailureScope(Parser& parser)
                : parser(&parser),
                  saved_depth(parser.constraint_substitution_failure_depth_),
                  saved_failure(parser.constraint_substitution_failure_) {
                parser.constraint_substitution_failure_depth_ = saved_depth + 1;
                parser.constraint_substitution_failure_ = false;
            }

            bool failed() const {
                return parser && parser->constraint_substitution_failure_;
            }

            void restore() {
                if (!parser) {
                    return;
                }
                parser->constraint_substitution_failure_depth_ = saved_depth;
                parser->constraint_substitution_failure_ = saved_failure;
                parser = nullptr;
            }

            ~ConstraintSubstitutionFailureScope() {
                restore();
            }
        } substitution_failure_scope(*this);

        ParserCheckpoint replay_checkpoint = capture_parser_checkpoint();
        size_t error_watermark = collect_session_.file().errors().size();
        size_t saved_constraint_replay_end =
            constraint_expression_replay_end_;
        std::vector<size_t> saved_template_argument_expression_begins =
            template_argument_expression_begins_;
        collect_session_.begin_speculative_parse();
        pending_template_closes_ = 0;
        template_argument_expression_begins_.clear();
        size_t parsed_begin = 0;
        size_t parsed_end = 0;
        std::optional<bool> value;
        bool introduced_substitution_failure = false;
        bool valid = true;
        if (is_introduced_type_constraint(constraint)) {
            valid = evaluate_introduced_type_constraint(
                info,
                constraint,
                arguments,
                loc,
                point_lookup_generation,
                value,
                introduced_substitution_failure);
        } else {
            seek_raw_index(constraint.begin);
            constraint_expression_replay_end_ = constraint.end;
            valid = parse_and_validate_constraint_expression(
                loc_for_index(constraint.begin),
                parsed_begin,
                parsed_end,
                &value);
            if (valid && (parsed_begin != constraint.begin ||
                          parsed_end != constraint.end)) {
                diagnose(DiagnosticLevel::Error,
                         "unexpected tokens in associated constraint-expression",
                         current_loc());
                valid = false;
            }
        }
        bool substitution_failure =
            substitution_failure_scope.failed() ||
            introduced_substitution_failure;
        std::vector<std::pair<SrcLoc, std::string>> captured_errors(
            collect_session_.file().errors().begin() + error_watermark,
            collect_session_.file().errors().end());
        std::vector<Diagnostic> captured_parser_diagnostics(
            diagnostics_.begin() + replay_checkpoint.diagnostics_size,
            diagnostics_.end());
        collect_session_.rollback_speculative_parse();
        restore_parser_checkpoint(replay_checkpoint);
        constraint_expression_replay_end_ =
            saved_constraint_replay_end;
        template_argument_expression_begins_ =
            std::move(saved_template_argument_expression_begins);
        substitution_failure_scope.restore();
        if (substitution_failure) {
            return finish_unsatisfied();
        }
        if (!valid) {
            for (auto& [error_loc, message] : captured_errors) {
                collect_session_.file().add_error(std::move(message),
                                                  error_loc);
            }
            diagnostics_.insert(diagnostics_.end(),
                                captured_parser_diagnostics.begin(),
                                captured_parser_diagnostics.end());
            return finish_invalid();
        }
        if (value.has_value() && !*value) {
            return finish_unsatisfied();
        }
        if (!value.has_value()) {
            saw_dependent_constraint = true;
        }
    }
    satisfaction_exit.finish(
        saw_dependent_constraint ? SatisfactionResult::Dependent
                                 : SatisfactionResult::Satisfied);
    return true;
}

collect::Session::PartialSpecializationSelection
Parser::select_template_partial_specialization(
    const collect::Session::TemplateInfo& primary,
    const std::vector<collect::Session::TemplateArgument>& arguments,
    SrcLoc loc,
    uint64_t point_lookup_generation) {
    bool requires_pattern_validation = false;
    for (const auto& entry : primary.partial_specializations) {
        for (const collect::Session::TemplateArgument& argument :
             entry.arguments) {
            if (argument.kind == cir::TemplateArgumentKind::Type &&
                (collect_session_.type_contains_nondeduced_context(
                     argument.type.type) ||
                 collect_session_
                     .type_contains_dependent_alias_specialization(
                         argument.type.type))) {
                requires_pattern_validation = true;
                break;
            }
        }
        if (requires_pattern_validation) {
            break;
        }
    }
    collect::Session::PartialSpecializationCandidatePredicate
        candidate_viable;
    if (requires_pattern_validation) {
        candidate_viable =
            [&](const collect::Session::TemplateInfo& partial,
                const collect::Session::TemplateArgumentBindings&
                    bindings) {
                return partial_specialization_pattern_is_viable(
                    primary,
                    partial,
                    bindings,
                    arguments,
                    loc,
                    point_lookup_generation);
            };
    }
    return collect_session_.select_template_partial_specialization(
        primary,
        arguments,
        [&](const collect::Session::TemplateInfo& partial,
            const collect::Session::TemplateArgumentBindings& bindings) {
            std::vector<collect::Session::TemplateArgument> deduced =
                collect_session_.flatten_template_argument_bindings(bindings);
            return check_template_associated_constraints(
                partial,
                deduced,
                loc,
                point_lookup_generation,
                /*diagnose_unsatisfied=*/false,
                &bindings);
        },
        candidate_viable);
}

bool Parser::partial_specialization_pattern_is_viable(
    const collect::Session::TemplateInfo& primary,
    const collect::Session::TemplateInfo& partial,
    const collect::Session::TemplateArgumentBindings& bindings,
    const std::vector<collect::Session::TemplateArgument>& actual,
    SrcLoc loc,
    uint64_t point_lookup_generation) {
    const collect::Session::TemplateInfo::PartialSpecialization* entry =
        nullptr;
    for (const auto& candidate : primary.partial_specializations) {
        if (candidate.entity == partial.entity) {
            entry = &candidate;
            break;
        }
    }
    if (!entry) {
        return false;
    }
    size_t fixed_argument_count = entry->arguments.size();
    if (!entry->arguments.empty() &&
        (entry->arguments.back().expands_parameter_pack ||
         entry->arguments.back().expands_pack_pattern)) {

        --fixed_argument_count;
    }
    if (fixed_argument_count > actual.size()) {
        return false;
    }

    RevertingTentativeParsingAction probe(*this,
                                          TentativeMode::CollectBacked);
    if (bindings.size() != partial.parameters.size()) {
        return false;
    }
    collect::Session::PatternInstantiationCallbacks callbacks;
    callbacks.point_lookup_generation = point_lookup_generation;
    callbacks.access_loc = loc;
    callbacks.argument_completion_mode =
        collect::Session::TemplateArgumentCompletionMode::Candidate;
    configure_pattern_instantiation_callbacks(callbacks, loc);
    if (!collect_session_.populate_exact_template_parameter_bindings(
            partial, bindings, callbacks)) {
        return false;
    }

    for (size_t i = 0; i < entry->arguments.size(); ++i) {
        const collect::Session::TemplateArgument& pattern =
            entry->arguments[i];
        if (pattern.expands_parameter_pack ||
            pattern.expands_pack_pattern) {

            break;
        }
        collect::Session::TemplateArgument substituted = pattern;
        if (substituted.kind == cir::TemplateArgumentKind::Type) {
            substituted.type =
                collect_session_.substitute_pattern_type_ref(
                    substituted.type, bindings, callbacks);
            if (!substituted.type.valid()) {
                return false;
            }
        } else if (substituted.kind ==
                   cir::TemplateArgumentKind::Value) {
            if (!collect_session_.substitute_template_value_argument(
                    substituted, bindings, callbacks)) {
                return false;
            }
        } else if (!collect_session_.substitute_template_template_argument(
                       substituted, bindings, callbacks)) {
            return false;
        }
        if (!collect_session_.template_arguments_equivalent(substituted,
                                                            actual[i])) {
            return false;
        }
    }
    return true;
}

bool Parser::check_non_function_template_associated_constraints(
    const collect::Session::TemplateInfo& info,
    const std::vector<collect::Session::TemplateArgument>& arguments,
    SrcLoc loc,
    uint64_t point_lookup_generation) {
    if (!info.is_class_template && !info.is_alias_template &&
        !info.is_variable_template) {
        return true;
    }
    return check_template_associated_constraints(info,
                                                 arguments,
                                                 loc,
                                                 point_lookup_generation,
                                                 /*diagnose_unsatisfied=*/
                                                 !in_constraint_substitution_failure_context());
}

bool Parser::deduce_function_template_declaration_match(
    const collect::Session::TemplateInfo& info,
    cir::TypeId function_type,
    std::vector<collect::Session::TemplateArgument>& deduced,
    const std::vector<collect::Session::TemplateArgument>* explicit_arguments,
    collect::Session::PatternInstantiationCallbacks& callbacks,
    SrcLoc loc,
    bool ignore_top_level_exception_spec) {
    if (!collect_session_.deduce_function_template_address_arguments(
            info,
            function_type,
            deduced,
            explicit_arguments,
            &callbacks,
            loc,
            ignore_top_level_exception_spec
                ? collect::Session::TypePatternExceptionMatch::
                      IgnoreAtCurrentFunction
                : collect::Session::TypePatternExceptionMatch::Exact)) {
        return false;
    }
    return check_template_associated_constraints(info,
                                                 deduced,
                                                 loc,
                                                 callbacks.point_lookup_generation,
                                                 /*diagnose_unsatisfied=*/false);
}

cir::EntityId Parser::form_function_template_candidate(
    const collect::Session::TemplateInfo& info,
    const collect::Session::TemplateArgumentBindings& argument_bindings,
    SrcLoc loc,
    uint64_t point_lookup_generation) {
    if (info.is_class_template || info.is_alias_template ||
        info.is_variable_template || info.is_concept ||
        !info.pattern_type.valid()) {
        return {};
    }
    std::vector<collect::Session::TemplateArgument> arguments =
        collect_session_.flatten_template_argument_bindings(
            argument_bindings);

    TentativeParsingAction transaction(*this, TentativeMode::CollectBacked);

    if (!check_template_associated_constraints(
            info,
            arguments,
            loc,
            point_lookup_generation,
            /*diagnose_unsatisfied=*/false,
            &argument_bindings)) {
        return {};
    }

    std::string memo_key =
        collect_session_.template_memo_key(info.entity, argument_bindings);
    if (cir::EntityId cached =
            collect_session_.cached_instantiation(memo_key);
        cached.valid()) {
        transaction.commit();
        return cached;
    }

    if (argument_bindings.size() != info.parameters.size()) {
        return {};
    }
    for (size_t index = 0; index < argument_bindings.size(); ++index) {
        const auto& binding = argument_bindings[index];
        if (info.parameters[index].is_parameter_pack) {
            if (!binding.is_pack()) {
                return {};
            }
        } else if (!binding.is_single() ||
                   binding.arguments.size() != 1) {
            return {};
        }
    }
    collect::Session::PatternInstantiationCallbacks callbacks;
    callbacks.point_lookup_generation = point_lookup_generation;
    callbacks.defer_function_exception_spec = false;
    callbacks.access_loc = loc;

    callbacks.materialize_type_template_definition = false;
    configure_pattern_instantiation_callbacks(callbacks, loc);
    if (!collect_session_.populate_exact_template_parameter_bindings(
            info, argument_bindings, callbacks)) {
        return {};
    }
    cir::TypeId declared_type{};
    bool structural_signature_valid = false;
    bool structural_failure_reported = false;
    std::vector<std::pair<SrcLoc, std::string>> hard_substitution_errors;
    bool replay_signature_failed = false;

    (void)collect_session_.take_substitution_hard_error();
    {

        TentativeParsingAction substitution_transaction(
            *this, TentativeMode::CollectBacked);
        size_t error_watermark = collect_session_.file().errors().size();
        size_t diagnostic_watermark = diagnostics_.size();
        declared_type =
            collect_session_.substitute_pattern_type(info.pattern_type,
                                                     argument_bindings,
                                                     callbacks);
        cir::TypeId substituted_resolved =
            collect_session_.file().resolved_type(declared_type);
        structural_signature_valid =
            declared_type.valid() &&
            collect_session_.file().valid(substituted_resolved) &&
            collect_session_.file().type(substituted_resolved).kind ==
                cir::TypeKind::Function;
        structural_failure_reported =
            collect_session_.file().errors().size() != error_watermark ||
            diagnostics_.size() != diagnostic_watermark;
        if (structural_signature_valid) {
            substitution_transaction.commit();
        } else if (structural_failure_reported &&
                   collect_session_.take_substitution_hard_error()) {
            hard_substitution_errors.assign(
                collect_session_.file().errors().begin() + error_watermark,
                collect_session_.file().errors().end());
        }
    }
    if (!structural_signature_valid && structural_failure_reported) {
        if (!hard_substitution_errors.empty()) {
            transaction.revert();
            for (auto& [error_loc, message] : hard_substitution_errors) {
                collect_session_.file().add_error(std::move(message),
                                                  error_loc);
            }
        }
        return {};
    }
    cir::TypeId resolved = collect_session_.file().resolved_type(declared_type);

    if (!structural_signature_valid ||
        collect_session_.type_contains_type_param(declared_type) ||
        type_contains_lambda_closure(collect_session_.file(),
                                     info.pattern_type)) {
        struct InstantiationScopeExit {
            collect::Session* session = nullptr;
            collect::Session::InstantiationScope scope;
            ~InstantiationScopeExit() {
                if (session) {
                    session->finish_template_instantiation(std::move(scope));
                }
            }
        } instantiation_scope;
        instantiation_scope.scope =
            collect_session_.begin_template_instantiation(
                info,
                arguments,
                loc,
                point_lookup_generation,
                {},
                &argument_bindings);
        if (!instantiation_scope.scope.active) {
            return {};
        }
        instantiation_scope.session = &collect_session_;

        size_t saved_cursor = cursor_;
        size_t saved_last_end = last_consumed_raw_end_;
        int saved_closes = pending_template_closes_;
        size_t error_watermark = collect_session_.file().errors().size();
        size_t diagnostic_watermark = diagnostics_.size();
        cursor_ = info.definition_begin;
        pending_template_closes_ = 0;
        const cir::Entity& primary =
            collect_session_.file().entity(info.entity);
        bool is_member = primary.kind == cir::EntityKind::Method ||
                         primary.kind == cir::EntityKind::Constructor ||
                         primary.kind == cir::EntityKind::Destructor;
        TypeParseContext context = TypeParseContext::type_only(
            is_member ? TypeParseContext::Origin::MemberDeclSpecifier
                      : TypeParseContext::Origin::NamespaceDeclSpecifier);
        DeclarationParser signature_parser(*this, context);
        cir::TypeRef base = signature_parser.parse_declaration(false, true);
        ParsedDeclarator concrete =
            signature_parser.parse_declarator(base, false);
        cursor_ = saved_cursor;
        last_consumed_raw_end_ = saved_last_end;
        pending_template_closes_ = saved_closes;
        declared_type = concrete.type;
        resolved = collect_session_.file().resolved_type(declared_type);
        bool valid_signature =
            concrete.has_name && declared_type.valid() &&
            collect_session_.file().valid(resolved) &&
            collect_session_.file().type(resolved).kind ==
                cir::TypeKind::Function &&
            !collect_session_.type_contains_type_param(declared_type) &&
            collect_session_.file().errors().size() == error_watermark &&
            diagnostics_.size() == diagnostic_watermark;
        if (!valid_signature) {

            if (collect_session_.take_substitution_hard_error()) {
                hard_substitution_errors.assign(
                    collect_session_.file().errors().begin() + error_watermark,
                    collect_session_.file().errors().end());
            }
            replay_signature_failed = true;
        }
    }
    if (replay_signature_failed) {
        if (!hard_substitution_errors.empty()) {
            transaction.revert();
            for (auto& [error_loc, message] : hard_substitution_errors) {
                collect_session_.file().add_error(std::move(message),
                                                  error_loc);
            }
        }
        return {};
    }

    cir::EntityId candidate{};
    const cir::Entity& primary = collect_session_.file().entity(info.entity);
    if (primary.kind == cir::EntityKind::Method ||
        primary.kind == cir::EntityKind::Constructor ||
        primary.kind == cir::EntityKind::Destructor) {
        candidate = collect_session_.create_member_template_specialization(
            info,
            arguments,
            declared_type,
            loc,
            nullptr,
            &argument_bindings,
            /*defer_inherited_constructor_definition=*/true);
        if (candidate.valid() &&
            info.explicit_specifier == cir::ExplicitSpecifierKind::Dependent) {
            std::optional<bool> explicit_value =
                resolve_member_specialization_explicit_specifier(
                    info, arguments, candidate, loc, &argument_bindings);
            if (!explicit_value.has_value()) {
                return {};
            }
        }
    } else {
        candidate =
            collect_session_.create_function_template_declaration_specialization(
                info,
                arguments,
                callbacks,
                loc,
                declared_type,
                &argument_bindings);
    }
    if (!candidate.valid()) {
        return {};
    }
    collect_session_.remember_instantiation(memo_key, candidate);
    transaction.commit();
    return candidate;
}

collect::Session::CoroutinePromiseResolution
Parser::resolve_coroutine_promise_type(
    const std::vector<cir::TypeRef>& traits_arguments,
    SrcLoc loc) {
    collect::Session::CoroutinePromiseResolution result;
    const collect::Session::TemplateInfo* traits_template =
        collect_session_.peek_qualified_template_info(
            /*global_qualifier=*/true,
            {std::string_view("std")},
            "coroutine_traits");
    if (!traits_template || !traits_template->is_class_template) {
        return result;
    }
    std::vector<collect::Session::TemplateArgument> arguments;
    arguments.reserve(traits_arguments.size());
    for (const cir::TypeRef& type : traits_arguments) {
        collect::Session::TemplateArgument argument;
        argument.kind = cir::TemplateArgumentKind::Type;
        argument.type = type;
        arguments.push_back(std::move(argument));
    }
    cir::EntityId specialization = instantiate_template_with_args(
        *traits_template, std::move(arguments), loc);
    const cir::File& file = collect_session_.file();
    if (!specialization.valid() || !file.valid(specialization)) {
        return result;
    }
    result.traits_specialization =
        file.resolved_type(file.entity(specialization).type);
    cir::DeclContextId traits_context =
        file.entity(specialization).semantic_context;
    if (!traits_context.valid()) {
        return result;
    }
    result.promise_type = collect_session_.lookup_qualified_type_name_checked(
        traits_context, "promise_type", loc);
    if (!result.promise_type.valid()) {
        return result;
    }

    const collect::Session::TemplateInfo* handle_template =
        collect_session_.peek_qualified_template_info(
            /*global_qualifier=*/true,
            {std::string_view("std")},
            "coroutine_handle");
    if (!handle_template || !handle_template->is_class_template) {
        return result;
    }
    collect::Session::TemplateArgument handle_argument;
    handle_argument.kind = cir::TemplateArgumentKind::Type;
    handle_argument.type = collect_session_.type_ref(result.promise_type);
    cir::EntityId handle = instantiate_template_with_args(
        *handle_template, {std::move(handle_argument)}, loc);
    if (handle.valid() && file.valid(handle) &&
        file.entity(handle).kind == cir::EntityKind::Record) {
        result.handle_type = file.resolved_type(file.entity(handle).type);
    }
    return result;
}

cir::EntityId Parser::instantiate_template_with_args(
    const collect::Session::TemplateInfo& info,
    std::vector<collect::Session::TemplateArgument> arguments,
    SrcLoc loc,
    uint64_t point_lookup_generation,
    bool replay_guard_entered,
    bool arguments_are_canonical,
    bool materialize_class_definition,
    bool record_point_of_instantiation,
    collect::Session::TemplateArgumentCompletionMode completion_mode,
    const collect::Session::TemplateArgumentBindings* exact_bindings) {
    if (exact_bindings) {
        arguments =
            collect_session_.flatten_template_argument_bindings(
                *exact_bindings);
        arguments_are_canonical = true;
    }

    if (Parser* owner = module_unit_parser_for(info.entity)) {
        collect::Session::ModuleVisibilityOverride visibility(
            collect_session_,
            collect_session_.file().entity(info.entity).origin_unit);
        return owner->instantiate_template_with_args(
            info, std::move(arguments), loc, point_lookup_generation,
            replay_guard_entered, arguments_are_canonical,
            materialize_class_definition, record_point_of_instantiation,
            completion_mode, exact_bindings);
    }
    TemplateReplayGuardExit replay_guard{&collect_session_, false};
    if (!replay_guard_entered) {
        if (!collect_session_.enter_template_replay_guard(loc)) {
            return {};
        }
        replay_guard.active = true;
    }

    if (!arguments_are_canonical &&
        !canonicalize_template_arguments(info,
                                         arguments,
                                         loc,
                                         &point_lookup_generation,
                                         completion_mode)) {
        return {};
    }
    bool is_template_template_parameter_placeholder =
        info.entity.valid() &&
        collect_session_.file().valid(info.entity) &&
        collect_session_.file().entity(info.entity).kind ==
            cir::EntityKind::TemplateParam;
    if (is_template_template_parameter_placeholder) {
        if (info.is_class_template) {
            return collect_session_.create_dependent_record_specialization(
                info,
                arguments,
                loc);
        }
        if (info.is_variable_template) {
            return collect_session_.create_dependent_variable_specialization(
                info,
                arguments,
                loc);
        }
    }
    bool is_function_template =
        !info.is_class_template && !info.is_alias_template &&
        !info.is_variable_template && !info.is_concept;
    if (is_function_template &&
        !check_template_associated_constraints(
            info,
            arguments,
            loc,
            point_lookup_generation,
            /*diagnose_unsatisfied=*/false,
            exact_bindings)) {
        return {};
    }
    if (!check_non_function_template_associated_constraints(
            info,
            arguments,
            loc,
            point_lookup_generation)) {
        return {};
    }
    std::string memo_key = exact_bindings
        ? collect_session_.template_memo_key(info.entity, *exact_bindings)
        : collect_session_.template_memo_key(info.entity, arguments);
    if (info.is_alias_template) {
        if (cir::EntityId cached =
                collect_session_.cached_instantiation(memo_key);
            cached.valid()) {
            return cached;
        }
        if (!info.has_definition) {
            diagnose(DiagnosticLevel::Error,
                     "cannot instantiate undefined template '" + info.name + "'",
                     loc);
            return {};
        }
        cir::EntityId dependent_primary_record =
            collect_session_.current_validation_record();
        if (!dependent_primary_record.valid()) {
            if (const collect::Session::TemplateInfo* validating =
                collect_session_.validating_template_info();
                validating && validating->is_class_template) {
                dependent_primary_record = validating->entity;
            }
        }
        cir::TypeRef target = info.alias_target_type_ref.valid()
            ? info.alias_target_type_ref
            : collect_session_.type_ref(info.alias_target_type);
        bool substitution_failed = false;
        bool deferred_on_enclosing_type_pack = false;
        {

            TentativeParsingAction transaction(*this,
                                               TentativeMode::CollectBacked);
            size_t error_watermark =
                collect_session_.file().errors().size();
            size_t diagnostic_watermark = diagnostics_.size();

            collect::Session::InstantiationScope alias_scope =
                collect_session_.begin_template_instantiation(
                    info, arguments, loc, point_lookup_generation);
            if (!alias_scope.active) {
                return {};
            }
            struct AliasInstantiationScopeExit {
                collect::Session* session = nullptr;
                collect::Session::InstantiationScope scope;
                ~AliasInstantiationScopeExit() {
                    if (session) {
                        session->finish_template_instantiation(
                            std::move(scope));
                    }
                }
            } alias_scope_exit{&collect_session_, std::move(alias_scope)};

            cir::TypeRef associated_type_ref;
            bool requires_fresh_closure = target.valid() &&
                type_contains_lambda_closure(collect_session_.file(),
                                             target.type);
            if (requires_fresh_closure) {

                size_t saved_cursor = cursor_;
                size_t saved_last_end = last_consumed_raw_end_;
                cursor_ = info.definition_begin;
                cir::TypeId associated_type;
                collect::Session::LookupGenerationCeilingScope ceiling(
                    collect_session_, info.definition_generation);
                parse_type_name(&associated_type,
                                nullptr,
                                nullptr,
                                &associated_type_ref);
                cursor_ = saved_cursor;
                last_consumed_raw_end_ = saved_last_end;
            } else {
                collect::Session::TemplateArgumentBindings bindings;
                collect::Session::PatternInstantiationCallbacks callbacks;
                callbacks.point_lookup_generation = point_lookup_generation;
                callbacks.access_loc = loc;
                callbacks.argument_completion_mode = completion_mode;
                if (template_arguments_are_dependent(arguments)) {
                    callbacks.dependent_primary_record =
                        dependent_primary_record;
                }
                configure_pattern_instantiation_callbacks(callbacks, loc);

                callbacks.materialize_type_template_definition =
                    materialize_class_definition;
                bool bound =
                    collect_session_.bind_template_arguments_to_parameters(
                        info.parameters,
                        arguments,
                        bindings,
                        nullptr,
                        collect::Session::TemplateArgumentBindingMode::
                            Canonical) &&
                    collect_session_.populate_exact_template_parameter_bindings(
                        info, bindings, callbacks);
                if (bound && target.valid()) {
                    collect::Session::LookupGenerationCeilingScope ceiling(
                        collect_session_, info.definition_generation);
                    associated_type_ref =
                        collect_session_.substitute_pattern_type_ref(
                            target, bindings, callbacks);
                    deferred_on_enclosing_type_pack =
                        callbacks.deferred_on_enclosing_type_pack;
                }
            }

            if (associated_type_ref.valid() &&
                !template_arguments_are_dependent(arguments) &&
                info.alias_type_attribute_begin <
                    info.alias_type_attribute_end) {
                size_t saved_cursor = cursor_;
                size_t saved_last_end = last_consumed_raw_end_;
                cursor_ = info.alias_type_attribute_begin;
                ParsedAttributes instantiated_attrs =
                    try_parse_standard_or_gnu_attributes();
                cursor_ = saved_cursor;
                last_consumed_raw_end_ = saved_last_end;
                associated_type_ref =
                    collect_session_.apply_type_attributes(
                        associated_type_ref,
                        instantiated_attrs.attrs,
                        loc);
            }

            bool hard_error =
                collect_session_.file().errors().size() != error_watermark ||
                diagnostics_.size() != diagnostic_watermark;
            if (hard_error) {
                transaction.commit();
                return {};
            }
            if (!associated_type_ref.valid()) {
                substitution_failed = true;
            } else {
                cir::EntityId alias =
                    collect_session_.create_alias_template_specialization(
                        info, arguments, associated_type_ref, loc);
                if (!alias.valid()) {
                    substitution_failed = true;
                } else {
                    collect_session_.remember_instantiation(memo_key, alias);
                    transaction.commit();
                    return alias;
                }
            }
        }
        if (substitution_failed) {
            if ((template_arguments_are_dependent(arguments) ||
                 deferred_on_enclosing_type_pack) &&
                target.valid()) {

                cir::EntityId alias =
                    collect_session_.create_alias_template_specialization(
                        info, arguments, target, loc);
                if (alias.valid()) {
                    collect_session_.remember_instantiation(memo_key, alias);
                    return alias;
                }
            }
            if (completion_mode ==
                collect::Session::TemplateArgumentCompletionMode::Candidate) {

                return {};
            }
            cir::TypeId resolved_target =
                collect_session_.file().resolved_type(target.type);
            const bool concrete_arguments =
                !template_arguments_are_dependent(arguments);
            bool diagnosed_specific_failure = false;
            if (concrete_arguments &&
                collect_session_.file().valid(resolved_target)) {
                cir::TypeKind target_kind =
                    collect_session_.file().type(resolved_target).kind;
                if (target_kind == cir::TypeKind::DependentName) {
                    const auto& dependent =
                        std::get<cir::DependentNameTypePayload>(
                            collect_session_.file().type_payload(
                                resolved_target));
                    diagnose(DiagnosticLevel::Error,
                             "no type named '" +
                                 collect_session_.file().name(
                                     dependent.member_name) +
                                 "' in typename qualifier",
                             loc);
                    diagnosed_specific_failure = true;
                } else if (target_kind ==
                           cir::TypeKind::PackIndex) {
                    const auto& pack_index =
                        std::get<cir::PackIndexTypePayload>(
                            collect_session_.file().type_payload(
                                resolved_target));
                    cir::TypeId pack_type =
                        collect_session_.file().resolved_type(
                            pack_index.pack_type.type);
                    const auto* parameter =
                        collect_session_.file().valid(pack_type)
                            ? std::get_if<cir::TypeParamTypePayload>(
                                  &collect_session_.file().type_payload(
                                      pack_type))
                            : nullptr;
                    collect::Session::TemplateArgumentBindings bindings;
                    collect::Session::PatternInstantiationCallbacks callbacks;
                    callbacks.access_loc = loc;
                    configure_pattern_instantiation_callbacks(
                        callbacks, loc);
                    if (parameter && parameter->is_parameter_pack &&
                        collect_session_
                            .bind_template_arguments_to_parameters(
                                info.parameters,
                                arguments,
                                bindings,
                                nullptr,
                                collect::Session::
                                    TemplateArgumentBindingMode::
                                        Canonical) &&
                        collect_session_
                            .populate_exact_template_parameter_bindings(
                                info, bindings, callbacks) &&
                        parameter->index < bindings.size() &&
                        bindings[parameter->index].is_pack()) {
                        collect::Session::TemplateArgument index;
                        index.kind =
                            cir::TemplateArgumentKind::Value;
                        index.value_type =
                            collect_session_.type_ref(
                                collect_session_.file().builtin_type(
                                    cir::BuiltinTypeKind::USize));
                        index.dependent_value_expr =
                            pack_index.index_expression;
                        index.is_dependent = true;
                        if (collect_session_
                                .substitute_template_value_argument(
                                    index, bindings, callbacks) &&
                            !index.is_dependent &&
                            (index.value_kind ==
                                 cir::TemplateValueKind::Integer ||
                             index.value_kind ==
                                 cir::TemplateValueKind::Boolean)) {
                            const size_t pack_size =
                                bindings[parameter->index]
                                    .arguments.size();
                            if (index.integer_value.is_negative()) {
                                diagnose(
                                    DiagnosticLevel::Error,
                                    "pack index is negative",
                                    loc);
                                diagnosed_specific_failure = true;
                            } else {
                                std::optional<uint64_t> converted =
                                    index.integer_value.try_as_uint64();
                                uint64_t value = converted.value_or(
                                    std::numeric_limits<uint64_t>::max());
                                if (value >= pack_size) {
                                    diagnose(
                                        DiagnosticLevel::Error,
                                        "pack index " +
                                            std::to_string(value) +
                                            " is out of bounds for pack "
                                            "of length " +
                                            std::to_string(pack_size),
                                        loc);
                                    diagnosed_specific_failure = true;
                                }
                            }
                        }
                    }
                }
            }
            if (!diagnosed_specific_failure && concrete_arguments &&
                collect_session_.file().valid(target.type)) {
                collect::Session::TemplateArgumentBindings bindings;
                collect::Session::PatternInstantiationCallbacks callbacks;
                callbacks.access_loc = loc;
                configure_pattern_instantiation_callbacks(callbacks, loc);
                if (collect_session_.bind_template_arguments_to_parameters(
                        info.parameters,
                        arguments,
                        bindings,
                        nullptr,
                        collect::Session::TemplateArgumentBindingMode::
                            Canonical) &&
                    collect_session_
                        .populate_exact_template_parameter_bindings(
                            info, bindings, callbacks) &&
                    collect_session_.type_pack_pattern_lengths_mismatch(
                        target.type, bindings, callbacks)) {
                    diagnose(DiagnosticLevel::Error,
                             "pack expansion contains packs with different "
                             "lengths",
                             loc);
                    diagnosed_specific_failure = true;
                }
            }
            if (!diagnosed_specific_failure) {
                diagnose(DiagnosticLevel::Error,
                         "alias template substitution failed",
                         loc);
            }
        }
        return {};
    }

    if (cir::EntityId current =
            collect_session_.current_instantiation_record(info, arguments);
        current.valid()) {
        return current;
    }
    if (collect_session_.validating_template_info() == &info) {

        cir::EntityId validation_entity =
            collect_session_.template_validation_entity(info);
        if (validation_entity.valid()) {
            std::string validation_memo_key =
                validation_entity == info.entity
                    ? memo_key
                    : collect_session_.template_memo_key(validation_entity,
                                                         arguments);
            cir::EntityId cached =
                collect_session_.cached_instantiation(validation_memo_key);
            const cir::RecordFacts* facts =
                cached.valid() && collect_session_.file().valid(cached) &&
                        collect_session_.file().entity(cached).kind ==
                            cir::EntityKind::Record
                    ? collect_session_.file().record_facts(cached)
                    : nullptr;
            if (facts && !facts->is_incomplete) {
                return cached;
            }
        }

        if (!info.is_class_template) {
            return {};
        }
        return collect_session_.create_dependent_record_specialization(
            info, arguments, loc);
    }

    bool has_dependent_argument = template_arguments_are_dependent(arguments);
    cir::EntityId incomplete_record_to_complete{};
    cir::EntityId function_declaration_to_complete{};
    if (cir::EntityId cached = collect_session_.cached_instantiation(memo_key);
        cached.valid()) {
        bool cached_function_declaration = is_function_template &&
            collect_session_.file().valid(cached) &&
            !collect_session_.file().entity(cached).is_definition;
        if (cached_function_declaration && info.has_definition) {
            function_declaration_to_complete = cached;
        } else if (has_dependent_argument || !info.is_class_template ||
            !collect_session_.file().valid(cached) ||
            collect_session_.file().entity(cached).kind !=
                cir::EntityKind::Record) {
            return cached;
        } else {
            const cir::RecordFacts* cached_facts =
                collect_session_.file().record_facts(cached);
            if (cached_facts && !cached_facts->is_incomplete) {
                return cached;
            }
            const cir::TemplateSpecializationFact* cached_specialization =
                collect_session_.file().template_specialization(cached);
            const cir::Entity& cached_entity =
                collect_session_.file().entity(cached);
            if (!cached_specialization ||
                cached_entity.lexical_context.valid() ||
                cached_entity.semantic_context.valid()) {
                return cached;
            }
            if (!materialize_class_definition) {
                return cached;
            }
            incomplete_record_to_complete = cached;
        }
    }
    if (has_dependent_argument) {

        if (!info.is_class_template && !info.is_variable_template) {
            return {};
        }
        cir::EntityId stub = info.is_variable_template
            ? collect_session_.create_dependent_variable_specialization(
                  info, arguments, loc)
            : collect_session_.create_dependent_record_specialization(
                  info, arguments, loc);
        collect_session_.remember_instantiation(memo_key, stub);
        return stub;
    }

    if (info.is_class_template && !incomplete_record_to_complete.valid()) {
        cir::EntityId shell =
            collect_session_.create_incomplete_record_specialization(
                info, arguments, loc);
        if (!shell.valid()) {
            return {};
        }

        collect_session_.remember_template_specialization(shell,
                                                        info,
                                                        arguments,
                                                        record_point_of_instantiation
                                                            ? loc
                                                            : SrcLoc(),
                                                        record_point_of_instantiation
                                                            ? point_lookup_generation
                                                            : 0);
        collect_session_.remember_instantiation(memo_key, shell);
        incomplete_record_to_complete = shell;
        if (!materialize_class_definition) {
            return shell;
        }
    }

    const collect::Session::TemplateInfo* replay_info = &info;
    std::vector<collect::Session::TemplateArgument> replay_arguments =
        arguments;
    collect::Session::TemplateArgumentBindings selected_argument_bindings;
    const collect::Session::TemplateArgumentBindings* replay_exact_bindings =
        exact_bindings;
    if ((info.is_class_template || info.is_variable_template) &&
        !info.is_partial_specialization) {
        collect::Session::PartialSpecializationSelection partial =
            select_template_partial_specialization(
                info,
                arguments,
                loc,
                point_lookup_generation);
        if (partial.is_ambiguous) {
            diagnose(DiagnosticLevel::Error,
                     std::string("ambiguous ") +
                         (info.is_variable_template ? "variable" : "class") +
                         " template partial specialization",
                     loc);
            for (SrcLoc candidate_loc : partial.candidate_locs) {
                diagnose(DiagnosticLevel::Note,
                         "candidate partial specialization declared here",
                         candidate_loc);
            }
            if (partial.has_unordered_associated_constraints) {
                diagnose(
                    DiagnosticLevel::Note,
                    "candidate associated constraints are not ordered by subsumption",
                    loc);
            }
            return {};
        }
        if (partial.info) {
            replay_info = partial.info;
            selected_argument_bindings =
                std::move(partial.argument_bindings);
            replay_arguments =
                collect_session_.flatten_template_argument_bindings(
                    selected_argument_bindings);
            replay_exact_bindings = &selected_argument_bindings;
        }
    }
    bool replay_declaration_only_function_template =
        !replay_info->has_definition && !replay_info->is_class_template &&
        !replay_info->is_variable_template && !replay_info->is_concept &&
        replay_info->entity.valid() &&
        collect_session_.file().valid(replay_info->entity) &&
        collect_session_.file().entity(replay_info->entity).kind ==
            cir::EntityKind::Function;
    bool replay_declaration_only_variable_template =
        !replay_info->has_definition && replay_info->is_variable_template &&
        replay_info->variable_is_extern;
    if (!replay_info->has_definition &&
        !replay_declaration_only_function_template &&
        !replay_declaration_only_variable_template) {
        if (info.is_class_template) {
            if (incomplete_record_to_complete.valid()) {
                return incomplete_record_to_complete;
            }
            cir::EntityId incomplete =
                collect_session_.create_incomplete_record_specialization(
                    info,
                    arguments,
                    loc);
            if (incomplete.valid()) {
                collect_session_.remember_instantiation(memo_key, incomplete);
            }
            return incomplete;
        }
        diagnose(DiagnosticLevel::Error,
                 "cannot instantiate undefined template '" + info.name + "'",
                 loc);
        return {};
    }

    struct ReplayOutcomeScopeExit {
        collect::Session* session = nullptr;
        collect::Session::TemplateReplayOutcome* previous = nullptr;
        collect::Session::TemplateReplayOutcome* current = nullptr;
        ~ReplayOutcomeScopeExit() {
            if (!session) {
                return;
            }
            session->set_template_replay_outcome(previous);
            if (!previous || !current) {
                return;
            }
            if (current->hard_error()) {
                previous->note_hard_error();
            } else if (current->unavailable()) {
                previous->note_unavailable(current->blocker);
            }
        }
    } replay_outcome_scope;
    collect::Session::TemplateReplayOutcome class_replay_outcome;
    std::unique_ptr<TentativeParsingAction> class_replay_transaction;
    size_t class_replay_error_watermark = 0;
    size_t class_replay_diagnostic_watermark = 0;
    bool transactional_class_replay =
        info.is_class_template && incomplete_record_to_complete.valid() &&
        materialize_class_definition;
    if (transactional_class_replay) {
        replay_outcome_scope.session = &collect_session_;
        replay_outcome_scope.previous =
            collect_session_.set_template_replay_outcome(
                &class_replay_outcome);
        replay_outcome_scope.current = &class_replay_outcome;
        class_replay_error_watermark =
            collect_session_.file().errors().size();
        class_replay_diagnostic_watermark = diagnostics_.size();
        class_replay_transaction =
            std::make_unique<TentativeParsingAction>(
                *this, TentativeMode::CollectBacked);
    }

    if (info.is_class_template && incomplete_record_to_complete.valid()) {
        if (const cir::TemplateSpecializationFact* stored =
                collect_session_.file().template_specialization(
                    incomplete_record_to_complete)) {
            cir::TemplateSpecializationFact fact = *stored;
            fact.selected_template_entity = replay_info->entity;
            if (replay_exact_bindings) {
                fact.selected_argument_bindings = *replay_exact_bindings;
            } else if (!collect_session_.bind_template_arguments_to_parameters(
                           replay_info->parameters,
                           replay_arguments,
                           fact.selected_argument_bindings)) {
                return {};
            }
            collect_session_.file().set_template_specialization(
                incomplete_record_to_complete, std::move(fact));
        }
    }

    collect::Session::InstantiationScope scope =
        collect_session_.begin_template_instantiation(*replay_info,
                                                      replay_arguments,
                                                      loc,
                                                      point_lookup_generation,
                                                      incomplete_record_to_complete,
                                                      replay_exact_bindings);
    if (!scope.active) {
        return {};
    }

    size_t saved_cursor = cursor_;
    size_t saved_last_end = last_consumed_raw_end_;
    int saved_pending_template_closes = pending_template_closes_;
    size_t saved_constraint_expression_replay_end =
        constraint_expression_replay_end_;
    std::vector<size_t> saved_template_argument_expression_begins =
        template_argument_expression_begins_;
    int saved_deferred_static_initializer_capture_depth =
        deferred_static_initializer_capture_depth_;
    cir::EntityId saved_deferred_static_initializer_dependency =
        deferred_static_initializer_dependency_;
    bool saved_deferred_static_initializer_probe_transaction_active =
        deferred_static_initializer_probe_transaction_active_;
    cursor_ = replay_info->definition_begin;

    pending_template_closes_ = 0;
    constraint_expression_replay_end_ = SIZE_MAX;
    template_argument_expression_begins_.clear();

    deferred_static_initializer_capture_depth_ = 0;
    deferred_static_initializer_dependency_ = {};
    deferred_static_initializer_probe_transaction_active_ = false;

    cir::EntityId instantiated{};
    if (replay_declaration_only_function_template &&
        collect_session_.is_hidden_friend_function_template(
            replay_info->entity)) {
        collect::Session::PatternInstantiationCallbacks callbacks;
        callbacks.point_lookup_generation = point_lookup_generation;
        callbacks.instantiate_type_template =
            [this, loc](
                cir::EntityId template_entity,
                std::vector<collect::Session::TemplateArgument> args,
                uint64_t nested_point_lookup_generation,
                bool materialize_type_template_definition,
                collect::Session::TemplateArgumentCompletionMode
                    completion_mode)
            -> cir::TypeRef {
            const collect::Session::TemplateInfo* target =
                collect_session_.template_info(template_entity);
            if (!target) {
                return {};
            }
            cir::EntityId record =
                instantiate_template_with_args(
                    *target,
                    std::move(args),
                    loc,
                    nested_point_lookup_generation,
                    false,
                    false,
                    materialize_type_template_definition,
                    true,
                    completion_mode);
            if (!record.valid()) {
                return {};
            }
            const cir::Entity& entity =
                collect_session_.file().entity(record);
            return {entity.type, entity.qualifiers, entity.memory_space};
        };
        instantiated =
            collect_session_.create_function_template_declaration_specialization(
                *replay_info,
                replay_arguments,
                callbacks,
                loc,
                {},
                replay_exact_bindings);
        if (instantiated.valid()) {
            collect_session_.remember_instantiation(memo_key, instantiated);
        }
    } else if (replay_info->is_class_template) {
        cir::TypeId type{};
        ExplicitClassTemplateSpecializationParse partial_replay_parse;
        ExplicitClassTemplateSpecializationParse* saved_specialization_parse =
            explicit_class_template_specialization_parse_;
        explicit_class_template_specialization_parse_ = nullptr;
        if (replay_info->is_partial_specialization) {
            partial_replay_parse.template_entity = info.entity;
            partial_replay_parse.is_partial_replay = true;
            partial_replay_parse.display_name =
                collect_session_.template_display_name(info, arguments);
            explicit_class_template_specialization_parse_ =
                &partial_replay_parse;
        }

        TemplateArgumentAccessExemptionScope access_exemption(
            collect_session_,
            replay_info->is_partial_specialization);
        (void)parse_record_specifier(&type);
        explicit_class_template_specialization_parse_ =
            saved_specialization_parse;
        if (type.valid()) {
            instantiated =
                collect_session_.file().record_entity(
                    collect_session_.file().resolved_type(type));
        }
        if (instantiated.valid()) {

            collect_session_.rename_entity(
                instantiated,
                collect_session_.template_display_name(info, arguments));
            collect_session_.remember_instantiation(memo_key, instantiated);
            collect_session_.remember_template_specialization(instantiated, info,
                                                            arguments,
                                                            loc,
                                                            0,
                                                            replay_info,
                                                            &replay_arguments,
                                                            exact_bindings,
                                                            replay_exact_bindings);
            for (const collect::Session::TemplateInfo::OutOfLineMember& member :
                 replay_info->out_of_line_members) {
                if (member.is_static_data_member_definition) {
                    continue;
                }
                cursor_ = member.begin;

                bool shadow_head =
                    !member.head_parameters.empty() &&
                    member.head_parameters.size() ==
                        member.head_parameter_owner_slots.size();
                if (shadow_head) {
                    for (uint32_t slot : member.head_parameter_owner_slots) {
                        if (slot >= arguments.size()) {
                            shadow_head = false;
                            break;
                        }
                    }
                }
                collect::Session::OutOfLineHeadRebinding head_rebinding;
                if (shadow_head) {
                    collect::Session::TemplateInfo head;
                    std::vector<collect::Session::TemplateArgument> reordered;
                    for (size_t j = 0;
                         j < member.head_parameters.size(); ++j) {
                        head.parameters.push_back(member.head_parameters[j]);
                        reordered.push_back(
                            arguments[member.head_parameter_owner_slots[j]]);
                    }
                    head_rebinding =
                        collect_session_.bind_out_of_line_member_head(
                            head, reordered, loc);
                }
                ParsedDecl member_decl = member.is_template_declaration
                    ? parse_cxx_template_declaration()
                    : parse_declaration(true);
                if (shadow_head) {
                    collect_session_.restore_out_of_line_member_head(
                        head_rebinding);
                }
                if (member_decl.sem.entity.valid()) {
                    cir::Entity& entity = collect_session_.file()
                                             .entity_mut(member_decl.sem.entity);
                    entity.linkage =
                        entity.suppressed_by_explicit_instantiation_declaration
                            ? cir::LinkageKind::External
                            : collect_session_.file().odr_linkage_for_entity(
                                  member_decl.sem.entity);
                }
            }
            collect_session_
                .apply_class_explicit_instantiation_declaration_suppression(
                    instantiated,
                    info,
                    arguments);
        }
    } else if (info.is_concept) {
        diagnose(DiagnosticLevel::Error,
                 "concept-id expressions are not supported yet",
                 loc);
    } else if (info.is_variable_template) {
        bool record_member_template =
            info.lexical_context.valid() &&
            collect_session_.file().decl_context(info.lexical_context).kind ==
                cir::DeclContextKind::Record;
        if (record_member_template) {
            DeclarationParser declaration_parser(
                *this,
                TypeParseContext::type_only(
                    TypeParseContext::Origin::MemberDeclSpecifier));
            cir::TypeRef base =
                declaration_parser.parse_declaration(false, true);
            ParsedDeclarator declarator =
                declaration_parser.parse_declarator(base, false);
            if (replay_info->is_partial_specialization &&
                check(TokenType::LESS_THAN)) {
                consume();
                int depth = 1;
                while (!at_end() && depth > 0) {
                    TokenType inner = current().type;
                    consume();
                    if (inner == TokenType::LESS_THAN) ++depth;
                    if (inner == TokenType::GREATER_THAN) --depth;
                    if (inner == TokenType::RIGHT_SHIFT) depth -= 2;
                }
            }
            ParsedAttributes trailing_attrs = try_parse_attributes();
            declarator.attrs.append(std::move(trailing_attrs.attrs));

            AttributeList attrs = declaration_parser.leading_attrs;
            attrs.append(declarator.attrs);
            declarator.attrs = std::move(attrs);
            declarator.type_ref =
                collect_session_.apply_type_attributes(declarator.type_ref,
                                                       declarator.attrs,
                                                       declarator.loc);
            declarator.type = declarator.type_ref.type;

            collect::DeclFlags flags;
            flags.is_constexpr = declaration_parser.is_constexpr;
            flags.is_consteval = declaration_parser.is_consteval;
            flags.is_constinit = declaration_parser.is_constinit;
            flags.is_inline = declaration_parser.is_inline;
            flags.is_thread_local = declaration_parser.is_thread_local;
            flags.is_extern =
                declaration_parser.storage_class == StorageClass::Extern;
            flags.is_static =
                declaration_parser.storage_class == StorageClass::Static;
            flags.is_auto_storage =
                declaration_parser.storage_class == StorageClass::Auto;
            flags.is_register =
                declaration_parser.storage_class == StorageClass::Register;
            flags.is_mutable = declaration_parser.is_mutable;
            flags.is_friend = declaration_parser.is_friend;
            flags.is_block_byref = declaration_parser.is_block_byref;
            flags.attrs = declarator.attrs;
            flags.type_qualifiers = declarator.type_ref.qualifiers;
            flags.vla_bounds = std::move(declarator.vla_bounds);

            std::string display =
                collect_session_.template_display_name(info, arguments);
            cir::DeclContextId member_context =
                declarator.qualified_context.valid()
                    ? declarator.qualified_context
                    : info.lexical_context;
            bool has_init_syntax =
                check(TokenType::ASSIGN) ||
                check(TokenType::LEFT_BRACE) ||
                (lang_opts_.is_cxx_mode() && check(TokenType::LEFT_PAREN));

            struct MemberTemplateScopeExit {
                collect::Session* session = nullptr;
                ~MemberTemplateScopeExit() {
                    if (session) {
                        session->leave_scope();
                    }
                }
            };

            collect::DeclResult declaration;
            {
                MemberTemplateScopeExit member_scope;
                collect_session_.enter_existing_context(
                    member_context,
                    collect::ScopeFlags::RecordScope);
                member_scope.session = &collect_session_;
                declaration =
                    collect_session_.declare_global_variable(display,
                                                             declarator.type,
                                                             std::nullopt,
                                                             declarator.loc,
                                                             flags,
                                                             has_init_syntax);
            }

            collect::ConstructorInitializationKind constructor_init_kind =
                check(TokenType::ASSIGN)
                    ? (peek(1).type == TokenType::LEFT_BRACE
                           ? collect::ConstructorInitializationKind::CopyList
                           : collect::ConstructorInitializationKind::Copy)
                    : collect::ConstructorInitializationKind::Direct;
            std::optional<collect::ExprResult> initializer;
            if (match(TokenType::ASSIGN)) {
                ParsedExpr init = parse_expression(PrecLevel::ASSIGNMENT);
                initializer = std::move(init.sem);
            } else if (check(TokenType::LEFT_BRACE)) {
                ParsedExpr init = parse_init_list_expression();
                initializer = std::move(init.sem);
            } else if (lang_opts_.is_cxx_mode() && check(TokenType::LEFT_PAREN)) {
                size_t init_begin = current_raw_index();
                consume();
                if (!check(TokenType::RIGHT_PAREN)) {
                    ParsedExpr init = parse_expression(PrecLevel::ASSIGNMENT);
                    initializer = std::move(init.sem);
                    while (match(TokenType::COMMA)) {
                        ParsedExpr extra =
                            parse_expression(PrecLevel::ASSIGNMENT);
                        (void)extra;
                        diagnose(DiagnosticLevel::Error,
                                 "direct initializers with multiple arguments require a class with a matching constructor",
                                 loc_for_index(init_begin));
                    }
                }
                if (!match(TokenType::RIGHT_PAREN)) {
                    diagnose(DiagnosticLevel::Error,
                             "expected ')' after initializer",
                             current_loc());
                }
            }

            cir::TypeId completed_type = declarator.type;
            if (initializer.has_value()) {
                completed_type =
                    collect_session_.complete_initializer_type(completed_type,
                                                              *initializer,
                                                              declarator.loc);
            }

            {
                MemberTemplateScopeExit member_scope;
                collect_session_.enter_existing_context(
                    member_context,
                    collect::ScopeFlags::RecordScope);
                member_scope.session = &collect_session_;
                declaration =
                    collect_session_.finish_variable_declaration(
                        std::move(declaration),
                        completed_type,
                        std::move(initializer),
                        declarator.loc,
                        flags,
                        {},
                        constructor_init_kind);
            }

            if (!match(TokenType::SEMICOLON)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ';' after static data member template definition",
                         current_loc());
                skip_until_statement_boundary();
            }
            instantiated = declaration.entity;
        } else if (replay_info->is_partial_specialization) {

            DeclarationParser partial_parser(
                *this,
                TypeParseContext::type_only(
                    TypeParseContext::Origin::NamespaceDeclSpecifier));
            cir::TypeRef base = partial_parser.parse_declaration(false, true);
            ParsedDeclarator declarator =
                partial_parser.parse_declarator(base, false);
            if (check(TokenType::LESS_THAN)) {
                consume();
                int depth = 1;
                while (!at_end() && depth > 0) {
                    TokenType inner = current().type;
                    consume();
                    if (inner == TokenType::LESS_THAN) ++depth;
                    if (inner == TokenType::GREATER_THAN) --depth;
                    if (inner == TokenType::RIGHT_SHIFT) depth -= 2;
                }
            }
            collect::DeclFlags flags;
            flags.is_constexpr = partial_parser.is_constexpr;
            flags.is_consteval = partial_parser.is_consteval;
            flags.is_constinit = partial_parser.is_constinit;
            flags.is_inline = partial_parser.is_inline;
            flags.is_thread_local = partial_parser.is_thread_local;
            flags.is_extern =
                partial_parser.storage_class == StorageClass::Extern;
            flags.is_static =
                partial_parser.storage_class == StorageClass::Static;
            flags.attrs = declarator.attrs;
            flags.type_qualifiers = declarator.type_ref.qualifiers;
            std::string display =
                collect_session_.template_display_name(info, arguments);
            bool has_init_syntax =
                check(TokenType::ASSIGN) ||
                check(TokenType::LEFT_BRACE) ||
                (lang_opts_.is_cxx_mode() && check(TokenType::LEFT_PAREN));
            collect::ConstructorInitializationKind constructor_init_kind =
                check(TokenType::ASSIGN)
                    ? (peek(1).type == TokenType::LEFT_BRACE
                           ? collect::ConstructorInitializationKind::CopyList
                           : collect::ConstructorInitializationKind::Copy)
                    : collect::ConstructorInitializationKind::Direct;
            collect::DeclResult declaration =
                collect_session_.declare_global_variable(display,
                                                         declarator.type,
                                                         std::nullopt,
                                                         declarator.loc,
                                                         flags,
                                                         has_init_syntax);
            std::optional<collect::ExprResult> initializer;
            if (match(TokenType::ASSIGN)) {
                if (check(TokenType::LEFT_BRACE)) {
                    ParsedExpr init = parse_init_list_expression();
                    initializer = std::move(init.sem);
                } else {
                    ParsedExpr init = parse_expression(PrecLevel::ASSIGNMENT);
                    initializer = std::move(init.sem);
                }
            } else if (check(TokenType::LEFT_BRACE)) {
                ParsedExpr init = parse_init_list_expression();
                initializer = std::move(init.sem);
            } else if (lang_opts_.is_cxx_mode() && check(TokenType::LEFT_PAREN)) {
                size_t init_begin = current_raw_index();
                consume();
                if (!check(TokenType::RIGHT_PAREN)) {
                    ParsedExpr init = parse_expression(PrecLevel::ASSIGNMENT);
                    initializer = std::move(init.sem);
                    while (match(TokenType::COMMA)) {
                        ParsedExpr extra =
                            parse_expression(PrecLevel::ASSIGNMENT);
                        (void)extra;
                        diagnose(DiagnosticLevel::Error,
                                 "direct initializers with multiple arguments require a class with a matching constructor",
                                 loc_for_index(init_begin));
                    }
                }
                if (!match(TokenType::RIGHT_PAREN)) {
                    diagnose(DiagnosticLevel::Error,
                             "expected ')' after initializer",
                             current_loc());
                }
            }
            cir::TypeId completed_type = declarator.type;
            if (initializer.has_value()) {
                completed_type =
                    collect_session_.complete_initializer_type(completed_type,
                                                               *initializer,
                                                               declarator.loc);
            }
            declaration = collect_session_.finish_variable_declaration(
                std::move(declaration),
                completed_type,
                std::move(initializer),
                declarator.loc,
                flags,
                {},
                constructor_init_kind);
            instantiated = declaration.entity;
        } else {
            ParsedDecl declaration = parse_declaration(true);
            instantiated = declaration.sem.entity;
        }
        if (instantiated.valid()) {
            collect_session_.file().entity_mut(instantiated).linkage =
                replay_info->has_definition
                    ? (replay_info->has_internal_linkage
                           ? cir::LinkageKind::Internal
                           : cir::LinkageKind::LinkOnceODR)
                    : cir::LinkageKind::External;
            collect_session_.rename_entity(
                instantiated,
                collect_session_.template_display_name(info, arguments));
            collect_session_.remember_instantiation(memo_key, instantiated);
            collect_session_.remember_template_specialization(
                instantiated,
                info,
                arguments,
                loc,
                point_lookup_generation,
                replay_info,
                &replay_arguments,
                exact_bindings,
                replay_exact_bindings);
        }
    } else if (info.entity.valid() &&
               collect_session_.file().valid(info.entity) &&
               ([&]() {
                   const cir::Entity& entity =
                       collect_session_.file().entity(info.entity);
                   if (entity.kind == cir::EntityKind::Method ||
                       entity.kind == cir::EntityKind::Constructor ||
                       entity.kind == cir::EntityKind::Destructor) {
                       return true;
                   }
                   return info.is_member_template_specialization_overlay &&
                       entity.kind == cir::EntityKind::Function &&
                       entity.semantic_context.valid() &&
                       collect_session_.file().valid(
                           entity.semantic_context) &&
                       collect_session_.file()
                               .decl_context(entity.semantic_context)
                               .kind == cir::DeclContextKind::Record;
               })()) {
        instantiated = instantiate_member_function_template(
            info,
            arguments,
            loc,
            function_declaration_to_complete,
            exact_bindings);
        if (instantiated.valid()) {
            collect_session_.remember_instantiation(memo_key, instantiated);
        }
    } else {
        bool clone_attempted = lang_opts_.template_pattern_cloning &&
            info.pattern_usable && info.pattern_function.valid();
        if (clone_attempted) {
            instantiated =
                instantiate_function_template_by_clone(
                    info,
                    arguments,
                    loc,
                    function_declaration_to_complete,
                    exact_bindings);
        }
        if (instantiated.valid()) {
            record_template_clone_instantiation(/*member=*/false);
        }
        if (!instantiated.valid()) {
            if (replay_info->has_definition) {
                record_template_replay_fallback(
                    clone_attempted,
                    /*member=*/false,
                    collect_session_.template_display_name(info, arguments),
                    loc);
            }
            ParsedDecl declaration;
            {
                struct MaterializationTargetExit {
                    collect::Session* session = nullptr;
                    cir::EntityId previous{};
                    ~MaterializationTargetExit() {
                        if (session) {
                            session->set_function_template_materialization_target(
                                previous);
                        }
                    }
                } target_exit;
                if (function_declaration_to_complete.valid()) {
                    target_exit.session = &collect_session_;
                    target_exit.previous =
                        collect_session_
                            .set_function_template_materialization_target(
                                function_declaration_to_complete);
                }
                collect::Session::LookupGenerationCeilingScope ceiling(
                    collect_session_,
                    info.definition_generation);
                declaration = parse_declaration(true);
            }
            instantiated = declaration.sem.entity;
            if (instantiated.valid()) {
                collect_session_.file().entity_mut(instantiated).linkage =
                    replay_info->has_definition
                        ? cir::LinkageKind::LinkOnceODR
                        : cir::LinkageKind::External;
            }
        }
        if (instantiated.valid()) {
            collect_session_.rename_entity(
                instantiated,
                collect_session_.template_display_name(info, arguments));
            collect_session_.remember_instantiation(memo_key, instantiated);
            collect_session_.remember_template_specialization(instantiated, info,
                                                            arguments,
                                                            loc,
                                                            0,
                                                            nullptr,
                                                            nullptr,
                                                            exact_bindings);
        }
    }
    if (instantiated.valid()) {
        collect_session_.apply_explicit_instantiation_declaration_suppression(
            instantiated,
            info,
            arguments);
    }
    cursor_ = saved_cursor;
    last_consumed_raw_end_ = saved_last_end;
    pending_template_closes_ = saved_pending_template_closes;
    constraint_expression_replay_end_ =
        saved_constraint_expression_replay_end;
    template_argument_expression_begins_ =
        std::move(saved_template_argument_expression_begins);
    deferred_static_initializer_capture_depth_ =
        saved_deferred_static_initializer_capture_depth;
    deferred_static_initializer_dependency_ =
        saved_deferred_static_initializer_dependency;
    deferred_static_initializer_probe_transaction_active_ =
        saved_deferred_static_initializer_probe_transaction_active;

    collect_session_.finish_template_instantiation(std::move(scope));

    if (class_replay_transaction) {
        const cir::RecordFacts* facts =
            instantiated.valid() &&
                    collect_session_.file().valid(instantiated)
                ? collect_session_.file().record_facts(instantiated)
                : nullptr;
        bool completed_canonical_shell =
            instantiated == incomplete_record_to_complete && facts &&
            !facts->is_incomplete;
        bool collect_had_error =
            collect_session_.file().errors().size() >
            class_replay_error_watermark;
        bool parser_had_error = std::any_of(
            diagnostics_.begin() +
                static_cast<std::ptrdiff_t>(
                    class_replay_diagnostic_watermark),
            diagnostics_.end(),
            [](const Diagnostic& diagnostic) {
                return diagnostic.level == DiagnosticLevel::Error &&
                    !diagnostic.suppressed;
            });

        if (class_replay_outcome.unavailable()) {

            class_replay_transaction->revert();
            instantiated = incomplete_record_to_complete;
        } else if (class_replay_outcome.hard_error() ||
                   collect_had_error || parser_had_error ||
                   !completed_canonical_shell) {
            class_replay_outcome.note_hard_error();
            std::vector<std::pair<SrcLoc, std::string>> captured_errors(
                collect_session_.file().errors().begin() +
                    static_cast<std::ptrdiff_t>(
                        class_replay_error_watermark),
                collect_session_.file().errors().end());
            std::vector<Diagnostic> captured_parser_diagnostics(
                diagnostics_.begin() +
                    static_cast<std::ptrdiff_t>(
                        class_replay_diagnostic_watermark),
                diagnostics_.end());
            class_replay_transaction->revert();
            for (auto& [error_loc, message] : captured_errors) {
                collect_session_.file().add_error(std::move(message),
                                                  error_loc);
            }
            diagnostics_.insert(
                diagnostics_.end(),
                std::make_move_iterator(
                    captured_parser_diagnostics.begin()),
                std::make_move_iterator(
                    captured_parser_diagnostics.end()));
            instantiated = {};
        } else {
            class_replay_transaction->commit();
        }
    }

    if (!instantiated.valid()) {
        diagnose(DiagnosticLevel::Error,
                 "instantiation of template '" + info.name + "' failed",
                 loc);
    }
    return instantiated;
}

collect::Session::InstantiationDemandResult
Parser::materialize_function_demand(
    cir::EntityId specialization,
    cir::InstantiationDemandKind kind,
    SrcLoc loc) {
    using Result = collect::Session::InstantiationDemandResult;
    const cir::File& file = collect_session_.file();
    if (!specialization.valid() || !file.valid(specialization)) {
        return Result::Failed;
    }
    uint64_t specialization_key =
        static_cast<uint64_t>(specialization.index);
    if (deferred_hidden_friend_bodies_.count(specialization_key) ||
        file.entity(specialization).result_type_only_definition) {
        return force_deferred_hidden_friend_body(specialization, kind)
            ? Result::Satisfied
            : Result::Failed;
    }
    if (file.entity(specialization).is_definition) {
        return Result::Satisfied;
    }
    const cir::RecordMethodFact* method =
        file.method_fact(specialization);
    if (method && method->inherited_constructor &&
        file.template_specialization(specialization)) {
        return collect_session_
                   .define_inherited_constructor_template_specialization(
                       specialization, loc)
            ? Result::Satisfied
            : Result::Failed;
    }
    if (file.entity(specialization).is_explicit_template_specialization) {
        return Result::Unavailable;
    }
    const cir::TemplateSpecializationFact* fact =
        file.template_specialization(specialization);
    if (!fact || !fact->template_entity.valid()) {
        return Result::Unavailable;
    }
    const collect::Session::TemplateInfo* info =
        collect_session_.template_info(fact->template_entity);
    if (!info) {
        return Result::Failed;
    }

    // [temp.point]p8
    if (kind == cir::InstantiationDemandKind::OdrUse &&
        !draining_odr_instantiations_ &&
        !file.entity(specialization).placeholder_result.valid() &&
        !collect_session_.function_has_placeholder_return(
            file.entity(specialization).type)) {
        queue_odr_instantiation(specialization,
                                OdrInstantiationOwner::FunctionDemand);
        return Result::Satisfied;
    }

    if (!info->has_definition) {
        diagnose(DiagnosticLevel::Error,
                 "cannot instantiate undefined template '" + info->name +
                     "'",
                 loc);
        return Result::Failed;
    }
    cir::EntityId materialized = instantiate_template_with_args(
        *info,
        fact->template_arguments(),
        loc,
        fact->point_lookup_generation,
        /*replay_guard_entered=*/false,
        /*arguments_are_canonical=*/true,
        /*materialize_class_definition=*/true,
        /*record_point_of_instantiation=*/true,
        collect::Session::TemplateArgumentCompletionMode::Required,
        &fact->argument_bindings);
    if (!materialized.valid() || materialized != specialization ||
        !collect_session_.file().entity(specialization).is_definition) {
        return Result::Failed;
    }
    if (kind == cir::InstantiationDemandKind::ResultType) {
        collect_session_.file().entity_mut(specialization)
            .result_type_only_definition = true;
        cir::PlaceholderResultFactId placeholder =
            collect_session_.file().entity(specialization)
                .placeholder_result;
        if (collect_session_.file().valid(placeholder)) {
            collect_session_.file()
                .placeholder_result_fact_mut(placeholder)
                .result_only_materialization = true;
        }
    }
    return Result::Satisfied;
}

collect::Session::InstantiationDemandResult Parser::materialize_class_demand(
    cir::EntityId specialization,
    cir::InstantiationDemandKind kind,
    cir::EntityId subject,
    SrcLoc loc) {
    using Result = collect::Session::InstantiationDemandResult;
    const cir::File& file = collect_session_.file();
    if (!specialization.valid() || !file.valid(specialization)) {
        return Result::Failed;
    }
    const cir::TemplateSpecializationFact* fact =
        file.template_specialization(specialization);
    if (!fact || !fact->template_entity.valid()) {
        return Result::Failed;
    }
    const collect::Session::TemplateInfo* info =
        collect_session_.template_info(fact->template_entity);
    if (!info || !info->is_class_template) {
        return Result::Failed;
    }

    if (kind == cir::InstantiationDemandKind::DeclarationSet) {
        cir::EntityId materialized = instantiate_template_with_args(
            *info,
            fact->template_arguments(),
            loc,
            fact->point_lookup_generation,
            /*replay_guard_entered=*/false,
            /*arguments_are_canonical=*/true,
            /*materialize_class_definition=*/true);
        if (!materialized.valid()) {
            return Result::Failed;
        }
        const cir::RecordFacts* facts =
            collect_session_.file().record_facts(materialized);
        return facts && !facts->is_incomplete ? Result::Satisfied
                                              : Result::Unavailable;
    }

    if (!subject.valid() || !file.valid(subject)) {
        return Result::Failed;
    }
    const cir::Entity& entity = file.entity(subject);
    if (entity.kind == cir::EntityKind::Record) {
        const cir::RecordFacts* facts = file.record_facts(subject);
        if (facts && !facts->is_incomplete) {
            return Result::Satisfied;
        }
        return force_deferred_member_class_definition(subject)
            ? Result::Satisfied
            : Result::Unavailable;
    }
    if (entity.is_definition &&
        !(kind == cir::InstantiationDemandKind::ConstantEvaluation &&
          entity.kind == cir::EntityKind::Variable &&
          !entity.has_constant_value)) {
        return Result::Satisfied;
    }
    if (entity.kind == cir::EntityKind::Variable) {
        return force_deferred_template_static_data_member_definition(subject,
                                                                     kind)
            ? Result::Satisfied
            : Result::Unavailable;
    }
    if (entity.kind == cir::EntityKind::Method ||
        entity.kind == cir::EntityKind::Constructor ||
        entity.kind == cir::EntityKind::Destructor) {
        // [temp.point]p8: the odr-use is not the point of instantiation for
        // the body. Queue it and let the end-of-unit drain instantiate it, so
        // the specialization sees declarations written after the use -- an
        // explicit specialization, most importantly. A deduced return type is
        // the exception: the use needs the body now to know its own type.
        if (kind == cir::InstantiationDemandKind::OdrUse &&
            !entity.placeholder_result.valid() &&
            !collect_session_.function_has_placeholder_return(entity.type)) {
            queue_odr_instantiation(subject,
                                    OdrInstantiationOwner::MemberBody);
            return Result::Satisfied;
        }

        // A member-function-template specialization is a function-template
        // specialization, even though its enclosing class owns the outer
        // demand. For an immediate semantic demand, route it through the
        // function-template materializer so its exact member-template
        // arguments and reusable body recipe are used. Ordinary odr-use stays
        // on the deferred member path above: that path also owns late explicit
        // specialization visibility and structor ABI wrapper emission.
        // [temp.inst] requires immediate materialization when the definition
        // affects semantics, including when needed for constant evaluation.
        if (kind == cir::InstantiationDemandKind::ConstantEvaluation ||
            kind == cir::InstantiationDemandKind::ResultType) {
            const cir::TemplateSpecializationFact* member_specialization =
                file.template_specialization(subject);
            if (member_specialization &&
                member_specialization->template_entity.valid()) {
                const collect::Session::TemplateInfo* member_template =
                    collect_session_.template_info(
                        member_specialization->template_entity);
                if (member_template &&
                    !member_template->is_class_template &&
                    !member_template->is_alias_template &&
                    !member_template->is_variable_template &&
                    !member_template->is_concept) {
                    return materialize_function_demand(subject, kind, loc);
                }
            }
        }
        return force_deferred_template_member_body(
                   subject,
                   kind != cir::InstantiationDemandKind::ConstantEvaluation &&
                       kind != cir::InstantiationDemandKind::ResultType)
            ? Result::Satisfied
            : Result::Unavailable;
    }
    if (entity.kind == cir::EntityKind::Enum) {
        return force_deferred_scoped_enum_definition(subject)
            ? Result::Satisfied
            : Result::Unavailable;
    }
    return Result::Unavailable;
}

bool Parser::register_source_late_out_of_line_member_body(
    cir::EntityId member_entity) {
    const cir::File& file = collect_session_.file();
    if (!member_entity.valid() || !file.valid(member_entity)) {
        return false;
    }
    const cir::Entity& member_record = file.entity(member_entity);
    SrcLoc member_loc = member_record.loc;
    bool method_kind =
        member_record.kind == cir::EntityKind::Method ||
        member_record.kind == cir::EntityKind::Constructor ||
        member_record.kind == cir::EntityKind::Destructor;
    cir::EntityId record_entity = member_record.parent;
    if (!method_kind || !record_entity.valid() ||
        !file.valid(record_entity)) {
        return false;
    }
    const cir::TemplateSpecializationFact* fact =
        file.template_specialization(record_entity);
    if (!fact || !fact->template_entity.valid()) {
        return false;
    }
    const collect::Session::TemplateInfo* info =
        collect_session_.template_info(fact->template_entity);
    if (!info) {
        return false;
    }

    const collect::Session::TemplateInfo* replay_info = info;
    std::vector<collect::Session::TemplateArgument> replay_arguments =
        fact->template_arguments();
    uint64_t point_lookup_generation = fact->point_lookup_generation;
    collect::Session::TemplateArgumentBindings replay_argument_bindings;
    const collect::Session::TemplateArgumentBindings* replay_exact_bindings =
        nullptr;
    if (fact->selected_template_entity.valid()) {
        if (const collect::Session::TemplateInfo* selected =
                collect_session_.template_info(
                    fact->selected_template_entity)) {
            replay_info = selected;
            replay_arguments = fact->selected_template_arguments();
            if (fact->selected_argument_bindings.size() ==
                selected->parameters.size()) {
                replay_argument_bindings =
                    fact->selected_argument_bindings;
                replay_exact_bindings = &replay_argument_bindings;
            }
        }
    } else if (info->is_class_template &&
               !info->is_partial_specialization) {
        collect::Session::PartialSpecializationSelection partial =
            select_template_partial_specialization(
                *info,
                replay_arguments,
                member_loc,
                point_lookup_generation);
        if (partial.is_ambiguous) {
            return false;
        }
        if (partial.info) {
            replay_info = partial.info;
            replay_argument_bindings =
                std::move(partial.argument_bindings);
            replay_arguments =
                collect_session_.flatten_template_argument_bindings(
                    replay_argument_bindings);
            replay_exact_bindings = &replay_argument_bindings;
        }
    }
    if (replay_info->out_of_line_members.empty()) {
        return false;
    }

    // A direct member explicit-instantiation declaration can complete the
    // owning class before a source-later out-of-line member definition is
    // registered on the class-template recipe. Recover that one definition
    // lazily when the exact member is odr-used. Probe each retained entry
    // transactionally so siblings never acquire bodies or semantic state.
    TemplateReplayGuardExit replay_guard{&collect_session_, false};
    if (!collect_session_.enter_template_replay_guard(member_loc)) {
        return false;
    }
    replay_guard.active = true;

    struct ParserReplayStateExit {
        Parser* parser = nullptr;
        size_t cursor = 0;
        size_t last_consumed_raw_end = 0;
        int pending_template_closes = 0;
        size_t constraint_expression_replay_end = SIZE_MAX;
        std::vector<size_t> template_argument_expression_begins;

        ~ParserReplayStateExit() {
            if (!parser) {
                return;
            }
            parser->cursor_ = cursor;
            parser->last_consumed_raw_end_ = last_consumed_raw_end;
            parser->pending_template_closes_ = pending_template_closes;
            parser->constraint_expression_replay_end_ =
                constraint_expression_replay_end;
            parser->template_argument_expression_begins_ =
                std::move(template_argument_expression_begins);
        }
    } replay_state_exit{
        this,
        cursor_,
        last_consumed_raw_end_,
        pending_template_closes_,
        constraint_expression_replay_end_,
        template_argument_expression_begins_};
    pending_template_closes_ = 0;
    constraint_expression_replay_end_ = SIZE_MAX;
    template_argument_expression_begins_.clear();

    auto parse_entry =
        [&](const collect::Session::TemplateInfo::OutOfLineMember& member) {
            cursor_ = member.begin;
            bool shadow_head =
                !member.head_parameters.empty() &&
                member.head_parameters.size() ==
                    member.head_parameter_owner_slots.size();
            if (shadow_head) {
                for (uint32_t slot :
                     member.head_parameter_owner_slots) {
                    if (slot >= replay_arguments.size()) {
                        shadow_head = false;
                        break;
                    }
                }
            }
            collect::Session::OutOfLineHeadRebinding head_rebinding;
            if (shadow_head) {
                collect::Session::TemplateInfo head;
                std::vector<collect::Session::TemplateArgument> reordered;
                for (size_t index = 0;
                     index < member.head_parameters.size();
                     ++index) {
                    head.parameters.push_back(
                        member.head_parameters[index]);
                    reordered.push_back(
                        replay_arguments[
                            member.head_parameter_owner_slots[index]]);
                }
                head_rebinding =
                    collect_session_.bind_out_of_line_member_head(
                        head, reordered, member_loc);
            }
            ParsedDecl result = parse_declaration(true);
            if (shadow_head) {
                collect_session_.restore_out_of_line_member_head(
                    head_rebinding);
            }
            return result;
        };
    auto entry_matches =
        [&](const collect::Session::TemplateInfo::OutOfLineMember& member) {
            if (member.is_static_data_member_definition ||
                member.is_template_declaration) {
                return false;
            }
            bool matches = false;
            {
                RevertingTentativeParsingAction tentative(
                    *this,
                    TentativeMode::CollectBacked);
                ParsedDecl probe = parse_entry(member);
                matches = probe.sem.entity == member_entity;
            }
            return matches;
        };

    std::optional<collect::Session::TemplateInfo::OutOfLineMember> selected;
    collect::Session::InstantiationScope probe_scope =
        collect_session_.begin_template_instantiation(
            *replay_info,
            replay_arguments,
            member_loc,
            point_lookup_generation,
            {},
            replay_exact_bindings);
    if (!probe_scope.active) {
        return false;
    }
    for (const collect::Session::TemplateInfo::OutOfLineMember& member :
        replay_info->out_of_line_members) {
        if (entry_matches(member)) {
            selected = member;
            break;
        }
    }
    collect_session_.finish_template_instantiation(std::move(probe_scope));
    if (!selected) {
        return false;
    }

    collect::Session::InstantiationScope replay_scope =
        collect_session_.begin_template_instantiation(
            *replay_info,
            replay_arguments,
            member_loc,
            point_lookup_generation,
            {},
            replay_exact_bindings);
    if (!replay_scope.active) {
        return false;
    }
    ParsedDecl member_decl = parse_entry(*selected);
    collect_session_.finish_template_instantiation(std::move(replay_scope));
    return member_decl.sem.entity == member_entity &&
           deferred_template_bodies_.count(
               static_cast<uint64_t>(member_entity.index)) != 0;
}

bool Parser::force_deferred_template_static_data_member_definition(
    cir::EntityId member_entity,
    cir::InstantiationDemandKind demand_kind) {
    const cir::File& file = collect_session_.file();
    if (!member_entity.valid() || !file.valid(member_entity)) {
        return false;
    }
    const cir::Entity& member_record = file.entity(member_entity);
    if (member_record.kind != cir::EntityKind::Variable) {
        return false;
    }
    if (member_record.has_constant_value &&
        demand_kind ==
            cir::InstantiationDemandKind::ConstantEvaluation) {
        return true;
    }
    if (member_record.is_definition &&
        demand_kind !=
            cir::InstantiationDemandKind::ConstantEvaluation) {
        return true;
    }
    if (collect_session_.explicit_static_data_member_specialization_declared(
            member_entity)) {
        return false;
    }
    if (demand_kind ==
            cir::InstantiationDemandKind::ConstantEvaluation) {
        if (const cir::RecordStaticDataMemberFact* member =
                collect_session_.record_static_data_member_fact(
                    member_entity);
            member && member->has_in_class_initializer &&
            member->initializer_begin < member->initializer_end &&
            ((member_record.qualifiers & cir::QualConst) ||
             member_record.decl_flags.is_constexpr) &&
            cir::is_integer_like_type(file, member_record.type)) {
            return routed_in_class_static_data_member_materialization(
                member_entity);
        }
    }
    if (member_record.is_definition) {
        return true;
    }

    cir::EntityId record_entity = member_record.parent;
    if (!record_entity.valid() || !file.valid(record_entity)) {
        return false;
    }
    const cir::TemplateSpecializationFact* fact =
        file.template_specialization(record_entity);
    if (!fact || !fact->template_entity.valid()) {
        return false;
    }
    const collect::Session::TemplateInfo* info =
        collect_session_.template_info(fact->template_entity);
    if (!info) {
        return false;
    }
    const collect::Session::TemplateInfo* replay_info = info;
    std::vector<collect::Session::TemplateArgument> replay_arguments =
        fact->template_arguments();
    collect::Session::TemplateArgumentBindings selected_argument_bindings;
    const collect::Session::TemplateArgumentBindings* replay_exact_bindings =
        nullptr;
    if (fact->selected_template_entity.valid()) {
        if (const collect::Session::TemplateInfo* selected =
                collect_session_.template_info(
                    fact->selected_template_entity)) {
            replay_info = selected;
            replay_arguments = fact->selected_template_arguments();
            if (fact->selected_argument_bindings.size() ==
                selected->parameters.size()) {
                replay_exact_bindings =
                    &fact->selected_argument_bindings;
            }
        }
    } else if (info->is_class_template &&
               !info->is_partial_specialization) {
        collect::Session::PartialSpecializationSelection partial =
            select_template_partial_specialization(
                *info,
                replay_arguments,
                member_record.loc,
                fact->point_lookup_generation);
        if (partial.is_ambiguous) {
            return false;
        }
        if (partial.info) {
            replay_info = partial.info;
            selected_argument_bindings =
                std::move(partial.argument_bindings);
            replay_arguments =
                collect_session_.flatten_template_argument_bindings(
                    selected_argument_bindings);
            replay_exact_bindings = &selected_argument_bindings;
        }
    }
    TemplateReplayGuardExit replay_guard{&collect_session_, false};
    if (!collect_session_.enter_template_replay_guard(member_record.loc)) {
        return false;
    }
    replay_guard.active = true;

    auto entry_matches =
        [&](const collect::Session::TemplateInfo::OutOfLineMember& member) {
        if (!member.is_static_data_member_definition) {
            return false;
        }
        bool matches = false;
        size_t saved_cursor = cursor_;
        size_t saved_last_end = last_consumed_raw_end_;
        {
            RevertingTentativeParsingAction tentative(
                *this,
                TentativeMode::CollectBacked);
            cursor_ = member.begin;
            ParsedDecl probe = parse_declaration(true);
            matches = probe.sem.entity == member_entity;
        }
        cursor_ = saved_cursor;
        last_consumed_raw_end_ = saved_last_end;
        return matches;
    };

    const collect::Session::TemplateInfo::OutOfLineMember* selected = nullptr;
    collect::Session::InstantiationScope probe_scope =
        collect_session_.begin_template_instantiation(
            *replay_info,
            replay_arguments,
            file.entity(member_entity).loc,
            fact->point_lookup_generation,
            {},
            replay_exact_bindings);
    if (!probe_scope.active) {
        return false;
    }
    for (const collect::Session::TemplateInfo::OutOfLineMember& member :
         replay_info->out_of_line_members) {
        if (entry_matches(member)) {
            selected = &member;
            break;
        }
    }
    collect_session_.finish_template_instantiation(std::move(probe_scope));
    if (!selected) {
        return false;
    }

    size_t saved_cursor = cursor_;
    size_t saved_last_end = last_consumed_raw_end_;
    collect::Session::InstantiationScope replay_scope =
        collect_session_.begin_template_instantiation(
            *replay_info,
            replay_arguments,
            file.entity(member_entity).loc,
            fact->point_lookup_generation,
            {},
            replay_exact_bindings);
    if (!replay_scope.active) {
        return false;
    }
    cursor_ = selected->begin;
    ParsedDecl member_decl = parse_declaration(true);
    if (member_decl.sem.entity.valid()) {
        cir::Entity& entity =
            collect_session_.file().entity_mut(member_decl.sem.entity);
        entity.linkage = entity.suppressed_by_explicit_instantiation_declaration
            ? cir::LinkageKind::External
            : collect_session_.file().odr_linkage_for_entity(
                  member_decl.sem.entity);
    }
    cursor_ = saved_cursor;
    last_consumed_raw_end_ = saved_last_end;
    collect_session_.finish_template_instantiation(std::move(replay_scope));

    return member_decl.sem.entity == member_entity &&
           collect_session_.file().entity(member_entity).is_definition;
}

bool Parser::routed_in_class_static_data_member_materialization(
    cir::EntityId member_entity) {
    const cir::File& file = collect_session_.file();
    if (!member_entity.valid() || !file.valid(member_entity)) {
        return false;
    }
    cir::EntityId owner = file.entity(member_entity).parent;
    cir::EntityId route = owner.valid() && file.valid(owner)
        ? module_pattern_identity(owner)
        : cir::EntityId{};
    if (!module_unit_parser_for(route)) {
        route = member_entity;
    }
    if (Parser* home = module_unit_parser_for(route)) {
        collect::Session::ModuleVisibilityOverride visibility(
            collect_session_, file.entity(route).origin_unit);
        return home->materialize_deferred_in_class_static_data_member(
            member_entity);
    }
    return materialize_deferred_in_class_static_data_member(member_entity);
}

bool Parser::materialize_deferred_in_class_static_data_member(
    cir::EntityId member_entity) {
    struct ParserReplayStateExit {
        Parser* parser = nullptr;
        size_t cursor = 0;
        size_t last_consumed_raw_end = 0;
        int pending_template_closes = 0;
        size_t constraint_expression_replay_end = SIZE_MAX;
        std::vector<size_t> template_argument_expression_begins;

        ~ParserReplayStateExit() {
            if (!parser) {
                return;
            }
            parser->cursor_ = cursor;
            parser->last_consumed_raw_end_ = last_consumed_raw_end;
            parser->pending_template_closes_ = pending_template_closes;
            parser->constraint_expression_replay_end_ =
                constraint_expression_replay_end;
            parser->template_argument_expression_begins_ =
                std::move(template_argument_expression_begins);
        }
    } replay_state_exit{
        this,
        cursor_,
        last_consumed_raw_end_,
        pending_template_closes_,
        constraint_expression_replay_end_,
        template_argument_expression_begins_};

    pending_template_closes_ = 0;
    constraint_expression_replay_end_ = SIZE_MAX;
    template_argument_expression_begins_.clear();

    enum class EvalStatus : uint8_t {
        Value,
        Dependency,
        Invalid,
    };
    struct EvalResult {
        EvalStatus status = EvalStatus::Invalid;
        int64_t value = 0;
        cir::EntityId dependency{};
    };
    struct RecipeParseResult {
        bool success = false;
        cir::EntityId dependency{};
    };

    cir::File& file = collect_session_.file();
    std::vector<cir::EntityId> work;
    std::unordered_set<uint64_t> active;
    std::unordered_map<uint64_t, collect::ExprResult>
        initializer_expressions;
    work.push_back(member_entity);
    active.insert(static_cast<uint64_t>(member_entity.index));

    auto member_fact =
        [&](cir::EntityId entity)
            -> std::optional<cir::RecordStaticDataMemberFact> {
        if (const cir::RecordStaticDataMemberFact* fact =
                collect_session_.record_static_data_member_fact(entity)) {
            return *fact;
        }
        return std::nullopt;
    };

    auto retain_expression =
        [&](cir::EntityId entity,
            cir::TemplateValueExpression expression) -> bool {
        if (!entity.valid() || !file.valid(entity)) {
            return false;
        }
        cir::EntityId owner = file.entity(entity).parent;
        const cir::RecordFacts* facts = file.record_facts(owner);
        if (!facts) {
            return false;
        }
        file.canonicalize_template_value_expression(expression);
        cir::RecordFacts updated = *facts;
        for (cir::RecordStaticDataMemberFact& member :
             updated.static_data_members) {
            if (member.entity != entity) {
                continue;
            }
            member.initializer_value_expression = std::move(expression);
            file.set_record_facts(owner, std::move(updated));
            return true;
        }
        return false;
    };

    auto parse_expression_recipe =
        [&](cir::EntityId entity,
            const cir::RecordStaticDataMemberFact& fact)
            -> RecipeParseResult {
        cir::EntityId owner = file.entity(entity).parent;
        bool use_current_validation_scope =
            owner.valid() &&
            owner == collect_session_.current_validation_record();
        collect::Session::InstantiationScope scope;
        if (!use_current_validation_scope &&
            !collect_session_.begin_member_instantiation_scope(entity,
                                                               scope)) {
            return {};
        }
        if (!owner.valid() || !file.valid(owner) ||
            !file.entity(owner).semantic_context.valid()) {
            if (!use_current_validation_scope) {
                collect_session_.finish_template_instantiation(
                    std::move(scope));
            }
            return {};
        }
        if (!use_current_validation_scope) {
            collect_session_.enter_existing_context(
                file.entity(owner).semantic_context,
                collect::ScopeFlags::RecordScope);
        }
        size_t saved_cursor = cursor_;
        size_t saved_last_end = last_consumed_raw_end_;
        int saved_pending_template_closes = pending_template_closes_;
        seek_raw_index(fact.initializer_begin);
        ParserCheckpoint dependency_probe_checkpoint =
            capture_parser_checkpoint();
        collect_session_.begin_speculative_parse();
        cir::EntityId saved_dependency =
            deferred_static_initializer_dependency_;
        bool saved_probe_transaction_active =
            deferred_static_initializer_probe_transaction_active_;
        deferred_static_initializer_dependency_ = {};
        deferred_static_initializer_probe_transaction_active_ = true;
        bool has_assignment = match(TokenType::ASSIGN);
        ++deferred_static_initializer_capture_depth_;
        ParsedExpr initializer;
        if (has_assignment) {
            initializer = check(TokenType::LEFT_BRACE)
                ? parse_init_list_expression()
                : parse_expression(PrecLevel::ASSIGNMENT);
            if (!initializer.sem.has_error) {
                initializer.sem = collect_session_.convert_to(
                    std::move(initializer.sem),
                    file.entity(entity).type,
                    collect::UseContext::Init,
                    fact.initializer_loc);
            }
        }
        --deferred_static_initializer_capture_depth_;
        cir::EntityId dependency =
            deferred_static_initializer_dependency_;
        deferred_static_initializer_dependency_ = saved_dependency;
        deferred_static_initializer_probe_transaction_active_ =
            saved_probe_transaction_active;
        bool consumed_recipe =
            has_assignment && !initializer.sem.has_error &&
            current_raw_index() == fact.initializer_end;
        if (dependency.valid()) {
            collect_session_.rollback_speculative_parse();
            restore_parser_checkpoint(dependency_probe_checkpoint);
        } else if (consumed_recipe) {
            collect_session_.commit_speculative_parse();
        } else {
            collect_session_.rollback_speculative_parse();
            restore_parser_checkpoint(dependency_probe_checkpoint);
        }
        cursor_ = saved_cursor;
        last_consumed_raw_end_ = saved_last_end;
        pending_template_closes_ = saved_pending_template_closes;
        if (!use_current_validation_scope) {
            collect_session_.leave_scope();
            collect_session_.finish_template_instantiation(
                std::move(scope));
        }
        if (dependency.valid()) {
            return {true, dependency};
        }
        if (!consumed_recipe) {
            return {};
        }
        if (initializer.sem.template_value_expr.valid()) {
            (void)retain_expression(
                entity, initializer.sem.template_value_expr);
        }
        initializer_expressions[static_cast<uint64_t>(entity.index)] =
            std::move(initializer.sem);
        return {true, {}};
    };

    auto queue_dependency = [&](cir::EntityId dependency) {
        if (!dependency.valid() || !file.valid(dependency)) {
            return false;
        }
        uint64_t key = static_cast<uint64_t>(dependency.index);
        if (active.count(key) != 0) {
            collect_session_.report_error(
                "recursive static data member constant initialization",
                file.entity(dependency).loc);
            return false;
        }
        if (work.size() >=
            collect_session_.template_instantiation_depth_limit()) {
            collect_session_.report_error(
                "template instantiation depth limit exceeded",
                file.entity(dependency).loc);
            size_t notes = 0;
            for (auto it = work.rbegin();
                 it != work.rend() && notes < 8;
                 ++it, ++notes) {
                collect_session_.report_note(
                    "in static data member constant initialization of '" +
                        file.format_entity(*it) + "'",
                    file.entity(*it).loc);
            }
            return false;
        }
        active.insert(key);
        work.push_back(dependency);
        return true;
    };

    while (!work.empty()) {
        cir::EntityId current = work.back();
        if (!current.valid() || !file.valid(current)) {
            return false;
        }
        if (file.entity(current).has_constant_value) {
            active.erase(static_cast<uint64_t>(current.index));
            work.pop_back();
            continue;
        }
        std::optional<cir::RecordStaticDataMemberFact> fact =
            member_fact(current);
        if (!fact.has_value() || !fact->has_in_class_initializer ||
            fact->initializer_begin >= fact->initializer_end) {
            return false;
        }
        uint64_t current_key = static_cast<uint64_t>(current.index);
        if (initializer_expressions.count(current_key) == 0) {
            RecipeParseResult parsed =
                parse_expression_recipe(current, *fact);
            if (!parsed.success) {
                return false;
            }
            if (parsed.dependency.valid()) {
                if (!queue_dependency(parsed.dependency)) {
                    return false;
                }
                continue;
            }
            fact = member_fact(current);
            if (!fact.has_value()) {
                return false;
            }
        }

        EvalResult result;
        int64_t value = 0;
        cir::EntityId dependency{};
        if (collect_session_.try_evaluate_required_integer_constant(
                initializer_expressions.at(current_key),
                value,
                fact->initializer_loc)) {
            result = {EvalStatus::Value, value, {}};
        } else {
            if (collect_session_.try_evaluate_integer_constant(
                    initializer_expressions.at(current_key),
                    value,
                    &dependency)) {
                result = {EvalStatus::Value, value, {}};
            } else if (dependency.valid()) {
                result = {EvalStatus::Dependency, 0, dependency};
            }
        }
        if (result.status == EvalStatus::Dependency) {
            if (!queue_dependency(result.dependency)) {
                return false;
            }
            continue;
        }
        if (result.status != EvalStatus::Value) {
            return false;
        }

        cir::Entity& current_entity = file.entity_mut(current);
        if (current_entity.is_template_pattern) {

            current_entity.has_constant_value = true;
            cir::IntegerTypeShape shape = cir::integer_shape_for_type(
                file, current_entity.type);
            current_entity.constant_integer_value =
                cir::IntegerValue::from_signed(result.value, 64).cast(
                    shape.bit_width, shape.is_unsigned);
            active.erase(static_cast<uint64_t>(current.index));
            work.pop_back();
            continue;
        }

        cir::TypeId declaration_type = file.entity(current).type;
        SrcLoc declaration_loc = file.entity(current).loc;
        collect::ExprResult literal =
            collect_session_.make_integer_literal(
                result.value,
                std::to_string(result.value),
                declaration_type,
                declaration_loc);
        if (!collect_session_
                 .materialize_record_static_data_member_initializer(
                     current,
                     declaration_type,
                     literal,
                     declaration_loc)) {
            return false;
        }
        active.erase(static_cast<uint64_t>(current.index));
        work.pop_back();
    }
    return file.valid(member_entity) &&
        file.entity(member_entity).has_constant_value;
}

void Parser::materialize_deferred_static_data_member_expr(
    collect::ExprResult& expression) {
    if (deferred_static_initializer_capture_depth_ != 0) {

        if (template_argument_expression_begins_.empty() &&
            constraint_expression_replay_end_ == SIZE_MAX) {
            return;
        }
        if (!expression.entity.valid() ||
            !collect_session_.file().valid(expression.entity)) {
            return;
        }
        cir::File& file = collect_session_.file();
        const cir::Entity& entity = file.entity(expression.entity);
        const cir::RecordStaticDataMemberFact* member =
            collect_session_.record_static_data_member_fact(
                expression.entity);
        bool deferred_integral_constant =
            member && member->has_in_class_initializer &&
            member->initializer_begin < member->initializer_end &&
            ((entity.qualifiers & cir::QualConst) ||
             entity.decl_flags.is_constexpr) &&
            cir::is_integer_like_type(file, entity.type) &&
            !entity.has_constant_value;
        if (!deferred_integral_constant) {
            return;
        }
        if (!deferred_static_initializer_dependency_.valid()) {

            if (deferred_static_initializer_probe_transaction_active_) {
                collect_session_.commit_speculative_parse();
                collect_session_.begin_speculative_parse();
            }
            deferred_static_initializer_dependency_ = expression.entity;
        }
        std::string name = expression.name;
        cir::EntityId dependency = expression.entity;
        expression = collect_session_.make_integer_literal(
            0, "0", entity.type, entity.loc);
        expression.entity = dependency;
        expression.name = std::move(name);
        return;
    }
    if (!expression.entity.valid() ||
        !collect_session_.file().valid(expression.entity) ||
        collect_session_.file().entity(expression.entity).kind !=
            cir::EntityKind::Variable) {
        return;
    }
    cir::File& file = collect_session_.file();
    const cir::Entity entity_before_demand =
        file.entity(expression.entity);
    cir::InstantiationDemandKind demand_kind =
        cir::InstantiationDemandKind::OdrUse;
    if (const cir::RecordStaticDataMemberFact* member =
            collect_session_.record_static_data_member_fact(
                expression.entity);
        member && member->has_in_class_initializer &&
        member->initializer_begin < member->initializer_end &&
        ((entity_before_demand.qualifiers & cir::QualConst) ||
         entity_before_demand.decl_flags.is_constexpr) &&
        cir::is_integer_like_type(file, entity_before_demand.type)) {
        demand_kind =
            cir::InstantiationDemandKind::ConstantEvaluation;
    }
    bool demand_satisfied = false;
    if (demand_kind ==
            cir::InstantiationDemandKind::ConstantEvaluation &&
        !entity_before_demand.has_constant_value) {

        demand_satisfied =
            routed_in_class_static_data_member_materialization(
                expression.entity);
    } else {
        demand_satisfied =
            collect_session_.request_class_member_instantiation(
                expression.entity,
                demand_kind,
                entity_before_demand.loc) ==
            collect::Session::InstantiationDemandResult::Satisfied;
    }
    if (!demand_satisfied) {
        return;
    }
    const cir::Entity& entity = file.entity(expression.entity);
    if (collect_session_.contains_auto_type(entity.type) ||
        collect_session_.is_dependent_type(entity.type)) {

        return;
    }
    cir::TypeRef object_type = file.type_ref(entity.type,
                                             entity.qualifiers,
                                             entity.memory_space);
    if (!expression.place.valid() || !file.valid(expression.place)) {
        expression.type = entity.type;
        return;
    }
    cir::Inst& place = file.inst_mut(expression.place);
    cir::TypeRef expression_object_type = object_type;
    cir::TypeId resolved_entity_type = file.resolved_type(entity.type);
    bool reference_entity =
        file.valid(resolved_entity_type) &&
        (file.type(resolved_entity_type).kind ==
             cir::TypeKind::LValueReference ||
         file.type(resolved_entity_type).kind ==
             cir::TypeKind::RValueReference);
    if (reference_entity && place.kind == cir::InstKind::Deref) {

        expression_object_type =
            file.reference_referred_ref(resolved_entity_type);
    }
    expression.type = expression_object_type.type;
    place.result_type = file.place_type(expression_object_type);
    if (place.place_fact.valid()) {
        file.place_fact_mut(place.place_fact).object_type =
            expression_object_type;
    }
}

void Parser::force_class_explicit_instantiation_definition_members(
    cir::EntityId record_entity,
    SrcLoc instantiation_loc) {

    const cir::File& file = collect_session_.file();
    std::unordered_set<uint64_t> visited_records;

    auto instantiate_members = [&](auto&& self, cir::EntityId record) -> void {
        if (!record.valid() || !file.valid(record) ||
            !visited_records.insert(static_cast<uint64_t>(record.index)).second) {
            return;
        }

        const cir::RecordFacts* facts = file.record_facts(record);
        if (!facts || facts->is_incomplete) {
            return;
        }

        std::vector<cir::EntityId> methods;
        methods.reserve(facts->methods.size());
        for (const cir::RecordMethodFact& method : facts->methods) {
            methods.push_back(method.entity);
        }
        std::vector<cir::EntityId> static_data_members;
        static_data_members.reserve(facts->static_data_members.size());
        for (const cir::RecordStaticDataMemberFact& member :
             facts->static_data_members) {
            static_data_members.push_back(member.entity);
        }

        for (cir::EntityId method : methods) {
            if (!method.valid() || !file.valid(method) ||
                collect_session_.template_info(method) ||
                file.entity(method)
                    .attr_facts.is_excluded_from_explicit_instantiation ||
                collect_session_.explicit_member_function_specialization_declared(
                    method)) {
                continue;
            }
            const cir::RecordMethodFact* method_fact =
                file.method_fact(method);
            if (!method_fact ||
                method_fact->constraint_satisfaction ==
                    cir::ConstraintSatisfactionKind::Unsatisfied ||
                method_fact->constraint_satisfaction ==
                    cir::ConstraintSatisfactionKind::Invalid) {
                continue;
            }
            (void)collect_session_.request_class_member_instantiation(
                method,
                cir::InstantiationDemandKind::MemberDefinition,
                instantiation_loc);
            if (!file.valid(method) || !file.entity(method).is_definition) {
                continue;
            }
            collect_session_.declare_explicit_entity_instantiation_definition(
                method,
                instantiation_loc);
            collect_session_.apply_explicit_entity_instantiation_definition_emission(
                method);
        }

        for (cir::EntityId member : static_data_members) {
            if (!member.valid() || !file.valid(member) ||
                collect_session_.template_info(member) ||
                file.entity(member)
                    .attr_facts.is_excluded_from_explicit_instantiation ||
                collect_session_.explicit_static_data_member_specialization_declared(
                    member)) {
                continue;
            }
            (void)collect_session_.request_class_member_instantiation(
                member,
                cir::InstantiationDemandKind::MemberDefinition,
                instantiation_loc);
            if (!file.valid(member) || !file.entity(member).is_definition) {
                continue;
            }
            collect_session_.declare_explicit_entity_instantiation_definition(
                member,
                instantiation_loc);
            collect_session_.apply_explicit_entity_instantiation_definition_emission(
                member);
        }

        std::vector<cir::EntityId> nested_records;
        std::unordered_set<uint64_t> seen_nested;
        cir::DeclContextId context = file.entity(record).semantic_context;
        if (context.valid() && file.valid(context)) {
            for (cir::BindingId binding_id :
                 file.decl_context(context).bindings) {
                if (!binding_id.valid() || !file.valid(binding_id)) {
                    continue;
                }
                for (cir::EntityId candidate : file.binding(binding_id).entities) {
                    if (!candidate.valid() || !file.valid(candidate) ||
                        candidate == record ||
                        file.entity(candidate).kind != cir::EntityKind::Record ||
                        collect_session_.template_info(candidate) ||
                        !seen_nested
                             .insert(static_cast<uint64_t>(candidate.index))
                             .second) {
                        continue;
                    }
                    const cir::RecordFacts* nested_facts =
                        file.record_facts(candidate);
                    if (!nested_facts || nested_facts->is_incomplete) {
                        (void)collect_session_
                            .request_class_member_instantiation(
                                candidate,
                                cir::InstantiationDemandKind::CompleteClass,
                                instantiation_loc);
                        nested_facts = file.record_facts(candidate);
                    }
                    if (nested_facts && !nested_facts->is_incomplete) {
                        nested_records.push_back(candidate);
                    }
                }
            }
        }

        for (cir::EntityId nested : nested_records) {
            collect_session_.declare_explicit_entity_instantiation_definition(
                nested,
                instantiation_loc);
            collect_session_.apply_record_explicit_instantiation_definition_emission(
                nested);
            self(self, nested);
            collect_session_.apply_record_explicit_instantiation_definition_emission(
                nested);
        }
    };

    instantiate_members(instantiate_members, record_entity);
}

void Parser::record_template_clone_instantiation(bool member) {
    if (auto* profiler = active_perf_profiler()) {
        profiler->add_counter(
            member ? PerfCounter::TemplateMemberCloneInstantiations
                   : PerfCounter::TemplateFunctionCloneInstantiations);
    }
}

void Parser::record_template_replay_fallback(bool clone_attempted,
                                             bool member,
                                             std::string display,
                                             SrcLoc loc) {
    if (auto* profiler = active_perf_profiler()) {
        profiler->add_counter(
            member ? (clone_attempted
                          ? PerfCounter::TemplateMemberCloneFallbacks
                          : PerfCounter::TemplateMemberTokenReplays)
                   : (clone_attempted
                          ? PerfCounter::TemplateFunctionCloneFallbacks
                          : PerfCounter::TemplateFunctionTokenReplays));
    }
    if (!lang_opts_.template_fallback_notes) {
        return;
    }
    std::string message = "'" + std::move(display) +
        "' instantiated by token replay: ";
    if (clone_attempted) {
        message += collect::Session::pattern_clone_bail_text(
            collect_session_.last_pattern_clone_bail());
    } else if (!lang_opts_.template_pattern_cloning) {
        message += "pattern cloning disabled";
    } else {
        message += "no usable pattern";
    }
    diagnose(DiagnosticLevel::Note, std::move(message), loc);
}

cir::EntityId Parser::instantiate_member_function_template(
    const collect::Session::TemplateInfo& info,
    const std::vector<collect::Session::TemplateArgument>& arguments,
    SrcLoc loc,
    cir::EntityId declaration_shell,
    const collect::Session::TemplateArgumentBindings* exact_bindings) {
    std::optional<collect::Session::TemplateArgumentBindings>
        inferred_bindings;
    if (!exact_bindings) {
        inferred_bindings = canonical_template_argument_bindings(
            collect_session_, info.parameters, arguments);
        if (!inferred_bindings.has_value()) {
            return {};
        }
        exact_bindings = &*inferred_bindings;
    }
    collect::Session::PatternInstantiationCallbacks callbacks;
    callbacks.instantiate_type_template =
        [this, loc](
            cir::EntityId template_entity,
            std::vector<collect::Session::TemplateArgument> args,
            uint64_t point_lookup_generation,
            bool materialize_type_template_definition,
            collect::Session::TemplateArgumentCompletionMode completion_mode)
        -> cir::TypeRef {
        const collect::Session::TemplateInfo* target =
            collect_session_.template_info(template_entity);
        if (!target) {
            return {};
        }
        cir::EntityId record =
            instantiate_template_with_args(
                *target,
                std::move(args),
                loc,
                point_lookup_generation,
                false,
                false,
                materialize_type_template_definition,
                true,
                completion_mode);
        if (!record.valid()) {
            return {};
        }
        const cir::Entity& entity =
            collect_session_.file().entity(record);
        return {entity.type, entity.qualifiers, entity.memory_space};
    };
    if (!collect_session_.populate_exact_template_parameter_bindings(
            info, *exact_bindings, callbacks)) {
        return {};
    }

    cir::TypeId declared_type =
        collect_session_.substitute_pattern_type(info.pattern_type,
                                                 *exact_bindings,
                                                 callbacks);
    if (!declared_type.valid()) {
        return {};
    }
    cir::EntityId specialization = declaration_shell;
    if (!specialization.valid() ||
        !collect_session_.file().valid(specialization)) {
        specialization =
            collect_session_.create_member_template_specialization(info,
                                                                   arguments,
                                                                   declared_type,
                                                                   loc,
                                                                   nullptr,
                                                                   exact_bindings);
    }
    if (!specialization.valid()) {
        return {};
    }

    collect_session_.file().entity_mut(specialization).is_template_pattern =
        false;
    if (info.explicit_specifier == cir::ExplicitSpecifierKind::Dependent) {
        std::optional<bool> explicit_value =
            resolve_member_specialization_explicit_specifier(
                info, arguments, specialization, loc,
                exact_bindings);
        if (!explicit_value.has_value()) {
            return {};
        }
    }

    struct LambdaFrameGuard {
        collect::Session* session = nullptr;
        ~LambdaFrameGuard() {
            if (session) {
                session->pop_lambda_instantiation_frame();
            }
        }
    } lambda_frame_guard;
    {
        const cir::File& file = collect_session_.file();
        cir::EntityId owner = file.entity(specialization).parent;
        const cir::RecordFacts* owner_facts = file.record_facts(owner);
        if (owner_facts && owner_facts->is_lambda_closure) {
            collect_session_.push_lambda_instantiation_frame(specialization);
            lambda_frame_guard.session = &collect_session_;
            // Every closure's specializations would otherwise share the
            // "operator()<T>" display name as their linkage-name fallback
            // (no Itanium lambda mangling yet); rename assembler-clean and
            // unique, like the primary ".lambda.N.op".
            std::string unique_name;
            if (owner.valid() && file.entity(owner).name.valid()) {
                unique_name = std::string(file.name(file.entity(owner).name));
            } else {
                unique_name = ".lambda";
            }
            unique_name += ".op.";
            unique_name += std::to_string(specialization.index);
            collect_session_.rename_entity(specialization, unique_name);
            collect_session_.file().entity_mut(specialization).linkage =
                cir::LinkageKind::Internal;
        }
    }

    bool deduced_return_pending = collect_session_.contains_auto_type(
        declared_type, cir::AutoTypeFlavor::Cxx);

    auto body_it = member_template_bodies_.find(
        static_cast<uint64_t>(info.entity.index));
    const PendingMemberBody* captured_body =
        body_it == member_template_bodies_.end() ? nullptr : &body_it->second;

    auto instantiate_body_parameters =
        [&](const std::vector<ParsedParam>& pattern_params)
            -> std::optional<std::vector<ParsedParam>> {
        std::vector<ParsedParam> concrete;
        concrete.reserve(pattern_params.size());
        for (const ParsedParam& pattern_param : pattern_params) {
            cir::TypeRef source_type = pattern_param.type_ref.type.valid()
                ? pattern_param.type_ref
                : collect_session_.type_ref(pattern_param.type);
            if (pattern_param.is_parameter_pack) {
                std::optional<std::vector<cir::TypeRef>> expanded_types =
                    collect_session_
                        .substitute_pattern_function_parameter_pack(
                            source_type,
                            *exact_bindings,
                            callbacks);
                if (!expanded_types.has_value()) {
                    return std::nullopt;
                }
                std::string source_name =
                    pattern_param.name != "<anonymous>"
                        ? pattern_param.name
                        : std::string{};
                if (expanded_types->empty()) {
                    ParsedParam sentinel = pattern_param;
                    sentinel.syntax = InvalidNodeId;
                    sentinel.prototype_entity = {};
                    sentinel.is_parameter_pack = false;
                    sentinel.source_parameter_pack_name = source_name;
                    sentinel.is_parameter_pack_expansion_sentinel = true;
                    concrete.push_back(std::move(sentinel));
                    continue;
                }
                size_t element_index = 0;
                for (cir::TypeRef substituted : *expanded_types) {
                    ParsedParam expanded = pattern_param;
                    expanded.syntax = element_index == 0
                        ? pattern_param.syntax
                        : InvalidNodeId;
                    expanded.name = source_name.empty()
                        ? "<anonymous>"
                        : source_name + "." +
                              std::to_string(element_index);
                    expanded.type = substituted.type;
                    expanded.type_ref = substituted;
                    expanded.prototype_entity = {};
                    expanded.is_parameter_pack = false;
                    expanded.source_parameter_pack_name = source_name;
                    expanded.is_parameter_pack_expansion_sentinel = false;
                    concrete.push_back(std::move(expanded));
                    ++element_index;
                }
                continue;
            }
            concrete.push_back(pattern_param);
        }
        for (ParsedParam& param : concrete) {
            if (param.is_parameter_pack_expansion_sentinel) {
                param.prototype_entity = {};
                continue;
            }
            cir::TypeRef source_type = param.type_ref.type.valid()
                ? param.type_ref
                : collect_session_.type_ref(param.type);
            cir::TypeRef substituted =
                collect_session_.substitute_pattern_type_ref(
                    source_type, *exact_bindings, callbacks);
            adjust_function_parameter_type(substituted);
            if (!substituted.valid()) {
                return std::nullopt;
            }
            param.type = substituted.type;
            param.type_ref = substituted;
            param.prototype_entity = {};
        }
        return concrete;
    };

    const collect::Session::MemberPattern* member = nullptr;
    for (const collect::Session::MemberPattern& candidate :
         info.member_patterns) {
        if (candidate.method == info.entity) {
            member = &candidate;
            break;
        }
    }
    if (!member && info.member_patterns.size() == 1) {
        member = &info.member_patterns.front();
    }
    bool clone_attempted = false;
    if (lang_opts_.template_pattern_cloning && member && member->usable &&
        !deduced_return_pending) {
        clone_attempted = true;
        TentativeParsingAction transaction(
            *this, TentativeMode::CollectBacked);
        callbacks.replay_statement =
            [this, &info](const collect::Session::PatternHole& hole) {
                size_t saved_cursor = cursor_;
                size_t saved_last_end = last_consumed_raw_end_;
                int saved_closes = pending_template_closes_;
                cursor_ = hole.token_begin;
                pending_template_closes_ = 0;
                collect::Session::LookupGenerationCeilingScope ceiling(
                    collect_session_,
                    info.definition_generation);
                ParsedStmt stmt = parse_statement();
                cursor_ = saved_cursor;
                last_consumed_raw_end_ = saved_last_end;
                pending_template_closes_ = saved_closes;
                return std::move(stmt.sem);
            };
        if (captured_body &&
            collect_session_.file().entity(specialization).kind ==
                cir::EntityKind::Constructor) {
            callbacks.collect_subobject_init = [this, &info, captured_body]() {
                std::vector<collect::Session::MemberInitializerInput>
                    initializers;
                collect::Session::LookupGenerationCeilingScope ceiling(
                    collect_session_,
                    info.definition_generation);
                if (captured_body->init_begin != captured_body->init_end) {
                    size_t saved_cursor = cursor_;
                    size_t saved_last_end = last_consumed_raw_end_;
                    cursor_ = captured_body->init_begin;
                    parse_member_initializer_list(initializers,
                                                  captured_body->init_end);
                    cursor_ = saved_cursor;
                    last_consumed_raw_end_ = saved_last_end;
                }
                collect::StmtResult init =
                    collect_session_.collect_constructor_initializers(
                        std::move(initializers), current_loc());
                return init;
            };
        }
        std::optional<std::vector<ParsedParam>> instantiated_body_params =
            captured_body
                ? instantiate_body_parameters(captured_body->params)
                : std::optional<std::vector<ParsedParam>>(
                      std::vector<ParsedParam>{});
        std::vector<collect::ParamInput> instantiated_params =
            instantiated_body_params.has_value()
                ? param_inputs_from_parsed_params(
                      *instantiated_body_params,
                      /*move_runtime_fragments=*/false)
                : std::vector<collect::ParamInput>{};
        bool cloned = instantiated_body_params.has_value() &&
            collect_session_.clone_member_pattern(info,
                                                  *member,
                                                  specialization,
                                                  arguments,
                                                  instantiated_params,
                                                  callbacks,
                                                  loc,
                                                  exact_bindings);
        if (cloned) {
            collect_session_.file().entity_mut(specialization).linkage =
                collect_session_.file().odr_linkage_for_entity(specialization);
            transaction.commit();
            record_template_clone_instantiation(/*member=*/true);
            return specialization;
        }
        transaction.revert();
    }

    if (!captured_body) {
        return {};
    }
    record_template_replay_fallback(
        clone_attempted,
        /*member=*/true,
        collect_session_.template_display_name(info, arguments),
        loc);
    PendingMemberBody concrete_body = *captured_body;
    std::optional<std::vector<ParsedParam>> concrete_params =
        instantiate_body_parameters(concrete_body.params);
    if (!concrete_params.has_value()) {
        return {};
    }
    concrete_body.params = std::move(*concrete_params);
    {
        collect::Session::LookupGenerationCeilingScope ceiling(
            collect_session_,
            info.definition_generation);
        replay_member_body(specialization, concrete_body);
    }
    return specialization;
}

cir::EntityId Parser::instantiate_function_template_by_clone(
    const collect::Session::TemplateInfo& info,
    const std::vector<collect::Session::TemplateArgument>& arguments,
    SrcLoc loc,
    cir::EntityId declaration_shell,
    const collect::Session::TemplateArgumentBindings* exact_bindings) {

    if (collect_session_.contains_auto_type(info.pattern_type,
                                            cir::AutoTypeFlavor::Cxx)) {
        return {};
    }

    TentativeParsingAction transaction(
        *this, TentativeMode::CollectBacked);
    collect::Session::PatternInstantiationCallbacks callbacks;
    configure_pattern_instantiation_callbacks(callbacks, loc);
    callbacks.replay_statement =
        [this, &info](const collect::Session::PatternHole& hole) {
            size_t saved_cursor = cursor_;
            size_t saved_last_end = last_consumed_raw_end_;
            int saved_closes = pending_template_closes_;
            cursor_ = hole.token_begin;
            pending_template_closes_ = 0;

            collect::Session::LookupGenerationCeilingScope ceiling(
                collect_session_,
                info.definition_generation);
            ParsedStmt stmt = parse_statement();
            cursor_ = saved_cursor;
            last_consumed_raw_end_ = saved_last_end;
            pending_template_closes_ = saved_closes;
            return std::move(stmt.sem);
        };
    cir::EntityId cloned =
        collect_session_.clone_pattern_function(info,
                                                arguments,
                                                callbacks,
                                                loc,
                                                declaration_shell,
                                                exact_bindings);
    if (cloned.valid()) {
        transaction.commit();
    } else {
        transaction.revert();
    }
    return cloned;
}

} // namespace aburi::syntax
