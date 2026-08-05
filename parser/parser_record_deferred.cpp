#include "parser.h"

#include <algorithm>
#include <functional>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace aburi::syntax {

namespace {

collect::ScopeFlags scope_flags_for_complete_class_context(
    const cir::File& file,
    cir::DeclContextId context) {
    if (!context.valid() || !file.valid(context)) {
        return collect::ScopeFlags::None;
    }
    switch (file.decl_context(context).kind) {
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
}

} // namespace

bool Parser::has_incomplete_enclosing_record(cir::EntityId record) const {
    const cir::File& file = collect_session_.file();
    if (!record.valid() || !file.valid(record)) {
        return false;
    }
    cir::DeclContextId context = file.entity(record).semantic_context;
    if (context.valid() && file.valid(context)) {
        context = file.decl_context(context).parent;
    }
    while (context.valid() && file.valid(context)) {
        const cir::DeclContext& declaration_context = file.decl_context(context);
        if (declaration_context.kind == cir::DeclContextKind::Record &&
            declaration_context.owner.valid() &&
            file.valid(declaration_context.owner)) {
            const cir::RecordFacts* facts =
                file.record_facts(declaration_context.owner);
            if (facts && facts->is_incomplete) {
                return true;
            }
        }
        context = declaration_context.parent;
    }
    return false;
}

void Parser::finalize_pending_member_templates(
    std::vector<PendingMemberTemplate> pending,
    const std::vector<cir::EntityId>& method_entities) {

    for (PendingMemberTemplate& member : pending) {
        if (member.method_index >= method_entities.size() ||
            !method_entities[member.method_index].valid()) {
            continue;
        }
        cir::EntityId method_entity = method_entities[member.method_index];
        if (member.info.has_complete_class_default_recipes &&
            member.info.complete_class_head_end >
                member.info.complete_class_head_begin) {
            size_t saved_cursor = cursor_;
            size_t saved_last_end = last_consumed_raw_end_;
            int saved_template_closes = pending_template_closes_;
            cursor_ = member.info.complete_class_head_begin;
            pending_template_closes_ = 0;

            bool entered = false;
            cir::DeclContextId context = member.info.lexical_context;
            collect::ScopeFlags flags =
                scope_flags_for_complete_class_context(
                    collect_session_.file(), context);
            if (flags != collect::ScopeFlags::None) {
                collect::ScopeEnterResult scope =
                    collect_session_.enter_existing_context(context, flags);
                entered = scope.scope != collect::InvalidScopeId;
            }
            collect::Session::TemplateInfo replayed;
            uint32_t parameter_depth = member.info.parameters.empty()
                ? 0
                : member.info.parameters.front().depth;
            bool replay_ok = parse_cxx_template_head(replayed,
                                                     member.loc,
                                                     parameter_depth);
            if (entered) {
                collect_session_.leave_scope();
            }
            cursor_ = saved_cursor;
            last_consumed_raw_end_ = saved_last_end;
            pending_template_closes_ = saved_template_closes;

            if (replay_ok &&
                replayed.parameters.size() == member.info.parameters.size()) {
                for (size_t i = 0; i < member.info.parameters.size(); ++i) {
                    if (!member.info.parameters[i]
                             .requires_complete_class_default_replay) {
                        continue;
                    }
                    member.info.parameters[i].default_argument =
                        replayed.parameters[i].default_argument;
                    member.info.parameters[i]
                        .requires_complete_class_default_replay = false;
                }
                member.info.has_complete_class_default_recipes = false;
            }
        }
        if (const cir::RecordMethodFact* fact =
                collect_session_.file().method_fact(method_entity)) {
            member.info.pattern_type = fact->type.type;
        }
    }

    for (PendingMemberTemplate& member : pending) {
        if (member.method_index >= method_entities.size() ||
            !method_entities[member.method_index].valid()) {
            continue;
        }
        cir::EntityId method_entity = method_entities[member.method_index];
        collect::Session::TemplateInfo declaration = member.info;
        if (member.body) {
            declaration.has_definition = false;
            declaration.definition_begin = 0;
            declaration.definition_end = 0;
            declaration.pattern_function = {};
            declaration.pattern_generic = {};
            declaration.pattern_usable = false;
            declaration.definition_generation = 0;
            declaration.pattern_holes.clear();
            declaration.pattern_events.clear();
            declaration.member_patterns.clear();
        }
        collect_session_.register_template_entity(std::move(declaration),
                                                  method_entity,
                                                  member.loc);
    }

    for (PendingMemberTemplate& member : pending) {
        if (member.method_index >= method_entities.size() ||
            !method_entities[member.method_index].valid()) {
            continue;
        }
        cir::EntityId method_entity = method_entities[member.method_index];
        if (member.body) {
            member.body->method_index = member.method_index;
            if (!collect_session_.collecting_pattern() &&
                !collect_session_.is_instantiating()) {

                validate_member_template_body(member.info,
                                              method_entity,
                                              *member.body,
                                              member.loc);
            }
            uint64_t key = static_cast<uint64_t>(method_entity.index);
            member_template_bodies_[key] = *member.body;
            collect_session_.track_speculative_rollback(
                [this, key] { member_template_bodies_.erase(key); });
            (void)collect_session_.define_member_template_entity(
                std::move(member.info), method_entity, member.loc);
        }
    }
}

cir::FunctionExceptionSpec Parser::replay_complete_class_noexcept(
    const cir::RecordMethodFact& method,
    const collect::Session::TemplateInfo* member_template_info) {
    cir::FunctionExceptionSpec result;
    if (!method.has_deferred_noexcept_operand ||
        method.noexcept_operand_end <= method.noexcept_operand_begin) {
        return result;
    }

    size_t saved_cursor = cursor_;
    size_t saved_last_end = last_consumed_raw_end_;
    int saved_template_closes = pending_template_closes_;
    cursor_ = method.noexcept_operand_begin;
    pending_template_closes_ = 0;

    cir::DeclContextId context = method.noexcept_declaration_context;
    collect::ScopeFlags flags = scope_flags_for_complete_class_context(
        collect_session_.file(), context);
    bool entered = false;
    if (flags != collect::ScopeFlags::None) {
        collect::ScopeEnterResult scope =
            collect_session_.enter_existing_context(context, flags);
        entered = scope.scope != collect::InvalidScopeId;
    }
    cir::EntityId declaration_record =
        collect_session_.enclosing_record_for_context(context);
    cir::EntityId previous_record{};
    if (declaration_record.valid()) {
        previous_record =
            collect_session_.override_member_access_record(
                declaration_record);
    }
    cir::EntityId previous_function =
        collect_session_.override_member_access_function(method.entity);
    collect::Session::LookupGenerationCeilingScope ceiling(
        collect_session_, collect_session_.lookup_generation());
    std::optional<collect::Session::ActiveTemplateHeaderScope> header_scope;
    if (member_template_info) {
        header_scope.emplace(collect_session_, *member_template_info);
    }
    collect::Session::PrototypeParameterScope parameter_scope;
    if (!method.declarator_parameters.empty()) {
        parameter_scope =
            collect_session_.begin_prototype_parameter_scope();
        for (const cir::FunctionParameterScopeFact& parameter :
             method.declarator_parameters) {
            collect::Session::TemplateInfo::FunctionConstraintParameter
                recipe;
            recipe.name = parameter.name.valid()
                ? std::string(collect_session_.file().name(parameter.name))
                : std::string("<anonymous>");
            recipe.type = parameter.type;
            recipe.loc = parameter.loc;
            recipe.is_parameter_pack = parameter.is_parameter_pack;
            if (parameter.source_parameter_pack_name.valid()) {
                recipe.source_parameter_pack_name = std::string(
                    collect_session_.file().name(
                        parameter.source_parameter_pack_name));
            }
            recipe.is_parameter_pack_expansion_sentinel =
                parameter.is_parameter_pack_expansion_sentinel;
            recipe.type_originates_from_template_parameter =
                parameter.type_originates_from_template_parameter;
            collect_session_.bind_prototype_parameter(parameter_scope,
                                                      recipe);
        }
    }

    bool member_is_const = false;
    bool member_is_volatile = false;
    cir::TypeId resolved_method_type =
        collect_session_.file().resolved_type(method.type.type);
    if (collect_session_.file().valid(resolved_method_type)) {
        const auto* function =
            std::get_if<cir::FunctionTypePayload>(
                &collect_session_.file().type_payload(
                    resolved_method_type));
        member_is_const = function && function->member_is_const;
        member_is_volatile = function && function->member_is_volatile;
    }
    collect::Session::MemberDeclaratorThisScope this_scope =
        collect_session_.begin_member_declarator_this(
            declaration_record,
            member_is_const,
            member_is_volatile,
            method.is_static);
    ParsedExpr operand = parse_conditional_expression();
    result = collect_session_.evaluate_noexcept_spec(
        operand.sem,
        method.noexcept_operand_loc);
    collect_session_.finish_member_declarator_this(
        std::move(this_scope));
    collect_session_.finish_prototype_parameter_scope(
        std::move(parameter_scope));

    collect_session_.override_member_access_function(previous_function);
    if (declaration_record.valid()) {
        collect_session_.override_member_access_record(previous_record);
    }
    if (entered) {
        collect_session_.leave_scope();
    }
    cursor_ = saved_cursor;
    last_consumed_raw_end_ = saved_last_end;
    pending_template_closes_ = saved_template_closes;
    return result;
}

void Parser::replay_complete_class_regions(
    cir::EntityId record,
    const std::vector<PendingMemberTemplate>& member_templates,
    const std::vector<cir::EntityId>& method_entities) {
    if (!record.valid() || !collect_session_.file().valid(record)) {
        return;
    }

    uint64_t completion_generation = collect_session_.lookup_generation();
    std::vector<collect::Session::TemplateInfo> template_defaults =
        collect_session_.complete_class_template_default_recipes(record);
    for (const collect::Session::TemplateInfo& recipe : template_defaults) {
        if (recipe.complete_class_head_end <=
            recipe.complete_class_head_begin) {
            continue;
        }
        size_t saved_cursor = cursor_;
        size_t saved_last_end = last_consumed_raw_end_;
        int saved_template_closes = pending_template_closes_;
        cursor_ = recipe.complete_class_head_begin;
        pending_template_closes_ = 0;
        bool entered = false;
        collect::ScopeFlags flags =
            scope_flags_for_complete_class_context(
                collect_session_.file(), recipe.lexical_context);
        if (flags != collect::ScopeFlags::None) {
            collect::ScopeEnterResult scope =
                collect_session_.enter_existing_context(
                    recipe.lexical_context, flags);
            entered = scope.scope != collect::InvalidScopeId;
        }
        collect::Session::TemplateInfo replayed;
        uint32_t parameter_depth = recipe.parameters.empty()
            ? 0
            : recipe.parameters.front().depth;
        bool replay_ok = parse_cxx_template_head(replayed,
                                                 SrcLoc{},
                                                 parameter_depth);
        if (entered) {
            collect_session_.leave_scope();
        }
        cursor_ = saved_cursor;
        last_consumed_raw_end_ = saved_last_end;
        pending_template_closes_ = saved_template_closes;
        if (replay_ok &&
            replayed.parameters.size() == recipe.parameters.size()) {
            collect_session_.resolve_complete_class_template_defaults(
                recipe.entity, replayed.parameters);
        }
    }
    std::vector<collect::Session::CompleteClassDefaultArgumentRef> defaults =
        collect_session_.prepare_complete_class_default_arguments(
            record, completion_generation);
    for (const auto& argument : defaults) {
        size_t error_watermark =
            collect_session_.file().errors().size();
        size_t diagnostic_watermark = diagnostics_.size();
        collect_session_.begin_speculative_parse();
        (void)replay_default_argument(argument.entity,
                                      argument.parameter_index,
                                      argument.loc);
        std::vector<std::pair<SrcLoc, std::string>> errors(
            collect_session_.file().errors().begin() + error_watermark,
            collect_session_.file().errors().end());
        std::vector<Diagnostic> replay_diagnostics(
            diagnostics_.begin() + diagnostic_watermark,
            diagnostics_.end());
        collect_session_.rollback_speculative_parse();
        diagnostics_.resize(diagnostic_watermark);
        for (auto& [loc, message] : errors) {
            collect_session_.file().add_error(std::move(message), loc);
        }
        diagnostics_.insert(diagnostics_.end(),
                            replay_diagnostics.begin(),
                            replay_diagnostics.end());
    }

    const cir::RecordFacts* facts =
        collect_session_.file().record_facts(record);
    if (!facts) {
        return;
    }
    std::vector<cir::RecordMethodFact> deferred;
    for (const cir::RecordMethodFact& method : facts->methods) {
        if (method.has_deferred_noexcept_operand) {
            deferred.push_back(method);
        }
    }
    for (const cir::RecordMethodFact& method : deferred) {
        const collect::Session::TemplateInfo* member_template_info = nullptr;
        for (const PendingMemberTemplate& pending : member_templates) {
            if (pending.method_index < method_entities.size() &&
                method_entities[pending.method_index] == method.entity) {
                member_template_info = &pending.info;
                break;
            }
        }
        cir::FunctionExceptionSpec spec =
            replay_complete_class_noexcept(method, member_template_info);
        collect_session_.resolve_record_method_noexcept(method.entity,
                                                        std::move(spec));
    }

    facts = collect_session_.file().record_facts(record);
    if (!facts) {
        return;
    }
    std::vector<cir::RecordFieldFact> initializer_fields;
    for (const cir::RecordFieldFact& field : facts->fields) {
        if (field.has_default_member_initializer) {
            initializer_fields.push_back(field);
        }
    }
    bool any_initializer_throws = false;
    bool any_initializer_throwing_dependent = false;
    for (const cir::RecordFieldFact& field : initializer_fields) {
        size_t error_watermark = collect_session_.file().errors().size();
        size_t diagnostic_watermark = diagnostics_.size();
        collect_session_.begin_speculative_parse();
        cir::InstId object_place =
            collect_session_.make_complete_class_validation_object(
                record, field.default_member_initializer_loc);
        collect::ExprResult initializer =
            replay_default_member_initializer(
                field.entity, object_place,
                field.default_member_initializer_loc);
        bool dependent = false;
        bool potentially_throwing =
            collect_session_.expression_potentially_throws(initializer,
                                                           &dependent);
        std::vector<std::pair<SrcLoc, std::string>> errors(
            collect_session_.file().errors().begin() + error_watermark,
            collect_session_.file().errors().end());
        std::vector<Diagnostic> replay_diagnostics(
            diagnostics_.begin() + diagnostic_watermark,
            diagnostics_.end());
        collect_session_.rollback_speculative_parse();
        diagnostics_.resize(diagnostic_watermark);
        for (auto& [error_loc, message] : errors) {
            collect_session_.file().add_error(std::move(message), error_loc);
        }
        diagnostics_.insert(diagnostics_.end(),
                            replay_diagnostics.begin(),
                            replay_diagnostics.end());
        collect_session_.resolve_record_field_initializer_exception(
            field.entity, potentially_throwing, dependent);
        any_initializer_throws =
            any_initializer_throws || potentially_throwing;
        any_initializer_throwing_dependent =
            any_initializer_throwing_dependent || dependent;
    }

    facts = collect_session_.file().record_facts(record);
    if (!facts || initializer_fields.empty()) {
        return;
    }
    for (const cir::RecordMethodFact& method : facts->methods) {
        if (method.special_member_kind !=
                cir::SpecialMemberKind::DefaultConstructor ||
            method.has_explicit_exception_spec) {
            continue;
        }
        const auto* payload = std::get_if<cir::FunctionTypePayload>(
            &collect_session_.file().type_payload(
                collect_session_.file().resolved_type(method.type.type)));
        if (!payload) {
            continue;
        }
        cir::FunctionExceptionSpec spec = payload->exception_spec;
        if (any_initializer_throws) {
            spec = cir::FunctionExceptionSpecKind::PotentiallyThrowing;
        } else if (any_initializer_throwing_dependent) {

            spec = cir::FunctionExceptionSpecKind::PotentiallyThrowing;
        }
        collect_session_.resolve_record_method_noexcept(method.entity,
                                                        std::move(spec));
    }
}

void Parser::replay_or_defer_record_bodies(
    cir::EntityId record,
    std::vector<PendingMemberTemplate> member_templates,
    std::vector<PendingMemberBody> bodies,
    std::vector<cir::EntityId> method_entities) {
    if (has_incomplete_enclosing_record(record)) {
        size_t queue_size = deferred_complete_class_records_.size();
        deferred_complete_class_records_.push_back(
            DeferredCompleteClassRecord{record,
                                       collect_session_.in_template_definition(),
                                       std::move(member_templates),
                                       std::move(bodies),
                                       std::move(method_entities)});
        collect_session_.track_speculative_rollback([this, queue_size] {
            if (deferred_complete_class_records_.size() > queue_size) {
                deferred_complete_class_records_.resize(queue_size);
            }
        });
        return;
    }

    replay_complete_class_regions(record, member_templates, method_entities);
    finalize_pending_member_templates(std::move(member_templates),
                                      method_entities);

    replay_ready_complete_class_records();
    replay_hidden_friend_bodies(record);
    replay_deferred_member_bodies(bodies, method_entities);
}

void Parser::replay_ready_complete_class_records() {
    for (;;) {
        auto ready = std::find_if(
            deferred_complete_class_records_.begin(),
            deferred_complete_class_records_.end(),
            [&](const DeferredCompleteClassRecord& pending) {
                if (has_incomplete_enclosing_record(pending.record)) {
                    return false;
                }
                if (!collect_session_.is_instantiating()) {
                    return true;
                }

                return std::any_of(
                    pending.method_entities.begin(),
                    pending.method_entities.end(),
                    [&](cir::EntityId method) {
                        return collect_session_
                            .member_instantiation_template(method, nullptr) !=
                            nullptr;
                    });
            });
        if (ready == deferred_complete_class_records_.end()) {
            return;
        }
        DeferredCompleteClassRecord pending = std::move(*ready);
        deferred_complete_class_records_.erase(ready);
        bool previous_template_definition =
            collect_session_.in_template_definition();
        collect_session_.set_in_template_definition(
            pending.in_template_definition);
        replay_complete_class_regions(pending.record,
                                      pending.member_templates,
                                      pending.method_entities);
        finalize_pending_member_templates(
            std::move(pending.member_templates), pending.method_entities);
        replay_hidden_friend_bodies(pending.record);
        replay_deferred_member_bodies(pending.bodies,
                                      pending.method_entities);
        collect_session_.set_in_template_definition(
            previous_template_definition);
    }
}

void Parser::replay_hidden_friend_bodies(cir::EntityId record) {
    if (!record.valid() || !collect_session_.file().valid(record)) {
        return;
    }
    uint64_t key = static_cast<uint64_t>(record.index);
    auto found = pending_hidden_friend_bodies_.find(key);
    if (found == pending_hidden_friend_bodies_.end()) {
        return;
    }
    std::vector<PendingHiddenFriendBody> pending = std::move(found->second);
    pending_hidden_friend_bodies_.erase(found);

    for (PendingHiddenFriendBody& body : pending) {
        if (!body.entity.valid() ||
            !collect_session_.file().valid(body.entity)) {
            continue;
        }
        if (collect_session_.is_instantiating() &&
            !body.is_defaulted_comparison) {
            (void)collect_session_.template_arguments_for_record(
                body.granting_record,
                &body.enclosing_template,
                &body.enclosing_template_arguments);
            if (const cir::TemplateSpecializationFact* specialization =
                    collect_session_.file().template_specialization(
                        body.granting_record)) {
                body.point_lookup_generation =
                    specialization->point_lookup_generation;
            }
            uint64_t body_key = static_cast<uint64_t>(body.entity.index);
            auto [deferred, inserted] =
                deferred_hidden_friend_bodies_.try_emplace(
                    body_key, std::move(body));
            if (!inserted) {
                diagnose(DiagnosticLevel::Error,
                         "redefinition of hidden friend function '" +
                             deferred->second.name + "'",
                         body.loc);
                diagnose(DiagnosticLevel::Note,
                         "previous hidden friend definition is here",
                         deferred->second.loc);
                continue;
            }
            collect_session_.track_speculative_rollback(
                [this, body_key] {
                    deferred_hidden_friend_bodies_.erase(body_key);
                });
            continue;
        }
        (void)replay_hidden_friend_body(std::move(body));
    }
}

bool Parser::replay_hidden_friend_body(PendingHiddenFriendBody body) {
    if (!body.entity.valid() || !collect_session_.file().valid(body.entity)) {
        return false;
    }
    if (body.is_defaulted_comparison) {
        collect::ScopeEnterResult lexical_scope =
            collect_session_.enter_existing_context(
                body.lexical_context, collect::ScopeFlags::RecordScope);
        collect_session_.synthesize_defaulted_friend_comparison(
            body.entity, body.granting_record, body.has_explicit_exception_spec,
            body.loc);
        if (body.implicit_equality_origin.valid()) {
            if (cir::DefaultedComparisonFact* plan =
                    collect_session_.file().defaulted_comparison_fact_mut(
                        body.entity)) {
                plan->is_implicit_equality = true;
                plan->implicit_equality_origin = body.implicit_equality_origin;
            }
        }
        if (lexical_scope.scope != collect::InvalidScopeId) {
            collect_session_.leave_scope();
        }
        return collect_session_.file().entity(body.entity).is_definition;
    }
    const cir::Entity& existing = collect_session_.file().entity(body.entity);
    if (existing.is_definition) {
        diagnose(DiagnosticLevel::Error,
                 "redefinition of hidden friend function '" + body.name + "'",
                 body.loc);
        diagnose(DiagnosticLevel::Note,
                 "previous hidden friend definition is here", existing.loc);
        return false;
    }

    size_t saved_cursor = cursor_;
    size_t saved_last_end = last_consumed_raw_end_;
    int saved_template_closes = pending_template_closes_;
    cursor_ = body.body_begin;
    pending_template_closes_ = 0;

    collect::ScopeEnterResult lexical_scope =
        collect_session_.enter_existing_context(
            body.lexical_context, collect::ScopeFlags::RecordScope);
    body.flags.is_friend = false;
    if (!collect_session_.file().entity(body.entity)
             .module_attachment.valid()) {
        body.flags.is_inline = true;
    }
    cir::DeclContextId semantic_context =
        collect_session_.file().entity(body.entity).semantic_context;
    collect::FunctionDeclStart start =
        collect_session_.begin_function_type_on_entity(
            body.entity, body.name, body.function_type, body.result_type,
            body.params, body.loc, body.flags);

    collect_session_.file().entity_mut(body.entity).semantic_context =
        semantic_context;
    bool deduce_return =
        collect_session_.function_has_placeholder_return(body.function_type);
    if (deduce_return) {
        collect_session_.begin_function_return_deduction(
            start.decl.entity, body.function_type, body.loc);
    }
    ParsedStmt statement = parse_compound_statement();
    if (deduce_return) {
        collect_session_.resolve_deduced_return_type(
            start.decl.entity, body.function_type, body.loc);
    }
    collect_session_.finish_function(std::move(statement.sem),
                                     last_consumed_loc());
    if (lexical_scope.scope != collect::InvalidScopeId) {
        collect_session_.leave_scope();
    }

    cursor_ = saved_cursor;
    last_consumed_raw_end_ = saved_last_end;
    pending_template_closes_ = saved_template_closes;
    return collect_session_.file().entity(body.entity).is_definition;
}

bool Parser::force_deferred_hidden_friend_body(
    cir::EntityId function,
    cir::InstantiationDemandKind demand_kind) {
    if (!function.valid() || !collect_session_.file().valid(function)) {
        return false;
    }
    cir::Entity& entity = collect_session_.file().entity_mut(function);
    if (entity.is_definition) {
        if (entity.result_type_only_definition &&
            demand_kind != cir::InstantiationDemandKind::ResultType) {
            entity.result_type_only_definition = false;
            if (collect_session_.file().valid(entity.placeholder_result)) {
                collect_session_.file()
                    .placeholder_result_fact_mut(entity.placeholder_result)
                    .result_only_materialization = false;
            }
        }
        return true;
    }

    uint64_t key = static_cast<uint64_t>(function.index);
    auto found = deferred_hidden_friend_bodies_.find(key);
    if (found == deferred_hidden_friend_bodies_.end()) {
        return false;
    }
    PendingHiddenFriendBody body = std::move(found->second);
    deferred_hidden_friend_bodies_.erase(found);
    PendingHiddenFriendBody rollback_body = body;
    collect_session_.track_speculative_rollback(
        [this, key, rollback_body = std::move(rollback_body)]() mutable {
            deferred_hidden_friend_bodies_.try_emplace(
                key, std::move(rollback_body));
        });

    collect::Session::InstantiationScope enclosing_scope;
    bool has_enclosing_scope = false;
    if (body.enclosing_template.valid()) {
        if (const collect::Session::TemplateInfo* info =
                collect_session_.template_info(body.enclosing_template)) {
            enclosing_scope = collect_session_.begin_template_instantiation(
                *info,
                body.enclosing_template_arguments,
                body.loc,
                body.point_lookup_generation);
            has_enclosing_scope = enclosing_scope.active;
        }
    }
    std::unique_ptr<collect::Session::BlockContextState> saved_function;
    if (!has_enclosing_scope) {
        saved_function = collect_session_.save_function_context();
    }
    bool replayed = replay_hidden_friend_body(std::move(body));
    if (has_enclosing_scope) {
        collect_session_.finish_template_instantiation(
            std::move(enclosing_scope));
    } else {
        collect_session_.restore_function_context(
            std::move(saved_function));
    }
    if (replayed &&
        demand_kind == cir::InstantiationDemandKind::ResultType) {
        cir::Entity& replayed_entity =
            collect_session_.file().entity_mut(function);
        replayed_entity.result_type_only_definition = true;
        if (collect_session_.file().valid(
                replayed_entity.placeholder_result)) {
            collect_session_.file()
                .placeholder_result_fact_mut(
                    replayed_entity.placeholder_result)
                .result_only_materialization = true;
        }
    }
    return replayed;
}

void Parser::replay_deferred_member_bodies(
    const std::vector<PendingMemberBody>& pending,
    const std::vector<cir::EntityId>& method_entities) {
    for (const PendingMemberBody& body : pending) {
        if (body.method_index >= method_entities.size()) {
            continue;
        }
        cir::EntityId method_entity = method_entities[body.method_index];
        if (!method_entity.valid()) {
            continue;
        }
        const cir::Entity& method_record =
            collect_session_.file().entity(method_entity);
        if (method_record.is_definition) {

            continue;
        }
        if (method_record.parent.valid() &&
            collect_session_.file().valid(method_record.parent) &&
            collect_session_.file().entity(method_record.parent)
                .is_template_pattern) {
            collect_session_.file().entity_mut(method_entity)
                .is_template_pattern = true;
        }
        const cir::RecordMethodFact* method_fact =
            collect_session_.file().method_fact(method_entity);
        if (method_fact && method_fact->entity.valid()) {
            const cir::Entity& method_entity_record =
                collect_session_.file().entity(method_fact->entity);
            const cir::RecordFacts* owner =
                collect_session_.file().record_facts(
                    method_entity_record.parent);
            if (method_fact->constraint_satisfaction ==
                    cir::ConstraintSatisfactionKind::Unsatisfied ||
                method_fact->constraint_satisfaction ==
                    cir::ConstraintSatisfactionKind::Invalid) {
                // An ineligible member that shares its ABI signature with a
                // sibling declaration must not register its losing body: a
                // later demand for the viable entity would otherwise replay
                // the losing body under that symbol. A uniquely-signed
                // ineligible member has no such conflict; its body may still
                // be demanded by an explicit instantiation, which names the
                // member directly ([temp.explicit]).
                bool has_competing_sibling = owner && std::any_of(
                    owner->methods.begin(), owner->methods.end(),
                    [&](const cir::RecordMethodFact& other) {
                        return other.entity != method_fact->entity &&
                            other.name == method_fact->name &&
                            collect_session_.function_signatures_match(
                                other.type.type, method_fact->type.type);
                    });
                if (has_competing_sibling) {
                    continue;
                }
            }
            bool dominated = owner && std::any_of(
                owner->methods.begin(), owner->methods.end(),
                [&](const cir::RecordMethodFact& other) {
                    return other.entity != method_fact->entity &&
                        other.name == method_fact->name &&
                        other.constraint_satisfaction ==
                            cir::ConstraintSatisfactionKind::Satisfied &&
                        collect_session_.function_signatures_match(
                            other.type.type, method_fact->type.type) &&
                        std::find(other.more_constrained_than.begin(),
                                  other.more_constrained_than.end(),
                                  method_fact
                                      ->associated_constraint_fingerprint) !=
                            other.more_constrained_than.end();
                });
            if (dominated) {

                continue;
            }
        }
        if (collect_session_.is_instantiating()) {
            register_deferred_template_member_body(method_entity, body);
            continue;
        }

        auto saved = collect_session_.save_function_context();
        replay_member_body(method_entity, body);
        collect_session_.restore_function_context(std::move(saved));
    }
}

void Parser::register_deferred_template_member_body(
    cir::EntityId method_entity,
    const PendingMemberBody& body) {
    if (!collect_session_.is_instantiating() ||
        !method_entity.valid() ||
        !collect_session_.file().valid(method_entity) ||
        collect_session_.file().entity(method_entity).is_definition ||
        collect_session_.explicit_member_function_specialization_declared(
            method_entity)) {
        return;
    }

    uint64_t key = static_cast<uint64_t>(method_entity.index);
    auto [entry, inserted] = deferred_template_bodies_.emplace(
        key, DeferredTemplateBody{method_entity, body});
    if (inserted) {
        collect_session_.track_speculative_rollback(
            [this, key] { deferred_template_bodies_.erase(key); });
    }
}

void Parser::replay_member_body(cir::EntityId method_entity,
                                const PendingMemberBody& body,
                                bool allow_return_deduction) {
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

    cursor_ = body.body_begin;
    pending_template_closes_ = 0;
    constraint_expression_replay_end_ = SIZE_MAX;
    template_argument_expression_begins_.clear();

    std::vector<ParsedParam> body_params = body.params;
    std::vector<collect::ParamInput> params =
        param_inputs_from_parsed_params(body_params,
                                        /*move_runtime_fragments=*/false);

    collect::FunctionDeclStart start =
        collect_session_.begin_member_function(method_entity,
                                               params,
                                               current_loc());
    if (start.decl.has_error) {
        return;
    }
    collect::Session::InstantiationScope replay_parameter_scope =
        collect_session_
            .begin_current_template_instantiation_parameter_scope(
                method_entity,
                current_loc());

    cir::TypeId method_type_with_auto{};
    cir::TypeId placeholder_method_type{};
    bool deduction_armed = false;
    {
        cir::TypeId method_type =
            collect_session_.file().entity(method_entity).type;
        cir::PlaceholderResultFactId placeholder =
            collect_session_.file().entity(method_entity)
                .placeholder_result;
        if (collect_session_.file().valid(placeholder)) {
            method_type = collect_session_.file()
                .placeholder_result_fact(placeholder)
                .declared_function_type;
        }
        if (collect_session_.function_has_placeholder_return(method_type)) {
            placeholder_method_type = method_type;
            if (allow_return_deduction) {
                method_type_with_auto = method_type;
            }
            deduction_armed = true;
            collect_session_.begin_function_return_deduction(
                method_entity, method_type, current_loc());
        }
    }

    cir::EntityKind method_kind =
        collect_session_.file().entity(method_entity).kind;

    ParsedStmt body_stmt;
    if (body.is_constructor_function_try) {

        collect_session_.begin_member_pattern(
            method_entity, start.function.function, body.body_begin, 0);
        body_stmt = parse_constructor_function_try();
        collect_session_.finish_member_pattern(
            body_stmt.sem.fragment.blocks.size());
    } else {

        collect::StmtResult subobject_init;
        bool initializer_requires_token_replay = false;
        if (method_kind == cir::EntityKind::Constructor) {
            size_t collect_error_watermark =
                collect_session_.file().errors().size();
            size_t parser_diagnostic_watermark = diagnostics_.size();
            TentativeParsingAction initializer_transaction(*this);
            std::vector<collect::Session::MemberInitializerInput> initializers;
            if (body.init_begin != body.init_end) {
                size_t body_cursor = cursor_;
                cursor_ = body.init_begin;
                initializer_requires_token_replay =
                    parse_member_initializer_list(initializers, body.init_end);
                cursor_ = body_cursor;
            }
            if (!initializer_requires_token_replay) {
                subobject_init =
                    collect_session_.collect_constructor_initializers(
                        std::move(initializers), current_loc());
                initializer_requires_token_replay =
                    subobject_init.requires_token_replay;
            }
            bool emitted_error =
                collect_session_.file().errors().size() >
                    collect_error_watermark ||
                std::any_of(
                    diagnostics_.begin() + parser_diagnostic_watermark,
                    diagnostics_.end(),
                    [](const Diagnostic& diagnostic) {
                        return diagnostic.level == DiagnosticLevel::Error;
                    });
            if (initializer_requires_token_replay && !emitted_error) {

                initializer_transaction.revert();
                subobject_init = {};
            } else {
                initializer_transaction.commit();
            }
        }

        collect_session_.begin_member_pattern(
            method_entity, start.function.function, body.body_begin,
            subobject_init.fragment.blocks.size());
        body_stmt = parse_compound_statement();
        collect_session_.finish_member_pattern(
            body_stmt.sem.fragment.blocks.size());
        if (method_kind == cir::EntityKind::Destructor &&
            body_stmt.sem.falls_through) {
            collect::StmtResult epilogue =
                collect_session_.collect_destructor_epilogue(current_loc());
            body_stmt.sem.fragment =
                collect_session_.chain(std::move(body_stmt.sem.fragment),
                                       std::move(epilogue.fragment),
                                       current_loc());
        }
        body_stmt.sem.fragment =
            collect_session_.chain(std::move(subobject_init.fragment),
                                   std::move(body_stmt.sem.fragment),
                                   current_loc());
        body_stmt.sem.has_error =
            body_stmt.sem.has_error || subobject_init.has_error;
    }
    if (method_type_with_auto.valid()) {
        collect_session_.resolve_deduced_return_type(method_entity,
                                                     method_type_with_auto,
                                                     current_loc());
        if (body.has_placeholder_return_type_constraint &&
            !validate_placeholder_return_type_constraint(
                method_entity,
                body.placeholder_return_type_constraint_begin,
                body.placeholder_return_type_constraint_end,
                body.placeholder_return_type_constraint_loc)) {
            body_stmt.sem.has_error = true;
        }
    } else if (deduction_armed) {
        collect_session_.patch_pattern_function_result_type(
            method_entity, placeholder_method_type, current_loc());
    }
    if (replay_parameter_scope.active) {
        collect_session_.finish_template_parameter_scope(
            std::move(replay_parameter_scope));
    }
    collect_session_.finish_member_function(std::move(body_stmt.sem),
                                            current_loc());

    cir::Entity& entity = collect_session_.file().entity_mut(method_entity);
    entity.linkage = entity.suppressed_by_explicit_instantiation_declaration
        ? cir::LinkageKind::External
        : collect_session_.file().odr_linkage_for_entity(method_entity);
}

void Parser::validate_member_template_body(
    collect::Session::TemplateInfo& info,
    cir::EntityId method_entity,
    const PendingMemberBody& body,
    SrcLoc loc) {

    size_t error_watermark = collect_session_.file().errors().size();
    collect_session_.begin_speculative_parse();
    ParserCheckpoint checkpoint = capture_parser_checkpoint();
    if (!info.entity.valid()) {
        info.entity = method_entity;
    }
    collect::Session::InstantiationScope scope =
        collect_session_.begin_template_header(info, loc);
    bool was_in_template_definition =
        collect_session_.in_template_definition();
    collect_session_.set_in_template_definition(true);
    collect_session_.begin_template_validation(info);
    collect_session_.begin_pattern_collection();

    collect_session_.file().entity_mut(method_entity).is_template_pattern =
        true;
    replay_member_body(method_entity, body, /*allow_return_deduction=*/false);

    collect::Session::PatternCollection pattern =
        collect_session_.finish_pattern_collection();
    collect_session_.finish_template_validation();
    collect_session_.set_in_template_definition(was_in_template_definition);
    collect_session_.finish_template_header(std::move(scope));

    bool parse_clean =
        pattern.usable &&
        collect_session_.file().errors().size() == error_watermark &&
        diagnostics_.size() == checkpoint.diagnostics_size &&
        !pattern.members.empty();
    if (parse_clean) {
        collect_session_.commit_speculative_parse();
        restore_parser_checkpoint(checkpoint);
        info.has_definition = true;
        info.definition_begin = body.body_begin;
        info.definition_end = body.body_end;
        info.definition_generation = collect_session_.lookup_generation();
        info.pattern_record =
            collect_session_.file().entity(method_entity).parent;
        info.member_patterns = std::move(pattern.members);
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

bool Parser::clone_member_body(cir::EntityId method_entity,
                               const PendingMemberBody& body) {

    std::vector<collect::Session::TemplateArgument> arguments;
    const collect::Session::TemplateInfo* info =
        collect_session_.member_instantiation_template(method_entity,
                                                       &arguments);
    const cir::File& file = collect_session_.file();
    auto method_display = [&]() {
        std::string display;
        cir::EntityId owner = file.entity(method_entity).parent;
        if (owner.valid() && file.valid(owner) &&
            file.entity(owner).name.valid()) {
            display += file.name(file.entity(owner).name);
            display += "::";
        }
        if (file.entity(method_entity).name.valid()) {
            display += file.name(file.entity(method_entity).name);
        }
        return display;
    };
    auto record_token_replay = [&](bool clone_attempted) {
        record_template_replay_fallback(clone_attempted,
                                        /*member=*/true,
                                        method_display(),
                                        file.entity(method_entity).loc);
    };
    if (!info || !info->pattern_record.valid() ||
        info->member_patterns.empty()) {
        record_token_replay(/*clone_attempted=*/false);
        return false;
    }
    const collect::Session::MemberPattern* member = nullptr;
    for (const collect::Session::MemberPattern& candidate :
         info->member_patterns) {
        if (candidate.body_token_begin == body.body_begin) {
            member = &candidate;
            break;
        }
    }
    if (!lang_opts_.template_pattern_cloning || !member || !member->usable) {
        record_token_replay(/*clone_attempted=*/false);
        return false;
    }

    SrcLoc loc = file.entity(method_entity).loc;
    collect_session_.begin_speculative_parse();
    collect::Session::PatternInstantiationCallbacks callbacks;
    callbacks.replay_statement =
        [this, info](const collect::Session::PatternHole& hole) {
            size_t saved_cursor = cursor_;
            size_t saved_last_end = last_consumed_raw_end_;
            int saved_closes = pending_template_closes_;
            cursor_ = hole.token_begin;
            pending_template_closes_ = 0;
            collect::Session::LookupGenerationCeilingScope ceiling(
                collect_session_,
                info->definition_generation);
            ParsedStmt stmt = parse_statement();
            cursor_ = saved_cursor;
            last_consumed_raw_end_ = saved_last_end;
            pending_template_closes_ = saved_closes;
            return std::move(stmt.sem);
        };
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
    callbacks.collect_subobject_init = [this, info, &body]() {

        std::vector<collect::Session::MemberInitializerInput> initializers;
        collect::Session::LookupGenerationCeilingScope ceiling(
            collect_session_,
            info->definition_generation);
        if (body.init_begin != body.init_end) {
            size_t saved_cursor = cursor_;
            size_t saved_last_end = last_consumed_raw_end_;
            cursor_ = body.init_begin;
            parse_member_initializer_list(initializers, body.init_end);
            cursor_ = saved_cursor;
            last_consumed_raw_end_ = saved_last_end;
        }
        collect::StmtResult init =
            collect_session_.collect_constructor_initializers(
                std::move(initializers), current_loc());
        return init;
    };
    std::vector<ParsedParam> body_params = body.params;
    std::vector<collect::ParamInput> instantiated_params =
        param_inputs_from_parsed_params(body_params,
                                        /*move_runtime_fragments=*/false);
    bool cloned = collect_session_.clone_member_pattern(
        *info,
        *member,
        method_entity,
        arguments,
        instantiated_params,
        callbacks,
        loc);
    if (cloned) {
        cir::Entity& entity =
            collect_session_.file().entity_mut(method_entity);
        entity.linkage = entity.suppressed_by_explicit_instantiation_declaration
            ? cir::LinkageKind::External
            : collect_session_.file().odr_linkage_for_entity(method_entity);
        collect_session_.commit_speculative_parse();
        record_template_clone_instantiation(/*member=*/true);
    } else {
        collect_session_.rollback_speculative_parse();
        record_token_replay(/*clone_attempted=*/true);
    }
    return cloned;
}

bool Parser::force_deferred_template_member_body(cir::EntityId method_entity,
                                                 bool allow_clone) {
    if (!method_entity.valid()) {
        return false;
    }
    uint64_t key = static_cast<uint64_t>(method_entity.index);
    auto found = deferred_template_bodies_.find(key);
    if (found == deferred_template_bodies_.end() &&
        register_source_late_out_of_line_member_body(method_entity)) {
        found = deferred_template_bodies_.find(key);
    }
    if (found == deferred_template_bodies_.end()) {
        return false;
    }

    DeferredTemplateBody deferred = std::move(found->second);
    deferred_template_bodies_.erase(found);

    DeferredTemplateBody rollback_deferred = deferred;
    collect_session_.track_speculative_rollback(
        [this, key, rollback_deferred = std::move(rollback_deferred)]() mutable {
            deferred_template_bodies_.try_emplace(
                key, std::move(rollback_deferred));
        });
    if (collect_session_.explicit_member_function_specialization_declared(
            deferred.method)) {
        return false;
    }

    collect::Session::InstantiationScope scope;
    if (!collect_session_.begin_member_instantiation_scope(deferred.method,
                                                           scope)) {
        return false;
    }

    auto saved_function = collect_session_.save_function_context();
    if (!allow_clone || !clone_member_body(deferred.method, deferred.body)) {
        replay_member_body(deferred.method, deferred.body);
    }
    collect_session_.restore_function_context(std::move(saved_function));
    collect_session_.finish_template_instantiation(std::move(scope));
    return true;
}

void Parser::queue_odr_instantiation(cir::EntityId entity,
                                     OdrInstantiationOwner owner) {
    if (!entity.valid() || !collect_session_.file().valid(entity)) {
        return;
    }
    uint64_t key = (static_cast<uint64_t>(entity.generation) << 32) |
        entity.index;
    if (!queued_odr_instantiations_.insert(key).second) {
        return;
    }
    cir::Entity& queued = collect_session_.file().entity_mut(entity);
    if (queued.linkage != cir::LinkageKind::LinkOnceODR &&
        collect_session_.file().template_specialization(entity)) {
        queued.linkage =
            collect_session_.file().odr_linkage_for_entity(entity);
    }
    pending_odr_instantiations_.push_back(
        PendingOdrInstantiation{entity, owner});
    collect_session_.track_speculative_rollback([this, key, entity] {
        queued_odr_instantiations_.erase(key);
        auto found = std::find_if(
            pending_odr_instantiations_.begin(),
            pending_odr_instantiations_.end(),
            [entity](const PendingOdrInstantiation& pending) {
                return pending.entity == entity;
            });
        if (found != pending_odr_instantiations_.end()) {
            pending_odr_instantiations_.erase(found);
        }
    });
}

bool Parser::drain_pending_odr_instantiations() {
    // Instantiating one queued body can odr-use further specializations, so
    // keep draining until the queue stops growing.
    bool saved_draining = draining_odr_instantiations_;
    draining_odr_instantiations_ = true;
    bool made_progress = false;
    for (size_t index = 0; index < pending_odr_instantiations_.size();
         ++index) {
        PendingOdrInstantiation pending = pending_odr_instantiations_[index];
        cir::EntityId entity = pending.entity;
        if (!entity.valid() || !collect_session_.file().valid(entity) ||
            collect_session_.file().entity(entity).is_definition) {
            continue;
        }
        if (pending.owner == OdrInstantiationOwner::FunctionDemand) {
            (void)materialize_function_demand(
                entity,
                cir::InstantiationDemandKind::OdrUse,
                collect_session_.file().entity(entity).loc);
        } else {
            (void)force_deferred_template_member_body(entity);
        }
        made_progress = made_progress ||
            (collect_session_.file().valid(entity) &&
             collect_session_.file().entity(entity).is_definition);
    }
    draining_odr_instantiations_ = saved_draining;
    pending_odr_instantiations_.clear();
    queued_odr_instantiations_.clear();
    return made_progress;
}

void Parser::replay_referenced_template_members() {
    (void)drain_pending_odr_instantiations();

    cir::File& file = collect_session_.file();
    std::vector<cir::EntityId> worklist;
    std::unordered_set<uint64_t> enqueued;

    auto entity_key = [](cir::EntityId entity) {
        return (static_cast<uint64_t>(entity.generation) << 32) |
               entity.index;
    };
    auto callable = [](cir::EntityKind kind) {
        return kind == cir::EntityKind::Function ||
               kind == cir::EntityKind::Method ||
               kind == cir::EntityKind::Constructor ||
               kind == cir::EntityKind::Destructor;
    };
    auto backend_symbol = [&](cir::EntityKind kind) {
        return callable(kind) || kind == cir::EntityKind::Variable;
    };
    auto definition_available = [&](cir::EntityId entity_id) {
        if (!entity_id.valid() || !file.valid(entity_id)) {
            return false;
        }
        const cir::Entity& entity = file.entity(entity_id);
        bool defines_alias_or_ifunc =
            !entity.attr_facts.alias_target.empty() ||
            !entity.attr_facts.weakref_target.empty() ||
            !entity.attr_facts.ifunc_target.empty();
        return backend_symbol(entity.kind) &&
            (entity.is_definition || defines_alias_or_ifunc) &&
            !entity.is_deleted &&
            !entity.decl_flags.is_consteval &&
            !entity.is_template_pattern &&
            !entity.result_type_only_definition &&
            !entity.suppressed_by_explicit_instantiation_declaration &&
            !entity.suppressed_as_unselected_template_candidate &&
            !(entity.symbol_policy.imported_definition &&
              entity.symbol_policy.emission !=
                  cir::LinkageKind::LinkOnceODR);
    };
    auto definition_owned_elsewhere = [&](cir::EntityId entity_id) {
        if (!entity_id.valid() || !file.valid(entity_id)) {
            return false;
        }
        const cir::Entity& entity = file.entity(entity_id);
        bool class_support =
            entity.generated_symbol_role ==
                cir::GeneratedSymbolRole::VTable ||
            entity.generated_symbol_role ==
                cir::GeneratedSymbolRole::VTT ||
            entity.generated_symbol_role ==
                cir::GeneratedSymbolRole::ConstructionVTable ||
            entity.generated_symbol_role ==
                cir::GeneratedSymbolRole::TypeInfo ||
            entity.generated_symbol_role ==
                cir::GeneratedSymbolRole::TypeName ||
            entity.generated_symbol_role ==
                cir::GeneratedSymbolRole::Thunk ||
            entity.generated_symbol_role ==
                cir::GeneratedSymbolRole::DeletingDestructor;
        if (!class_support ||
            !entity.abi_owner.valid() ||
            !file.valid(entity.abi_owner)) {
            return false;
        }
        const cir::RecordFacts* owner =
            file.record_facts(entity.abi_owner);
        return owner && owner->key_function.valid();
    };
    auto materialize = [&](cir::EntityId entity_id, SrcLoc loc) {
        if (!entity_id.valid() || !file.valid(entity_id) ||
            definition_available(entity_id)) {
            return false;
        }
        const cir::Entity before = file.entity(entity_id);
        bool is_record_member =
            before.parent.valid() && file.valid(before.parent) &&
            file.entity(before.parent).kind == cir::EntityKind::Record;
        uint64_t key = static_cast<uint64_t>(entity_id.index);

        const cir::TemplateSpecializationFact* specialization =
            file.template_specialization(entity_id);
        const collect::Session::TemplateInfo* function_template = nullptr;
        if (specialization &&
            specialization->template_entity.valid()) {
            function_template = collect_session_.template_info(
                specialization->template_entity);
        }

        if (callable(before.kind) &&
            deferred_hidden_friend_bodies_.count(key)) {
            (void)force_deferred_hidden_friend_body(
                entity_id, cir::InstantiationDemandKind::OdrUse);
        } else if (callable(before.kind) &&
            function_template &&
            !function_template->is_class_template &&
            !deferred_template_bodies_.count(key)) {
            (void)collect_session_.request_function_instantiation(
                entity_id, cir::InstantiationDemandKind::OdrUse, loc);
        } else if (is_record_member) {
            collect::Session::InstantiationDemandResult result =
                collect_session_.request_class_member_instantiation(
                    entity_id, cir::InstantiationDemandKind::OdrUse, loc);

            if (result ==
                    collect::Session::InstantiationDemandResult::Satisfied &&
                deferred_template_bodies_.count(key)) {
                (void)force_deferred_template_member_body(entity_id);
            } else if (
                result !=
                collect::Session::InstantiationDemandResult::Satisfied) {
                deferred_template_bodies_.erase(key);
            }
        }
        return definition_available(entity_id);
    };

    std::function<void(cir::EntityId, SrcLoc)> require_entity;
    require_entity = [&](cir::EntityId entity_id, SrcLoc loc) {
        if (!entity_id.valid() || !file.valid(entity_id)) {
            return;
        }
        bool was_available = definition_available(entity_id);
        bool materialized_now =
            !was_available && materialize(entity_id, loc);
        if (!definition_available(entity_id)) {
            return;
        }

        cir::Entity& entity = file.entity_mut(entity_id);

        if (!materialized_now &&
            entity.symbol_policy.finalized &&
            entity.symbol_policy.definition_emission ==
                cir::DefinitionEmissionKind::DeclarationOnly &&
            definition_owned_elsewhere(entity_id)) {
            return;
        }
        entity.symbol_policy.definition_emission =
            cir::DefinitionEmissionKind::Required;

        if (entity.kind == cir::EntityKind::Variable &&
            entity.storage_duration != cir::StorageDuration::Static &&
            entity.storage_duration != cir::StorageDuration::Thread) {
            return;
        }
        uint64_t key = entity_key(entity_id);
        if (enqueued.insert(key).second) {
            worklist.push_back(entity_id);
        }
    };

    auto seed_required_roots = [&] {

        for (cir::EntityId entity_id : file.entity_ids()) {
            if (!file.valid(entity_id) ||
                file.entity(entity_id)
                        .symbol_policy.definition_emission !=
                    cir::DefinitionEmissionKind::Required) {
                continue;
            }
            require_entity(entity_id, file.entity(entity_id).loc);
        }
    };

    auto process_required_entity = [&](cir::EntityId entity_id) {
        if (!file.valid(entity_id)) {
            return;
        }
        const cir::Entity snapshot = file.entity(entity_id);

        if ((snapshot.generated_symbol_role ==
                 cir::GeneratedSymbolRole::VTable ||
             snapshot.generated_symbol_role ==
                 cir::GeneratedSymbolRole::ConstructionVTable) &&
            snapshot.abi_owner.valid() &&
            file.valid(snapshot.abi_owner)) {
            collect_session_.mark_record_vtable_methods_required(
                snapshot.abi_owner);
        }

        if (callable(snapshot.kind)) {

            std::vector<cir::FunctionId> functions = file.function_ids();
            for (cir::FunctionId function_id : functions) {
                const cir::Function& function = file.function(function_id);
                if (function.entity != entity_id) {
                    continue;
                }
                for (cir::BlockId block_id : function.blocks) {
                    if (!file.valid(block_id)) {
                        continue;
                    }
                    const cir::Block& block = file.block(block_id);
                    for (cir::InstId inst_id : block.instructions) {
                        if (!file.valid(inst_id)) {
                            continue;
                        }
                        const cir::Inst& inst = file.inst(inst_id);
                        for (const cir::Operand& operand :
                             file.operands(inst.operands)) {
                            if (const auto* dependency =
                                    std::get_if<cir::EntityId>(
                                        &operand.data)) {
                                require_entity(*dependency, inst.loc);
                            }
                        }
                    }
                }
            }
        }

        if (snapshot.kind == cir::EntityKind::Variable &&
            (snapshot.storage_duration == cir::StorageDuration::Static ||
             snapshot.storage_duration == cir::StorageDuration::Thread)) {

            std::vector<cir::StaticInitializerRelocation> relocations =
                file.entity(entity_id).static_initializer_relocations;
            for (const cir::StaticInitializerRelocation& relocation :
                 relocations) {
                require_entity(relocation.entity, snapshot.loc);
            }
        }
    };

    seed_required_roots();
    size_t cursor = 0;
    for (;;) {
        while (cursor < worklist.size()) {
            process_required_entity(worklist[cursor++]);
        }

        // Replaying a newly reachable member body can queue ordinary function
        // template specializations after the initial ODR drain. Materialize
        // that work before declaring the definition graph closed, then rescan
        // existing roots so their previously unavailable callees enter the
        // required-symbol worklist.
        bool odr_progress = drain_pending_odr_instantiations();
        size_t previous_size = worklist.size();
        collect_session_.finalize_name_linkage();
        seed_required_roots();
        if (odr_progress) {
            cursor = 0;
            continue;
        }
        if (worklist.size() == previous_size) {
            break;
        }
    }

    deferred_template_bodies_.clear();
    deferred_hidden_friend_bodies_.clear();
}

bool Parser::parse_member_initializer_list(
    std::vector<collect::Session::MemberInitializerInput>& initializers,
    size_t end_index) {
    bool requires_token_replay = false;
    auto parse_single_member_initializer =
        [&]() -> std::optional<collect::Session::MemberInitializerInput> {
        bool starts_qualified =
            check(TokenType::SCOPE_RESOLUTION) ||
            (is_identifier_token(current().type) &&
             peek(1).type == TokenType::SCOPE_RESOLUTION);
        if (!is_identifier_token(current().type) &&
            !check(TokenType::DECLTYPE_KW) && !starts_qualified) {
            return std::nullopt;
        }
        collect::Session::MemberInitializerInput initializer;
        initializer.loc = current().loc;
        if (check(TokenType::DECLTYPE_KW)) {
            DeclarationParser type_parser(*this);
            cir::TypeRef initializer_type =
                type_parser.parse_declaration(false, true);
            initializer.base_type = initializer_type.type;
        } else if (starts_qualified) {
            std::optional<QualifiedTypeLookahead> qualified =
                peek_cxx_qualified_type();
            if (!qualified.has_value()) {
                diagnose(DiagnosticLevel::Error,
                         "constructor initializer does not name a type",
                         current_loc());
                return std::nullopt;
            }
            SrcLoc qualified_loc = current_loc();
            for (size_t i = 0; i < qualified->tokens_to_consume; ++i) {
                consume();
            }
            if (qualified->template_info) {
                cir::EntityId instantiated = instantiate_template(
                    *qualified->template_info, qualified_loc);
                if (instantiated.valid()) {
                    initializer.base_type = collect_session_.file()
                        .entity(instantiated).type;
                }
            } else {
                cir::TypeId checked = collect_session_
                    .lookup_qualified_type_name_checked(
                        qualified->terminal_context,
                        qualified->terminal_name,
                        qualified->terminal_loc);
                initializer.base_type = checked.valid()
                    ? checked
                    : qualified->type.type;
            }
        } else {
            initializer.name = current().value;
            collect_session_.capture_type_parameter_pack_name(initializer.name);
            cir::TypeRef initializer_type =
                collect_session_.lookup_type_name_ref(initializer.name);
            consume();
            if (lang_opts_.is_cxx_mode() && check(TokenType::LESS_THAN)) {

                const collect::Session::TemplateInfo* info =
                    collect_session_.template_info_for_name(initializer.name);
                if (info &&
                    (info->is_class_template || info->is_alias_template)) {
                    cir::EntityId instantiated =
                        instantiate_template(*info, initializer.loc);
                    if (instantiated.valid()) {
                        initializer.base_type = collect_session_.file()
                            .entity(instantiated).type;
                        initializer.name = collect_session_.file().name(
                            collect_session_.file()
                                .entity(instantiated).name);
                    }
                }
            } else if (initializer_type.valid()) {
                initializer.base_type = initializer_type.type;
            }
        }
        if (initializer.base_type.valid()) {
            cir::EntityId record = collect_session_.file().record_entity(
                initializer.base_type);
            if (record.valid() && collect_session_.file().valid(record) &&
                collect_session_.file().entity(record).name.valid()) {
                initializer.name = collect_session_.file().name(
                    collect_session_.file().entity(record).name);
            }
        }
        initializer.boundary =
            collect_session_.begin_lifetime_boundary();
        if (match(TokenType::LEFT_PAREN)) {
            ParsedExpressionList arguments =
                parse_expression_list(TokenType::RIGHT_PAREN);
            initializer.arguments = std::move(arguments.sem);
            requires_token_replay = requires_token_replay ||
                arguments.has_dependent_pack_expansion;
            if (!match(TokenType::RIGHT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ')' in member initializer",
                         current_loc());
                collect_session_.discard_lifetime_boundary(
                    initializer.boundary);
                return std::nullopt;
            }
        } else if (check(TokenType::LEFT_BRACE)) {

            initializer.braced = true;
            bool dependent_pack_expansion = false;
            ParsedExpr list = parse_init_list_expression(
                &dependent_pack_expansion);
            initializer.arguments.push_back(std::move(list.sem));
            requires_token_replay = requires_token_replay ||
                dependent_pack_expansion;
        } else {
            diagnose(DiagnosticLevel::Error,
                     "expected '(' or '{' in member initializer",
                     current_loc());
            collect_session_.discard_lifetime_boundary(
                initializer.boundary);
            return std::nullopt;
        }
        collect_session_.close_lifetime_boundary_without_cleanup(
            initializer.boundary);
        return initializer;
    };

    while (!at_end() && (end_index == 0 || cursor_ < end_index) &&
           (is_identifier_token(current().type) ||
            check(TokenType::DECLTYPE_KW) ||
            check(TokenType::SCOPE_RESOLUTION))) {
        if (std::optional<PackExpansionPattern> pattern =
                try_parse_pack_expansion_pattern(
                    [&] { (void)parse_single_member_initializer(); })) {

            if (!pattern->has_pack_names()) {
                diagnose(DiagnosticLevel::Error,
                         "pack expansion pattern does not contain a template parameter pack",
                         pattern->ellipsis_loc);
                cursor_ = pattern->after_ellipsis_cursor;
                last_consumed_raw_end_ =
                    pattern->after_ellipsis_last_consumed_raw_end;
            } else {
                bool arity_dependent = false;
                std::optional<size_t> element_count =
                    resolve_pack_expansion_element_count(*pattern,
                                                         &arity_dependent);
                if (arity_dependent) {

                    parse_pack_expansion_pattern_deferred(
                        [&] { (void)parse_single_member_initializer(); });
                    requires_token_replay = true;
                    cursor_ = pattern->after_ellipsis_cursor;
                    last_consumed_raw_end_ =
                        pattern->after_ellipsis_last_consumed_raw_end;
                } else {
                    replay_pack_expansion_elements(
                        *pattern,
                        element_count.value_or(0),
                        [&](size_t) {
                            if (std::optional<
                                    collect::Session::MemberInitializerInput>
                                    replayed =
                                        parse_single_member_initializer()) {
                                initializers.push_back(std::move(*replayed));
                            }
                        });
                }
            }
        } else if (std::optional<collect::Session::MemberInitializerInput>
                       initializer = parse_single_member_initializer()) {
            initializers.push_back(std::move(*initializer));
        } else {
            return requires_token_replay;
        }
        if (!match(TokenType::COMMA)) {
            break;
        }
    }
    return requires_token_replay;
}

} // namespace aburi::syntax
