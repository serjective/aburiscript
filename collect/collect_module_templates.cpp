

#include "collect.h"

#include <cstdio>
#include <cstdlib>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "collect_template_state.h"

namespace aburi::collect {

namespace {

struct TemplateStateRemapper {
    const cir::File::ModuleGraphRemap& remap;
    uint64_t generation = 0;

    cir::TemplateArgument argument(const cir::TemplateArgument& value) const {
        return remap.argument(value);
    }

    void arguments(std::vector<cir::TemplateArgument>& values) const {
        for (cir::TemplateArgument& value : values) {
            value = argument(value);
        }
    }

    void attributes(AttributeList& values) const {
        for (ParsedAttribute& attribute : values.attrs) {
            attribute.loc = remap.loc(attribute.loc);
            for (AttributeArg& argument : attribute.args) {
                argument.loc = remap.loc(argument.loc);
            }
        }
    }

    Session::TemplateParameter parameter(
        const Session::TemplateParameter& source) const {
        Session::TemplateParameter result = source;
        result.entity = remap.entity(result.entity);
        result.type_param_type = remap.type(result.type_param_type);
        result.non_type_type = remap.type(result.non_type_type);
        if (result.nested_head) {
            result.nested_head = std::make_shared<Session::TemplateInfo>(
                info(*result.nested_head));
        }
        if (result.default_argument) {
            *result.default_argument = argument(*result.default_argument);
        }
        result.default_argument_context =
            remap.context(result.default_argument_context);
        result.default_argument_lookup_generation = generation;
        result.loc = remap.loc(result.loc);
        return result;
    }

    void parameters(std::vector<Session::TemplateParameter>& values) const {
        for (Session::TemplateParameter& value : values) {
            value = parameter(value);
        }
    }

    void constraint_mapping(
        Session::ConstraintParameterMapping& mapping) const {
        mapping.parameter_entity = remap.entity(mapping.parameter_entity);
        mapping.argument = argument(mapping.argument);
        if (mapping.argument_pack) {
            arguments(*mapping.argument_pack);
        }
    }

    Session::NormalizedConstraint normalized(
        const Session::NormalizedConstraint& source) const {
        Session::NormalizedConstraint result = source;
        for (Session::NormalizedConstraintNode& node : result.nodes) {
            node.atom.appearance_owner =
                remap.entity(node.atom.appearance_owner);
            for (Session::ConstraintParameterMapping& mapping :
                 node.atom.parameter_mapping) {
                constraint_mapping(mapping);
            }
            node.concept_id_entity = remap.entity(node.concept_id_entity);
            node.concept_id_dependent_qualifier =
                remap.type_ref(node.concept_id_dependent_qualifier);
            node.concept_id_name = remap.name(node.concept_id_name);
            arguments(node.concept_id_arguments);
            for (Session::ConstraintFoldExpansionParameter& fold_parameter :
                 node.fold_expansion_parameters) {
                fold_parameter.parameter_entity =
                    remap.entity(fold_parameter.parameter_entity);
                fold_parameter.owning_template_entity =
                    remap.entity(fold_parameter.owning_template_entity);
                fold_parameter.type_parameter_pack_type =
                    remap.type(fold_parameter.type_parameter_pack_type);
                fold_parameter.argument = argument(fold_parameter.argument);
                if (fold_parameter.argument_pack) {
                    arguments(*fold_parameter.argument_pack);
                }
            }
            for (Session::TemplateArgumentBinding& binding :
                 node.fold_pattern_argument_bindings) {
                arguments(binding.arguments);
            }
        }
        result.value_expression =
            remap.value_expression(result.value_expression, generation);
        for (Session::ConstraintParameterReference& reference :
             result.referenced_parameters) {
            reference.parameter_entity =
                remap.entity(reference.parameter_entity);
            reference.parameter_type = remap.type(reference.parameter_type);
            reference.owning_template_entity =
                remap.entity(reference.owning_template_entity);
        }
        return result;
    }

    Session::TemplateInfo::IntroducedConstraint introduced(
        const Session::TemplateInfo::IntroducedConstraint& source) const {
        Session::TemplateInfo::IntroducedConstraint result = source;
        result.type_constraint_concept =
            remap.entity(result.type_constraint_concept);
        arguments(result.type_constraint_arguments);
        result.loc = remap.loc(result.loc);
        if (result.normal_form) {
            *result.normal_form = normalized(*result.normal_form);
        }
        return result;
    }

    void scope_events(std::vector<Session::PatternScopeEvent>& events) const {
        for (Session::PatternScopeEvent& event : events) {
            event.entity = remap.entity(event.entity);
            event.place = remap.inst(event.place);
            event.lookup_generation = generation;
        }
    }

    Session::MemberPattern member_pattern(
        const Session::MemberPattern& source) const {
        Session::MemberPattern result = source;
        result.method = remap.entity(result.method);
        result.function = remap.function(result.function);
        cir::BlockId mapped_start = remap.block(
            cir::BlockId{static_cast<uint32_t>(result.body_start_block), 0});

        result.body_start_block =
            mapped_start.valid() ? mapped_start.index : 0;
        scope_events(result.events);
        return result;
    }

    Session::TemplateInfo info(const Session::TemplateInfo& source) const {
        Session::TemplateInfo result = source;
        result.entity = remap.entity(result.entity);
        result.operator_function.literal_suffix =
            remap.name(result.operator_function.literal_suffix);
        parameters(result.parameters);
        for (Session::TemplateInfo::FunctionConstraintParameter& parameter :
             result.function_constraint_parameters) {
            parameter.type = remap.type_ref(parameter.type);
            parameter.loc = remap.loc(parameter.loc);
        }
        for (Session::TemplateInfo::IntroducedConstraint& constraint :
             result.introduced_constraints) {
            constraint = introduced(constraint);
        }
        result.alias_target_type = remap.type(result.alias_target_type);
        result.alias_target_type_ref =
            remap.type_ref(result.alias_target_type_ref);
        if (result.alias_deduction_projection) {
            result.alias_deduction_projection->target_template =
                remap.entity(
                    result.alias_deduction_projection->target_template);
            arguments(result.alias_deduction_projection->target_arguments);
        }
        result.variable_type = remap.type(result.variable_type);
        result.variable_type_ref = remap.type_ref(result.variable_type_ref);
        if (result.constraint_normal_form) {
            *result.constraint_normal_form =
                normalized(*result.constraint_normal_form);
        }
        result.lexical_context = remap.context(result.lexical_context);
        result.pattern_function = remap.function(result.pattern_function);
        result.pattern_generic = remap.generic(result.pattern_generic);
        result.definition_generation = generation;
        scope_events(result.pattern_events);
        result.pattern_record = remap.entity(result.pattern_record);
        for (Session::MemberPattern& member : result.member_patterns) {
            member = member_pattern(member);
        }
        for (Session::TemplateInfo::StaticDataMemberInitializer& initializer :
             result.static_data_member_initializers) {
            initializer.loc = remap.loc(initializer.loc);
            initializer.declaration_context =
                remap.context(initializer.declaration_context);
            initializer.lookup_generation = generation;
            initializer.value_expression = remap.value_expression(
                initializer.value_expression, generation);
        }
        result.pattern_type = remap.type(result.pattern_type);
        for (cir::TypeId& type : result.param_types) {
            type = remap.type(type);
        }
        for (Session::TemplateInfo::TemplateInstantiationBinding& binding :
             result.enclosing_instantiation_bindings) {
            parameters(binding.parameters);
            for (Session::TemplateArgumentBinding& argument_binding :
                 binding.argument_bindings) {
                arguments(argument_binding.arguments);
            }
        }
        for (Session::TemplateInfo::OutOfLineMember& member :
             result.out_of_line_members) {
            parameters(member.head_parameters);
        }
        for (Session::TemplateInfo::PartialSpecialization& partial :
             result.partial_specializations) {
            partial.entity = remap.entity(partial.entity);
            arguments(partial.arguments);
            partial.loc = remap.loc(partial.loc);
        }
        for (Session::TemplateInfo::DeductionGuide& guide :
             result.deduction_guides) {
            guide.pattern_type = remap.type(guide.pattern_type);
            parameters(guide.parameters);
            arguments(guide.return_arguments);
            for (Session::TemplateInfo::IntroducedConstraint& constraint :
                 guide.introduced_constraints) {
                constraint = introduced(constraint);
            }
            guide.loc = remap.loc(guide.loc);
            guide.declaration_context =
                remap.context(guide.declaration_context);
            guide.declaration_generation = generation;
            guide.explicit_value_expression = remap.value_expression(
                guide.explicit_value_expression, generation);
            guide.explicit_declaration_context =
                remap.context(guide.explicit_declaration_context);
            guide.explicit_lookup_generation = generation;
        }
        result.explicit_value_expression = remap.value_expression(
            result.explicit_value_expression, generation);
        return result;
    }

    void function_friend_grant(cir::RecordFunctionFriendGrant& grant) const {
        grant.entity = remap.entity(grant.entity);
        grant.context = remap.context(grant.context);
        grant.module_attachment = remap.attachment(grant.module_attachment);
        grant.signature_owner = remap.entity(grant.signature_owner);
        grant.name = remap.name(grant.name);
        grant.type_pattern = remap.type_ref(grant.type_pattern);
        grant.qualifier_pattern = remap.type_ref(grant.qualifier_pattern);
        grant.member_name = remap.name(grant.member_name);
    }
};

} // namespace

void Session::stash_captured_member_body(uint64_t template_entity_index,
                                         CapturedMemberBody body) {
    tstate().captured_member_bodies_[template_entity_index] =
        std::move(body);
}

const std::unordered_map<uint64_t, Session::CapturedMemberBody>&
Session::captured_member_bodies() const {
    return tstate().captured_member_bodies_;
}

std::vector<std::pair<uint64_t, const Session::CapturedMemberBody*>>
Session::captured_member_bodies_for_unit(
    cir::ModuleAttachmentId unit) const {
    std::vector<std::pair<uint64_t, const CapturedMemberBody*>> bodies;
    if (!unit.valid() || tstate().captured_member_bodies_.empty()) {
        return bodies;
    }
    for (cir::EntityId entity : file_.entity_ids()) {
        auto found = tstate().captured_member_bodies_.find(
            static_cast<uint64_t>(entity.index));
        if (found == tstate().captured_member_bodies_.end() ||
            !found->second.transferable) {
            continue;
        }
        if (file_.entity(entity).origin_unit == unit) {
            bodies.emplace_back(found->first, &found->second);
        }
    }
    return bodies;
}

std::shared_ptr<void> Session::export_template_state() const {
    auto exported = std::make_shared<TemplateState>(*template_state_);

    exported->function_template_instantiation_callback_ = {};
    exported->pattern_instantiation_callback_configurator_ = {};
    exported->class_template_placeholder_deduction_callback_ = {};
    exported->class_instantiation_demand_callback_ = {};
    exported->function_instantiation_demand_callback_ = {};
    exported->function_template_materialization_target_ = {};
    exported->template_instantiation_requests_.clear();
    exported->current_instantiation_frames_.clear();
    exported->partial_spec_selection_cache_.clear();
    exported->pattern_holes_.clear();
    exported->pattern_members_.clear();
    exported->pattern_holed_locals_.clear();
    exported->exported_default_arguments_ = function_default_arguments_;
    return exported;
}

bool Session::template_state_has_templates(const void* exported_state) {
    if (exported_state == nullptr) {
        return false;
    }
    return !static_cast<const TemplateState*>(exported_state)
                ->templates_.empty();
}

bool Session::template_state_adoptable(const void* exported_state,
                                       const cir::File& source_file) {
    if (exported_state == nullptr) {
        return false;
    }
    const TemplateState& state =
        *static_cast<const TemplateState*>(exported_state);
    for (const auto& [key, info] : state.templates_) {

        if (!info.enclosing_instantiation_bindings.empty() ||
            !info.explicit_member_function_specializations.empty() ||
            !info.explicit_static_data_member_specializations.empty() ||
            info.is_member_template_specialization_overlay ||
            info.is_candidate_neutral_argument_recipe) {
            return false;
        }

        if (info.entity.valid() && source_file.valid(info.entity)) {
            cir::EntityId parent = source_file.entity(info.entity).parent;
            if (parent.valid() && source_file.valid(parent) &&
                source_file.entity(parent).kind == cir::EntityKind::Record &&
                !source_file.entity(parent).is_template_pattern &&
                info.has_definition) {
                auto body = state.captured_member_bodies_.find(
                    static_cast<uint64_t>(info.entity.index));
                if (body == state.captured_member_bodies_.end() ||
                    !body->second.transferable) {
                    return false;
                }
            }
        }
    }

    if (!state.pending_class_friends_.empty() ||
        !state.pending_function_friends_.empty()) {
        return false;
    }
    return true;
}

void Session::adopt_imported_templates(
    const void* exported_state,
    const cir::File::ModuleGraphRemap& remap,
    const cir::File& source_file,
    size_t first_imported_entity_index) {
    const TemplateState& state =
        *static_cast<const TemplateState*>(exported_state);
    TemplateStateRemapper remapper{remap, lookup_generation()};

    auto own_addition = [&](cir::EntityId remapped) {
        return remapped.valid() &&
               remapped.index >= first_imported_entity_index;
    };

    for (const auto& [key, source_info] : state.templates_) {
        cir::EntityId remapped_entity = remap.entity(source_info.entity);
        if (!own_addition(remapped_entity)) {
            continue;
        }
        TemplateInfo remapped = remapper.info(source_info);
        tstate().templates_.emplace(
            static_cast<uint64_t>(remapped.entity.index),
            std::move(remapped));
    }
    for (const auto& [key, recipes] : state.exported_default_arguments_) {
        cir::EntityId remapped_entity = remap.entity(
            cir::EntityId{static_cast<uint32_t>(key), 0});
        if (!own_addition(remapped_entity)) {
            continue;
        }
        std::vector<ParamInput::DefaultArgument> adopted = recipes;
        for (ParamInput::DefaultArgument& recipe : adopted) {
            recipe.loc = remap.loc(recipe.loc);
            recipe.declaration_context =
                remap.context(recipe.declaration_context);
            recipe.lookup_generation = remapper.generation;
        }
        function_default_arguments_.emplace(
            static_cast<uint64_t>(remapped_entity.index),
            std::move(adopted));
    }
    for (const auto& [key, body] : state.captured_member_bodies_) {
        cir::EntityId remapped_entity = remap.entity(
            cir::EntityId{static_cast<uint32_t>(key), 0});
        if (!own_addition(remapped_entity)) {
            continue;
        }
        CapturedMemberBody adopted = body;
        for (CapturedMemberParam& param : adopted.params) {
            param.type = remap.type(param.type);
            param.type_ref = remap.type_ref(param.type_ref);
            param.loc = remap.loc(param.loc);
            param.default_argument_loc =
                remap.loc(param.default_argument_loc);
            param.default_argument_declaration_context =
                remap.context(param.default_argument_declaration_context);
            param.default_argument_lookup_generation = remapper.generation;
        }
        tstate().captured_member_bodies_.emplace(
            static_cast<uint64_t>(remapped_entity.index),
            std::move(adopted));
    }
    for (const auto& [key, template_entity] :
         state.pattern_record_templates_) {
        cir::EntityId pattern = remap.entity(
            cir::EntityId{static_cast<uint32_t>(key), 0});
        cir::EntityId owner = remap.entity(template_entity);
        if (own_addition(pattern) && owner.valid()) {
            tstate().pattern_record_templates_.emplace(
                static_cast<uint64_t>(pattern.index), owner);
        }
    }
    for (TemplateState::FriendClassTemplateIdentity identity :
         state.hidden_friend_class_template_identities_) {
        identity.entity = remap.entity(identity.entity);
        if (!own_addition(identity.entity)) {
            continue;
        }
        identity.context = remap.context(identity.context);
        remapper.parameters(identity.parameters);
        tstate().hidden_friend_class_template_identities_.push_back(
            std::move(identity));
    }
    for (TemplateState::HiddenFriendRecordIdentity identity :
         state.hidden_friend_record_identities_) {
        identity.entity = remap.entity(identity.entity);
        if (!own_addition(identity.entity)) {
            continue;
        }
        identity.context = remap.context(identity.context);
        identity.module_attachment =
            remap.attachment(identity.module_attachment);
        tstate().hidden_friend_record_identities_.push_back(
            std::move(identity));
    }
    for (TemplateState::FriendFunctionTemplateIdentity identity :
         state.hidden_friend_function_template_identities_) {
        identity.entity = remap.entity(identity.entity);
        if (!own_addition(identity.entity)) {
            continue;
        }
        identity.context = remap.context(identity.context);
        identity.module_attachment =
            remap.attachment(identity.module_attachment);
        identity.signature_owner = remap.entity(identity.signature_owner);
        remapper.parameters(identity.parameters);
        identity.pattern_type = remap.type(identity.pattern_type);
        tstate().hidden_friend_function_template_identities_.push_back(
            std::move(identity));
    }
    for (cir::RecordFunctionFriendGrant grant :
         state.friend_function_identities_) {
        if (!own_addition(remap.entity(grant.entity))) {
            continue;
        }
        remapper.function_friend_grant(grant);
        tstate().friend_function_identities_.push_back(std::move(grant));
    }
    for (const auto& [key, declaration] :
         state.explicit_instantiation_declarations_) {
        cir::EntityId template_entity =
            remap.entity(declaration.template_entity);
        if (!template_entity.valid()) {
            continue;
        }
        TemplateState::ExplicitInstantiationDeclaration adopted;
        adopted.template_entity = template_entity;
        adopted.arguments = declaration.arguments;
        remapper.arguments(adopted.arguments);
        adopted.loc = remap.loc(declaration.loc);
        adopted.attrs = declaration.attrs;
        remapper.attributes(adopted.attrs);
        tstate().explicit_instantiation_declarations_.emplace(
            template_memo_key(template_entity, adopted.arguments),
            std::move(adopted));
    }
    for (const auto& [key, definition] :
         state.explicit_instantiation_definitions_) {
        cir::EntityId template_entity =
            remap.entity(definition.template_entity);
        if (!template_entity.valid()) {
            continue;
        }
        TemplateState::ExplicitInstantiationDeclaration adopted;
        adopted.template_entity = template_entity;
        adopted.arguments = definition.arguments;
        remapper.arguments(adopted.arguments);
        adopted.loc = remap.loc(definition.loc);
        adopted.attrs = definition.attrs;
        remapper.attributes(adopted.attrs);
        tstate().explicit_instantiation_definitions_.emplace(
            template_memo_key(template_entity, adopted.arguments),
            std::move(adopted));
    }
    for (const auto& [key, declared_loc] :
         state.explicit_entity_instantiation_declarations_) {
        cir::EntityId entity = remap.entity(
            cir::EntityId{static_cast<uint32_t>(key), 0});
        if (own_addition(entity)) {
            tstate().explicit_entity_instantiation_declarations_.emplace(
                static_cast<uint64_t>(entity.index),
                remap.loc(declared_loc));
        }
    }
    for (const auto& [key, defined_loc] :
         state.explicit_entity_instantiation_definitions_) {
        cir::EntityId entity = remap.entity(
            cir::EntityId{static_cast<uint32_t>(key), 0});
        if (own_addition(entity)) {
            tstate().explicit_entity_instantiation_definitions_.emplace(
                static_cast<uint64_t>(entity.index),
                remap.loc(defined_loc));
        }
    }
    for (const TemplateState::TemplateParameterObjectRecord& record :
         state.template_parameter_object_records_) {
        cir::EntityId object = remap.entity(record.object);
        if (!own_addition(object)) {
            continue;
        }
        TemplateArgument argument = remapper.argument(record.argument);
        tstate().template_parameter_object_cache_.emplace(
            template_argument_identity_key(argument), object);
        tstate().template_parameter_object_records_.push_back(
            {std::move(argument), object});
    }

    for (const auto& [key, fact] : source_file.template_specializations()) {
        cir::EntityId specialization = remap.entity(
            cir::EntityId{static_cast<uint32_t>(key), 0});
        cir::EntityId template_entity = remap.entity(fact.template_entity);
        if (!specialization.valid() || !template_entity.valid()) {
            continue;
        }
        TemplateArgumentBindings remapped_bindings = fact.argument_bindings;
        for (TemplateArgumentBinding& binding : remapped_bindings) {
            remapper.arguments(binding.arguments);
        }
        tstate().instantiation_cache_.emplace(
            template_memo_key(template_entity, remapped_bindings),
            specialization);
    }
}

} // namespace aburi::collect
