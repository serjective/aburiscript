#ifndef ABURI_COLLECT_COLLECT_TEMPLATE_STATE_H
#define ABURI_COLLECT_COLLECT_TEMPLATE_STATE_H

#include <cstdint>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "collect.h"

namespace aburi::collect {

struct Session::TemplateState {
    std::unordered_map<uint64_t, TemplateInfo> templates_;
    std::unordered_map<uint64_t, CapturedMemberBody>
        captured_member_bodies_;
    std::unordered_map<uint64_t, std::vector<ParamInput::DefaultArgument>>
        exported_default_arguments_;
    std::unordered_map<uint64_t, cir::EntityId> pattern_record_templates_;
    std::unordered_map<std::string, cir::EntityId> instantiation_cache_;
    std::unordered_map<std::string, PartialSpecializationSelection>
        partial_spec_selection_cache_;
    std::unordered_map<std::string, ConstraintSatisfactionResult>
        constraint_satisfaction_cache_;
    std::unordered_map<std::string, ConstraintSatisfactionResult>
        stable_constraint_satisfaction_cache_;
    std::vector<std::string> active_constraint_satisfactions_;
    uint64_t constraint_environment_revision_ = 1;
    std::unordered_map<std::string, cir::EntityId>
        template_parameter_object_cache_;
    struct TemplateParameterObjectRecord {
        TemplateArgument argument;
        cir::EntityId object{};
    };
    std::vector<TemplateParameterObjectRecord>
        template_parameter_object_records_;
    struct ExplicitInstantiationDeclaration {
        cir::EntityId template_entity{};
        std::vector<TemplateArgument> arguments;
        SrcLoc loc{};
        AttributeList attrs;
    };
    std::unordered_map<std::string, ExplicitInstantiationDeclaration>
        explicit_instantiation_declarations_;
    std::unordered_map<std::string, ExplicitInstantiationDeclaration>
        explicit_instantiation_definitions_;
    std::unordered_map<uint64_t, SrcLoc>
        explicit_entity_instantiation_declarations_;
    std::unordered_map<uint64_t, SrcLoc>
        explicit_entity_instantiation_definitions_;
    FunctionTemplateInstantiationCallback function_template_instantiation_callback_;
    PatternInstantiationCallbackConfigurator
        pattern_instantiation_callback_configurator_;
    ClassTemplatePlaceholderDeductionCallback
        class_template_placeholder_deduction_callback_;
    ClassInstantiationDemandCallback class_instantiation_demand_callback_;
    FunctionInstantiationDemandCallback function_instantiation_demand_callback_;
    cir::EntityId function_template_materialization_target_{};
    std::vector<TemplateInstantiationRequest> template_instantiation_requests_;
    struct CurrentInstantiationFrame {
        const TemplateInfo* info = nullptr;
        std::string memo_key;
        std::string display_name;
        std::vector<TemplateArgument> arguments;
        TemplateArgumentBindings argument_bindings;
        SrcLoc point_of_instantiation{};
        uint64_t point_lookup_generation = 0;
        cir::EntityId record_to_complete{};
        cir::EntityId record{};
        bool has_dependent_bases = false;
        bool replays_as_template_pattern = false;
        cir::EntityId template_entity{};
        std::unordered_map<uint64_t, TemplateArgument>
            dependent_value_bindings;
    };
    std::vector<CurrentInstantiationFrame> current_instantiation_frames_;
    std::vector<PatternHole> pattern_holes_;
    std::vector<MemberPattern> pattern_members_;
    std::unordered_set<uint64_t> pattern_holed_locals_;
    std::unordered_map<uint64_t, uint32_t> header_value_params_;
    std::unordered_set<uint64_t> header_value_param_packs_;
    std::unordered_set<uint64_t> function_parameter_pack_params_;
    std::unordered_set<std::string> function_parameter_pack_names_;
    std::unordered_map<std::string, std::vector<FunctionParameterPackElement>>
        function_parameter_pack_elements_;
    std::unordered_map<std::string, uint32_t>
        function_parameter_pack_template_indices_;
    std::unordered_set<uint64_t> template_type_origin_parameter_entities_;
    std::vector<Session::FunctionParameterPackScopeState>
        function_parameter_pack_scope_stack_;
    std::vector<std::vector<ParameterPackIdentity>>
        parameter_pack_pattern_captures_;
    std::vector<std::vector<std::vector<ParameterPackIdentity>>>
        parameter_pack_pattern_capture_suspensions_;
    std::vector<ParameterPackElementBinding>
        parameter_pack_element_replay_bindings_;
    std::vector<std::vector<ParameterPackElementBinding>>
        parameter_pack_element_replay_stack_;
    std::vector<std::vector<ParameterPackElementBinding>>
        parameter_pack_element_replay_suspensions_;
    std::vector<std::vector<uint64_t>>
        scoped_template_parameter_template_keys_;
    std::unordered_map<uint64_t, std::vector<cir::RecordClassFriendGrant>>
        pending_class_friends_;
    std::unordered_map<uint64_t,
                       std::vector<cir::RecordFunctionFriendGrant>>
        pending_function_friends_;
    struct FriendClassTemplateIdentity {
        std::string name;
        cir::DeclContextId context{};
        cir::EntityId entity{};
        std::vector<TemplateParameter> parameters;
    };
    std::vector<FriendClassTemplateIdentity>
        hidden_friend_class_template_identities_;
    struct HiddenFriendRecordIdentity {
        std::string name;
        cir::DeclContextId context{};
        cir::RecordKind kind = cir::RecordKind::Struct;
        cir::ModuleAttachmentId module_attachment{};
        cir::EntityId entity{};
    };
    std::vector<HiddenFriendRecordIdentity> hidden_friend_record_identities_;
    struct FriendFunctionTemplateIdentity {
        std::string name;
        cir::DeclContextId context{};
        cir::ModuleAttachmentId module_attachment{};
        cir::EntityId signature_owner{};
        cir::EntityId entity{};
        std::vector<TemplateParameter> parameters;
        cir::TypeId pattern_type{};
    };
    std::vector<FriendFunctionTemplateIdentity>
        hidden_friend_function_template_identities_;
    std::vector<cir::RecordFunctionFriendGrant> friend_function_identities_;
};

} // namespace aburi::collect

#endif // ABURI_COLLECT_COLLECT_TEMPLATE_STATE_H
