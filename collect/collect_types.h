#ifndef ABURI_COLLECT_COLLECT_TYPES_H
#define ABURI_COLLECT_COLLECT_TYPES_H

#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <vector>

#include "../cir/builder.h"
#include "../cir/file.h"

namespace aburi::collect {

enum class ValueCategory : uint8_t {
    Invalid,
    PrValue,
    LValue,
    XValue,
    FunctionDesignator,
    OverloadDesignator,
    QualifiedMember,
    MemberPointerDesignator,
    MemberFunctionPointerCallee,
    Type,
    InitList,
    Dependent
};

enum class UseContext : uint8_t {
    RValue,
    LValue,
    Init,
    DirectInit,
    Assignment,
    Return,
    Condition,
    Discard
};

enum class CppNamedCastKind : uint8_t {
    Static,
    Const,
    Reinterpret,
    Dynamic
};

enum class ScopeFlags : uint32_t {
    None = 0,
    FileScope = 1u << 0,
    FunctionScope = 1u << 1,
    BlockScope = 1u << 2,
    PrototypeScope = 1u << 3,
    LoopScope = 1u << 4,
    SwitchScope = 1u << 5,
    NamespaceScope = 1u << 6,
    TemplateParameterScope = 1u << 7,
    RecordScope = 1u << 8,
    EnumScope = 1u << 9
};

inline ScopeFlags operator|(ScopeFlags lhs, ScopeFlags rhs) {
    return static_cast<ScopeFlags>(
        static_cast<uint32_t>(lhs) | static_cast<uint32_t>(rhs));
}

inline ScopeFlags operator&(ScopeFlags lhs, ScopeFlags rhs) {
    return static_cast<ScopeFlags>(
        static_cast<uint32_t>(lhs) & static_cast<uint32_t>(rhs));
}

inline ScopeFlags& operator|=(ScopeFlags& lhs, ScopeFlags rhs) {
    lhs = lhs | rhs;
    return lhs;
}

inline bool scope_flags_contains(ScopeFlags flags, ScopeFlags value) {
    return (flags & value) != ScopeFlags::None;
}

using ScopeId = uint32_t;
constexpr ScopeId InvalidScopeId = 0;

struct ScopeEnterResult {
    ScopeId scope = InvalidScopeId;
    bool created_new = false;
};

struct ExprResult;
struct InitListValue;

struct DependentMemberAccessIdentity {
    std::shared_ptr<ExprResult> base;
    std::string member_name;
    bool is_arrow = false;
};

struct AccessBaseStep {
    cir::EntityId derived_class{};
    cir::TypeId base_type{};
    cir::RecordMemberAccess declared_access =
        cir::RecordMemberAccess::Public;
    bool operator==(const AccessBaseStep&) const = default;
};

struct MemberCandidateObjectPaths {
    cir::EntityId entity{};
    std::vector<std::vector<cir::EntityId>> paths;
    cir::TypeId implicit_object_class{};
    bool found_through_using = false;
    cir::EntityId access_owner{};
    cir::TypeId declaring_class{};
    cir::TypeId lookup_class{};
    cir::RecordMemberAccess declared_access =
        cir::RecordMemberAccess::Public;
    bool has_declared_access = false;
    std::vector<std::vector<AccessBaseStep>> base_paths;
};

enum class OverloadAddressCategory : uint8_t {
    FunctionPointer,
    MemberPointer,
};

struct OverloadDesignatorCandidate {
    cir::EntityId entity{};
    OverloadAddressCategory address_category =
        OverloadAddressCategory::FunctionPointer;
};

struct CandidateExplicitTemplateArguments {
    cir::EntityId template_entity{};
    std::vector<cir::TemplateArgument> arguments;
    bool viable = true;
};

struct OverloadDesignator {
    std::vector<OverloadDesignatorCandidate> candidates;
    std::vector<MemberCandidateObjectPaths> member_candidate_object_paths;
    cir::TypeId qualified_member_owner{};
    uint64_t lookup_generation = 0;
    bool qualified_name = false;
    bool address_of_written = false;
    bool address_operand_parenthesized = false;
    bool has_explicit_template_arguments = false;
    std::vector<cir::TemplateArgument> explicit_template_arguments;
    std::vector<CandidateExplicitTemplateArguments>
        candidate_explicit_template_arguments;
};

struct ObjCPropertyReference {
    std::shared_ptr<ExprResult> receiver;
    cir::EntityId interface{};
    std::string getter;
    std::string setter;
    cir::TypeId type{};
    std::shared_ptr<ExprResult> subscript_index;
};

enum class UserDefinedLiteralKind : uint8_t {
    Integer,
    Floating,
    Character,
    String
};

struct UserDefinedLiteralInfo {
    UserDefinedLiteralKind kind = UserDefinedLiteralKind::Integer;
    cir::NameId suffix{};
    std::string base_spelling;
    SrcLoc loc{};
};

struct ExprResult {
    cir::Fragment fragment;
    cir::InstId value{};
    cir::InstId place{};
    cir::TypeId type{};
    std::optional<uint8_t> semantic_object_qualifiers;
    bool unevaluated_semantic_operand = false;
    cir::EntityId entity{};
    std::vector<cir::EntityId> potential_results;
    bool deferred_entity_place = false;
    cir::EntityId nodiscard_callee{};
    std::shared_ptr<InitListValue> init_list;
    std::shared_ptr<ObjCPropertyReference> objc_property;
    std::string name;
    // True when parsing selected a compiler builtin call designator rather
    // than an ordinary declaration
    bool builtin_call_designator = false;
    bool unresolved_unqualified_name = false;
    std::vector<cir::EntityId> candidates;
    std::shared_ptr<const OverloadDesignator> overload_designator;
    std::vector<MemberCandidateObjectPaths> member_candidate_object_paths;
    cir::TypeId qualified_member_owner{};
    cir::TypeId member_access_object_type{};
    bool has_explicit_template_arguments = false;
    std::vector<cir::TemplateArgument> explicit_template_arguments;
    std::vector<CandidateExplicitTemplateArguments>
        candidate_explicit_template_arguments;
    std::vector<cir::TemplateValuePackReference> pack_expansion_references;
    cir::TypeRef dependent_value_qualifier;
    cir::NameId dependent_value_name{};
    std::optional<DependentMemberAccessIdentity> dependent_member_access;
    bool qualified_name = false;
    bool suppress_argument_dependent_lookup = false;
    ValueCategory bound_member_object_category = ValueCategory::Invalid;
    bool unparenthesized_id_or_member = false;
    bool unmaterialized_abstract_call_result = false;
    SrcLoc abstract_call_loc{};
    bool designates_bitfield = false;
    bool reference_binds_to_temporary = false;
    std::vector<cir::LifetimeId> materialized_lifetimes;
    bool arc_plus_one = false;
    bool arc_fresh_call = false;
    uint64_t arc_pending_token = 0;
    bool destructor_designator = false;
    bool unparenthesized_identifier = false;
    bool possibly_parenthesized_identifier = false;
    cir::InstId direct_dereference_pointer{};
    cir::TypeId direct_dereference_pointer_type{};
    bool references_template_value_parameter = false;
    bool value_dependent = false;
    cir::TemplateValueExpression template_value_expr;
    std::optional<UserDefinedLiteralInfo> user_defined_literal;
    bool type_originates_from_template_parameter = false;
    ValueCategory category = ValueCategory::Invalid;
    bool has_error = false;
};

enum class RangeEndpointKind : uint8_t {
    Invalid,
    Array,
    Member,
    ArgumentDependent,
    Dependent,
};

struct RangeEndpointPlan {
    RangeEndpointKind kind = RangeEndpointKind::Invalid;
    cir::TypeRef array_element;
    size_t array_extent = 0;
    std::vector<cir::EntityId> begin_candidates;
    std::vector<cir::EntityId> end_candidates;
    bool has_error = false;
};

enum class InitDesignatorKind : uint8_t {
    Field,
    Index,
    Range
};

struct InitDesignator {
    InitDesignatorKind kind = InitDesignatorKind::Field;
    std::string field_name;
    ExprResult index;
    ExprResult range_end;
    SrcLoc loc{};
};

struct InitElementInput {
    std::vector<InitDesignator> designators;
    ExprResult value;
    SrcLoc loc{};
};

enum class InferredArrayBoundKind : uint8_t {
    NotInferable,
    Concrete,
    Dependent,
    Invalid,
};

struct InferredArrayBound {
    InferredArrayBoundKind kind = InferredArrayBoundKind::NotInferable;
    size_t size = 0;
};

enum class InitListSyntax {
    Braced,
    Parenthesized
};

enum class ConstructorInitializationKind : uint8_t {
    Direct,
    Copy,
    CopyList
};

enum class ListInitializationDestination : uint8_t {
    Invalid,
    Scalar,
    Reference,
    Array,
    Aggregate,
    ClassConstructor,
    InitializerList,
};

enum class ListConstructorPhase : uint8_t {
    None,
    InitializerListConstructors,
    OrdinaryConstructors,
};

struct ListElementConversionPlan {
    cir::TypeRef target;
    SrcLoc loc{};
    bool viable = false;
    bool narrowing = false;
};

struct ListInitializationPlan {
    InitListSyntax syntax = InitListSyntax::Braced;
    ConstructorInitializationKind initialization_kind =
        ConstructorInitializationKind::Direct;
    ListInitializationDestination destination =
        ListInitializationDestination::Invalid;
    ListConstructorPhase constructor_phase = ListConstructorPhase::None;
    cir::TypeRef target;
    cir::EntityId selected_constructor{};
    std::vector<ListElementConversionPlan> elements;
    bool viable = false;
    bool has_designators = false;
};

struct InitListValue {
    std::vector<InitElementInput> elements;
    SrcLoc loc{};
    InitListSyntax syntax = InitListSyntax::Braced;
    bool has_error = false;
};

struct AsmOperand {
    std::string symbolic_name;
    std::string constraint;
    ExprResult expr;
    SrcLoc loc{};
};

struct GenericAssociation {
    bool is_default = false;
    cir::TypeRef type{};
    ExprResult expr;
    SrcLoc loc{};
};

struct StmtResult {
    cir::Fragment fragment;
    std::optional<ExprResult> result_expr;
    bool falls_through = true;
    bool always_returns = false;
    bool contains_switch_label = false;
    bool requires_token_replay = false;
    std::vector<cir::BlockId> break_exits;
    std::vector<cir::BlockId> continue_exits;
    bool has_error = false;
    bool preserves_result_expr = false;
};

struct DeclResult {
    cir::Fragment fragment;
    cir::EntityId entity{};
    cir::TypeId type{};
    cir::InstId place{};
    bool has_error = false;
};

struct StructuredBindingNameInput {
    std::string name;
    SrcLoc loc{};
    AttributeList attrs;
    bool is_pack = false;
};

struct StructuredBindingStart {
    std::string backing_name;
    std::vector<StructuredBindingNameInput> names;
    std::vector<cir::EntityId> entities;
    std::vector<cir::BindingId> bindings;
    SrcLoc loc{};
    bool has_error = false;
};

struct StructuredBindingTupleElementInput {
    cir::TypeRef element_type;
    ExprResult initializer;
};

struct StructuredBindingTupleInput {
    bool selected = false;
    bool has_error = false;
    std::vector<StructuredBindingTupleElementInput> elements;
};

struct DeclFlags {
    AttributeList attrs;
    bool is_constexpr = false;
    bool is_consteval = false;
    bool is_constinit = false;
    bool is_inline = false;
    bool is_thread_local = false;
    bool is_extern = false;
    bool is_static = false;
    bool is_auto_storage = false;
    bool is_register = false;
    bool is_mutable = false;
    bool is_friend = false;
    bool is_block_byref = false;
    bool is_deleted = false;
    bool is_defaulted = false;
    bool is_declaration_only = false;
    bool suppress_name_binding = false;
    uint8_t type_qualifiers = cir::QualNone;
    std::string asm_label;
    cir::Fragment vla_bounds;

    cir::DeclSemanticFlags to_cir() const {
        return {is_constexpr, is_consteval, is_constinit, is_inline,
                is_thread_local, is_register};
    }
};

struct RecordFieldInput {
    std::string name;
    cir::TypeId type{};
    uint8_t qualifiers = cir::QualNone;
    cir::EntityId lambda_capture_source{};
    cir::LambdaCaptureFieldKind lambda_capture_kind =
        cir::LambdaCaptureFieldKind::None;
    SrcLoc loc{};
    AttributeList attrs;
    cir::RecordMemberAccess declared_access = cir::RecordMemberAccess::Public;
    size_t forced_alignment = 0;
    bool is_packed = false;
    bool is_bitfield = false;
    uint32_t bit_width = 0;
    cir::TemplateValueExpression bit_width_expression;
    bool bit_width_is_dependent = false;
    bool is_mutable = false;
    bool is_anonymous_union_object = false;
    bool has_default_member_initializer = false;
    bool default_member_initializer_braced = false;
    uint32_t default_member_initializer_begin = 0;
    uint32_t default_member_initializer_end = 0;
    SrcLoc default_member_initializer_loc{};
    cir::DeclContextId default_member_initializer_context{};
    uint64_t default_member_initializer_lookup_generation = 0;
    bool default_member_initializer_potentially_throwing = false;
    bool default_member_initializer_throwing_dependent = false;
    cir::EntityId entity{};
};

struct RecordLayoutOptions {
    AttributeList attrs;
    bool is_packed = false;
    bool is_transparent_union = false;
    size_t requested_alignment = 0;
    size_t pack_alignment = 0;
    bool arc_managed_aggregate = false;
};

struct RecordStaticDataMemberInput {
    std::string name;
    cir::TypeId type{};
    cir::EntityId entity{};
    SrcLoc loc{};
    AttributeList attrs;
    cir::RecordMemberAccess declared_access = cir::RecordMemberAccess::Public;
    DeclFlags flags;
    ConstructorInitializationKind initialization_kind =
        ConstructorInitializationKind::Direct;
    std::optional<ExprResult> initializer;
    bool initializer_materialization_attempted = false;
    bool has_deferred_initializer = false;
    size_t initializer_begin = 0;
    size_t initializer_end = 0;
    SrcLoc initializer_loc{};
    cir::DeclContextId initializer_context{};
    uint64_t initializer_lookup_generation = 0;
    cir::TemplateValueExpression initializer_value_expression;
    bool has_error = false;
};

struct ParamInput {
    std::string name;
    cir::TypeRef type{};
    SrcLoc loc{};
    AttributeList attrs;
    bool arc_unretained = false;
    bool arc_consumed = false;
    cir::EntityId prototype_entity{};
    cir::Fragment vla_bounds;
    struct DefaultArgument {
        size_t token_begin = 0;
        size_t token_end = 0;
        SrcLoc loc{};
        cir::DeclContextId declaration_context{};
        uint64_t lookup_generation = 0;
        bool requires_complete_class_replay = false;
    };
    std::optional<DefaultArgument> default_argument;
    bool is_parameter_pack = false;
    std::string source_parameter_pack_name;
    bool is_parameter_pack_expansion_sentinel = false;
    bool type_originates_from_template_parameter = false;
};

struct RecordMethodInput {
    std::string name;
    cir::TypeId type{};
    cir::OperatorFunctionIdentity operator_function;
    std::vector<ParamInput> params;
    SrcLoc loc{};
    AttributeList attrs;
    cir::RecordMemberAccess declared_access = cir::RecordMemberAccess::Public;
    DeclFlags flags;
    bool is_static = false;
    bool is_function_template = false;
    bool is_conversion_function = false;
    bool is_virtual = false;
    bool is_override = false;
    bool is_final = false;
    bool is_deleted = false;
    bool is_defaulted = false;
    bool is_implicitly_declared = false;
    bool has_deferred_definition = false;
    size_t implicit_equality_source_index = static_cast<size_t>(-1);
    bool is_pure = false;
    bool is_constructor = false;
    bool is_destructor = false;
    bool has_explicit_exception_spec = false;
    bool is_explicit = false;
    cir::ExplicitSpecifierKind explicit_specifier =
        cir::ExplicitSpecifierKind::Absent;
    size_t explicit_expression_begin = 0;
    size_t explicit_expression_end = 0;
    cir::TemplateValueExpression explicit_value_expression;
    cir::DeclContextId explicit_declaration_context{};
    uint64_t explicit_lookup_generation = 0;
    bool has_deferred_noexcept_operand = false;
    size_t noexcept_operand_begin = 0;
    size_t noexcept_operand_end = 0;
    SrcLoc noexcept_operand_loc{};
    cir::DeclContextId noexcept_declaration_context{};
    uint64_t noexcept_lookup_generation = 0;
    cir::ConstraintSatisfactionKind constraint_satisfaction =
        cir::ConstraintSatisfactionKind::Unconstrained;
    uint64_t associated_constraint_fingerprint = 0;
    std::vector<uint64_t> more_constrained_than;
    cir::EntityId precreated_entity{};
};

struct RecordBaseInput {
    cir::TypeId type{};
    cir::RecordMemberAccess declared_access = cir::RecordMemberAccess::Public;
    bool is_virtual = false;
    bool is_dependent = false;
    SrcLoc loc{};
};

struct RecordDeclResult {
    cir::EntityId entity{};
    cir::TypeId type{};
    bool is_definition = false;
    bool has_error = false;
    bool fold_duplicate_definition = false;
};

struct ObjCInterfaceDeclResult {
    cir::EntityId entity{};
    cir::TypeId object_type{};
    bool has_error = false;
};

struct ObjCIvarInput {
    std::string name;
    cir::TypeRef type{};
    cir::ObjCIvarAccess access = cir::ObjCIvarAccess::Protected;
    bool is_bitfield = false;
    uint32_t bit_width = 0;
    AttributeList attrs;
    SrcLoc loc{};
};

struct ObjCMethodInput {
    std::string selector;
    bool is_class_method = false;
    cir::TypeRef return_type{};
    bool returns_instancetype = false;
    std::vector<ParamInput> params;
    bool is_variadic = false;
    bool is_optional = false;
    AttributeList attrs;
    SrcLoc loc{};
};

struct ObjCPropertyInput {
    std::string name;
    cir::TypeRef type{};
    cir::ObjCPropertyOwnership ownership =
        cir::ObjCPropertyOwnership::Assign;
    bool is_readonly = false;
    bool is_class_property = false;
    bool is_nonatomic = false;
    std::string getter;
    std::string setter;
    AttributeList attrs;
    SrcLoc loc{};
};

enum class ObjCBridgeKind : uint8_t {
    Bridge,
    BridgeRetained,
    BridgeTransfer,
};

struct ObjCMessageSendInput {
    std::optional<ExprResult> receiver;
    cir::EntityId receiver_class{};
    bool is_super = false;
    std::string selector;
    std::vector<ExprResult> args;
    SrcLoc loc{};
    bool internal = false;
};

struct EnumEnumeratorInput {
    std::string name;
    std::optional<int64_t> value;
    SrcLoc loc{};
    cir::EntityId entity{};
};

struct EnumDeclResult {
    cir::EntityId entity{};
    cir::TypeId type{};
    bool is_definition = false;
    bool has_error = false;
};

struct BlockCapture {
    std::string name;
    cir::InstId source_place{};
    cir::TypeId type{};
    cir::TypeId object_type{};
    bool is_byref = false;
    cir::TypeId byref_record{};
};

struct BlockLiteralStart {
    uint32_t index = 0;
    SrcLoc loc{};
    std::vector<ParamInput> params;
    std::vector<BlockCapture> captures;
    cir::TypeId literal_record{};
    cir::EntityId invoke_entity{};
    cir::FunctionId invoke_function{};
};

enum class LambdaCaptureDefault : uint8_t {
    None,
    ByCopy,
    ByRef,
};

struct LambdaCaptureItem {
    std::string name;
    bool by_ref = false;
    bool is_this = false;
    bool is_star_this = false;
    bool is_pack = false;
    bool is_init_pack = false;
    std::optional<ExprResult> init;
    std::vector<ExprResult> pack_inits;
    SrcLoc loc{};
};

struct LambdaSpecifiers {
    bool is_mutable = false;
    cir::FunctionExceptionSpec exception_spec;
    bool is_static = false;
    bool is_constexpr = false;
    bool is_consteval = false;
    AttributeList attrs;
};

struct LambdaClosureStart {
    uint32_t index = 0;
    SrcLoc loc{};
    cir::ClosureIdentityId closure_identity{};
    RecordDeclResult record;
    cir::EntityId call_operator{};
    cir::TypeId declared_fn_type{};
    std::vector<ParamInput> params;
    bool is_mutable = false;
    cir::FunctionExceptionSpec exception_spec;
    bool is_static = false;
    bool is_constexpr = false;
    bool is_consteval = false;
    bool deduced_return = false;
    bool is_generic = false;
    bool has_lambda_capture = false;
    bool has_error = false;
};

struct FunctionDeclStart {
    DeclResult decl;
    cir::FunctionStart function;
};

struct WhileControl {
    cir::BlockId condition_exit{};
    cir::BlockId body_block{};
    cir::BlockId continuation_block{};
    cir::BlockId condition_entry{};
    ExprResult condition;
    SrcLoc loc{};
    bool has_condition_scope = false;
};

struct ForControl {
    cir::BlockId condition_entry{};
    cir::BlockId condition_exit{};
    cir::BlockId body_block{};
    cir::BlockId step_entry{};
    cir::BlockId step_exit{};
    cir::BlockId continuation_block{};
    ExprResult condition;
    StmtResult init;
    StmtResult step;
    SrcLoc loc{};
};

struct DoWhileControl {
    cir::BlockId body_block{};
    cir::BlockId condition_block{};
    cir::BlockId continuation_block{};
    SrcLoc loc{};
};

enum class SwitchLabelKind : uint8_t {
    Case,
    Default
};

struct SwitchLabelInput {
    SwitchLabelKind kind = SwitchLabelKind::Case;
    ExprResult value;
    ExprResult range_end;
    bool has_range = false;
    SrcLoc loc{};
};

struct SwitchControl {
    size_t context_index = 0;
    SrcLoc loc{};
};

enum class TryRegionKind : uint8_t {
    Statement,
    ConstructorFunction
};

struct TryControl {
    struct Handler {
        cir::EntityId typeinfo{};
        bool is_catch_all = false;
        cir::Fragment fragment;
        bool falls_through = true;
        bool always_returns = false;
        cir::BlockId saved_unwind_target{};
        cir::BlockId cleanup_pad{};
        cir::BlockId cleanup_action{};
        cir::InstId cleanup_landing_pad{};
        SrcLoc loc{};
    };
    cir::BlockId pad_block{};
    cir::BlockId saved_unwind_target{};
    cir::InstId landing_pad{};
    cir::InstId selector{};
    cir::BlockId dispatch_block{};
    cir::InstId dispatch_exn{};
    cir::InstId dispatch_sel{};
    size_t pads_snapshot = 0;
    StmtResult body;
    std::vector<Handler> handlers;
    cir::Fragment handler_entry_fragment;
    cir::Fragment handler_decl_fragment;
    bool has_catch_all = false;
    bool has_error = false;
    bool move_boundary_pushed = false;
    TryRegionKind kind = TryRegionKind::Statement;
    SrcLoc loc{};
};

struct ObjCSynchronizedControl {
    TryControl try_control;
    cir::InstId object{};
    cir::Fragment prologue;
    bool has_error = false;
};

struct ObjCForInControl {
    cir::Fragment prologue;
    cir::Fragment condition;
    cir::Fragment refill;
    cir::Fragment prepare;
    cir::Fragment step;
    cir::InstId condition_value{};
    cir::InstId refill_empty_value{};
    cir::BlockId continuation_block{};
    SrcLoc loc{};
    bool has_error = false;
};

struct FunctionParameterPackElement {
    cir::EntityId entity{};
    cir::TypeId type{};
    cir::InstId place{};
    SrcLoc loc{};
};

} // namespace aburi::collect

#endif // ABURI_COLLECT_COLLECT_TYPES_H
