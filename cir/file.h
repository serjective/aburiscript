#ifndef ABURI_CIR_FILE_H
#define ABURI_CIR_FILE_H

#include <cstddef>
#include <cstdint>
#include <iosfwd>
#include <limits>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <variant>
#include <vector>

#include "ids.h"
#include "type.h"
#include "../abi/abi_policy.h"
#include "../attributes.h"
#include "../builtin_registry.h"
#include "../source_mgnt.h"

namespace aburi::cir {

enum class EntityKind : uint16_t {
    Invalid,
    TranslationUnit,
    Function,
    Parameter,
    Variable,
    Concept,
    TypeAlias,
    Record,
    Enum,
    Enumerator,
    Field,
    Method,
    Constructor,
    Destructor,
    TemplateParam,
    StructuredBinding,
    Namespace,
    NamespaceAlias,
    ObjCInterface,
    ObjCProtocol,
    ObjCCategory,
    ObjCImplementation,
    ObjCMethod,
    ObjCIvar,
    ObjCProperty
};

enum class EntityObjectOrigin : uint8_t {
    Ordinary,
    StructuredBindingBacking,
    AnonymousUnion,
    TemplateParameterObject,
    StringLiteral,
    TypeInfo,
    PredefinedFunctionVariable
};

enum class StorageDuration : uint8_t {
    None,
    Automatic,
    Static,
    Thread,
    Allocated,
    Temporary,
    Parameter,
    Unknown
};

enum class ExecutionSpace : uint8_t {
    Host,
    Device,
    Kernel,
    HostDevice,
    Unspecified
};

enum class RecordKind : uint8_t {
    Struct,
    Class,
    Union
};

enum class RecordMemberAccess : uint8_t {
    Public,
    Protected,
    Private
};

// ABI mangling must consume structural operator identity because reparsing the
// spelling loses distinctions between conversion and allocation functions.
enum class OperatorFunctionKind : uint8_t {
    None,
    Symbolic,
    Conversion,
    Allocation,
    Deallocation,
    Literal
};

enum class OperatorFunctionSpelling : uint8_t {
    None,
    New,
    NewArray,
    Delete,
    DeleteArray,
    CoAwait,
    Call,
    Subscript,
    Arrow,
    ArrowStar,
    BitwiseNot,
    LogicalNot,
    Plus,
    Minus,
    Multiply,
    Divide,
    Modulo,
    BitwiseXor,
    BitwiseAnd,
    BitwiseOr,
    Assign,
    AddAssign,
    SubtractAssign,
    MultiplyAssign,
    DivideAssign,
    ModuloAssign,
    XorAssign,
    AndAssign,
    OrAssign,
    LeftShift,
    RightShift,
    LeftShiftAssign,
    RightShiftAssign,
    Equal,
    NotEqual,
    Less,
    Greater,
    LessEqual,
    GreaterEqual,
    ThreeWayCompare,
    LogicalAnd,
    LogicalOr,
    Increment,
    Decrement,
    Comma
};

inline std::string_view operator_function_spelling_text(
    OperatorFunctionSpelling spelling) {
    switch (spelling) {
        case OperatorFunctionSpelling::New: return "new";
        case OperatorFunctionSpelling::NewArray: return "new[]";
        case OperatorFunctionSpelling::Delete: return "delete";
        case OperatorFunctionSpelling::DeleteArray: return "delete[]";
        case OperatorFunctionSpelling::CoAwait: return "co_await";
        case OperatorFunctionSpelling::Call: return "()";
        case OperatorFunctionSpelling::Subscript: return "[]";
        case OperatorFunctionSpelling::Arrow: return "->";
        case OperatorFunctionSpelling::ArrowStar: return "->*";
        case OperatorFunctionSpelling::BitwiseNot: return "~";
        case OperatorFunctionSpelling::LogicalNot: return "!";
        case OperatorFunctionSpelling::Plus: return "+";
        case OperatorFunctionSpelling::Minus: return "-";
        case OperatorFunctionSpelling::Multiply: return "*";
        case OperatorFunctionSpelling::Divide: return "/";
        case OperatorFunctionSpelling::Modulo: return "%";
        case OperatorFunctionSpelling::BitwiseXor: return "^";
        case OperatorFunctionSpelling::BitwiseAnd: return "&";
        case OperatorFunctionSpelling::BitwiseOr: return "|";
        case OperatorFunctionSpelling::Assign: return "=";
        case OperatorFunctionSpelling::AddAssign: return "+=";
        case OperatorFunctionSpelling::SubtractAssign: return "-=";
        case OperatorFunctionSpelling::MultiplyAssign: return "*=";
        case OperatorFunctionSpelling::DivideAssign: return "/=";
        case OperatorFunctionSpelling::ModuloAssign: return "%=";
        case OperatorFunctionSpelling::XorAssign: return "^=";
        case OperatorFunctionSpelling::AndAssign: return "&=";
        case OperatorFunctionSpelling::OrAssign: return "|=";
        case OperatorFunctionSpelling::LeftShift: return "<<";
        case OperatorFunctionSpelling::RightShift: return ">>";
        case OperatorFunctionSpelling::LeftShiftAssign: return "<<=";
        case OperatorFunctionSpelling::RightShiftAssign: return ">>=";
        case OperatorFunctionSpelling::Equal: return "==";
        case OperatorFunctionSpelling::NotEqual: return "!=";
        case OperatorFunctionSpelling::Less: return "<";
        case OperatorFunctionSpelling::Greater: return ">";
        case OperatorFunctionSpelling::LessEqual: return "<=";
        case OperatorFunctionSpelling::GreaterEqual: return ">=";
        case OperatorFunctionSpelling::ThreeWayCompare: return "<=>";
        case OperatorFunctionSpelling::LogicalAnd: return "&&";
        case OperatorFunctionSpelling::LogicalOr: return "||";
        case OperatorFunctionSpelling::Increment: return "++";
        case OperatorFunctionSpelling::Decrement: return "--";
        case OperatorFunctionSpelling::Comma: return ",";
        case OperatorFunctionSpelling::None: return {};
    }
    return {};
}

struct OperatorFunctionIdentity {
    OperatorFunctionKind kind = OperatorFunctionKind::None;
    OperatorFunctionSpelling spelling = OperatorFunctionSpelling::None;
    TypeRef conversion_type{};
    NameId literal_suffix{};

    bool valid() const { return kind != OperatorFunctionKind::None; }
    explicit operator bool() const { return valid(); }

    friend bool operator==(const OperatorFunctionIdentity& lhs,
                           const OperatorFunctionIdentity& rhs) {
        return lhs.kind == rhs.kind && lhs.spelling == rhs.spelling &&
               lhs.conversion_type == rhs.conversion_type &&
               lhs.literal_suffix == rhs.literal_suffix;
    }

    friend bool operator!=(const OperatorFunctionIdentity& lhs,
                           const OperatorFunctionIdentity& rhs) {
        return !(lhs == rhs);
    }
};

enum class DeclContextKind : uint8_t {
    Invalid,
    TranslationUnit,
    Namespace,
    Record,
    Enum,
    Function,
    Prototype,
    TemplateParameter,
    Block
};

enum class LookupNamespace : uint32_t {
    None = 0,
    Ordinary = 1u << 0,
    Tag = 1u << 1,
    Label = 1u << 2
};

enum class OrdinaryBindingCategory : uint8_t {
    Value,
    Callable,
    TypeName,
    TemplateName,
    NamespaceName
};

inline LookupNamespace operator|(LookupNamespace lhs, LookupNamespace rhs) {
    return static_cast<LookupNamespace>(
        static_cast<uint32_t>(lhs) | static_cast<uint32_t>(rhs));
}

inline LookupNamespace operator&(LookupNamespace lhs, LookupNamespace rhs) {
    return static_cast<LookupNamespace>(
        static_cast<uint32_t>(lhs) & static_cast<uint32_t>(rhs));
}

inline LookupNamespace& operator|=(LookupNamespace& lhs, LookupNamespace rhs) {
    lhs = lhs | rhs;
    return lhs;
}

inline bool lookup_namespace_contains(LookupNamespace set, LookupNamespace value) {
    return (set & value) != LookupNamespace::None;
}

enum class InstKind : uint16_t {
    Invalid,
    Param,
    IntegerLiteral,
    BooleanLiteral,
    NullptrLiteral,
    FloatingLiteral,
    CharacterLiteral,
    StringLiteral,
    NameRef,
    LocalPlace,
    GlobalPlace,
    Load,
    LValueToRValue,
    FunctionToPointer,
    MemberPointerValue,
    LabelAddress,
    Store,
    ZeroObject,
    StackAlloc,
    StackSave,
    StackRestore,
    LifetimeStart,
    LifetimeEnd,
    AtomicLoad,
    AtomicStore,
    AtomicRmw,
    AtomicCmpXchg,
    AtomicFence,
    ComplexMake,
    ComplexReal,
    ComplexImag,
    ComplexRealPlace,
    ComplexImagPlace,
    AddrOf,
    Deref,
    FieldAddr,
    DataMemberPointerPlace,
    MemberFunctionPointerCallee,
    MemberFunctionPointerThis,
    ArrayElementPlace,
    VectorElementPlace,
    VectorExtract,
    SizeofType,
    AlignofType,
    UnaryOp,
    BinaryOp,
    Cast,
    Call,
    VaStart,
    VaArg,
    VaEnd,
    VaCopy,
    BuiltinCall,
    InlineAsm,
    ConstructInPlace,
    Destroy,
    DependentCall,
    DependentRegion,
    EhAllocException,
    EhLandingPad,
    EhSelector,
    EhTypeId,
    CatchBegin,
    CatchEnd,
    ReflectValue,
    CoroBegin,
    CoroFrameSize,
    CoroFrameAlign,
    CoroPromisePlace,
    CoroSave,
    CoroTransfer,
    ObjCMessageSend,
    ObjCIvarAddr,
    ObjCSelectorLiteral,
    ObjCStringLiteral,
    ObjCArcOp,
    Error
};

enum class TerminatorKind : uint16_t {
    Invalid,
    Return,
    Branch,
    CondBranch,
    Switch,
    IndirectBranch,
    AsmGoto,
    Unreachable,
    Throw,
    Rethrow,
    Resume,
    CoroSuspend,
    CoroEnd
};

struct ValueRef {
    InstId inst{};

    ValueRef() = default;
    explicit ValueRef(InstId id) : inst(id) {}

    bool valid() const { return inst.valid(); }

    friend bool operator==(ValueRef lhs, ValueRef rhs) {
        return lhs.inst == rhs.inst;
    }

    friend bool operator!=(ValueRef lhs, ValueRef rhs) {
        return !(lhs == rhs);
    }
};

enum class OperandKind : uint8_t {
    None,
    Value,
    Type,
    Entity,
    Name,
    Specific
};

using OperandData = std::variant<std::monostate,
                                 ValueRef,
                                 TypeRef,
                                 EntityId,
                                 NameId,
                                 SpecificId>;

struct Operand {
    OperandKind kind = OperandKind::None;
    OperandData data;

    static Operand value(InstId inst) {
        return value(ValueRef(inst));
    }

    static Operand value(ValueRef ref) {
        Operand operand;
        operand.kind = OperandKind::Value;
        operand.data = ref;
        return operand;
    }

    static Operand type(TypeRef ref) {
        Operand operand;
        operand.kind = OperandKind::Type;
        operand.data = ref;
        return operand;
    }

    static Operand entity(EntityId entity) {
        Operand operand;
        operand.kind = OperandKind::Entity;
        operand.data = entity;
        return operand;
    }

    static Operand name(NameId name) {
        Operand operand;
        operand.kind = OperandKind::Name;
        operand.data = name;
        return operand;
    }

    static Operand specific(SpecificId specific) {
        Operand operand;
        operand.kind = OperandKind::Specific;
        operand.data = specific;
        return operand;
    }
};

struct OperandRange {
    uint32_t first = 0;
    uint32_t count = 0;
};

struct DeclSemanticFlags {
    bool is_constexpr = false;
    bool is_consteval = false;
    bool is_constinit = false;
    bool is_inline = false;
    bool is_thread_local = false;
    bool is_register = false;
};

struct EntityAttributeFacts {
    std::vector<ParsedAttribute> retained;
    size_t requested_alignment = 0;
    std::string section;
    std::string visibility;
    std::string asm_label;
    bool is_named_register = false;
    std::string weakref_target;
    std::string alias_target;
    std::string ifunc_target;
    std::string deprecated_message;
    std::vector<uint32_t> nonnull_params;
    int constructor_priority = -1;
    int destructor_priority = -1;
    bool is_weak = false;
    bool is_common = false;
    bool is_used = false;
    bool is_unused = false;
    bool is_deprecated = false;
    bool is_nodiscard = false;
    bool is_warn_unused_result = false;
    bool is_noreturn = false;
    bool is_gnu_inline = false;
    bool is_noinline = false;
    bool is_always_inline = false;
    bool is_excluded_from_explicit_instantiation = false;
    bool is_cold = false;
    bool is_hot = false;
    bool is_nothrow = false;
    bool is_pure = false;
    bool is_const_function = false;
    bool is_malloc = false;
    bool returns_nonnull = false;
    bool nonnull_all_pointer_params = false;
    bool has_format = false;
};

enum class LinkageKind : uint8_t {
    None,
    External,
    Internal,
    LinkOnceODR
};

enum class DefinitionEmissionKind : uint8_t {
    DeclarationOnly,
    Deferred,
    Required
};

enum class NameLinkageKind : uint8_t {
    None,
    Internal,
    Module,
    External
};

enum class LanguageLinkageKind : uint8_t {
    None,
    C,
    CXX
};

enum class SymbolVisibilityKind : uint8_t {
    Default,
    Hidden,
    Protected
};

enum class AbiIdentityKind : uint8_t {
    Declared,
    Local,
    Generated,
    Exact
};

enum class LocalNameComponentKind : uint8_t {
    None,
    SourceName,
    Lambda,
    Anonymous
};

enum class GeneratedSymbolRole : uint8_t {
    None,
    Guard,
    StaticInitializer,
    StaticCleanup,
    ThreadInitializer,
    ThreadCleanup,
    ArrayCleanup,
    VTable,
    VTT,
    ConstructionVTable,
    TypeInfo,
    TypeName,
    Thunk,
    StructorVariant,
    DeletingDestructor
};

struct SymbolPolicy {
    NameLinkageKind name_linkage = NameLinkageKind::None;
    LanguageLinkageKind name_language = LanguageLinkageKind::None;
    LanguageLinkageKind type_language = LanguageLinkageKind::None;
    LinkageKind emission = LinkageKind::None;
    DefinitionEmissionKind definition_emission =
        DefinitionEmissionKind::DeclarationOnly;
    SymbolVisibilityKind visibility = SymbolVisibilityKind::Default;
    EntityId semantic_owner{};
    EntityId abi_owner{};
    NameId comdat_key{};
    ModuleAttachmentId module_attachment{};
    GeneratedSymbolRole generated_role = GeneratedSymbolRole::None;
    bool imported_definition = false;
    bool finalized = false;
};

struct StaticInitializerRelocation {
    size_t offset = 0;
    EntityId entity{};
    int64_t addend = 0;
    BlockId block{};
    BlockId subtract_block{};
};

enum class ModuleFragment : uint8_t {
    None,
    Global,
    Purview,
    Private,
};

struct ModuleUnitFact {
    enum class Kind : uint8_t {
        PrimaryInterface,
        InterfacePartition,
        ImplementationPartition,
        Implementation,
        HeaderUnit,
    };
    Kind kind = Kind::PrimaryInterface;
    NameId module_name{};
    NameId partition_name{};
    std::vector<ModuleAttachmentId> direct_imports;
    std::vector<ModuleAttachmentId> exported_imports;
    SrcLoc loc{};
};

struct Entity {
    EntityKind kind = EntityKind::Invalid;
    NameId name{};
    // [dcl.typedef]: the first typedef-name declared with an otherwise unnamed
    // class is its class-name for linkage purposes. Keep that ABI identity
    // separate from the synthesized diagnostic/tag spelling in `name`.
    NameId unnamed_type_linkage_name{};
    static constexpr uint32_t NoUnnamedTypeOrdinal =
        std::numeric_limits<uint32_t>::max();
    uint32_t unnamed_type_ordinal = NoUnnamedTypeOrdinal;
    TypeId type{};
    EntityId parent{};
    OperatorFunctionIdentity operator_function;
    EntityId declaring_record{};
    RecordMemberAccess declared_member_access = RecordMemberAccess::Public;
    bool is_record_member = false;
    bool is_static_member_function = false;
    DeclContextId lexical_context{};
    DeclContextId semantic_context{};
    EntityId namespace_alias_target{};
    bool namespace_alias_is_dependent = false;
    EntityId owning_function{};
    EntityId structured_binding_backing{};
    uint32_t structured_binding_index =
        std::numeric_limits<uint32_t>::max();
    NameId local_source_name{};
    EntityId local_enclosing_function{};
    uint32_t local_name_ordinal = 0;
    LocalNameComponentKind local_name_kind = LocalNameComponentKind::None;
    uint32_t local_component_ordinal = 0;
    StorageDuration storage_duration = StorageDuration::Unknown;
    MemorySpace memory_space = MemorySpace::Default;
    LinkageKind linkage = LinkageKind::None;
    SymbolPolicy symbol_policy;
    AbiIdentityKind abi_identity = AbiIdentityKind::Declared;
    EntityId abi_owner{};
    GeneratedSymbolRole generated_symbol_role = GeneratedSymbolRole::None;
    ModuleAttachmentId module_attachment{};
    ModuleAttachmentId origin_unit{};
    ModuleFragment origin_fragment = ModuleFragment::None;
    bool is_module_exported = false;
    EntityId linkage_predecessor{};
    PlaceholderResultFactId placeholder_result{};
    EntityObjectOrigin object_origin = EntityObjectOrigin::Ordinary;
    EntityId object_storage_alias{};
    InstId object_storage_alias_place{};
    bool is_function_result_object = false;
    bool is_exception_declaration = false;
    bool is_parameter_argument_object = false;
    uint8_t qualifiers = QualNone;
    DeclSemanticFlags decl_flags;
    EntityAttributeFacts attr_facts;
    bool is_definition = true;
    bool has_deferred_definition = false;
    bool is_deleted = false;
    bool is_unnamed_record = false;
    bool inline_definition_only = false;
    bool declared_with_extern = false;
    bool is_extern_c = false;
    bool is_block_byref = false;
    bool is_template_pattern = false;
    bool result_type_only_definition = false;
    bool suppressed_by_explicit_instantiation_declaration = false;
    bool suppressed_as_unselected_template_candidate = false;
    bool is_explicit_instantiation_definition = false;
    bool is_explicit_template_specialization = false;
    bool has_static_initializer = false;
    bool has_initializer = false;
    bool initializer_is_value_dependent = false;
    std::vector<uint8_t> static_initializer_bytes;
    std::vector<StaticInitializerRelocation> static_initializer_relocations;
    bool has_constant_value = false;
    TemplateValueKind constant_value_kind = TemplateValueKind::Integer;
    TemplateNullKind constant_null_kind = TemplateNullKind::None;
    IntegerValue constant_integer_value;
    FloatingValue constant_floating_value;
    EntityId constant_entity{};
    ClosureIdentityId constant_closure_identity{};
    MetaInfoKind constant_meta_kind = MetaInfoKind::Null;
    TypeRef constant_meta_type{};
    int64_t constant_byte_offset = 0;
    std::vector<TemplateArgument> constant_value_elements;
    ConstantStateId constant_state{};
    EntityId template_parameter_object{};
    SrcLoc loc{};
};

struct MemberUsingOrigin {
    EntityId entity{};
    EntityId importing_record{};
    EntityId nominated_record{};
    uint32_t using_fact_index = std::numeric_limits<uint32_t>::max();
    RecordMemberAccess declared_access = RecordMemberAccess::Public;
    SrcLoc loc{};
};

struct Binding {
    NameId name{};
    DeclContextId context{};
    LookupNamespace lookup_namespace = LookupNamespace::Ordinary;
    std::vector<EntityId> entities;
    std::vector<uint64_t> entity_generations;
    std::vector<MemberUsingOrigin> member_using_origins;
    TypeRef type{};
    InstId place{};
    bool is_type_name = false;
    bool is_template_name = false;
    bool dependent_member_using = false;
    bool is_definition = false;
    bool has_block_scope_function_declaration = false;
    uint64_t generation = 0;
    SrcLoc loc{};
};

enum class AnonymousUnionObjectKind : uint8_t {
    None,
    Member,
    BlockVariable,
    NamespaceVariable,
};

struct AnonymousUnionPromotionFact {
    NameId name{};
    EntityId member{};
    std::vector<EntityId> path;
};

struct VariantMemberFact {
    EntityId member{};
    EntityId owning_union{};
    std::vector<EntityId> path;
};

struct DeclContext {
    DeclContextKind kind = DeclContextKind::Invalid;
    EntityId owner{};
    DeclContextId parent{};
    std::vector<DeclContextId> children;
    std::vector<BindingId> bindings;
    std::unordered_map<uint64_t, BindingId> ordinary_latest_bindings;
    std::unordered_map<uint64_t, BindingId> ordinary_value_bindings;
    std::unordered_map<uint64_t, BindingId> ordinary_callable_bindings;
    std::unordered_map<uint64_t, BindingId> ordinary_type_name_bindings;
    std::unordered_map<uint64_t, BindingId> ordinary_template_name_bindings;
    std::unordered_map<uint64_t, BindingId> ordinary_namespace_bindings;
    std::unordered_map<uint64_t, BindingId> tag_bindings;
    std::unordered_map<uint64_t, BindingId> label_bindings;
    std::vector<DeclContextId> using_directives;
    std::vector<ModuleAttachmentId> using_directive_origins;
    bool is_inline_namespace = false;
    SrcLoc loc{};
};

enum class DeclContextIndexKind : uint8_t {
    OrdinaryLatest,
    OrdinaryValue,
    OrdinaryCallable,
    OrdinaryTypeName,
    OrdinaryTemplateName,
    OrdinaryNamespace,
    Tag,
    Label,
};

struct DeclContextDelta {
    enum class Kind : uint8_t {
        BindingAppended,
        ChildAppended,
        UsingDirectiveAppended,
        IndexAssigned,
    };
    uint32_t context = 0;
    Kind kind = Kind::BindingAppended;
    DeclContextIndexKind index = DeclContextIndexKind::OrdinaryLatest;
    bool had_previous = false;
    uint64_t key = 0;
    BindingId previous{};
};

struct RecordDefinitionData {
    bool has_user_declared_constructor = false;
    bool has_inherited_constructor = false;
    bool has_default_constructor = false;
    bool default_constructor_is_deleted = false;
    bool has_copy_constructor = false;
    bool has_move_constructor = false;
    bool has_user_declared_copy_constructor = false;
    bool has_user_declared_move_constructor = false;
    bool has_copy_assignment = false;
    bool has_move_assignment = false;
    bool has_user_declared_copy_assignment = false;
    bool has_user_declared_move_assignment = false;
    bool has_user_declared_destructor = false;
    bool has_deleted_destructor = false;
};

enum class SubobjectSizeKind : uint8_t {
    NonZero,
    Zero,
    Dependent
};

enum class LambdaCaptureFieldKind : uint8_t {
    None,
    Entity,
    Init,
    ThisPointer,
    ThisObject,
};

struct RecordFieldFact {
    NameId name{};
    EntityId entity{};
    TypeRef type{};
    EntityId lambda_capture_source{};
    LambdaCaptureFieldKind lambda_capture_kind =
        LambdaCaptureFieldKind::None;
    RecordMemberAccess declared_access = RecordMemberAccess::Public;
    size_t offset = 0;
    size_t forced_alignment = 0;
    size_t storage_size_override = 0;
    size_t storage_alignment_override = 0;
    bool is_bitfield = false;
    bool is_flexible_array_member = false;
    uint32_t bit_offset = 0;
    uint32_t bit_width = 0;
    TemplateValueExpression bit_width_expression;
    bool bit_width_is_dependent = false;
    uint32_t storage_size = 0;
    bool is_mutable = false;
    bool is_anonymous_union_object = false;
    bool is_base_subobject = false;
    bool is_virtual_base_storage = false;
    bool is_no_unique_address = false;
    bool is_potentially_overlapping = false;
    SubobjectSizeKind subobject_size = SubobjectSizeKind::NonZero;
    bool has_default_member_initializer = false;
    bool default_member_initializer_braced = false;
    uint32_t default_member_initializer_begin = 0;
    uint32_t default_member_initializer_end = 0;
    SrcLoc default_member_initializer_loc{};
    DeclContextId default_member_initializer_context{};
    uint64_t default_member_initializer_lookup_generation = 0;
    bool default_member_initializer_potentially_throwing = false;
    bool default_member_initializer_throwing_dependent = false;
    std::vector<ParsedAttribute> attributes;
};

struct RecordBaseFact {
    NameId name{};
    TypeRef type{};
    RecordMemberAccess declared_access = RecordMemberAccess::Public;
    EntityId record_entity{};
    bool is_virtual = false;
    bool has_non_virtual_offset = false;
    size_t non_virtual_offset = 0;
    uint32_t declaration_index = 0;
};

enum class ConstraintSatisfactionKind : uint8_t {
    Unconstrained,
    Dependent,
    Satisfied,
    Unsatisfied,
    Invalid
};

enum class ExplicitSpecifierKind : uint8_t {
    Absent,
    True,
    False,
    Dependent,
    Invalid
};

enum class SpecialMemberKind : uint8_t {
    None,
    DefaultConstructor,
    CopyConstructor,
    MoveConstructor,
    CopyAssignment,
    MoveAssignment,
    Destructor
};

enum class ClassPropertyState : uint8_t {
    False,
    True,
    Dependent,
    Unavailable
};

struct VirtualSubobjectFact {
    uint32_t id = 0;
    EntityId record_entity{};
    TypeRef type{};
    std::vector<EntityId> storage_path;
    size_t static_offset_bytes = 0;
    bool is_virtual = false;
};

struct VirtualSubobjectEdgeFact {
    uint32_t derived_subobject = 0;
    uint32_t base_subobject = 0;
    RecordMemberAccess declared_access = RecordMemberAccess::Public;
    uint32_t declaration_index = 0;
    bool is_virtual = false;
};

enum class VirtualReturnRelation : uint8_t {
    Identical,
    Covariant,
    Invalid,
    Dependent,
};

struct VirtualOverrideEdgeFact {
    EntityId overriding{};
    EntityId overridden{};
    uint32_t overriding_subobject = 0;
    uint32_t overridden_subobject = 0;
    VirtualReturnRelation return_relation = VirtualReturnRelation::Dependent;
    std::vector<EntityId> covariance_path;
    bool predicate_dependent = false;
};

struct VirtualFinalOverriderFact {
    EntityId virtual_declaration{};
    uint32_t declaration_subobject = 0;
    EntityId final_overrider{};
    uint32_t final_subobject = 0;
    std::vector<EntityId> conflict_candidates;

    bool has_conflict() const { return !conflict_candidates.empty(); }
};

enum class VirtualAdjustmentKind : uint8_t {
    None,
    NonVirtual,
    Virtual,
};

struct VirtualAdjustmentFact {
    VirtualAdjustmentKind kind = VirtualAdjustmentKind::None;
    int64_t static_offset_bytes = 0;
    int64_t vtable_offset_bytes = 0;
    std::vector<EntityId> path;

    bool required() const { return kind != VirtualAdjustmentKind::None; }
};

struct VirtualTableSlotFact {
    EntityId declaration{};
    EntityId final_overrider{};
    uint32_t declaration_subobject = 0;
    uint32_t final_subobject = 0;
    VirtualAdjustmentFact this_adjustment;
    VirtualAdjustmentFact result_adjustment;
    bool is_deleting_destructor = false;
    bool runtime_callable = true;
};

enum class PotentiallyConstructedSubobjectKind : uint8_t {
    DirectBase,
    VirtualBase,
    NonStaticDataMember
};

struct PotentiallyConstructedSubobjectFact {
    PotentiallyConstructedSubobjectKind kind =
        PotentiallyConstructedSubobjectKind::NonStaticDataMember;
    EntityId entity{};
    TypeRef type{};
};

// Canonical [expr.new]/[expr.delete] operator classification.  The selected
// entity is retained independently of the eventual call instruction so
// constructor-failure cleanup and deleting-destructor synthesis cannot infer
// a different ABI entry point from an object's size or virtuality.
struct AllocationFunctionForm {
    bool is_array = false;
    bool is_placement = false;
    bool is_aligned = false;
    bool is_nonallocating = false;
    bool is_nonthrowing = false;
};

struct DeallocationFunctionForm {
    bool is_array = false;
    bool is_placement = false;
    bool is_sized = false;
    bool is_aligned = false;
    bool is_destroying = false;
};

struct DeallocationFunctionSelectionFact {
    EntityId entity{};
    DeallocationFunctionForm form;

    bool valid() const { return entity.valid(); }
};

struct InheritedConstructorRouteFact {
    EntityId nominated_direct_base{};
    uint32_t origin_subobject = std::numeric_limits<uint32_t>::max();
    SrcLoc using_loc{};
};

struct InheritedConstructorFact {
    // Identity is never flattened through an inherited-constructor chain.
    // Default arguments, access, constraints, and ABI naming consult this
    // ultimate declaration and its owning record.
    EntityId origin_constructor{};
    EntityId origin_record{};
    std::vector<InheritedConstructorRouteFact> routes;
};

enum class ConstructorDelegationState : uint8_t {
    Dependent,
    Resolved
};

enum class ConstructorDelegationInitializationKind : uint8_t {
    Parenthesized,
    Braced
};

struct ConstructorDelegationFact {
    ConstructorDelegationState state =
        ConstructorDelegationState::Dependent;
    ConstructorDelegationInitializationKind initialization_kind =
        ConstructorDelegationInitializationKind::Parenthesized;
    EntityId target_constructor{};
    SrcLoc initializer_loc{};

    bool resolved() const {
        return state == ConstructorDelegationState::Resolved;
    }
};

struct FunctionParameterScopeFact {
    NameId name{};
    TypeRef type{};
    SrcLoc loc{};
    bool is_parameter_pack = false;
    NameId source_parameter_pack_name{};
    bool is_parameter_pack_expansion_sentinel = false;
    bool type_originates_from_template_parameter = false;
};

struct RecordMethodFact {
    NameId name{};
    TypeRef type{};
    RecordMemberAccess declared_access = RecordMemberAccess::Public;
    EntityId entity{};
    OperatorFunctionIdentity operator_function;
    bool is_static = false;
    bool is_function_template = false;
    bool is_conversion_function = false;
    bool is_virtual = false;
    bool is_override = false;
    bool overrides_base = false;
    bool is_final = false;
    bool is_deleted = false;
    bool is_defaulted = false;
    bool is_pure = false;
    bool is_constexpr = false;
    bool is_consteval = false;
    bool has_explicit_exception_spec = false;
    bool has_deferred_noexcept_operand = false;
    uint32_t noexcept_operand_begin = 0;
    uint32_t noexcept_operand_end = 0;
    SrcLoc noexcept_operand_loc{};
    DeclContextId noexcept_declaration_context{};
    uint64_t noexcept_lookup_generation = 0;
    std::vector<FunctionParameterScopeFact> declarator_parameters;
    bool is_selected_destructor = false;
    bool is_explicit = false;
    SpecialMemberKind special_member_kind = SpecialMemberKind::None;
    bool is_implicitly_declared = false;
    EntityId implicit_equality_origin{};
    bool is_user_provided = false;
    // Candidate status at the end of the class definition. It is retained
    // separately because a later out-of-class inline definition changes the
    // entity's final inline bit, while some Itanium ABI variants keep the
    // originally selected key function and others disqualify it.
    bool is_key_function_candidate = false;
    bool is_eligible = true;
    bool is_trivial = false;
    bool has_computed_exception_spec = false;
    std::vector<PotentiallyConstructedSubobjectFact>
        potentially_constructed_subobjects;
    ExplicitSpecifierKind explicit_specifier = ExplicitSpecifierKind::Absent;
    size_t explicit_expression_begin = 0;
    size_t explicit_expression_end = 0;
    TemplateValueExpression explicit_value_expression;
    DeclContextId explicit_declaration_context{};
    uint64_t explicit_lookup_generation = 0;
    ConstraintSatisfactionKind constraint_satisfaction =
        ConstraintSatisfactionKind::Unconstrained;
    uint64_t associated_constraint_fingerprint = 0;
    std::vector<uint64_t> more_constrained_than;
    SrcLoc first_required_loc{};
    uint64_t first_required_lookup_generation = 0;
    int32_t vtable_slot = -1;
    DeallocationFunctionSelectionFact deleting_destructor_deallocation;
    std::optional<InheritedConstructorFact> inherited_constructor;
    std::optional<ConstructorDelegationFact> constructor_delegation;
    std::vector<ParsedAttribute> attributes;
};

struct RecordStaticDataMemberFact {
    NameId name{};
    TypeRef type{};
    RecordMemberAccess declared_access = RecordMemberAccess::Public;
    EntityId entity{};
    bool is_constexpr = false;
    bool is_consteval = false;
    bool is_inline = false;
    bool has_in_class_initializer = false;
    size_t initializer_begin = 0;
    size_t initializer_end = 0;
    SrcLoc initializer_loc{};
    DeclContextId initializer_context{};
    uint64_t initializer_lookup_generation = 0;
    TemplateValueExpression initializer_value_expression;
    std::vector<ParsedAttribute> attributes;
};

enum class DefaultedComparisonKind : uint8_t {
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    ThreeWay,
};

enum class ComparisonSubobjectKind : uint8_t {
    DirectBase,
    Field,
};

struct ComparisonSubobjectFact {
    ComparisonSubobjectKind kind = ComparisonSubobjectKind::Field;
    EntityId entity{};
    TypeRef type{};
    std::vector<size_t> array_extents;
    TypeRef array_leaf_type{};
    size_t array_element_count = 0;
    EntityId selected_operator{};
    bool selected_builtin = false;
    bool selected_rewritten = false;
    bool selected_reversed = false;
    bool usable = true;
};

struct DefaultedComparisonFact {
    EntityId function{};
    EntityId owner_record{};
    DefaultedComparisonKind kind = DefaultedComparisonKind::Equal;
    TypeRef result_type{};
    EntityId implicit_equality_origin{};
    std::vector<ComparisonSubobjectFact> subobjects;
    bool is_friend = false;
    bool is_implicit_equality = false;
    bool is_dependent = false;
    bool is_deleted = false;
    bool is_constexpr = false;
    bool is_noexcept = false;
    std::string deletion_reason;
};

enum class StructuredBindingStrategy : uint8_t {
    Dependent,
    Array,
    Tuple,
    Member,
    Invalid,
};

struct StructuredBindingProjectionFact {
    EntityId binding{};
    EntityId holder{};
    EntityId member{};
    std::vector<EntityId> base_path;
    TypeRef type{};
    TypeRef referenced_type{};
    uint32_t index = 0;
    bool is_bitfield = false;
    bool is_pack_element = false;
    bool is_dependent = false;
    SrcLoc loc{};
};

struct StructuredBindingFact {
    EntityId backing{};
    TypeRef decomposed_type{};
    StructuredBindingStrategy strategy = StructuredBindingStrategy::Invalid;
    std::vector<NameId> source_names;
    std::vector<StructuredBindingProjectionFact> projections;
    bool has_pack = false;
    uint32_t pack_position = std::numeric_limits<uint32_t>::max();
    bool is_condition = false;
    bool is_dependent = false;
    SrcLoc loc{};
};

struct RecordDependentBaseFact {
    TypeRef type;
    RecordMemberAccess declared_access = RecordMemberAccess::Public;
    bool is_virtual = false;
    uint32_t declaration_index = 0;
};

enum class RecordClassFriendGrantKind : uint8_t {
    ExactRecord,
    PrimaryClassTemplate,
    DependentRecipe,
};

enum class RecordClassFriendRecipeKind : uint8_t {
    DirectType,
    MemberOfClassTemplate,
};

struct RecordClassFriendGrant {
    RecordClassFriendGrantKind kind =
        RecordClassFriendGrantKind::ExactRecord;
    RecordClassFriendRecipeKind recipe_kind =
        RecordClassFriendRecipeKind::DirectType;
    EntityId entity{};
    TypeRef type_pattern{};
    NameId member_name{};
    std::vector<uint32_t> required_type_params;
    std::vector<uint32_t> required_value_params;
    std::vector<uint32_t> required_template_params;
    bool is_pack_expansion = false;
    SrcLoc loc{};
};

enum class TemplateParameterPatternKind : uint8_t {
    Type,
    NonType,
    Template,
};

struct TemplateParameterPattern {
    TemplateParameterPatternKind kind = TemplateParameterPatternKind::Type;
    bool is_parameter_pack = false;
    TypeId type_param_type{};
    TypeRef non_type_type{};
    std::vector<TemplateParameterPattern> template_parameters;
};

enum class RecordFunctionFriendGrantKind : uint8_t {
    ExactFunction,
    PrimaryFunctionTemplate,
    FunctionTemplateSpecialization,
    DependentMemberFunction,
    DependentMemberFunctionTemplate,
};

// [class.friend]/[temp.friend]: every function friendship grant carries one
// canonical declaration identity or one retained dependent recipe. Hidden
// namespace ownership and ordinary visibility are deliberately not encoded by
// spelling: ExactFunction names the namespace/member function entity,
// PrimaryFunctionTemplate names the primary, and specialization grants retain
// the primary plus canonical arguments.
struct RecordFunctionFriendGrant {
    RecordFunctionFriendGrantKind kind =
        RecordFunctionFriendGrantKind::ExactFunction;
    EntityId entity{};
    DeclContextId context{};
    ModuleAttachmentId module_attachment{};
    EntityId signature_owner{};
    NameId name{};
    TypeRef type_pattern{};
    std::vector<TemplateArgument> arguments;
    TypeRef qualifier_pattern{};
    NameId member_name{};
    std::vector<TemplateParameterPattern> member_template_parameters;
    std::vector<uint32_t> required_type_params;
    std::vector<uint32_t> required_value_params;
    std::vector<uint32_t> required_template_params;
    SrcLoc loc{};
};

struct RecordUsingDeclarationEntry {
    EntityId entity{};
    EntityId hidden_by{};
};

struct RecordUsingDeclarationFact {
    NameId terminal_name{};
    EntityId nominated_entity{};
    TypeRef dependent_qualifier{};
    RecordMemberAccess declared_access = RecordMemberAccess::Public;
    std::vector<RecordUsingDeclarationEntry> entries;
    bool uses_typename = false;
    bool base_validation_deferred = false;
    SrcLoc loc{};
};

struct RecordInheritedConstructorNominationFact {
    EntityId nominated_record{};
    TypeRef dependent_qualifier{};
    bool base_validation_deferred = false;
    SrcLoc loc{};
};

enum class ClosureAbiContextKind : uint8_t {
    TranslationUnit,
    FunctionBody,
    DefaultArgument,
    VariableInitializer,
};

struct ClosureIdentityFact {
    SrcLoc source_loc{};
    SrcLoc key_loc{};
    EntityId lexical_owner{};
    NameId abi_context_name{};
    DeclContextId abi_context_decl{};
    EntityId record{};
    TypeRef type{};
    EntityId call_operator{};
    EntityId invoker{};
    ClosureAbiContextKind abi_context =
        ClosureAbiContextKind::TranslationUnit;
    bool is_structural = false;
    bool is_generic = false;
};

struct RecordFacts {
    EntityId entity{};
    TypeRef type{};
    RecordKind kind = RecordKind::Struct;
    bool is_incomplete = true;
    bool is_template_pattern_provisional = false;
    bool is_final = false;
    bool is_polymorphic = false;
    bool is_abstract = false;
    ClassPropertyState is_consteval_only = ClassPropertyState::False;
    bool is_literal_class_type = false;
    ClassPropertyState is_aggregate = ClassPropertyState::Unavailable;
    ClassPropertyState is_trivial = ClassPropertyState::Unavailable;
    ClassPropertyState is_trivially_copyable =
        ClassPropertyState::Unavailable;
    ClassPropertyState is_empty = ClassPropertyState::Unavailable;
    ClassPropertyState is_standard_layout = ClassPropertyState::Unavailable;
    ClassPropertyState is_implicit_lifetime =
        ClassPropertyState::Unavailable;
    bool is_non_trivial_for_calls = false;
    bool has_virtual_destructor = false;
    bool is_packed = false;
    bool is_transparent_union = false;
    bool has_flexible_array_member = false;
    bool is_lambda_closure = false;
    bool lambda_has_capture = false;
    ClosureIdentityId closure_identity{};
    size_t requested_alignment = 0;
    size_t pack_alignment = 0;
    std::vector<ParsedAttribute> attributes;
    RecordDefinitionData definition_data;
    std::vector<RecordBaseFact> bases;
    std::vector<RecordDependentBaseFact> dependent_bases;
    std::vector<RecordFieldFact> fields;
    AnonymousUnionObjectKind anonymous_union_object_kind =
        AnonymousUnionObjectKind::None;
    bool is_anonymous_union_definition = false;
    EntityId anonymous_union_object{};
    DeclContextId anonymous_union_parent_context{};
    std::vector<AnonymousUnionPromotionFact> anonymous_union_promotions;
    bool is_union_like = false;
    std::vector<VariantMemberFact> variant_members;
    std::vector<RecordMethodFact> methods;
    std::vector<RecordStaticDataMemberFact> static_data_members;
    std::vector<RecordUsingDeclarationFact> using_declarations;
    std::vector<RecordInheritedConstructorNominationFact>
        inherited_constructor_nominations;
    std::vector<VirtualSubobjectFact> virtual_subobjects;
    std::vector<VirtualSubobjectEdgeFact> virtual_subobject_edges;
    std::vector<VirtualOverrideEdgeFact> virtual_override_edges;
    std::vector<VirtualFinalOverriderFact> virtual_final_overriders;
    bool virtual_graph_dependent = false;
    EntityId key_function{};
    std::vector<RecordClassFriendGrant> class_friends;
    std::vector<RecordFunctionFriendGrant> function_friends;
    std::vector<EntityId> vtable_slots;
    std::vector<VirtualTableSlotFact> primary_vtable_slot_facts;
    EntityId vtable_entity{};
    EntityId typeinfo_entity{};
    EntityId vtt_entity{};
    struct SecondaryVtable {
        EntityId base_field{};
        std::vector<EntityId> storage_path;
        size_t base_offset_bytes = 0;
        size_t address_point_bytes = 0;
        TypeRef base_type;
        bool is_virtual = false;
        std::vector<EntityId> slots;
        std::vector<VirtualTableSlotFact> slot_facts;
    };
    std::vector<SecondaryVtable> secondary_vtables;
    struct VirtualBase {
        EntityId record_entity{};
        TypeRef type;
        EntityId storage_field{};
        size_t storage_offset_bytes = 0;
        size_t vtable_index = 0;
    };
    std::vector<VirtualBase> virtual_bases;
    size_t vtable_address_point = 16;
    size_t non_virtual_size_bits = 0;
    size_t non_virtual_alignment = 1;
    size_t size_bits = 0;
    size_t alignment = 1;
};

enum class ObjCIvarAccess : uint8_t {
    Private,
    Protected,
    Public,
    Package
};

// The Objective-C ARC ABI must infer retained results and consumed receivers
// from method families unless an ownership attribute overrides the convention.
enum class ObjCMethodFamily : uint8_t {
    None,
    Alloc,
    Copy,
    Init,
    MutableCopy,
    New,
    Retain,
    Release,
    Autorelease,
    Dealloc
};

struct ObjCIvarFact {
    EntityId entity{};
    NameId name{};
    TypeRef type{};
    ObjCIvarAccess access = ObjCIvarAccess::Protected;
    bool is_bitfield = false;
    uint32_t bit_width = 0;
    size_t offset_bytes = 0;
    EntityId offset_variable{};
    bool is_property_backing = false;
    std::vector<ParsedAttribute> attributes;
    SrcLoc loc{};
};

struct ObjCMethodFact {
    EntityId entity{};
    SelectorId selector{};
    TypeId function_type{};
    TypeRef return_type{};
    bool is_class_method = false;
    bool is_variadic = false;
    bool returns_instancetype = false;
    ObjCMethodFamily family = ObjCMethodFamily::None;
    bool is_optional = false;
    bool is_property_accessor = false;
    EntityId definition{};
    std::vector<ParsedAttribute> attributes;
    SrcLoc loc{};
};

enum class ObjCPropertyOwnership : uint8_t {
    Assign,
    Retain,
    Copy,
    Strong,
    Weak,
    UnsafeUnretained
};

struct ObjCPropertyFact {
    EntityId entity{};
    NameId name{};
    TypeRef type{};
    ObjCPropertyOwnership ownership = ObjCPropertyOwnership::Assign;
    bool is_readonly = false;
    bool is_class_property = false;
    bool is_nonatomic = false;
    SelectorId getter{};
    SelectorId setter{};
    EntityId getter_method{};
    EntityId setter_method{};
    EntityId backing_ivar{};
    NameId spelled_backing_name{};
    bool is_dynamic = false;
    std::vector<ParsedAttribute> attributes;
    SrcLoc loc{};
};

struct ObjCInterfaceFacts {
    EntityId entity{};
    NameId name{};
    TypeId object_type{};
    EntityId super_class{};
    bool is_forward_only = true;
    bool is_defined = false;
    std::vector<ObjCIvarFact> ivars;
    std::vector<ObjCMethodFact> instance_methods;
    std::vector<ObjCMethodFact> class_methods;
    std::vector<ObjCPropertyFact> properties;
    std::vector<EntityId> protocols;
    std::vector<EntityId> categories;
    EntityId implementation{};
    EntityId protocol_reference{};
    EntityId ehtype{};
    size_t instance_start_bytes = 0;
    size_t instance_size_bytes = 0;
    bool layout_computed = false;
    bool has_nontrivial_cxx_ivars = false;
    std::vector<EntityId> cxx_construct_ivars;
    std::vector<ParsedAttribute> attributes;
    SrcLoc loc{};
};

struct PlaceFact {
    TypeRef object_type{};
    StorageDuration storage_duration = StorageDuration::Unknown;
    EntityId entity{};
    InstId base{};
    InstId source{};
    bool addressable = true;
    bool modifiable = true;
    SrcLoc loc{};
};

struct SwitchCaseRange {
    int64_t low = 0;
    int64_t high = 0;
    BlockId target{};
    SrcLoc loc{};
};

struct SwitchTerminatorPayload {
    TypeRef condition_type{};
    std::vector<SwitchCaseRange> cases;
};

enum class CoroSaveKind : uint8_t {
    Initial,
    User,
    Final
};

struct CoroSuspendPayload {
    uint32_t index = 0;
    CoroSaveKind kind = CoroSaveKind::User;
};

struct SwitchFact {
    ValueRef condition{};
    TypeRef condition_type{};
    BlockId dispatch_block{};
    BlockId default_block{};
    BlockId end_block{};
    std::vector<SwitchCaseRange> cases;
    SrcLoc loc{};
};

struct CoroutineFact {
    EntityId function{};
    TypeId promise_type{};
    BlockId ramp_return_block{};
    BlockId alloc_failure_block{};
    BlockId eh_action_block{};
    uint32_t suspend_count = 0;
    EntityId frame_record{};
    EntityId resume_function{};
    EntityId destroy_function{};
};

using LiteralByteArray = std::vector<uint8_t>;
using LiteralValue = std::variant<std::monostate,
                                  IntegerValue,
                                  FloatingValue,
                                  bool,
                                  LiteralByteArray>;

struct LiteralPayload {
    LiteralValue value;
    std::string spelling;
};

enum class UnaryOpKind : uint8_t {
    Invalid,
    Plus,
    Minus,
    LogicalNot,
    BitwiseNot
};

enum class BinaryOpKind : uint8_t {
    Invalid,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Equal,
    NotEqual,
    LogicalAnd,
    LogicalOr,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Comma
};

enum class OperatorValueDomain : uint8_t {
    Unknown,
    Bool,
    SignedInteger,
    UnsignedInteger,
    Floating,
    Complex,
    Pointer
};

struct UnaryOpDescriptor {
    UnaryOpKind op = UnaryOpKind::Invalid;
    TypeRef computation_type{};
};

struct BinaryOpDescriptor {
    BinaryOpKind op = BinaryOpKind::Invalid;
    TypeRef computation_type{};
};

struct CastPayload {
    std::string kind;
};

struct CallPayload {
    EntityId virtual_declaration{};
    bool must_tail = false;
};

struct ErrorPayload {
    std::string message;
};

struct DependentRegionPayload {
    uint32_t hole = 0;
    std::string display;
};

struct EhLandingPadPayload {
    bool is_cleanup = false;
    bool has_catch_all = false;
    std::vector<EntityId> clause_typeinfos;
};

struct BuiltinCallPayload {
    BuiltinKind kind = BuiltinKind::EXPECT;
    std::string name;
    TypeRef type_operand{};
    std::vector<int64_t> integer_operands;
};

struct ReflectPayload {
    MetaInfoKind kind = MetaInfoKind::Type;
};

struct LabelAddressPayload {
    NameId name{};
    BlockId target{};
};

struct InlineAsmOperandPayload {
    NameId symbolic_name{};
    std::string constraint;
    bool is_output = false;
    std::string register_binding;
};

struct InlineAsmPayload {
    std::string asm_string;
    std::string constraints;
    std::vector<InlineAsmOperandPayload> outputs;
    std::vector<InlineAsmOperandPayload> inputs;
    std::vector<std::string> clobbers;
    std::vector<NameId> goto_labels;
    std::vector<BlockId> goto_targets;
    bool has_side_effects = false;
    bool is_inline = false;
    bool is_goto = false;
    bool align_stack = false;
    bool intel_dialect = false;
};

struct InlineAsmPayloadRef {
    InlineAsmPayloadId payload{};
};

enum class MemoryOrder : uint8_t {
    Relaxed = 0,
    Consume = 1,
    Acquire = 2,
    Release = 3,
    AcqRel = 4,
    SeqCst = 5,
};

enum class AtomicRmwOp : uint8_t {
    Xchg,
    Add,
    Sub,
    And,
    Or,
    Xor,
    Nand,
};

struct AtomicPayload {
    MemoryOrder order = MemoryOrder::SeqCst;
    MemoryOrder failure_order = MemoryOrder::SeqCst;
    AtomicRmwOp rmw_op = AtomicRmwOp::Xchg;
    bool is_weak = false;
};

enum class ObjCReceiverKind : uint8_t {
    Instance,
    Class,
    Super,
    SuperClass
};

struct ObjCMessageSendPayload {
    SelectorId selector{};
    EntityId method_declaration{};
    EntityId interface_context{};
    ObjCReceiverKind receiver_kind = ObjCReceiverKind::Instance;
};

struct ObjCSelectorLiteralPayload {
    SelectorId selector{};
};

enum class ObjCArcOpKind : uint8_t {
    Retain,
    Release,
    Autorelease,
    RetainAutoreleasedReturnValue,
    AutoreleaseReturnValue,
    StoreStrong,
    LoadWeak,
    StoreWeak,
    InitWeak,
    DestroyWeak,
    MoveWeak,
    CopyWeak,
    RetainBlock,
};

struct ObjCArcOpPayload {
    ObjCArcOpKind op = ObjCArcOpKind::Retain;
};

using InstPayload = std::variant<std::monostate,
                                 LiteralPayload,
                                 AtomicPayload,
                                 UnaryOpDescriptor,
                                 BinaryOpDescriptor,
                                 CastPayload,
                                 CallPayload,
                                 BuiltinCallPayload,
                                 ReflectPayload,
                                 LabelAddressPayload,
                                 SwitchTerminatorPayload,
                                 InlineAsmPayloadRef,
                                 ErrorPayload,
                                 DependentRegionPayload,
                                 EhLandingPadPayload,
                                 CoroSuspendPayload,
                                 ObjCMessageSendPayload,
                                 ObjCSelectorLiteralPayload,
                                 ObjCArcOpPayload>;

static_assert(sizeof(ObjCMessageSendPayload) <= sizeof(LiteralPayload),
              "ObjCMessageSendPayload must not widen InstPayload");
static_assert(sizeof(ObjCSelectorLiteralPayload) <= sizeof(LiteralPayload),
              "ObjCSelectorLiteralPayload must not widen InstPayload");
static_assert(sizeof(ObjCArcOpPayload) <= sizeof(LiteralPayload),
              "ObjCArcOpPayload must not widen InstPayload");

struct Inst {
    InstKind kind = InstKind::Invalid;
    TypeId result_type{};
    PlaceFactId place_fact{};
    OperandRange operands{};
    uint32_t payload_index = 0;
    EntityId result_object_entity{};
    bool runtime_elided_object_operation = false;
    SrcLoc loc{};
};

struct Terminator {
    TerminatorKind kind = TerminatorKind::Invalid;
    OperandRange operands{};
    BlockId target{};
    BlockId false_target{};
    uint32_t payload_index = 0;
    SrcLoc loc{};
};

struct Block {
    NameId name{};
    std::vector<InstId> parameters;
    std::vector<InstId> instructions;
    Terminator terminator{};
    BlockId unwind_target{};
};

struct FunctionParameter {
    EntityId entity{};
    ValueRef value{};
};

struct Fragment {
    std::vector<BlockId> blocks;
    BlockId entry{};
    BlockId exit{};
    bool falls_through = true;

    bool empty() const { return blocks.empty(); }
};

struct Function {
    EntityId entity{};
    TypeId type{};
    TypeId result_type{};
    ExecutionSpace execution_space = ExecutionSpace::Host;
    std::vector<FunctionParameter> parameters;
    std::vector<BlockId> blocks;
    BlockId entry_block{};
    SrcLoc loc{};
};

enum class PlaceholderResultState : uint8_t {
    Undeduced,
    Deducing,
    Complete,
    Failed,
};

struct PlaceholderResultFact {
    TypeId declared_function_type{};
    TypeRef declared_return_pattern{};
    TypeRef candidate{};
    TypeRef result{};
    EntityId defining_entity{};
    SrcLoc declaration_loc{};
    SrcLoc first_return_loc{};
    PlaceholderResultState state = PlaceholderResultState::Undeduced;
    bool conflict_diagnosed = false;
    bool result_only_materialization = false;
};

enum class InstantiationDemandKind : uint8_t {
    Identity,
    DeclarationSet,
    CompleteClass,
    MemberDefinition,
    ScopedEnumDefinition,
    ConstantEvaluation,
    ResultType,
    OdrUse,
    DeletionSemantics,
    BaseMemberList,
};

enum class InstantiationDemandStatus : uint8_t {
    Active,
    Satisfied,
    Unavailable,
    Failed,
};

struct InstantiationDemandFact {
    InstantiationDemandKind kind = InstantiationDemandKind::Identity;
    InstantiationDemandStatus status = InstantiationDemandStatus::Active;
    EntityId subject{};
    SrcLoc first_requirement{};
    uint64_t point_lookup_generation = 0;
    uint64_t request_id = 0;
};

struct TemplateSpecializationFact {
    EntityId template_entity{};
    EntityId selected_template_entity{};
    uint32_t template_param_index = ArrayTypePayload::no_extent_param;
    TemplateArgumentBindings argument_bindings;
    TemplateArgumentBindings selected_argument_bindings;
    std::vector<TemplateArgument> dependent_arguments;
    std::vector<TemplateArgument> selected_dependent_arguments;
    TypeId pattern_type{};
    SrcLoc point_of_instantiation{};
    uint64_t point_lookup_generation = 0;
    std::vector<InstantiationDemandFact> instantiation_demands;

    std::vector<TemplateArgument> template_arguments() const {
        return argument_bindings.empty()
            ? dependent_arguments
            : flatten_template_argument_bindings(argument_bindings);
    }

    std::vector<TemplateArgument> selected_template_arguments() const {
        return selected_argument_bindings.empty()
            ? selected_dependent_arguments
            : flatten_template_argument_bindings(
                  selected_argument_bindings);
    }
};

struct Generic {
    EntityId entity{};
    SrcLoc loc{};
    std::vector<EntityId> parameters;
    FunctionId pattern_function{};
};

struct Specific {
    GenericId generic{};
    FunctionId function{};
    EntityId entity{};
    SrcLoc loc{};
};

std::string_view entity_kind_name(EntityKind kind);
std::string_view storage_duration_name(StorageDuration duration);
std::string_view execution_space_name(ExecutionSpace space);
std::string_view record_kind_name(RecordKind kind);
std::string_view record_member_access_name(RecordMemberAccess access);
std::string_view decl_context_kind_name(DeclContextKind kind);
std::string_view lookup_namespace_name(LookupNamespace lookup_namespace);
std::string_view inst_kind_name(InstKind kind);
std::string_view terminator_kind_name(TerminatorKind kind);
std::string_view unary_op_kind_name(UnaryOpKind kind);
std::string_view unary_op_spelling(UnaryOpKind kind);
std::string_view binary_op_kind_name(BinaryOpKind kind);
std::string_view binary_op_spelling(BinaryOpKind kind);
std::string_view operator_value_domain_name(OperatorValueDomain domain);

class File {
public:
    using TransactionId = uint32_t;

    File();

    void set_target_info(std::shared_ptr<TargetInfo> target);
    const TargetInfo& target_info() const;
    std::shared_ptr<TargetInfo> target_info_ptr() const { return target_; }
    const AbiPolicy& abi_policy() const { return abi_policy_; }

    TransactionId begin_transaction();
    void commit_transaction(TransactionId id);
    void rollback_transaction(TransactionId id);
    bool in_transaction() const { return !transactions_.empty(); }
    void set_transaction_integrity_checks(bool enabled) {
        transaction_integrity_checks_ = enabled;
    }
    NameId intern_name(std::string_view name);
    const std::string& name(NameId id) const;

    TypeId builtin_type(BuiltinTypeKind kind);
    TypeId builtin_type(BuiltinTypeKind kind) const;
    TypeId builtin_type(std::string_view spelling);
    TypeId unknown_type();
    TypeId dependent_type(const std::string& name);
    TypeId dependent_name_type(TypeRef qualifier_type,
                               std::string_view member_name,
                               std::vector<TemplateArgument> template_arguments = {},
                               bool is_current_instantiation = false);
    TypeId template_specialization_type(
        NameId template_name,
        EntityId primary_template,
        std::vector<TemplateArgument> arguments,
        bool is_dependent = true,
        bool is_class_template_placeholder = false,
        TemplateValueExpression splice_operand = {});
    TypeId alias_specialization_type(
        NameId template_name,
        EntityId alias_template,
        std::vector<TemplateArgument> arguments,
        TypeRef associated_type);
    TypeRef type_ref(TypeId type,
                     uint8_t qualifiers = QualNone,
                     MemorySpace memory_space = MemorySpace::Default) const;
    TypeRef entity_type_ref(EntityId entity) const;
    TypeRef qualified_type(TypeId type, uint8_t qualifiers) const;
    TypeRef memory_type_ref(TypeId type, MemorySpace memory_space) const;
    TemplateValueExprNode template_integer_expression_node(
        IntegerValue value,
        TypeRef result_type) const;
    ValueExprId intern_template_value_expression(
        TemplateValueExpression expression);
    ValueExprId canonicalize_template_value_expression(
        TemplateValueExpression& expression);
    const TemplateValueExpression& template_value_expression(
        ValueExprId id) const;
    TypeId pointer_type(TypeId pointee);
    TypeId pointer_type(TypeRef pointee);
    TypeId block_pointer_type(TypeRef pointee);
    TypeId reference_type(TypeRef referred, ReferenceKind reference_kind);
    TypeId member_pointer_type(TypeRef class_type, TypeRef member_type);
    TypeId auto_type(AutoTypeFlavor flavor = AutoTypeFlavor::Gnu);
    TypeId typeof_expr_type(InstId expr);
    TypeId decltype_expr_type(
        InstId expr,
        bool use_declared_type_rule,
        DecltypeOperandCategory operand_category =
            DecltypeOperandCategory::Unknown,
        TypeRef operand_type = {},
        TypeRef dependent_value_qualifier = {},
        NameId dependent_value_name = {},
        TemplateValueExpression operand_expression = {});
    TypeId builtin_type_transform_type(BuiltinTypeTransformKind transform_kind,
                                       TypeRef operand_type);
    TypeId builtin_pack_element_type(
        std::vector<TemplateArgument> arguments);
    TypeId array_type(TypeId element, std::optional<size_t> size = std::nullopt);
    TypeId array_type(TypeRef element,
                      ArraySizeKind size_kind,
                      std::optional<size_t> size = std::nullopt,
                      InstId size_expr = {},
                      bool size_expr_is_dependent = false,
                      uint32_t extent_param = ArrayTypePayload::no_extent_param,
                      TemplateValueExpression dependent_size_expr = {});
    TypeId pack_index_type(TypeRef pack_type,
                           TemplateValueExpression index_expression,
                           std::vector<TypeRef> expansions = {},
                           bool fully_substituted = false);
    TypeId place_type(TypeId object_type);
    TypeId place_type(TypeRef object_type);
    TypeId record_type(EntityId entity, const std::string& name);
    TypeId enum_type(EntityId entity,
                     const std::string& name,
                     TypeRef underlying_type,
                     bool is_scoped = false,
                     bool is_incomplete = true,
                     bool has_fixed_underlying_type = false);
    TypeId vector_type(TypeRef element_type,
                       uint32_t element_count,
                       uint64_t size_bytes);
    TypeId complex_type(TypeRef element_type);
    TypeId bit_int_type(uint32_t bits, bool is_unsigned);
    TypeId type_param_type(EntityId entity,
                           const std::string& name,
                           uint32_t index = 0,
                           uint32_t depth = 0,
                           bool is_parameter_pack = false);
    TypeId function_type(TypeId result, const std::vector<TypeId>& parameters);
    TypeId function_type(TypeRef result,
                         const std::vector<TypeRef>& parameters,
                         bool is_variadic = false,
                         bool has_prototype = true,
                         bool member_is_const = false,
                         FunctionExceptionSpec exception_spec = {},
                         const std::vector<uint8_t>& parameter_pack_flags = {},
                         FunctionRefQualifierKind member_ref_qualifier =
                             FunctionRefQualifierKind::None,
                         bool member_is_volatile = false);
    const Type& type(TypeId id) const {
        static const Type invalid;
        if (!valid(id)) {
            return invalid;
        }
        return types_[id.index];
    }
    const TypePayload& type_payload(TypeId id) const;
    const TypePayload& type_payload(uint32_t index) const;
    TypeId canonical_type(TypeId id) const {
        if (!valid(id)) {
            return {};
        }
        TypeId canonical = types_[id.index].canonical;
        return canonical.valid() ? canonical : id;
    }
    TypeId desugared_type(TypeId id) const {
        if (!valid(id)) {
            return {};
        }
        TypeId desugared = types_[id.index].desugared;
        return desugared.valid() ? desugared : canonical_type(id);
    }
    TypeId resolved_type(TypeId id) const {
        if (!valid(id)) {
            return {};
        }
        TypeId resolved = types_[id.index].resolved;
        return resolved.valid() ? resolved : desugared_type(id);
    }
    OperatorValueDomain operator_value_domain(TypeRef ref) const;
    TypeRef array_element_ref(TypeId id) const;
    TypeId array_element_type(TypeId id) const;
    TypeRef vector_element_ref(TypeId id) const;
    TypeId vector_element_type(TypeId id) const;
    uint32_t vector_element_count(TypeId id) const;
    uint64_t vector_size_bytes(TypeId id) const;
    TypeRef place_object_ref(TypeId id) const;
    TypeId place_object_type(TypeId id) const;
    void retype_entity_places(EntityId entity);
    TypeRef pointer_pointee_ref(TypeId id) const;
    TypeRef reference_referred_ref(TypeId id) const;
    TypeId reference_referred_type(TypeId id) const;
    TypeId pointer_pointee_type(TypeId id) const;
    TypeRef member_pointer_class_ref(TypeId id) const;
    TypeRef member_pointer_member_ref(TypeId id) const;
    bool member_pointer_points_to_function(TypeId id) const;
    TemplateValueKind template_value_kind_for_type(TypeId id) const;
    TemplateNullKind template_null_kind_for_type(TypeId id) const;
    bool template_type_accepts_null_kind(TypeId id,
                                         TemplateNullKind kind) const;
    bool template_argument_references_internal_entity(
        const TemplateArgument& argument) const;
    bool template_context_references_internal_entity(EntityId entity) const;
    LinkageKind odr_linkage_for_entity(EntityId entity) const;
    EntityId record_entity(TypeId id) const;
    RecordFacts* record_facts(EntityId entity);
    const RecordFacts* record_facts(EntityId entity) const;
    const RecordFacts* record_facts_for_type(TypeId type) const;
    ClassPropertyState consteval_only_type_state(TypeId type) const;
    const RecordFieldFact* field_fact(EntityId field) const;
    const RecordMethodFact* method_fact(EntityId method) const;
    RecordMethodFact* method_fact_mut(EntityId method);
    const DefaultedComparisonFact* defaulted_comparison_fact(
        EntityId function) const;
    DefaultedComparisonFact* defaulted_comparison_fact_mut(
        EntityId function);
    void set_defaulted_comparison_fact(EntityId function,
                                       DefaultedComparisonFact fact);
    const StructuredBindingFact* structured_binding_fact(
        EntityId backing_or_binding) const;
    StructuredBindingFact* structured_binding_fact_mut(
        EntityId backing_or_binding);
    void set_structured_binding_fact(EntityId backing,
                                     StructuredBindingFact fact);
    void set_record_facts(EntityId entity, RecordFacts facts);
    ObjCInterfaceFacts* objc_interface_facts_mut(EntityId entity);
    const ObjCInterfaceFacts* objc_interface_facts(EntityId entity) const;
    void set_objc_interface_facts(EntityId entity, ObjCInterfaceFacts facts);
    const std::unordered_map<uint64_t, ObjCInterfaceFacts>&
    objc_interface_fact_table() const {
        return objc_interface_facts_;
    }
    SelectorId intern_selector(std::string_view spelling);
    NameId selector_name(SelectorId selector) const;
    std::string_view selector_spelling(SelectorId selector) const;
    void set_template_specialization(EntityId entity, TemplateSpecializationFact fact);
    const TemplateSpecializationFact* template_specialization(EntityId entity) const;
    const std::unordered_map<uint64_t, TemplateSpecializationFact>&
    template_specializations() const {
        return template_specializations_;
    }

    EntityId add_entity(Entity entity);
    const Entity& entity(EntityId id) const;
    Entity& entity_mut(EntityId id);
    std::vector<EntityId> entity_ids() const;
    uint32_t entity_table_size() const {
        return static_cast<uint32_t>(entities_.size());
    }

    DeclContextId add_decl_context(DeclContext context);
    DeclContextId create_decl_context(DeclContextKind kind,
                                      DeclContextId parent = {},
                                      EntityId owner = {},
                                      SrcLoc loc = SrcLoc());
    const DeclContext& decl_context(DeclContextId id) const;
    DeclContext& decl_context_mut(DeclContextId id);
    std::vector<DeclContextId> decl_context_ids() const;

    BindingId add_binding(Binding binding);
    BindingId bind_callable_overload(DeclContextId context,
                                     NameId name,
                                     EntityId entity,
                                     TypeRef type,
                                     bool is_definition,
                                     SrcLoc loc);
    BindingId bind_entity(DeclContextId context,
                          NameId name,
                          LookupNamespace lookup_namespace,
                          EntityId entity,
                          TypeRef type,
                          bool is_type_name = false,
                          bool is_template_name = false,
                          bool is_definition = false,
                          InstId place = {},
                          SrcLoc loc = SrcLoc());
    const Binding& binding(BindingId id) const;
    Binding* binding_mut(BindingId id);
    bool binding_is_callable(const Binding& binding) const;
    Binding* mutable_ordinary_binding(DeclContextId context, std::string_view spelling);
    BindingId add_alias_binding(DeclContextId context,
                                const Binding& source,
                                SrcLoc loc,
                                uint64_t introduction_generation);
    void add_using_directive(DeclContextId context, DeclContextId target);
    const Binding* lookup_ordinary_binding(DeclContextId start,
                                           NameId name,
                                           bool include_parents = true) const;
    const Binding* lookup_ordinary_binding(DeclContextId start,
                                           std::string_view name,
                                           bool include_parents = true) const;
    const Binding* lookup_direct_ordinary_binding(
        DeclContextId context,
        NameId name) const;
    const Binding* lookup_direct_ordinary_binding(
        DeclContextId context,
        std::string_view name) const;
    const Binding* lookup_value_binding(DeclContextId start,
                                        NameId name,
                                        bool include_parents = true) const;
    const Binding* lookup_value_binding(DeclContextId start,
                                        std::string_view name,
                                        bool include_parents = true) const;
    const Binding* lookup_callable_binding(DeclContextId start,
                                           NameId name,
                                           bool include_parents = true) const;
    const Binding* lookup_callable_binding(DeclContextId start,
                                           std::string_view name,
                                           bool include_parents = true) const;
    const Binding* lookup_type_name_binding(DeclContextId start,
                                            NameId name,
                                            bool include_parents = true) const;
    const Binding* lookup_type_name_binding(DeclContextId start,
                                            std::string_view name,
                                            bool include_parents = true) const;
    const Binding* lookup_template_name_binding(DeclContextId start,
                                                NameId name,
                                                bool include_parents = true) const;
    const Binding* lookup_template_name_binding(DeclContextId start,
                                                std::string_view name,
                                                bool include_parents = true) const;
    const Binding* lookup_namespace_name_binding(DeclContextId start,
                                                 NameId name,
                                                 bool include_parents = true) const;
    const Binding* lookup_namespace_name_binding(DeclContextId start,
                                                 std::string_view name,
                                                 bool include_parents = true) const;
    // Lookup for a name followed by `::` restricts declarations before
    // deciding whether an enclosing scope must be searched. Keep namespaces
    // and types in one search so neither category can bypass a nearer result
    // from the other category.
    const Binding* lookup_qualifier_binding(DeclContextId start,
                                            NameId name,
                                            bool include_parents = true) const;
    const Binding* lookup_qualifier_binding(DeclContextId start,
                                            std::string_view name,
                                            bool include_parents = true) const;
    const Binding* lookup_tag_binding(DeclContextId start,
                                      NameId name,
                                      bool include_parents = true) const;
    const Binding* lookup_tag_binding(DeclContextId start,
                                      std::string_view name,
                                      bool include_parents = true) const;
    const Binding* lookup_label_binding(DeclContextId start,
                                        NameId name,
                                        bool include_parents = true) const;
    const Binding* lookup_label_binding(DeclContextId start,
                                        std::string_view name,
                                        bool include_parents = true) const;
    std::vector<BindingId> binding_ids() const;

    PlaceFactId add_place_fact(PlaceFact fact);
    const PlaceFact& place_fact(PlaceFactId id) const;
    PlaceFact& place_fact_mut(PlaceFactId id);

    PlaceholderResultFactId add_placeholder_result_fact(
        PlaceholderResultFact fact);
    const PlaceholderResultFact& placeholder_result_fact(
        PlaceholderResultFactId id) const;
    PlaceholderResultFact& placeholder_result_fact_mut(
        PlaceholderResultFactId id);

    ConstantStateId add_constant_state(ConstantStateFact fact);
    const ConstantStateFact& constant_state(ConstantStateId id) const;

    ClosureIdentityId add_closure_identity(ClosureIdentityFact fact);
    const ClosureIdentityFact& closure_identity(ClosureIdentityId id) const;
    ClosureIdentityFact& closure_identity_mut(ClosureIdentityId id);
    std::vector<ClosureIdentityId> closure_identity_ids() const;

    SwitchId add_switch_fact(SwitchFact fact);
    const SwitchFact& switch_fact(SwitchId id) const;
    std::vector<SwitchId> switch_ids() const;

    void add_coroutine_fact(CoroutineFact fact);
    const CoroutineFact* coroutine_fact_for_function(EntityId function) const;
    CoroutineFact* coroutine_fact_for_function_mut(EntityId function);
    const std::vector<CoroutineFact>& coroutine_facts() const {
        return coroutine_facts_;
    }
    bool coroutines_lowered() const { return coroutines_lowered_; }
    void set_coroutines_lowered(bool lowered) {
        coroutines_lowered_ = lowered;
    }
    struct ModuleGraphRemap {
        uint32_t srcloc_delta = 0;
        ModuleAttachmentId unit{};
        std::vector<NameId> names;
        std::vector<TypeId> types;
        std::vector<EntityId> entities;
        std::vector<DeclContextId> contexts;
        std::vector<BindingId> bindings;
        std::vector<FunctionId> functions;
        std::vector<BlockId> blocks;
        std::vector<InstId> insts;
        std::vector<GenericId> generics;
        std::vector<SpecificId> specifics;
        std::vector<ConstantStateId> constant_states;
        std::vector<ClosureIdentityId> closure_identities;
        std::vector<PlaceFactId> place_facts;
        std::vector<InlineAsmPayloadId> inline_asm_payloads;
        std::vector<PlaceholderResultFactId> placeholder_facts;
        std::vector<ModuleAttachmentId> units;

        SrcLoc loc(SrcLoc value) const {
            return value.isInvalid() ? value
                                     : SrcLoc(value.offset + srcloc_delta);
        }
        template <typename IdT>
        static IdT lookup(const std::vector<IdT>& map, IdT id) {
            return id.valid() && id.index < map.size() ? map[id.index]
                                                       : IdT{};
        }
        NameId name(NameId id) const { return lookup(names, id); }
        TypeId type(TypeId id) const { return lookup(types, id); }
        TypeRef type_ref(TypeRef ref) const {
            ref.type = type(ref.type);
            return ref;
        }
        EntityId entity(EntityId id) const { return lookup(entities, id); }
        DeclContextId context(DeclContextId id) const {
            return lookup(contexts, id);
        }
        FunctionId function(FunctionId id) const {
            return lookup(functions, id);
        }
        BlockId block(BlockId id) const { return lookup(blocks, id); }
        InstId inst(InstId id) const { return lookup(insts, id); }
        GenericId generic(GenericId id) const {
            return lookup(generics, id);
        }
        SpecificId specific(SpecificId id) const {
            return lookup(specifics, id);
        }
        ConstantStateId constant_state(ConstantStateId id) const {
            return lookup(constant_states, id);
        }
        ClosureIdentityId closure(ClosureIdentityId id) const {
            return lookup(closure_identities, id);
        }
        BindingId binding(BindingId id) const {
            return lookup(bindings, id);
        }
        PlaceFactId place_fact(PlaceFactId id) const {
            return lookup(place_facts, id);
        }
        InlineAsmPayloadId inline_asm(InlineAsmPayloadId id) const {
            return lookup(inline_asm_payloads, id);
        }
        PlaceholderResultFactId placeholder(
            PlaceholderResultFactId id) const {
            return lookup(placeholder_facts, id);
        }
        ModuleAttachmentId attachment(ModuleAttachmentId id) const {
            if (!id.valid()) {
                return {};
            }
            if (id.index < units.size() && units[id.index].valid()) {
                return units[id.index];
            }
            return unit;
        }
        TemplateArgument argument(const TemplateArgument& value) const;
        TemplateValueExpression value_expression(
            const TemplateValueExpression& expression,
            uint64_t definition_lookup_generation) const;
    };
    struct ModuleGraphImportResult {
        ModuleAttachmentId unit{};
        std::string refusal;
        size_t first_imported_entity_index = 0;
        ModuleGraphRemap remap;
    };
    ModuleGraphImportResult import_module_graph(const File& source,
                                                std::string_view module_key,
                                                uint32_t srcloc_delta,
                                                uint64_t binding_generation,
                                                bool allow_templates);
    const std::unordered_map<std::string, ModuleGraphRemap>&
    module_import_provenance() const {
        return module_import_provenance_;
    }
    friend struct ModuleGraphImporter;
    friend struct ModuleGraphSerializer;
    struct PreludeMark {
        size_t entities = 0;
        size_t decl_contexts = 0;
        size_t bindings = 0;
    };
    void mark_prelude() {
        prelude_mark_.entities = entities_.size();
        prelude_mark_.decl_contexts = decl_contexts_.size();
        prelude_mark_.bindings = bindings_.size();
    }
    const PreludeMark& prelude_mark() const { return prelude_mark_; }

    // The C++20 module invariant requires ActiveModuleContext to stamp every
    // entity so attachment remains consistent across all declaration paths.
    struct ActiveModuleContext {
        ModuleAttachmentId unit{};
        ModuleFragment fragment = ModuleFragment::None;
        uint32_t export_depth = 0;
    };
    ModuleAttachmentId add_module_unit(ModuleUnitFact fact);
    const ModuleUnitFact& module_unit(ModuleAttachmentId id) const;
    ModuleUnitFact* module_unit_mut(ModuleAttachmentId id);
    bool valid(ModuleAttachmentId id) const;
    std::vector<ModuleAttachmentId> module_unit_ids() const;
    bool has_module_units() const { return module_units_.size() > 1; }
    void set_active_module_context(ActiveModuleContext context) {
        active_module_ = context;
    }
    const ActiveModuleContext& active_module_context() const {
        return active_module_;
    }
    ModuleAttachmentId effective_module_attachment(const Entity& entity) const {
        return entity.is_extern_c ? ModuleAttachmentId{}
                                  : entity.module_attachment;
    }
    void set_active_module_visibility(
        ModuleAttachmentId unit, const std::vector<uint32_t>& visible_units) {
        visibility_unit_ = unit;
        visible_units_.assign(module_units_.size(), 0);
        for (uint32_t index : visible_units) {
            if (index < visible_units_.size()) {
                visible_units_[index] = 1;
            }
        }
    }
    bool entity_lookup_visible(EntityId id) const;
    void note_imported_definitions_since(size_t first_entity_index) {
        if (imported_definition_entities_.size() < entities_.size()) {
            imported_definition_entities_.resize(entities_.size(), 0);
        }
        for (size_t index = first_entity_index; index < entities_.size();
             ++index) {
            if (entities_[index].is_definition) {
                imported_definition_entities_[index] = 1;
            }
        }
    }
    bool has_imported_definition(EntityId id) const {
        return id.valid() &&
               id.index < imported_definition_entities_.size() &&
               imported_definition_entities_[id.index] != 0;
    }
    void note_module_entity_redeclared(EntityId id) const {
        if (!id.valid()) {
            return;
        }
        if (module_redeclared_entities_.size() <= id.index) {
            module_redeclared_entities_.resize(id.index + 1, 0);
        }
        module_redeclared_entities_[id.index] = 1;
    }
    class ModuleVisibilityBypass {
    public:
        explicit ModuleVisibilityBypass(const File& file)
            : file_(file), previous_(file.module_visibility_bypass_) {
            file_.module_visibility_bypass_ = true;
        }
        ~ModuleVisibilityBypass() {
            file_.module_visibility_bypass_ = previous_;
        }
        ModuleVisibilityBypass(const ModuleVisibilityBypass&) = delete;
        ModuleVisibilityBypass& operator=(const ModuleVisibilityBypass&) =
            delete;

    private:
        const File& file_;
        bool previous_;
    };

    InstId add_inst(Inst inst);
    const Inst& inst(InstId id) const;
    Inst& inst_mut(InstId id);

    uint32_t add_payload(InstPayload payload);
    const InstPayload& payload(uint32_t index) const;
    InlineAsmPayloadId add_inline_asm_payload(InlineAsmPayload payload);
    const InlineAsmPayload& inline_asm_payload(InlineAsmPayloadId id) const;

    OperandRange add_operands(const std::vector<Operand>& operands);
    OperandRange add_value_operands(const std::vector<InstId>& operands);
    std::vector<Operand> operands(OperandRange range) const;
    std::vector<ValueRef> value_operands(OperandRange range) const;
    BlockId add_block(Block block = {});
    void append_to_block(BlockId block, InstId inst);
    void set_terminator(BlockId block, Terminator terminator);
    const Block& block(BlockId id) const;
    Block& block_mut(BlockId id);

    FunctionId add_function(Function function);
    const Function& function(FunctionId id) const;
    Function& function_mut(FunctionId id);
    std::vector<FunctionId> function_ids() const;

    GenericId add_generic(Generic generic);
    SpecificId add_specific(Specific specific);
    size_t generic_count() const;
    size_t specific_count() const;
    bool valid(NameId id) const;
    bool valid(TypeId id) const {
        return valid_id<Type, TypeId>(types_, type_generations_, id);
    }
    bool valid(EntityId id) const;
    bool valid(DeclContextId id) const;
    bool valid(BindingId id) const;
    bool valid(PlaceFactId id) const;
    bool valid(PlaceholderResultFactId id) const;
    bool valid(ConstantStateId id) const;
    bool valid(ClosureIdentityId id) const;
    bool valid(SwitchId id) const;
    bool valid(InstId id) const;
    bool valid(BlockId id) const;
    bool valid(FunctionId id) const;
    bool valid(InlineAsmPayloadId id) const;
    bool valid(ValueExprId id) const {
        return valid_id<TemplateValueExpression, ValueExprId>(
            value_expressions_, value_expression_generations_, id);
    }

    std::string format_type(TypeId id) const;
    std::string format_type(TypeRef ref) const;
    std::string format_entity(EntityId id) const;
    std::string format_inst(InstId id) const;
    std::string format_value(ValueRef ref) const;
    std::string format_operand(const Operand& operand) const;

    void add_module_asm(std::string asm_string) {
        module_asm_.push_back(std::move(asm_string));
    }
    const std::vector<std::string>& module_asm() const { return module_asm_; }
    void add_error(std::string message, SrcLoc loc = SrcLoc());
    bool has_errors() const { return !errors_.empty(); }
    void add_warning(std::string message, SrcLoc loc = SrcLoc());
    void add_note(std::string message, SrcLoc loc = SrcLoc());
    // Pin the diagnostics emitted so far so no rollback can discard them.
    void pin_diagnostics() {
        error_floor_ = errors_.size();
        note_floor_ = notes_.size();
    }
    const std::vector<std::pair<SrcLoc, std::string>>& warnings() const {
        return warnings_;
    }
    const std::vector<std::pair<SrcLoc, std::string>>& notes() const {
        return notes_;
    }
    const std::vector<std::pair<SrcLoc, std::string>>& errors() const {
        return errors_;
    }

    bool verify(std::ostream* err = nullptr) const;
    void dump(std::ostream& out) const;
    std::string debug_semantic_fingerprint() const;

private:
    void canonicalize_template_argument_value_expressions(
        TemplateArgument& argument);

    struct Transaction {
        TransactionId id = 0;
        size_t names_size = 0;
        size_t types_size = 0;
        size_t type_payloads_size = 0;
        size_t entities_size = 0;
        size_t decl_contexts_size = 0;
        size_t bindings_size = 0;
        size_t place_facts_size = 0;
        size_t placeholder_result_facts_size = 0;
        size_t constant_states_size = 0;
        size_t closure_identities_size = 0;
        size_t switch_facts_size = 0;
        size_t coroutine_facts_size = 0;
        size_t module_units_size = 0;
        size_t insts_size = 0;
        size_t payloads_size = 0;
        size_t inline_asm_payloads_size = 0;
        size_t operands_size = 0;
        size_t blocks_size = 0;
        size_t functions_size = 0;
        size_t generics_size = 0;
        size_t specifics_size = 0;
        size_t value_expressions_size = 0;
        size_t module_asm_size = 0;
        size_t errors_size = 0;
        size_t warnings_size = 0;
        size_t notes_size = 0;
        PreludeMark prelude_mark;
        ActiveModuleContext active_module;
        ModuleAttachmentId visibility_unit{};
        std::vector<char> visible_units;
        std::vector<char> module_redeclared_entities;
        std::vector<char> imported_definition_entities;
        bool coroutines_lowered = false;
        std::vector<std::string> inserted_name_keys;
        std::vector<std::pair<uint64_t, TypeId>> inserted_type_entries;
        std::vector<std::pair<uint64_t, ValueExprId>>
            inserted_value_expression_entries;
#ifdef ABURI_VERIFY_TYPE_INTERN
        std::vector<std::string> inserted_type_keys;
#endif
        std::vector<BuiltinTypeKind> inserted_builtin_type_keys;
        std::unordered_map<uint32_t, Entity> entity_mutations;
        std::unordered_map<uint32_t, DeclContext> decl_context_mutations;
        std::vector<DeclContextDelta> decl_context_deltas;
        std::unordered_map<uint32_t, Binding> binding_mutations;
        std::unordered_map<uint32_t, PlaceFact> place_fact_mutations;
        std::unordered_map<uint32_t, PlaceholderResultFact>
            placeholder_result_fact_mutations;
        std::unordered_map<uint32_t, ClosureIdentityFact>
            closure_identity_mutations;
        std::unordered_map<uint32_t, CoroutineFact> coroutine_fact_mutations;
        std::unordered_map<uint32_t, ModuleUnitFact> module_unit_mutations;
        std::unordered_map<uint32_t, Inst> inst_mutations;
        std::unordered_map<uint32_t, Block> block_mutations;
        std::unordered_map<uint32_t, Function> function_mutations;
        std::unordered_map<uint64_t, std::optional<RecordFacts>> record_fact_mutations;
        std::unordered_map<uint64_t, std::optional<ObjCInterfaceFacts>>
            objc_interface_fact_mutations;
        std::unordered_map<uint64_t,
                           std::optional<DefaultedComparisonFact>>
            defaulted_comparison_fact_mutations;
        std::unordered_map<uint64_t,
                           std::optional<StructuredBindingFact>>
            structured_binding_fact_mutations;
        std::unordered_map<uint64_t, std::optional<TemplateSpecializationFact>>
            template_specialization_mutations;
        std::unordered_map<std::string, std::optional<ModuleGraphRemap>>
            module_import_provenance_mutations;
#ifndef NDEBUG
        std::optional<std::string> rollback_fingerprint;
#endif
    };

    template <typename T, typename IdT>
    IdT add_record(std::vector<T>& table, std::vector<uint32_t>& generations,
                   T record) {
        uint32_t index = static_cast<uint32_t>(table.size());
        uint32_t generation = 1;
        if (index < generations.size()) {
            generation = generations[index] + 1;
            if (generation == 0) {
                generation = 1;
            }
            generations[index] = generation;
        } else {
            generations.push_back(generation);
        }
        table.push_back(std::move(record));
        return IdT{index, generation};
    }

    template <typename T, typename IdT>
    bool valid_id(const std::vector<T>& table,
                  const std::vector<uint32_t>& generations,
                  IdT id) const {
        return id.valid() &&
               id.index < table.size() &&
               id.index < generations.size() &&
               generations[id.index] == id.generation;
    }

    bool is_void_type(TypeId id) const;
    TypeId operand_result_type(InstId id) const;
    TypeId operand_result_type(ValueRef ref) const;
    TypeId intern_type(TypeSpec spec);
    uint32_t add_type_payload(TypePayload payload);
    bool ordinary_binding_matches_category(
        const Binding& binding,
        OrdinaryBindingCategory category) const;
    bool ordinary_binding_names_qualifier(const Binding& binding) const;
    NameId find_existing_name(std::string_view spelling) const;
    void index_binding_in_decl_context(DeclContextId context_id,
                                       BindingId binding_id);
    static std::unordered_map<uint64_t, BindingId>& decl_context_index(
        DeclContext& context,
        DeclContextIndexKind kind);
    Transaction* decl_context_delta_journal(DeclContextId id);
    void journal_decl_context_append(DeclContextId id,
                                     DeclContextDelta::Kind kind);
    void assign_decl_context_index(DeclContextId id,
                                   DeclContextIndexKind kind,
                                   uint64_t key,
                                   BindingId binding_id);
    void undo_decl_context_delta(const DeclContextDelta& delta);
    const Binding* lookup_ordinary_category_binding(
        DeclContextId start,
        NameId name,
        OrdinaryBindingCategory category,
        bool include_parents) const;
    const Binding* find_binding_via_directives(
        const DeclContext& context,
        uint64_t key,
        const OrdinaryBindingCategory* category,
        std::vector<uint32_t>& visited) const;
    const Binding* find_qualifier_binding_via_directives(
        const DeclContext& context,
        uint64_t key,
        std::vector<uint32_t>& visited) const;
    const Binding* lookup_indexed_namespace_binding(
        DeclContextId start,
        NameId name,
        LookupNamespace lookup_namespace,
        bool include_parents) const;
    void stamp_module_export(DeclContextId context, EntityId entity_id);
    void record_entity_mutation(EntityId id);
    void record_decl_context_mutation(DeclContextId id);
    void record_binding_mutation(BindingId id);
    void record_place_fact_mutation(PlaceFactId id);
    void record_placeholder_result_fact_mutation(PlaceholderResultFactId id);
    void record_closure_identity_mutation(ClosureIdentityId id);
    void record_coroutine_fact_mutation(size_t index);
    void record_module_unit_mutation(ModuleAttachmentId id);
    void record_inst_mutation(InstId id);
    void record_block_mutation(BlockId id);
    void record_function_mutation(FunctionId id);
    void record_record_facts_mutation(uint64_t key);
    void record_objc_interface_facts_mutation(uint64_t key);
    void record_defaulted_comparison_fact_mutation(uint64_t key);
    void record_structured_binding_fact_mutation(uint64_t key);
    void record_template_specialization_mutation(uint64_t key);
    void record_module_import_provenance_mutation(std::string_view key);
    void merge_committed_transaction(Transaction transaction);
    void rollback_table_sizes(const Transaction& transaction);
    bool verify_function(const Function& function,
                         FunctionId function_id,
                         std::ostream* err) const;
    bool verify_inst(InstId id, std::ostream* err) const;

    struct NameIndexHash {
        using is_transparent = void;
        size_t operator()(std::string_view value) const {
            return std::hash<std::string_view>{}(value);
        }
    };
    std::vector<std::string> names_;
    std::vector<uint32_t> name_generations_;
    std::unordered_map<std::string, NameId, NameIndexHash, std::equal_to<>>
        name_index_;

    std::shared_ptr<TargetInfo> target_;
    AbiPolicy abi_policy_;

    std::vector<Type> types_;
    std::vector<uint32_t> type_generations_;
    std::vector<TypePayload> type_payloads_;
    std::unordered_multimap<uint64_t, TypeId> type_index_;
#ifdef ABURI_VERIFY_TYPE_INTERN
    std::unordered_map<std::string, TypeId> verify_type_index_;
#endif
    std::unordered_map<BuiltinTypeKind, TypeId> builtin_types_;

    std::vector<Entity> entities_;
    std::vector<uint32_t> entity_generations_;
    std::unordered_map<uint64_t, RecordFacts> record_facts_;
    std::unordered_map<uint64_t, ObjCInterfaceFacts> objc_interface_facts_;
    std::unordered_map<uint64_t, DefaultedComparisonFact>
        defaulted_comparison_facts_;
    std::unordered_map<uint64_t, StructuredBindingFact>
        structured_binding_facts_;
    std::unordered_map<uint64_t, TemplateSpecializationFact> template_specializations_;

    std::vector<DeclContext> decl_contexts_;
    std::vector<uint32_t> decl_context_generations_;

    std::vector<Binding> bindings_;
    std::vector<uint32_t> binding_generations_;

    std::vector<PlaceFact> place_facts_;
    std::vector<uint32_t> place_fact_generations_;

    std::vector<PlaceholderResultFact> placeholder_result_facts_;
    std::vector<uint32_t> placeholder_result_fact_generations_;

    std::vector<ConstantStateFact> constant_states_;
    std::vector<uint32_t> constant_state_generations_;

    std::vector<ClosureIdentityFact> closure_identities_;
    std::vector<uint32_t> closure_identity_generations_;

    std::vector<SwitchFact> switch_facts_;
    std::vector<uint32_t> switch_fact_generations_;
    std::vector<CoroutineFact> coroutine_facts_;
    std::vector<ModuleUnitFact> module_units_;
    PreludeMark prelude_mark_;
    std::unordered_map<std::string, ModuleGraphRemap>
        module_import_provenance_;
    std::vector<uint32_t> module_unit_generations_;
    ActiveModuleContext active_module_;
    ModuleAttachmentId visibility_unit_{};
    std::vector<char> visible_units_;
    mutable bool module_visibility_bypass_ = false;
    mutable std::vector<char> module_redeclared_entities_;
    std::vector<char> imported_definition_entities_;
    bool binding_hidden_by_modules(const DeclContext& context,
                                   const Binding& binding) const;
    bool coroutines_lowered_ = false;

    std::vector<Inst> insts_;
    std::vector<uint32_t> inst_generations_;

    std::vector<InstPayload> payloads_;
    std::vector<InlineAsmPayload> inline_asm_payloads_;
    std::vector<uint32_t> inline_asm_payload_generations_;
    std::vector<Operand> operands_;

    std::vector<Block> blocks_;
    std::vector<uint32_t> block_generations_;

    std::vector<Function> functions_;
    std::vector<uint32_t> function_generations_;

    std::vector<Generic> generics_;
    std::vector<uint32_t> generic_generations_;

    std::vector<Specific> specifics_;
    std::vector<uint32_t> specific_generations_;

    std::vector<TemplateValueExpression> value_expressions_;
    std::vector<uint32_t> value_expression_generations_;
    std::unordered_multimap<uint64_t, ValueExprId> value_expression_index_;

    std::vector<std::pair<SrcLoc, std::string>> errors_;
    std::vector<std::pair<SrcLoc, std::string>> warnings_;
    std::vector<std::pair<SrcLoc, std::string>> notes_;
    size_t error_floor_ = 0;
    size_t note_floor_ = 0;
    std::vector<std::string> module_asm_;
    std::vector<Transaction> transactions_;
    TransactionId next_transaction_id_ = 1;
    bool transaction_integrity_checks_ = false;
};

} // namespace aburi::cir

#endif // ABURI_CIR_FILE_H
