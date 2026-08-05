#ifndef ABURI_CIR_TYPE_H
#define ABURI_CIR_TYPE_H

#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <variant>
#include <vector>

#include "../numeric/floating_point.h"
#include "../numeric/integer_value.h"

#include "ids.h"
#include "../source_mgnt.h"

namespace aburi::cir {

enum TypeQualifiers : uint8_t {
    QualNone = 0x00,
    QualConst = 0x01,
    QualVolatile = 0x02,
    QualRestrict = 0x04,
    QualAtomic = 0x08,
    QualOwnershipShift = 4,
    QualOwnershipMask = 0x70,
};

enum class ObjCOwnership : uint8_t {
    Unspecified = 0,
    Strong = 1,
    Weak = 2,
    UnsafeUnretained = 3,
    Autoreleasing = 4,
};

inline ObjCOwnership ownership_of(uint8_t qualifiers) {
    return static_cast<ObjCOwnership>(
        (qualifiers & QualOwnershipMask) >> QualOwnershipShift);
}

inline uint8_t with_ownership(uint8_t qualifiers, ObjCOwnership ownership) {
    return static_cast<uint8_t>(
        (qualifiers & ~QualOwnershipMask) |
        (static_cast<uint8_t>(ownership) << QualOwnershipShift));
}

enum class MemorySpace : uint8_t {
    Default,
    Generic,
    Global,
    Constant,
    Workgroup,
    Private,
    Function,
};

struct TypeRef {
    TypeId type{};
    uint8_t qualifiers = QualNone;
    MemorySpace memory_space = MemorySpace::Default;

    bool valid() const { return type.valid(); }
    explicit operator bool() const { return valid(); }

    friend bool operator==(TypeRef lhs, TypeRef rhs) {
        return lhs.type == rhs.type &&
               lhs.qualifiers == rhs.qualifiers &&
               lhs.memory_space == rhs.memory_space;
    }

    friend bool operator!=(TypeRef lhs, TypeRef rhs) {
        return !(lhs == rhs);
    }
};

enum class TypeKind : uint16_t {
    Invalid,
    Error,
    Unknown,
    Builtin,
    Pointer,
    BlockPointer,
    MemberPointer,
    LValueReference,
    RValueReference,
    Array,
    Function,
    Record,
    Enum,
    Vector,
    Complex,
    BitInt,
    Typedef,
    TypeParam,
    TemplateSpecialization,
    AliasSpecialization,
    DependentName,
    Dependent,
    Placeholder,
    Auto,
    TypeofExpr,
    DecltypeExpr,
    BuiltinTransform,
    BuiltinPackElement,
    PackIndex,
    Place
};

enum class BuiltinTypeKind : uint16_t {
    Void,
    NullPtr,
    Bool,
    Char,
    SChar,
    UChar,
    WChar,
    Char8,
    Char16,
    Char32,
    Short,
    UShort,
    Int,
    UInt,
    Long,
    ULong,
    LongLong,
    ULongLong,
    Int128,
    UInt128,
    USize,
    Float16,
    Float,
    Double,
    LongDouble,
    MetaInfo,
    Other,
};

enum class MetaInfoKind : uint8_t {
    Null,
    Type,
    Entity,
    Namespace,
    Template,
    Value,
};

enum class ReferenceKind : uint8_t {
    LValue,
    RValue,
};

enum class ArraySizeKind : uint8_t {
    Incomplete,
    Constant,
    Variable,
};

enum class FunctionExceptionSpecKind : uint8_t {
    PotentiallyThrowing,
    NonThrowing,
    Dependent,
};

enum class FunctionRefQualifierKind : uint8_t {
    None,
    LValue,
    RValue,
};

enum class CallingConventionKind : uint8_t {
    Default,
};

enum class AutoTypeFlavor : uint8_t {
    Gnu,
    Cxx,
    TemplateNonType,
    DecltypeAuto,
    DecltypeAutoTemplateNonType,
};

enum class BuiltinTypeTransformKind : uint8_t {
    RemoveConst,
    RemoveVolatile,
    RemoveCV,
    RemoveCVRef,
    RemoveReference,
    UnderlyingType,
    RemoveExtent,
    RemoveAllExtents,
    Decay,
    AddPointer,
    AddLValueReference,
    AddRValueReference,
};

enum class DecltypeOperandCategory : uint8_t {
    Unknown,
    PrValue,
    LValue,
    XValue,
    FunctionDesignator,
    MemberPointerDesignator,
};

enum class TemplateArgumentKind : uint8_t {
    Type,
    Value,
    Template,
};

enum class TemplateGeneratedPackKind : uint8_t {
    None,
    IntegerSequence,
};

enum class TemplateValueKind : uint8_t {
    None,
    Integer,
    Boolean,
    Floating,
    Null,
    Address,
    MemberPointer,
    Closure,
    StructuralObject,
    MetaInfo,
};

using FloatingSemantics = numeric::FloatFormat;
using FloatingValue = numeric::FloatValue;
using IntegerValue = numeric::IntegerValue;

enum class TemplateNullKind : uint8_t {
    None,
    Nullptr,
    Pointer,
    MemberPointer,
};

enum class TemplateValueExprKind : uint8_t {
    None,
    Integer,
    Parameter,
    PackSize,
    Entity,
    Unary,
    Binary,
    Conditional,
    Cast,
    SizeofType,
    AlignofType,
    TypeTrait,
    TypeOperand,
    Callee,
    Call,
    Noexcept,
    ConceptId,
    PackIndex,
    Fold,
};

enum class TemplateValueFoldKind : uint8_t {
    None,
    UnaryLeft,
    UnaryRight,
    BinaryLeft,
    BinaryRight,
};

enum class TemplateValueExprOp : uint8_t {
    None,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Shl,
    Shr,
    BitAnd,
    BitOr,
    BitXor,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Equal,
    NotEqual,
    ThreeWay,
    LogicalAnd,
    LogicalOr,
    Comma,
    UnaryPlus,
    UnaryMinus,
    LogicalNot,
    BitwiseNot,
    Dereference,
    MemberPointerDot,
    MemberPointerArrow,
    Delete,
    DeleteArray,
    AddressOf,
};

enum class TemplateCalleeFlag : uint32_t {
    None = 0,
    QualifiedName = 1u << 0,
    SuppressArgumentDependentLookup = 1u << 1,
    UnresolvedUnqualifiedName = 1u << 2,
    HasExplicitTemplateArguments = 1u << 3,
    MemberArrow = 1u << 4,
    BuiltinCallDesignator = 1u << 5,
    MemberAccess = 1u << 6,
};

inline constexpr TemplateCalleeFlag operator|(TemplateCalleeFlag lhs,
                                               TemplateCalleeFlag rhs) {
    return static_cast<TemplateCalleeFlag>(
        static_cast<uint32_t>(lhs) | static_cast<uint32_t>(rhs));
}

inline constexpr TemplateCalleeFlag& operator|=(TemplateCalleeFlag& lhs,
                                                TemplateCalleeFlag rhs) {
    lhs = lhs | rhs;
    return lhs;
}

enum class BuiltinTypeTraitKind : uint8_t {
    None,
    IsSame,
    IsFunction,
    IsReference,
    IsLValueReference,
    IsRValueReference,
    HasVirtualDestructor,
    IsAbstract,
    IsArray,
    IsBoundedArray,
    IsUnion,
    IsVolatile,
    IsConst,
    IsEmpty,
    IsEnum,
    IsScopedEnum,
    IsFundamental,
    IsIntegral,
    IsUnsigned,
    IsAssignable,
    IsTriviallyAssignable,
    IsNothrowAssignable,
    IsBaseOf,
    IsClass,
    IsFinal,
    IsAggregate,
    IsMemberPointer,
    IsMemberObjectPointer,
    IsMemberFunctionPointer,
    IsNullPointer,
    IsObject,
    IsPointer,
    IsPolymorphic,
    IsStandardLayout,
    IsTrivial,
    IsTriviallyCopyable,
    HasUniqueObjectRepresentations,
    IsPod,
    IsSigned,
    IsConstructible,
    IsTriviallyConstructible,
    IsNothrowConstructible,
    IsConvertible,
    IsCoreConvertible,
    IsNothrowConvertible,
    IsDestructible,
    IsTriviallyDestructible,
    HasTrivialDestructor,
    ReferenceBindsToTemporary,
    IsVoid,
    IsNothrowDestructible,
    IsFloatingPoint,
    IsArithmetic,
    IsScalar,
    IsCompound,
    IsLiteralType,
};

inline constexpr uint32_t TemplateValueExprNoNode = 0xFFFFFFFFu;
inline constexpr uint32_t TemplateValueExprNoParameter = 0xFFFFFFFFu;

enum class TemplateValuePackKind : uint8_t {
    Function,
    Type,
    Value,
    Template,
};

struct TemplateValuePackReference {
    TemplateValuePackKind kind = TemplateValuePackKind::Type;
    EntityId declaration{};
    EntityId owner{};
    uint32_t depth = 0;
    uint32_t index = TemplateValueExprNoParameter;
    TypeId parameter_type{};
    NameId name{};

    bool operator==(const TemplateValuePackReference&) const = default;
};

struct TemplateArgument;

class TemplateArgumentList {
public:
    TemplateArgumentList();
    explicit TemplateArgumentList(std::vector<TemplateArgument> arguments);
    TemplateArgumentList(const TemplateArgumentList& other);
    TemplateArgumentList(TemplateArgumentList&& other) noexcept;
    TemplateArgumentList& operator=(const TemplateArgumentList& other);
    TemplateArgumentList& operator=(TemplateArgumentList&& other) noexcept;
    ~TemplateArgumentList();

    bool empty() const;
    size_t size() const;
    const std::vector<TemplateArgument>& values() const;
    std::vector<TemplateArgument>& values();

private:
    std::shared_ptr<std::vector<TemplateArgument>> arguments_;
};

struct TemplateValueExprNode {
    TemplateValueExprKind kind = TemplateValueExprKind::None;
    TemplateValueExprOp op = TemplateValueExprOp::None;
    BuiltinTypeTraitKind trait_kind = BuiltinTypeTraitKind::None;
    TemplateValueFoldKind fold_kind = TemplateValueFoldKind::None;
    int64_t value = 0;
    IntegerValue integer_value;
    uint32_t parameter_index = TemplateValueExprNoParameter;
    uint32_t lhs = TemplateValueExprNoNode;
    uint32_t rhs = TemplateValueExprNoNode;
    uint32_t third = TemplateValueExprNoNode;
    std::vector<uint32_t> operands;
    bool expands_parameter_pack = false;
    std::vector<TemplateValuePackReference> pack_references;
    TemplateArgumentList template_arguments;
    TypeId type{};
    TypeRef result_type;
    EntityId entity{};
    NameId name{};
    TypeRef qualifier_type;
    std::string semantic_key;
};

struct TemplateValueExpression {
    std::vector<TemplateValueExprNode> nodes;
    uint32_t root = TemplateValueExprNoNode;
    ValueExprId canonical_id{};
    SrcLoc loc{};
    DeclContextId definition_context{};
    uint64_t definition_lookup_generation = 0;

    bool valid() const {
        return root != TemplateValueExprNoNode && root < nodes.size();
    }
};

struct FunctionExceptionSpec {
    FunctionExceptionSpecKind kind =
        FunctionExceptionSpecKind::PotentiallyThrowing;
    TemplateValueExpression predicate;

    FunctionExceptionSpec() = default;
    FunctionExceptionSpec(FunctionExceptionSpecKind kind) : kind(kind) {}
    FunctionExceptionSpec(FunctionExceptionSpecKind kind,
                          TemplateValueExpression predicate)
        : kind(kind), predicate(std::move(predicate)) {}

    bool valid() const {
        return kind != FunctionExceptionSpecKind::Dependent ||
               predicate.valid();
    }
};

uint64_t template_value_expression_structural_hash(
    const TemplateValueExpression& expression);
bool template_value_expressions_structurally_equal(
    const TemplateValueExpression& lhs,
    const TemplateValueExpression& rhs);

enum class DependencyFlag : uint32_t {
    TypeDependent = 1u << 0,
    ValueDependent = 1u << 1,
    InstantiationDependent = 1u << 2,
    ContainsUnexpandedPack = 1u << 3,
    HasDependentLookup = 1u << 4,
    HasDeferredResolution = 1u << 5,
    LayoutDependent = 1u << 6,
    RequiresInstantiation = 1u << 7,
};

enum class TypeUseKind : uint8_t {
    TypeIdentity,
    MemberLookup,
    Layout,
    Conversion,
    ConstantEvaluation,
    Codegen,
};

struct DependencyFacts {
    uint32_t flags = 0;

    bool empty() const { return flags == 0; }
    bool has(DependencyFlag flag) const {
        return (flags & static_cast<uint32_t>(flag)) != 0;
    }
    void add(DependencyFlag flag) {
        flags |= static_cast<uint32_t>(flag);
    }
    void merge(DependencyFacts other) {
        flags |= other.flags;
    }
    bool is_dependent() const {
        return has(DependencyFlag::TypeDependent) ||
               has(DependencyFlag::ValueDependent) ||
               has(DependencyFlag::InstantiationDependent) ||
               has(DependencyFlag::ContainsUnexpandedPack) ||
               has(DependencyFlag::HasDependentLookup);
    }
};

struct TypeReadiness {
    TypeUseKind use_kind = TypeUseKind::TypeIdentity;
    DependencyFacts facts;
    bool ready = true;

    bool is_ready() const { return ready; }
};

struct InvalidTypePayload {};
struct ErrorTypePayload {};

struct UnknownTypePayload {
    std::string debug_name;
};

struct BuiltinTypePayload {
    BuiltinTypeKind kind = BuiltinTypeKind::Int;
    std::string spelling;
    int64_t width_override = -1;
    int rank_override = -1;
    int8_t unsigned_override = -1;
};

struct PointerTypePayload {
    TypeRef pointee;
};

struct BlockPointerTypePayload {
    TypeRef pointee;
};

struct MemberPointerTypePayload {
    TypeRef class_type;
    TypeRef member_type;
};

struct ReferenceTypePayload {
    TypeRef referred_type;
    ReferenceKind reference_kind = ReferenceKind::LValue;
};

struct ArrayTypePayload {
    TypeRef element_type;
    ArraySizeKind size_kind = ArraySizeKind::Incomplete;
    std::optional<size_t> size;
    InstId size_expr{};
    bool size_expr_is_dependent = false;
    static constexpr uint32_t no_extent_param = 0xFFFFFFFFu;
    uint32_t extent_param = no_extent_param;
    TemplateValueExpression dependent_size_expr;
};

struct FunctionTypePayload {
    TypeRef return_type;
    std::vector<TypeRef> parameters;
    std::vector<uint8_t> parameter_pack_flags;
    bool is_variadic = false;
    bool has_prototype = true;
    FunctionRefQualifierKind member_ref_qualifier =
        FunctionRefQualifierKind::None;
    bool member_is_const = false;
    bool member_is_volatile = false;
    FunctionExceptionSpec exception_spec;
    CallingConventionKind calling_convention = CallingConventionKind::Default;
};

struct RecordTypePayload {
    EntityId entity{};
    NameId name{};
    bool is_union = false;
    bool is_incomplete = false;
};

struct EnumTypePayload {
    EntityId entity{};
    NameId name{};
    bool is_scoped = false;
    bool is_incomplete = false;
    bool has_fixed_underlying_type = false;
    TypeRef underlying_type;
};

struct VectorTypePayload {
    TypeRef element_type;
    uint32_t element_count = 0;
    uint64_t size_bytes = 0;
};

struct ComplexTypePayload {
    TypeRef element_type;
};

struct BitIntTypePayload {
    uint32_t bits = 0;
    bool is_unsigned = false;
};

struct TypedefTypePayload {
    EntityId entity{};
    NameId name{};
    TypeRef underlying_type;
};

struct TypeParamTypePayload {
    EntityId entity{};
    NameId name{};
    uint32_t depth = 0;
    uint32_t index = 0;
    bool is_parameter_pack = false;
};

enum class ConstantStateKind : uint8_t {
    Invalid,
    Integer,
    Boolean,
    Floating,
    Complex,
    Null,
    Address,
    MemberPointer,
    Record,
    Array,
    MetaInfo,
};

enum class ConstantLifetimeState : uint8_t {
    NotStarted,
    Constructing,
    Alive,
    Destroying,
    Ended,
};

struct ConstantStateSubobject {
    EntityId entity{};
    uint64_t array_index = 0;
    bool is_array_element = false;
};

struct ConstantStateFact {
    ConstantStateKind kind = ConstantStateKind::Invalid;
    ConstantLifetimeState lifetime = ConstantLifetimeState::Alive;
    TypeRef type;
    bool initialized = false;

    IntegerValue integer_value;
    bool boolean_value = false;
    FloatingValue floating_value;
    FloatingValue floating_real;
    FloatingValue floating_imag;
    IntegerValue complex_integer_real;
    IntegerValue complex_integer_imag;
    bool complex_is_integer = false;
    TemplateNullKind null_kind = TemplateNullKind::None;

    EntityId address_entity{};
    InstId address_string_literal{};
    int64_t address_byte_offset = 0;
    std::vector<ConstantStateSubobject> address_subobjects;

    EntityId member_entity{};
    int64_t member_byte_offset = 0;
    int32_t member_virtual_slot = -1;
    bool member_is_function = false;
    EntityId subobject_entity{};
    uint64_t subobject_index = 0;
    EntityId active_union_member{};
    ClosureIdentityId closure_identity{};
    std::vector<ConstantStateFact> elements;
};

struct TemplateArgument {
    TemplateArgumentKind kind = TemplateArgumentKind::Type;
    TypeRef type;
    TypeRef value_type;
    TemplateValueKind value_kind = TemplateValueKind::None;
    TemplateNullKind null_kind = TemplateNullKind::None;
    IntegerValue integer_value;
    FloatingValue floating_value;
    std::string value_spelling;
    EntityId value_entity{};
    ClosureIdentityId closure_identity{};
    int64_t value_byte_offset = 0;
    MetaInfoKind meta_kind = MetaInfoKind::Null;
    std::vector<TemplateArgument> value_elements;
    uint32_t value_param_index = ArrayTypePayload::no_extent_param;
    TemplateValueExpression dependent_value_expr;
    TemplateGeneratedPackKind generated_pack_kind =
        TemplateGeneratedPackKind::None;
    TypeRef generated_pack_count_type;
    TemplateValueExpression generated_pack_count_expr;
    TypeRef dependent_value_qualifier;
    NameId dependent_value_name{};
    EntityId template_entity{};
    uint32_t template_param_index = ArrayTypePayload::no_extent_param;
    TypeRef dependent_template_qualifier;
    bool is_dependent = false;
    bool is_defaulted = false;
    bool expands_parameter_pack = false;
    bool expands_pack_pattern = false;
    NameId template_name{};
    std::shared_ptr<TemplateArgument> unconverted_value_alternative;
    ConstantStateId constant_state{};
};

inline TemplateArgumentList::TemplateArgumentList()
    : arguments_(std::make_shared<std::vector<TemplateArgument>>()) {}

inline TemplateArgumentList::TemplateArgumentList(
    std::vector<TemplateArgument> arguments)
    : arguments_(std::make_shared<std::vector<TemplateArgument>>(
          std::move(arguments))) {}

inline TemplateArgumentList::TemplateArgumentList(
    const TemplateArgumentList& other)
    : arguments_(std::make_shared<std::vector<TemplateArgument>>(
          other.values())) {}

inline TemplateArgumentList::TemplateArgumentList(
    TemplateArgumentList&& other) noexcept = default;

inline TemplateArgumentList& TemplateArgumentList::operator=(
    const TemplateArgumentList& other) {
    if (this != &other) {
        arguments_ = std::make_shared<std::vector<TemplateArgument>>(
            other.values());
    }
    return *this;
}

inline TemplateArgumentList& TemplateArgumentList::operator=(
    TemplateArgumentList&& other) noexcept = default;

inline TemplateArgumentList::~TemplateArgumentList() = default;

inline bool TemplateArgumentList::empty() const {
    return !arguments_ || arguments_->empty();
}

inline size_t TemplateArgumentList::size() const {
    return arguments_ ? arguments_->size() : 0;
}

inline const std::vector<TemplateArgument>&
TemplateArgumentList::values() const {
    static const std::vector<TemplateArgument> empty;
    return arguments_ ? *arguments_ : empty;
}

inline std::vector<TemplateArgument>& TemplateArgumentList::values() {
    if (!arguments_) {
        arguments_ =
            std::make_shared<std::vector<TemplateArgument>>();
    }
    return *arguments_;
}

enum class TemplateArgumentBindingKind : uint8_t {
    Unbound,
    Single,
    Pack,
};

struct TemplateArgumentBinding {
    TemplateArgumentBindingKind kind = TemplateArgumentBindingKind::Unbound;
    std::vector<TemplateArgument> arguments;

    bool is_unbound() const {
        return kind == TemplateArgumentBindingKind::Unbound;
    }
    bool is_single() const {
        return kind == TemplateArgumentBindingKind::Single;
    }
    bool is_pack() const {
        return kind == TemplateArgumentBindingKind::Pack;
    }
};

using TemplateArgumentBindings = std::vector<TemplateArgumentBinding>;

inline std::vector<TemplateArgument> flatten_template_argument_bindings(
    const TemplateArgumentBindings& bindings) {
    std::vector<TemplateArgument> flattened;
    size_t total = 0;
    for (const TemplateArgumentBinding& binding : bindings) {
        if (!binding.is_unbound()) {
            total += binding.arguments.size();
        }
    }
    flattened.reserve(total);
    for (const TemplateArgumentBinding& binding : bindings) {
        if (!binding.is_unbound()) {
            flattened.insert(flattened.end(),
                             binding.arguments.begin(),
                             binding.arguments.end());
        }
    }
    return flattened;
}

struct TemplateSpecializationTypePayload {
    NameId template_name{};
    EntityId primary_template{};
    std::vector<TemplateArgument> arguments;
    TemplateValueExpression splice_operand;
    bool is_dependent = false;
    bool is_class_template_placeholder = false;
};

struct AliasSpecializationTypePayload {
    NameId template_name{};
    EntityId alias_template{};
    std::vector<TemplateArgument> arguments;
    TypeRef associated_type;
};

struct DependentNameTypePayload {
    TypeRef qualifier_type;
    NameId member_name{};
    std::vector<TemplateArgument> template_arguments;
    bool is_current_instantiation = false;
};

struct DependentTypePayload {
    NameId debug_name{};
};

struct PlaceholderTypePayload {};

struct AutoTypePayload {
    AutoTypeFlavor flavor = AutoTypeFlavor::Gnu;
};

struct TypeofExprTypePayload {
    InstId expr{};
};

struct DecltypeExprTypePayload {
    InstId expr{};
    bool use_declared_type_rule = false;
    DecltypeOperandCategory operand_category =
        DecltypeOperandCategory::Unknown;
    TypeRef operand_type;
    TypeRef dependent_value_qualifier;
    NameId dependent_value_name{};
    TemplateValueExpression operand_expression;
};

struct BuiltinTypeTransformTypePayload {
    BuiltinTypeTransformKind transform_kind =
        BuiltinTypeTransformKind::RemoveCV;
    TypeRef operand_type;
};

struct BuiltinPackElementTypePayload {
    std::vector<TemplateArgument> arguments;
};

struct PackIndexTypePayload {
    TypeRef pack_type;
    TemplateValueExpression index_expression;
    std::vector<TypeRef> expansions;
    bool fully_substituted = false;
};

struct PlaceTypePayload {
    TypeRef object_type;
};

using TypePayload = std::variant<InvalidTypePayload,
                                 ErrorTypePayload,
                                 UnknownTypePayload,
                                 BuiltinTypePayload,
                                 PointerTypePayload,
                                 BlockPointerTypePayload,
                                 MemberPointerTypePayload,
                                 ReferenceTypePayload,
                                 ArrayTypePayload,
                                 FunctionTypePayload,
                                 RecordTypePayload,
                                 EnumTypePayload,
                                 VectorTypePayload,
                                 ComplexTypePayload,
                                 BitIntTypePayload,
                                 TypedefTypePayload,
                                 TypeParamTypePayload,
                                 TemplateSpecializationTypePayload,
                                 AliasSpecializationTypePayload,
                                 DependentNameTypePayload,
                                 DependentTypePayload,
                                 PlaceholderTypePayload,
                                 AutoTypePayload,
                                 TypeofExprTypePayload,
                                 DecltypeExprTypePayload,
                                 BuiltinTypeTransformTypePayload,
                                 BuiltinPackElementTypePayload,
                                 PackIndexTypePayload,
                                 PlaceTypePayload>;

struct Type {
    TypeKind kind = TypeKind::Invalid;
    uint32_t payload_index = 0;
    TypeId canonical{};
    TypeId desugared{};
    TypeId resolved{};
    DependencyFacts dependency;
    NameId debug_name{};
    SrcLoc loc{};
};

struct TypeSpec {
    TypeKind kind = TypeKind::Invalid;
    TypePayload payload = InvalidTypePayload{};
    NameId debug_name{};
    TypeId canonical{};
    TypeId desugared{};
    TypeId resolved{};
    DependencyFacts dependency;
    SrcLoc loc{};
};

std::string_view type_kind_name(TypeKind kind);
std::string_view memory_space_name(MemorySpace space);
std::string_view builtin_type_kind_name(BuiltinTypeKind kind);
TypeKind type_payload_kind(const TypePayload& payload);
bool type_spec_matches_payload(const TypeSpec& spec);
std::string type_structural_key(const TypeSpec& spec);
std::string type_ref_structural_key(TypeRef ref);

uint64_t type_spec_hash(const TypeSpec& spec);
bool type_payloads_structurally_equal(const TypePayload& lhs,
                                      const TypePayload& rhs);
BuiltinTypeKind builtin_type_kind_from_spelling(std::string_view spelling);

} // namespace aburi::cir

#endif // ABURI_CIR_TYPE_H
