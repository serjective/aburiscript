#ifndef ABURI_TYPES_H
#define ABURI_TYPES_H
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>
#include <queue>
#include "constexpr/const_value.h"
// Forward declarations
class BitfieldLayoutEngine;
class ASTContext;
ASTContext* get_active_side_table_ast_context();
struct TargetInfo;
enum class SignedStatus {
    NO_SIGN,
    SIGNED,
    UNSIGNED,

};
struct Expr;
struct Decl;
struct TagDecl;
struct ObjectDecl;
struct EnumDecl;
struct EnumConstantDecl;
struct TypedefDecl;
struct CppMethodDecl;
struct CppConstructorDecl;
struct CppDestructorDecl;
struct FriendDecl;
struct FuncDecl;
struct VariableDecl;
struct FieldDecl;
struct FunctionType;
struct CppBaseSpecifier;
struct Symbol;
struct AbiPolicy;
struct TemplateParameterDecl;
struct TemplateTypeParmDecl;
struct TemplateNonTypeParmDecl;
struct TemplateTemplateParmDecl;
struct TemplateSpecializationType;
struct DependentNameType;
struct TemplateDecl;
struct CppTypeConstraint;
struct AliasTemplateDecl;
struct FunctionTemplateDecl;
struct VariableTemplateDecl;
struct ClassTemplateDecl;
struct VariableTemplatePartialSpecializationDecl;
struct ClassTemplatePartialSpecializationDecl;

bool template_decls_share_lookup_identity(const Decl* lhs, const Decl* rhs);

using TemplateParameterList = std::vector<std::unique_ptr<TemplateParameterDecl>>;

enum class TypeKind {
    Builtin, Pointer, MemberPointer, Reference, Array, Function, Object, Enum,
    CppTypeInfo,
    Typedef, Vector, Complex, BlockPointer, TemplateTypeParm,
    TemplateSpecialization, DependentName, Other, Placeholder, Auto,
    TypeofExpr, DecltypeExpr, BuiltinTypeTransform, BuiltinTypePackElement
};
std::string to_string_type_kind(TypeKind tkind);

enum class TagTypeKind : uint8_t {
    Record,
    Enum,
};

enum class AutoTypeFlavor : uint8_t {
    Gnu,
    Cxx,
    TemplateNonType,
    DecltypeAuto,
    DecltypeAutoTemplateNonType,
};

enum class ReferenceKind : uint8_t {
    LValue,
    RValue
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

// Qualifier flags — bitmask
enum Qualifiers : uint8_t {
    QUAL_NONE     = 0x00,
    QUAL_CONST    = 0x01,
    QUAL_VOLATILE = 0x02,
    QUAL_RESTRICT = 0x04,
    QUAL_ATOMIC   = 0x08,
};

// Forward declare
class QualType;

struct CType {
    TypeKind kind;
    mutable uint32_t external_semantic_owner_id = 0;
    explicit CType(): kind(TypeKind::Other) {}
    explicit CType(TypeKind k) : kind(k) {}
    virtual ~CType() = default;
    // this is in bits!!!
    virtual int64_t getWidth() { return 0; }
    int64_t getWidthBytes() {
        return (getWidth() + 7) / 8; // round up to the nearest byte if neceessary
    }
    virtual bool isArithmetic() const { return false; }
    virtual bool isScalar()     const {
        return isArithmetic() || kind == TypeKind::Pointer ||
               kind == TypeKind::MemberPointer || kind == TypeKind::Enum ||
               kind == TypeKind::BlockPointer;
    }
    virtual bool isAggregate()  const { return kind == TypeKind::Array || kind == TypeKind::Object; }
    virtual bool isIncomplete() const { return false; }
    virtual bool isInteger() const { return false; }
    virtual bool isFloatingPoint() const { return false; }
    virtual bool isComplex() const { return false; }
    virtual bool isUnsigned() const { return false; }
    virtual bool isVoid() const { return false; }
    virtual bool equals(const CType& other) {
        throw std::runtime_error("not implemented");
    }
    virtual std::string to_string() const { return "unknown"; }
    explicit CType(CType * prev) {
        kind = prev->kind;
    }
    /* bool operator==(const CType &other) {
        return typeid(*this) == typeid(other) && equals(other);
    }
 */
};
// for the explicit purpose of parsing declarations
struct PlaceholderType: CType {
    explicit PlaceholderType(): CType(TypeKind::Placeholder) {}
    static bool classof(const CType *t) { return t->kind == TypeKind::Placeholder; }
};

// Represents __auto_type before type deduction (transient: replaced by sema)
struct AutoType : CType {
    explicit AutoType(
        AutoTypeFlavor flavor = AutoTypeFlavor::Gnu,
        std::shared_ptr<const CppTypeConstraint> type_constraint = nullptr)
        : CType(TypeKind::Auto),
          flavor(flavor),
          type_constraint(std::move(type_constraint)) {}
    AutoTypeFlavor flavor = AutoTypeFlavor::Gnu;
    std::shared_ptr<const CppTypeConstraint> type_constraint = nullptr;
    bool isIncomplete() const override { return true; }
    std::string to_string() const override;
    bool equals(const CType& other) override;
    static bool classof(const CType *t) { return t->kind == TypeKind::Auto; }
};

// Represents typeof(expr) before sema resolves the expression's type (transient: replaced by sema)
struct TypeofExprType : CType {
    std::shared_ptr<Expr> expr;
    explicit TypeofExprType(std::shared_ptr<Expr> e)
        : CType(TypeKind::TypeofExpr), expr(std::move(e)) {}
    bool isIncomplete() const override { return true; }
    std::string to_string() const override { return "typeof(<expr>)"; }
    bool equals(const CType& other) override {
        return other.kind == TypeKind::TypeofExpr;
    }
    static bool classof(const CType *t) { return t->kind == TypeKind::TypeofExpr; }
};

// Represents decltype(expr) before sema resolves the declared-type /
// value-category rules (transient: replaced by sema).
struct DecltypeExprType : CType {
    std::shared_ptr<Expr> expr;
    bool use_declared_type_rule = false;

    explicit DecltypeExprType(std::shared_ptr<Expr> e,
                              bool use_declared_type_rule = false)
        : CType(TypeKind::DecltypeExpr),
          expr(std::move(e)),
          use_declared_type_rule(use_declared_type_rule) {}
    bool isIncomplete() const override { return true; }
    std::string to_string() const override { return "decltype(<expr>)"; }
    bool equals(const CType& other) override;
    static bool classof(const CType *t) {
        return t->kind == TypeKind::DecltypeExpr;
    }
};

// QualType wraps a shared_ptr<CType> with qualifier bits.
// The underlying CType is always the unqualified canonical type.
// Qualifiers live on the wrapper, not the type node.
class QualType {
    std::shared_ptr<CType> type;
    uint8_t quals = QUAL_NONE;

public:
    QualType() : type(nullptr), quals(QUAL_NONE) {}
    QualType(std::shared_ptr<CType> t) : type(std::move(t)), quals(QUAL_NONE) {}
    QualType(std::shared_ptr<CType> t, uint8_t q) : type(std::move(t)), quals(q) {}
    QualType(std::nullptr_t) : type(nullptr), quals(QUAL_NONE) {}

    // Explicit conversion to shared_ptr<CType>.  Drops qualifiers.
    // Use get_shared() at call sites that need the raw type pointer.
    explicit operator std::shared_ptr<CType>() const { return type; }

    // Pointer-like access to the underlying CType
    CType* operator->() const { return type.get(); }
    CType& operator*() const { return *type; }
    CType* get() const { return type.get(); }
    std::shared_ptr<CType> get_shared() const { return type; }
    std::shared_ptr<CType> get_unqualified_type() const { return type; }

    // Null checks
    bool is_null() const { return type == nullptr; }
    explicit operator bool() const { return type != nullptr; }

    // Qualifier queries
    uint8_t get_qualifiers() const { return quals; }
    bool is_const()    const { return quals & QUAL_CONST; }
    bool is_volatile() const { return quals & QUAL_VOLATILE; }
    bool is_restrict() const { return quals & QUAL_RESTRICT; }
    bool is_atomic()   const { return quals & QUAL_ATOMIC; }
    bool has_qualifiers() const { return quals != QUAL_NONE; }

    // Create qualified variants (returns new QualType sharing same CType)
    QualType with_const()    const { return {type, static_cast<uint8_t>(quals | QUAL_CONST)}; }
    QualType with_volatile() const { return {type, static_cast<uint8_t>(quals | QUAL_VOLATILE)}; }
    QualType with_restrict() const { return {type, static_cast<uint8_t>(quals | QUAL_RESTRICT)}; }
    QualType with_atomic()   const { return {type, static_cast<uint8_t>(quals | QUAL_ATOMIC)}; }
    QualType with_qualifiers(uint8_t q) const { return {type, static_cast<uint8_t>(quals | q)}; }
    QualType without_qualifiers() const { return {type, QUAL_NONE}; }

    // Type downcasting helpers (kind-based, no RTTI)
    template<typename T>
    T* as() const {
        if (!type || !T::classof(type.get())) return nullptr;
        return static_cast<T*>(type.get());
    }

    template<typename T>
    std::shared_ptr<T> as_shared() const {
        if (!type || !T::classof(type.get())) return nullptr;
        return std::static_pointer_cast<T>(type);
    }

    // Qualifier comparison
    bool has_all_qualifiers_of(const QualType& other) const {
        return (quals & other.quals) == other.quals;
    }

    // Equality ignoring qualifiers (backward compatible with existing equals())
    bool equals_unqualified(const QualType& other) const {
        if (!type || !other.type) return type.get() == other.type.get();
        return type->equals(*other.type) || other.type->equals(*type);
    }

    // Equality including qualifiers
    bool equals_qualified(const QualType& other) const {
        return quals == other.quals && equals_unqualified(other);
    }

    // Human-readable type string with qualifiers
    std::string to_string() const {
        if (!type) return "(null)";
        std::string result;
        // For pointer/block pointer types, qualifiers go after the */^ (e.g. "int *const")
        if (type->kind == TypeKind::Pointer || type->kind == TypeKind::BlockPointer) {
            result = type->to_string();
            if (quals & QUAL_CONST)    result += " const";
            if (quals & QUAL_VOLATILE) result += " volatile";
            if (quals & QUAL_RESTRICT) result += " restrict";
            if (quals & QUAL_ATOMIC)   result += " _Atomic";
        } else {
            if (quals & QUAL_CONST)    result += "const ";
            if (quals & QUAL_VOLATILE) result += "volatile ";
            if (quals & QUAL_RESTRICT) result += "restrict ";
            if (quals & QUAL_ATOMIC)   result += "_Atomic ";
            result += type->to_string();
        }
        return result;
    }
};

// Represents builtin type transformations such as __remove_reference(_Tp)
// before sema resolves the transformed type.
struct BuiltinTypeTransformType : CType {
    BuiltinTypeTransformKind transform_kind;
    QualType operand_type;

    explicit BuiltinTypeTransformType(BuiltinTypeTransformKind transform_kind,
                                      QualType operand_type)
        : CType(TypeKind::BuiltinTypeTransform),
          transform_kind(transform_kind),
          operand_type(std::move(operand_type)) {}
    bool isIncomplete() const override { return true; }
    std::string to_string() const override;
    bool equals(const CType& other) override {
        if (other.kind != TypeKind::BuiltinTypeTransform) {
            return false;
        }
        const auto& rhs = static_cast<const BuiltinTypeTransformType&>(other);
        return rhs.transform_kind == transform_kind &&
               operand_type.equals_qualified(rhs.operand_type);
    }
    static bool classof(const CType *t) {
        return t->kind == TypeKind::BuiltinTypeTransform;
    }
};

enum class TemplateArgumentKind : uint8_t {
    Type,
    Value,
    Template,
};

struct TemplateArgument {
    TemplateArgumentKind kind = TemplateArgumentKind::Type;
    QualType type = nullptr;
    QualType value_type = nullptr;
    ConstValue value = ConstValue::invalid();
    std::shared_ptr<Expr> value_expr = nullptr;
    const TemplateDecl* template_decl = nullptr;
    const TemplateParameterDecl* referenced_parameter = nullptr;
    QualType dependent_template_qualifier_type = nullptr;
    std::string dependent_template_member_name;
    bool is_dependent = false;
    bool expands_parameter_pack = false;
    std::string template_name;
    std::string value_spelling;
    std::vector<const TemplateParameterDecl*> pack_expansion_parameters;

    TemplateArgument() = default;
    explicit TemplateArgument(QualType type);

    static TemplateArgument value_argument(QualType value_type,
                                           ConstValue value,
                                           std::string spelling = {},
                                           std::shared_ptr<Expr> value_expr = nullptr);

    static TemplateArgument dependent_value_argument(
        QualType value_type,
        std::shared_ptr<Expr> value_expr,
        std::string spelling = {},
        const TemplateParameterDecl* referenced_parameter = nullptr);

    static TemplateArgument template_argument(
        const TemplateDecl* template_decl,
        std::string spelling = {});

    static TemplateArgument dependent_template_argument(
        std::string spelling = {},
        const TemplateParameterDecl* referenced_parameter = nullptr);

    TemplateArgument as_pack_expansion(
        std::vector<const TemplateParameterDecl*> referenced_pack_parameters = {})
        const;

    bool equals(const TemplateArgument& other) const;
    std::string to_string() const;
};

// Represents Clang's template-style builtin type selection
// __type_pack_element<I, Ts...>.  The first argument is the index expression;
// remaining arguments are type arguments and may include pack expansions until
// template substitution materializes them.
struct BuiltinTypePackElementType : CType {
    std::vector<TemplateArgument> arguments;

    explicit BuiltinTypePackElementType(std::vector<TemplateArgument> arguments)
        : CType(TypeKind::BuiltinTypePackElement),
          arguments(std::move(arguments)) {}

    bool isIncomplete() const override;
    std::string to_string() const override;
    bool equals(const CType& other) override {
        if (other.kind != TypeKind::BuiltinTypePackElement) {
            return false;
        }
        const auto& rhs =
            static_cast<const BuiltinTypePackElementType&>(other);
        if (arguments.size() != rhs.arguments.size()) {
            return false;
        }
        for (size_t idx = 0; idx < arguments.size(); ++idx) {
            if (!arguments[idx].equals(rhs.arguments[idx])) {
                return false;
            }
        }
        return true;
    }
    static bool classof(const CType* t) {
        return t->kind == TypeKind::BuiltinTypePackElement;
    }
};

bool template_specialization_components_are_dependent(
    const Decl* primary_template,
    const std::vector<TemplateArgument>& arguments,
    bool explicitly_dependent,
    const ASTContext* ast_ctx = nullptr);

enum class TemplateArgumentBindingKind : uint8_t {
    Unbound,
    Single,
    Pack,
};

struct TemplateArgumentBinding {
    TemplateArgumentBindingKind kind = TemplateArgumentBindingKind::Unbound;
    std::vector<TemplateArgument> arguments;

    TemplateArgumentBinding() = default;

    static TemplateArgumentBinding single(TemplateArgument argument) {
        TemplateArgumentBinding binding;
        binding.kind = TemplateArgumentBindingKind::Single;
        binding.arguments.push_back(std::move(argument));
        return binding;
    }

    static TemplateArgumentBinding pack(std::vector<TemplateArgument> arguments) {
        TemplateArgumentBinding binding;
        binding.kind = TemplateArgumentBindingKind::Pack;
        binding.arguments = std::move(arguments);
        return binding;
    }

    bool is_unbound() const {
        return kind == TemplateArgumentBindingKind::Unbound;
    }

    bool is_single() const {
        return kind == TemplateArgumentBindingKind::Single;
    }

    bool is_pack() const {
        return kind == TemplateArgumentBindingKind::Pack;
    }

    const TemplateArgument* single_argument() const {
        return is_single() && arguments.size() == 1 ? &arguments.front() : nullptr;
    }

    bool equals(const TemplateArgumentBinding& other) const {
        if (kind != other.kind || arguments.size() != other.arguments.size()) {
            return false;
        }
        for (size_t idx = 0; idx < arguments.size(); ++idx) {
            if (!arguments[idx].equals(other.arguments[idx])) {
                return false;
            }
        }
        return true;
    }

    std::string to_string() const {
        switch (kind) {
            case TemplateArgumentBindingKind::Unbound:
                return "<unbound-template-arg>";
            case TemplateArgumentBindingKind::Single:
                return single_argument()
                    ? single_argument()->to_string()
                    : "<invalid-single-template-arg>";
            case TemplateArgumentBindingKind::Pack: {
                std::string out = "{";
                for (size_t idx = 0; idx < arguments.size(); ++idx) {
                    if (idx > 0) {
                        out += ", ";
                    }
                    out += arguments[idx].to_string();
                }
                out += "}";
                return out;
            }
        }
        return "<unknown-template-arg-binding>";
    }
};

using TemplateArgumentBindings = std::vector<TemplateArgumentBinding>;

struct DependentLookupQualifier {
    bool has_global_qualifier = false;
    bool is_type_qualified = false;
    bool is_current_instantiation = false;
    bool names_dependent_base = false;
    QualType qualifier_type = nullptr;
    std::vector<std::string> qualifiers;

    bool has_qualifier() const {
        return has_global_qualifier || is_type_qualified || !qualifiers.empty();
    }
};

struct CppQualifiedExprInfo {
    bool has_global_qualifier = false;
    bool is_type_qualified = false;
    bool is_current_instantiation = false;
    QualType qualifier_type = nullptr;
    std::vector<std::string> qualifiers;

    bool has_qualifier() const {
        return has_global_qualifier || is_type_qualified || !qualifiers.empty();
    }
};

inline CppQualifiedExprInfo build_cpp_qualified_expr_info(
    bool has_global_qualifier,
    std::vector<std::string> qualifiers = {},
    QualType qualifier_type = nullptr,
    bool is_type_qualified = false,
    bool is_current_instantiation = false) {
    CppQualifiedExprInfo info;
    info.has_global_qualifier = has_global_qualifier;
    info.is_type_qualified = is_type_qualified;
    info.is_current_instantiation = is_current_instantiation;
    info.qualifier_type = qualifier_type;
    info.qualifiers = std::move(qualifiers);
    return info;
}

inline CppQualifiedExprInfo build_cpp_qualified_expr_info(
    const DependentLookupQualifier& qualifier) {
    return build_cpp_qualified_expr_info(
        qualifier.has_global_qualifier,
        qualifier.qualifiers,
        qualifier.qualifier_type,
        qualifier.is_type_qualified,
        qualifier.is_current_instantiation);
}

inline DependentLookupQualifier build_dependent_lookup_qualifier(
    const CppQualifiedExprInfo& info) {
    DependentLookupQualifier qualifier;
    qualifier.has_global_qualifier = info.has_global_qualifier;
    qualifier.is_type_qualified = info.is_type_qualified;
    qualifier.is_current_instantiation = info.is_current_instantiation;
    qualifier.qualifier_type = info.qualifier_type;
    qualifier.qualifiers = info.qualifiers;
    return qualifier;
}

inline DependentLookupQualifier build_dependent_lookup_qualifier(
    const CppQualifiedExprInfo* info) {
    if (!info) {
        return DependentLookupQualifier{};
    }
    return build_dependent_lookup_qualifier(*info);
}

bool template_parameter_references_have_same_lookup_shape(
    const TemplateParameterDecl* lhs,
    const TemplateParameterDecl* rhs);
bool template_parameter_types_have_same_lookup_shape(QualType lhs,
                                                     QualType rhs);
bool template_argument_has_same_lookup_shape(const TemplateArgument& lhs,
                                             const TemplateArgument& rhs);
bool template_arguments_have_same_lookup_shape(
    const std::vector<TemplateArgument>& lhs,
    const std::vector<TemplateArgument>& rhs);
bool expressions_have_same_structural_shape(const Expr* lhs,
                                            const Expr* rhs);
bool types_equivalent_after_template_argument_canonicalization(
    QualType lhs,
    QualType rhs,
    const ASTContext* ast_ctx,
    bool ignore_top_level_qualifiers = false);

struct TemplateEnvironmentFrame {
    std::vector<const TemplateParameterDecl*> parameters;
    TemplateArgumentBindings bindings;
    const TemplateDecl* template_decl = nullptr;
    const Decl* owner_decl = nullptr;
    QualType current_instantiation_type = nullptr;
    std::optional<uint32_t> template_depth;

    TemplateEnvironmentFrame() = default;
    TemplateEnvironmentFrame(
        std::vector<const TemplateParameterDecl*> parameters,
        TemplateArgumentBindings bindings = {},
        const TemplateDecl* template_decl = nullptr,
        const Decl* owner_decl = nullptr,
        QualType current_instantiation_type = nullptr,
        std::optional<uint32_t> template_depth = std::nullopt);

    const TemplateArgumentBinding* lookup(
        const TemplateParameterDecl* parameter) const;
    TemplateArgumentBinding* lookup(const TemplateParameterDecl* parameter);
    std::optional<size_t> pack_binding_size(
        const TemplateParameterDecl* parameter,
        std::string* error_out = nullptr) const;
};

enum class TemplateDelayedResolutionPolicy : uint8_t {
    PreserveUnresolved,
    ResolveWhenConcrete,
};

struct TemplatePatternContext {
    const Decl* owning_decl = nullptr;
    QualType current_instantiation_type = nullptr;
    const Decl* point_of_instantiation_decl = nullptr;
    TemplateDelayedResolutionPolicy delayed_resolution_policy =
        TemplateDelayedResolutionPolicy::PreserveUnresolved;
};

struct TemplateEnvironment {
    std::vector<TemplateEnvironmentFrame> frames;
    std::optional<TemplatePatternContext> pattern_context;

    void push_frame(TemplateEnvironmentFrame frame);
    void pop_frame();
    bool empty() const;

    const TemplateArgumentBinding* lookup(
        const TemplateParameterDecl* parameter) const;
    TemplateArgumentBinding* lookup(const TemplateParameterDecl* parameter);

    const TemplateEnvironmentFrame* lookup_frame(
        const TemplateParameterDecl* parameter) const;
    TemplateEnvironmentFrame* lookup_frame(
        const TemplateParameterDecl* parameter);

    std::optional<size_t> pack_binding_size(
        const TemplateParameterDecl* parameter,
        std::string* error_out = nullptr) const;
    std::optional<size_t> pack_expansion_arity(
        const std::vector<const TemplateParameterDecl*>& parameters,
        std::string* error_out = nullptr) const;

    QualType current_instantiation_type() const;
};

bool bind_template_arguments_to_parameters(
    const TemplateParameterList& parameters,
    const std::vector<TemplateArgument>& arguments,
    TemplateArgumentBindings& bindings_out,
    std::string* error_out = nullptr);

bool bind_explicit_template_arguments_prefix_to_parameters(
    const TemplateParameterList& parameters,
    const std::vector<TemplateArgument>& explicit_arguments,
    TemplateArgumentBindings& bindings_out,
    std::string* error_out = nullptr);

bool complete_template_argument_bindings_with_defaults(
    const TemplateDecl* template_decl,
    TemplateArgumentBindings& bindings_out,
    std::string* error_out = nullptr);

bool template_template_parameter_lists_are_compatible(
    const TemplateParameterList& formal_parameters,
    const TemplateParameterList& actual_parameters);

std::vector<TemplateArgument> flatten_template_argument_bindings(
    const TemplateArgumentBindings& bindings);

QualType lookup_template_specialization_resolved_type(
    const TemplateSpecializationType* type,
    const ASTContext* ast_ctx);
void cache_template_specialization_resolved_type(
    ASTContext* ast_ctx,
    QualType type,
    QualType resolved_type);
void cache_existing_class_template_specialization_resolved_type(
    ASTContext* ast_ctx,
    QualType type,
    bool publish_to_persistent_store = false);
QualType lookup_dependent_name_resolved_type(
    const DependentNameType* type,
    const ASTContext* ast_ctx);
void cache_dependent_name_resolved_type(
    ASTContext* ast_ctx,
    QualType type,
    QualType resolved_type);

bool is_nullptr_type(QualType type, const ASTContext* ast_ctx = nullptr);
bool is_null_pointer_like_type(QualType type, const ASTContext* ast_ctx = nullptr);
bool is_supported_non_type_template_parameter_type(
    QualType type,
    const ASTContext* ast_ctx = nullptr);

bool type_depends_on_template_parameters(QualType type);
bool type_depends_on_template_parameters(QualType type,
                                         const ASTContext* ast_ctx);
bool template_argument_depends_on_template_parameters(
    const TemplateArgument& argument);
bool template_argument_depends_on_template_parameters(
    const TemplateArgument& argument,
    const ASTContext* ast_ctx);
bool function_exception_specs_equal(const FunctionType& lhs,
                                    const FunctionType& rhs);

enum class BuiltinTypes {
    Void,
    NullPtr,
    Bool,
    Char,
    SChar,
    UChar,
    WChar,
    Char16,
    Char32,
    Short,
    UShort,
    UInt,
    Int,
    Long,
    ULong,
    LongLong,
    ULongLong,
    Int128,
    UInt128,
    Float16,
    Float,
    Double,
    LongDouble,
};
struct BuiltinType : CType {
    BuiltinTypes builtin_kind;
    int64_t width_override = -1;
    int rank_override = -1;
    int8_t unsigned_override = -1;

    BuiltinType(BuiltinTypes k) : CType(TypeKind::Builtin), builtin_kind(k) {}
    BuiltinType(BuiltinTypes k,
                int64_t width_override,
                int rank_override,
                int8_t unsigned_override)
        : CType(TypeKind::Builtin),
          builtin_kind(k),
          width_override(width_override),
          rank_override(rank_override),
          unsigned_override(unsigned_override) {}
    bool isArithmetic() const override {
        return builtin_kind != BuiltinTypes::Void &&
               builtin_kind != BuiltinTypes::NullPtr;
    }
    bool isScalar() const override {
        return builtin_kind != BuiltinTypes::Void;
    }
    bool isInteger() const override {
        return builtin_kind != BuiltinTypes::Void &&
               builtin_kind != BuiltinTypes::NullPtr &&
               builtin_kind != BuiltinTypes::Float16 &&
               builtin_kind != BuiltinTypes::Float &&
               builtin_kind != BuiltinTypes::Double && builtin_kind != BuiltinTypes::LongDouble;
    }
    bool isFloatingPoint() const override {
        return builtin_kind == BuiltinTypes::Float16 || builtin_kind == BuiltinTypes::Float ||
               builtin_kind == BuiltinTypes::Double ||
               builtin_kind == BuiltinTypes::LongDouble;
    }
    // in bits
    bool equals(const CType &other) override {
        if (other.kind != TypeKind::Builtin) return false;
        return builtin_kind == static_cast<const BuiltinType&>(other).builtin_kind;
    }
    static bool classof(const CType *t) { return t->kind == TypeKind::Builtin; }
    bool isVoid() const override {
        return builtin_kind == BuiltinTypes::Void;
    }
    int64_t getWidth() override;
    int getRank() const;
    bool isUnsigned() const override;
    std::string to_string() const override {
        switch (builtin_kind) {
            case BuiltinTypes::Void: return "void";
            case BuiltinTypes::NullPtr: return "decltype(nullptr)";
            case BuiltinTypes::Bool: return "_Bool";
            case BuiltinTypes::Char: return "char";
            case BuiltinTypes::SChar: return "signed char";
            case BuiltinTypes::UChar: return "unsigned char";
            case BuiltinTypes::WChar: return "wchar_t";
            case BuiltinTypes::Char16: return "char16_t";
            case BuiltinTypes::Char32: return "char32_t";
            case BuiltinTypes::Short: return "short";
            case BuiltinTypes::UShort: return "unsigned short";
            case BuiltinTypes::Int: return "int";
            case BuiltinTypes::UInt: return "unsigned int";
            case BuiltinTypes::Long: return "long";
            case BuiltinTypes::ULong: return "unsigned long";
            case BuiltinTypes::LongLong: return "long long";
            case BuiltinTypes::ULongLong: return "unsigned long long";
            case BuiltinTypes::Int128: return "__int128";
            case BuiltinTypes::UInt128: return "unsigned __int128";
            case BuiltinTypes::Float16: return "_Float16";
            case BuiltinTypes::Float: return "float";
            case BuiltinTypes::Double: return "double";
            case BuiltinTypes::LongDouble: return "long double";
        }
        return "unknown";
    }
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

struct FunctionType: CType {
    FunctionType(): CType(TypeKind::Function) {};
    QualType ret_type;
    std::vector<QualType> parameters;
    std::vector<uint8_t> parameter_pack_flags;
    bool is_variadic = false;
    // true = proper prototype with typed params or (void); false = K&R ()
    bool has_prototype = true;
    // Member-function ref-qualifier (none, &, &&).
    FunctionRefQualifierKind member_ref_qualifier = FunctionRefQualifierKind::None;
    // Whether the declaration had an explicit exception specification.
    bool has_explicit_exception_spec = false;
    // C++ noexcept model: currently tracks potentially-throwing vs non-throwing.
    FunctionExceptionSpecKind exception_spec = FunctionExceptionSpecKind::PotentiallyThrowing;
    // in a function like void process() noexcept(sizeof(void*) == 8)
    // , exception_spec_expr is the expression in the noexcept
    std::shared_ptr<Expr> exception_spec_expr = nullptr;
    bool equals(const CType &other) override;
    bool parameter_is_pack(size_t index) const {
        return index < parameter_pack_flags.size() &&
               parameter_pack_flags[index] != 0;
    }
    void normalize_parameter_pack_flags() {
        parameter_pack_flags.resize(parameters.size(), 0);
    }
    void push_parameter(QualType parameter, bool is_parameter_pack = false) {
        parameters.push_back(std::move(parameter));
        parameter_pack_flags.push_back(is_parameter_pack ? 1 : 0);
    }
    void insert_parameter(size_t index,
                          QualType parameter,
                          bool is_parameter_pack = false) {
        if (index > parameters.size()) {
            index = parameters.size();
        }
        parameters.insert(parameters.begin() + index, std::move(parameter));
        if (parameter_pack_flags.size() < parameters.size() - 1) {
            parameter_pack_flags.resize(parameters.size() - 1, 0);
        }
        parameter_pack_flags.insert(
            parameter_pack_flags.begin() + index,
            is_parameter_pack ? 1 : 0);
    }
    void clear_parameters() {
        parameters.clear();
        parameter_pack_flags.clear();
    }
    int64_t getWidth() override {
        return 8; // for sizeof gcc extension
    }
    static bool classof(const CType *t) { return t->kind == TypeKind::Function; }
    std::string to_string() const override;
};
struct PointerType : CType {
    QualType pointed_type;
    explicit PointerType(QualType pointed) : CType(TypeKind::Pointer), pointed_type(std::move(pointed)) {}
    bool equals(const CType &other) override;
    int64_t getWidth() override;
    bool isUnsigned() const override { return true; }
    static bool classof(const CType *t) { return t->kind == TypeKind::Pointer; }
    std::string to_string() const override;
};

struct MemberPointerType : CType {
    QualType class_type;
    QualType member_type;

    MemberPointerType(QualType class_type, QualType member_type)
        : CType(TypeKind::MemberPointer),
          class_type(std::move(class_type)),
          member_type(std::move(member_type)) {}

    bool equals(const CType& other) override;
    int64_t getWidth() override;
    bool isUnsigned() const override { return true; }
    bool isScalar() const override { return true; }

    static bool classof(const CType* t) { return t->kind == TypeKind::MemberPointer; }
    std::string to_string() const override;
};

struct ReferenceType : CType {
    QualType referred_type;
    ReferenceKind reference_kind;

    explicit ReferenceType(QualType referred, ReferenceKind kind = ReferenceKind::LValue)
        : CType(TypeKind::Reference), referred_type(std::move(referred)), reference_kind(kind) {}

    bool equals(const CType& other) override {
        if (other.kind != TypeKind::Reference) return false;
        const auto& rhs = static_cast<const ReferenceType&>(other);
        return reference_kind == rhs.reference_kind &&
            referred_type.equals_qualified(rhs.referred_type);
    }

    int64_t getWidth() override {
        return referred_type ? referred_type->getWidth() : 0;
    }

    bool isScalar() const override { return true; }

    bool isIncomplete() const override {
        return !referred_type || referred_type->isIncomplete();
    }

    bool isLValueReference() const { return reference_kind == ReferenceKind::LValue; }
    bool isRValueReference() const { return reference_kind == ReferenceKind::RValue; }

    static bool classof(const CType* t) { return t->kind == TypeKind::Reference; }
    std::string to_string() const override;
};

// Compiler-owned RTTI surface type used for `typeid` until stdlib headers are
// available. The expression-level surface is `const __aburi_type_info&`.
struct CppTypeInfoType : CType {
    int64_t descriptor_width_bits = 64;

    explicit CppTypeInfoType(int64_t descriptor_width_bits = 64)
        : CType(TypeKind::CppTypeInfo),
          descriptor_width_bits(descriptor_width_bits > 0
                                    ? descriptor_width_bits
                                    : 64) {}

    bool equals(const CType& other) override {
        if (other.kind != TypeKind::CppTypeInfo) {
            return false;
        }
        const auto& rhs = static_cast<const CppTypeInfoType&>(other);
        return descriptor_width_bits == rhs.descriptor_width_bits;
    }

    int64_t getWidth() override {
        return descriptor_width_bits;
    }

    std::string to_string() const override {
        return "__aburi_type_info";
    }

    static bool classof(const CType* t) {
        return t->kind == TypeKind::CppTypeInfo;
    }
};
// Apple Block pointer type: void (^)(int, float)
// The pointed_type is always a FunctionType describing the block's signature.
// At the ABI level, a block pointer is a regular pointer to a heap-allocated block struct.
struct BlockPointerType : CType {
    QualType pointed_type;

    explicit BlockPointerType(QualType pointed)
        : CType(TypeKind::BlockPointer), pointed_type(std::move(pointed)) {}

    bool isScalar() const override { return true; }

    bool equals(const CType &other) override {
        if (other.kind != TypeKind::BlockPointer) return false;
        return pointed_type.equals_qualified(static_cast<const BlockPointerType&>(other).pointed_type);
    }

    int64_t getWidth() override {
        return 64;
    }

    bool isUnsigned() const override { return true; }

    static bool classof(const CType *t) { return t->kind == TypeKind::BlockPointer; }

    std::string to_string() const override {
        if (auto func = pointed_type.as_shared<FunctionType>()) {
            std::string result = func->ret_type.to_string() + " (^)(";
            for (size_t i = 0; i < func->parameters.size(); ++i) {
                if (i > 0) result += ", ";
                result += func->parameters[i].to_string();
            }
            if (func->is_variadic) {
                if (!func->parameters.empty()) result += ", ";
                result += "...";
            }
            result += ")";
            return result;
        }
        return pointed_type.to_string() + " ^";
    }
};
enum class ArraySizeKind {
    Incomplete,
    Constant,
    Variable
};
struct ArrayType : CType {
    QualType element_type;
    ArraySizeKind size_kind;
    std::optional<size_t> size; // std::nullopt if incomplete/unknown size, 0 sized arrays are handled per GCC extension
    std::shared_ptr<Expr> size_expr;
    explicit ArrayType(QualType element, std::optional<size_t> size = std::nullopt)
        : CType(TypeKind::Array), element_type(std::move(element)),
          size_kind(size.has_value() ? ArraySizeKind::Constant : ArraySizeKind::Incomplete),
          size(size), size_expr(nullptr) {}
    explicit ArrayType(QualType element, std::shared_ptr<Expr> size_expr)
    : CType(TypeKind::Array), element_type(std::move(element)),
      size_kind(ArraySizeKind::Variable), size(std::nullopt),
      size_expr(std::move(size_expr)) {}
    bool equals(const CType &other) override {
        if (other.kind != TypeKind::Array) return false;
        const auto& otherArr = static_cast<const ArrayType&>(other);
        if (!element_type.equals_qualified(otherArr.element_type)) return false;
        bool this_const = size_kind == ArraySizeKind::Constant && size.has_value();
        bool other_const = otherArr.size_kind == ArraySizeKind::Constant && otherArr.size.has_value();
        if (this_const && other_const) {
            return size.value() == otherArr.size.value();
        }
        bool this_incomplete =
            size_kind == ArraySizeKind::Incomplete ||
            (size_kind == ArraySizeKind::Constant && !size.has_value());
        bool other_incomplete =
            otherArr.size_kind == ArraySizeKind::Incomplete ||
            (otherArr.size_kind == ArraySizeKind::Constant && !otherArr.size.has_value());
        if (this_incomplete || other_incomplete) {
            return true;
        }
        // VLA bounds are expression-based; treat variable-bounded arrays with
        // compatible element types as compatible.
        if (size_kind == ArraySizeKind::Variable &&
            otherArr.size_kind == ArraySizeKind::Variable) {
            return true;
        }
        return size_kind == otherArr.size_kind && size == otherArr.size;
    }
    static bool classof(const CType *t) { return t->kind == TypeKind::Array; }
    int64_t getWidth() override {
        if (size == std::nullopt) return 0;
        return *size * element_type->getWidth();
    }
    bool isIncomplete() const override {
        if (size_kind != ArraySizeKind::Constant || !size.has_value()) return 0;

        // int [][3] is incomplete
        return !size.has_value() || element_type->isIncomplete();
    }
    bool isVLA() const {
        return size_kind == ArraySizeKind::Variable;
    }
    std::string to_string() const override;
};

// Represents a SIMD vector type created by __attribute__((vector_size(N)))
struct VectorType : CType {
    QualType element_type;     // Must be integer or floating-point builtin
    size_t num_elements;       // N / sizeof(element_type)
    size_t total_bytes;        // N from vector_size(N)

    explicit VectorType(QualType elem, size_t total_bytes)
        : CType(TypeKind::Vector), element_type(std::move(elem)),
          total_bytes(total_bytes) {
        int64_t elem_bytes = element_type->getWidthBytes();
        num_elements = (elem_bytes > 0) ? total_bytes / static_cast<size_t>(elem_bytes) : 0;
    }

    int64_t getWidth() override {
        return static_cast<int64_t>(total_bytes) * 8;
    }
    bool isUnsigned() const override { return element_type->isUnsigned(); }
    bool isFloatingPoint() const override { return element_type->isFloatingPoint(); }
    bool isInteger() const override { return element_type->isInteger(); }
    bool isArithmetic() const override { return true; }
    bool equals(const CType& other) override {
        if (other.kind != TypeKind::Vector) return false;
        const auto& o = static_cast<const VectorType&>(other);
        return total_bytes == o.total_bytes && element_type->equals(*o.element_type);
    }
    static bool classof(const CType *t) { return t->kind == TypeKind::Vector; }
    std::string to_string() const override {
        return element_type.to_string() + " __attribute__((vector_size(" +
               std::to_string(total_bytes) + ")))";
    }
};

// Represents a C _Complex type. GCC also supports integer complex as an extension.
// Stored as a two-element aggregate: { real, imag }
struct ComplexType : CType {
    std::shared_ptr<BuiltinType> element_type;

    explicit ComplexType(std::shared_ptr<BuiltinType> elem)
        : CType(TypeKind::Complex), element_type(std::move(elem)) {}

    int64_t getWidth() override {
        return element_type->getWidth() * 2;
    }

    bool isArithmetic() const override { return true; }
    bool isFloatingPoint() const override { return element_type && element_type->isFloatingPoint(); }
    bool isComplex() const override { return true; }

    bool equals(const CType& other) override {
        if (other.kind != TypeKind::Complex) return false;
        return element_type->equals(*static_cast<const ComplexType&>(other).element_type);
    }

    static bool classof(const CType *t) { return t->kind == TypeKind::Complex; }

    std::string to_string() const override {
        return element_type->to_string() + " _Complex";
    }

    std::shared_ptr<BuiltinType> get_real_type() const {
        return element_type;
    }
};

// Represents a typedef spelling while preserving access to its underlying type.
struct TypedefType : CType {
    std::string name;
    QualType underlying_type;
    const TypedefDecl* typedef_decl;

    explicit TypedefType(std::string typedef_name,
                         QualType underlying,
                         const TypedefDecl* decl = nullptr)
        : CType(TypeKind::Typedef),
          name(std::move(typedef_name)),
          underlying_type(std::move(underlying)),
          typedef_decl(decl) {}

    int64_t getWidth() override {
        return underlying_type ? underlying_type->getWidth() : 0;
    }
    bool isArithmetic() const override {
        return underlying_type && underlying_type->isArithmetic();
    }
    bool isScalar() const override {
        return underlying_type && underlying_type->isScalar();
    }
    bool isAggregate() const override {
        return underlying_type && underlying_type->isAggregate();
    }
    bool isIncomplete() const override {
        return !underlying_type || underlying_type->isIncomplete();
    }
    bool isInteger() const override {
        return underlying_type && underlying_type->isInteger();
    }
    bool isFloatingPoint() const override {
        return underlying_type && underlying_type->isFloatingPoint();
    }
    bool isComplex() const override {
        return underlying_type && underlying_type->isComplex();
    }
    bool isUnsigned() const override {
        return underlying_type && underlying_type->isUnsigned();
    }
    bool isVoid() const override {
        return underlying_type && underlying_type->isVoid();
    }
    bool equals(const CType& other) override {
        if (!underlying_type) {
            return false;
        }
        if (other.kind == TypeKind::Typedef) {
            const auto& rhs = static_cast<const TypedefType&>(other);
            if (!rhs.underlying_type) {
                return false;
            }
            return underlying_type.equals_qualified(rhs.underlying_type) ||
                underlying_type.equals_unqualified(rhs.underlying_type);
        }
        return underlying_type->equals(other);
    }
    static bool classof(const CType *t) { return t->kind == TypeKind::Typedef; }
    std::string to_string() const override {
        if (!name.empty()) {
            return name;
        }
        return underlying_type ? underlying_type.to_string() : "(typedef)";
    }
};

struct TemplateTypeParmType : CType {
    std::string name;
    uint32_t depth = 0;
    uint32_t index = 0;
    bool is_parameter_pack = false;
    const TemplateTypeParmDecl* parameter_decl = nullptr;

    explicit TemplateTypeParmType(std::string name,
                                  uint32_t depth = 0,
                                  uint32_t index = 0,
                                  bool is_parameter_pack = false,
                                  const TemplateTypeParmDecl* parameter_decl = nullptr)
        : CType(TypeKind::TemplateTypeParm),
          name(std::move(name)),
          depth(depth),
          index(index),
          is_parameter_pack(is_parameter_pack),
          parameter_decl(parameter_decl) {}

    bool isIncomplete() const override { return true; }

    bool equals(const CType& other) override {
        if (other.kind != TypeKind::TemplateTypeParm) {
            return false;
        }
        const auto& rhs = static_cast<const TemplateTypeParmType&>(other);
        if (parameter_decl && rhs.parameter_decl) {
            return parameter_decl == rhs.parameter_decl;
        }
        return depth == rhs.depth &&
               index == rhs.index &&
               is_parameter_pack == rhs.is_parameter_pack &&
               name == rhs.name;
    }

    std::string to_string() const override {
        std::string prefix;
        if (is_parameter_pack) {
            prefix = "...";
        }
        if (!name.empty()) {
            return prefix + name;
        }
        return prefix + "type-parameter-" + std::to_string(depth) + "-" +
               std::to_string(index);
    }

    static bool classof(const CType* t) {
        return t->kind == TypeKind::TemplateTypeParm;
    }
};

struct TemplateSpecializationType : CType {
    std::string template_name;
    const Decl* primary_template = nullptr;
    std::vector<TemplateArgument> arguments;
    bool is_dependent = false;
    bool is_class_template_placeholder = false;
    explicit TemplateSpecializationType(std::string template_name,
                                        const Decl* primary_template,
                                        std::vector<TemplateArgument> arguments,
                                        bool is_dependent = false,
                                        bool is_class_template_placeholder = false)
        : CType(TypeKind::TemplateSpecialization),
          template_name(std::move(template_name)),
          primary_template(primary_template),
          arguments(std::move(arguments)),
          is_dependent(is_dependent),
          is_class_template_placeholder(is_class_template_placeholder) {
        this->is_dependent = template_specialization_components_are_dependent(
            this->primary_template,
            this->arguments,
            this->is_dependent);
    }

    bool depends_on_template_parameters(
        const ASTContext* ast_ctx = nullptr) const;

    bool isIncomplete() const override {
        auto resolved =
            lookup_template_specialization_resolved_type(
                this,
                get_active_side_table_ast_context());
        return !resolved || resolved->isIncomplete();
    }

    bool equals(const CType& other) override {
        if (other.kind != TypeKind::TemplateSpecialization) {
            return false;
        }
        const auto& rhs = static_cast<const TemplateSpecializationType&>(other);
        if (primary_template && rhs.primary_template &&
            !template_decls_share_lookup_identity(primary_template,
                                                  rhs.primary_template)) {
            return false;
        }
        if (template_name != rhs.template_name ||
            arguments.size() != rhs.arguments.size()) {
            return false;
        }
        for (size_t idx = 0; idx < arguments.size(); ++idx) {
            if (!arguments[idx].equals(rhs.arguments[idx])) {
                return false;
            }
        }
        return true;
    }

    std::string to_string() const override {
        std::string out = template_name;
        if (is_class_template_placeholder) {
            return out;
        }
        out += "<";
        for (size_t idx = 0; idx < arguments.size(); ++idx) {
            if (idx > 0) {
                out += ", ";
            }
            out += arguments[idx].to_string();
        }
        out += ">";
        return out;
    }

    static bool classof(const CType* t) {
        return t->kind == TypeKind::TemplateSpecialization;
    }
};

struct DependentNameType : CType {
    QualType qualifier_type;
    std::string member_name;
    std::vector<TemplateArgument> template_arguments;
    bool is_current_instantiation = false;
    bool requires_typename_keyword = false;
    bool requires_template_keyword = false;
    explicit DependentNameType(QualType qualifier_type,
                               std::string member_name,
                               std::vector<TemplateArgument> template_arguments = {},
                               bool is_current_instantiation = false,
                               bool requires_typename_keyword = false,
                               bool requires_template_keyword = false)
        : CType(TypeKind::DependentName),
          qualifier_type(std::move(qualifier_type)),
          member_name(std::move(member_name)),
          template_arguments(std::move(template_arguments)),
          is_current_instantiation(is_current_instantiation),
          requires_typename_keyword(requires_typename_keyword),
          requires_template_keyword(requires_template_keyword) {}

    bool isIncomplete() const override {
        auto resolved =
            lookup_dependent_name_resolved_type(
                this,
                get_active_side_table_ast_context());
        return !resolved || resolved->isIncomplete();
    }

    bool equals(const CType& other) override {
        if (other.kind != TypeKind::DependentName) {
            return false;
        }
        const auto& rhs = static_cast<const DependentNameType&>(other);
        if (!qualifier_type.equals_qualified(rhs.qualifier_type) ||
            member_name != rhs.member_name ||
            template_arguments.size() != rhs.template_arguments.size() ||
            is_current_instantiation != rhs.is_current_instantiation ||
            requires_typename_keyword != rhs.requires_typename_keyword ||
            requires_template_keyword != rhs.requires_template_keyword) {
            return false;
        }
        for (size_t idx = 0; idx < template_arguments.size(); ++idx) {
            if (!template_arguments[idx].equals(rhs.template_arguments[idx])) {
                return false;
            }
        }
        return true;
    }

    std::string to_string() const override {
        std::string out;
        if (requires_typename_keyword) {
            out += "typename ";
        }
        out += qualifier_type.to_string();
        out += "::";
        if (requires_template_keyword) {
            out += "template ";
        }
        out += member_name;
        if (!template_arguments.empty()) {
            out += "<";
            for (size_t idx = 0; idx < template_arguments.size(); ++idx) {
                if (idx > 0) {
                    out += ", ";
                }
                out += template_arguments[idx].to_string();
            }
            out += ">";
        }
        return out;
    }

    static bool classof(const CType* t) {
        return t->kind == TypeKind::DependentName;
    }
};

// Clang-style scaffolding: tag types share a base carrying a declaration
// reference.
struct TagType : CType {
    const TagDecl* tag_decl;

    explicit TagType(TypeKind kind, const TagDecl* decl = nullptr)
        : CType(kind), tag_decl(decl) {}

    const TagDecl* get_decl() const { return tag_decl; }
    void set_decl(const TagDecl* decl) { tag_decl = decl; }

    virtual TagTypeKind get_tag_type_kind() const = 0;
    static bool classof(const CType *t) {
        return t && (t->kind == TypeKind::Object || t->kind == TypeKind::Enum);
    }
};

enum class RecordMemberAccess : uint8_t {
    Public = 1,
    Protected = 2,
    Private = 3,
};

// Represents a struct or union type
struct ObjectType : TagType {
    struct ClassTemplateSpecializationInfo {
        const ClassTemplateDecl* primary_template = nullptr;
        std::vector<TemplateArgument> arguments;
    };

    struct Field {
        std::string name;
        QualType type;
        size_t offset;  // Byte offset from start of struct (or storage unit for bitfields)

        // Bitfield support
        bool is_bitfield = false;
        uint32_t bit_offset = 0;    // Bit offset within storage unit
        uint32_t bit_width = 0;     // Width in bits (0 for non-bitfield)
        uint32_t storage_size = 0;  // Size of storage unit in bits (byte-multiple)

        // Per-field alignment override (from __attribute__((aligned(N))))
        size_t forced_alignment = 0;
        // Internal layout metadata for C++ base-subobject modeling.
        bool is_base_subobject = false;
        bool is_virtual_base_storage = false;
        size_t storage_size_override = 0;
        size_t storage_alignment_override = 0;
        // C++ member access metadata.
        RecordMemberAccess declared_access = RecordMemberAccess::Public;
        bool is_mutable = false;
        const FieldDecl* decl = nullptr;

        // Constructor for regular fields
        Field(std::string name, QualType type, size_t offset = 0,
              RecordMemberAccess declared_access = RecordMemberAccess::Public,
              bool is_mutable = false,
              const FieldDecl* decl = nullptr)
            : name(std::move(name)), type(std::move(type)), offset(offset),
              is_bitfield(false), bit_offset(0), bit_width(0), storage_size(0),
              forced_alignment(0), is_base_subobject(false),
              is_virtual_base_storage(false), storage_size_override(0),
              storage_alignment_override(0), declared_access(declared_access),
              is_mutable(is_mutable), decl(decl) {}

        // Constructor for bitfields
        Field(std::string name, QualType type, size_t offset,
              uint32_t bit_offset, uint32_t bit_width, uint32_t storage_size,
              RecordMemberAccess declared_access = RecordMemberAccess::Public,
              bool is_mutable = false,
              const FieldDecl* decl = nullptr)
            : name(std::move(name)), type(std::move(type)), offset(offset),
              is_bitfield(true), bit_offset(bit_offset), bit_width(bit_width),
              storage_size(storage_size), forced_alignment(0),
              is_base_subobject(false), is_virtual_base_storage(false),
              storage_size_override(0), storage_alignment_override(0),
              declared_access(declared_access), is_mutable(is_mutable),
              decl(decl) {}
    };

    bool is_union;                    // True if union, false if struct
    bool is_packed = false;           // True if __attribute__((packed))
    bool is_transparent_union = false; // True if __attribute__((transparent_union))
    size_t requested_alignment = 0;   // Type-level __attribute__((aligned(N)))
    size_t pack_alignment = 0;        // Max alignment from #pragma pack, 0 = default
    std::shared_ptr<ClassTemplateSpecializationInfo> class_template_specialization = nullptr;

    // When we use this constructor, we will rebuild the fields so we don't copy them
    explicit ObjectType(ObjectType *prev): TagType(TypeKind::Object, prev->get_decl()) {
        is_union = prev->is_union;
        is_packed = prev->is_packed;
        is_transparent_union = prev->is_transparent_union;
        requested_alignment = prev->requested_alignment;
        pack_alignment = prev->pack_alignment;
        class_template_specialization = prev->class_template_specialization;
    }
    explicit ObjectType(std::string tag, bool isUnion = false, bool incomplete = false)
        : TagType(TypeKind::Object), is_union(isUnion) {
        (void)tag;
        (void)incomplete;
    }

    ObjectType(std::string tag, std::vector<Field> fields, bool isUnion = false)
        : TagType(TypeKind::Object), is_union(isUnion) {
        (void)tag;
        (void)fields;
    }

    bool equals(const CType &other) override {
        if (other.kind != TypeKind::Object) return false;
        const auto& otherRec = static_cast<const ObjectType&>(other);
        const TagDecl* lhs_decl = get_decl();
        const TagDecl* rhs_decl = otherRec.get_decl();
        if (lhs_decl && rhs_decl) {
            return lhs_decl == rhs_decl;
        }
        return this == &otherRec;
    }
    static bool classof(const CType *t) { return t->kind == TypeKind::Object; }

    bool isIncomplete() const override;
    int64_t getWidth() override;
    size_t getAlignment();
    const std::vector<Field>& semantic_fields() const;
    bool semantic_has_flexible_array_member() const;

    void set_class_template_specialization_info(
        const ClassTemplateDecl* primary_template,
        std::vector<TemplateArgument> arguments) {
        auto info = std::make_shared<ClassTemplateSpecializationInfo>();
        info->primary_template = primary_template;
        info->arguments = std::move(arguments);
        class_template_specialization = std::move(info);
    }

    bool is_class_template_specialization() const {
        return class_template_specialization != nullptr;
    }

    const ClassTemplateDecl* get_primary_class_template() const {
        return class_template_specialization
            ? class_template_specialization->primary_template
            : nullptr;
    }

    const std::vector<TemplateArgument>& get_template_specialization_arguments() const {
        static const std::vector<TemplateArgument> empty;
        return class_template_specialization
            ? class_template_specialization->arguments
            : empty;
    }

    // Find field by name, returns nullptr if not found
    const Field* findField(const std::string& name) const;

    // Check if struct contains any bitfield members
    bool has_bitfields() const;
    std::string to_string() const override;

    TagTypeKind get_tag_type_kind() const override { return TagTypeKind::Record; }
};

struct RecordSemanticState {
    enum class NestedTemplateKind : uint8_t {
        Alias,
        Class,
    };

    struct DefinitionData {
        bool has_user_declared_constructor = false;
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

    struct Base {
        std::string name;
        QualType type;
        RecordMemberAccess declared_access = RecordMemberAccess::Public;
        bool is_virtual = false;
        bool has_non_virtual_offset = false;
        size_t non_virtual_offset = 0;
        const CppBaseSpecifier* spec = nullptr;
        const ObjectDecl* record_decl = nullptr;
    };

    struct Method {
        std::string name;
        QualType type;
        RecordMemberAccess declared_access = RecordMemberAccess::Public;
        bool is_implicit = false;
        bool is_static = false;
        bool is_deleted = false;
        bool is_defaulted = false;
        bool is_constexpr = false;
        bool is_consteval = false;
        bool is_explicit = false;
        bool is_virtual = false;
        bool is_override = false;
        bool is_final = false;
        bool is_pure = false;
        bool is_conversion_function = false;
        QualType conversion_target_type;
        bool overrides_base_virtual = false;
        int32_t virtual_slot_index = -1;
        const CppMethodDecl* decl = nullptr;
        std::shared_ptr<Symbol> symbol = nullptr;
    };

    struct MethodTemplate {
        std::string name;
        RecordMemberAccess declared_access = RecordMemberAccess::Public;
        bool is_static = false;
        const FunctionTemplateDecl* decl = nullptr;
    };

    struct StaticDataMember {
        std::string name;
        QualType type;
        RecordMemberAccess declared_access = RecordMemberAccess::Public;
        const VariableDecl* decl = nullptr;
        std::shared_ptr<Symbol> symbol = nullptr;
    };

    struct NestedType {
        std::string name;
        QualType type;
        RecordMemberAccess declared_access = RecordMemberAccess::Public;
        const Decl* decl = nullptr;
        std::shared_ptr<Symbol> symbol = nullptr;
    };

    struct NestedTemplate {
        std::string name;
        RecordMemberAccess declared_access = RecordMemberAccess::Public;
        NestedTemplateKind kind = NestedTemplateKind::Alias;
        const TemplateDecl* decl = nullptr;
    };

    struct FriendFunction {
        std::string name;
        QualType type;
        const FriendDecl* decl = nullptr;
        const FuncDecl* function_decl = nullptr;
        const FunctionTemplateDecl* function_template = nullptr;
        std::shared_ptr<Symbol> symbol = nullptr;
    };

    struct FriendType {
        QualType type;
        const FriendDecl* decl = nullptr;
        const ClassTemplateDecl* class_template = nullptr;
    };

    struct Constructor {
        std::string name;
        QualType type;
        RecordMemberAccess declared_access = RecordMemberAccess::Public;
        bool is_implicit = false;
        bool is_explicit = false;
        bool is_deleted = false;
        bool is_defaulted = false;
        bool is_constexpr = false;
        bool is_consteval = false;
        const CppConstructorDecl* decl = nullptr;
        std::shared_ptr<Symbol> symbol = nullptr;
        const FunctionTemplateDecl* function_template = nullptr;
    };

    struct Destructor {
        std::string name;
        QualType type;
        RecordMemberAccess declared_access = RecordMemberAccess::Public;
        bool is_implicit = false;
        bool is_defaulted = false;
        bool is_deleted = false;
        bool is_constexpr = false;
        bool is_consteval = false;
        bool is_virtual = false;
        bool is_override = false;
        bool is_final = false;
        bool is_pure = false;
        bool overrides_base_virtual = false;
        int32_t virtual_slot_index = -1;
        const CppDestructorDecl* decl = nullptr;
        std::shared_ptr<Symbol> symbol = nullptr;
    };

    struct VirtualSlot {
        std::string key;
        std::string name;
        bool is_destructor = false;
        bool is_pure = false;
        bool is_final = false;
        std::shared_ptr<Symbol> final_symbol = nullptr;
    };

    struct VirtualBase {
        std::string name;
        QualType type;
        RecordMemberAccess declared_access = RecordMemberAccess::Public;
        const ObjectDecl* record_decl = nullptr;
        bool has_offset = false;
        size_t offset = 0;
    };

    struct EnumeratorMember {
        std::string name;
        RecordMemberAccess declared_access = RecordMemberAccess::Public;
        const EnumDecl* enum_decl = nullptr;
        const EnumConstantDecl* decl = nullptr;
        std::shared_ptr<Symbol> symbol = nullptr;
    };

    bool is_incomplete = true;
    bool is_template_pattern_provisional = false;
    bool is_final = false;
    bool is_polymorphic = false;
    bool is_abstract = false;
    bool has_virtual_destructor = false;
    DefinitionData definition_data;
    std::vector<Base> bases;
    std::vector<ObjectType::Field> fields;
    std::vector<Method> methods;
    std::vector<MethodTemplate> method_templates;
    std::vector<StaticDataMember> static_data_members;
    std::vector<NestedType> nested_types;
    std::vector<NestedTemplate> nested_templates;
    std::vector<FriendFunction> friend_functions;
    std::vector<FriendType> friend_types;
    std::vector<EnumeratorMember> enumerator_members;
    std::vector<Constructor> constructors;
    std::vector<Destructor> destructors;
    std::vector<VirtualSlot> virtual_slots;
    std::vector<VirtualBase> virtual_bases;
    size_t non_virtual_size_bits = 0;
    size_t non_virtual_alignment = 1;
    size_t size_bits = 0;
    size_t alignment = 1;
    bool has_flexible_array_member = false;
};

void record_semantics_cache_clear(ASTContext* ast_ctx);
void record_semantics_cache_set(ASTContext* ast_ctx,
                                const ObjectDecl* record_decl,
                                RecordSemanticState state);
void record_semantics_cache_set(const ObjectDecl* record_decl,
                                RecordSemanticState state);
void record_semantics_cache_erase(ASTContext* ast_ctx,
                                  const ObjectDecl* record_decl);
void record_semantics_cache_erase(const ObjectDecl* record_decl);
const RecordSemanticState* record_semantics_cache_lookup(
    const ObjectDecl* record_decl,
    const ASTContext* ast_ctx);
const RecordSemanticState* record_semantics_cache_lookup(
    const ObjectDecl* record_decl);
uint64_t record_semantics_cache_epoch(const ASTContext* ast_ctx);
QualType cpp_written_method_type(QualType method_type,
                                 const ASTContext* ast_ctx = nullptr);
std::string make_cpp_virtual_slot_key(const std::string& method_name,
                                      QualType method_type,
                                      const ASTContext* ast_ctx = nullptr);
std::optional<size_t> record_base_subobject_offset(
    const ObjectDecl* from_decl,
    const ObjectDecl* to_decl,
    const ASTContext* ast_ctx = nullptr);
size_t count_record_base_subobjects(const ObjectDecl* derived_decl,
                                    const ObjectDecl* target_base_decl,
                                    bool require_public_path,
                                    const ASTContext* ast_ctx = nullptr);
bool has_unambiguous_record_base_path(const ObjectDecl* derived_decl,
                                      const ObjectDecl* target_base_decl,
                                      bool require_public_path,
                                      const ASTContext* ast_ctx = nullptr);
struct RecordBasePathSummary {
    size_t public_nonvirtual_paths = 0;
    size_t nonpublic_nonvirtual_paths = 0;
    size_t public_nonvirtual_offset = 0;
    bool has_virtual_path = false;
};
RecordBasePathSummary summarize_record_base_paths(
    const ObjectDecl* derived_decl,
    const ObjectDecl* target_base_decl,
    const ASTContext* ast_ctx = nullptr);
RecordSemanticState compute_record_semantics(std::vector<ObjectType::Field> fields,
                                             bool is_union,
                                             bool is_packed,
                                             size_t requested_alignment,
                                             size_t pack_alignment,
                                             bool is_incomplete = false,
                                             const AbiPolicy* abi_policy = nullptr);
size_t object_field_storage_size_bytes(const ObjectType::Field& field,
                                       const AbiPolicy* abi_policy = nullptr);
size_t object_field_storage_alignment(const ObjectType::Field& field);
std::vector<ObjectType::Field> get_record_fields_for_type_matching(
    const ObjectType* record_type);
struct EnumSemanticState {
    struct Enumerator {
        std::string name;
        const EnumConstantDecl* decl = nullptr;
        std::shared_ptr<Symbol> symbol = nullptr;
        int64_t value = 0;
    };

    bool is_incomplete = true;
    bool is_scoped = false;
    bool has_negative_values = false;
    std::shared_ptr<CType> underlying_type;
    std::vector<Enumerator> enumerators;
};
void enum_semantics_cache_clear(ASTContext* ast_ctx);
void enum_semantics_cache_set(ASTContext* ast_ctx,
                              const EnumDecl* enum_decl,
                              EnumSemanticState state);
void enum_semantics_cache_set(const EnumDecl* enum_decl,
                              EnumSemanticState state);
void enum_semantics_cache_erase(ASTContext* ast_ctx, const EnumDecl* enum_decl);
void enum_semantics_cache_erase(const EnumDecl* enum_decl);
bool enum_semantics_cache_lookup(const EnumDecl* enum_decl,
                                 EnumSemanticState& state_out,
                                 const ASTContext* ast_ctx);
bool enum_semantics_cache_lookup(const EnumDecl* enum_decl,
                                 EnumSemanticState& state_out);

struct EnumType : TagType {
    explicit EnumType(std::string tag, bool incomplete = false)
        : TagType(TypeKind::Enum) {
        (void)tag;
        (void)incomplete;
    }

    bool equals(const CType &other) override {
        if (other.kind != TypeKind::Enum) return false;
        const auto& otherEnum = static_cast<const EnumType&>(other);
        const TagDecl* lhs_decl = get_decl();
        const TagDecl* rhs_decl = otherEnum.get_decl();
        if (lhs_decl && rhs_decl) {
            return lhs_decl == rhs_decl;
        }
        return this == &otherEnum;
    }
    static bool classof(const CType *t) { return t->kind == TypeKind::Enum; }

    bool isIncomplete() const override;
    bool isScoped() const;

    bool isArithmetic() const override { return true; }
    bool isInteger() const override { return true; }

    // GCC treats enums as unsigned when all values are non-negative
    std::shared_ptr<CType> semantic_underlying_type() const;
    bool isUnsigned() const override;
    int64_t getWidth() override;
    std::string to_string() const override;

    TagTypeKind get_tag_type_kind() const override { return TagTypeKind::Enum; }
};
std::shared_ptr<CType> convert_arr_to_pointer(std::shared_ptr<ArrayType> arr_type);
struct TypeContext {
    std::unordered_map<BuiltinTypes, std::shared_ptr<BuiltinType>> builtins;
    std::unordered_map<BuiltinTypes, std::shared_ptr<ComplexType>> complex_types;
    std::shared_ptr<CppTypeInfoType> cpp_type_info_type;
    std::shared_ptr<TargetInfo> target;

    TypeContext();
    explicit TypeContext(std::shared_ptr<TargetInfo> ti);

    std::shared_ptr<BuiltinType> get_builtin(BuiltinTypes typ) {
        if (!builtins.contains(typ)) {
            return nullptr;
        }
        return builtins[typ];
    }

    std::shared_ptr<ComplexType> get_complex(BuiltinTypes real_kind) {
        auto it = complex_types.find(real_kind);
        if (it != complex_types.end()) return it->second;
        auto real_type = get_builtin(real_kind);
        if (!real_type) return nullptr;
        auto ct = std::make_shared<ComplexType>(real_type);
        complex_types[real_kind] = ct;
        return ct;
    }

    std::shared_ptr<CppTypeInfoType> get_cpp_type_info() {
        return cpp_type_info_type;
    }
};
// Narrow helper: remove typedef sugar only.
QualType desugar_typedefs(QualType type);
std::shared_ptr<CType> desugar_typedefs(const std::shared_ptr<CType>& type);
std::shared_ptr<TemplateSpecializationType>
get_class_template_placeholder_type(QualType type);
bool is_class_template_placeholder_type(QualType type);

// General sugar-removal hook. Today this forwards to typedef desugaring, but
// it is intended to grow as C++ sugar forms are introduced.
QualType desugar_type(QualType type);
QualType desugar_type(QualType type, const ASTContext* ast_ctx);
std::shared_ptr<CType> desugar_type(const std::shared_ptr<CType>& type);
std::shared_ptr<CType> desugar_type(const std::shared_ptr<CType>& type,
                                    const ASTContext* ast_ctx);

TypeKind canonical_type_kind(QualType type);
TypeKind canonical_type_kind(QualType type, const ASTContext* ast_ctx);
TypeKind canonical_type_kind(const std::shared_ptr<CType>& type);
TypeKind canonical_type_kind(const std::shared_ptr<CType>& type,
                             const ASTContext* ast_ctx);

bool is_reference_type(QualType type);
bool is_reference_type(QualType type, const ASTContext* ast_ctx);
bool is_reference_type(const std::shared_ptr<CType>& type);
bool is_reference_type(const std::shared_ptr<CType>& type,
                       const ASTContext* ast_ctx);
QualType remove_reference(QualType type);
QualType remove_reference(QualType type, const ASTContext* ast_ctx);
std::shared_ptr<CType> remove_reference(const std::shared_ptr<CType>& type);
std::shared_ptr<CType> remove_reference(const std::shared_ptr<CType>& type,
                                        const ASTContext* ast_ctx);
QualType make_reference_type(QualType referred, ReferenceKind kind);
std::shared_ptr<CType> make_reference_type(
    const std::shared_ptr<CType>& referred,
    ReferenceKind kind);

bool lookup_builtin_type_transform_kind(
    std::string_view name,
    BuiltinTypeTransformKind& out);
bool is_builtin_type_pack_element_name(std::string_view name);
QualType apply_builtin_type_transform(
    BuiltinTypeTransformKind kind,
    QualType operand_type);
QualType apply_builtin_type_transform(
    BuiltinTypeTransformKind kind,
    QualType operand_type,
    const ASTContext* ast_ctx);
QualType apply_builtin_type_pack_element(
    const std::vector<TemplateArgument>& arguments);
QualType apply_builtin_type_pack_element(
    const std::vector<TemplateArgument>& arguments,
    const ASTContext* ast_ctx);

bool type_contains_vla(const std::shared_ptr<CType>& type);
// inline TypeContext global_type_context;
#endif //ABURI_TYPES_H
