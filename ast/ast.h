#ifndef ABURI_AST_H
#define ABURI_AST_H

#include "../constexpr/const_value.h"

// ============================================================================
// AST Node Ownership Conventions
// ============================================================================
//
// Pointer types in this header follow these conventions:
//
//   unique_ptr<T>          Owning.  The enclosing node is the sole owner and
//                          destroys the child when it is itself destroyed.
//                          Most child statements, expressions, and declarations
//                          use this pattern.
//
//   shared_ptr<T>          Shared ownership.  Used when multiple AST nodes or
//                          the symbol table need to reference the same object
//                          (e.g., shared_ptr<Symbol> for symbols that are
//                          referenced by both declarations and expressions,
//                          shared_ptr<CType>/QualType for types that can be
//                          aliased across the AST).
//
//   raw pointer (T*)       Non-owning reference ("borrowed").  The pointee is
//                          owned by another node, a parent scope, or the
//                          ASTContext side tables.  Raw pointers MUST NOT be
//                          deleted by the node that holds them.  Common uses:
//                          back-references to parent declarations, pointers
//                          into scope/decl-context trees, template parameter
//                          declarations that outlive individual references.
//
// external_semantic_owner_id:
//   A mutable uint32_t present on TemplateParameterDecl, FuncDecl, FieldDecl,
//   and Symbol.  It records the registry_id() of the owning
//   CollectSemanticStore, reached through the owning ASTContext.  The store
//   owns semantic side-table entries such as qualifier prefixes, owner record
//   types, template specialization info, and record/enum semantic caches.
//   A value of 0 means "no external semantic owner"; side-table accessors must
//   then rely on an explicit active ASTContext or return no data.  The field
//   is mutable because semantic store bookkeeping may update it through const
//   AST-facing APIs.
// ============================================================================

#include <string>
#include <vector>
#include <memory>
#include <unordered_set>
#include <cstdint>
#include <string_view>
#include "symbols.h"
#include "types.h"
#include <map>
#include <optional>
#include "source_mgnt.h"
#include "attributes.h"
#include "builtin_registry.h"
#include "helpers/casting.h"

class ASTContext;
class Scope;
class DeclContext;
ASTContext* get_side_table_ast_context_for(const ObjectDecl* decl);
ASTContext* get_side_table_ast_context_for(const EnumDecl* decl);
struct FuncDecl;
struct FieldDecl;
struct ObjectDecl;
struct CppRecordDecl;
struct TemplateDecl;
struct ConceptDecl;
enum class UnaryOpTypes : uint8_t;

enum class IfStatementKind : uint8_t {
    Runtime,
    Constexpr,
};

// Discriminant for Stmt hierarchy (includes Expr via ValueStmt)
enum class StmtKind : uint8_t {
    // --- Pure Stmt nodes ---
    CompoundStmt,
    Decl2Stmt,
    ReturnStmt,
    CppTryStmt,
    IfStmt,
    CaseStmt,
    DefaultStmt,
    LabeledStmt,
    GoToStmt,
    ComputedGotoStmt,
    SwitchStmt,
    WhileStmt,
    DoWhileStmt,
    ForStmt,
    CppRangeForStmt,
    ContinueStmt,
    BreakStmt,
    EmptyStmt,
    ErrorStmt,
    AsmStmt,

    // --- Expr nodes (Expr : ValueStmt : Stmt) ---
    FirstExpr,
    IntegerLiteral = FirstExpr,
    FloatingLiteral,
    CharacterLiteral,
    StringLiteral,
    PredefinedExpr,
    CppThisExpr,
    VarRef,
    QualifiedVarRef,
    UnresolvedLookupExpr,
    LabelAddressExpr,
    FuncCall,
    DependentCallExpr,
    DependentArraySubscriptExpr,
    DependentUnaryExpr,
    DependentBinaryExpr,
    DependentMemberPointerAccessExpr,
    PackExpansionExpr,
    FoldExpr,
    CppMemberCallExpr,
    CppConstructExpr,
    CppValueInitExpr,
    CppFunctionStyleCastExpr,
    CppImmediateInvocationExpr,
    CondExpr,
    UnaryOperation,
    BinaryOperation,
    CppBuiltinThreeWayCompareExpr,
    CompoundAssignOperation,
    ImplicitCast,
    ExplicitCast,
    ArraySubscriptExpr,
    MemberExpr,
    UnresolvedMemberExpr,
    MemberPointerLiteralExpr,
    MemberPointerAccessExpr,
    InitListExpr,
    CompoundLiteralExpr,
    SizeOfExpr,
    SizeOfPackExpr,
    AlignOfExpr,
    CppNoexceptExpr,
    OffsetOfExpr,
    GenericExpr,
    StmtExpr,
    VaArgExpr,
    VaStartExpr,
    VaEndExpr,
    VaCopyExpr,
    BuiltinCallExpr,
    CppTypeIdExpr,
    CppDynamicCastExpr,
    CppThrowExpr,
    CppNewExpr,
    CppDeleteExpr,
    CppPseudoDestructorExpr,
    BlockByrefAccessExpr,
    BlockExpr,
    CppLambdaExpr,
    ConceptSpecializationExpr,
    RequiresExpr,
    ErrorExpr,
    LastExpr = ErrorExpr,
};

// Discriminant for Decl hierarchy
enum class DeclKind : uint8_t {
    NopDecl,
    CppUsingDeclarationDecl,
    TypedefDecl,
    TemplateTypeParmDecl,
    TemplateNonTypeParmDecl,
    TemplateTemplateParmDecl,
    TranslationUnit,
    NamespaceDecl,
    AliasTemplateDecl,
    FunctionTemplateDecl,
    VariableTemplateDecl,
    ClassTemplateDecl,
    CppDeductionGuideDecl,
    ConceptDecl,
    VariableTemplatePartialSpecializationDecl,
    ClassTemplatePartialSpecializationDecl,
    TemplateExplicitSpecializationDecl,
    FuncDecl,
    CppMethodDecl,
    CppConstructorDecl,
    CppDestructorDecl,
    FriendDecl,
    VariableDecl,
    ParamDecl,
    FieldDecl,
    ObjectDecl,
    CppRecordDecl,
    CppAccessSpecDecl,
    EnumDecl,
    EnumConstantDecl,
    FileScopeAsmDecl,
    StaticAssertDecl,
    ErrorDecl,
};

enum class TagDeclKind : uint8_t {
    Record,
    Enum,
};

enum class CppRecordKind : uint8_t {
    Class,
    Struct,
    Union,
};

enum class CppAccessSpecifier : uint8_t {
    None,
    Public,
    Protected,
    Private,
};

enum class CppFriendKind : uint8_t {
    Function,
    Type,
    Unknown,
};

struct Stmt {
    SrcLoc location;
    uint32_t node_id = 0;
    virtual ~Stmt() = default;

    StmtKind get_kind() const { return stmt_kind_; }

protected:
    Stmt(StmtKind k, SrcLoc loc = SrcLoc()) : stmt_kind_(k), location(loc) {}

private:
    StmtKind stmt_kind_;
};
struct Decl {
    SrcLoc location;
    uint32_t node_id = 0;
    virtual ~Decl() = default;

    DeclKind get_kind() const { return decl_kind_; }

protected:
    Decl(DeclKind k, SrcLoc loc = SrcLoc()) : decl_kind_(k), location(loc) {}

private:
    DeclKind decl_kind_;
};

// Clang-style scaffolding: tag declarations (record/enum) share a base class.
// PR1 keeps existing ObjectDecl/EnumDecl payload ownership unchanged; later
// migration steps will move canonical semantic ownership to TagDecl-based nodes.
struct TagDecl : Decl {
    mutable uint32_t external_semantic_owner_id = 0; // Side-table/cache ownership

    TagDeclKind get_tag_decl_kind() const {
        return get_kind() == DeclKind::EnumDecl
            ? TagDeclKind::Enum
            : TagDeclKind::Record;
    }

    bool is_record_decl() const { return get_kind() == DeclKind::ObjectDecl; }
    bool is_enum_decl() const { return get_kind() == DeclKind::EnumDecl; }

    virtual bool is_complete_definition() const = 0;
    virtual const std::string& get_tag_name() const = 0;

    const std::shared_ptr<CType>& get_tag_type() const { return tag_type_; }
    void set_tag_type(std::shared_ptr<CType> tag_type) { tag_type_ = std::move(tag_type); }

    static bool classof(const Decl *d) {
        return d->get_kind() == DeclKind::ObjectDecl ||
               d->get_kind() == DeclKind::EnumDecl;
    }

protected:
    TagDecl(DeclKind k, SrcLoc loc = SrcLoc()) : Decl(k, loc) {}

private:
    std::shared_ptr<CType> tag_type_;
};
// Use this when we want to "remove in place" a AST node
// Location can be 0 or represent the place of the AST node relaced by the NopDecl
struct NopDecl: Decl {
    NopDecl(SrcLoc loc = SrcLoc()) : Decl(DeclKind::NopDecl, loc) {}
    static bool classof(const Decl *d) { return d->get_kind() == DeclKind::NopDecl; }
};

enum class CppUsingImportNamespace : uint8_t {
    Ordinary,
    Tag
};

struct CppUsingDeclarationDecl: Decl {
    struct ImportedSymbol {
        std::string name;
        std::shared_ptr<Symbol> symbol;
    };

    struct ImportedTemplate {
        std::string name;
        const Decl* decl = nullptr;
        CppUsingImportNamespace lookup_namespace =
            CppUsingImportNamespace::Ordinary;
    };

    struct ImportedTag {
        std::string name;
        TagDecl* decl = nullptr;
    };

    struct ReplayTarget {
        std::string name;
        const DeclContext* target_context = nullptr;
        bool import_ordinary = false;
        bool import_tag = false;
        std::vector<ImportedSymbol> ordinary_symbols;
        std::vector<ImportedTemplate> template_decls;
        std::vector<ImportedTag> tag_decls;
    };

    std::vector<ImportedSymbol> ordinary_symbols;
    std::vector<ImportedTemplate> template_decls;
    std::vector<ImportedTag> tag_decls;
    std::vector<ReplayTarget> replay_targets;

    CppUsingDeclarationDecl(SrcLoc loc = SrcLoc())
        : Decl(DeclKind::CppUsingDeclarationDecl, loc) {}

    static bool classof(const Decl *d) {
        return d->get_kind() == DeclKind::CppUsingDeclarationDecl;
    }
};

struct TypedefDecl: Decl {
    std::string name;
    // Spelled typedef type (may preserve TypedefType sugar).
    QualType type;
    // Canonical underlying type with typedef sugar removed.
    QualType underlying;
    std::shared_ptr<Symbol> sym;

    TypedefDecl(std::string name, QualType type, std::shared_ptr<Symbol> sym, SrcLoc loc = SrcLoc())
        : Decl(DeclKind::TypedefDecl, loc),
          name(std::move(name)),
          type(std::move(type)),
          underlying(desugar_type(this->type)),
          sym(std::move(sym)) {}

    QualType alias_type() const { return type; }
    QualType underlying_type() const { return underlying; }

    static bool classof(const Decl *d) { return d->get_kind() == DeclKind::TypedefDecl; }
};
// a ValueStmt could return a value and/or have an associated type
struct ValueStmt: Stmt {
    using Stmt::Stmt;
    virtual ~ValueStmt() = default;
};
struct Expr: ValueStmt {
    using ValueStmt::ValueStmt;
    // std::shared_ptr<CType> type = nullptr;
    virtual ~Expr() = default;
    virtual bool isLValue() { return false; }
    // Don't try to cast or wrap this node automatically (e.x: implicit casting)
    virtual bool letPassthrough() { return false; }
    virtual QualType get_type() {return nullptr; }

    static bool classof(const Stmt *s) {
        return s->get_kind() >= StmtKind::FirstExpr && s->get_kind() <= StmtKind::LastExpr;
    }
};

struct CppExplicitSpecifier {
    bool is_present = false;
    bool is_conditional = false;
    bool is_dependent = false;
    bool effective_value = false;
    std::shared_ptr<Expr> condition = nullptr;
    SrcLoc location;
};

struct CompoundStmt: Stmt {
    explicit CompoundStmt(std::vector<std::unique_ptr<Stmt>> statements, SrcLoc loc = SrcLoc())
    : Stmt(StmtKind::CompoundStmt, loc), statements(std::move(statements)), scope(nullptr) {}
    CompoundStmt(std::vector<std::unique_ptr<Stmt>> statements, std::shared_ptr<Scope> scope,
        SrcLoc loc = SrcLoc())
    : Stmt(StmtKind::CompoundStmt, loc), statements(std::move(statements)), scope(scope) {};

    std::vector<std::unique_ptr<Stmt>> statements;
    std::shared_ptr<Scope> scope;

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::CompoundStmt; }
};
enum class CppLambdaCaptureDefault : uint8_t {
    None,
    ByCopy,
    ByReference,
};

struct CppThisContext {
    bool is_member_function = false;
    bool is_static_member_function = false;
    QualType this_type = nullptr;
    QualType friend_access_type = nullptr;
};

struct CppLambdaCapture {
    std::string name;
    std::shared_ptr<Symbol> symbol;
    std::shared_ptr<Expr> initializer;
    bool by_reference = false;
    bool captures_this = false;
    bool is_init_capture = false;
    SrcLoc location;
};

struct LambdaClosureInfo {
    CppLambdaCaptureDefault default_capture = CppLambdaCaptureDefault::None;
    std::vector<CppLambdaCapture> captures;
};

struct LambdaSemanticInfo {
    std::unique_ptr<ObjectDecl> closure_semantic_decl;   // Owned
    std::unique_ptr<CppRecordDecl> closure_record_decl;  // Owned
    FuncDecl* call_operator_decl = nullptr;              // Borrowed from closure_semantic_decl members
    std::shared_ptr<Symbol> call_operator_symbol;        // Shared: referenced by both the decl and call sites
    TemplateDecl* call_operator_template = nullptr;      // Borrowed from closure_semantic_decl members
    std::unique_ptr<FuncDecl> function_pointer_invoker_decl; // Owned
    CppThisContext lexical_this_context;
    std::vector<FieldDecl*> capture_fields;
    FieldDecl* this_capture_field = nullptr;
    std::vector<std::unique_ptr<Expr>> capture_initializers;
    std::unique_ptr<Expr> closure_initializer;

    QualType closure_type() const;
    ObjectDecl* semantic_owner();
    const ObjectDecl* semantic_owner() const;
    CppRecordDecl* closure_record();
    const CppRecordDecl* closure_record() const;
    const std::string& closure_name() const;
};

std::string make_lambda_closure_internal_name(SrcLoc loc);
LambdaSemanticInfo make_lambda_semantic_info(ASTContext& ctx, SrcLoc loc);

enum class BlockCaptureKind : uint8_t {
    ConstCopy,
    ByRef,
};

struct BlockCapture {
    std::string name;
    std::shared_ptr<Symbol> symbol;
    FieldDecl* field = nullptr;
    QualType capture_type;
    BlockCaptureKind kind = BlockCaptureKind::ConstCopy;
    SrcLoc location;
};

struct BlockSemanticInfo {
    std::unique_ptr<ObjectDecl> literal_semantic_decl; // Owned
    std::unique_ptr<FuncDecl> invoke_decl;             // Owned
    std::vector<BlockCapture> captures;

    QualType literal_type() const;
    ObjectDecl* literal_record();
    const ObjectDecl* literal_record() const;
    const std::string& literal_name() const;
};

std::string make_block_internal_name(SrcLoc loc);
BlockSemanticInfo make_block_semantic_info(ASTContext& ctx, SrcLoc loc);

struct TranslationUnit: Decl {
    std::vector<std::unique_ptr<Decl>> declarations;
    explicit TranslationUnit(std::vector<std::unique_ptr<Decl>> declarations, SrcLoc loc = SrcLoc())
    : Decl(DeclKind::TranslationUnit, loc), declarations(std::move(declarations)) {};

    static bool classof(const Decl *d) { return d->get_kind() == DeclKind::TranslationUnit; }
};

struct NamespaceDecl : Decl {
    std::string name;
    std::vector<Decl*> members;
    DeclContext* semantic_context = nullptr;
    const NamespaceDecl* canonical_decl = nullptr;
    const NamespaceDecl* previous_decl = nullptr;
    bool is_anonymous = false;
    bool is_inline = false;

    NamespaceDecl(std::string name,
                  std::vector<Decl*> members = {},
                  DeclContext* semantic_context = nullptr,
                  bool is_anonymous = false,
                  bool is_inline = false,
                  SrcLoc loc = SrcLoc())
        : Decl(DeclKind::NamespaceDecl, loc),
          name(std::move(name)),
          members(std::move(members)),
          semantic_context(semantic_context),
          is_anonymous(is_anonymous),
          is_inline(is_inline) {}

    const NamespaceDecl* get_canonical_decl() const {
        return canonical_decl ? canonical_decl : this;
    }

    bool is_canonical_decl() const {
        return get_canonical_decl() == this;
    }

    static bool classof(const Decl *d) {
        return d->get_kind() == DeclKind::NamespaceDecl;
    }
};

struct TemplateParameterDecl : Decl {
    std::string name;
    uint32_t depth = 0;
    uint32_t index = 0;
    bool is_parameter_pack = false;
    mutable uint32_t external_semantic_owner_id = 0; // See ownership conventions at top of file
    mutable std::optional<TemplateArgument> default_argument;

    const std::string& get_name() const { return name; }

    static bool classof(const Decl* d) {
        return d->get_kind() == DeclKind::TemplateTypeParmDecl ||
               d->get_kind() == DeclKind::TemplateNonTypeParmDecl ||
               d->get_kind() == DeclKind::TemplateTemplateParmDecl;
    }

protected:
    TemplateParameterDecl(DeclKind kind,
                          std::string name,
                          uint32_t depth,
                          uint32_t index,
                          bool is_parameter_pack = false,
                          SrcLoc loc = SrcLoc())
        : Decl(kind, loc),
          name(std::move(name)),
          depth(depth),
          index(index),
          is_parameter_pack(is_parameter_pack) {}
};

enum class ConstraintRequirementKind : uint8_t {
    Simple,
    Type,
    Compound,
    Nested,
};

struct CppTypeConstraint {
    const ConceptDecl* concept_decl = nullptr;
    std::string concept_name;
    std::vector<TemplateArgument> template_arguments;
    SrcLoc location;
};

struct ConstraintRequirement {
    ConstraintRequirementKind kind = ConstraintRequirementKind::Simple;
    std::unique_ptr<Expr> expr;
    QualType type_requirement = nullptr;
    uint8_t is_noexcept : 1;
    std::optional<CppTypeConstraint> return_type_constraint;
    SrcLoc location;

    ConstraintRequirement()
        : is_noexcept(false) {}
};

struct TemplateTypeParmDecl : TemplateParameterDecl {
    std::shared_ptr<TemplateTypeParmType> type;
    std::unique_ptr<Expr> type_constraint;

    TemplateTypeParmDecl(std::string name,
                         uint32_t depth,
                         uint32_t index,
                         std::shared_ptr<TemplateTypeParmType> type,
                         bool is_parameter_pack = false,
                         SrcLoc loc = SrcLoc())
        : TemplateParameterDecl(
              DeclKind::TemplateTypeParmDecl,
              std::move(name),
              depth,
              index,
              is_parameter_pack,
              loc),
          type(std::move(type)) {}

    static bool classof(const Decl* d) {
        return d->get_kind() == DeclKind::TemplateTypeParmDecl;
    }
};

struct TemplateNonTypeParmDecl : TemplateParameterDecl {
    QualType type;
    std::shared_ptr<Symbol> sym;

    TemplateNonTypeParmDecl(std::string name,
                            uint32_t depth,
                            uint32_t index,
                            QualType type,
                            std::shared_ptr<Symbol> sym = nullptr,
                            bool is_parameter_pack = false,
                            SrcLoc loc = SrcLoc())
        : TemplateParameterDecl(
              DeclKind::TemplateNonTypeParmDecl,
              std::move(name),
              depth,
              index,
              is_parameter_pack,
              loc),
          type(std::move(type)),
          sym(std::move(sym)) {
        if (this->sym) {
            this->sym->template_parameter_decl = this;
        }
    }

    static bool classof(const Decl* d) {
        return d->get_kind() == DeclKind::TemplateNonTypeParmDecl;
    }
};

struct TemplateTemplateParmDecl : TemplateParameterDecl {
    TemplateParameterList parameters;
    bool uses_typename_keyword = false;

    TemplateTemplateParmDecl(TemplateParameterList parameters,
                             std::string name,
                             uint32_t depth,
                             uint32_t index,
                             bool uses_typename_keyword = false,
                             bool is_parameter_pack = false,
                             SrcLoc loc = SrcLoc())
        : TemplateParameterDecl(
              DeclKind::TemplateTemplateParmDecl,
              std::move(name),
              depth,
              index,
              is_parameter_pack,
              loc),
          parameters(std::move(parameters)),
          uses_typename_keyword(uses_typename_keyword) {}

    static bool classof(const Decl* d) {
        return d->get_kind() == DeclKind::TemplateTemplateParmDecl;
    }
};

struct FuncDecl: Decl {
    FuncDecl(const std::string name, const std::shared_ptr<CType> type, std::vector<std::unique_ptr<Decl>> parameters,
             std::unique_ptr<Stmt> body, std::unordered_set<std::string> stmt_labels = {},
             StorageClass storage_class = StorageClass::NONE, bool is_inline = false, SrcLoc loc = SrcLoc())
             : FuncDecl(DeclKind::FuncDecl, name, type, std::move(parameters), std::move(body),
                        std::move(stmt_labels), storage_class, is_inline, loc) {}
    FuncDecl(SrcLoc loc = SrcLoc()): FuncDecl(DeclKind::FuncDecl, loc) {}

    std::string name;
    std::shared_ptr<CType> type;
    std::unordered_set<std::string> stmt_labels;
    std::vector<std::unique_ptr<Decl>> parameters;
    std::unique_ptr<Stmt> body;
    std::vector<TemplateArgument> explicit_specialization_arguments;
    std::shared_ptr<Scope> scope;
    const std::string* asm_label;
    StorageClass storage_class;
    std::unique_ptr<Expr> trailing_requires_clause;
    bool has_explicit_specialization_argument_list = false;
    uint8_t is_inline : 1;
    uint8_t has_prior_non_inline_declaration : 1;
    // todo: combine constexpr/consteval fields?
    uint8_t is_constexpr : 1;
    uint8_t is_consteval : 1;
    uint8_t is_deleted : 1;
    uint8_t is_defaulted : 1;
    uint8_t is_defaulted_on_first_declaration : 1;
    uint8_t language_linkage : 2;
    mutable uint32_t external_semantic_owner_id = 0; // See ownership conventions at top of file

    void set_asm_label(std::optional<std::string> label) {
        if (!label.has_value()) {
            asm_label = nullptr;
            return;
        }
        asm_label = intern_asm_label(std::move(*label));
    }
    void set_asm_label(const std::string& label) {
        asm_label = intern_asm_label(std::string(label));
    }
    void clear_asm_label() { asm_label = nullptr; }
    LanguageLinkage get_language_linkage() const {
        return static_cast<LanguageLinkage>(language_linkage);
    }
    void set_language_linkage(LanguageLinkage linkage_kind) {
        language_linkage = static_cast<uint8_t>(linkage_kind);
    }

    static bool classof(const Decl *d) {
        return d->get_kind() == DeclKind::FuncDecl ||
               d->get_kind() == DeclKind::CppMethodDecl ||
               d->get_kind() == DeclKind::CppConstructorDecl ||
               d->get_kind() == DeclKind::CppDestructorDecl;
    }

protected:
    FuncDecl(DeclKind kind, const std::string name, const std::shared_ptr<CType> type,
             std::vector<std::unique_ptr<Decl>> parameters, std::unique_ptr<Stmt> body,
             std::unordered_set<std::string> stmt_labels = {},
             StorageClass storage_class = StorageClass::NONE, bool is_inline = false, SrcLoc loc = SrcLoc())
             : Decl(kind, loc), name(name), type(nullptr), stmt_labels(std::move(stmt_labels)),
               parameters(std::move(parameters)), body(std::move(body)), scope(nullptr),
               asm_label(nullptr),
               storage_class(storage_class), is_inline(is_inline),
               has_prior_non_inline_declaration(false), is_constexpr(false),
               is_consteval(false),
               is_deleted(false), is_defaulted(false),
               is_defaulted_on_first_declaration(false),
               language_linkage(static_cast<uint8_t>(LanguageLinkage::None)) {}
    FuncDecl(DeclKind kind, SrcLoc loc = SrcLoc()): Decl(kind, loc), type(nullptr), body(nullptr), scope(nullptr),
                                                     asm_label(nullptr),
                                                     storage_class(StorageClass::NONE), is_inline(false),
                                                     has_prior_non_inline_declaration(false),
                                                     is_constexpr(false),
                                                     is_consteval(false),
                                                     is_deleted(false),
                                                     is_defaulted(false),
                                                     is_defaulted_on_first_declaration(false),
                                                     language_linkage(static_cast<uint8_t>(LanguageLinkage::None)) {}

private:
    static const std::string* intern_asm_label(std::string label) {
        static std::unordered_set<std::string> pool;
        auto [it, _] = pool.emplace(std::move(label));
        return &(*it);
    }
};
struct CppMethodDecl : FuncDecl {
    uint8_t has_deferred_inline_body_tokens : 1;
    uint8_t is_virtual : 1;
    uint8_t is_override : 1;
    uint8_t is_final : 1;
    uint8_t is_pure : 1;
    uint8_t is_conversion_function : 1;
    uint8_t is_explicit_conversion : 1;
    size_t deferred_inline_body_begin_token_idx;
    size_t deferred_inline_body_end_token_idx;
    QualType conversion_target_type;
    CppExplicitSpecifier explicit_specifier;

    CppMethodDecl(const std::string name, const std::shared_ptr<CType> type,
                  std::vector<std::unique_ptr<Decl>> parameters, std::unique_ptr<Stmt> body,
                  std::unordered_set<std::string> stmt_labels = {},
                  StorageClass storage_class = StorageClass::NONE, bool is_inline = false,
                  SrcLoc loc = SrcLoc())
        : FuncDecl(DeclKind::CppMethodDecl, name, type, std::move(parameters), std::move(body),
                   std::move(stmt_labels), storage_class, is_inline, loc),
          has_deferred_inline_body_tokens(false),
          is_virtual(false),
          is_override(false),
          is_final(false),
          is_pure(false),
          is_conversion_function(false),
          is_explicit_conversion(false),
          deferred_inline_body_begin_token_idx(0),
          deferred_inline_body_end_token_idx(0),
          conversion_target_type(nullptr) {}
    explicit CppMethodDecl(SrcLoc loc = SrcLoc())
        : FuncDecl(DeclKind::CppMethodDecl, loc),
          has_deferred_inline_body_tokens(false),
          is_virtual(false),
          is_override(false),
          is_final(false),
          is_pure(false),
          is_conversion_function(false),
          is_explicit_conversion(false),
          deferred_inline_body_begin_token_idx(0),
          deferred_inline_body_end_token_idx(0),
          conversion_target_type(nullptr) {}

    bool has_deferred_inline_body() const {
        return has_deferred_inline_body_tokens != 0 &&
            deferred_inline_body_end_token_idx > deferred_inline_body_begin_token_idx;
    }

    void set_deferred_inline_body_token_range(size_t begin_token_idx,
                                              size_t end_token_idx) {
        has_deferred_inline_body_tokens = 1;
        deferred_inline_body_begin_token_idx = begin_token_idx;
        deferred_inline_body_end_token_idx = end_token_idx;
    }

    void clear_deferred_inline_body_token_range() {
        has_deferred_inline_body_tokens = 0;
        deferred_inline_body_begin_token_idx = 0;
        deferred_inline_body_end_token_idx = 0;
    }

    static bool classof(const Decl *d) {
        return d->get_kind() == DeclKind::CppMethodDecl;
    }
};

struct CppCtorInitializer {
    std::string member_name;
    bool is_base_initializer = false;
    bool is_delegating_initializer = false;
    bool is_list_init = false;
    size_t deferred_init_begin_token_idx = 0;
    size_t deferred_init_end_token_idx = 0;
    std::unique_ptr<Expr> member_expr = nullptr;
    std::unique_ptr<Expr> init_expr = nullptr;
    SrcLoc location;
};

struct CppConstructorDecl : FuncDecl {
    uint8_t is_explicit : 1;
    uint8_t has_deferred_inline_body_tokens : 1;
    size_t deferred_inline_body_begin_token_idx;
    size_t deferred_inline_body_end_token_idx;
    CppExplicitSpecifier explicit_specifier;
    std::vector<CppCtorInitializer> ctor_initializers;

    CppConstructorDecl(const std::string name, const std::shared_ptr<CType> type,
                       std::vector<std::unique_ptr<Decl>> parameters, std::unique_ptr<Stmt> body,
                       std::unordered_set<std::string> stmt_labels = {},
                       StorageClass storage_class = StorageClass::NONE, bool is_inline = false,
                       bool is_explicit = false, SrcLoc loc = SrcLoc())
        : FuncDecl(DeclKind::CppConstructorDecl, name, type, std::move(parameters),
                   std::move(body), std::move(stmt_labels), storage_class, is_inline, loc),
          is_explicit(is_explicit),
          has_deferred_inline_body_tokens(false),
          deferred_inline_body_begin_token_idx(0),
          deferred_inline_body_end_token_idx(0) {}

    explicit CppConstructorDecl(SrcLoc loc = SrcLoc())
        : FuncDecl(DeclKind::CppConstructorDecl, loc),
          is_explicit(false),
          has_deferred_inline_body_tokens(false),
          deferred_inline_body_begin_token_idx(0),
          deferred_inline_body_end_token_idx(0) {}

    bool has_deferred_inline_body() const {
        return has_deferred_inline_body_tokens != 0 &&
            deferred_inline_body_end_token_idx > deferred_inline_body_begin_token_idx;
    }

    void set_deferred_inline_body_token_range(size_t begin_token_idx,
                                              size_t end_token_idx) {
        has_deferred_inline_body_tokens = 1;
        deferred_inline_body_begin_token_idx = begin_token_idx;
        deferred_inline_body_end_token_idx = end_token_idx;
    }

    void clear_deferred_inline_body_token_range() {
        has_deferred_inline_body_tokens = 0;
        deferred_inline_body_begin_token_idx = 0;
        deferred_inline_body_end_token_idx = 0;
    }

    static bool classof(const Decl *d) {
        return d->get_kind() == DeclKind::CppConstructorDecl;
    }
};

struct CppDestructorDecl : FuncDecl {
    uint8_t has_deferred_inline_body_tokens : 1;
    uint8_t is_virtual : 1;
    uint8_t is_override : 1;
    uint8_t is_final : 1;
    uint8_t is_pure : 1;
    size_t deferred_inline_body_begin_token_idx;
    size_t deferred_inline_body_end_token_idx;

    CppDestructorDecl(const std::string name, const std::shared_ptr<CType> type,
                      std::vector<std::unique_ptr<Decl>> parameters, std::unique_ptr<Stmt> body,
                      std::unordered_set<std::string> stmt_labels = {},
                      StorageClass storage_class = StorageClass::NONE, bool is_inline = false,
                      SrcLoc loc = SrcLoc())
        : FuncDecl(DeclKind::CppDestructorDecl, name, type, std::move(parameters),
                   std::move(body), std::move(stmt_labels), storage_class, is_inline, loc),
          has_deferred_inline_body_tokens(false),
          is_virtual(false),
          is_override(false),
          is_final(false),
          is_pure(false),
          deferred_inline_body_begin_token_idx(0),
          deferred_inline_body_end_token_idx(0) {}

    explicit CppDestructorDecl(SrcLoc loc = SrcLoc())
        : FuncDecl(DeclKind::CppDestructorDecl, loc),
          has_deferred_inline_body_tokens(false),
          is_virtual(false),
          is_override(false),
          is_final(false),
          is_pure(false),
          deferred_inline_body_begin_token_idx(0),
          deferred_inline_body_end_token_idx(0) {}

    bool has_deferred_inline_body() const {
        return has_deferred_inline_body_tokens != 0 &&
            deferred_inline_body_end_token_idx > deferred_inline_body_begin_token_idx;
    }

    void set_deferred_inline_body_token_range(size_t begin_token_idx,
                                              size_t end_token_idx) {
        has_deferred_inline_body_tokens = 1;
        deferred_inline_body_begin_token_idx = begin_token_idx;
        deferred_inline_body_end_token_idx = end_token_idx;
    }

    void clear_deferred_inline_body_token_range() {
        has_deferred_inline_body_tokens = 0;
        deferred_inline_body_begin_token_idx = 0;
        deferred_inline_body_end_token_idx = 0;
    }

    static bool classof(const Decl *d) {
        return d->get_kind() == DeclKind::CppDestructorDecl;
    }
};

inline bool function_decl_defines_entity(const FuncDecl* decl) {
    if (!decl) {
        return false;
    }
    if (decl->body || decl->is_deleted || decl->is_defaulted) {
        return true;
    }
    if (auto* method_decl = dyn_cast<const CppMethodDecl>(decl)) {
        return method_decl->has_deferred_inline_body();
    }
    if (auto* ctor_decl = dyn_cast<const CppConstructorDecl>(decl)) {
        return ctor_decl->has_deferred_inline_body();
    }
    if (auto* dtor_decl = dyn_cast<const CppDestructorDecl>(decl)) {
        return dtor_decl->has_deferred_inline_body();
    }
    return false;
}

struct FriendDecl : Decl {
    std::unique_ptr<Decl> target_decl;
    QualType granting_record_type;
    std::shared_ptr<Symbol> function_symbol;
    uint8_t friend_kind : 3;
    uint8_t has_deferred_inline_body_tokens : 1;
    size_t deferred_inline_body_begin_token_idx;
    size_t deferred_inline_body_end_token_idx;

    FriendDecl(std::unique_ptr<Decl> target_decl,
               QualType granting_record_type,
               CppFriendKind friend_kind = CppFriendKind::Unknown,
               SrcLoc loc = SrcLoc())
        : Decl(DeclKind::FriendDecl, loc),
          target_decl(std::move(target_decl)),
          granting_record_type(std::move(granting_record_type)),
          friend_kind(static_cast<uint8_t>(friend_kind)),
          has_deferred_inline_body_tokens(false),
          deferred_inline_body_begin_token_idx(0),
          deferred_inline_body_end_token_idx(0) {}

    CppFriendKind get_friend_kind() const {
        return static_cast<CppFriendKind>(friend_kind);
    }

    Decl* target() { return target_decl.get(); }
    const Decl* target() const { return target_decl.get(); }

    FuncDecl* function_decl() {
        return dyn_cast<FuncDecl>(target_decl.get());
    }

    const FuncDecl* function_decl() const {
        return dyn_cast<const FuncDecl>(target_decl.get());
    }

    bool has_deferred_inline_body() const {
        return has_deferred_inline_body_tokens != 0 &&
            deferred_inline_body_end_token_idx > deferred_inline_body_begin_token_idx;
    }

    void set_deferred_inline_body_token_range(size_t begin_token_idx,
                                              size_t end_token_idx) {
        has_deferred_inline_body_tokens = 1;
        deferred_inline_body_begin_token_idx = begin_token_idx;
        deferred_inline_body_end_token_idx = end_token_idx;
    }

    void clear_deferred_inline_body_token_range() {
        has_deferred_inline_body_tokens = 0;
        deferred_inline_body_begin_token_idx = 0;
        deferred_inline_body_end_token_idx = 0;
    }

    static bool classof(const Decl *d) {
        return d->get_kind() == DeclKind::FriendDecl;
    }
};

struct FunctionTemplateSpecializationInfo;
struct VariableTemplateSpecializationInfo;
struct TemplateDecl;
void set_func_decl_cxx_qualifier_prefix(const FuncDecl* decl,
                                        std::optional<std::string> prefix);
const std::string* get_func_decl_cxx_qualifier_prefix(const FuncDecl* decl);
void clear_func_decl_cxx_qualifier_prefixes();
void set_func_decl_owner_record_type(const FuncDecl* decl, QualType owner_type);
QualType get_func_decl_owner_record_type(const FuncDecl* decl);
void clear_func_decl_owner_record_types();
void set_func_decl_function_template_specialization(
    const FuncDecl* decl,
    const FunctionTemplateSpecializationInfo& info);
const FunctionTemplateSpecializationInfo*
get_func_decl_function_template_specialization(const FuncDecl* decl);
void clear_func_decl_function_template_specializations();
void set_variable_decl_variable_template_specialization(
    const VariableDecl* decl,
    const VariableTemplateSpecializationInfo& info);
const VariableTemplateSpecializationInfo*
get_variable_decl_variable_template_specialization(const VariableDecl* decl);
void clear_variable_decl_variable_template_specializations();
void set_template_decl_canonical_decl(const TemplateDecl* decl,
                                      const TemplateDecl* canonical_decl);
const TemplateDecl* get_template_decl_canonical_decl(const TemplateDecl* decl);
void clear_template_decl_canonical_decls();
const TemplateDecl* get_template_decl_lookup_identity(const Decl* decl);
bool template_decls_share_lookup_identity(const Decl* lhs, const Decl* rhs);
bool template_decl_is_preferred_lookup_representative(const Decl* existing,
                                                      const Decl* candidate);
void set_template_parameter_default_argument(
    const TemplateParameterDecl* decl,
    std::optional<TemplateArgument> argument);
const TemplateArgument* get_template_parameter_default_argument(
    const TemplateParameterDecl* decl);
void clear_template_parameter_default_arguments();
bool merge_template_decl_default_arguments(
    const TemplateDecl* decl,
    size_t* conflict_param_index = nullptr);
const std::vector<std::optional<TemplateArgument>>*
get_template_decl_default_arguments(const TemplateDecl* decl);
void clear_template_decl_default_arguments();
struct ParamDecl;
void set_param_decl_default_argument(const ParamDecl* decl, std::unique_ptr<Expr> expr);
const Expr* get_param_decl_default_argument(const ParamDecl* decl);
void clear_param_decl_default_arguments();
// this wraps a decl(s) in a statement
struct Decl2Stmt: Stmt {
    std::vector<std::unique_ptr<Decl>> decls;
    Decl2Stmt(SrcLoc loc = SrcLoc()): Stmt(StmtKind::Decl2Stmt, loc) {
    };
    explicit Decl2Stmt(std::unique_ptr<Decl> decl, SrcLoc loc = SrcLoc()): Stmt(StmtKind::Decl2Stmt, loc) {
        decls.push_back(std::move(decl));
    };
    explicit Decl2Stmt(std::vector<std::unique_ptr<Decl>> decls, SrcLoc loc = SrcLoc()): Stmt(StmtKind::Decl2Stmt, loc) {
        this->decls = std::move(decls);
        if (loc.isInvalid() && this->decls.size() > 0) {
            this->location = this->decls[0]->location;
        }
    };

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::Decl2Stmt; }
};
struct IntegerLiteral: Expr {
    explicit IntegerLiteral(std::string value, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::IntegerLiteral, loc), value(intern_fallback(std::move(value))) {}
    explicit IntegerLiteral(const std::string* value, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::IntegerLiteral, loc), value(value) {}
    explicit IntegerLiteral(std::string value, QualType ctype, SrcLoc loc = SrcLoc())
    : Expr(StmtKind::IntegerLiteral, loc), value(intern_fallback(std::move(value))), ctype(std::move(ctype)) {}
    explicit IntegerLiteral(const std::string* value, QualType ctype, SrcLoc loc = SrcLoc())
    : Expr(StmtKind::IntegerLiteral, loc), value(value), ctype(std::move(ctype)) {}

    const std::string* value = nullptr;
    QualType ctype;
    const std::string& get_value() const {
        if (value) {
            return *value;
        }
        static const std::string empty_value;
        return empty_value;
    }
    const std::string* get_value_ptr() const { return value; }
    QualType get_type() override {
        return ctype;
    }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::IntegerLiteral; }

private:
    static const std::string* intern_fallback(std::string value) {
        static std::unordered_set<std::string> pool;
        auto [it, _] = pool.emplace(std::move(value));
        return &(*it);
    }
};
struct FloatingLiteral: Expr {
    explicit FloatingLiteral(std::string value, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::FloatingLiteral, loc), value(value), is_imaginary(false) {};
    explicit FloatingLiteral(std::string value, QualType ctype, SrcLoc loc = SrcLoc())
    : Expr(StmtKind::FloatingLiteral, loc), value(value), ctype(std::move(ctype)), is_imaginary(false) {};
    FloatingLiteral(std::string value, QualType ctype, bool is_imaginary, SrcLoc loc = SrcLoc())
    : Expr(StmtKind::FloatingLiteral, loc), value(value), ctype(std::move(ctype)), is_imaginary(is_imaginary) {};

    std::string value;
    QualType ctype;
    uint8_t is_imaginary : 1;
    QualType get_type() override {
        return ctype;
    }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::FloatingLiteral; }
};
struct CharacterLiteral: Expr {
    explicit CharacterLiteral(std::string value, int32_t int_val, SrcLoc loc = SrcLoc()): Expr(StmtKind::CharacterLiteral, loc), value(std::move(value)),
    int_value(int_val) {};
    explicit CharacterLiteral(std::string value, int32_t int_val, QualType ctype, SrcLoc loc = SrcLoc())
    : Expr(StmtKind::CharacterLiteral, loc), value(std::move(value)), ctype(std::move(ctype)), int_value(int_val) {};

    std::string value;
    int32_t int_value;
    QualType ctype;
    QualType get_type() override {
        return ctype;
    }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::CharacterLiteral; }
};
struct StringLiteral: Expr {
    explicit StringLiteral(std::string value, SrcLoc loc = SrcLoc()): Expr(StmtKind::StringLiteral, loc), value(value) {};
    explicit StringLiteral(std::string value, QualType ctype, SrcLoc loc = SrcLoc())
    : Expr(StmtKind::StringLiteral, loc), value(value), ctype(std::move(ctype)) {};

    std::string value;
    QualType ctype;
    QualType get_type() override {
        return ctype;
    }
    bool letPassthrough() override {
        return true;
    }
    bool isLValue() override {
        return true; // String literals are lvalues
    }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::StringLiteral; }
};
// C99 __func__, GCC __FUNCTION__ / __PRETTY_FUNCTION__
// Behaves like: static const char __func__[] = "function_name";
enum class PredefinedIdentKind : uint8_t { Func, Function, PrettyFunction };
struct PredefinedExpr: Expr {
    PredefinedExpr(PredefinedIdentKind kind, std::string func_name, QualType ctype, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::PredefinedExpr, loc), ident_kind(kind), func_name(std::move(func_name)), ctype(std::move(ctype)) {}

    PredefinedIdentKind ident_kind;
    std::string func_name;
    QualType ctype;
    QualType get_type() override { return ctype; }
    bool isLValue() override { return true; }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::PredefinedExpr; }
};
struct CppThisExpr : Expr {
    QualType this_type;

    explicit CppThisExpr(QualType this_type, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::CppThisExpr, loc), this_type(std::move(this_type)) {}

    QualType get_type() override { return this_type; }
    bool isLValue() override { return false; }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::CppThisExpr; }
};
struct QualifiedVarRef;
struct VarRef: Expr {
    explicit VarRef(std::string name, SrcLoc loc = SrcLoc())
        : VarRef(StmtKind::VarRef, intern_fallback(std::move(name)), nullptr, loc) {}

    explicit VarRef(std::string name, std::shared_ptr<Symbol> symref, SrcLoc loc = SrcLoc())
        : VarRef(
              StmtKind::VarRef,
              symref ? nullptr : intern_fallback(std::move(name)),
              std::move(symref),
              loc) {}

    explicit VarRef(const std::string* spelled_name, SrcLoc loc = SrcLoc())
        : VarRef(StmtKind::VarRef, spelled_name, nullptr, loc) {}

    explicit VarRef(std::shared_ptr<Symbol> symref, SrcLoc loc = SrcLoc())
        : VarRef(StmtKind::VarRef, nullptr, std::move(symref), loc) {}

    VarRef(const std::string* spelled_name, std::shared_ptr<Symbol> symref, SrcLoc loc = SrcLoc())
        : VarRef(StmtKind::VarRef, spelled_name, std::move(symref), loc) {}

    bool isLValue() override {
        if (symref && (symref->kind == SymbolKind::ENUM_CONSTANT
            || symref->kind == SymbolKind::FUNCTION)) {
            return false;
        }
        return true;
    }

    const std::string& get_name() const {
        if (spelled_name) {
            return *spelled_name;
        }
        if (symref) {
            return symref->name;
        }
        static const std::string empty_name;
        return empty_name;
    }

    std::string_view name_view() const { return get_name(); }
    bool has_spelled_name() const { return spelled_name != nullptr; }
    const std::string* get_spelled_name_ptr() const { return spelled_name; }
    bool has_cpp_qualified_info() const;
    const CppQualifiedExprInfo* get_cpp_qualified_info() const;
    CppQualifiedExprInfo* get_cpp_qualified_info();

    const std::string* spelled_name = nullptr;
    std::shared_ptr<Symbol> symref;
    QualType get_type() override {
        if (!symref) return nullptr;
        return symref->type;
    }

    static bool classof(const Stmt *s) {
        return s->get_kind() == StmtKind::VarRef ||
               s->get_kind() == StmtKind::QualifiedVarRef;
    }

protected:
    VarRef(StmtKind kind,
           const std::string* spelled_name,
           std::shared_ptr<Symbol> symref,
           SrcLoc loc = SrcLoc())
        : Expr(kind, loc),
          spelled_name(spelled_name),
          symref(std::move(symref)) {}

private:
    static const std::string* intern_fallback(std::string name) {
        static std::unordered_set<std::string> pool;
        auto [it, _] = pool.emplace(std::move(name));
        return &(*it);
    }
};
struct QualifiedVarRef: VarRef {
    QualifiedVarRef(const std::string* spelled_name,
                    std::shared_ptr<Symbol> symref,
                    CppQualifiedExprInfo qualified_info,
                    SrcLoc loc = SrcLoc())
        : VarRef(
              StmtKind::QualifiedVarRef,
              spelled_name,
              std::move(symref),
              loc),
          qualified_info(std::make_unique<CppQualifiedExprInfo>(
              std::move(qualified_info))) {}

    std::unique_ptr<CppQualifiedExprInfo> qualified_info;

    static bool classof(const Stmt *s) {
        return s->get_kind() == StmtKind::QualifiedVarRef;
    }
};

inline bool VarRef::has_cpp_qualified_info() const {
    return get_cpp_qualified_info() != nullptr;
}

inline const CppQualifiedExprInfo* VarRef::get_cpp_qualified_info() const {
    auto* qualified = dyn_cast<QualifiedVarRef>(this);
    if (!qualified) {
        return nullptr;
    }
    return qualified->qualified_info.get();
}

inline CppQualifiedExprInfo* VarRef::get_cpp_qualified_info() {
    auto* qualified = dyn_cast<QualifiedVarRef>(this);
    if (!qualified) {
        return nullptr;
    }
    return qualified->qualified_info.get();
}

inline std::unique_ptr<Expr> attach_cpp_qualified_info_to_expr(
    std::unique_ptr<Expr> expr,
    CppQualifiedExprInfo qualified_info) {
    auto* var_ref = dyn_cast<VarRef>(expr.get());
    if (!var_ref) {
        return expr;
    }
    if (auto* qualified_var_ref = dyn_cast<QualifiedVarRef>(expr.get())) {
        *qualified_var_ref->qualified_info = std::move(qualified_info);
        return expr;
    }

    auto upgraded = std::make_unique<QualifiedVarRef>(
        var_ref->get_spelled_name_ptr(),
        var_ref->symref,
        std::move(qualified_info),
        var_ref->location);
    upgraded->node_id = var_ref->node_id;
    return upgraded;
}
struct UnresolvedLookupExpr : Expr {
    std::string name;
    DependentLookupQualifier qualifier;
    std::optional<std::vector<TemplateArgument>> explicit_template_arguments;
    std::shared_ptr<Scope> lexical_lookup_scope;
    std::shared_ptr<DeclContext> lexical_lookup_context;
    bool requires_template_keyword = false;
    bool is_dependent = true;
    QualType ctype;

    explicit UnresolvedLookupExpr(std::string name, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::UnresolvedLookupExpr, loc),
          name(std::move(name)) {}

    UnresolvedLookupExpr(
        std::string name,
        DependentLookupQualifier qualifier,
        std::optional<std::vector<TemplateArgument>> explicit_template_arguments = std::nullopt,
        bool requires_template_keyword = false,
        bool is_dependent = true,
        QualType ctype = nullptr,
        SrcLoc loc = SrcLoc(),
        std::shared_ptr<Scope> lexical_lookup_scope = nullptr,
        std::shared_ptr<DeclContext> lexical_lookup_context = nullptr)
        : Expr(StmtKind::UnresolvedLookupExpr, loc),
          name(std::move(name)),
          qualifier(std::move(qualifier)),
          explicit_template_arguments(std::move(explicit_template_arguments)),
          lexical_lookup_scope(std::move(lexical_lookup_scope)),
          lexical_lookup_context(std::move(lexical_lookup_context)),
          requires_template_keyword(requires_template_keyword),
          is_dependent(is_dependent),
          ctype(std::move(ctype)) {}

    bool has_explicit_template_arguments() const {
        return explicit_template_arguments.has_value();
    }

    QualType get_type() override { return ctype; }

    static bool classof(const Stmt *s) {
        return s->get_kind() == StmtKind::UnresolvedLookupExpr;
    }
};
struct LabelAddressExpr: Expr {
    std::string label;
    QualType ctype;

    explicit LabelAddressExpr(std::string label, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::LabelAddressExpr, loc), label(std::move(label)) {}
    LabelAddressExpr(std::string label, QualType ctype, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::LabelAddressExpr, loc), label(std::move(label)), ctype(std::move(ctype)) {}

    QualType get_type() override {
        return ctype;
    }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::LabelAddressExpr; }
};
struct FuncCall: Expr {
    std::unique_ptr<Expr> func; // where/what is the function?
    std::vector<std::unique_ptr<Expr>> args; // arguments
    QualType ctype;
    FuncCall(std::unique_ptr<Expr> func, SrcLoc loc = SrcLoc()): Expr(StmtKind::FuncCall, loc), func(std::move(func)) {};

    FuncCall(std::unique_ptr<Expr> func, std::vector<std::unique_ptr<Expr>> args, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::FuncCall, loc), func(std::move(func)),
          args(std::move(args)),
          ctype(nullptr)  {}

    QualType get_type() override {
        return ctype;
    }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::FuncCall; }
};
struct DependentCallExpr : Expr {
    std::unique_ptr<Expr> callee;
    std::vector<std::unique_ptr<Expr>> args;
    QualType ctype;
    QualType known_function_type;

    explicit DependentCallExpr(std::unique_ptr<Expr> callee,
                               SrcLoc loc = SrcLoc())
        : Expr(StmtKind::DependentCallExpr, loc),
          callee(std::move(callee)) {}

    DependentCallExpr(std::unique_ptr<Expr> callee,
                      std::vector<std::unique_ptr<Expr>> args,
                      QualType ctype = nullptr,
                      QualType known_function_type = nullptr,
                      SrcLoc loc = SrcLoc())
        : Expr(StmtKind::DependentCallExpr, loc),
          callee(std::move(callee)),
          args(std::move(args)),
          ctype(std::move(ctype)),
          known_function_type(std::move(known_function_type)) {}

    QualType get_type() override { return ctype; }

    static bool classof(const Stmt *s) {
        return s->get_kind() == StmtKind::DependentCallExpr;
    }
};
struct DependentArraySubscriptExpr : Expr {
    std::unique_ptr<Expr> array;
    std::unique_ptr<Expr> index;
    QualType ctype;

    explicit DependentArraySubscriptExpr(SrcLoc loc = SrcLoc())
        : Expr(StmtKind::DependentArraySubscriptExpr, loc) {}

    DependentArraySubscriptExpr(std::unique_ptr<Expr> array,
                                std::unique_ptr<Expr> index,
                                QualType ctype = nullptr,
                                SrcLoc loc = SrcLoc())
        : Expr(StmtKind::DependentArraySubscriptExpr, loc),
          array(std::move(array)),
          index(std::move(index)),
          ctype(std::move(ctype)) {}

    QualType get_type() override { return ctype; }

    bool isLValue() override { return true; }

    static bool classof(const Stmt *s) {
        return s->get_kind() == StmtKind::DependentArraySubscriptExpr;
    }
};
struct PackExpansionExpr : Expr {
    std::unique_ptr<Expr> pattern;

    explicit PackExpansionExpr(std::unique_ptr<Expr> pattern,
                               SrcLoc loc = SrcLoc())
        : Expr(StmtKind::PackExpansionExpr, loc), pattern(std::move(pattern)) {}

    QualType get_type() override {
        return pattern ? pattern->get_type() : QualType(nullptr);
    }

    bool isLValue() override {
        return pattern ? pattern->isLValue() : false;
    }

    static bool classof(const Stmt* s) {
        return s->get_kind() == StmtKind::PackExpansionExpr;
    }
};
struct CppMemberCallExpr: Expr {
    std::unique_ptr<FuncCall> lowered_call; // Existing lowered call payload.
    std::string member_name;
    QualType ctype;
    uint8_t isArrow : 1;
    uint8_t suppress_virtual_dispatch : 1;
    uint8_t has_implicit_object_argument : 1;

    CppMemberCallExpr(std::unique_ptr<FuncCall> lowered_call,
                      std::string member_name,
                      bool isArrow,
                      bool suppress_virtual_dispatch,
                      bool has_implicit_object_argument,
                      SrcLoc loc = SrcLoc())
        : Expr(StmtKind::CppMemberCallExpr, loc),
          lowered_call(std::move(lowered_call)),
          member_name(std::move(member_name)),
          ctype(this->lowered_call ? this->lowered_call->get_type() : QualType(nullptr)),
          isArrow(isArrow),
          suppress_virtual_dispatch(suppress_virtual_dispatch),
          has_implicit_object_argument(has_implicit_object_argument) {}

    QualType get_type() override {
        if (ctype) {
            return ctype;
        }
        return lowered_call ? lowered_call->get_type() : QualType(nullptr);
    }

    static bool classof(const Stmt *s) {
        return s->get_kind() == StmtKind::CppMemberCallExpr;
    }
};
struct CppConstructExpr: Expr {
    std::shared_ptr<Symbol> ctor_sym;
    std::vector<std::unique_ptr<Expr>> args;
    QualType ctype;
    bool is_list_init = false;

    CppConstructExpr(std::shared_ptr<Symbol> ctor_sym,
                     std::vector<std::unique_ptr<Expr>> args,
                     QualType ctype,
                     bool is_list_init = false,
                     SrcLoc loc = SrcLoc())
        : Expr(StmtKind::CppConstructExpr, loc),
          ctor_sym(std::move(ctor_sym)),
          args(std::move(args)),
          ctype(std::move(ctype)),
          is_list_init(is_list_init) {}

    QualType get_type() override {
        return ctype;
    }

    static bool classof(const Stmt *s) {
        return s->get_kind() == StmtKind::CppConstructExpr;
    }
};
struct CppValueInitExpr: Expr {
    QualType ctype;

    CppValueInitExpr(QualType ctype, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::CppValueInitExpr, loc), ctype(std::move(ctype)) {}

    QualType get_type() override {
        return ctype;
    }

    static bool classof(const Stmt *s) {
        return s->get_kind() == StmtKind::CppValueInitExpr;
    }
};
struct CppFunctionStyleCastExpr: Expr {
    QualType target_type;
    std::vector<std::unique_ptr<Expr>> args;

    CppFunctionStyleCastExpr(QualType target_type,
                             std::vector<std::unique_ptr<Expr>> args,
                             SrcLoc loc = SrcLoc())
        : Expr(StmtKind::CppFunctionStyleCastExpr, loc),
          target_type(std::move(target_type)),
          args(std::move(args)) {}

    QualType get_type() override {
        return target_type;
    }

    bool isLValue() override {
        auto ref = desugar_type(target_type).as_shared<ReferenceType>();
        return ref && ref->isLValueReference();
    }

    static bool classof(const Stmt *s) {
        return s->get_kind() == StmtKind::CppFunctionStyleCastExpr;
    }
};
struct CppImmediateInvocationExpr: Expr {
    std::unique_ptr<Expr> invocation;
    ConstValue value;
    QualType ctype;

    CppImmediateInvocationExpr(std::unique_ptr<Expr> invocation,
                               ConstValue value,
                               QualType ctype,
                               SrcLoc loc = SrcLoc())
        : Expr(StmtKind::CppImmediateInvocationExpr, loc),
          invocation(std::move(invocation)),
          value(std::move(value)),
          ctype(std::move(ctype)) {}

    QualType get_type() override {
        return ctype;
    }

    static bool classof(const Stmt *s) {
        return s->get_kind() == StmtKind::CppImmediateInvocationExpr;
    }
};
struct CppThrowExpr: Expr {
    std::unique_ptr<Expr> thrown_expr;
    QualType ctype;
    bool is_rethrow = false;

    CppThrowExpr(std::unique_ptr<Expr> thrown_expr,
                 QualType ctype,
                 bool is_rethrow,
                 SrcLoc loc = SrcLoc())
        : Expr(StmtKind::CppThrowExpr, loc),
          thrown_expr(std::move(thrown_expr)),
          ctype(std::move(ctype)),
          is_rethrow(is_rethrow) {}

    QualType get_type() override {
        return ctype;
    }

    static bool classof(const Stmt *s) {
        return s->get_kind() == StmtKind::CppThrowExpr;
    }
};
struct CppNewExpr: Expr {
    QualType allocated_type;
    QualType result_type;
    std::vector<std::unique_ptr<Expr>> placement_args;
    std::unique_ptr<Expr> initializer;
    std::vector<std::unique_ptr<Expr>> constructor_args;
    std::shared_ptr<Symbol> allocator_sym;
    std::shared_ptr<Symbol> deallocator_sym;
    std::shared_ptr<Symbol> ctor_sym;
    uint8_t is_array_form : 1;
    uint8_t is_global_allocation : 1;
    uint8_t is_list_init : 1;

    CppNewExpr(QualType allocated_type,
               QualType result_type,
               std::vector<std::unique_ptr<Expr>> placement_args,
               std::unique_ptr<Expr> initializer,
               std::vector<std::unique_ptr<Expr>> constructor_args,
               std::shared_ptr<Symbol> allocator_sym,
               std::shared_ptr<Symbol> deallocator_sym,
               std::shared_ptr<Symbol> ctor_sym,
               bool is_array_form,
               bool is_global_allocation,
               bool is_list_init,
               SrcLoc loc = SrcLoc())
        : Expr(StmtKind::CppNewExpr, loc),
          allocated_type(std::move(allocated_type)),
          result_type(std::move(result_type)),
          placement_args(std::move(placement_args)),
          initializer(std::move(initializer)),
          constructor_args(std::move(constructor_args)),
          allocator_sym(std::move(allocator_sym)),
          deallocator_sym(std::move(deallocator_sym)),
          ctor_sym(std::move(ctor_sym)),
          is_array_form(is_array_form),
          is_global_allocation(is_global_allocation),
          is_list_init(is_list_init) {}

    QualType get_type() override {
        return result_type;
    }

    static bool classof(const Stmt *s) {
        return s->get_kind() == StmtKind::CppNewExpr;
    }
};
struct CppDeleteExpr: Expr {
    enum class DestructionKind : uint8_t {
        None,
        Direct,
        Virtual,
    };

    std::unique_ptr<Expr> operand;
    QualType ctype;
    QualType destroyed_type;
    std::shared_ptr<Symbol> deallocator_sym;
    std::shared_ptr<Symbol> destructor_sym;
    DestructionKind destruction_kind = DestructionKind::None;
    uint8_t is_array_form : 1;
    uint8_t is_global_delete : 1;

    CppDeleteExpr(std::unique_ptr<Expr> operand,
                  QualType ctype,
                  QualType destroyed_type,
                  std::shared_ptr<Symbol> deallocator_sym,
                  std::shared_ptr<Symbol> destructor_sym,
                  DestructionKind destruction_kind,
                  bool is_array_form,
                  bool is_global_delete,
                  SrcLoc loc = SrcLoc())
        : Expr(StmtKind::CppDeleteExpr, loc),
          operand(std::move(operand)),
          ctype(std::move(ctype)),
          destroyed_type(std::move(destroyed_type)),
          deallocator_sym(std::move(deallocator_sym)),
          destructor_sym(std::move(destructor_sym)),
          destruction_kind(destruction_kind),
          is_array_form(is_array_form),
          is_global_delete(is_global_delete) {}

    QualType get_type() override {
        return ctype;
    }

    static bool classof(const Stmt *s) {
        return s->get_kind() == StmtKind::CppDeleteExpr;
    }
};
struct CppPseudoDestructorExpr : Expr {
    std::unique_ptr<Expr> base;
    QualType destroyed_type;
    QualType ctype;
    std::shared_ptr<Symbol> destructor_sym;
    uint8_t is_arrow : 1;

    CppPseudoDestructorExpr(std::unique_ptr<Expr> base,
                            QualType destroyed_type,
                            QualType ctype,
                            std::shared_ptr<Symbol> destructor_sym,
                            bool is_arrow,
                            SrcLoc loc = SrcLoc())
        : Expr(StmtKind::CppPseudoDestructorExpr, loc),
          base(std::move(base)),
          destroyed_type(std::move(destroyed_type)),
          ctype(std::move(ctype)),
          destructor_sym(std::move(destructor_sym)),
          is_arrow(is_arrow) {}

    QualType get_type() override {
        return ctype;
    }

    static bool classof(const Stmt* s) {
        return s->get_kind() == StmtKind::CppPseudoDestructorExpr;
    }
};
struct BlockByrefAccessExpr : Expr {
    std::unique_ptr<Expr> cell_expr;
    std::shared_ptr<Symbol> symbol;
    QualType ctype;

    BlockByrefAccessExpr(std::unique_ptr<Expr> cell_expr,
                         std::shared_ptr<Symbol> symbol,
                         QualType ctype,
                         SrcLoc loc = SrcLoc())
        : Expr(StmtKind::BlockByrefAccessExpr, loc),
          cell_expr(std::move(cell_expr)),
          symbol(std::move(symbol)),
          ctype(std::move(ctype)) {}

    QualType get_type() override { return ctype; }
    bool isLValue() override { return true; }

    static bool classof(const Stmt* s) {
        return s->get_kind() == StmtKind::BlockByrefAccessExpr;
    }
};
struct BlockExpr : Expr {
    BlockSemanticInfo semantic_info;
    QualType block_type;
    std::vector<std::unique_ptr<Decl>> parameters;
    std::unique_ptr<CompoundStmt> body;
    std::unordered_set<std::string> stmt_labels;
    QualType explicit_return_type;
    uint8_t has_parameter_clause : 1;
    uint8_t has_explicit_return_type : 1;

    BlockExpr(BlockSemanticInfo semantic_info,
              QualType block_type,
              std::vector<std::unique_ptr<Decl>> parameters,
              std::unique_ptr<CompoundStmt> body,
              std::unordered_set<std::string> stmt_labels,
              QualType explicit_return_type,
              bool has_parameter_clause,
              bool has_explicit_return_type,
              SrcLoc loc = SrcLoc())
        : Expr(StmtKind::BlockExpr, loc),
          semantic_info(std::move(semantic_info)),
          block_type(std::move(block_type)),
          parameters(std::move(parameters)),
          body(std::move(body)),
          stmt_labels(std::move(stmt_labels)),
          explicit_return_type(std::move(explicit_return_type)),
          has_parameter_clause(has_parameter_clause),
          has_explicit_return_type(has_explicit_return_type) {}

    QualType get_type() override { return block_type; }

    QualType function_type() const {
        if (auto block_ptr = block_type.as_shared<BlockPointerType>()) {
            return block_ptr->pointed_type;
        }
        return QualType();
    }

    static bool classof(const Stmt* s) {
        return s->get_kind() == StmtKind::BlockExpr;
    }
};
struct CppLambdaExpr : Expr {
    LambdaClosureInfo closure_info;
    LambdaSemanticInfo semantic_info;
    QualType written_call_operator_type;
    TemplateParameterList call_operator_template_parameters;
    std::unique_ptr<Expr> template_requires_clause;
    std::unique_ptr<Expr> trailing_requires_clause;
    std::vector<std::unique_ptr<Decl>> parameters;
    std::unique_ptr<CompoundStmt> body;
    std::unordered_set<std::string> stmt_labels;
    QualType explicit_return_type;
    uint8_t has_parameter_clause : 1;
    uint8_t is_mutable : 1;
    uint8_t is_constexpr : 1;
    uint8_t is_consteval : 1;
    uint8_t has_noexcept : 1;
    uint8_t has_trailing_return : 1;
    uint8_t is_generic : 1;

    CppLambdaExpr(LambdaClosureInfo closure_info,
                  LambdaSemanticInfo semantic_info,
                  QualType written_call_operator_type,
                  TemplateParameterList call_operator_template_parameters,
                  std::unique_ptr<Expr> template_requires_clause,
                  std::unique_ptr<Expr> trailing_requires_clause,
                  std::vector<std::unique_ptr<Decl>> parameters,
                  std::unique_ptr<CompoundStmt> body,
                  std::unordered_set<std::string> stmt_labels,
                  QualType explicit_return_type,
                  bool has_parameter_clause,
                  bool is_mutable,
                  bool is_constexpr,
                  bool is_consteval,
                  bool has_noexcept,
                  bool has_trailing_return,
                  bool is_generic,
                  SrcLoc loc = SrcLoc())
        : Expr(StmtKind::CppLambdaExpr, loc),
          closure_info(std::move(closure_info)),
          semantic_info(std::move(semantic_info)),
          written_call_operator_type(std::move(written_call_operator_type)),
          call_operator_template_parameters(
              std::move(call_operator_template_parameters)),
          template_requires_clause(std::move(template_requires_clause)),
          trailing_requires_clause(std::move(trailing_requires_clause)),
          parameters(std::move(parameters)),
          body(std::move(body)),
          stmt_labels(std::move(stmt_labels)),
          explicit_return_type(std::move(explicit_return_type)),
          has_parameter_clause(has_parameter_clause),
          is_mutable(is_mutable),
          is_constexpr(is_constexpr),
          is_consteval(is_consteval),
          has_noexcept(has_noexcept),
          has_trailing_return(has_trailing_return),
          is_generic(is_generic) {}

    QualType get_type() override { return semantic_info.closure_type(); }

    ObjectDecl* closure_semantic_owner() {
        return semantic_info.semantic_owner();
    }

    const ObjectDecl* closure_semantic_owner() const {
        return semantic_info.semantic_owner();
    }

    const std::string& closure_name() const {
        return semantic_info.closure_name();
    }

    static bool classof(const Stmt* s) {
        return s->get_kind() == StmtKind::CppLambdaExpr;
    }
};
struct CppTypeIdExpr: Expr {
    QualType type_operand;
    std::unique_ptr<Expr> expr_operand;
    QualType ctype;
    bool is_type_operand = false;

    CppTypeIdExpr(QualType type_operand,
                  QualType ctype,
                  SrcLoc loc = SrcLoc())
        : Expr(StmtKind::CppTypeIdExpr, loc),
          type_operand(std::move(type_operand)),
          ctype(std::move(ctype)),
          is_type_operand(true) {}

    CppTypeIdExpr(std::unique_ptr<Expr> expr_operand,
                  QualType ctype,
                  SrcLoc loc = SrcLoc())
        : Expr(StmtKind::CppTypeIdExpr, loc),
          expr_operand(std::move(expr_operand)),
          ctype(std::move(ctype)),
          is_type_operand(false) {}

    QualType get_type() override {
        return ctype;
    }

    bool isLValue() override {
        return true;
    }

    static bool classof(const Stmt *s) {
        return s->get_kind() == StmtKind::CppTypeIdExpr;
    }
};
struct CppDynamicCastExpr: Expr {
    std::unique_ptr<Expr> expr;
    QualType target_type;

    CppDynamicCastExpr(std::unique_ptr<Expr> expr,
                       QualType target_type,
                       SrcLoc loc = SrcLoc())
        : Expr(StmtKind::CppDynamicCastExpr, loc),
          expr(std::move(expr)),
          target_type(std::move(target_type)) {}

    QualType get_type() override {
        return target_type;
    }

    bool isLValue() override {
        auto ref = desugar_type(target_type).as_shared<ReferenceType>();
        return ref && ref->isLValueReference();
    }

    static bool classof(const Stmt *s) {
        return s->get_kind() == StmtKind::CppDynamicCastExpr;
    }
};
struct CondExpr: Expr {
    std::unique_ptr<Expr> condition;
    std::unique_ptr<Expr> true_expr;
    std::unique_ptr<Expr> false_expr;
    QualType type;
    CondExpr(std::unique_ptr<Expr> condition, std::unique_ptr<Expr> true_expr,
        std::unique_ptr<Expr> false_expr, QualType type)
        : Expr(StmtKind::CondExpr),
          condition(std::move(condition)),
          true_expr(std::move(true_expr)),
          false_expr(std::move(false_expr)), type(std::move(type)) {
        this->location = this->condition->location;
    };

    QualType get_type() override {
        return type;
    }

    bool isLValue() override {
        Expr* true_operand = true_expr ? true_expr.get() : condition.get();
        if (!true_operand || !false_expr) {
            return false;
        }
        QualType true_type = true_operand->get_type();
        QualType false_type = false_expr->get_type();
        if (!true_type || !false_type) {
            return false;
        }
        bool same_glvalue_type = true_type.equals_unqualified(false_type);
        if (!same_glvalue_type) {
            auto true_ref = desugar_type(true_type).as_shared<ReferenceType>();
            auto false_ref = desugar_type(false_type).as_shared<ReferenceType>();
            same_glvalue_type =
                true_ref &&
                false_ref &&
                true_ref->reference_kind == ReferenceKind::LValue &&
                false_ref->reference_kind == ReferenceKind::LValue &&
                true_ref->referred_type.equals_unqualified(
                    false_ref->referred_type);
        }
        if (!same_glvalue_type) {
            return false;
        }
        return true_operand->isLValue() && false_expr->isLValue();
    }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::CondExpr; }
};

enum class UnaryOpTypes : uint8_t {
    UNKNOWN,
    INCREMENT, // ++
    DECREMENT, // --
    INCREMENT_PREFIX, // ++a
    DECREMENT_PREFIX, // --a
    INCREMENT_POSTFIX, // a++
    DECREMENT_POSTFIX, // a--

    NEG, // -
    POSITIVE, // + (unary plus, identity for arithmetic)
    BITWISE_NOT, // ~
    LOGICAL_NOT, // !
    DEREFERENCE, // *
    ADDRESS_OF, // &
    REAL_PART, // __real__
    IMAG_PART, // __imag__
};
bool is_unary_operator(std::string& c);
UnaryOpTypes string2uop(std::string& c);
struct DependentUnaryExpr : Expr {
    UnaryOpTypes uop = UnaryOpTypes::UNKNOWN;
    std::unique_ptr<Expr> operand;
    QualType ctype;

    explicit DependentUnaryExpr(UnaryOpTypes uop, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::DependentUnaryExpr, loc), uop(uop) {}

    DependentUnaryExpr(UnaryOpTypes uop,
                       std::unique_ptr<Expr> operand,
                       QualType ctype = nullptr,
                       SrcLoc loc = SrcLoc())
        : Expr(StmtKind::DependentUnaryExpr, loc),
          uop(uop),
          operand(std::move(operand)),
          ctype(std::move(ctype)) {}

    QualType get_type() override { return ctype; }

    bool isLValue() override {
        return uop == UnaryOpTypes::DEREFERENCE;
    }

    static bool classof(const Stmt* s) {
        return s->get_kind() == StmtKind::DependentUnaryExpr;
    }
};
struct DependentMemberPointerAccessExpr : Expr {
    std::unique_ptr<Expr> base;
    std::unique_ptr<Expr> member_pointer;
    QualType ctype;
    uint8_t is_arrow : 1;

    explicit DependentMemberPointerAccessExpr(bool is_arrow,
                                              SrcLoc loc = SrcLoc())
        : Expr(StmtKind::DependentMemberPointerAccessExpr, loc),
          ctype(QualType(std::make_shared<AutoType>(AutoTypeFlavor::Cxx))),
          is_arrow(is_arrow ? 1 : 0) {}

    DependentMemberPointerAccessExpr(std::unique_ptr<Expr> base,
                                     std::unique_ptr<Expr> member_pointer,
                                     QualType ctype,
                                     bool is_arrow,
                                     SrcLoc loc = SrcLoc())
        : Expr(StmtKind::DependentMemberPointerAccessExpr, loc),
          base(std::move(base)),
          member_pointer(std::move(member_pointer)),
          ctype(std::move(ctype)),
          is_arrow(is_arrow ? 1 : 0) {}

    QualType get_type() override { return ctype; }
    bool isLValue() override { return true; }

    static bool classof(const Stmt* s) {
        return s->get_kind() == StmtKind::DependentMemberPointerAccessExpr;
    }
};
enum class BinOpTypes : uint8_t;
struct DependentBinaryExpr : Expr {
    BinOpTypes bop;
    std::unique_ptr<Expr> left;
    std::unique_ptr<Expr> right;
    QualType ctype;

    explicit DependentBinaryExpr(BinOpTypes bop, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::DependentBinaryExpr, loc), bop(bop) {}

    DependentBinaryExpr(std::unique_ptr<Expr> left,
                        std::unique_ptr<Expr> right,
                        BinOpTypes bop,
                        QualType ctype = nullptr,
                        SrcLoc loc = SrcLoc())
        : Expr(StmtKind::DependentBinaryExpr, loc),
          bop(bop),
          left(std::move(left)),
          right(std::move(right)),
          ctype(std::move(ctype)) {}

    QualType get_type() override { return ctype; }

    static bool classof(const Stmt* s) {
        return s->get_kind() == StmtKind::DependentBinaryExpr;
    }
};
struct UnaryOperation: Expr {
    UnaryOpTypes uop;
    std::unique_ptr<Expr> exp;
    QualType ctype; // For dereference/address_of

    explicit UnaryOperation(UnaryOpTypes uop, SrcLoc loc = SrcLoc()): Expr(StmtKind::UnaryOperation, loc), uop(uop), exp(nullptr) {};
    UnaryOperation(UnaryOpTypes uop, std::unique_ptr<Expr> exp, SrcLoc loc = SrcLoc())
    : Expr(StmtKind::UnaryOperation, loc), uop(uop), exp(std::move(exp)) {

    };


    QualType get_type() override {
        if (ctype) return ctype;
        return exp->get_type();
    }
    bool isLValue() override {
        if (uop == UnaryOpTypes::REAL_PART || uop == UnaryOpTypes::IMAG_PART) {
            // __real__ and __imag__ are lvalues when operand is a complex lvalue
            return exp && exp->get_type() && exp->get_type()->isComplex() && exp->isLValue();
        }
        if (uop != UnaryOpTypes::DEREFERENCE) {
            return false;
        }
        if (ctype && ctype->kind == TypeKind::Function) {
            return false;
        }
        return true;
    }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::UnaryOperation; }
};
enum class BinOpTypes : uint8_t {
    UNKNOWN,
    COMMA, // ,
    MEMBER_PTR_DOT, // .*
    MEMBER_PTR_ARROW, // ->*
    MULT, // *
    DIV, // /
    MOD, // %
    ADD, // +
    SUB, // -
    QUESTION, // ?
    BITWISE_AND, // &
    BITWISE_XOR, // ^
    BITWISE_OR, // |
    LOGICAL_AND, // &&
    LOGICAL_OR, // ||
    SHIFT_LEFT, // <<
    SHIFT_RIGHT, // >>
    THREE_WAY_COMPARE, // <=>
    LESS_EQUAL_THAN, // <=
    LESS_THAN, // <
    GREATER_EQUAL_THAN, // >=
    GREATER_THAN, // >
    EQUAL, // ==
    NOT_EQUAL, // !=

    ASSIGN, // =
    ASSIGN_MUL, // *=
    ASSIGN_DIV, // /=
    ASSIGN_MOD, // %=
    ASSIGN_ADD, // +=
    ASSIGN_SUB, // -=
    ASSIGN_LSHIFT, // <<=
    ASSIGN_RSHIFT, // >>=
    ASSIGN_AND, // &=
    ASSIGN_XOR, // ^=
    ASSIGN_OR, // |=


};
bool is_assignment_binop(BinOpTypes typ);
bool is_compound_assignment_binop(BinOpTypes typ);
bool is_binary_operator(std::string c);
BinOpTypes string2bop(std::string& c);

enum class ImplicitCastTypes : uint8_t {
    UNKNOWN,
    RAW_CAST, // never sign extend, trunc if necessary. Just raw data transported. Use for ptrs
    ARITH_CAST,
    LVALUE_TO_RVALUE,
    ARRAY_TO_POINTER,
    FUNCTION_TO_POINTER,
    LAMBDA_TO_FUNCTION_POINTER,
    VECTOR_SPLAT,       // scalar -> vector broadcast
    REAL_TO_COMPLEX,    // real scalar -> complex (set imag = 0)
    COMPLEX_TO_REAL,    // complex -> real (discard imag)
    COMPLEX_TO_COMPLEX  // complex -> complex (convert both parts)
};
struct ImplicitCast: Expr {
    ImplicitCastTypes kind;
    std::unique_ptr<Expr> expr;
    QualType ctype;
    QualType get_type() override {
        if (ctype) return ctype;
        return expr->get_type();
    }

    ImplicitCast(std::unique_ptr<Expr> expr, QualType ctype)
        : Expr(StmtKind::ImplicitCast),
          kind(ImplicitCastTypes::ARITH_CAST),
          expr(std::move(expr)),
          ctype(std::move(ctype)) {
        if (this->ctype && this->expr && this->expr->get_type() &&
            ((this->ctype->kind == TypeKind::Pointer &&
              this->expr->get_type()->kind == TypeKind::Pointer) ||
             (this->ctype->kind == TypeKind::BlockPointer &&
              this->expr->get_type()->kind == TypeKind::BlockPointer) ||
             (this->ctype->kind == TypeKind::MemberPointer &&
              this->expr->get_type()->kind == TypeKind::MemberPointer))) {
            this->kind = ImplicitCastTypes::RAW_CAST;
        }
        // Auto-detect complex cast kinds
        if (this->ctype && this->expr) {
            bool dest_complex = this->ctype->isComplex();
            bool src_complex = this->expr->get_type() && this->expr->get_type()->isComplex();
            if (dest_complex && !src_complex) {
                this->kind = ImplicitCastTypes::REAL_TO_COMPLEX;
            } else if (!dest_complex && src_complex) {
                this->kind = ImplicitCastTypes::COMPLEX_TO_REAL;
            } else if (dest_complex && src_complex) {
                this->kind = ImplicitCastTypes::COMPLEX_TO_COMPLEX;
            }
        }
        if (this->expr) this->location = this->expr->location;
    }
    ImplicitCast(ImplicitCastTypes kind, std::unique_ptr<Expr> expr,
        QualType ctype)
    : Expr(StmtKind::ImplicitCast),
      kind(kind),
      expr(std::move(expr)),
      ctype(std::move(ctype)) {
        if (this->expr) this->location = this->expr->location;
    }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::ImplicitCast; }
};
enum class ExplicitCastKind : uint8_t {
    General,
    CppConstCast
};

struct ExplicitCast: Expr {
    std::unique_ptr<Expr> expr;
    QualType ctype;
    ExplicitCastKind cast_kind = ExplicitCastKind::General;
    QualType get_type() override {
        return ctype;
    }

    bool isLValue() override {
        auto ref = desugar_type(ctype).as_shared<ReferenceType>();
        return ref && ref->isLValueReference();
    }

    ExplicitCast(std::unique_ptr<Expr> expr,
                 QualType ctype,
                 SrcLoc loc = SrcLoc(),
                 ExplicitCastKind cast_kind = ExplicitCastKind::General)
        : Expr(StmtKind::ExplicitCast, loc), expr(std::move(expr)),
          ctype(std::move(ctype)), cast_kind(cast_kind) {
    }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::ExplicitCast; }
};
// we need to handle the IR for this differently

// e1 OP= e2 is equivelant to e1 = e1 OP e2
struct CompoundAssignOperation: Expr {
    BinOpTypes bop;
    std::unique_ptr<Expr> left; // needs to be lvalue
    std::unique_ptr<Expr> right;
    QualType ctype; // this is the type of e1 OP e2

    CompoundAssignOperation(std::unique_ptr<Expr> left, std::unique_ptr<Expr> right, BinOpTypes bop,
        QualType ctype, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::CompoundAssignOperation, loc), bop(bop), left(std::move(left)),
          right(std::move(right)),
          ctype(std::move(ctype)) {
        // convert the ASSIGN_ADD to ADD in bop
        switch (this->bop) {
            case BinOpTypes::ASSIGN_ADD: this->bop = BinOpTypes::ADD; break;
            case BinOpTypes::ASSIGN_SUB: this->bop = BinOpTypes::SUB; break;
            case BinOpTypes::ASSIGN_MUL: this->bop = BinOpTypes::MULT; break;
            case BinOpTypes::ASSIGN_DIV: this->bop = BinOpTypes::DIV; break;
            case BinOpTypes::ASSIGN_MOD: this->bop = BinOpTypes::MOD; break;
            case BinOpTypes::ASSIGN_AND: this->bop = BinOpTypes::BITWISE_AND; break;
            case BinOpTypes::ASSIGN_OR: this->bop = BinOpTypes::BITWISE_OR; break;
            case BinOpTypes::ASSIGN_XOR: this->bop = BinOpTypes::BITWISE_XOR; break;
            case BinOpTypes::ASSIGN_LSHIFT: this->bop = BinOpTypes::SHIFT_LEFT; break;
            case BinOpTypes::ASSIGN_RSHIFT: this->bop = BinOpTypes::SHIFT_RIGHT; break;
            default: break; // Should not happen for compound assignment operators
        }
    }
    QualType get_type() override {
        return left->get_type();
    }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::CompoundAssignOperation; }
};
struct BinaryOperation: Expr {
    BinOpTypes bop;
    std::unique_ptr<Expr> left;
    std::unique_ptr<Expr> right;
    QualType ctype;

    BinaryOperation(std::unique_ptr<Expr> left, std::unique_ptr<Expr> right, BinOpTypes bop)
      : Expr(StmtKind::BinaryOperation),
        bop(bop), left(std::move(left)), right(std::move(right)) {
        this->location = this->left->location;
    };

    QualType get_type() override {
        return ctype;
    }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::BinaryOperation; }
};
enum class CppBuiltinThreeWayCompareCategory : uint8_t {
    Strong,
    Partial
};

struct CppBuiltinThreeWayCompareExpr : Expr {
    std::unique_ptr<Expr> left;
    std::unique_ptr<Expr> right;
    QualType ctype;
    CppBuiltinThreeWayCompareCategory category =
        CppBuiltinThreeWayCompareCategory::Strong;
    std::shared_ptr<Symbol> less_member;
    std::shared_ptr<Symbol> equivalent_member;
    std::shared_ptr<Symbol> greater_member;
    std::shared_ptr<Symbol> unordered_member;

    CppBuiltinThreeWayCompareExpr(
        std::unique_ptr<Expr> left,
        std::unique_ptr<Expr> right,
        QualType ctype,
        CppBuiltinThreeWayCompareCategory category,
        std::shared_ptr<Symbol> less_member,
        std::shared_ptr<Symbol> equivalent_member,
        std::shared_ptr<Symbol> greater_member,
        std::shared_ptr<Symbol> unordered_member = nullptr,
        SrcLoc loc = SrcLoc())
        : Expr(StmtKind::CppBuiltinThreeWayCompareExpr, loc),
          left(std::move(left)),
          right(std::move(right)),
          ctype(std::move(ctype)),
          category(category),
          less_member(std::move(less_member)),
          equivalent_member(std::move(equivalent_member)),
          greater_member(std::move(greater_member)),
          unordered_member(std::move(unordered_member)) {}

    QualType get_type() override { return ctype; }
    bool isLValue() override { return false; }

    static bool classof(const Stmt *s) {
        return s->get_kind() == StmtKind::CppBuiltinThreeWayCompareExpr;
    }
};
enum class FoldDirection : uint8_t {
    Left,
    Right,
};
struct FoldExpr : Expr {
    BinOpTypes op = BinOpTypes::UNKNOWN;
    FoldDirection direction = FoldDirection::Left;
    std::unique_ptr<Expr> pattern;
    std::unique_ptr<Expr> init;
    QualType result_type;

    FoldExpr(BinOpTypes op,
             FoldDirection direction,
             std::unique_ptr<Expr> pattern,
             std::unique_ptr<Expr> init = nullptr,
             QualType result_type = nullptr,
             SrcLoc loc = SrcLoc())
        : Expr(StmtKind::FoldExpr, loc),
          op(op),
          direction(direction),
          pattern(std::move(pattern)),
          init(std::move(init)),
          result_type(std::move(result_type)) {}

    bool is_binary_fold() const { return init != nullptr; }

    QualType get_type() override { return result_type; }
    bool isLValue() override { return false; }

    static bool classof(const Stmt* s) {
        return s->get_kind() == StmtKind::FoldExpr;
    }
};
struct ArraySubscriptExpr: Expr {
    std::unique_ptr<Expr> array;
    std::unique_ptr<Expr> index;
    QualType ctype;

    ArraySubscriptExpr(std::unique_ptr<Expr> array, std::unique_ptr<Expr> index,
        QualType ctype, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::ArraySubscriptExpr, loc), array(std::move(array)), index(std::move(index)), ctype(std::move(ctype)) {}

    QualType get_type() override {
        return ctype;
    }
    bool isLValue() override {
        return true;
    }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::ArraySubscriptExpr; }
};
struct ReturnStmt: Stmt {
    explicit ReturnStmt( std::unique_ptr<Expr> expression, SrcLoc loc = SrcLoc())
    : Stmt(StmtKind::ReturnStmt, loc), expression(std::move(expression)) {}
    std::unique_ptr<Expr> expression;

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::ReturnStmt; }
};
struct CppCatchClause {
    bool is_catch_all = false;
    QualType exception_type;
    std::string exception_name;
    std::shared_ptr<Symbol> exception_symbol;
    std::unique_ptr<Stmt> handler;
    SrcLoc location;
};
struct CppTryStmt: Stmt {
    std::unique_ptr<Stmt> try_block;
    std::vector<CppCatchClause> handlers;

    CppTryStmt(std::unique_ptr<Stmt> try_block,
               std::vector<CppCatchClause> handlers,
               SrcLoc loc = SrcLoc())
        : Stmt(StmtKind::CppTryStmt, loc),
          try_block(std::move(try_block)),
          handlers(std::move(handlers)) {}

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::CppTryStmt; }
};
struct IfStmt: Stmt {
    IfStatementKind statement_kind = IfStatementKind::Runtime;
    std::unique_ptr<Stmt> init_stmt;
    std::unique_ptr<Expr> condition;
    std::unique_ptr<Stmt> then_stmt;
    std::unique_ptr<Stmt> else_stmt;
    std::shared_ptr<Scope> scope;
    std::optional<bool> constexpr_condition_value;

    IfStmt(std::unique_ptr<Expr> condition, std::unique_ptr<Stmt> then_stmt,
        std::unique_ptr<Stmt> else_stmt = nullptr, SrcLoc loc = SrcLoc(),
        IfStatementKind statement_kind = IfStatementKind::Runtime,
        std::unique_ptr<Stmt> init_stmt = nullptr,
        std::shared_ptr<Scope> scope = nullptr,
        std::optional<bool> constexpr_condition_value = std::nullopt)
        : Stmt(StmtKind::IfStmt, loc), statement_kind(statement_kind),
          init_stmt(std::move(init_stmt)), condition(std::move(condition)),
          then_stmt(std::move(then_stmt)), else_stmt(std::move(else_stmt)),
          scope(std::move(scope)),
          constexpr_condition_value(constexpr_condition_value) {}

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::IfStmt; }
};
struct DefaultStmt;
struct CaseStmt: Stmt {
    std::unique_ptr<Expr> const_expr;
    std::unique_ptr<Expr> range_end; // For GCC case ranges: case LOW ... HIGH
    std::unique_ptr<Stmt> stmt;

    CaseStmt(std::unique_ptr<Expr> const_expr, std::unique_ptr<Stmt> stmt, SrcLoc loc = SrcLoc())
        : Stmt(StmtKind::CaseStmt, loc), const_expr(std::move(const_expr)),
          stmt(std::move(stmt)) {
    }

    CaseStmt(std::unique_ptr<Expr> const_expr, std::unique_ptr<Expr> range_end,
             std::unique_ptr<Stmt> stmt, SrcLoc loc = SrcLoc())
        : Stmt(StmtKind::CaseStmt, loc), const_expr(std::move(const_expr)),
          range_end(std::move(range_end)), stmt(std::move(stmt)) {
    }

    ~CaseStmt() override;

    bool is_range() const { return range_end != nullptr; }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::CaseStmt; }
};
struct DefaultStmt: Stmt {
    std::unique_ptr<Stmt> stmt;

    DefaultStmt(std::unique_ptr<Stmt> stmt, SrcLoc loc = SrcLoc())
        : Stmt(StmtKind::DefaultStmt, loc), stmt(std::move(stmt)) {
    }

    ~DefaultStmt() override {
        Stmt* next = stmt.release();
        while (next) {
            if (next->get_kind() == StmtKind::DefaultStmt) {
                auto* nested_default = static_cast<DefaultStmt*>(next);
                Stmt* nested = nested_default->stmt.release();
                delete nested_default;
                next = nested;
                continue;
            }
            if (next->get_kind() == StmtKind::CaseStmt) {
                auto* nested_case = static_cast<CaseStmt*>(next);
                Stmt* nested = nested_case->stmt.release();
                delete nested_case;
                next = nested;
                continue;
            }
            delete next;
            break;
        }
    }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::DefaultStmt; }
};
inline CaseStmt::~CaseStmt() {
    Stmt* next = stmt.release();
    while (next) {
        if (next->get_kind() == StmtKind::CaseStmt) {
            auto* nested_case = static_cast<CaseStmt*>(next);
            Stmt* nested = nested_case->stmt.release();
            delete nested_case;
            next = nested;
            continue;
        }
        if (next->get_kind() == StmtKind::DefaultStmt) {
            auto* nested_default = static_cast<DefaultStmt*>(next);
            Stmt* nested = nested_default->stmt.release();
            delete nested_default;
            next = nested;
            continue;
        }
        delete next;
        break;
    }
}
struct LabeledStmt: Stmt {
    std::string name;
    std::unique_ptr<Stmt> stmt;

    LabeledStmt(std::string name, std::unique_ptr<Stmt> stmt, SrcLoc loc = SrcLoc())
        : Stmt(StmtKind::LabeledStmt, loc), name(name), stmt(std::move(stmt)) {
    }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::LabeledStmt; }
};
struct GoToStmt: Stmt {
    std::string name;

    GoToStmt(std::string name, SrcLoc loc = SrcLoc())
        : Stmt(StmtKind::GoToStmt, loc), name(name) {
    }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::GoToStmt; }
};
struct ComputedGotoStmt: Stmt {
    std::unique_ptr<Expr> target;

    ComputedGotoStmt(std::unique_ptr<Expr> target, SrcLoc loc = SrcLoc())
        : Stmt(StmtKind::ComputedGotoStmt, loc), target(std::move(target)) {
    }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::ComputedGotoStmt; }
};
struct SwitchStmt: Stmt {
    std::unique_ptr<Expr> condition;
    std::unique_ptr<Stmt> stmt;

    SwitchStmt(std::unique_ptr<Expr> condition, std::unique_ptr<Stmt> stmt, SrcLoc loc = SrcLoc())
        : Stmt(StmtKind::SwitchStmt, loc), condition(std::move(condition)), stmt(std::move(stmt)) {}

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::SwitchStmt; }
};
struct WhileStmt: Stmt {
    std::unique_ptr<Expr> condition;
    std::unique_ptr<Stmt> body_stmt;

    WhileStmt(std::unique_ptr<Expr> condition, std::unique_ptr<Stmt> body_stmt, SrcLoc loc = SrcLoc())
        : Stmt(StmtKind::WhileStmt, loc), condition(std::move(condition)), body_stmt(std::move(body_stmt)) {}

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::WhileStmt; }
};
struct DoWhileStmt: Stmt {
    std::unique_ptr<Expr> condition;
    std::unique_ptr<Stmt> body_stmt;

    DoWhileStmt(std::unique_ptr<Expr> condition, std::unique_ptr<Stmt> body_stmt, SrcLoc loc = SrcLoc())
        : Stmt(StmtKind::DoWhileStmt, loc), condition(std::move(condition)), body_stmt(std::move(body_stmt)) {}

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::DoWhileStmt; }
};
struct ForStmt: Stmt {
    std::unique_ptr<Stmt> init;  // 1st clause
    std::unique_ptr<Expr> cond; // 2nd clause
    std::unique_ptr<Expr> action; // 3rd clause

    std::unique_ptr<Stmt> body_stmt;

    std::shared_ptr<Scope> scope;

    ForStmt(std::unique_ptr<Stmt> init, std::unique_ptr<Expr> cond, std::unique_ptr<Expr> action,
        std::unique_ptr<Stmt> body_stmt, std::shared_ptr<Scope> scope, SrcLoc loc = SrcLoc())
        : Stmt(StmtKind::ForStmt, loc), init(std::move(init)),
          cond(std::move(cond)),
          action(std::move(action)),
          body_stmt(std::move(body_stmt)),
          scope(scope) {
    }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::ForStmt; }
};
struct CppRangeForStmt: Stmt {
    std::unique_ptr<Stmt> init_statement;
    std::vector<std::unique_ptr<Decl>> range_declaration_side_decls;
    // reference of range-initalizer
    std::unique_ptr<Decl> range_variable;
    std::unique_ptr<Decl> begin_variable;
    std::unique_ptr<Decl> end_variable;
    std::unique_ptr<Decl> loop_variable;
    // lowered loop test
    std::unique_ptr<Expr> condition;
    // lowered loop step
    std::unique_ptr<Expr> increment;
    std::unique_ptr<Stmt> body_stmt;
    std::shared_ptr<Scope> scope;

    CppRangeForStmt(std::unique_ptr<Stmt> init_statement,
                    std::vector<std::unique_ptr<Decl>> range_declaration_side_decls,
                    std::unique_ptr<Decl> range_variable,
                    std::unique_ptr<Decl> begin_variable,
                    std::unique_ptr<Decl> end_variable,
                    std::unique_ptr<Decl> loop_variable,
                    std::unique_ptr<Expr> condition,
                    std::unique_ptr<Expr> increment,
                    std::unique_ptr<Stmt> body_stmt,
                    std::shared_ptr<Scope> scope,
                    SrcLoc loc = SrcLoc())
        : Stmt(StmtKind::CppRangeForStmt, loc),
          init_statement(std::move(init_statement)),
          range_declaration_side_decls(std::move(range_declaration_side_decls)),
          range_variable(std::move(range_variable)),
          begin_variable(std::move(begin_variable)),
          end_variable(std::move(end_variable)),
          loop_variable(std::move(loop_variable)),
          condition(std::move(condition)),
          increment(std::move(increment)),
          body_stmt(std::move(body_stmt)),
          scope(std::move(scope)) {}

    static bool classof(const Stmt *s) {
        return s->get_kind() == StmtKind::CppRangeForStmt;
    }
};
struct ContinueStmt: Stmt {
    ContinueStmt(SrcLoc loc = SrcLoc()) : Stmt(StmtKind::ContinueStmt, loc) {};

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::ContinueStmt; }
};
struct BreakStmt: Stmt {
    BreakStmt(SrcLoc loc = SrcLoc()) : Stmt(StmtKind::BreakStmt, loc) {};

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::BreakStmt; }
};
struct EmptyStmt: Stmt {
    EmptyStmt(SrcLoc loc = SrcLoc()) : Stmt(StmtKind::EmptyStmt, loc) {};

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::EmptyStmt; }
};
// Error recovery AST nodes — represent constructs that failed to parse.
// Downstream passes (sema, codegen) detect these and skip the subtree.
struct ErrorStmt : Stmt {
    std::string error_message;
    ErrorStmt(std::string msg, SrcLoc loc = SrcLoc())
        : Stmt(StmtKind::ErrorStmt, loc), error_message(std::move(msg)) {}

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::ErrorStmt; }
};
struct ErrorDecl : Decl {
    std::string error_message;
    ErrorDecl(std::string msg, SrcLoc loc = SrcLoc())
        : Decl(DeclKind::ErrorDecl, loc), error_message(std::move(msg)) {}

    static bool classof(const Decl *d) { return d->get_kind() == DeclKind::ErrorDecl; }
};
struct ErrorExpr : Expr {
    std::string error_message;
    ErrorExpr(std::string msg, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::ErrorExpr, loc), error_message(std::move(msg)) {}
    QualType get_type() override { return nullptr; }
    bool isLValue() override { return false; }
    bool letPassthrough() override { return true; }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::ErrorExpr; }
};
struct Designator {
    enum class Kind {
        Field,
        Index,
        Range
    };

    Kind kind;
    std::string field_name;
    std::unique_ptr<Expr> index;
    std::unique_ptr<Expr> range_end;
    SrcLoc loc;

    static Designator field(std::string name, SrcLoc loc = SrcLoc()) {
        Designator d;
        d.kind = Kind::Field;
        d.field_name = std::move(name);
        d.loc = loc;
        return d;
    }
    static Designator index_designator(std::unique_ptr<Expr> idx, SrcLoc loc = SrcLoc()) {
        Designator d;
        d.kind = Kind::Index;
        d.index = std::move(idx);
        d.loc = loc;
        return d;
    }
    static Designator range_designator(std::unique_ptr<Expr> start, std::unique_ptr<Expr> end, SrcLoc loc = SrcLoc()) {
        Designator d;
        d.kind = Kind::Range;
        d.index = std::move(start);
        d.range_end = std::move(end);
        d.loc = loc;
        return d;
    }
};

struct InitElement {
    std::vector<Designator> designators;
    std::unique_ptr<Expr> value;
    SrcLoc loc;
};

struct InitAction {
    std::vector<std::vector<size_t>> paths; // One or more target paths for a single evaluated value
    std::shared_ptr<Expr> value;
    SrcLoc loc;
};

struct InitListExpr: Expr {
    std::vector<InitElement> elements;
    std::vector<InitAction> actions;
    std::map<size_t, std::shared_ptr<Expr>> mappings;
    bool is_paren_init = false;
    QualType type;
    InitListExpr(SrcLoc loc = SrcLoc()) : Expr(StmtKind::InitListExpr, loc), type(nullptr) {}
    QualType get_type() override {
        return type;
    }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::InitListExpr; }
};
struct VariableDecl: Decl {
    QualType type;
    QualType original_type;
    std::string name;
    std::unique_ptr<Expr> init;
    std::vector<TemplateArgument> explicit_specialization_arguments;
    std::shared_ptr<Symbol> sym;
    const std::string* asm_label;
    StorageClass storage_class;
    bool has_explicit_specialization_argument_list = false;
    uint8_t is_inline : 1;
    uint8_t is_constexpr : 1;
    uint8_t is_thread_local : 1;
    uint8_t is_block_byref : 1;
    uint8_t language_linkage : 2;
    mutable uint32_t external_semantic_owner_id = 0; // See ownership conventions at top of file

    bool is_const() const { return type.is_const(); }

    VariableDecl(QualType type, const std::string &name,
                 std::unique_ptr<Expr> init, bool is_inline = false, SrcLoc loc = SrcLoc()) :
    Decl(DeclKind::VariableDecl, loc), type(std::move(type)), original_type(nullptr), name(name), init(std::move(init)), asm_label(nullptr),
    storage_class(StorageClass::NONE),
    has_explicit_specialization_argument_list(false),
    is_inline(is_inline), is_constexpr(false), is_thread_local(false),
    is_block_byref(false),
    language_linkage(static_cast<uint8_t>(LanguageLinkage::None)) {}

    VariableDecl(QualType type, const std::string &name,
             std::unique_ptr<Expr> init, std::shared_ptr<Symbol> sym,
             StorageClass storage_class = StorageClass::NONE, bool is_inline = false, SrcLoc loc = SrcLoc()) :
    Decl(DeclKind::VariableDecl, loc), type(std::move(type)), original_type(nullptr), name(name), init(std::move(init)), sym(std::move(sym)),
    asm_label(nullptr), storage_class(storage_class),
    has_explicit_specialization_argument_list(false),
    is_inline(is_inline), is_constexpr(false), is_thread_local(false),
    is_block_byref(false),
    language_linkage(static_cast<uint8_t>(LanguageLinkage::None)) {}

    void set_cxx_constructor_init(std::shared_ptr<Symbol> ctor_sym,
                                  std::vector<std::unique_ptr<Expr>> ctor_args,
                                  bool is_list_init = false) {
        init = std::make_unique<CppConstructExpr>(
            std::move(ctor_sym),
            std::move(ctor_args),
            type,
            is_list_init,
            location);
    }

    void clear_cxx_constructor_init() {
        if (isa<CppConstructExpr>(init.get())) {
            init.reset();
        }
    }

    CppConstructExpr* get_cpp_construct_init() {
        return dyn_cast<CppConstructExpr>(init.get());
    }

    const CppConstructExpr* get_cpp_construct_init() const {
        return dyn_cast<CppConstructExpr>(init.get());
    }

    bool has_cxx_constructor_call() const {
        const auto* ctor_init = get_cpp_construct_init();
        return ctor_init != nullptr && ctor_init->ctor_sym != nullptr;
    }

    void set_asm_label(std::optional<std::string> label) {
        if (!label.has_value()) {
            asm_label = nullptr;
            return;
        }
        asm_label = intern_asm_label(std::move(*label));
    }
    void set_asm_label(const std::string& label) {
        asm_label = intern_asm_label(std::string(label));
    }
    void clear_asm_label() { asm_label = nullptr; }
    LanguageLinkage get_language_linkage() const {
        return static_cast<LanguageLinkage>(language_linkage);
    }
    void set_language_linkage(LanguageLinkage linkage_kind) {
        language_linkage = static_cast<uint8_t>(linkage_kind);
    }

    static bool classof(const Decl *d) { return d->get_kind() == DeclKind::VariableDecl; }

private:
    static const std::string* intern_asm_label(std::string label) {
        static std::unordered_set<std::string> pool;
        auto [it, _] = pool.emplace(std::move(label));
        return &(*it);
    }
};
struct ParamDecl: Decl {
    QualType type;
    const std::string* name;
    std::shared_ptr<Symbol> sym;
    StorageClass storage_class;
    uint8_t is_constexpr : 1;
    uint8_t is_parameter_pack : 1;
    mutable uint32_t external_semantic_owner_id = 0; // See ownership conventions at top of file
    std::shared_ptr<CType> original_type; // Unadjusted type (before array-to-pointer decay)


    ParamDecl(QualType type, const std::string &name, SrcLoc loc = SrcLoc())
    : Decl(DeclKind::ParamDecl, loc), type(std::move(type)), name(intern_name(std::string(name))),
    storage_class(StorageClass::NONE),
    is_constexpr(false), is_parameter_pack(false), original_type(nullptr) {}
    ParamDecl(QualType type, const std::string &name, std::shared_ptr<Symbol> sym,
              StorageClass storage_class = StorageClass::NONE, SrcLoc loc = SrcLoc())
    : Decl(DeclKind::ParamDecl, loc), type(std::move(type)), name(intern_name(std::string(name))), sym(std::move(sym)),
    storage_class(storage_class),
    is_constexpr(false), is_parameter_pack(false), original_type(nullptr) {}

    const std::string& get_name() const {
        if (name) {
            return *name;
        }
        static const std::string empty_name;
        return empty_name;
    }
    bool has_name() const { return name != nullptr && !name->empty(); }
    const std::string* get_name_ptr() const { return name; }

    static bool classof(const Decl *d) { return d->get_kind() == DeclKind::ParamDecl; }

private:
    static const std::string* intern_name(std::string name) {
        static std::unordered_set<std::string> pool;
        auto [it, _] = pool.emplace(std::move(name));
        return &(*it);
    }
};

// Struct/union field declaration (C11 6.7.2.1)
// Unlike VariableDecl, fields have no storage class, no linkage,
// no symbol table entry, and no initializer (in C).
struct FieldDecl : Decl {
    QualType type;
    std::string name;  // Empty for anonymous fields / anonymous bitfields
    bool is_mutable = false;

    // Bitfield support: UINT32_MAX means "not a bitfield".
    static constexpr uint32_t k_no_bitfield_width = UINT32_MAX;
    uint32_t bitfield_width;

    bool is_bitfield() const { return bitfield_width != k_no_bitfield_width; }
    bool is_const() const { return type.is_const(); }

    // Regular field constructor
    FieldDecl(QualType type, const std::string &name, SrcLoc loc = SrcLoc())
        : Decl(DeclKind::FieldDecl, loc), type(std::move(type)), name(name),
          is_mutable(false), bitfield_width(k_no_bitfield_width) {}

    // Bitfield constructor
    FieldDecl(QualType type, const std::string &name,
              uint32_t bf_width, SrcLoc loc = SrcLoc())
        : Decl(DeclKind::FieldDecl, loc), type(std::move(type)), name(name),
          is_mutable(false), bitfield_width(bf_width) {}

    static bool classof(const Decl *d) { return d->get_kind() == DeclKind::FieldDecl; }
};

// C++ access specifier declaration (public:, protected:, private:).
struct CppAccessSpecDecl : Decl {
    CppAccessSpecifier access;

    explicit CppAccessSpecDecl(CppAccessSpecifier access, SrcLoc loc = SrcLoc())
        : Decl(DeclKind::CppAccessSpecDecl, loc), access(access) {}

    static bool classof(const Decl *d) {
        return d->get_kind() == DeclKind::CppAccessSpecDecl;
    }
};

struct CppBaseSpecifier {
    std::string type_name;
    QualType type = nullptr;
    CppAccessSpecifier access = CppAccessSpecifier::None;
    bool is_virtual_base = false;
    bool is_pack_expansion = false;
    SrcLoc location;

    CppBaseSpecifier() = default;
    CppBaseSpecifier(std::string type_name,
                     QualType type,
                     CppAccessSpecifier access,
                     bool is_virtual_base,
                     bool is_pack_expansion,
                     SrcLoc location = SrcLoc())
        : type_name(std::move(type_name)),
          type(type),
          access(access),
          is_virtual_base(is_virtual_base),
          is_pack_expansion(is_pack_expansion),
          location(location) {}
};

// C++ class/struct/union declaration scaffold.
struct CppRecordDecl : Decl {
    CppRecordKind record_kind;
    std::string name;
    std::vector<CppBaseSpecifier> bases;
    std::vector<std::unique_ptr<Decl>> members;
    std::optional<RecordSemanticState::DefinitionData> definition_data;
    CppAccessSpecifier default_access;
    uint8_t is_definition : 1;

    CppRecordDecl(CppRecordKind record_kind, std::string name,
                  std::vector<CppBaseSpecifier> bases,
                  std::vector<std::unique_ptr<Decl>> members,
                  bool is_definition = true, SrcLoc loc = SrcLoc())
        : Decl(DeclKind::CppRecordDecl, loc),
          record_kind(record_kind),
          name(std::move(name)),
          bases(std::move(bases)),
          members(std::move(members)),
          definition_data(is_definition
              ? std::optional<RecordSemanticState::DefinitionData>(
                    RecordSemanticState::DefinitionData{})
              : std::nullopt),
          default_access(default_access_for(record_kind)),
          is_definition(is_definition) {}

    CppRecordDecl(CppRecordKind record_kind, std::string name,
                  std::vector<CppBaseSpecifier> bases,
                  bool is_definition = false, SrcLoc loc = SrcLoc())
        : Decl(DeclKind::CppRecordDecl, loc),
          record_kind(record_kind),
          name(std::move(name)),
          bases(std::move(bases)),
          definition_data(is_definition
              ? std::optional<RecordSemanticState::DefinitionData>(
                    RecordSemanticState::DefinitionData{})
              : std::nullopt),
          default_access(default_access_for(record_kind)),
          is_definition(is_definition) {}

    bool is_class() const { return record_kind == CppRecordKind::Class; }
    bool is_struct() const { return record_kind == CppRecordKind::Struct; }
    bool is_union() const { return record_kind == CppRecordKind::Union; }
    bool has_definition_data() const { return definition_data.has_value(); }

    RecordSemanticState::DefinitionData* get_definition_data() {
        return definition_data ? &definition_data.value() : nullptr;
    }

    const RecordSemanticState::DefinitionData* get_definition_data() const {
        return definition_data ? &definition_data.value() : nullptr;
    }

    static bool classof(const Decl *d) {
        return d->get_kind() == DeclKind::CppRecordDecl;
    }

    static CppAccessSpecifier default_access_for(CppRecordKind kind) {
        switch (kind) {
            case CppRecordKind::Class:
                return CppAccessSpecifier::Private;
            case CppRecordKind::Struct:
            case CppRecordKind::Union:
                return CppAccessSpecifier::Public;
        }
        return CppAccessSpecifier::Private;
    }
};

struct TemplateDecl : Decl {
    TemplateParameterList parameters;
    std::unique_ptr<Decl> templated_decl;
    std::unique_ptr<Expr> associated_constraint;
    mutable uint32_t external_semantic_owner_id = 0; // See ownership conventions at top of file
    mutable const TemplateDecl* canonical_decl = nullptr;
    mutable const TemplateDecl* pattern_template_decl = nullptr;
    mutable std::vector<std::optional<TemplateArgument>> merged_default_arguments;
    std::vector<class TemplateExplicitSpecializationDecl*> explicit_specializations_;

    const Decl* get_templated_decl() const { return templated_decl.get(); }
    Decl* get_templated_decl() { return templated_decl.get(); }

    void add_explicit_specialization(
        class TemplateExplicitSpecializationDecl* explicit_specialization) {
        if (!explicit_specialization) {
            return;
        }
        explicit_specializations_.push_back(explicit_specialization);
    }

    void replace_explicit_specialization(
        const class TemplateExplicitSpecializationDecl* existing,
        class TemplateExplicitSpecializationDecl* replacement) {
        if (!existing || !replacement) {
            return;
        }
        for (auto*& explicit_specialization : explicit_specializations_) {
            if (explicit_specialization == existing) {
                explicit_specialization = replacement;
                return;
            }
        }
    }

    const std::vector<class TemplateExplicitSpecializationDecl*>&
    explicit_specializations() const {
        return explicit_specializations_;
    }

    void set_pattern_template_decl(const TemplateDecl* pattern_template_decl) {
        this->pattern_template_decl =
            pattern_template_decl ? pattern_template_decl : this;
    }

    const TemplateDecl* get_pattern_template_decl() const {
        return pattern_template_decl ? pattern_template_decl : this;
    }

    class TemplateExplicitSpecializationDecl* find_explicit_specialization(
        const std::vector<TemplateArgument>& specialization_arguments,
        const std::vector<TemplateArgument>& owner_specialization_arguments = {},
        const Decl* primary_member_decl = nullptr);

    const class TemplateExplicitSpecializationDecl* find_explicit_specialization(
        const std::vector<TemplateArgument>& specialization_arguments,
        const std::vector<TemplateArgument>& owner_specialization_arguments = {},
        const Decl* primary_member_decl = nullptr) const;

protected:
    TemplateDecl(DeclKind kind,
                 TemplateParameterList parameters,
                 std::unique_ptr<Decl> templated_decl,
                 SrcLoc loc = SrcLoc())
        : Decl(kind, loc),
          parameters(std::move(parameters)),
          templated_decl(std::move(templated_decl)) {}
};

struct TemplateExplicitSpecializationDecl : Decl {
    std::unique_ptr<Decl> specialized_decl;
    std::unique_ptr<TagDecl> specialized_semantic_decl_;
    std::vector<TemplateArgument> specialization_arguments;
    std::vector<TemplateArgument> owner_specialization_arguments;
    const TemplateDecl* primary_template = nullptr;
    const Decl* primary_member_decl = nullptr;
    bool is_out_of_class_member_specialization = false;
    bool has_explicit_argument_list = false;

    TemplateExplicitSpecializationDecl(
        const TemplateDecl* primary_template,
        std::unique_ptr<Decl> specialized_decl,
        std::vector<TemplateArgument> specialization_arguments = {},
        std::vector<TemplateArgument> owner_specialization_arguments = {},
        const Decl* primary_member_decl = nullptr,
        bool is_out_of_class_member_specialization = false,
        bool has_explicit_argument_list = false,
        SrcLoc loc = SrcLoc())
        : Decl(DeclKind::TemplateExplicitSpecializationDecl, loc),
          specialized_decl(std::move(specialized_decl)),
          specialization_arguments(std::move(specialization_arguments)),
          owner_specialization_arguments(
              std::move(owner_specialization_arguments)),
          primary_template(primary_template),
          primary_member_decl(primary_member_decl),
          is_out_of_class_member_specialization(
              is_out_of_class_member_specialization),
          has_explicit_argument_list(has_explicit_argument_list) {}

    const Decl* get_specialized_decl() const { return specialized_decl.get(); }
    Decl* get_specialized_decl() { return specialized_decl.get(); }

    void set_specialized_record_semantic_decl(std::unique_ptr<ObjectDecl> decl);
    ObjectDecl* specialized_record_semantic_decl();
    const ObjectDecl* specialized_record_semantic_decl() const;

    bool is_definition() const {
        if (auto* function_decl = dyn_cast<FuncDecl>(specialized_decl.get())) {
            return function_decl_defines_entity(function_decl);
        }
        if (auto* record_decl = dyn_cast<CppRecordDecl>(specialized_decl.get())) {
            return record_decl->is_definition;
        }
        if (auto* variable_decl = dyn_cast<VariableDecl>(specialized_decl.get())) {
            if (variable_decl->init) {
                return true;
            }
            return variable_decl->storage_class != StorageClass::EXTERN;
        }
        return false;
    }

    static bool classof(const Decl* d) {
        return d->get_kind() == DeclKind::TemplateExplicitSpecializationDecl;
    }
};

struct FunctionTemplateDecl : TemplateDecl {
    FunctionTemplateDecl(TemplateParameterList parameters,
                         std::unique_ptr<Decl> templated_decl,
                         SrcLoc loc = SrcLoc())
        : TemplateDecl(DeclKind::FunctionTemplateDecl,
                       std::move(parameters),
                       std::move(templated_decl),
                       loc) {}

    FuncDecl* function_decl() {
        return static_cast<FuncDecl*>(templated_decl.get());
    }

    const FuncDecl* function_decl() const {
        return static_cast<const FuncDecl*>(templated_decl.get());
    }

    static bool classof(const Decl* d) {
        return d->get_kind() == DeclKind::FunctionTemplateDecl;
    }
};

struct ClassTemplateDecl;

struct CppDeductionGuideDecl : TemplateDecl {
    std::string name;
    const ClassTemplateDecl* primary_template = nullptr;
    std::vector<std::unique_ptr<Decl>> guide_parameters;
    std::shared_ptr<FunctionType> function_type;
    CppExplicitSpecifier explicit_specifier;

    CppDeductionGuideDecl(TemplateParameterList parameters,
                          std::string name,
                          const ClassTemplateDecl* primary_template,
                          std::vector<std::unique_ptr<Decl>> guide_parameters,
                          std::shared_ptr<FunctionType> function_type,
                          SrcLoc loc = SrcLoc())
        : TemplateDecl(DeclKind::CppDeductionGuideDecl,
                       std::move(parameters),
                       nullptr,
                       loc),
          name(std::move(name)),
          primary_template(primary_template),
          guide_parameters(std::move(guide_parameters)),
          function_type(std::move(function_type)) {}

    QualType return_type() const {
        return function_type ? function_type->ret_type : QualType();
    }

    static bool classof(const Decl* d) {
        return d->get_kind() == DeclKind::CppDeductionGuideDecl;
    }
};

struct VariableTemplateDecl : TemplateDecl {
    bool is_pattern_complete = true;

    VariableTemplateDecl(TemplateParameterList parameters,
                         std::unique_ptr<Decl> templated_decl,
                         SrcLoc loc = SrcLoc())
        : TemplateDecl(DeclKind::VariableTemplateDecl,
                       std::move(parameters),
                       std::move(templated_decl),
                       loc) {}

    VariableDecl* variable_decl() {
        return static_cast<VariableDecl*>(templated_decl.get());
    }

    const VariableDecl* variable_decl() const {
        return static_cast<const VariableDecl*>(templated_decl.get());
    }

    void add_partial_specialization(
        VariableTemplatePartialSpecializationDecl* partial_specialization) {
        if (!partial_specialization) {
            return;
        }
        partial_specializations_.push_back(partial_specialization);
    }

    const std::vector<VariableTemplatePartialSpecializationDecl*>&
    partial_specializations() const {
        return partial_specializations_;
    }

    static bool classof(const Decl* d) {
        return d->get_kind() == DeclKind::VariableTemplateDecl;
    }

private:
    std::vector<VariableTemplatePartialSpecializationDecl*>
        partial_specializations_;
};

inline const TemplateExplicitSpecializationDecl*
TemplateDecl::find_explicit_specialization(
    const std::vector<TemplateArgument>& specialization_arguments,
    const std::vector<TemplateArgument>& owner_specialization_arguments,
    const Decl* primary_member_decl) const {
    auto arguments_match =
        [](const std::vector<TemplateArgument>& lhs,
           const std::vector<TemplateArgument>& rhs) -> bool {
        if (lhs.size() != rhs.size()) {
            return false;
        }
        for (size_t idx = 0; idx < lhs.size(); ++idx) {
            if (!lhs[idx].equals(rhs[idx])) {
                return false;
            }
        }
        return true;
    };

    for (auto* explicit_specialization : explicit_specializations_) {
        if (!explicit_specialization ||
            explicit_specialization->primary_template != this ||
            explicit_specialization->primary_member_decl != primary_member_decl) {
            continue;
        }
        if (!arguments_match(
                explicit_specialization->specialization_arguments,
                specialization_arguments)) {
            continue;
        }
        if (!arguments_match(
                explicit_specialization->owner_specialization_arguments,
                owner_specialization_arguments)) {
            continue;
        }
        return explicit_specialization;
    }
    return nullptr;
}

inline TemplateExplicitSpecializationDecl*
TemplateDecl::find_explicit_specialization(
    const std::vector<TemplateArgument>& specialization_arguments,
    const std::vector<TemplateArgument>& owner_specialization_arguments,
    const Decl* primary_member_decl) {
    return const_cast<TemplateExplicitSpecializationDecl*>(
        const_cast<const TemplateDecl*>(this)->find_explicit_specialization(
            specialization_arguments,
            owner_specialization_arguments,
            primary_member_decl));
}

struct ObjectDecl;
struct VariableTemplatePartialSpecializationDecl;
struct ClassTemplatePartialSpecializationDecl;

struct ClassTemplateDecl : TemplateDecl {
    ClassTemplateDecl(TemplateParameterList parameters,
                      std::unique_ptr<Decl> templated_decl,
                      SrcLoc loc = SrcLoc())
        : TemplateDecl(DeclKind::ClassTemplateDecl,
                       std::move(parameters),
                       std::move(templated_decl),
                       loc) {}

    CppRecordDecl* record_decl() {
        return static_cast<CppRecordDecl*>(templated_decl.get());
    }

    const CppRecordDecl* record_decl() const {
        return static_cast<const CppRecordDecl*>(templated_decl.get());
    }

    void add_partial_specialization(
        ClassTemplatePartialSpecializationDecl* partial_specialization) {
        if (!partial_specialization) {
            return;
        }
        partial_specializations_.push_back(partial_specialization);
    }

    const std::vector<ClassTemplatePartialSpecializationDecl*>&
    partial_specializations() const {
        return partial_specializations_;
    }

    void add_deduction_guide(CppDeductionGuideDecl* deduction_guide) {
        if (!deduction_guide) {
            return;
        }
        deduction_guides_.push_back(deduction_guide);
    }

    const std::vector<CppDeductionGuideDecl*>& deduction_guides() const {
        return deduction_guides_;
    }

    void set_pattern_semantic_decl(std::unique_ptr<ObjectDecl> semantic_decl);
    ObjectDecl* pattern_semantic_decl();
    const ObjectDecl* pattern_semantic_decl() const;

    static bool classof(const Decl* d) {
        return d->get_kind() == DeclKind::ClassTemplateDecl;
    }

private:
    // Canonical semantic owner for the primary class template pattern.
    std::unique_ptr<TagDecl> pattern_semantic_decl_;
    std::vector<ClassTemplatePartialSpecializationDecl*> partial_specializations_;
    std::vector<CppDeductionGuideDecl*> deduction_guides_;
};

struct AliasTemplateDecl : TemplateDecl {
    AliasTemplateDecl(TemplateParameterList parameters,
                      std::unique_ptr<Decl> templated_decl,
                      SrcLoc loc = SrcLoc())
        : TemplateDecl(DeclKind::AliasTemplateDecl,
                       std::move(parameters),
                       std::move(templated_decl),
                       loc) {}

    TypedefDecl* alias_decl() {
        return static_cast<TypedefDecl*>(templated_decl.get());
    }

    const TypedefDecl* alias_decl() const {
        return static_cast<const TypedefDecl*>(templated_decl.get());
    }

    static bool classof(const Decl* d) {
        return d->get_kind() == DeclKind::AliasTemplateDecl;
    }
};

struct ConceptDecl : TemplateDecl {
    std::string name;
    std::unique_ptr<Expr> constraint_expr;

    ConceptDecl(TemplateParameterList parameters,
                std::string name,
                std::unique_ptr<Expr> constraint_expr,
                SrcLoc loc = SrcLoc())
        : TemplateDecl(DeclKind::ConceptDecl,
                       std::move(parameters),
                       nullptr,
                       loc),
          name(std::move(name)),
          constraint_expr(std::move(constraint_expr)) {}

    static bool classof(const Decl* d) {
        return d->get_kind() == DeclKind::ConceptDecl;
    }
};

struct ClassTemplatePartialSpecializationDecl : TemplateDecl {
    std::vector<TemplateArgument> specialization_arguments;

    ClassTemplatePartialSpecializationDecl(
        const ClassTemplateDecl* primary_template,
        TemplateParameterList parameters,
        std::vector<TemplateArgument> specialization_arguments,
        std::unique_ptr<Decl> templated_decl,
        SrcLoc loc = SrcLoc())
        : TemplateDecl(DeclKind::ClassTemplatePartialSpecializationDecl,
                       std::move(parameters),
                       std::move(templated_decl),
                       loc),
          primary_template_(primary_template),
          specialization_arguments(std::move(specialization_arguments)) {}

    CppRecordDecl* record_decl() {
        return static_cast<CppRecordDecl*>(templated_decl.get());
    }

    const CppRecordDecl* record_decl() const {
        return static_cast<const CppRecordDecl*>(templated_decl.get());
    }

    const ClassTemplateDecl* primary_template() const {
        return primary_template_;
    }

    void set_pattern_semantic_decl(std::unique_ptr<ObjectDecl> semantic_decl);
    ObjectDecl* pattern_semantic_decl();
    const ObjectDecl* pattern_semantic_decl() const;

    static bool classof(const Decl* d) {
        return d->get_kind() == DeclKind::ClassTemplatePartialSpecializationDecl;
    }

private:
    const ClassTemplateDecl* primary_template_ = nullptr;
    std::unique_ptr<TagDecl> pattern_semantic_decl_;
};

struct VariableTemplatePartialSpecializationDecl : TemplateDecl {
    std::vector<TemplateArgument> specialization_arguments;

    VariableTemplatePartialSpecializationDecl(
        const VariableTemplateDecl* primary_template,
        TemplateParameterList parameters,
        std::vector<TemplateArgument> specialization_arguments,
        std::unique_ptr<Decl> templated_decl,
        SrcLoc loc = SrcLoc())
        : TemplateDecl(DeclKind::VariableTemplatePartialSpecializationDecl,
                       std::move(parameters),
                       std::move(templated_decl),
                       loc),
          primary_template_(primary_template),
          specialization_arguments(std::move(specialization_arguments)) {}

    VariableDecl* variable_decl() {
        return static_cast<VariableDecl*>(templated_decl.get());
    }

    const VariableDecl* variable_decl() const {
        return static_cast<const VariableDecl*>(templated_decl.get());
    }

    const VariableTemplateDecl* primary_template() const {
        return primary_template_;
    }

    static bool classof(const Decl* d) {
        return d->get_kind() ==
               DeclKind::VariableTemplatePartialSpecializationDecl;
    }

private:
    const VariableTemplateDecl* primary_template_ = nullptr;
};

// Struct/Union declaration
struct ObjectDecl: TagDecl {
    // Canonical record semantics are declaration-owned via side-table metadata.
    std::string tag;                                // Struct tag name
    std::vector<std::unique_ptr<Decl>> fields;      // Field declarations (FieldDecl nodes, plus nested EnumDecl/ObjectDecl)
    uint8_t is_union : 1;

    ObjectDecl(std::string tag, std::vector<std::unique_ptr<Decl>> fields,
               std::shared_ptr<CType> record_type, bool isUnion = false, SrcLoc loc = SrcLoc())
        : TagDecl(DeclKind::ObjectDecl, loc), tag(std::move(tag)), fields(std::move(fields)),
          is_union(isUnion) {
        set_tag_type(std::move(record_type));
        bind_type_backref();
    }

    // For forward declarations (no fields)
    ObjectDecl(std::string tag, std::shared_ptr<CType> record_type, bool isUnion = false, SrcLoc loc = SrcLoc())
        : TagDecl(DeclKind::ObjectDecl, loc), tag(std::move(tag)),
          is_union(isUnion) {
        set_tag_type(std::move(record_type));
        bind_type_backref();
    }

    ~ObjectDecl() override {
        record_semantics_cache_erase(this);
    }

    bool is_complete_definition() const override {
        const RecordSemanticState* state =
            record_semantics_cache_lookup(this, get_side_table_ast_context_for(this));
        return state && !state->is_incomplete;
    }

    const std::string& get_tag_name() const override { return tag; }
    std::shared_ptr<ObjectType> get_record_type() const {
        return dyn_cast_shared<ObjectType>(get_tag_type());
    }

    static bool classof(const Decl *d) { return d->get_kind() == DeclKind::ObjectDecl; }

private:
    void bind_type_backref() {
        auto obj = get_record_type();
        if (obj) {
            const TagDecl* current = obj->get_decl();
            if (!current) {
                obj->set_decl(this);
                return;
            }
            // Keep canonical backrefs stable across transient specifier decls.
            // Only promote an existing incomplete backref to a complete one.
            if (!current->is_complete_definition() && is_complete_definition()) {
                obj->set_decl(this);
            }
        }
    }
};

inline void ClassTemplateDecl::set_pattern_semantic_decl(
    std::unique_ptr<ObjectDecl> semantic_decl) {
    pattern_semantic_decl_.reset(semantic_decl.release());
}

inline ObjectDecl* ClassTemplateDecl::pattern_semantic_decl() {
    return static_cast<ObjectDecl*>(pattern_semantic_decl_.get());
}

inline const ObjectDecl* ClassTemplateDecl::pattern_semantic_decl() const {
    return static_cast<const ObjectDecl*>(pattern_semantic_decl_.get());
}

inline void ClassTemplatePartialSpecializationDecl::set_pattern_semantic_decl(
    std::unique_ptr<ObjectDecl> semantic_decl) {
    pattern_semantic_decl_.reset(semantic_decl.release());
}

inline ObjectDecl* ClassTemplatePartialSpecializationDecl::pattern_semantic_decl() {
    return static_cast<ObjectDecl*>(pattern_semantic_decl_.get());
}

inline const ObjectDecl* ClassTemplatePartialSpecializationDecl::pattern_semantic_decl() const {
    return static_cast<const ObjectDecl*>(pattern_semantic_decl_.get());
}

inline void TemplateExplicitSpecializationDecl::set_specialized_record_semantic_decl(
    std::unique_ptr<ObjectDecl> decl) {
    specialized_semantic_decl_.reset(decl.release());
}

inline ObjectDecl*
TemplateExplicitSpecializationDecl::specialized_record_semantic_decl() {
    return static_cast<ObjectDecl*>(specialized_semantic_decl_.get());
}

inline const ObjectDecl*
TemplateExplicitSpecializationDecl::specialized_record_semantic_decl() const {
    return static_cast<const ObjectDecl*>(specialized_semantic_decl_.get());
}

inline QualType LambdaSemanticInfo::closure_type() const {
    return closure_semantic_decl && closure_semantic_decl->get_record_type()
        ? QualType(closure_semantic_decl->get_record_type())
        : QualType(nullptr);
}

inline ObjectDecl* LambdaSemanticInfo::semantic_owner() {
    return closure_semantic_decl.get();
}

inline const ObjectDecl* LambdaSemanticInfo::semantic_owner() const {
    return closure_semantic_decl.get();
}

inline CppRecordDecl* LambdaSemanticInfo::closure_record() {
    return closure_record_decl.get();
}

inline const CppRecordDecl* LambdaSemanticInfo::closure_record() const {
    return closure_record_decl.get();
}

inline const std::string& LambdaSemanticInfo::closure_name() const {
    if (closure_semantic_decl) {
        return closure_semantic_decl->tag;
    }
    static const std::string empty_name;
    return empty_name;
}

inline QualType BlockSemanticInfo::literal_type() const {
    return literal_semantic_decl && literal_semantic_decl->get_record_type()
        ? QualType(literal_semantic_decl->get_record_type())
        : QualType(nullptr);
}

inline ObjectDecl* BlockSemanticInfo::literal_record() {
    return literal_semantic_decl.get();
}

inline const ObjectDecl* BlockSemanticInfo::literal_record() const {
    return literal_semantic_decl.get();
}

inline const std::string& BlockSemanticInfo::literal_name() const {
    if (literal_semantic_decl) {
        return literal_semantic_decl->tag;
    }
    static const std::string empty_name;
    return empty_name;
}

// Member access expression (e.g., struct_var.field or ptr->field)
struct MemberExpr: Expr {
    std::unique_ptr<Expr> base;     // Base expression (the struct or pointer-to-struct)
    const std::string* member_name; // Name of the member being accessed (interned pointer)
    QualType member_type; // Type of the member
    QualType declared_member_type; // Declared member type before object cv-qualification
    const ObjectDecl* virtual_base_record_decl = nullptr; // Resolved virtual-base root, if lookup crossed one
    uint32_t field_index;           // Index of field in the struct (for codegen)
    std::vector<uint32_t> field_path; // Path of field indices for nested/anonymous members
    uint32_t byte_offset = 0;       // Byte offset from base to field/storage unit
    uint8_t isArrow : 1;            // true for ptr->member, false for obj.member
    uint8_t is_bitfield : 1;        // Bitfield data stored in ASTContext side table
    uint8_t suppress_virtual_dispatch : 1; // true for qualified-id calls (e.g. Base::f())

    MemberExpr(std::unique_ptr<Expr> base, std::string member_name, bool isArrow = false,
               bool suppress_virtual_dispatch = false, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::MemberExpr, loc), base(std::move(base)),
          member_name(intern_fallback(std::move(member_name))),
          member_type(nullptr), declared_member_type(nullptr), field_index(0), isArrow(isArrow), is_bitfield(false),
          suppress_virtual_dispatch(suppress_virtual_dispatch) {}

    MemberExpr(std::unique_ptr<Expr> base, const std::string* member_name, bool isArrow = false,
               bool suppress_virtual_dispatch = false, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::MemberExpr, loc), base(std::move(base)), member_name(member_name),
          member_type(nullptr), declared_member_type(nullptr), field_index(0), isArrow(isArrow), is_bitfield(false),
          suppress_virtual_dispatch(suppress_virtual_dispatch) {}

    MemberExpr(std::unique_ptr<Expr> base, std::string member_name,
               QualType member_type_arg, size_t field_index, bool isArrow = false,
               bool suppress_virtual_dispatch = false, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::MemberExpr, loc), base(std::move(base)),
          member_name(intern_fallback(std::move(member_name))),
          member_type(member_type_arg), declared_member_type(std::move(member_type_arg)),
          field_index(static_cast<uint32_t>(field_index)),
          isArrow(isArrow), is_bitfield(false),
          suppress_virtual_dispatch(suppress_virtual_dispatch) {}

    MemberExpr(std::unique_ptr<Expr> base, const std::string* member_name,
               QualType member_type_arg, size_t field_index, bool isArrow = false,
               bool suppress_virtual_dispatch = false, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::MemberExpr, loc), base(std::move(base)), member_name(member_name),
          member_type(member_type_arg), declared_member_type(std::move(member_type_arg)),
          field_index(static_cast<uint32_t>(field_index)),
          isArrow(isArrow), is_bitfield(false),
          suppress_virtual_dispatch(suppress_virtual_dispatch) {}

    const std::string& get_member_name() const {
        if (member_name) {
            return *member_name;
        }
        static const std::string empty_name;
        return empty_name;
    }

    bool has_member_name() const { return member_name != nullptr; }
    const std::string* get_member_name_ptr() const { return member_name; }

    bool isLValue() override {
        return true; // Member access produces an lvalue
    }

    QualType get_type() override {
        return member_type;
    }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::MemberExpr; }

private:
    static const std::string* intern_fallback(std::string name) {
        static std::unordered_set<std::string> pool;
        auto [it, _] = pool.emplace(std::move(name));
        return &(*it);
    }
};
struct UnresolvedMemberExpr : Expr {
    std::unique_ptr<Expr> base;
    std::string member_name;
    QualType member_type;
    QualType declared_member_type;
    std::optional<std::vector<TemplateArgument>> explicit_template_arguments;
    uint8_t isArrow : 1;
    uint8_t is_current_instantiation : 1;
    uint8_t names_dependent_base : 1;
    uint8_t requires_template_keyword : 1;
    uint8_t suppress_virtual_dispatch : 1;

    UnresolvedMemberExpr(std::unique_ptr<Expr> base,
                         std::string member_name,
                         bool isArrow = false,
                         bool is_current_instantiation = false,
                         bool names_dependent_base = false,
                         bool requires_template_keyword = false,
                         bool suppress_virtual_dispatch = false,
                         SrcLoc loc = SrcLoc())
        : Expr(StmtKind::UnresolvedMemberExpr, loc),
          base(std::move(base)),
          member_name(std::move(member_name)),
          member_type(nullptr),
          declared_member_type(nullptr),
          isArrow(isArrow),
          is_current_instantiation(is_current_instantiation),
          names_dependent_base(names_dependent_base),
          requires_template_keyword(requires_template_keyword),
          suppress_virtual_dispatch(suppress_virtual_dispatch) {}

    UnresolvedMemberExpr(
        std::unique_ptr<Expr> base,
        std::string member_name,
        QualType member_type_arg,
        std::optional<std::vector<TemplateArgument>> explicit_template_arguments = std::nullopt,
        bool isArrow = false,
        bool is_current_instantiation = false,
        bool names_dependent_base = false,
        bool requires_template_keyword = false,
        bool suppress_virtual_dispatch = false,
        SrcLoc loc = SrcLoc())
        : Expr(StmtKind::UnresolvedMemberExpr, loc),
          base(std::move(base)),
          member_name(std::move(member_name)),
          member_type(member_type_arg),
          declared_member_type(std::move(member_type_arg)),
          explicit_template_arguments(std::move(explicit_template_arguments)),
          isArrow(isArrow),
          is_current_instantiation(is_current_instantiation),
          names_dependent_base(names_dependent_base),
          requires_template_keyword(requires_template_keyword),
          suppress_virtual_dispatch(suppress_virtual_dispatch) {}

    bool has_explicit_template_arguments() const {
        return explicit_template_arguments.has_value();
    }

    QualType get_type() override { return member_type; }
    bool isLValue() override { return true; }

    static bool classof(const Stmt *s) {
        return s->get_kind() == StmtKind::UnresolvedMemberExpr;
    }
};

// Pointer-to-member constant expression formed by '&C::member'.
// Currently stores only data-member byte offset payload.
struct MemberPointerLiteralExpr : Expr {
    QualType ctype;
    int64_t byte_offset = 0;
    std::shared_ptr<Symbol> method_symbol = nullptr;
    int32_t virtual_slot_index = -1;
    const std::string* member_name = nullptr;
    uint8_t is_function_member : 1;

    MemberPointerLiteralExpr(
                             QualType ctype,
                             int64_t byte_offset,
                             bool is_function_member,
                             std::shared_ptr<Symbol> method_symbol = nullptr,
                             int32_t virtual_slot_index = -1,
                             const std::string* member_name = nullptr,
                             SrcLoc loc = SrcLoc())
        : Expr(StmtKind::MemberPointerLiteralExpr, loc),
          ctype(std::move(ctype)),
          byte_offset(byte_offset),
          method_symbol(std::move(method_symbol)),
          virtual_slot_index(virtual_slot_index),
          member_name(member_name),
          is_function_member(is_function_member ? 1 : 0) {}

    QualType get_type() override { return ctype; }
    bool isLValue() override { return false; }

    static bool classof(const Stmt* s) {
        return s->get_kind() == StmtKind::MemberPointerLiteralExpr;
    }
};

// Pointer-to-member access expression: obj.*pm or ptr->*pm.
struct MemberPointerAccessExpr : Expr {
    std::unique_ptr<Expr> base;
    std::unique_ptr<Expr> member_pointer;
    QualType result_type;
    uint8_t is_arrow : 1;
    uint8_t is_function_member : 1;

    MemberPointerAccessExpr(std::unique_ptr<Expr> base,
                            std::unique_ptr<Expr> member_pointer,
                            QualType result_type,
                            bool is_arrow,
                            bool is_function_member,
                            SrcLoc loc = SrcLoc())
        : Expr(StmtKind::MemberPointerAccessExpr, loc),
          base(std::move(base)),
          member_pointer(std::move(member_pointer)),
          result_type(std::move(result_type)),
          is_arrow(is_arrow ? 1 : 0),
          is_function_member(is_function_member ? 1 : 0) {}

    QualType get_type() override { return result_type; }
    bool isLValue() override { return !is_function_member; }

    static bool classof(const Stmt* s) {
        return s->get_kind() == StmtKind::MemberPointerAccessExpr;
    }
};

struct EnumConstantDecl: Decl {
    std::string name;
    std::unique_ptr<Expr> init; // Optional initializer
    std::shared_ptr<Symbol> sym;
    int64_t value;

    EnumConstantDecl(std::string name, std::unique_ptr<Expr> init, SrcLoc loc = SrcLoc())
        : Decl(DeclKind::EnumConstantDecl, loc), name(std::move(name)), init(std::move(init)), value(0) {}

    static bool classof(const Decl *d) { return d->get_kind() == DeclKind::EnumConstantDecl; }
};

struct EnumDecl: TagDecl {
    // Canonical enum semantics are declaration-owned via side-table metadata.
    std::string tag;
    std::vector<std::unique_ptr<EnumConstantDecl>> constants;

    EnumDecl(std::string tag, std::vector<std::unique_ptr<EnumConstantDecl>> constants,
             std::shared_ptr<CType> enum_type, SrcLoc loc = SrcLoc())
        : TagDecl(DeclKind::EnumDecl, loc), tag(std::move(tag)), constants(std::move(constants)) {
        set_tag_type(std::move(enum_type));
        bind_type_backref();
    }

    EnumDecl(std::string tag, std::shared_ptr<CType> enum_type, SrcLoc loc = SrcLoc())
        : TagDecl(DeclKind::EnumDecl, loc), tag(std::move(tag)) {
        set_tag_type(std::move(enum_type));
        bind_type_backref();
    }

    ~EnumDecl() override {
        enum_semantics_cache_erase(this);
    }

    bool is_complete_definition() const override {
        EnumSemanticState state;
        if (enum_semantics_cache_lookup(this,
                                        state,
                                        get_side_table_ast_context_for(this))) {
            return !state.is_incomplete;
        }
        return false;
    }

    const std::string& get_tag_name() const override { return tag; }
    std::shared_ptr<EnumType> get_enum_type() const {
        return dyn_cast_shared<EnumType>(get_tag_type());
    }
    bool is_scoped() const {
        auto enum_type = get_enum_type();
        return enum_type ? enum_type->isScoped() : false;
    }

    static bool classof(const Decl *d) { return d->get_kind() == DeclKind::EnumDecl; }

private:
    void bind_type_backref() {
        auto enm = get_enum_type();
        if (enm) {
            const TagDecl* current = enm->get_decl();
            if (!current) {
                enm->set_decl(this);
                return;
            }
            // Keep canonical backrefs stable across transient specifier decls.
            // Only promote an existing incomplete backref to a complete one.
            if (!current->is_complete_definition() && is_complete_definition()) {
                enm->set_decl(this);
            }
        }
    }
};

// CompoundLiteralExpr represents a compound literal (C99 6.5.2.5)
// Syntax: (type-name) { initializer-list }
// Example: (int) { 42 }, (struct point) { 1, 2 }, (int[]) { 1, 2, 3 }
//
// Key semantics:
// - A compound literal is an lvalue (can be modified, address taken)
// - Storage duration depends on context:
//   - At file scope: static storage duration
//   - At block scope: automatic storage duration (lifetime of enclosing block)
struct CompoundLiteralExpr : Expr {
    QualType type;           // The declared type
    std::unique_ptr<Expr> init;            // this has to be a InitListExpr
    uint8_t has_static_storage : 1;        // True if at file scope

    // Constructor
    CompoundLiteralExpr(QualType type, std::unique_ptr<Expr> init, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::CompoundLiteralExpr, loc), type(std::move(type)), init(std::move(init)), has_static_storage(false) {}

    QualType get_type() override {
        return type;
    }

    // Compound literals are lvalues (C99 6.5.2.5)
    bool isLValue() override {
        return true;
    }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::CompoundLiteralExpr; }
};

// SizeOfExpr represents the sizeof operator
// It can operate on either:
// 1. A type (sizeof(int), sizeof(struct foo))
// 2. An expression (sizeof x, sizeof *p)
//
// For expressions, the expression is NOT evaluated (except for VLAs).
// The size is determined from the type of the expression.
struct SizeOfExpr : Expr {
    // Exactly one of these will be set:
    QualType type_operand;      // For sizeof(type-name)
    std::unique_ptr<Expr> expr_operand;       // For sizeof expr

    // Cached result type (size_t, which is unsigned long)
    QualType result_type;

    // For VLAs: marks whether this sizeof requires runtime evaluation
    uint8_t is_runtime_sizeof : 1;

    // Constructor for sizeof(type-name)
    SizeOfExpr(QualType type, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::SizeOfExpr, loc), type_operand(std::move(type)), expr_operand(nullptr),
          is_runtime_sizeof(false) {}

    // Constructor for sizeof expr
    SizeOfExpr(std::unique_ptr<Expr> expr, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::SizeOfExpr, loc), type_operand(nullptr), expr_operand(std::move(expr)),
          is_runtime_sizeof(false) {}

    QualType get_type() override {
        return result_type;
    }

    // sizeof is never an lvalue
    bool isLValue() override { return false; }

    // Get the type being measured
    QualType getTargetType() const {
        if (type_operand) return type_operand;
        if (expr_operand) return expr_operand->get_type();
        return nullptr;
    }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::SizeOfExpr; }
};

struct SizeOfPackExpr : Expr {
    std::string pack_name;
    const TemplateParameterDecl* parameter_decl = nullptr;
    DeclKind parameter_kind = DeclKind::TemplateTypeParmDecl;
    uint32_t parameter_depth = 0;
    uint32_t parameter_index = 0;
    QualType result_type;

    SizeOfPackExpr(std::string pack_name,
                   const TemplateParameterDecl* parameter_decl,
                   SrcLoc loc = SrcLoc())
        : Expr(StmtKind::SizeOfPackExpr, loc),
          pack_name(std::move(pack_name)),
          parameter_decl(parameter_decl) {
        if (parameter_decl) {
            parameter_kind = parameter_decl->get_kind();
            parameter_depth = parameter_decl->depth;
            parameter_index = parameter_decl->index;
        }
    }

    QualType get_type() override { return result_type; }
    bool isLValue() override { return false; }

    bool matches_parameter(const TemplateParameterDecl* parameter) const {
        if (!parameter || !parameter->is_parameter_pack) {
            return false;
        }
        if (parameter_decl && parameter == parameter_decl) {
            return true;
        }
        if (parameter->get_kind() != parameter_kind ||
            parameter->depth != parameter_depth ||
            parameter->index != parameter_index) {
            return false;
        }
        return pack_name.empty() || parameter->name.empty() ||
               parameter->name == pack_name;
    }

    static bool classof(const Stmt *s) {
        return s->get_kind() == StmtKind::SizeOfPackExpr;
    }
};

struct StmtExpr : Expr {
    std::unique_ptr<CompoundStmt> compound_stmt;

    StmtExpr(std::unique_ptr<CompoundStmt> compound_stmt, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::StmtExpr, loc), compound_stmt(std::move(compound_stmt)) {}

    QualType get_type() override {
        // This will be set by Sema
        return type;
    }
    QualType type;

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::StmtExpr; }
};

// VaArgExpr represents __builtin_va_arg(ap, type)
struct VaArgExpr : Expr {
    std::unique_ptr<Expr> va_list_expr;
    QualType arg_type;

    VaArgExpr(std::unique_ptr<Expr> va_list_expr, QualType arg_type, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::VaArgExpr, loc), va_list_expr(std::move(va_list_expr)), arg_type(std::move(arg_type)) {}

    QualType get_type() override { return arg_type; }
    bool isLValue() override { return false; }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::VaArgExpr; }
};

// VaStartExpr represents __builtin_va_start(ap, last_named_param)
struct VaStartExpr : Expr {
    std::unique_ptr<Expr> va_list_expr;
    std::unique_ptr<Expr> last_param;

    VaStartExpr(std::unique_ptr<Expr> va_list_expr, std::unique_ptr<Expr> last_param,
                SrcLoc loc = SrcLoc())
        : Expr(StmtKind::VaStartExpr, loc), va_list_expr(std::move(va_list_expr)),
          last_param(std::move(last_param)) {}

    QualType get_type() override { return nullptr; }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::VaStartExpr; }
};

// VaEndExpr represents __builtin_va_end(ap)
struct VaEndExpr : Expr {
    std::unique_ptr<Expr> va_list_expr;

    VaEndExpr(std::unique_ptr<Expr> va_list_expr, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::VaEndExpr, loc), va_list_expr(std::move(va_list_expr)) {}

    QualType get_type() override { return nullptr; }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::VaEndExpr; }
};

// VaCopyExpr represents __builtin_va_copy(dest, src)
struct VaCopyExpr : Expr {
    std::unique_ptr<Expr> dest;
    std::unique_ptr<Expr> src;

    VaCopyExpr(std::unique_ptr<Expr> dest, std::unique_ptr<Expr> src, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::VaCopyExpr, loc), dest(std::move(dest)), src(std::move(src)) {}

    QualType get_type() override { return nullptr; }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::VaCopyExpr; }
};

// Represents a single operand in an extended asm statement
struct AsmOperand {
    std::string symbolic_name;   // Optional [name] -- empty if not provided
    std::string constraint;      // Constraint string, e.g. "=r", "+rm", "r", "0"
    std::unique_ptr<Expr> expr;  // The C expression (lvalue for outputs, any for inputs)
    SrcLoc loc;

    AsmOperand() = default;
    AsmOperand(std::string symbolic_name, std::string constraint,
               std::unique_ptr<Expr> expr, SrcLoc loc = SrcLoc())
        : symbolic_name(std::move(symbolic_name)),
          constraint(std::move(constraint)),
          expr(std::move(expr)), loc(loc) {}
};

// Asm statement -- covers both basic and extended inline asm
// Basic asm: has asm_template only, no operands/clobbers/labels
// Extended asm: has operands and/or clobbers and/or goto_labels
struct AsmStmt : Stmt {
    uint8_t is_volatile : 1;
    uint8_t is_inline : 1;
    uint8_t is_goto : 1;
    std::string asm_template;

    std::vector<AsmOperand> output_operands;
    std::vector<AsmOperand> input_operands;
    std::vector<std::string> clobbers;
    std::vector<std::string> goto_labels;

    // Parser sets this to true if any colon was seen (even if all lists are empty)
    uint8_t has_colon_syntax : 1;

    bool is_basic() const {
        return !has_colon_syntax;
    }

    AsmStmt(SrcLoc loc = SrcLoc()) : Stmt(StmtKind::AsmStmt, loc),
        is_volatile(false), is_inline(false), is_goto(false), has_colon_syntax(false) {}

    AsmStmt(std::string asm_template, bool is_volatile, bool is_inline, bool is_goto,
            bool has_colon_syntax, SrcLoc loc = SrcLoc())
        : Stmt(StmtKind::AsmStmt, loc),
          is_volatile(is_volatile), is_inline(is_inline), is_goto(is_goto),
          asm_template(std::move(asm_template)),
          has_colon_syntax(has_colon_syntax) {}

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::AsmStmt; }
};

// File-scope asm declaration (top-level asm outside functions)
// Emitted as module-level assembly in LLVM IR
struct FileScopeAsmDecl : Decl {
    std::string asm_string;

    FileScopeAsmDecl(std::string asm_string, SrcLoc loc = SrcLoc())
        : Decl(DeclKind::FileScopeAsmDecl, loc), asm_string(std::move(asm_string)) {}

    static bool classof(const Decl *d) { return d->get_kind() == DeclKind::FileScopeAsmDecl; }
};

// StaticAssertDecl represents _Static_assert(expr, "msg") or _Static_assert(expr)
struct StaticAssertDecl : Decl {
    std::unique_ptr<Expr> condition;
    std::string message;
    uint8_t has_message : 1;

    StaticAssertDecl(std::unique_ptr<Expr> condition, std::string message, bool has_message, SrcLoc loc = SrcLoc())
        : Decl(DeclKind::StaticAssertDecl, loc), condition(std::move(condition)), message(std::move(message)), has_message(has_message) {}

    static bool classof(const Decl *d) { return d->get_kind() == DeclKind::StaticAssertDecl; }
};

// AlignOfExpr represents _Alignof(type-name)
struct AlignOfExpr : Expr {
    QualType type_operand;
    std::unique_ptr<Expr> expr_operand; // For __alignof__(expr)
    QualType result_type;

    // Constructor for alignof(type-name)
    AlignOfExpr(QualType type, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::AlignOfExpr, loc), type_operand(std::move(type)), expr_operand(nullptr) {}

    // Constructor for __alignof__(expr)
    AlignOfExpr(std::unique_ptr<Expr> expr, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::AlignOfExpr, loc), type_operand(nullptr), expr_operand(std::move(expr)) {}

    QualType get_type() override { return result_type; }
    bool isLValue() override { return false; }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::AlignOfExpr; }
};
struct CppNoexceptExpr : Expr {
    std::unique_ptr<Expr> operand;
    QualType ctype;

    CppNoexceptExpr(std::unique_ptr<Expr> operand,
                    QualType ctype,
                    SrcLoc loc = SrcLoc())
        : Expr(StmtKind::CppNoexceptExpr, loc),
          operand(std::move(operand)),
          ctype(std::move(ctype)) {}

    QualType get_type() override { return ctype; }
    bool isLValue() override { return false; }

    static bool classof(const Stmt* s) {
        return s->get_kind() == StmtKind::CppNoexceptExpr;
    }
};

// GenericAssociation for _Generic expression
struct GenericAssociation {
    QualType type;              // nullptr for default
    std::unique_ptr<Expr> expr;
    uint8_t is_default : 1;
    SrcLoc loc;

    GenericAssociation() : is_default(false) {}
};

// GenericExpr represents _Generic(controlling-expr, type: expr, ...)
struct GenericExpr : Expr {
    std::unique_ptr<Expr> controlling_expr;
    std::vector<GenericAssociation> associations;
    size_t result_index = 0;    // set by sema
    QualType result_type;

    GenericExpr(std::unique_ptr<Expr> controlling, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::GenericExpr, loc), controlling_expr(std::move(controlling)) {}

    QualType get_type() override { return result_type; }
    bool isLValue() override { return false; }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::GenericExpr; }
};

// Component of an offsetof designator path (field access or array subscript)
struct OffsetOfComponent {
    std::string field_name;   // for .field access
    int64_t array_index = -1; // for [N] access, -1 means no array index
    std::unique_ptr<Expr> array_index_expr;
};

// OffsetOfExpr represents __builtin_offsetof(type, member)
struct OffsetOfExpr : Expr {
    QualType type_operand;
    std::string member_name;
    std::vector<OffsetOfComponent> designator_path; // extended path after member_name
    QualType result_type;
    int64_t computed_offset = -1; // set by sema

    OffsetOfExpr(QualType type, std::string member, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::OffsetOfExpr, loc), type_operand(std::move(type)), member_name(std::move(member)) {}

    QualType get_type() override { return result_type; }
    bool isLValue() override { return false; }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::OffsetOfExpr; }
};

// BuiltinCallExpr represents a generic __builtin_* call
// (va_* and offsetof builtins use their own dedicated AST nodes)
struct BuiltinCallExpr : Expr {
    BuiltinKind kind;
    std::vector<std::unique_ptr<Expr>> args;
    std::vector<QualType> type_args; // for builtins that take type arguments
    QualType result_type;
    std::optional<int64_t> const_value; // for compile-time constant builtins

    BuiltinCallExpr(BuiltinKind kind, std::vector<std::unique_ptr<Expr>> args,
                    QualType result_type, SrcLoc loc = SrcLoc())
        : Expr(StmtKind::BuiltinCallExpr, loc), kind(kind), args(std::move(args)),
          result_type(std::move(result_type)) {}

    BuiltinCallExpr(BuiltinKind kind, std::vector<std::unique_ptr<Expr>> args,
                    std::vector<QualType> type_args, QualType result_type,
                    SrcLoc loc = SrcLoc())
        : Expr(StmtKind::BuiltinCallExpr, loc), kind(kind), args(std::move(args)),
          type_args(std::move(type_args)), result_type(std::move(result_type)) {}

    QualType get_type() override { return result_type; }
    bool isLValue() override { return false; }

    static bool classof(const Stmt *s) { return s->get_kind() == StmtKind::BuiltinCallExpr; }
};

struct ConceptSpecializationExpr : Expr {
    const ConceptDecl* concept_decl = nullptr;
    std::string concept_name;
    std::vector<TemplateArgument> arguments;
    QualType result_type;
    std::optional<bool> satisfaction;

    ConceptSpecializationExpr(const ConceptDecl* concept_decl,
                              std::string concept_name,
                              std::vector<TemplateArgument> arguments,
                              QualType result_type,
                              SrcLoc loc = SrcLoc())
        : Expr(StmtKind::ConceptSpecializationExpr, loc),
          concept_decl(concept_decl),
          concept_name(std::move(concept_name)),
          arguments(std::move(arguments)),
          result_type(std::move(result_type)) {}

    QualType get_type() override { return result_type; }
    bool isLValue() override { return false; }

    static bool classof(const Stmt* s) {
        return s->get_kind() == StmtKind::ConceptSpecializationExpr;
    }
};

struct RequiresExpr : Expr {
    std::vector<std::unique_ptr<ParamDecl>> parameters;
    std::vector<ConstraintRequirement> requirements;
    QualType result_type;
    std::optional<bool> satisfaction;

    RequiresExpr(std::vector<std::unique_ptr<ParamDecl>> parameters,
                 std::vector<ConstraintRequirement> requirements,
                 QualType result_type,
                 SrcLoc loc = SrcLoc())
        : Expr(StmtKind::RequiresExpr, loc),
          parameters(std::move(parameters)),
          requirements(std::move(requirements)),
          result_type(std::move(result_type)) {}

    QualType get_type() override { return result_type; }
    bool isLValue() override { return false; }

    static bool classof(const Stmt* s) {
        return s->get_kind() == StmtKind::RequiresExpr;
    }
};

#endif //ABURI_AST_H
