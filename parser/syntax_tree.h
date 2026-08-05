#ifndef ABURI_SYNTAX_TREE_H
#define ABURI_SYNTAX_TREE_H

#include <cstddef>
#include <cstdint>
#include <iosfwd>
#include <span>
#include <string>
#include <string_view>
#include <variant>
#include <vector>

#include "../lexer.h"
#include "../source_mgnt.h"

namespace aburi::syntax {

using NodeId = uint32_t;
constexpr NodeId InvalidNodeId = 0;

enum class NodeKind : uint16_t {
    Invalid,
    TranslationUnit,
    UnknownDecl,
    FunctionDecl,
    ParamDecl,
    VarDecl,
    StructuredBindingDecl,
    StructuredBindingName,
    RecordDecl,
    FieldDecl,
    TypeName,
    Name,
    CompoundStmt,
    ReturnStmt,
    IfStmt,
    WhileStmt,
    DoWhileStmt,
    ForStmt,
    RangeForStmt,
    ExpansionStmt,
    SwitchStmt,
    CaseStmt,
    DefaultStmt,
    LabelStmt,
    LocalLabelDeclStmt,
    GotoStmt,
    AsmStmt,
    BreakStmt,
    ContinueStmt,
    ExprStmt,
    StmtExpr,
    BinaryExpr,
    UnaryExpr,
    ReflectExpr,
    SpliceExpr,
    ParenExpr,
    CastExpr,
    ConditionalExpr,
    RequiresExpr,
    CallExpr,
    PackIndexExpr,
    ArraySubscriptExpr,
    MemberExpr,
    InitListExpr,
    InitElementExpr,
    Designator,
    CompoundLiteralExpr,
    GenericSelectionExpr,
    StaticAssertDecl,
    BlockExpr,
    LambdaExpr,
    IntegerLiteral,
    BooleanLiteral,
    FloatingLiteral,
    CharacterLiteral,
    StringLiteral,
    Identifier,
    LinkageSpecDecl,
    NamespaceDecl,
    AmbiguousSyntax,
    DeferredBody,
    ThrowExpr,
    TryStmt,
    CatchClause,
    DiscardedStmt,
    AwaitExpr,
    YieldExpr,
    CoReturnStmt,
    ModuleDecl,
    ExportDecl,
    ImportDecl,
    GlobalModuleFragment,
    PrivateModuleFragment,
    ObjCClassForwardDecl,
    ObjCInterfaceDecl,
    ObjCImplementationDecl,
    ObjCMethodDecl,
    ObjCIvarDecl,
    ObjCMessageExpr,
    ObjCSelectorExpr,
    ObjCStringLiteral,
    ObjCBoxedExpr,
    ObjCArrayLiteral,
    ObjCDictionaryLiteral,
    Error
};

enum class UnaryOperator : uint16_t {
    Invalid,
    AddressOf,
    Dereference,
    Plus,
    Minus,
    LogicalNot,
    BitwiseNot,
    PrefixIncrement,
    PrefixDecrement,
    PostfixIncrement,
    PostfixDecrement,
    SizeofExpr,
    SizeofType,
    AlignofExpr,
    AlignofType,
    TypeidExpr,
    TypeidType,
    LabelAddress,
    // The [expr.await] lookup invariant stores operator co_await identity
    // separately because ordinary expression syntax never produces it.
    CoAwait
};

enum class BinaryOperator : uint16_t {
    Invalid,
    Assign,
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
    ThreeWay,
    LogicalAnd,
    LogicalOr,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    PtrMemDot,
    PtrMemArrow,
    Comma,
    AssignAdd,
    AssignSub,
    AssignMul,
    AssignDiv,
    AssignMod,
    AssignShl,
    AssignShr,
    AssignAnd,
    AssignXor,
    AssignOr
};

enum class CastOperator : uint16_t {
    Invalid,
    CStyle,
    CppStatic,
    CppConst,
    CppReinterpret,
    CppDynamic
};

enum NodeFlags : uint16_t {
    NodeFlagNone = 0,
    NodeFlagHasError = 1u << 0,
    NodeFlagAmbiguous = 1u << 1,
    NodeFlagDeferred = 1u << 2,
    NodeFlagFromMacro = 1u << 3
};

struct TokenSpan {
    size_t begin = 0;
    size_t end = 0;
};

enum class FloatingLiteralKind : uint8_t {
    Float,
    Double,
    LongDouble
};

struct TextPayload {
    std::string text;
};

struct IntegerLiteralPayload {
    int64_t value = 0;
    std::string spelling;
    std::string suffix;
};

struct BooleanLiteralPayload {
    bool value = false;
    std::string spelling;
};

struct FloatingLiteralPayload {
    FloatingLiteralKind kind = FloatingLiteralKind::Double;
    std::string spelling;
    std::string suffix;
};

struct CharacterLiteralPayload {
    int64_t value = 0;
    LiteralPrefix prefix = LiteralPrefix::None;
    std::string decoded;
    std::string spelling;
    std::string suffix;
};

struct StringLiteralPayload {
    LiteralPrefix prefix = LiteralPrefix::None;
    std::string decoded;
    std::string spelling;
    std::string suffix;
};

using NodePayload = std::variant<std::monostate,
                                 TextPayload,
                                 IntegerLiteralPayload,
                                 BooleanLiteralPayload,
                                 FloatingLiteralPayload,
                                 CharacterLiteralPayload,
                                 StringLiteralPayload>;

struct Node {
    NodeKind kind = NodeKind::Invalid;
    SrcLoc loc{};
    TokenSpan tokens{};
    uint32_t first_child = 0;
    uint32_t child_count = 0;
    uint16_t flags = NodeFlagNone;
    uint16_t opcode = 0;
    NodePayload payload;
};

std::string_view node_kind_name(NodeKind kind);
std::string_view floating_literal_kind_name(FloatingLiteralKind kind);
std::string_view unary_operator_name(UnaryOperator op);
std::string_view binary_operator_name(BinaryOperator op);
std::string_view cast_operator_name(CastOperator op);
std::string_view unary_operator_spelling(UnaryOperator op);
std::string_view binary_operator_spelling(BinaryOperator op);
const std::string& node_text(const Node& node);
bool node_has_text(const Node& node);

class Tree {
public:
    struct Checkpoint {
        size_t node_count = 0;
        size_t child_count = 0;
        NodeId root = InvalidNodeId;
    };

    Tree();

    NodeId add_node(NodeKind kind,
                    SrcLoc loc,
                    TokenSpan tokens,
                    std::span<const NodeId> children = {},
                    NodePayload payload = {},
                    uint16_t flags = NodeFlagNone,
                    uint16_t opcode = 0);

    void set_root(NodeId root);
    NodeId root() const { return root_; }

    const Node& node(NodeId id) const;
    std::span<const NodeId> children(NodeId id) const;
    size_t node_count() const { return nodes_.size() - 1; }

    Checkpoint checkpoint() const;
    void rollback_to(Checkpoint checkpoint);

    bool valid(NodeId id) const;
    bool verify(std::ostream* err = nullptr) const;
    void dump(std::ostream& out, const std::vector<Token>& tokens) const;

private:
    void dump_node(std::ostream& out,
                   const std::vector<Token>& tokens,
                   NodeId id,
                   unsigned indent) const;

    std::vector<Node> nodes_;
    std::vector<NodeId> children_;
    NodeId root_ = InvalidNodeId;
};

} // namespace aburi::syntax

#endif // ABURI_SYNTAX_TREE_H
