#include "syntax_tree.h"

#include <algorithm>
#include <iomanip>
#include <ostream>
#include <sstream>
#include <variant>

namespace aburi::syntax {

std::string_view node_kind_name(NodeKind kind) {
    switch (kind) {
        case NodeKind::Invalid: return "Invalid";
        case NodeKind::TranslationUnit: return "TranslationUnit";
        case NodeKind::UnknownDecl: return "UnknownDecl";
        case NodeKind::FunctionDecl: return "FunctionDecl";
        case NodeKind::ParamDecl: return "ParamDecl";
        case NodeKind::VarDecl: return "VarDecl";
        case NodeKind::StructuredBindingDecl: return "StructuredBindingDecl";
        case NodeKind::StructuredBindingName: return "StructuredBindingName";
        case NodeKind::RecordDecl: return "RecordDecl";
        case NodeKind::FieldDecl: return "FieldDecl";
        case NodeKind::TypeName: return "TypeName";
        case NodeKind::Name: return "Name";
        case NodeKind::CompoundStmt: return "CompoundStmt";
        case NodeKind::ReturnStmt: return "ReturnStmt";
        case NodeKind::IfStmt: return "IfStmt";
        case NodeKind::WhileStmt: return "WhileStmt";
        case NodeKind::DoWhileStmt: return "DoWhileStmt";
        case NodeKind::ForStmt: return "ForStmt";
        case NodeKind::RangeForStmt: return "RangeForStmt";
        case NodeKind::ExpansionStmt: return "ExpansionStmt";
        case NodeKind::SwitchStmt: return "SwitchStmt";
        case NodeKind::CaseStmt: return "CaseStmt";
        case NodeKind::DefaultStmt: return "DefaultStmt";
        case NodeKind::LabelStmt: return "LabelStmt";
        case NodeKind::LocalLabelDeclStmt: return "LocalLabelDeclStmt";
        case NodeKind::GotoStmt: return "GotoStmt";
        case NodeKind::AsmStmt: return "AsmStmt";
        case NodeKind::BreakStmt: return "BreakStmt";
        case NodeKind::ContinueStmt: return "ContinueStmt";
        case NodeKind::ExprStmt: return "ExprStmt";
        case NodeKind::StmtExpr: return "StmtExpr";
        case NodeKind::BinaryExpr: return "BinaryExpr";
        case NodeKind::UnaryExpr: return "UnaryExpr";
        case NodeKind::ReflectExpr: return "ReflectExpr";
        case NodeKind::SpliceExpr: return "SpliceExpr";
        case NodeKind::ParenExpr: return "ParenExpr";
        case NodeKind::CastExpr: return "CastExpr";
        case NodeKind::ConditionalExpr: return "ConditionalExpr";
        case NodeKind::RequiresExpr: return "RequiresExpr";
        case NodeKind::CallExpr: return "CallExpr";
        case NodeKind::PackIndexExpr: return "PackIndexExpr";
        case NodeKind::ArraySubscriptExpr: return "ArraySubscriptExpr";
        case NodeKind::MemberExpr: return "MemberExpr";
        case NodeKind::InitListExpr: return "InitListExpr";
        case NodeKind::InitElementExpr: return "InitElementExpr";
        case NodeKind::Designator: return "Designator";
        case NodeKind::CompoundLiteralExpr: return "CompoundLiteralExpr";
        case NodeKind::GenericSelectionExpr: return "GenericSelectionExpr";
        case NodeKind::StaticAssertDecl: return "StaticAssertDecl";
        case NodeKind::BlockExpr: return "BlockExpr";
        case NodeKind::IntegerLiteral: return "IntegerLiteral";
        case NodeKind::BooleanLiteral: return "BooleanLiteral";
        case NodeKind::FloatingLiteral: return "FloatingLiteral";
        case NodeKind::CharacterLiteral: return "CharacterLiteral";
        case NodeKind::StringLiteral: return "StringLiteral";
        case NodeKind::Identifier: return "Identifier";
        case NodeKind::LinkageSpecDecl: return "LinkageSpecDecl";
        case NodeKind::NamespaceDecl: return "NamespaceDecl";
        case NodeKind::AmbiguousSyntax: return "AmbiguousSyntax";
        case NodeKind::DeferredBody: return "DeferredBody";
        case NodeKind::ThrowExpr: return "ThrowExpr";
        case NodeKind::TryStmt: return "TryStmt";
        case NodeKind::CatchClause: return "CatchClause";
        case NodeKind::DiscardedStmt: return "DiscardedStmt";
        case NodeKind::AwaitExpr: return "AwaitExpr";
        case NodeKind::YieldExpr: return "YieldExpr";
        case NodeKind::CoReturnStmt: return "CoReturnStmt";
        case NodeKind::ModuleDecl: return "ModuleDecl";
        case NodeKind::ExportDecl: return "ExportDecl";
        case NodeKind::ImportDecl: return "ImportDecl";
        case NodeKind::GlobalModuleFragment: return "GlobalModuleFragment";
        case NodeKind::PrivateModuleFragment: return "PrivateModuleFragment";
        case NodeKind::Error: return "Error";
    }
    return "UnknownNodeKind";
}

std::string_view floating_literal_kind_name(FloatingLiteralKind kind) {
    switch (kind) {
        case FloatingLiteralKind::Float: return "float";
        case FloatingLiteralKind::Double: return "double";
        case FloatingLiteralKind::LongDouble: return "long_double";
    }
    return "unknown";
}

std::string_view unary_operator_name(UnaryOperator op) {
    switch (op) {
        case UnaryOperator::Invalid: return "Invalid";
        case UnaryOperator::AddressOf: return "AddressOf";
        case UnaryOperator::Dereference: return "Dereference";
        case UnaryOperator::Plus: return "Plus";
        case UnaryOperator::Minus: return "Minus";
        case UnaryOperator::LogicalNot: return "LogicalNot";
        case UnaryOperator::BitwiseNot: return "BitwiseNot";
        case UnaryOperator::PrefixIncrement: return "PrefixIncrement";
        case UnaryOperator::PrefixDecrement: return "PrefixDecrement";
        case UnaryOperator::PostfixIncrement: return "PostfixIncrement";
        case UnaryOperator::PostfixDecrement: return "PostfixDecrement";
        case UnaryOperator::SizeofExpr: return "SizeofExpr";
        case UnaryOperator::SizeofType: return "SizeofType";
        case UnaryOperator::AlignofExpr: return "AlignofExpr";
        case UnaryOperator::AlignofType: return "AlignofType";
        case UnaryOperator::TypeidExpr: return "TypeidExpr";
        case UnaryOperator::TypeidType: return "TypeidType";
        case UnaryOperator::LabelAddress: return "LabelAddress";
    }
    return "UnknownUnaryOperator";
}

std::string_view binary_operator_name(BinaryOperator op) {
    switch (op) {
        case BinaryOperator::Invalid: return "Invalid";
        case BinaryOperator::Assign: return "Assign";
        case BinaryOperator::Add: return "Add";
        case BinaryOperator::Sub: return "Sub";
        case BinaryOperator::Mul: return "Mul";
        case BinaryOperator::Div: return "Div";
        case BinaryOperator::Mod: return "Mod";
        case BinaryOperator::Less: return "Less";
        case BinaryOperator::LessEqual: return "LessEqual";
        case BinaryOperator::Greater: return "Greater";
        case BinaryOperator::GreaterEqual: return "GreaterEqual";
        case BinaryOperator::Equal: return "Equal";
        case BinaryOperator::NotEqual: return "NotEqual";
        case BinaryOperator::ThreeWay: return "ThreeWay";
        case BinaryOperator::LogicalAnd: return "LogicalAnd";
        case BinaryOperator::LogicalOr: return "LogicalOr";
        case BinaryOperator::BitAnd: return "BitAnd";
        case BinaryOperator::BitOr: return "BitOr";
        case BinaryOperator::BitXor: return "BitXor";
        case BinaryOperator::Shl: return "Shl";
        case BinaryOperator::Shr: return "Shr";
        case BinaryOperator::PtrMemDot: return "PtrMemDot";
        case BinaryOperator::PtrMemArrow: return "PtrMemArrow";
        case BinaryOperator::Comma: return "Comma";
        case BinaryOperator::AssignAdd: return "AssignAdd";
        case BinaryOperator::AssignSub: return "AssignSub";
        case BinaryOperator::AssignMul: return "AssignMul";
        case BinaryOperator::AssignDiv: return "AssignDiv";
        case BinaryOperator::AssignMod: return "AssignMod";
        case BinaryOperator::AssignShl: return "AssignShl";
        case BinaryOperator::AssignShr: return "AssignShr";
        case BinaryOperator::AssignAnd: return "AssignAnd";
        case BinaryOperator::AssignXor: return "AssignXor";
        case BinaryOperator::AssignOr: return "AssignOr";
    }
    return "UnknownBinaryOperator";
}

std::string_view cast_operator_name(CastOperator op) {
    switch (op) {
        case CastOperator::Invalid: return "Invalid";
        case CastOperator::CStyle: return "CStyle";
        case CastOperator::CppStatic: return "CppStatic";
        case CastOperator::CppConst: return "CppConst";
        case CastOperator::CppReinterpret: return "CppReinterpret";
        case CastOperator::CppDynamic: return "CppDynamic";
    }
    return "UnknownCastOperator";
}

std::string_view unary_operator_spelling(UnaryOperator op) {
    switch (op) {
        case UnaryOperator::AddressOf: return "&";
        case UnaryOperator::Dereference: return "*";
        case UnaryOperator::Plus: return "+";
        case UnaryOperator::Minus: return "-";
        case UnaryOperator::LogicalNot: return "!";
        case UnaryOperator::BitwiseNot: return "~";
        case UnaryOperator::PrefixIncrement: return "++";
        case UnaryOperator::PrefixDecrement: return "--";
        case UnaryOperator::PostfixIncrement: return "++";
        case UnaryOperator::PostfixDecrement: return "--";
        case UnaryOperator::SizeofExpr: return "sizeof";
        case UnaryOperator::SizeofType: return "sizeof";
        case UnaryOperator::AlignofExpr: return "alignof";
        case UnaryOperator::AlignofType: return "alignof";
        case UnaryOperator::TypeidExpr: return "typeid";
        case UnaryOperator::TypeidType: return "typeid";
        case UnaryOperator::LabelAddress: return "&&";
        case UnaryOperator::Invalid: break;
    }
    return "";
}

std::string_view binary_operator_spelling(BinaryOperator op) {
    switch (op) {
        case BinaryOperator::Assign: return "=";
        case BinaryOperator::Add: return "+";
        case BinaryOperator::Sub: return "-";
        case BinaryOperator::Mul: return "*";
        case BinaryOperator::Div: return "/";
        case BinaryOperator::Mod: return "%";
        case BinaryOperator::Less: return "<";
        case BinaryOperator::LessEqual: return "<=";
        case BinaryOperator::Greater: return ">";
        case BinaryOperator::GreaterEqual: return ">=";
        case BinaryOperator::Equal: return "==";
        case BinaryOperator::NotEqual: return "!=";
        case BinaryOperator::ThreeWay: return "<=>";
        case BinaryOperator::LogicalAnd: return "&&";
        case BinaryOperator::LogicalOr: return "||";
        case BinaryOperator::BitAnd: return "&";
        case BinaryOperator::BitOr: return "|";
        case BinaryOperator::BitXor: return "^";
        case BinaryOperator::Shl: return "<<";
        case BinaryOperator::Shr: return ">>";
        case BinaryOperator::PtrMemDot: return ".*";
        case BinaryOperator::PtrMemArrow: return "->*";
        case BinaryOperator::Comma: return ",";
        case BinaryOperator::AssignAdd: return "+=";
        case BinaryOperator::AssignSub: return "-=";
        case BinaryOperator::AssignMul: return "*=";
        case BinaryOperator::AssignDiv: return "/=";
        case BinaryOperator::AssignMod: return "%=";
        case BinaryOperator::AssignShl: return "<<=";
        case BinaryOperator::AssignShr: return ">>=";
        case BinaryOperator::AssignAnd: return "&=";
        case BinaryOperator::AssignXor: return "^=";
        case BinaryOperator::AssignOr: return "|=";
        case BinaryOperator::Invalid: break;
    }
    return "";
}

const std::string& node_text(const Node& node) {
    static const std::string empty;
    if (const auto* payload = std::get_if<TextPayload>(&node.payload)) {
        return payload->text;
    }
    return empty;
}

bool node_has_text(const Node& node) {
    return !node_text(node).empty();
}

Tree::Tree() {
    nodes_.push_back(Node{});
}

NodeId Tree::add_node(NodeKind kind,
                      SrcLoc loc,
                      TokenSpan tokens,
                      std::span<const NodeId> children,
                      NodePayload payload,
                      uint16_t flags,
                      uint16_t opcode) {
    Node node;
    node.kind = kind;
    node.loc = loc;
    node.tokens = tokens;
    node.first_child = static_cast<uint32_t>(children_.size());
    node.child_count = static_cast<uint32_t>(children.size());
    node.flags = flags;
    node.opcode = opcode;
    node.payload = std::move(payload);
    for (NodeId child : children) {
        children_.push_back(child);
    }
    nodes_.push_back(std::move(node));
    return static_cast<NodeId>(nodes_.size() - 1);
}

void Tree::set_root(NodeId root) {
    root_ = root;
}

Tree::Checkpoint Tree::checkpoint() const {
    return Checkpoint{nodes_.size(), children_.size(), root_};
}

void Tree::rollback_to(Checkpoint checkpoint) {
    if (checkpoint.node_count == 0 || checkpoint.node_count > nodes_.size()) {
        return;
    }
    nodes_.resize(checkpoint.node_count);
    children_.resize(std::min(checkpoint.child_count, children_.size()));
    root_ = checkpoint.root;
}

const Node& Tree::node(NodeId id) const {
    if (!valid(id)) {
        return nodes_[InvalidNodeId];
    }
    return nodes_[id];
}

std::span<const NodeId> Tree::children(NodeId id) const {
    const Node& n = node(id);
    if (n.child_count == 0 || n.first_child >= children_.size()) {
        return {};
    }
    return std::span<const NodeId>(children_.data() + n.first_child, n.child_count);
}

bool Tree::valid(NodeId id) const {
    return id != InvalidNodeId && id < nodes_.size();
}

bool Tree::verify(std::ostream* err) const {
    bool ok = true;
    auto fail = [&](const std::string& message) {
        ok = false;
        if (err) {
            *err << "syntax tree verification failed: " << message << '\n';
        }
    };

    if (!valid(root_)) {
        fail("root is invalid");
    }
    for (NodeId id = 1; id < nodes_.size(); ++id) {
        const Node& n = nodes_[id];
        if (n.first_child > children_.size() ||
            n.first_child + n.child_count > children_.size()) {
            fail("child range is out of bounds for node " + std::to_string(id));
            continue;
        }
        if (n.tokens.end < n.tokens.begin) {
            fail("token span is inverted for node " + std::to_string(id));
        }
        for (NodeId child : children(id)) {
            if (!valid(child)) {
                fail("child id is invalid for node " + std::to_string(id));
            }
        }
    }
    return ok;
}

static std::string flags_to_string(uint16_t flags) {
    std::ostringstream out;
    bool first = true;
    auto add = [&](std::string_view name) {
        if (!first) {
            out << '|';
        }
        first = false;
        out << name;
    };
    if (flags & NodeFlagHasError) add("has_error");
    if (flags & NodeFlagAmbiguous) add("ambiguous");
    if (flags & NodeFlagDeferred) add("deferred");
    if (flags & NodeFlagFromMacro) add("from_macro");
    return out.str();
}

static void append_hex_escape(std::ostream& out, unsigned char byte) {
    static const char kHex[] = "0123456789ABCDEF";
    out << "\\x" << kHex[(byte >> 4) & 0xF] << kHex[byte & 0xF];
}

static void dump_escaped_string(std::ostream& out, std::string_view text) {
    for (unsigned char c : text) {
        switch (c) {
            case '\n': out << "\\n"; break;
            case '\r': out << "\\r"; break;
            case '\t': out << "\\t"; break;
            case '\\': out << "\\\\"; break;
            case '"': out << "\\\""; break;
            default:
                if (c < 0x20 || c >= 0x7F) {
                    append_hex_escape(out, c);
                } else {
                    out << static_cast<char>(c);
                }
                break;
        }
    }
}

static void dump_payload(std::ostream& out, const NodePayload& payload) {
    struct Visitor {
        std::ostream& out;

        void operator()(const std::monostate&) const {}

        void operator()(const TextPayload& payload) const {
            if (payload.text.empty()) {
                return;
            }
            out << " text=\"";
            dump_escaped_string(out, payload.text);
            out << '"';
        }

        void operator()(const IntegerLiteralPayload& payload) const {
            out << " payload=integer value=" << payload.value;
            if (!payload.spelling.empty()) {
                out << " spelling=\"";
                dump_escaped_string(out, payload.spelling);
                out << '"';
            }
            if (!payload.suffix.empty()) {
                out << " suffix=\"";
                dump_escaped_string(out, payload.suffix);
                out << '"';
            }
        }

        void operator()(const BooleanLiteralPayload& payload) const {
            out << " payload=bool value=" << (payload.value ? "true" : "false");
            if (!payload.spelling.empty()) {
                out << " spelling=\"";
                dump_escaped_string(out, payload.spelling);
                out << '"';
            }
        }

        void operator()(const FloatingLiteralPayload& payload) const {
            out << " payload=float kind=" << floating_literal_kind_name(payload.kind);
            if (!payload.spelling.empty()) {
                out << " spelling=\"";
                dump_escaped_string(out, payload.spelling);
                out << '"';
            }
            if (!payload.suffix.empty()) {
                out << " suffix=\"";
                dump_escaped_string(out, payload.suffix);
                out << '"';
            }
        }

        void operator()(const CharacterLiteralPayload& payload) const {
            out << " payload=char value=" << payload.value;
            if (!payload.decoded.empty()) {
                out << " decoded=\"";
                dump_escaped_string(out, payload.decoded);
                out << '"';
            }
            if (!payload.spelling.empty()) {
                out << " spelling=\"";
                dump_escaped_string(out, payload.spelling);
                out << '"';
            }
            if (!payload.suffix.empty()) {
                out << " suffix=\"";
                dump_escaped_string(out, payload.suffix);
                out << '"';
            }
        }

        void operator()(const StringLiteralPayload& payload) const {
            out << " payload=string";
            out << " decoded=\"";
            dump_escaped_string(out, payload.decoded);
            out << '"';
            if (!payload.spelling.empty()) {
                out << " spelling=\"";
                dump_escaped_string(out, payload.spelling);
                out << '"';
            }
            if (!payload.suffix.empty()) {
                out << " suffix=\"";
                dump_escaped_string(out, payload.suffix);
                out << '"';
            }
        }
    };

    std::visit(Visitor{out}, payload);
}

void Tree::dump(std::ostream& out, const std::vector<Token>& tokens) const {
    if (!valid(root_)) {
        out << "<invalid syntax tree>\n";
        return;
    }
    dump_node(out, tokens, root_, 0);
}

void Tree::dump_node(std::ostream& out,
                     const std::vector<Token>& tokens,
                     NodeId id,
                     unsigned indent) const {
    const Node& n = node(id);
    out << std::string(indent, ' ') << node_kind_name(n.kind) << " #" << id;
    out << " loc=" << n.loc.offset;
    out << " tokens=[" << n.tokens.begin << "," << n.tokens.end << ")";
    dump_payload(out, n.payload);
    if (n.kind == NodeKind::UnaryExpr && n.opcode != 0) {
        out << " op=" << unary_operator_name(static_cast<UnaryOperator>(n.opcode));
    }
    if (n.kind == NodeKind::BinaryExpr && n.opcode != 0) {
        out << " op=" << binary_operator_name(static_cast<BinaryOperator>(n.opcode));
    }
    if (n.kind == NodeKind::CastExpr && n.opcode != 0) {
        out << " op=" << cast_operator_name(static_cast<CastOperator>(n.opcode));
    }
    if (n.flags != NodeFlagNone) {
        out << " flags=" << flags_to_string(n.flags);
    }
    if (n.tokens.begin < n.tokens.end && n.tokens.begin < tokens.size()) {
        out << " first_token=" << token_type_to_string(tokens[n.tokens.begin].type);
    }
    out << '\n';

    for (NodeId child : children(id)) {
        dump_node(out, tokens, child, indent + 2);
    }
}

} // namespace aburi::syntax
