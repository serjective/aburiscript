#ifndef ABURI_ATTRIBUTES_H
#define ABURI_ATTRIBUTES_H

#include <string>
#include <vector>
#include <unordered_map>
#include <cstdint>
#include <memory>
#include "source_mgnt.h"

struct Expr;

// What kind of entity can this attribute be applied to?
enum class AttributeTarget : uint16_t {
    NONE          = 0x0000,
    FUNCTION      = 0x0001,
    VARIABLE      = 0x0002,
    TYPE          = 0x0004,
    FIELD         = 0x0008,
    LABEL         = 0x0010,
    ENUMERATOR    = 0x0020,
    STATEMENT     = 0x0040,
    PARAMETER     = 0x0080,
    FUNC_OR_VAR   = 0x0003,
    ANY_DECL      = 0x00FF,
    ALL           = 0xFFFF,
};

inline AttributeTarget operator|(AttributeTarget a, AttributeTarget b) {
    return static_cast<AttributeTarget>(
        static_cast<uint16_t>(a) | static_cast<uint16_t>(b));
}
inline bool operator&(AttributeTarget a, AttributeTarget b) {
    return (static_cast<uint16_t>(a) & static_cast<uint16_t>(b)) != 0;
}

// Attribute argument: can be an identifier, integer constant, string, or expression
struct AttributeArg {
    enum class Kind { IDENTIFIER, INTEGER, STRING, FLOAT, KEY_VALUE, EXPR };
    Kind kind;
    std::string str_value;
    std::string key;
    int64_t int_value = 0;
    double float_value = 0.0;
    std::shared_ptr<Expr> expr_value;
    SrcLoc loc;

    AttributeArg() : kind(Kind::IDENTIFIER), int_value(0), float_value(0.0) {}

    static AttributeArg make_ident(const std::string& name, SrcLoc loc = SrcLoc()) {
        AttributeArg a;
        a.kind = Kind::IDENTIFIER;
        a.str_value = name;
        a.loc = loc;
        return a;
    }
    static AttributeArg make_int(int64_t val, SrcLoc loc = SrcLoc()) {
        AttributeArg a;
        a.kind = Kind::INTEGER;
        a.int_value = val;
        a.loc = loc;
        return a;
    }
    static AttributeArg make_string(const std::string& s, SrcLoc loc = SrcLoc()) {
        AttributeArg a;
        a.kind = Kind::STRING;
        a.str_value = s;
        a.loc = loc;
        return a;
    }
    static AttributeArg make_float(const std::string& s, double val, SrcLoc loc = SrcLoc()) {
        AttributeArg a;
        a.kind = Kind::FLOAT;
        a.str_value = s;
        a.float_value = val;
        a.loc = loc;
        return a;
    }
    static AttributeArg make_key_value(const std::string& k, const std::string& v, SrcLoc loc = SrcLoc()) {
        AttributeArg a;
        a.kind = Kind::KEY_VALUE;
        a.key = k;
        a.str_value = v;
        a.loc = loc;
        return a;
    }
    static AttributeArg make_expr(std::shared_ptr<Expr> expr, SrcLoc loc = SrcLoc()) {
        AttributeArg a;
        a.kind = Kind::EXPR;
        a.expr_value = std::move(expr);
        a.loc = loc;
        return a;
    }
};

// Known attribute IDs for fast switching in sema/codegen
enum class AttributeKind {
    UNKNOWN,

    // Function attributes
    NORETURN,
    NOINLINE,
    ALWAYS_INLINE,
    PURE,
    CONST_ATTR,
    COLD,
    HOT,
    NOTHROW,
    MALLOC_ATTR,
    ALLOC_SIZE,
    FLATTEN,
    FORCE_ALIGN_ARG_POINTER,
    OPTIMIZE_ATTR,
    WARN_UNUSED_RESULT,
    FORMAT,
    NONNULL,
    RETURNS_NONNULL,
    CONSTRUCTOR,
    DESTRUCTOR,

    // Variable attributes
    CLEANUP,
    COMMON_ATTR,

    // Type attributes
    PACKED,
    TRANSPARENT_UNION,
    DESIGNATED_INIT,
    MAY_ALIAS,
    VECTOR_SIZE,

    // Shared attributes (apply to multiple targets)
    UNUSED,
    USED,
    DEPRECATED,
    UNAVAILABLE,
    AVAILABILITY,
    ALIGNED,
    SECTION,
    VISIBILITY,
    TYPE_VISIBILITY,
    WEAK,
    ABI_TAG,
    NODEBUG,
    EXCLUDE_FROM_EXPLICIT_INSTANTIATION,
    GLOBAL_ATTR,
    DEVICE_ATTR,
    DEVICE_BUILTIN_ATTR,

    // Statement attributes
    FALLTHROUGH,

    // C23 standard attributes
    NODISCARD,
    MAYBE_UNUSED,

    // Objective-C (future)
    OBJC_ROOT_CLASS,
    OBJC_DESIGNATED_INITIALIZER,
};

// A parsed attribute as it comes out of the parser
struct ParsedAttribute {
    std::string ns;
    std::string name;
    std::vector<AttributeArg> args;
    SrcLoc loc;
    AttributeKind resolved_kind = AttributeKind::UNKNOWN;

    // Strip leading/trailing __ from name for matching
    std::string canonical_name() const {
        std::string n = name;
        if (n.size() >= 4 && n.substr(0, 2) == "__" && n.substr(n.size() - 2) == "__") {
            n = n.substr(2, n.size() - 4);
        }
        return n;
    }
};

// Collection of parsed attributes attached to an AST node
struct AttributeList {
    std::vector<ParsedAttribute> attrs;

    bool empty() const { return attrs.empty(); }
    size_t size() const { return attrs.size(); }

    bool has(AttributeKind kind) const {
        for (const auto& a : attrs) {
            if (a.resolved_kind == kind) return true;
        }
        return false;
    }

    const ParsedAttribute* find(AttributeKind kind) const {
        for (const auto& a : attrs) {
            if (a.resolved_kind == kind) return &a;
        }
        return nullptr;
    }

    void append(std::vector<ParsedAttribute>&& other) {
        attrs.insert(attrs.end(),
            std::make_move_iterator(other.begin()),
            std::make_move_iterator(other.end()));
    }
};

// Registry entry describing an attribute's properties
struct AttributeDescriptor {
    AttributeKind kind;
    std::string name;
    AttributeTarget valid_targets;
    int min_args;
    int max_args;  // -1 = unlimited
    bool is_c23_standard;
    bool is_type_attribute;
};

// Singleton registry mapping attribute names to descriptors
class AttributeRegistry {
public:
    static AttributeRegistry& instance();

    void register_attribute(const AttributeDescriptor& desc);
    const AttributeDescriptor* find(const std::string& canonical_name) const;
    const AttributeDescriptor* find_by_kind(AttributeKind kind) const;

private:
    AttributeRegistry();
    std::unordered_map<std::string, AttributeDescriptor> by_name;
    std::unordered_map<int, AttributeDescriptor> by_kind;
};

#endif // ABURI_ATTRIBUTES_H
