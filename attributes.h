#ifndef ABURI_ATTRIBUTES_H
#define ABURI_ATTRIBUTES_H

#include "source_mgnt.h"

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

namespace aburi {

enum class AttributeTarget : uint16_t {
    None = 0x0000,
    Function = 0x0001,
    Variable = 0x0002,
    Type = 0x0004,
    Field = 0x0008,
    Label = 0x0010,
    Enumerator = 0x0020,
    Statement = 0x0040,
    Parameter = 0x0080,
    Concept = 0x0100,
    AnyDecl = 0x01ff,
    All = 0xffff,
};

inline AttributeTarget operator|(AttributeTarget lhs, AttributeTarget rhs) {
    return static_cast<AttributeTarget>(
        static_cast<uint16_t>(lhs) | static_cast<uint16_t>(rhs));
}

inline AttributeTarget& operator|=(AttributeTarget& lhs, AttributeTarget rhs) {
    lhs = lhs | rhs;
    return lhs;
}

inline bool attribute_target_contains(AttributeTarget mask, AttributeTarget target) {
    return (static_cast<uint16_t>(mask) & static_cast<uint16_t>(target)) != 0;
}

enum class AttributeSyntax : uint8_t {
    GNU,
    Standard,
    Alignas,
    Keyword
};

enum class AttributeKind : uint8_t {
    Unknown,
    ObjCFamily,
    NoReturn,
    NoInstrumentFunction,
    AssumeAligned,
    NoInline,
    AlwaysInline,
    Pure,
    Const,
    Cold,
    Hot,
    NoThrow,
    Malloc,
    AllocSize,
    Flatten,
    ForceAlignArgPointer,
    Optimize,
    WarnUnusedResult,
    Format,
    FormatArg,
    NonNull,
    ReturnsNonNull,
    Constructor,
    Destructor,
    Cleanup,
    Common,
    Packed,
    TransparentUnion,
    DesignatedInit,
    MayAlias,
    VectorSize,
    ExtVectorType,
    NeonVectorType,
    Mode,
    Unused,
    Used,
    Deprecated,
    Unavailable,
    Availability,
    Aligned,
    Section,
    Visibility,
    TypeVisibility,
    Weak,
    WeakRef,
    Alias,
    Ifunc,
    GnuInline,
    AbiTag,
    NoDebug,
    ExcludeFromExplicitInstantiation,
    Global,
    Device,
    DeviceBuiltin,
    Fallthrough,
    NoDiscard,
    MaybeUnused,
    NoUniqueAddress
};

struct AttributeArg {
    enum class Kind : uint8_t {
        Identifier,
        Integer,
        String,
        Float,
        KeyValue,
        TokenText
    };

    Kind kind = Kind::Identifier;
    std::string value;
    std::string key;
    int64_t int_value = 0;
    long double float_value = 0.0;
    uint32_t dependent_value_param_index = UINT32_MAX;
    SrcLoc loc{};

    static AttributeArg identifier(std::string value, SrcLoc loc = SrcLoc());
    static AttributeArg integer(int64_t value, SrcLoc loc = SrcLoc());
    static AttributeArg string(std::string value, SrcLoc loc = SrcLoc());
    static AttributeArg floating(std::string spelling,
                                 long double value,
                                 SrcLoc loc = SrcLoc());
    static AttributeArg key_value(std::string key,
                                  std::string value,
                                  SrcLoc loc = SrcLoc());
    static AttributeArg token_text(std::string value, SrcLoc loc = SrcLoc());
};

struct ParsedAttribute {
    std::string ns;
    std::string name;
    std::vector<AttributeArg> args;
    SrcLoc loc{};
    AttributeSyntax syntax = AttributeSyntax::GNU;
    AttributeKind kind = AttributeKind::Unknown;

    std::string canonical_name() const;
};

struct AttributeList {
    std::vector<ParsedAttribute> attrs;

    bool empty() const { return attrs.empty(); }
    size_t size() const { return attrs.size(); }
    void append(AttributeList other);
    void append(std::vector<ParsedAttribute> other);
    bool has(AttributeKind kind) const;
    const ParsedAttribute* find(AttributeKind kind) const;
};

struct AttributeDescriptor {
    AttributeKind kind = AttributeKind::Unknown;
    std::string name;
    AttributeTarget targets = AttributeTarget::None;
    int min_args = 0;
    int max_args = 0;
    bool standard = false;
    bool type_attribute = false;
    bool active_support = false;
};

class AttributeRegistry {
public:
    static const AttributeRegistry& instance();

    const AttributeDescriptor* find(std::string_view canonical_name) const;
    const AttributeDescriptor* find(AttributeKind kind) const;
    bool is_active(std::string_view canonical_name) const;
    bool is_standard(std::string_view canonical_name) const;

private:
    AttributeRegistry();
    void register_attribute(AttributeDescriptor descriptor);

    std::unordered_map<std::string, AttributeDescriptor> by_name_;
    std::unordered_map<uint8_t, AttributeDescriptor> by_kind_;
};

std::string canonicalize_attribute_name(std::string_view name);
std::string_view attribute_kind_name(AttributeKind kind);

} // namespace aburi

#endif // ABURI_ATTRIBUTES_H
