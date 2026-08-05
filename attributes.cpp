#include "attributes.h"

#include <algorithm>

namespace aburi {

AttributeArg AttributeArg::identifier(std::string value, SrcLoc loc) {
    AttributeArg arg;
    arg.kind = Kind::Identifier;
    arg.value = std::move(value);
    arg.loc = loc;
    return arg;
}

AttributeArg AttributeArg::integer(int64_t value, SrcLoc loc) {
    AttributeArg arg;
    arg.kind = Kind::Integer;
    arg.int_value = value;
    arg.loc = loc;
    return arg;
}

AttributeArg AttributeArg::string(std::string value, SrcLoc loc) {
    AttributeArg arg;
    arg.kind = Kind::String;
    arg.value = std::move(value);
    arg.loc = loc;
    return arg;
}

AttributeArg AttributeArg::floating(std::string spelling,
                                    long double value,
                                    SrcLoc loc) {
    AttributeArg arg;
    arg.kind = Kind::Float;
    arg.value = std::move(spelling);
    arg.float_value = value;
    arg.loc = loc;
    return arg;
}

AttributeArg AttributeArg::key_value(std::string key,
                                     std::string value,
                                     SrcLoc loc) {
    AttributeArg arg;
    arg.kind = Kind::KeyValue;
    arg.key = std::move(key);
    arg.value = std::move(value);
    arg.loc = loc;
    return arg;
}

AttributeArg AttributeArg::token_text(std::string value, SrcLoc loc) {
    AttributeArg arg;
    arg.kind = Kind::TokenText;
    arg.value = std::move(value);
    arg.loc = loc;
    return arg;
}

std::string canonicalize_attribute_name(std::string_view name) {
    std::string result(name);
    while (result.size() >= 4 &&
           result.starts_with("__") &&
           result.ends_with("__")) {
        result = result.substr(2, result.size() - 4);
    }
    return result;
}

std::string ParsedAttribute::canonical_name() const {
    return canonicalize_attribute_name(name);
}

void AttributeList::append(AttributeList other) {
    append(std::move(other.attrs));
}

void AttributeList::append(std::vector<ParsedAttribute> other) {
    attrs.insert(attrs.end(),
                 std::make_move_iterator(other.begin()),
                 std::make_move_iterator(other.end()));
}

bool AttributeList::has(AttributeKind kind) const {
    return std::any_of(attrs.begin(), attrs.end(), [&](const ParsedAttribute& attr) {
        return attr.kind == kind;
    });
}

const ParsedAttribute* AttributeList::find(AttributeKind kind) const {
    for (const ParsedAttribute& attr : attrs) {
        if (attr.kind == kind) {
            return &attr;
        }
    }
    return nullptr;
}

const AttributeRegistry& AttributeRegistry::instance() {
    static const AttributeRegistry registry;
    return registry;
}

void AttributeRegistry::register_attribute(AttributeDescriptor descriptor) {
    by_kind_[static_cast<uint8_t>(descriptor.kind)] = descriptor;
    by_name_[descriptor.name] = std::move(descriptor);
}

const AttributeDescriptor* AttributeRegistry::find(std::string_view canonical_name) const {
    auto it = by_name_.find(std::string(canonical_name));
    return it == by_name_.end() ? nullptr : &it->second;
}

const AttributeDescriptor* AttributeRegistry::find(AttributeKind kind) const {
    auto it = by_kind_.find(static_cast<uint8_t>(kind));
    return it == by_kind_.end() ? nullptr : &it->second;
}

bool AttributeRegistry::is_active(std::string_view canonical_name) const {
    if (const AttributeDescriptor* desc = find(canonical_name)) {
        return desc->active_support;
    }
    return false;
}

bool AttributeRegistry::is_standard(std::string_view canonical_name) const {
    if (const AttributeDescriptor* desc = find(canonical_name)) {
        return desc->standard;
    }
    return false;
}

AttributeRegistry::AttributeRegistry() {
    auto fn = AttributeTarget::Function;
    auto var = AttributeTarget::Variable;
    auto type = AttributeTarget::Type;
    auto field = AttributeTarget::Field;
    auto label = AttributeTarget::Label;
    auto stmt = AttributeTarget::Statement;
    auto param = AttributeTarget::Parameter;
    auto func_or_var = fn | var;

    register_attribute({AttributeKind::NoReturn, "noreturn", fn | var | type | field, 0, 0, true, false, true});
    register_attribute({AttributeKind::NoInstrumentFunction, "no_instrument_function", fn, 0, 0, false, false, true});
    register_attribute({AttributeKind::AssumeAligned, "assume_aligned", fn, 1, 2, false, false, false});
    register_attribute({AttributeKind::Unused, "unused", AttributeTarget::All, 0, 0, true, false, true});
    register_attribute({AttributeKind::Deprecated, "deprecated", AttributeTarget::AnyDecl, 0, 1, true, false, true});
    register_attribute({AttributeKind::Aligned, "aligned", var | type | field | fn | param, 0, 1, false, true, true});
    register_attribute({AttributeKind::Packed, "packed", type | field | var, 0, 0, false, true, true});
    register_attribute({AttributeKind::NoInline, "noinline", fn, 0, 0, false, false, true});
    register_attribute({AttributeKind::AlwaysInline, "always_inline", fn, 0, 0, false, false, true});
    register_attribute({AttributeKind::Weak, "weak", func_or_var, 0, 0, false, false, true});
    register_attribute({AttributeKind::WeakRef, "weakref", func_or_var, 0, 1, false, false, true});
    register_attribute({AttributeKind::Alias, "alias", func_or_var, 1, 1, false, false, true});
    register_attribute({AttributeKind::Ifunc, "ifunc", fn, 1, 1, false, false, true});
    register_attribute({AttributeKind::GnuInline, "gnu_inline", fn, 0, 0, false, false, true});
    register_attribute({AttributeKind::Visibility, "visibility", func_or_var | type, 1, 1, false, false, true});
    register_attribute({AttributeKind::TypeVisibility, "type_visibility", AttributeTarget::All, 1, 1, false, false, true});
    register_attribute({AttributeKind::Section, "section", func_or_var, 1, 1, false, false, true});
    register_attribute({AttributeKind::AbiTag, "abi_tag", AttributeTarget::All, 1, -1, false, false, false});
    register_attribute({AttributeKind::NoDebug, "nodebug", AttributeTarget::All, 0, 0, false, false, false});
    register_attribute({AttributeKind::ExcludeFromExplicitInstantiation,
                        "exclude_from_explicit_instantiation",
                        AttributeTarget::All,
                        0,
                        0,
                        false,
                        false,
                        true});
    register_attribute({AttributeKind::WarnUnusedResult, "warn_unused_result", fn | var | type | field, 0, 0, false, false, true});
    register_attribute({AttributeKind::Format, "format", fn | param | var | type | field, 3, 3, false, false, true});
    register_attribute({AttributeKind::FormatArg, "format_arg", fn, 1, 1, false, false, false});
    register_attribute({AttributeKind::NonNull, "nonnull", AttributeTarget::AnyDecl, 0, -1, false, false, true});
    register_attribute({AttributeKind::ReturnsNonNull, "returns_nonnull", fn, 0, 0, false, false, true});
    register_attribute({AttributeKind::Pure, "pure", fn, 0, 0, false, false, true});
    register_attribute({AttributeKind::Const, "const", fn, 0, 0, false, false, true});
    register_attribute({AttributeKind::Cold, "cold", fn | label, 0, 0, false, false, true});
    register_attribute({AttributeKind::Hot, "hot", fn | label, 0, 0, false, false, true});
    register_attribute({AttributeKind::NoThrow, "nothrow", fn, 0, 0, false, false, true});
    register_attribute({AttributeKind::Malloc, "malloc", fn, 0, 0, false, false, true});
    register_attribute({AttributeKind::AllocSize, "alloc_size", fn, 1, 2, false, false, false});
    register_attribute({AttributeKind::Flatten, "flatten", fn, 0, 0, false, false, false});
    register_attribute({AttributeKind::ForceAlignArgPointer, "force_align_arg_pointer", fn, 0, 0, false, false, false});
    register_attribute({AttributeKind::Optimize, "optimize", fn, 1, -1, false, false, false});
    register_attribute({AttributeKind::Used, "used", func_or_var, 0, 0, false, false, true});
    register_attribute({AttributeKind::Constructor, "constructor", fn, 0, 1, false, false, true});
    register_attribute({AttributeKind::Destructor, "destructor", fn, 0, 1, false, false, true});
    register_attribute({AttributeKind::Cleanup, "cleanup", var, 1, 1, false, false, false});
    register_attribute({AttributeKind::Common, "common", var, 0, 0, false, false, true});
    register_attribute({AttributeKind::Unavailable, "unavailable", AttributeTarget::AnyDecl, 0, 1, false, false, false});
    register_attribute({AttributeKind::Availability, "availability", AttributeTarget::AnyDecl, 1, -1, false, false, false});
    register_attribute({AttributeKind::Global, "global", AttributeTarget::All, 0, 0, false, false, false});
    register_attribute({AttributeKind::Device, "device", AttributeTarget::All, 0, 0, false, false, false});
    register_attribute({AttributeKind::DeviceBuiltin, "device_builtin", AttributeTarget::All, 0, 0, false, false, false});
    register_attribute({AttributeKind::TransparentUnion, "transparent_union", type, 0, 0, false, true, true});
    register_attribute({AttributeKind::MayAlias, "may_alias", type, 0, 0, false, true, false});
    register_attribute({AttributeKind::VectorSize, "vector_size", type | var | fn | AttributeTarget::Field | AttributeTarget::Parameter, 1, 1, false, true, true});
    register_attribute({AttributeKind::ExtVectorType, "ext_vector_type", type | var | fn | AttributeTarget::Field | AttributeTarget::Parameter, 1, 1, false, true, true});
    register_attribute({AttributeKind::NeonVectorType, "neon_vector_type", type | var | fn | AttributeTarget::Field | AttributeTarget::Parameter, 1, 1, false, true, true});
    register_attribute({AttributeKind::Mode, "mode", type | var | AttributeTarget::Field | AttributeTarget::Parameter, 1, 1, false, true, true});
    register_attribute({AttributeKind::Fallthrough, "fallthrough", stmt, 0, 0, true, false, true});
    register_attribute({AttributeKind::NoDiscard, "nodiscard", fn | type, 0, 1, true, false, true});
    register_attribute({AttributeKind::MaybeUnused, "maybe_unused", AttributeTarget::All, 0, 0, true, false, true});
    register_attribute({AttributeKind::ObjCFamily, "objc_bridge", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "objc_bridge_mutable", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "objc_bridge_related", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "objc_root_class", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "objc_subclassing_restricted", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "objc_designated_initializer", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "objc_requires_super", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "objc_method_family", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "objc_returns_inner_pointer", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "objc_independent_class", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "objc_boxable", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "ns_returns_retained", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "ns_returns_not_retained", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "ns_returns_autoreleased", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "ns_consumed", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "ns_consumes_self", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "ns_error_domain", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "cf_returns_retained", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "cf_returns_not_retained", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "cf_consumed", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "cf_audited_transfer", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "cf_unknown_transfer", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "swift_name", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "swift_private", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "swift_error", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "swift_bridge", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "swift_newtype", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "swift_attr", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "swift_async", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "swift_async_name", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::ObjCFamily, "noescape", AttributeTarget::AnyDecl, 0, -1, false, true, true});
    register_attribute({AttributeKind::NoUniqueAddress, "no_unique_address", AttributeTarget::Field, 0, 0, true, false, true});
}

std::string_view attribute_kind_name(AttributeKind kind) {
    switch (kind) {
        case AttributeKind::Unknown: return "unknown";
        case AttributeKind::ObjCFamily: return "objc-family";
        case AttributeKind::NoReturn: return "noreturn";
        case AttributeKind::NoInstrumentFunction: return "no_instrument_function";
        case AttributeKind::AssumeAligned: return "assume_aligned";
        case AttributeKind::NoInline: return "noinline";
        case AttributeKind::AlwaysInline: return "always_inline";
        case AttributeKind::Pure: return "pure";
        case AttributeKind::Const: return "const";
        case AttributeKind::Cold: return "cold";
        case AttributeKind::Hot: return "hot";
        case AttributeKind::NoThrow: return "nothrow";
        case AttributeKind::Malloc: return "malloc";
        case AttributeKind::AllocSize: return "alloc_size";
        case AttributeKind::Flatten: return "flatten";
        case AttributeKind::ForceAlignArgPointer: return "force_align_arg_pointer";
        case AttributeKind::Optimize: return "optimize";
        case AttributeKind::WarnUnusedResult: return "warn_unused_result";
        case AttributeKind::Format: return "format";
        case AttributeKind::FormatArg: return "format_arg";
        case AttributeKind::NonNull: return "nonnull";
        case AttributeKind::ReturnsNonNull: return "returns_nonnull";
        case AttributeKind::Constructor: return "constructor";
        case AttributeKind::Destructor: return "destructor";
        case AttributeKind::Cleanup: return "cleanup";
        case AttributeKind::Common: return "common";
        case AttributeKind::Packed: return "packed";
        case AttributeKind::TransparentUnion: return "transparent_union";
        case AttributeKind::DesignatedInit: return "designated_init";
        case AttributeKind::MayAlias: return "may_alias";
        case AttributeKind::VectorSize: return "vector_size";
        case AttributeKind::ExtVectorType: return "ext_vector_type";
        case AttributeKind::NeonVectorType: return "neon_vector_type";
        case AttributeKind::Mode: return "mode";
        case AttributeKind::Unused: return "unused";
        case AttributeKind::Used: return "used";
        case AttributeKind::Deprecated: return "deprecated";
        case AttributeKind::Unavailable: return "unavailable";
        case AttributeKind::Availability: return "availability";
        case AttributeKind::Aligned: return "aligned";
        case AttributeKind::Section: return "section";
        case AttributeKind::Visibility: return "visibility";
        case AttributeKind::TypeVisibility: return "type_visibility";
        case AttributeKind::Weak: return "weak";
        case AttributeKind::WeakRef: return "weakref";
        case AttributeKind::Alias: return "alias";
        case AttributeKind::Ifunc: return "ifunc";
        case AttributeKind::GnuInline: return "gnu_inline";
        case AttributeKind::AbiTag: return "abi_tag";
        case AttributeKind::NoDebug: return "nodebug";
        case AttributeKind::ExcludeFromExplicitInstantiation: return "exclude_from_explicit_instantiation";
        case AttributeKind::Global: return "global";
        case AttributeKind::Device: return "device";
        case AttributeKind::DeviceBuiltin: return "device_builtin";
        case AttributeKind::Fallthrough: return "fallthrough";
        case AttributeKind::NoDiscard: return "nodiscard";
        case AttributeKind::MaybeUnused: return "maybe_unused";
        case AttributeKind::NoUniqueAddress: return "no_unique_address";
    }
    return "unknown";
}

} // namespace aburi
