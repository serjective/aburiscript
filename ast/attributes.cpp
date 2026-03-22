#include "attributes.h"

AttributeRegistry& AttributeRegistry::instance() {
    static AttributeRegistry registry;
    return registry;
}

void AttributeRegistry::register_attribute(const AttributeDescriptor& desc) {
    by_name[desc.name] = desc;
    by_kind[static_cast<int>(desc.kind)] = desc;
}

const AttributeDescriptor* AttributeRegistry::find(const std::string& canonical_name) const {
    auto it = by_name.find(canonical_name);
    if (it == by_name.end()) return nullptr;
    return &it->second;
}

const AttributeDescriptor* AttributeRegistry::find_by_kind(AttributeKind kind) const {
    auto it = by_kind.find(static_cast<int>(kind));
    if (it == by_kind.end()) return nullptr;
    return &it->second;
}

AttributeRegistry::AttributeRegistry() {
    // Core attributes
    register_attribute({AttributeKind::NORETURN, "noreturn",
        AttributeTarget::FUNCTION, 0, 0, true, false});
    register_attribute({AttributeKind::UNUSED, "unused",
        AttributeTarget::ALL, 0, 0, true, false});
    register_attribute({AttributeKind::DEPRECATED, "deprecated",
        AttributeTarget::ANY_DECL, 0, 1, true, false});
    register_attribute({AttributeKind::ALIGNED, "aligned",
        AttributeTarget::VARIABLE | AttributeTarget::TYPE | AttributeTarget::FIELD,
        0, 1, false, true});
    register_attribute({AttributeKind::PACKED, "packed",
        AttributeTarget::TYPE | AttributeTarget::FIELD | AttributeTarget::VARIABLE, 0, 0, false, true});
    register_attribute({AttributeKind::NOINLINE, "noinline",
        AttributeTarget::FUNCTION, 0, 0, false, false});
    register_attribute({AttributeKind::ALWAYS_INLINE, "always_inline",
        AttributeTarget::FUNCTION, 0, 0, false, false});
    register_attribute({AttributeKind::WEAK, "weak",
        AttributeTarget::FUNC_OR_VAR, 0, 0, false, false});
    register_attribute({AttributeKind::VISIBILITY, "visibility",
        AttributeTarget::FUNC_OR_VAR | AttributeTarget::TYPE, 1, 1, false, false});
    register_attribute({AttributeKind::SECTION, "section",
        AttributeTarget::FUNC_OR_VAR, 1, 1, false, false});

    // Extended attributes
    register_attribute({AttributeKind::WARN_UNUSED_RESULT, "warn_unused_result",
        AttributeTarget::FUNCTION, 0, 0, false, false});
    register_attribute({AttributeKind::FORMAT, "format",
        AttributeTarget::FUNCTION, 3, 3, false, false});
    register_attribute({AttributeKind::NONNULL, "nonnull",
        AttributeTarget::FUNCTION, 0, -1, false, false});
    register_attribute({AttributeKind::RETURNS_NONNULL, "returns_nonnull",
        AttributeTarget::FUNCTION, 0, 0, false, false});
    register_attribute({AttributeKind::PURE, "pure",
        AttributeTarget::FUNCTION, 0, 0, false, false});
    register_attribute({AttributeKind::CONST_ATTR, "const",
        AttributeTarget::FUNCTION, 0, 0, false, false});
    register_attribute({AttributeKind::COLD, "cold",
        AttributeTarget::FUNCTION | AttributeTarget::LABEL, 0, 0, false, false});
    register_attribute({AttributeKind::HOT, "hot",
        AttributeTarget::FUNCTION | AttributeTarget::LABEL, 0, 0, false, false});
    register_attribute({AttributeKind::NOTHROW, "nothrow",
        AttributeTarget::FUNCTION, 0, 0, false, false});
    register_attribute({AttributeKind::MALLOC_ATTR, "malloc",
        AttributeTarget::FUNCTION, 0, 0, false, false});
    register_attribute({AttributeKind::ALLOC_SIZE, "alloc_size",
        AttributeTarget::FUNCTION, 1, 2, false, false});
    register_attribute({AttributeKind::FLATTEN, "flatten",
        AttributeTarget::FUNCTION, 0, 0, false, false});
    register_attribute({AttributeKind::FORCE_ALIGN_ARG_POINTER, "force_align_arg_pointer",
        AttributeTarget::FUNCTION, 0, 0, false, false});
    register_attribute({AttributeKind::OPTIMIZE_ATTR, "optimize",
        AttributeTarget::FUNCTION, 1, -1, false, false});
    register_attribute({AttributeKind::USED, "used",
        AttributeTarget::FUNC_OR_VAR, 0, 0, false, false});
    register_attribute({AttributeKind::CONSTRUCTOR, "constructor",
        AttributeTarget::FUNCTION, 0, 1, false, false});
    register_attribute({AttributeKind::DESTRUCTOR, "destructor",
        AttributeTarget::FUNCTION, 0, 1, false, false});
    register_attribute({AttributeKind::CLEANUP, "cleanup",
        AttributeTarget::VARIABLE, 1, 1, false, false});
    register_attribute({AttributeKind::COMMON_ATTR, "common",
        AttributeTarget::VARIABLE, 0, 0, false, false});
    register_attribute({AttributeKind::UNAVAILABLE, "unavailable",
        AttributeTarget::ANY_DECL, 0, 1, false, false});
    register_attribute({AttributeKind::AVAILABILITY, "availability",
        AttributeTarget::ANY_DECL, 1, -1, false, false});
    register_attribute({AttributeKind::GLOBAL_ATTR, "global",
        AttributeTarget::ALL, 0, 0, false, false});
    register_attribute({AttributeKind::DEVICE_ATTR, "device",
        AttributeTarget::ALL, 0, 0, false, false});
    register_attribute({AttributeKind::DEVICE_BUILTIN_ATTR, "device_builtin",
        AttributeTarget::ALL, 0, 0, false, false});

    // Type attributes
    register_attribute({AttributeKind::TRANSPARENT_UNION, "transparent_union",
        AttributeTarget::TYPE, 0, 0, false, true});
    register_attribute({AttributeKind::MAY_ALIAS, "may_alias",
        AttributeTarget::TYPE, 0, 0, false, true});
    register_attribute({AttributeKind::VECTOR_SIZE, "vector_size",
        AttributeTarget::TYPE | AttributeTarget::VARIABLE,
        1, 1, false, true});

    // Statement attributes
    register_attribute({AttributeKind::FALLTHROUGH, "fallthrough",
        AttributeTarget::STATEMENT, 0, 0, true, false});

    // C23 standard attributes
    register_attribute({AttributeKind::NODISCARD, "nodiscard",
        AttributeTarget::FUNCTION | AttributeTarget::TYPE, 0, 1, true, false});
    register_attribute({AttributeKind::MAYBE_UNUSED, "maybe_unused",
        AttributeTarget::ALL, 0, 0, true, false});
}
