#include "qualified_name_utils.h"

namespace qualified_name_utils {

std::string make_cpp_namespace_reopen_key(
    const DeclContext* semantic_parent,
    std::string_view namespace_name) {
    uint64_t parent_id = semantic_parent ? semantic_parent->stable_id() : 0;
    return std::to_string(parent_id) + "#" + std::string(namespace_name);
}

std::shared_ptr<Scope> resolve_named_namespace_scope(
    const NamespaceScopeCache& namespace_scope_cache,
    const DeclContext* start_context,
    std::string_view namespace_name,
    bool allow_enclosing_lookup) {
    if (namespace_name.empty()) {
        return nullptr;
    }
    if (allow_enclosing_lookup) {
        for (auto* ctx = start_context; ctx; ctx = ctx->semantic_parent()) {
            auto it = namespace_scope_cache.find(
                make_cpp_namespace_reopen_key(ctx, namespace_name));
            if (it != namespace_scope_cache.end()) {
                return it->second;
            }
        }
        return nullptr;
    }
    if (!start_context) {
        return nullptr;
    }
    auto it = namespace_scope_cache.find(
        make_cpp_namespace_reopen_key(start_context, namespace_name));
    if (it == namespace_scope_cache.end()) {
        return nullptr;
    }
    return it->second;
}

std::string format_cpp_qualified_name(
    bool has_global_qualifier,
    const std::vector<std::string>& qualifiers,
    std::string_view terminal_name) {
    std::string full_name;
    if (has_global_qualifier) {
        full_name = "::";
    }
    for (const auto& qualifier : qualifiers) {
        full_name += qualifier;
        full_name += "::";
    }
    full_name += terminal_name;
    return full_name;
}

std::optional<std::string> namespace_prefix_from_scope(
    const std::shared_ptr<Scope>& scope) {
    if (!scope || scope->cxx_namespace_path.empty()) {
        return std::nullopt;
    }
    std::string prefix;
    for (size_t idx = 0; idx < scope->cxx_namespace_path.size(); ++idx) {
        if (idx > 0) {
            prefix += "::";
        }
        prefix += scope->cxx_namespace_path[idx];
    }
    if (prefix.empty()) {
        return std::nullopt;
    }
    return prefix;
}

void ensure_namespace_qualifier_prefix_for_scope(
    const std::shared_ptr<Scope>& scope,
    std::string& qualifier_prefix) {
    auto namespace_prefix = namespace_prefix_from_scope(scope);
    if (!namespace_prefix.has_value()) {
        return;
    }
    std::string expected_prefix = *namespace_prefix + "::";
    if (qualifier_prefix.empty()) {
        qualifier_prefix = *namespace_prefix;
        return;
    }
    if (qualifier_prefix.rfind(expected_prefix, 0) == 0) {
        return;
    }
    qualifier_prefix = expected_prefix + qualifier_prefix;
}

} // namespace qualified_name_utils
