#include "qualified_name_utils.h"

namespace qualified_name_utils {

std::shared_ptr<Scope> resolve_named_namespace_scope(
    const DeclContext* start_context,
    std::string_view namespace_name,
    bool allow_enclosing_lookup) {
    if (namespace_name.empty()) {
        return nullptr;
    }

    auto resolve_in_context =
        [&](const DeclContext* candidate) -> std::shared_ptr<Scope> {
            if (!candidate) {
                return nullptr;
            }
            auto binding = candidate->lookup_local_namespace_binding(namespace_name);
            if (!binding || !binding.entry) {
                return nullptr;
            }
            return binding.entry->target_scope;
        };

    if (allow_enclosing_lookup) {
        for (auto* ctx = start_context; ctx; ctx = ctx->semantic_parent()) {
            if (auto resolved = resolve_in_context(ctx)) {
                return resolved;
            }
        }
        return nullptr;
    }
    return resolve_in_context(start_context);
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
