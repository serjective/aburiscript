#include "qualified_name_utils.h"

#include <algorithm>
#include <unordered_set>

namespace qualified_name_utils {

namespace {

const DeclContext* canonical_decl_context(const DeclContext* context) {
    if (!context) {
        return nullptr;
    }
    return context->primary_context() ? context->primary_context() : context;
}

uint64_t effective_lookup_position(const DeclContext* context) {
    return context ? context->next_lookup_event_index() : 0;
}

bool nomination_is_visible(const NamespaceNominationRecord& nomination,
                           uint64_t lookup_position) {
    return nomination.point_of_declaration_index != 0 &&
           nomination.point_of_declaration_index < lookup_position;
}

struct NamespaceResolutionResult {
    std::shared_ptr<DeclContext> target_context = nullptr;
    std::shared_ptr<Scope> target_scope = nullptr;

    explicit operator bool() const {
        return target_context != nullptr || target_scope != nullptr;
    }
};

NamespaceResolutionResult resolve_named_namespace_in_context_graph(
    const DeclContext* context,
    std::string_view namespace_name,
    uint64_t lookup_position,
    std::unordered_set<const DeclContext*>& visited_contexts) {
    NamespaceResolutionResult result;
    context = canonical_decl_context(context);
    if (!context || namespace_name.empty() ||
        !visited_contexts.insert(context).second) {
        return result;
    }

    lookup_position = lookup_position == 0
        ? effective_lookup_position(context)
        : std::min(lookup_position, effective_lookup_position(context));

    auto binding = context->lookup_local_namespace_binding(namespace_name);
    if (binding && binding.entry) {
        result.target_context = binding.entry->target_context;
        result.target_scope = binding.entry->target_scope;
        if (result.target_context &&
            result.target_context->primary_context() &&
            result.target_context->primary_context() != result.target_context.get()) {
            auto canonical = result.target_context->primary_context();
            result.target_context = canonical->shared_from_this();
        }
        return result;
    }

    auto* child = context->find_named_lexical_child(namespace_name);
    if (child) {
        auto* canonical = child->primary_context() ? child->primary_context() : child;
        result.target_context = canonical->shared_from_this();
        return result;
    }

    auto search_nominations_of_kind =
        [&](NamespaceNominationKind kind) -> NamespaceResolutionResult {
            for (const auto& nomination : context->namespace_nominations()) {
                if (nomination.kind != kind ||
                    !nomination.nominated_context ||
                    !nomination_is_visible(nomination, lookup_position)) {
                    continue;
                }
                auto nomination_result = resolve_named_namespace_in_context_graph(
                    nomination.nominated_context.get(),
                    namespace_name,
                    nomination.nominated_context->next_lookup_event_index(),
                    visited_contexts);
                if (nomination_result) {
                    return nomination_result;
                }
            }
            return {};
        };

    if (auto inline_result =
            search_nominations_of_kind(NamespaceNominationKind::InlineImplicit)) {
        return inline_result;
    }
    if (auto nominated_result =
            search_nominations_of_kind(NamespaceNominationKind::UsingDirective)) {
        return nominated_result;
    }

    return result;
}

NamespaceResolutionResult resolve_named_namespace_result(
    const DeclContext* start_context,
    std::string_view namespace_name,
    bool allow_enclosing_lookup) {
    if (namespace_name.empty()) {
        return {};
    }

    if (allow_enclosing_lookup) {
        for (auto* ctx = start_context; ctx; ctx = ctx->semantic_parent()) {
            std::unordered_set<const DeclContext*> visited_contexts;
            auto resolved = resolve_named_namespace_in_context_graph(
                ctx,
                namespace_name,
                ctx->next_lookup_event_index(),
                visited_contexts);
            if (resolved) {
                return resolved;
            }
        }
        return {};
    }
    std::unordered_set<const DeclContext*> visited_contexts;
    return resolve_named_namespace_in_context_graph(
        start_context,
        namespace_name,
        start_context ? start_context->next_lookup_event_index() : 0,
        visited_contexts);
}

} // namespace

std::shared_ptr<DeclContext> resolve_named_namespace_context(
    const DeclContext* start_context,
    std::string_view namespace_name,
    bool allow_enclosing_lookup) {
    return resolve_named_namespace_result(
               start_context,
               namespace_name,
               allow_enclosing_lookup)
        .target_context;
}

std::shared_ptr<Scope> resolve_named_namespace_scope(
    const DeclContext* start_context,
    std::string_view namespace_name,
    bool allow_enclosing_lookup) {
    return resolve_named_namespace_result(
               start_context,
               namespace_name,
               allow_enclosing_lookup)
        .target_scope;
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

std::optional<std::string> namespace_prefix_from_effective_decl_scope(
    const std::shared_ptr<Scope>& scope) {
    auto effective_scope = scope;
    while (effective_scope &&
           scope_flags_contains(
               effective_scope->flags,
               ScopeFlags::TemplateParameterScope) &&
           effective_scope->parent) {
        effective_scope = effective_scope->parent;
    }
    return namespace_prefix_from_scope(effective_scope);
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
