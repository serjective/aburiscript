#ifndef ABURI_QUALIFIED_NAME_UTILS_H
#define ABURI_QUALIFIED_NAME_UTILS_H

#include "ast/symbols.h"
#include "collect/decl_context.h"

#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

namespace qualified_name_utils {

std::shared_ptr<DeclContext> resolve_named_namespace_context(
    const DeclContext* start_context,
    std::string_view namespace_name,
    bool allow_enclosing_lookup);

std::shared_ptr<Scope> resolve_named_namespace_scope(
    const DeclContext* start_context,
    std::string_view namespace_name,
    bool allow_enclosing_lookup);

std::string format_cpp_qualified_name(
    bool has_global_qualifier,
    const std::vector<std::string>& qualifiers,
    std::string_view terminal_name);

std::optional<std::string> namespace_prefix_from_scope(
    const std::shared_ptr<Scope>& scope);

std::optional<std::string> namespace_prefix_from_effective_decl_scope(
    const std::shared_ptr<Scope>& scope);

void ensure_namespace_qualifier_prefix_for_scope(
    const std::shared_ptr<Scope>& scope,
    std::string& qualifier_prefix);

} // namespace qualified_name_utils

#endif // ABURI_QUALIFIED_NAME_UTILS_H
