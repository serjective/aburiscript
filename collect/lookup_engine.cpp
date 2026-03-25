#include "lookup_engine.h"
#include <unordered_set>
#include "../ast/ast.h"
#include "../helpers/casting.h"
#include "../helpers/qualified_name_utils.h"
#include "decl_context.h"

namespace {
enum class ContextLookupDisposition : uint8_t {
    NotFound,
    Found,
    Blocked
};

struct OrdinaryContextLookupResult {
    ContextLookupDisposition disposition = ContextLookupDisposition::NotFound;
    std::shared_ptr<Symbol> symbol = nullptr;
};

struct FunctionContextLookupResult {
    bool found = false;
    bool blocked = false;
    std::vector<std::shared_ptr<Symbol>> candidates;
};

struct TagContextLookupResult {
    bool found = false;
    const DeclBinding* binding = nullptr;
    TagDecl* decl = nullptr;
};

struct OrdinaryBindingSetResult {
    bool blocked = false;
    std::vector<LookupEngine::QualifiedOrdinaryBindingMatch> bindings;
};

bool symbol_matches_filter(const std::shared_ptr<Symbol>& sym,
                           LookupEngine::OrdinaryFilter filter) {
    if (!sym) {
        return false;
    }
    if (filter == LookupEngine::OrdinaryFilter::TypedefOnly) {
        return sym->kind == SymbolKind::TYPE;
    }
    return true;
}

const DeclBinding* lookup_context_local(const DeclContext* context,
                                        const std::string& name,
                                        LookupNamespace ns) {
    if (!context) {
        return nullptr;
    }
    return context->lookup_local(name, ns);
}

bool binding_has_template_entity(const DeclBinding* binding) {
    return binding &&
           (binding->template_decl != nullptr ||
            binding->has_template_overload_set());
}

bool binding_matches_ordinary_filter(const DeclBinding* binding,
                                     LookupEngine::OrdinaryFilter filter) {
    if (!binding) {
        return false;
    }
    if (filter == LookupEngine::OrdinaryFilter::Any) {
        return true;
    }
    if (symbol_matches_filter(binding->symbol, filter)) {
        return true;
    }
    if (!binding->has_overload_set()) {
        return false;
    }
    for (const auto& candidate : binding->overload_candidates) {
        if (symbol_matches_filter(candidate, filter)) {
            return true;
        }
    }
    return false;
}

const DeclContext* canonical_decl_context(const DeclContext* context);

std::shared_ptr<Symbol> select_binding_symbol(const DeclBinding* binding,
                                              LookupEngine::OrdinaryFilter filter) {
    if (!binding) {
        return nullptr;
    }
    if (symbol_matches_filter(binding->symbol, filter)) {
        return binding->symbol;
    }
    if (binding->has_overload_set()) {
        for (const auto& candidate : binding->overload_candidates) {
            if (symbol_matches_filter(candidate, filter)) {
                return candidate;
            }
        }
    }
    return nullptr;
}

const DeclContext* translation_unit_context(const DeclContext* context) {
    auto* current = context;
    while (current && current->semantic_parent()) {
        current = current->semantic_parent();
    }
    return current;
}

const DeclContext* resolve_named_child_context(const DeclContext* context,
                                               const std::string& component,
                                               bool allow_enclosing_lookup) {
    if (!context || component.empty()) {
        return nullptr;
    }

    auto resolve_in_context = [&](const DeclContext* candidate) -> const DeclContext* {
        if (!candidate) {
            return nullptr;
        }
        auto namespace_context =
            qualified_name_utils::resolve_named_namespace_context(
                candidate,
                component,
                /*allow_enclosing_lookup=*/false);
        if (namespace_context) {
            auto* canonical = namespace_context->primary_context();
            return canonical ? canonical : namespace_context.get();
        }
        auto* child = candidate->find_named_lexical_child(component);
        if (!child) {
            return nullptr;
        }
        return child->primary_context() ? child->primary_context() : child;
    };

    if (!allow_enclosing_lookup) {
        return resolve_in_context(context);
    }
    for (auto* candidate = context; candidate; candidate = candidate->semantic_parent()) {
        if (const DeclContext* resolved = resolve_in_context(candidate)) {
            return resolved;
        }
    }
    return nullptr;
}

std::vector<std::shared_ptr<Symbol>> extract_function_candidates(const DeclBinding* binding) {
    std::vector<std::shared_ptr<Symbol>> out;
    if (!binding) {
        return out;
    }
    auto maybe_push = [&](const std::shared_ptr<Symbol>& sym) {
        if (!sym || sym->kind != SymbolKind::FUNCTION) {
            return;
        }
        for (const auto& existing : out) {
            if (existing == sym) {
                return;
            }
        }
        out.push_back(sym);
    };
    if (binding->has_overload_set()) {
        for (const auto& candidate : binding->overload_candidates) {
            maybe_push(candidate);
        }
    } else {
        maybe_push(binding->symbol);
    }
    return out;
}

void append_unique_binding(std::vector<const DeclBinding*>& bindings,
                           const DeclBinding* binding) {
    if (!binding) {
        return;
    }
    for (const auto* existing : bindings) {
        if (existing == binding) {
            return;
        }
    }
    bindings.push_back(binding);
}

void append_unique_binding_match(
    std::vector<LookupEngine::QualifiedOrdinaryBindingMatch>& bindings,
    const DeclBinding* binding,
    const DeclContext* owner_context,
    const std::shared_ptr<Scope>& owner_scope) {
    if (!binding) {
        return;
    }
    owner_context = canonical_decl_context(owner_context);
    for (const auto& existing : bindings) {
        if (existing.binding == binding &&
            canonical_decl_context(existing.owner_context) == owner_context) {
            return;
        }
    }
    bindings.push_back(
        LookupEngine::QualifiedOrdinaryBindingMatch{
            binding,
            owner_context,
            owner_scope});
}

std::shared_ptr<Scope> resolve_direct_child_namespace_scope(
    const DeclContext* owner_context,
    const DeclContext* child_context) {
    owner_context = canonical_decl_context(owner_context);
    child_context = canonical_decl_context(child_context);
    if (!owner_context || !child_context) {
        return nullptr;
    }

    const auto& child_name = child_context->lookup_name();
    if (child_name.empty()) {
        return nullptr;
    }

    const auto* direct_child = owner_context->lookup_local_namespace(child_name);
    if (!direct_child || !direct_child->target_context) {
        return nullptr;
    }

    const DeclContext* direct_child_context =
        canonical_decl_context(direct_child->target_context.get());
    if (direct_child_context != child_context) {
        return nullptr;
    }
    return direct_child->target_scope;
}

void append_unique_template_decl(std::vector<const Decl*>& decls,
                                 const Decl* decl) {
    if (!decl) {
        return;
    }
    for (const auto* existing : decls) {
        if (existing == decl) {
            return;
        }
    }
    decls.push_back(decl);
}

bool binding_has_non_function_ordinary_entity(const DeclBinding* binding) {
    if (!binding) {
        return false;
    }
    if (binding->symbol && binding->symbol->kind != SymbolKind::FUNCTION) {
        return true;
    }
    if (binding->template_decl &&
        !isa<FunctionTemplateDecl>(binding->template_decl)) {
        return true;
    }
    for (const auto* decl : binding->template_overload_candidates) {
        if (!isa<FunctionTemplateDecl>(decl)) {
            return true;
        }
    }
    return false;
}

bool binding_has_function_family_entity(const DeclBinding* binding) {
    if (!binding) {
        return false;
    }
    if (binding->symbol && binding->symbol->kind == SymbolKind::FUNCTION) {
        return true;
    }
    for (const auto& candidate : binding->overload_candidates) {
        if (candidate && candidate->kind == SymbolKind::FUNCTION) {
            return true;
        }
    }
    if (binding->template_decl && isa<FunctionTemplateDecl>(binding->template_decl)) {
        return true;
    }
    for (const auto* decl : binding->template_overload_candidates) {
        if (isa<FunctionTemplateDecl>(decl)) {
            return true;
        }
    }
    return false;
}

std::shared_ptr<DeclBinding> synthesize_merged_function_binding(
    const std::string& name,
    const std::vector<const DeclBinding*>& bindings,
    LookupEngine::OrdinaryFilter filter) {
    auto merged = std::make_shared<DeclBinding>();
    merged->name = name;
    merged->lookup_namespace = LookupNamespace::Ordinary;
    merged->symbol_kind = SymbolKind::FUNCTION;

    for (const auto* binding : bindings) {
        if (!binding) {
            continue;
        }
        if (!merged->symbol) {
            merged->symbol = select_binding_symbol(binding, filter);
            if (merged->symbol) {
                merged->type = merged->symbol->type;
            }
        }
        for (const auto& candidate : extract_function_candidates(binding)) {
            bool seen = false;
            for (const auto& existing : merged->overload_candidates) {
                if (existing == candidate) {
                    seen = true;
                    break;
                }
            }
            if (!seen) {
                merged->overload_candidates.push_back(candidate);
            }
        }
        if (binding->template_decl) {
            append_unique_template_decl(
                merged->template_overload_candidates,
                binding->template_decl);
        }
        for (const auto* decl : binding->template_overload_candidates) {
            append_unique_template_decl(merged->template_overload_candidates, decl);
        }
    }

    if (!merged->symbol && !merged->overload_candidates.empty()) {
        merged->symbol = merged->overload_candidates.front();
        merged->type = merged->symbol ? merged->symbol->type : QualType();
    }
    if (!merged->template_overload_candidates.empty()) {
        merged->template_decl = merged->template_overload_candidates.front();
    }
    merged->ordinary_entry_kind =
        merged->overload_candidates.size() > 1
            ? OrdinaryEntryKind::OverloadSet
            : OrdinaryEntryKind::SingleSymbol;
    return merged;
}

std::string scope_flags_to_string(ScopeFlags flags) {
    std::string out;
    if (scope_flags_contains(flags, ScopeFlags::FileScope)) out += "File|";
    if (scope_flags_contains(flags, ScopeFlags::FunctionScope)) out += "Function|";
    if (scope_flags_contains(flags, ScopeFlags::BlockScope)) out += "Block|";
    if (scope_flags_contains(flags, ScopeFlags::PrototypeScope)) out += "Proto|";
    if (scope_flags_contains(flags, ScopeFlags::LoopScope)) out += "Loop|";
    if (scope_flags_contains(flags, ScopeFlags::SwitchScope)) out += "Switch|";
    if (scope_flags_contains(flags, ScopeFlags::NamespaceScope)) out += "Namespace|";
    if (scope_flags_contains(flags, ScopeFlags::TemplateParameterScope)) out += "TemplateParam|";
    if (out.empty()) return "None";
    out.pop_back();
    return out;
}

void trace_scope_step(LookupEngine::LookupTrace* trace,
                      size_t depth,
                      ScopeFlags flags) {
    if (!trace) {
        return;
    }
    trace->add_step(
        "scope[" + std::to_string(depth) + "] flags=" + scope_flags_to_string(flags));
}

void trace_named_step(LookupEngine::LookupTrace* trace,
                      const char* prefix,
                      const std::string& name) {
    if (!trace) {
        return;
    }
    std::string step(prefix);
    step += name;
    trace->add_step(std::move(step));
}

const DeclContext* canonical_decl_context(const DeclContext* context) {
    if (!context) {
        return nullptr;
    }
    return context->primary_context() ? context->primary_context() : context;
}

uint64_t effective_lookup_position(const DeclContext* context,
                                   uint64_t lookup_position) {
    if (!context) {
        return 0;
    }
    uint64_t next_index = context->next_lookup_event_index();
    if (lookup_position == 0 || lookup_position > next_index) {
        return next_index;
    }
    return lookup_position;
}

bool nomination_is_visible(const NamespaceNominationRecord& nomination,
                           uint64_t lookup_position) {
    return nomination.point_of_declaration_index > 0 &&
           nomination.point_of_declaration_index < lookup_position;
}

bool namespace_reachability_includes_inline(
    LookupEngine::NamespaceReachability reachability) {
    return reachability == LookupEngine::NamespaceReachability::InlineVisible ||
           reachability == LookupEngine::NamespaceReachability::FullyVisible;
}

bool namespace_reachability_includes_using(
    LookupEngine::NamespaceReachability reachability) {
    return reachability == LookupEngine::NamespaceReachability::FullyVisible;
}

template <typename Fn>
bool visit_visible_namespace_nominations_of_kind(
    const DeclContext* context,
    uint64_t lookup_position,
    NamespaceNominationKind kind,
    const Fn& visitor) {
    if (!context) {
        return false;
    }
    for (const auto& nomination : context->namespace_nominations()) {
        if (nomination.kind != kind ||
            !nomination_is_visible(nomination, lookup_position) ||
            !nomination.nominated_context) {
            continue;
        }
        if (visitor(nomination)) {
            return true;
        }
    }
    return false;
}

void append_unique_function_candidate(
    std::vector<std::shared_ptr<Symbol>>& candidates,
    const std::shared_ptr<Symbol>& candidate) {
    if (!candidate || candidate->kind != SymbolKind::FUNCTION) {
        return;
    }
    for (const auto& existing : candidates) {
        if (existing == candidate) {
            return;
        }
    }
    candidates.push_back(candidate);
}

TagDecl* tag_decl_from_binding(const DeclBinding* binding) {
    if (!binding) {
        return nullptr;
    }
    if (binding->ast_decl) {
        return const_cast<TagDecl*>(static_cast<const TagDecl*>(binding->ast_decl));
    }
    if (binding->type) {
        auto tag_ty = dyn_cast_shared<TagType>(binding->type.get_shared());
        if (tag_ty && tag_ty->get_decl()) {
            return const_cast<TagDecl*>(tag_ty->get_decl());
        }
    }
    return nullptr;
}

OrdinaryContextLookupResult lookup_ordinary_in_context_graph(
    const std::string& name,
    const DeclContext* context,
    uint64_t lookup_position,
    LookupEngine::OrdinaryFilter filter,
    std::unordered_set<const DeclContext*>& visited_contexts,
    LookupEngine::LookupTrace* trace) {
    OrdinaryContextLookupResult result;
    context = canonical_decl_context(context);
    if (!context || !visited_contexts.insert(context).second) {
        return result;
    }

    lookup_position = effective_lookup_position(context, lookup_position);
    auto* binding = lookup_context_local(context, name, LookupNamespace::Ordinary);
    if (binding) {
        auto selected = select_binding_symbol(binding, filter);
        if (selected) {
            trace_named_step(trace, "hit decl-context ordinary: ", name);
            result.disposition = ContextLookupDisposition::Found;
            result.symbol = std::move(selected);
            return result;
        }
        if (filter == LookupEngine::OrdinaryFilter::TypedefOnly) {
            trace_named_step(
                trace, "blocked by non-typedef ordinary binding: ", name);
            result.disposition = ContextLookupDisposition::Blocked;
            return result;
        }
    } else {
        trace_named_step(trace, "miss decl-context ordinary: ", name);
    }

    auto search_nominations_of_kind =
        [&](NamespaceNominationKind kind) -> OrdinaryContextLookupResult {
            OrdinaryContextLookupResult nomination_match;
            visit_visible_namespace_nominations_of_kind(
                context,
                lookup_position,
                kind,
                [&](const NamespaceNominationRecord& nomination) {
                    trace_named_step(
                        trace,
                        kind == NamespaceNominationKind::InlineImplicit
                            ? "follow inline namespace ordinary: "
                            : "follow namespace nomination ordinary: ",
                        name);
                    auto nomination_result = lookup_ordinary_in_context_graph(
                        name,
                        nomination.nominated_context.get(),
                        nomination.nominated_context->next_lookup_event_index(),
                        filter,
                        visited_contexts,
                        trace);
                    if (nomination_result.disposition !=
                        ContextLookupDisposition::NotFound) {
                        nomination_match = std::move(nomination_result);
                        return true;
                    }
                    return false;
                });
            return nomination_match;
        };

    auto inline_result =
        search_nominations_of_kind(NamespaceNominationKind::InlineImplicit);
    if (inline_result.disposition != ContextLookupDisposition::NotFound) {
        return inline_result;
    }
    auto nominated_result =
        search_nominations_of_kind(NamespaceNominationKind::UsingDirective);
    if (nominated_result.disposition != ContextLookupDisposition::NotFound) {
        return nominated_result;
    }

    return result;
}

FunctionContextLookupResult lookup_functions_in_context_graph(
    const std::string& name,
    const DeclContext* context,
    uint64_t lookup_position,
    std::unordered_set<const DeclContext*>& visited_contexts,
    LookupEngine::LookupTrace* trace) {
    FunctionContextLookupResult result;
    context = canonical_decl_context(context);
    if (!context || !visited_contexts.insert(context).second) {
        return result;
    }

    lookup_position = effective_lookup_position(context, lookup_position);
    auto* binding = lookup_context_local(context, name, LookupNamespace::Ordinary);
    if (binding) {
        auto local_candidates = extract_function_candidates(binding);
        if (local_candidates.empty()) {
            trace_named_step(
                trace, "ordinary-name hit is not function overload set: ", name);
            result.blocked = true;
            return result;
        }
        trace_named_step(trace, "hit decl-context function candidates: ", name);
        result.found = true;
        for (const auto& candidate : local_candidates) {
            append_unique_function_candidate(result.candidates, candidate);
        }
    } else {
        trace_named_step(trace, "miss decl-context function candidates: ", name);
    }

    auto append_nominated_candidates = [&](NamespaceNominationKind kind) {
        visit_visible_namespace_nominations_of_kind(
            context,
            lookup_position,
            kind,
            [&](const NamespaceNominationRecord& nomination) {
                trace_named_step(
                    trace,
                    kind == NamespaceNominationKind::InlineImplicit
                        ? "follow inline namespace functions: "
                        : "follow namespace nomination functions: ",
                    name);
                auto nomination_result = lookup_functions_in_context_graph(
                    name,
                    nomination.nominated_context.get(),
                    nomination.nominated_context->next_lookup_event_index(),
                    visited_contexts,
                    trace);
                if (nomination_result.found) {
                    result.found = true;
                    for (const auto& candidate : nomination_result.candidates) {
                        append_unique_function_candidate(result.candidates, candidate);
                    }
                }
                return false;
            });
    };

    append_nominated_candidates(NamespaceNominationKind::InlineImplicit);
    append_nominated_candidates(NamespaceNominationKind::UsingDirective);

    return result;
}

TagContextLookupResult lookup_tag_in_context_graph(
    const std::string& name,
    const DeclContext* context,
    uint64_t lookup_position,
    std::unordered_set<const DeclContext*>& visited_contexts,
    LookupEngine::LookupTrace* trace) {
    TagContextLookupResult result;
    context = canonical_decl_context(context);
    if (!context || !visited_contexts.insert(context).second) {
        return result;
    }

    lookup_position = effective_lookup_position(context, lookup_position);
    auto* binding = lookup_context_local(context, name, LookupNamespace::Tag);
    if (binding) {
        trace_named_step(trace, "hit decl-context tag: ", name);
        result.found = true;
        result.binding = binding;
        result.decl = tag_decl_from_binding(binding);
        return result;
    }
    trace_named_step(trace, "miss decl-context tag: ", name);

    auto search_nominated_tags =
        [&](NamespaceNominationKind kind) -> TagContextLookupResult {
            TagContextLookupResult nomination_match;
            visit_visible_namespace_nominations_of_kind(
                context,
                lookup_position,
                kind,
                [&](const NamespaceNominationRecord& nomination) {
                    trace_named_step(
                        trace,
                        kind == NamespaceNominationKind::InlineImplicit
                            ? "follow inline namespace tag: "
                            : "follow namespace nomination tag: ",
                        name);
                    auto nomination_result = lookup_tag_in_context_graph(
                        name,
                        nomination.nominated_context.get(),
                        nomination.nominated_context->next_lookup_event_index(),
                        visited_contexts,
                        trace);
                    if (nomination_result.found) {
                        nomination_match = nomination_result;
                        return true;
                    }
                    return false;
                });
            return nomination_match;
        };

    auto inline_result =
        search_nominated_tags(NamespaceNominationKind::InlineImplicit);
    if (inline_result.found) {
        return inline_result;
    }
    auto nominated_result =
        search_nominated_tags(NamespaceNominationKind::UsingDirective);
    if (nominated_result.found) {
        return nominated_result;
    }

    return result;
}

OrdinaryBindingSetResult collect_ordinary_bindings_in_context_graph(
    const std::string& name,
    const DeclContext* context,
    const std::shared_ptr<Scope>& context_scope,
    uint64_t lookup_position,
    LookupEngine::OrdinaryFilter filter,
    LookupEngine::NamespaceReachability reachability,
    std::unordered_set<const DeclContext*>& visited_contexts,
    LookupEngine::LookupTrace* trace) {
    OrdinaryBindingSetResult result;
    context = canonical_decl_context(context);
    if (!context || !visited_contexts.insert(context).second) {
        return result;
    }

    lookup_position = effective_lookup_position(context, lookup_position);
    auto* binding = lookup_context_local(context, name, LookupNamespace::Ordinary);
    if (binding) {
        if (binding_matches_ordinary_filter(binding, filter)) {
            trace_named_step(trace, "hit decl-context qualified ordinary: ", name);
            append_unique_binding_match(
                result.bindings,
                binding,
                context,
                context_scope);
        } else {
            trace_named_step(
                trace,
                "blocked by non-matching qualified ordinary binding: ",
                name);
            result.blocked = true;
        }
        return result;
    }
    trace_named_step(trace, "miss decl-context qualified ordinary: ", name);

    auto append_nominated_ordinary_bindings = [&](NamespaceNominationKind kind) {
        visit_visible_namespace_nominations_of_kind(
            context,
            lookup_position,
            kind,
            [&](const NamespaceNominationRecord& nomination) {
                trace_named_step(
                    trace,
                    kind == NamespaceNominationKind::InlineImplicit
                        ? "follow inline namespace qualified ordinary: "
                        : "follow namespace nomination qualified ordinary: ",
                    name);
                auto nomination_result = collect_ordinary_bindings_in_context_graph(
                    name,
                    nomination.nominated_context.get(),
                    resolve_direct_child_namespace_scope(
                        context,
                        nomination.nominated_context.get()),
                    nomination.nominated_context->next_lookup_event_index(),
                    filter,
                    reachability,
                    visited_contexts,
                    trace);
                for (const auto& candidate : nomination_result.bindings) {
                    append_unique_binding_match(
                        result.bindings,
                        candidate.binding,
                        candidate.owner_context,
                        candidate.owner_scope);
                }
                result.blocked = result.blocked || nomination_result.blocked;
                return false;
            });
    };

    if (namespace_reachability_includes_inline(reachability)) {
        append_nominated_ordinary_bindings(NamespaceNominationKind::InlineImplicit);
    }
    if (namespace_reachability_includes_using(reachability)) {
        append_nominated_ordinary_bindings(NamespaceNominationKind::UsingDirective);
    }

    return result;
}

const DeclBinding* lookup_template_binding_in_context_graph(
    const std::string& name,
    const DeclContext* context,
    uint64_t lookup_position,
    LookupNamespace lookup_namespace,
    std::unordered_set<const DeclContext*>& visited_contexts,
    LookupEngine::LookupTrace* trace) {
    context = canonical_decl_context(context);
    if (!context || !visited_contexts.insert(context).second) {
        return nullptr;
    }

    lookup_position = effective_lookup_position(context, lookup_position);
    auto* binding = lookup_context_local(context, name, lookup_namespace);
    if (binding) {
        if (binding_has_template_entity(binding)) {
            trace_named_step(trace, "hit template binding: ", name);
            return binding;
        }
        trace_named_step(trace, "blocked by non-template binding: ", name);
        return nullptr;
    }
    trace_named_step(trace, "miss template binding: ", name);

    const DeclBinding* found = nullptr;
    auto search_nominations_of_kind = [&](NamespaceNominationKind kind) {
        visit_visible_namespace_nominations_of_kind(
            context,
            lookup_position,
            kind,
            [&](const NamespaceNominationRecord& nomination) {
                trace_named_step(
                    trace,
                    kind == NamespaceNominationKind::InlineImplicit
                        ? "follow inline namespace template binding: "
                        : "follow namespace nomination template binding: ",
                    name);
                found = lookup_template_binding_in_context_graph(
                    name,
                    nomination.nominated_context.get(),
                    nomination.nominated_context->next_lookup_event_index(),
                    lookup_namespace,
                    visited_contexts,
                    trace);
                return found != nullptr;
            });
    };

    search_nominations_of_kind(NamespaceNominationKind::InlineImplicit);
    if (found) {
        return found;
    }
    search_nominations_of_kind(NamespaceNominationKind::UsingDirective);
    return found;
}
}

LookupEngine::LookupEnvironment LookupEngine::build_unqualified_environment(
    const std::shared_ptr<Scope>& start_scope,
    bool look_parents,
    LookupTrace* trace) {
    LookupEnvironment environment;
    std::unordered_set<const DeclContext*> visited_contexts;
    size_t depth = 0;
    for (auto scope = start_scope;
         scope;
         scope = look_parents ? scope->parent : nullptr, ++depth) {
        trace_scope_step(trace, depth, scope->flags);
        auto* context = canonical_decl_context(scope->associated_decl_context);
        if (!context || !visited_contexts.insert(context).second) {
            if (!look_parents) {
                break;
            }
            continue;
        }
        environment.frames.push_back(LookupEnvironmentFrame{
            scope,
            context,
            context->next_lookup_event_index(),
            depth});
        if (!look_parents) {
            break;
        }
    }
    return environment;
}

std::shared_ptr<Symbol> LookupEngine::lookup_unqualified_ordinary(
    const std::string& name,
    const std::shared_ptr<Scope>& start_scope,
    bool look_parents,
    OrdinaryFilter filter,
    LookupTrace* trace) {
    auto environment = build_unqualified_environment(start_scope, look_parents, trace);
    for (const auto& frame : environment.frames) {
        std::unordered_set<const DeclContext*> visited_contexts;
        auto result = lookup_ordinary_in_context_graph(
            name,
            frame.decl_context,
            frame.lookup_position,
            filter,
            visited_contexts,
            trace);
        if (result.disposition == ContextLookupDisposition::Found) {
            return result.symbol;
        }
        if (result.disposition == ContextLookupDisposition::Blocked) {
            return nullptr;
        }
    }
    trace_named_step(trace, "lookup miss: ", name);
    return nullptr;
}

const DeclBinding* LookupEngine::lookup_unqualified_template_binding(
    const std::string& name,
    const std::shared_ptr<Scope>& start_scope,
    bool look_parents,
    LookupNamespace lookup_namespace,
    LookupTrace* trace) {

    std::unordered_set<const DeclContext*> visited_contexts;
    size_t depth = 0;
    for (auto scope = start_scope; scope; scope = look_parents ? scope->parent : nullptr, ++depth) {
        trace_scope_step(trace, depth, scope->flags);
        if (scope->associated_decl_context &&
            visited_contexts.insert(scope->associated_decl_context).second) {
            const DeclContext* context =
                canonical_decl_context(scope->associated_decl_context);
            const DeclBinding* binding = nullptr;
            if (context &&
                (context->kind() == DeclContextKind::Namespace ||
                 context->kind() == DeclContextKind::TranslationUnit)) {
                std::unordered_set<const DeclContext*> visited_context_graph;
                binding = lookup_template_binding_in_context_graph(
                    name,
                    context,
                    context->next_lookup_event_index(),
                    lookup_namespace,
                    visited_context_graph,
                    trace);
            } else {
                binding = lookup_context_local(context, name, lookup_namespace);
                if (binding) {
                    if (binding_has_template_entity(binding)) {
                        trace_named_step(trace, "hit template binding: ", name);
                        return binding;
                    }
                    trace_named_step(trace, "blocked by non-template binding: ", name);
                    return nullptr;
                }
                trace_named_step(trace, "miss template binding: ", name);
            }
            if (binding) {
                return binding;
            }
        }

        if (!look_parents) {
            break;
        }
    }
    trace_named_step(trace, "template lookup miss: ", name);
    return nullptr;
}

std::vector<LookupEngine::QualifiedOrdinaryBindingMatch>
LookupEngine::lookup_qualified_ordinary_bindings(
    const std::string& name,
    const DeclContext* start_decl_context,
    const std::shared_ptr<Scope>& start_scope,
    OrdinaryFilter filter,
    NamespaceReachability reachability) {

    if (!start_decl_context || name.empty()) {
        return {};
    }

    start_decl_context = canonical_decl_context(start_decl_context);
    bool use_namespace_graph =
        start_decl_context &&
        (start_decl_context->kind() == DeclContextKind::Namespace ||
         start_decl_context->kind() == DeclContextKind::TranslationUnit);

    if (use_namespace_graph) {
        std::unordered_set<const DeclContext*> visited_contexts;
        auto ordinary_results = collect_ordinary_bindings_in_context_graph(
            name,
            start_decl_context,
            start_scope,
            start_decl_context->next_lookup_event_index(),
            filter,
            reachability,
            visited_contexts,
            nullptr);
        return ordinary_results.bindings;
    }

    auto* binding = lookup_context_local(
        start_decl_context,
        name,
        LookupNamespace::Ordinary);
    if (!binding || !binding_matches_ordinary_filter(binding, filter)) {
        return {};
    }
    return {
        QualifiedOrdinaryBindingMatch{
            binding,
            start_decl_context,
            start_scope}};
}

LookupEngine::QualifiedLookupResult LookupEngine::lookup_qualified(
    const std::string& name,
    const DeclContext* start_decl_context,
    LookupNamespace lookup_namespace,
    OrdinaryFilter filter) {

    QualifiedLookupResult result;
    if (!start_decl_context || name.empty()) {
        return result;
    }

    start_decl_context = canonical_decl_context(start_decl_context);
    bool use_namespace_graph =
        start_decl_context &&
        (start_decl_context->kind() == DeclContextKind::Namespace ||
         start_decl_context->kind() == DeclContextKind::TranslationUnit);

    if (use_namespace_graph &&
        lookup_namespace_contains(lookup_namespace, LookupNamespace::Ordinary)) {
        std::unordered_set<const DeclContext*> visited_contexts;
        auto ordinary_results = collect_ordinary_bindings_in_context_graph(
            name,
            start_decl_context,
            nullptr,
            start_decl_context->next_lookup_event_index(),
            filter,
            NamespaceReachability::FullyVisible,
            visited_contexts,
            nullptr);
        if (ordinary_results.bindings.empty()) {
            result.status = QualifiedLookupStatus::NotFound;
            return result;
        }
        if (ordinary_results.bindings.size() == 1) {
            result.status = QualifiedLookupStatus::Found;
            result.binding = ordinary_results.bindings.front().binding;
            result.symbol = select_binding_symbol(result.binding, filter);
            return result;
        }

        bool can_merge_functions = true;
        std::vector<const DeclBinding*> ordinary_bindings;
        ordinary_bindings.reserve(ordinary_results.bindings.size());
        for (const auto& match : ordinary_results.bindings) {
            const auto* binding = match.binding;
            ordinary_bindings.push_back(binding);
            if (binding_has_non_function_ordinary_entity(binding) ||
                !binding_has_function_family_entity(binding)) {
                can_merge_functions = false;
                break;
            }
        }
        if (!can_merge_functions) {
            result.status = QualifiedLookupStatus::Unsupported;
            result.unsupported_reason = "ambiguous qualified namespace lookup";
            return result;
        }

        result.owned_binding = synthesize_merged_function_binding(
            name,
            ordinary_bindings,
            filter);
        result.binding = result.owned_binding.get();
        result.symbol = select_binding_symbol(result.binding, filter);
        result.status = QualifiedLookupStatus::Found;
        return result;
    }

    if (use_namespace_graph &&
        lookup_namespace == LookupNamespace::Tag) {
        std::unordered_set<const DeclContext*> visited_contexts;
        auto tag_result = lookup_tag_in_context_graph(
            name,
            start_decl_context,
            start_decl_context->next_lookup_event_index(),
            visited_contexts,
            nullptr);
        if (!tag_result.found || !tag_result.binding) {
            result.status = QualifiedLookupStatus::NotFound;
            return result;
        }
        result.status = QualifiedLookupStatus::Found;
        result.binding = tag_result.binding;
        result.symbol = select_binding_symbol(result.binding, filter);
        return result;
    }

    auto* binding = lookup_context_local(start_decl_context, name, lookup_namespace);
    if (!binding) {
        result.status = QualifiedLookupStatus::NotFound;
        return result;
    }
    if (lookup_namespace_contains(lookup_namespace, LookupNamespace::Ordinary) &&
        lookup_namespace_contains(binding->lookup_namespace, LookupNamespace::Ordinary) &&
        !binding_matches_ordinary_filter(binding, filter)) {
        result.status = QualifiedLookupStatus::NotFound;
        return result;
    }

    result.status = QualifiedLookupStatus::Found;
    result.binding = binding;
    result.symbol = select_binding_symbol(binding, filter);
    return result;
}

LookupEngine::QualifiedLookupResult LookupEngine::lookup_qualified_name(
    const QualifiedNameSpec& name_spec,
    const DeclContext* start_decl_context,
    LookupNamespace lookup_namespace,
    OrdinaryFilter filter) {

    QualifiedLookupResult result;
    if (name_spec.terminal_name.empty() || !start_decl_context) {
        return result;
    }

    const DeclContext* resolved_context = start_decl_context;
    if (name_spec.has_global_qualifier) {
        resolved_context = translation_unit_context(start_decl_context);
    }

    for (size_t idx = 0; idx < name_spec.qualifiers.size(); ++idx) {
        bool allow_enclosing_lookup = (!name_spec.has_global_qualifier && idx == 0);
        resolved_context = resolve_named_child_context(
            resolved_context, name_spec.qualifiers[idx], allow_enclosing_lookup);
        if (!resolved_context) {
            result.status = QualifiedLookupStatus::NotFound;
            return result;
        }
    }

    return lookup_qualified(
        name_spec.terminal_name, resolved_context, lookup_namespace, filter);
}

std::vector<std::shared_ptr<Symbol>> LookupEngine::lookup_unqualified_function_candidates(
    const std::string& name,
    const std::shared_ptr<Scope>& start_scope,
    bool look_parents,
    LookupTrace* trace) {
    auto environment = build_unqualified_environment(start_scope, look_parents, trace);
    for (const auto& frame : environment.frames) {
        std::unordered_set<const DeclContext*> visited_contexts;
        auto result = lookup_functions_in_context_graph(
            name,
            frame.decl_context,
            frame.lookup_position,
            visited_contexts,
            trace);
        if (result.blocked) {
            return {};
        }
        if (result.found) {
            return result.candidates;
        }
    }

    trace_named_step(trace, "lookup miss function candidates: ", name);
    return {};
}

TagDecl* LookupEngine::lookup_tag_decl(const std::string& tag,
                                       const std::shared_ptr<Scope>& start_scope,
                                       bool look_parents,
                                       LookupTrace* trace) {

    if (tag.empty()) {
        return nullptr;
    }

    auto environment = build_unqualified_environment(start_scope, look_parents, trace);
    for (const auto& frame : environment.frames) {
        std::unordered_set<const DeclContext*> visited_contexts;
        auto result = lookup_tag_in_context_graph(
            tag,
            frame.decl_context,
            frame.lookup_position,
            visited_contexts,
            trace);
        if (!result.found) {
            continue;
        }
        if (result.decl) {
            return result.decl;
        }
        if (result.binding && result.binding->type) {
            return tag_decl_from_binding(result.binding);
        }
        return nullptr;
    }
    trace_named_step(trace, "lookup miss tag: ", tag);
    return nullptr;
}

std::shared_ptr<CType> LookupEngine::lookup_tag_type(const std::string& tag,
                                                     const std::shared_ptr<Scope>& start_scope,
                                                     bool look_parents,
                                                     LookupTrace* trace) {

    auto* decl = lookup_tag_decl(tag, start_scope, look_parents, trace);
    if (decl) {
        trace_named_step(trace, "tag-type from decl: ", tag);
        return decl->get_tag_type();
    }
    if (tag.empty()) {
        return nullptr;
    }

    auto environment = build_unqualified_environment(start_scope, look_parents, trace);
    for (const auto& frame : environment.frames) {
        std::unordered_set<const DeclContext*> visited_contexts;
        auto result = lookup_tag_in_context_graph(
            tag,
            frame.decl_context,
            frame.lookup_position,
            visited_contexts,
            trace);
        if (!result.found) {
            continue;
        }
        if (result.binding && result.binding->type) {
            trace_named_step(trace, "hit decl-context tag type: ", tag);
            return result.binding->type.get_shared();
        }
        if (result.decl) {
            trace_named_step(trace, "tag-type from decl: ", tag);
            return result.decl->get_tag_type();
        }
        return nullptr;
    }
    trace_named_step(trace, "lookup miss tag type: ", tag);
    return nullptr;
}

bool LookupEngine::lookup_label(const std::string& label,
                                const std::shared_ptr<Scope>& start_scope,
                                bool look_parents,
                                LookupTrace* trace) {

    if (label.empty()) {
        return false;
    }

    std::unordered_set<const DeclContext*> visited_contexts;
    size_t depth = 0;
    for (auto scope = start_scope; scope; scope = look_parents ? scope->parent : nullptr, ++depth) {
        trace_scope_step(trace, depth, scope->flags);
        if (scope->associated_decl_context &&
            visited_contexts.insert(scope->associated_decl_context).second) {
            auto* binding = lookup_context_local(
                scope->associated_decl_context, label, LookupNamespace::Label);
            if (binding) {
                trace_named_step(trace, "hit decl-context label: ", label);
                return true;
            }
            trace_named_step(trace, "miss decl-context label: ", label);
        }
        if (!look_parents) {
            break;
        }
    }
    trace_named_step(trace, "lookup miss label: ", label);
    return false;
}
