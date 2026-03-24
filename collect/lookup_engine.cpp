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
    std::vector<const DeclBinding*> bindings;
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

    for (const auto& nomination : context->namespace_nominations()) {
        if (!nomination_is_visible(nomination, lookup_position) ||
            !nomination.nominated_context) {
            continue;
        }
        trace_named_step(trace, "follow namespace nomination ordinary: ", name);
        auto nomination_result = lookup_ordinary_in_context_graph(
            name,
            nomination.nominated_context.get(),
            nomination.nominated_context->next_lookup_event_index(),
            filter,
            visited_contexts,
            trace);
        if (nomination_result.disposition != ContextLookupDisposition::NotFound) {
            return nomination_result;
        }
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

    for (const auto& nomination : context->namespace_nominations()) {
        if (!nomination_is_visible(nomination, lookup_position) ||
            !nomination.nominated_context) {
            continue;
        }
        trace_named_step(trace, "follow namespace nomination functions: ", name);
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
    }

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

    for (const auto& nomination : context->namespace_nominations()) {
        if (!nomination_is_visible(nomination, lookup_position) ||
            !nomination.nominated_context) {
            continue;
        }
        trace_named_step(trace, "follow namespace nomination tag: ", name);
        auto nomination_result = lookup_tag_in_context_graph(
            name,
            nomination.nominated_context.get(),
            nomination.nominated_context->next_lookup_event_index(),
            visited_contexts,
            trace);
        if (nomination_result.found) {
            return nomination_result;
        }
    }

    return result;
}

OrdinaryBindingSetResult collect_ordinary_bindings_in_context_graph(
    const std::string& name,
    const DeclContext* context,
    uint64_t lookup_position,
    LookupEngine::OrdinaryFilter filter,
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
            append_unique_binding(result.bindings, binding);
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

    for (const auto& nomination : context->namespace_nominations()) {
        if (!nomination_is_visible(nomination, lookup_position) ||
            !nomination.nominated_context) {
            continue;
        }
        trace_named_step(trace, "follow namespace nomination qualified ordinary: ", name);
        auto nomination_result = collect_ordinary_bindings_in_context_graph(
            name,
            nomination.nominated_context.get(),
            nomination.nominated_context->next_lookup_event_index(),
            filter,
            visited_contexts,
            trace);
        for (const auto* candidate : nomination_result.bindings) {
            append_unique_binding(result.bindings, candidate);
        }
        result.blocked = result.blocked || nomination_result.blocked;
    }

    return result;
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
            auto* binding = lookup_context_local(
                scope->associated_decl_context, name, lookup_namespace);
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

        if (!look_parents) {
            break;
        }
    }
    trace_named_step(trace, "template lookup miss: ", name);
    return nullptr;
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
            start_decl_context->next_lookup_event_index(),
            filter,
            visited_contexts,
            nullptr);
        if (ordinary_results.bindings.empty()) {
            result.status = QualifiedLookupStatus::NotFound;
            return result;
        }
        if (ordinary_results.bindings.size() == 1) {
            result.status = QualifiedLookupStatus::Found;
            result.binding = ordinary_results.bindings.front();
            result.symbol = select_binding_symbol(result.binding, filter);
            return result;
        }

        bool can_merge_functions = true;
        for (const auto* binding : ordinary_results.bindings) {
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
            ordinary_results.bindings,
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
