#include "lookup_engine.h"
#include <unordered_set>
#include "../ast/ast.h"
#include "../helpers/casting.h"
#include "decl_context.h"

namespace {
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
        auto binding = candidate->lookup_local_namespace_binding(component);
        if (binding && binding.entry && binding.entry->target_context) {
            auto* canonical = binding.entry->target_context->primary_context();
            return canonical ? canonical : binding.entry->target_context.get();
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
}

std::shared_ptr<Symbol> LookupEngine::lookup_unqualified_ordinary(
    const std::string& name,
    const std::shared_ptr<Scope>& start_scope,
    bool look_parents,
    OrdinaryFilter filter,
    LookupTrace* trace) {

    std::unordered_set<const DeclContext*> visited_contexts;
    size_t depth = 0;
    for (auto scope = start_scope; scope; scope = look_parents ? scope->parent : nullptr, ++depth) {
        trace_scope_step(trace, depth, scope->flags);
        if (scope->associated_decl_context &&
            visited_contexts.insert(scope->associated_decl_context).second) {
            auto* binding = lookup_context_local(
                scope->associated_decl_context, name, LookupNamespace::Ordinary);
            if (binding) {
                if (symbol_matches_filter(binding->symbol, filter)) {
                    trace_named_step(trace, "hit decl-context ordinary: ", name);
                    return binding->symbol;
                }
                if (filter == OrdinaryFilter::TypedefOnly) {
                    // Ordinary identifiers in inner scope hide outer typedef names.
                    trace_named_step(
                        trace, "blocked by non-typedef ordinary binding: ", name);
                    return nullptr;
                }
            }
            trace_named_step(trace, "miss decl-context ordinary: ", name);
        }

        if (!look_parents) {
            break;
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

    std::unordered_set<const DeclContext*> visited_contexts;
    size_t depth = 0;
    for (auto scope = start_scope; scope; scope = look_parents ? scope->parent : nullptr, ++depth) {
        trace_scope_step(trace, depth, scope->flags);
        if (scope->associated_decl_context &&
            visited_contexts.insert(scope->associated_decl_context).second) {
            auto* binding = lookup_context_local(
                scope->associated_decl_context, name, LookupNamespace::Ordinary);
            if (binding) {
                auto candidates = extract_function_candidates(binding);
                if (!candidates.empty()) {
                    trace_named_step(
                        trace, "hit decl-context function candidates: ", name);
                    return candidates;
                }
                trace_named_step(
                    trace, "ordinary-name hit is not function overload set: ", name);
                return {};
            }
            trace_named_step(trace, "miss decl-context function candidates: ", name);
        }

        if (!look_parents) {
            break;
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

    std::unordered_set<const DeclContext*> visited_contexts;
    size_t depth = 0;
    for (auto scope = start_scope; scope; scope = look_parents ? scope->parent : nullptr, ++depth) {
        trace_scope_step(trace, depth, scope->flags);
        if (scope->associated_decl_context &&
            visited_contexts.insert(scope->associated_decl_context).second) {
            auto* binding = lookup_context_local(
                scope->associated_decl_context, tag, LookupNamespace::Tag);
            if (binding) {
                if (binding->ast_decl) {
                    trace_named_step(trace, "hit decl-context tag ast: ", tag);
                    return const_cast<TagDecl*>(
                        static_cast<const TagDecl*>(binding->ast_decl));
                }
                if (binding->type) {
                    auto tag_ty = dyn_cast_shared<TagType>(binding->type.get_shared());
                    if (tag_ty && tag_ty->get_decl()) {
                        trace_named_step(trace, "hit decl-context tag type: ", tag);
                        return const_cast<TagDecl*>(tag_ty->get_decl());
                    }
                }
            }
            trace_named_step(trace, "miss decl-context tag: ", tag);
        }

        if (!look_parents) {
            break;
        }
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

    std::unordered_set<const DeclContext*> visited_contexts;
    size_t depth = 0;
    for (auto scope = start_scope; scope; scope = look_parents ? scope->parent : nullptr, ++depth) {
        trace_scope_step(trace, depth, scope->flags);
        if (scope->associated_decl_context &&
            visited_contexts.insert(scope->associated_decl_context).second) {
            auto* binding = lookup_context_local(
                scope->associated_decl_context, tag, LookupNamespace::Tag);
            if (binding && binding->type) {
                trace_named_step(trace, "hit decl-context tag type: ", tag);
                return binding->type.get_shared();
            }
            trace_named_step(trace, "miss decl-context tag type: ", tag);
        }

        if (!look_parents) {
            break;
        }
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
