#include "decl_context.h"
#include <algorithm>
#include <atomic>
#include "../ast/ast.h"
#include "../ast/ast_context.h"
#include "../helpers/casting.h"

namespace {
std::atomic<uint64_t> g_next_decl_context_stable_id{1};

template <typename T>
void append_unique(std::vector<T>& values, const T& value) {
    for (const auto& existing : values) {
        if (existing == value) {
            return;
        }
    }
    values.push_back(value);
}
}

DeclContext::DeclContext(
    DeclContextKind kind,
    std::shared_ptr<ASTContext> ast_ctx,
    std::shared_ptr<std::unordered_set<std::string>> local_intern_pool,
    DeclContext* lexical_parent,
    DeclContext* semantic_parent,
    const Decl* owner_decl,
    std::string lookup_name)
    : ast_ctx_(std::move(ast_ctx)),
      local_intern_pool_(std::move(local_intern_pool)),
      kind_(kind),
      lexical_parent_(lexical_parent),
      semantic_parent_(semantic_parent ? semantic_parent : lexical_parent),
      primary_context_(this),
      stable_id_(g_next_decl_context_stable_id.fetch_add(
          1, std::memory_order_relaxed)),
      owner_decl_(owner_decl),
      lookup_name_(std::move(lookup_name)) {
    interned_lookup_name_ = intern_name(lookup_name_);
}

std::shared_ptr<DeclContext> DeclContext::create_translation_unit(
    std::shared_ptr<ASTContext> ast_ctx) {
    auto local_intern_pool =
        std::make_shared<std::unordered_set<std::string>>();
    auto tu = std::make_shared<DeclContext>(
        DeclContextKind::TranslationUnit,
        std::move(ast_ctx),
        std::move(local_intern_pool));
    tu->set_primary_context(tu.get());
    return tu;
}

std::shared_ptr<DeclContext> DeclContext::add_lexical_child(
    DeclContextKind kind,
    DeclContext* semantic_parent,
    const Decl* owner_decl,
    std::string lookup_name) {
    auto child = std::make_shared<DeclContext>(
        kind,
        ast_ctx_,
        local_intern_pool_,
        this,
        semantic_parent ? semantic_parent : this,
        owner_decl,
        std::move(lookup_name));
    lexical_children_.push_back(child);
    index_lexical_child_name(child.get());
    return child;
}

InternedName DeclContext::intern_name(std::string_view spelling) const {
    if (spelling.empty()) {
        return nullptr;
    }
    if (ast_ctx_) {
        (void)ast_ctx_->intern_identifier(spelling);
    }
    auto [it, _] = local_intern_pool_->emplace(spelling);
    return &(*it);
}

void DeclContext::set_lookup_name(std::string lookup_name) {
    InternedName new_interned_name = intern_name(lookup_name);
    if (lookup_name_ == lookup_name &&
        interned_lookup_name_ == new_interned_name) {
        return;
    }
    if (lexical_parent_) {
        lexical_parent_->remove_lexical_child_name(this, interned_lookup_name_);
    }
    lookup_name_ = std::move(lookup_name);
    interned_lookup_name_ = new_interned_name;
    if (lexical_parent_) {
        lexical_parent_->index_lexical_child_name(this);
    }
}

void DeclContext::index_lexical_child_name(DeclContext* child) {
    if (!child || !child->interned_lookup_name()) {
        return;
    }
    named_lexical_children_[child->interned_lookup_name()].push_back(child);
}

void DeclContext::remove_lexical_child_name(DeclContext* child,
                                            InternedName lookup_name) {
    if (!child || !lookup_name) {
        return;
    }
    auto it = named_lexical_children_.find(lookup_name);
    if (it == named_lexical_children_.end()) {
        return;
    }
    auto& children = it->second;
    children.erase(
        std::remove(children.begin(), children.end(), child),
        children.end());
    if (children.empty()) {
        named_lexical_children_.erase(it);
    }
}

DeclContext* DeclContext::find_named_lexical_child(
    std::string_view lookup_name) const {
    return find_named_lexical_child(intern_name(lookup_name));
}

DeclContext* DeclContext::find_named_lexical_child(InternedName lookup_name) const {
    if (!lookup_name) {
        return nullptr;
    }
    auto by_name_it = named_lexical_children_.find(lookup_name);
    if (by_name_it == named_lexical_children_.end()) {
        return nullptr;
    }
    const auto& named_children = by_name_it->second;
    for (auto it = named_children.rbegin(); it != named_children.rend(); ++it) {
        if (*it) {
            return *it;
        }
    }
    return nullptr;
}

DeclContext::BindingSlot* DeclContext::lookup_slot(InternedName name,
                                                   LookupNamespace ns) {
    return const_cast<BindingSlot*>(
        static_cast<const DeclContext*>(this)->lookup_slot(name, ns));
}

const DeclContext::BindingSlot* DeclContext::lookup_slot(
    InternedName name,
    LookupNamespace ns) const {
    if (!name) {
        return nullptr;
    }
    const auto* map = [&]() -> const std::unordered_map<InternedName, std::unique_ptr<BindingSlot>>* {
        switch (ns) {
            case LookupNamespace::Tag:
                return &tag_slots_;
            case LookupNamespace::Label:
                return &label_slots_;
            case LookupNamespace::Ordinary:
            case LookupNamespace::None:
            default:
                return &ordinary_slots_;
        }
    }();
    auto it = map->find(name);
    return it == map->end() ? nullptr : it->second.get();
}

DeclContext::BindingSlot& DeclContext::ensure_slot(InternedName name,
                                                   std::string_view spelled_name,
                                                   LookupNamespace ns) {
    auto& map = [&]() -> std::unordered_map<InternedName, std::unique_ptr<BindingSlot>>& {
        switch (ns) {
            case LookupNamespace::Tag:
                return tag_slots_;
            case LookupNamespace::Label:
                return label_slots_;
            case LookupNamespace::Ordinary:
            case LookupNamespace::None:
            default:
                return ordinary_slots_;
        }
    }();
    auto [it, inserted] = map.emplace(name, nullptr);
    if (inserted || !it->second) {
        auto slot = std::make_unique<BindingSlot>();
        slot->interned_name = name;
        slot->lookup_namespace = ns;
        slot->spelled_name =
            spelled_name.empty() && name ? *name : std::string(spelled_name);
        it->second = std::move(slot);
    } else if (it->second->spelled_name.empty() && name) {
        it->second->spelled_name = *name;
    }
    return *it->second;
}

void DeclContext::refresh_cached_binding(BindingSlot& slot) {
    DeclBinding rebuilt;
    size_t source_index = slot.visible_decl_index != k_no_decl_index
                              ? slot.visible_decl_index
                              : slot.last_update_decl_index;
    if (source_index != k_no_decl_index && source_index < declarations_.size()) {
        rebuilt = declarations_[source_index];
    }

    rebuilt.name =
        !slot.spelled_name.empty()
            ? slot.spelled_name
            : (slot.interned_name ? *slot.interned_name : std::string());
    rebuilt.interned_name = slot.interned_name;
    rebuilt.lookup_namespace = slot.lookup_namespace;
    rebuilt.ordinary_entry_kind = OrdinaryEntryKind::SingleSymbol;
    rebuilt.overload_candidates.clear();
    rebuilt.template_overload_candidates.clear();

    if (slot.lookup_namespace == LookupNamespace::Ordinary &&
        !slot.overload_candidates.empty()) {
        rebuilt.overload_candidates = slot.overload_candidates;
        rebuilt.symbol = slot.overload_candidates.front();
        if (slot.overload_candidates.size() > 1) {
            rebuilt.ordinary_entry_kind = OrdinaryEntryKind::OverloadSet;
        }
    }

    if (!slot.template_candidates.empty()) {
        rebuilt.template_overload_candidates = slot.template_candidates;
        // The visible template binding should reflect the most recent
        // declaration in this context. Keeping the first declaration here
        // causes forward declarations to mask later definitions.
        rebuilt.template_decl = slot.template_candidates.back();
    } else {
        rebuilt.template_decl = nullptr;
    }

    if (slot.lookup_namespace == LookupNamespace::Tag &&
        rebuilt.type.is_null()) {
        if (auto* tag_decl =
                dyn_cast<TagDecl>(const_cast<Decl*>(rebuilt.ast_decl))) {
            rebuilt.type = tag_decl->get_tag_type();
            rebuilt.symbol_kind = SymbolKind::TYPE;
        }
        if (auto* class_template =
                dyn_cast<ClassTemplateDecl>(
                    const_cast<Decl*>(rebuilt.template_decl))) {
            if (auto* semantic_decl = class_template->pattern_semantic_decl()) {
                rebuilt.ast_decl = semantic_decl;
                rebuilt.type = semantic_decl->get_tag_type();
                rebuilt.symbol_kind = SymbolKind::TYPE;
            }
        }
    }

    slot.cached_binding = std::move(rebuilt);
}

void DeclContext::replay_binding_into_slot(const DeclBinding& binding, size_t idx) {
    InternedName interned_name = binding.interned_name
                                     ? binding.interned_name
                                     : intern_name(binding.name);
    if (!interned_name) {
        return;
    }

    BindingSlot& slot = ensure_slot(
        interned_name,
        binding.name.empty() && interned_name ? *interned_name : binding.name,
        binding.lookup_namespace);

    const size_t previous_visible_decl_index = slot.visible_decl_index;
    const DeclBinding* previous_visible_binding =
        previous_visible_decl_index != k_no_decl_index &&
                previous_visible_decl_index < declarations_.size()
            ? &declarations_[previous_visible_decl_index]
            : nullptr;

    bool contributes_visible_decl =
        binding.symbol != nullptr ||
        binding.lookup_namespace == LookupNamespace::Tag ||
        binding.lookup_namespace == LookupNamespace::Label ||
        (binding.ast_decl != nullptr && binding.template_decl == nullptr);

    if (contributes_visible_decl) {
        slot.visible_decl_index = idx;
    }
    slot.last_update_decl_index = idx;

    if (binding.lookup_namespace == LookupNamespace::Ordinary) {
        if (binding.has_overload_set()) {
            slot.overload_candidates.clear();
            append_unique(slot.overload_candidates, binding.symbol);
            for (const auto& candidate : binding.overload_candidates) {
                append_unique(slot.overload_candidates, candidate);
            }
        } else if (binding.symbol && binding.symbol->kind == SymbolKind::FUNCTION) {
            bool extends_existing_family =
                previous_visible_binding &&
                previous_visible_binding->symbol &&
                previous_visible_binding->symbol->kind == SymbolKind::FUNCTION;
            if (!extends_existing_family) {
                slot.overload_candidates.clear();
            } else if (slot.overload_candidates.empty()) {
                append_unique(slot.overload_candidates,
                              previous_visible_binding->symbol);
            }
            append_unique(slot.overload_candidates, binding.symbol);
        } else if (contributes_visible_decl) {
            slot.overload_candidates.clear();
        }
    } else {
        slot.overload_candidates.clear();
    }

    if (binding.template_decl) {
        append_unique(slot.template_candidates, binding.template_decl);
    }
    for (const auto* candidate : binding.template_overload_candidates) {
        append_unique(slot.template_candidates, candidate);
    }

    refresh_cached_binding(slot);
}

void DeclContext::rebuild_binding_slots() {
    ordinary_slots_.clear();
    tag_slots_.clear();
    label_slots_.clear();
    for (size_t idx = 0; idx < declarations_.size(); ++idx) {
        replay_binding_into_slot(declarations_[idx], idx);
    }
}

void DeclContext::add_declaration(DeclBinding binding) {
    InternedName interned_name = binding.interned_name
                                     ? binding.interned_name
                                     : intern_name(binding.name);
    if (!interned_name) {
        return;
    }
    binding.interned_name = interned_name;
    if (binding.name.empty()) {
        binding.name = *interned_name;
    }
    allocate_lookup_event_index();
    const size_t idx = declarations_.size();
    declarations_.push_back(std::move(binding));
    replay_binding_into_slot(declarations_.back(), idx);
}

void DeclContext::truncate_declarations(size_t count) {
    if (count >= declarations_.size()) {
        return;
    }
    declarations_.resize(count);
    rebuild_binding_slots();
}

void DeclContext::truncate_lexical_children(size_t count) {
    if (count >= lexical_children_.size()) {
        return;
    }

    for (size_t idx = count; idx < lexical_children_.size(); ++idx) {
        auto& child = lexical_children_[idx];
        if (!child) {
            continue;
        }
        remove_lexical_child_name(child.get(), child->interned_lookup_name());
    }
    lexical_children_.resize(count);
}

void DeclContext::reindex_namespace_bindings() {
    namespace_binding_indices_.clear();
    for (size_t idx = 0; idx < namespace_bindings_.size(); ++idx) {
        auto& binding = namespace_bindings_[idx];
        if (binding.interned_local_name == nullptr) {
            binding.interned_local_name = intern_name(binding.local_name);
        }
        if (binding.interned_local_name) {
            namespace_binding_indices_[binding.interned_local_name] = idx;
        }
    }
}

void DeclContext::reindex_namespace_aliases() {
    namespace_alias_indices_.clear();
    for (size_t idx = 0; idx < namespace_aliases_.size(); ++idx) {
        auto& alias = namespace_aliases_[idx];
        if (alias.interned_local_name == nullptr) {
            alias.interned_local_name = intern_name(alias.local_name);
        }
        if (alias.interned_local_name) {
            namespace_alias_indices_[alias.interned_local_name] = idx;
        }
    }
}

void DeclContext::truncate_namespace_bindings(size_t count) {
    if (count >= namespace_bindings_.size()) {
        return;
    }
    namespace_bindings_.resize(count);
    reindex_namespace_bindings();
}

void DeclContext::truncate_namespace_aliases(size_t count) {
    if (count >= namespace_aliases_.size()) {
        return;
    }
    namespace_aliases_.resize(count);
    reindex_namespace_aliases();
}

void DeclContext::truncate_namespace_nominations(size_t count) {
    if (count >= namespace_nominations_.size()) {
        return;
    }
    namespace_nominations_.resize(count);
}

void DeclContext::set_inline_namespace(bool is_inline,
                                       DeclContext* enclosing_namespace) {
    is_inline_namespace_ = is_inline;
    inline_enclosing_namespace_ = is_inline ? enclosing_namespace : nullptr;
}

const DeclBinding* DeclContext::lookup_local(const std::string& name,
                                             LookupNamespace ns) const {
    return lookup_local(intern_name(name), ns);
}

const DeclBinding* DeclContext::lookup_local(InternedName name,
                                             LookupNamespace ns) const {
    const BindingSlot* selected = nullptr;

    auto try_namespace = [&](LookupNamespace single_ns) {
        const auto* slot = lookup_slot(name, single_ns);
        if (!slot) {
            return;
        }
        if (!selected || slot->last_update_decl_index >=
                             selected->last_update_decl_index) {
            selected = slot;
        }
    };

    if (lookup_namespace_contains(ns, LookupNamespace::Ordinary)) {
        try_namespace(LookupNamespace::Ordinary);
    }
    if (lookup_namespace_contains(ns, LookupNamespace::Tag)) {
        try_namespace(LookupNamespace::Tag);
    }
    if (lookup_namespace_contains(ns, LookupNamespace::Label)) {
        try_namespace(LookupNamespace::Label);
    }
    return selected ? &selected->cached_binding : nullptr;
}

std::vector<const DeclBinding*> DeclContext::lookup_local_all(
    const std::string& name,
    LookupNamespace ns) const {
    return lookup_local_all(intern_name(name), ns);
}

std::vector<const DeclBinding*> DeclContext::lookup_local_all(
    InternedName name,
    LookupNamespace ns) const {
    std::vector<const DeclBinding*> out;
    if (!name) {
        return out;
    }
    for (const auto& binding : declarations_) {
        if (binding.interned_name != name) {
            continue;
        }
        if (!lookup_namespace_contains(ns, binding.lookup_namespace)) {
            continue;
        }
        out.push_back(&binding);
    }
    return out;
}

const NamespaceBindingEntry* DeclContext::lookup_local_namespace(
    std::string_view local_name) const {
    return lookup_local_namespace(intern_name(local_name));
}

const NamespaceBindingEntry* DeclContext::lookup_local_namespace(
    InternedName local_name) const {
    if (!local_name) {
        return nullptr;
    }
    auto it = namespace_binding_indices_.find(local_name);
    if (it == namespace_binding_indices_.end()) {
        return nullptr;
    }
    return &namespace_bindings_[it->second];
}

const NamespaceBindingEntry* DeclContext::lookup_local_namespace_alias(
    std::string_view local_name) const {
    return lookup_local_namespace_alias(intern_name(local_name));
}

const NamespaceBindingEntry* DeclContext::lookup_local_namespace_alias(
    InternedName local_name) const {
    if (!local_name) {
        return nullptr;
    }
    auto it = namespace_alias_indices_.find(local_name);
    if (it == namespace_alias_indices_.end()) {
        return nullptr;
    }
    return &namespace_aliases_[it->second];
}

NamespaceBindingLookup DeclContext::lookup_local_namespace_binding(
    std::string_view local_name) const {
    return lookup_local_namespace_binding(intern_name(local_name));
}

NamespaceBindingLookup DeclContext::lookup_local_namespace_binding(
    InternedName local_name) const {
    if (const auto* binding = lookup_local_namespace(local_name)) {
        return NamespaceBindingLookup{binding, false};
    }
    if (const auto* alias = lookup_local_namespace_alias(local_name)) {
        return NamespaceBindingLookup{alias, true};
    }
    return NamespaceBindingLookup{};
}

void DeclContext::add_namespace_binding(NamespaceBindingEntry binding) {
    binding.interned_local_name =
        binding.interned_local_name
            ? binding.interned_local_name
            : intern_name(binding.local_name);
    if (!binding.interned_local_name || !binding.target_context ||
        !binding.target_scope) {
        return;
    }
    if (binding.local_name.empty()) {
        binding.local_name = *binding.interned_local_name;
    }
    auto it = namespace_binding_indices_.find(binding.interned_local_name);
    if (it != namespace_binding_indices_.end()) {
        namespace_bindings_[it->second] = std::move(binding);
        return;
    }
    namespace_binding_indices_[binding.interned_local_name] =
        namespace_bindings_.size();
    namespace_bindings_.push_back(std::move(binding));
}

void DeclContext::add_namespace_alias(NamespaceBindingEntry alias) {
    alias.interned_local_name =
        alias.interned_local_name
            ? alias.interned_local_name
            : intern_name(alias.local_name);
    if (!alias.interned_local_name || !alias.target_context ||
        !alias.target_scope) {
        return;
    }
    if (alias.local_name.empty()) {
        alias.local_name = *alias.interned_local_name;
    }
    auto it = namespace_alias_indices_.find(alias.interned_local_name);
    if (it != namespace_alias_indices_.end()) {
        namespace_aliases_[it->second] = std::move(alias);
        return;
    }
    namespace_alias_indices_[alias.interned_local_name] =
        namespace_aliases_.size();
    namespace_aliases_.push_back(std::move(alias));
}

void DeclContext::add_namespace_nomination(NamespaceNominationRecord nomination) {
    if (!nomination.nominated_context) {
        return;
    }
    if (nomination.point_of_declaration_index == 0) {
        nomination.point_of_declaration_index = allocate_lookup_event_index();
    }
    namespace_nominations_.push_back(std::move(nomination));
}
