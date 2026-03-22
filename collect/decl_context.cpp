#include "decl_context.h"
#include <algorithm>
#include <atomic>
#include <unordered_set>

namespace {
std::atomic<uint64_t> g_next_decl_context_stable_id{1};
}

DeclContext::DeclContext(DeclContextKind kind,
                         DeclContext* lexical_parent,
                         DeclContext* semantic_parent,
                         const Decl* owner_decl,
                         std::string lookup_name)
    : kind_(kind),
      lexical_parent_(lexical_parent),
      semantic_parent_(semantic_parent ? semantic_parent : lexical_parent),
      primary_context_(this),
      stable_id_(g_next_decl_context_stable_id.fetch_add(1, std::memory_order_relaxed)),
      owner_decl_(owner_decl),
      lookup_name_(std::move(lookup_name)) {}

std::shared_ptr<DeclContext> DeclContext::create_translation_unit() {
    auto tu = std::make_shared<DeclContext>(DeclContextKind::TranslationUnit);
    tu->set_primary_context(tu.get());
    return tu;
}

std::shared_ptr<DeclContext> DeclContext::add_lexical_child(DeclContextKind kind,
                                                             DeclContext* semantic_parent,
                                                             const Decl* owner_decl,
                                                             std::string lookup_name) {
    auto child = std::make_shared<DeclContext>(
        kind,
        this,
        semantic_parent ? semantic_parent : this,
        owner_decl,
        std::move(lookup_name));
    lexical_children_.push_back(child);
    index_lexical_child_name(child.get());
    return child;
}

void DeclContext::set_lookup_name(std::string lookup_name) {
    if (lookup_name_ == lookup_name) {
        return;
    }
    if (lexical_parent_) {
        lexical_parent_->remove_lexical_child_name(this, lookup_name_);
    }
    lookup_name_ = std::move(lookup_name);
    if (lexical_parent_) {
        lexical_parent_->index_lexical_child_name(this);
    }
}

void DeclContext::index_lexical_child_name(DeclContext* child) {
    if (!child) {
        return;
    }
    const std::string& child_name = child->lookup_name();
    if (child_name.empty()) {
        return;
    }
    named_lexical_children_[child_name].push_back(child);
}

void DeclContext::remove_lexical_child_name(DeclContext* child,
                                            std::string_view lookup_name) {
    if (!child || lookup_name.empty()) {
        return;
    }
    auto it = named_lexical_children_.find(std::string(lookup_name));
    if (it == named_lexical_children_.end()) {
        return;
    }
    auto& children = it->second;
    children.erase(std::remove(children.begin(), children.end(), child), children.end());
    if (children.empty()) {
        named_lexical_children_.erase(it);
    }
}

DeclContext* DeclContext::find_named_lexical_child(
    std::string_view lookup_name) const {
    if (lookup_name.empty()) {
        return nullptr;
    }
    auto by_name_it = named_lexical_children_.find(std::string(lookup_name));
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

void DeclContext::index_binding(const DeclBinding& binding, size_t idx) {
    if (binding.name.empty()) {
        return;
    }
    if (lookup_namespace_contains(binding.lookup_namespace, LookupNamespace::Ordinary)) {
        ordinary_lookup_[binding.name].push_back(idx);
    }
    if (lookup_namespace_contains(binding.lookup_namespace, LookupNamespace::Tag)) {
        tag_lookup_[binding.name].push_back(idx);
    }
    if (lookup_namespace_contains(binding.lookup_namespace, LookupNamespace::Label)) {
        label_lookup_[binding.name].push_back(idx);
    }
}

void DeclContext::add_declaration(DeclBinding binding) {
    size_t idx = declarations_.size();
    declarations_.push_back(std::move(binding));
    index_binding(declarations_.back(), idx);
}

void DeclContext::truncate_declarations(size_t count) {
    if (count >= declarations_.size()) {
        return;
    }
    declarations_.resize(count);

    auto prune_lookup_indices =
        [count](std::unordered_map<std::string, std::vector<size_t>>& lookup_map) {
            for (auto it = lookup_map.begin(); it != lookup_map.end();) {
                auto& indices = it->second;
                indices.erase(
                    std::remove_if(indices.begin(),
                                   indices.end(),
                                   [count](size_t idx) { return idx >= count; }),
                    indices.end());
                if (indices.empty()) {
                    it = lookup_map.erase(it);
                } else {
                    ++it;
                }
            }
        };

    prune_lookup_indices(ordinary_lookup_);
    prune_lookup_indices(tag_lookup_);
    prune_lookup_indices(label_lookup_);
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
        remove_lexical_child_name(child.get(), child->lookup_name());
    }
    lexical_children_.resize(count);
}

const std::unordered_map<std::string, std::vector<size_t>>&
DeclContext::map_for_namespace(LookupNamespace ns) const {
    switch (ns) {
        case LookupNamespace::Tag:
            return tag_lookup_;
        case LookupNamespace::Label:
            return label_lookup_;
        case LookupNamespace::Ordinary:
        case LookupNamespace::None:
        default:
            return ordinary_lookup_;
    }
}

std::unordered_map<std::string, std::vector<size_t>>&
DeclContext::map_for_namespace(LookupNamespace ns) {
    switch (ns) {
        case LookupNamespace::Tag:
            return tag_lookup_;
        case LookupNamespace::Label:
            return label_lookup_;
        case LookupNamespace::Ordinary:
        case LookupNamespace::None:
        default:
            return ordinary_lookup_;
    }
}

const DeclBinding* DeclContext::lookup_local(const std::string& name,
                                             LookupNamespace ns) const {
    const DeclBinding* selected = nullptr;
    size_t selected_idx = 0;

    auto try_namespace = [&](LookupNamespace single_ns) {
        const auto& map = map_for_namespace(single_ns);
        auto it = map.find(name);
        if (it == map.end() || it->second.empty()) {
            return;
        }
        size_t idx = it->second.back();
        if (!selected || idx >= selected_idx) {
            selected = &declarations_[idx];
            selected_idx = idx;
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
    return selected;
}

std::vector<const DeclBinding*> DeclContext::lookup_local_all(const std::string& name,
                                                              LookupNamespace ns) const {
    std::vector<const DeclBinding*> out;
    std::vector<size_t> indices;
    std::unordered_set<size_t> seen;

    auto collect_namespace_indices = [&](LookupNamespace single_ns) {
        const auto& map = map_for_namespace(single_ns);
        auto it = map.find(name);
        if (it == map.end()) {
            return;
        }
        for (size_t idx : it->second) {
            if (seen.insert(idx).second) {
                indices.push_back(idx);
            }
        }
    };

    if (lookup_namespace_contains(ns, LookupNamespace::Ordinary)) {
        collect_namespace_indices(LookupNamespace::Ordinary);
    }
    if (lookup_namespace_contains(ns, LookupNamespace::Tag)) {
        collect_namespace_indices(LookupNamespace::Tag);
    }
    if (lookup_namespace_contains(ns, LookupNamespace::Label)) {
        collect_namespace_indices(LookupNamespace::Label);
    }

    std::sort(indices.begin(), indices.end());
    out.reserve(indices.size());
    for (size_t idx : indices) {
        out.push_back(&declarations_[idx]);
    }
    return out;
}
