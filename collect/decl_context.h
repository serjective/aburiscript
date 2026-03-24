#ifndef ABURI_DECL_CONTEXT_H
#define ABURI_DECL_CONTEXT_H

#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>
#include "../source_mgnt.h"
#include "../ast/symbols.h"
#include "../ast/types.h"

struct Decl;
class DeclContext;

struct NamespaceBindingEntry {
    std::string local_name;
    std::shared_ptr<DeclContext> target_context = nullptr;
    std::shared_ptr<Scope> target_scope = nullptr;
};

struct NamespaceBindingLookup {
    const NamespaceBindingEntry* entry = nullptr;
    bool is_alias = false;

    explicit operator bool() const { return entry != nullptr; }
};

enum class NamespaceNominationKind : uint8_t {
    UsingDirective,
    InlineImplicit
};

struct NamespaceNominationRecord {
    NamespaceNominationKind kind = NamespaceNominationKind::UsingDirective;
    std::shared_ptr<DeclContext> nominated_context = nullptr;
    SrcLoc introducer_loc;
    uint64_t point_of_declaration_index = 0;
};

enum class DeclContextKind : uint8_t {
    TranslationUnit,
    Function,
    Block,
    // C++ scaffold: class/struct/union declaration context.
    Record,
    Enum,
    // C++ scaffold: namespace declaration context.
    Namespace,
    // C++ scaffold: function prototype scope declaration context.
    FunctionPrototype,
    // C++ scaffold: template parameter declaration context.
    TemplateParameter
};

enum class LookupNamespace : uint32_t {
    None = 0,
    Ordinary = 1u << 0,
    Tag = 1u << 1,
    Label = 1u << 2
};

inline LookupNamespace operator|(LookupNamespace lhs, LookupNamespace rhs) {
    return static_cast<LookupNamespace>(
        static_cast<uint32_t>(lhs) | static_cast<uint32_t>(rhs));
}

inline LookupNamespace operator&(LookupNamespace lhs, LookupNamespace rhs) {
    return static_cast<LookupNamespace>(
        static_cast<uint32_t>(lhs) & static_cast<uint32_t>(rhs));
}

inline LookupNamespace& operator|=(LookupNamespace& lhs, LookupNamespace rhs) {
    lhs = lhs | rhs;
    return lhs;
}

inline bool lookup_namespace_contains(LookupNamespace set, LookupNamespace value) {
    return (set & value) != LookupNamespace::None;
}

enum class OrdinaryEntryKind : uint8_t {
    SingleSymbol,
    OverloadSet
};

struct DeclBinding {
    std::string name;
    LookupNamespace lookup_namespace = LookupNamespace::Ordinary;
    SymbolKind symbol_kind = SymbolKind::VARIABLE;
    OrdinaryEntryKind ordinary_entry_kind = OrdinaryEntryKind::SingleSymbol;
    QualType type = nullptr;
    StorageClass storage_class = StorageClass::NONE;
    VariableLinkage linkage = VariableLinkage::NONE;
    bool is_definition = false;
    const Decl* ast_decl = nullptr;
    std::shared_ptr<Symbol> symbol = nullptr;
    const Decl* template_decl = nullptr;
    // C++ scaffold: overload candidates for ordinary-name entries.
    std::vector<std::shared_ptr<Symbol>> overload_candidates;
    std::vector<const Decl*> template_overload_candidates;

    bool has_overload_set() const {
        return ordinary_entry_kind == OrdinaryEntryKind::OverloadSet;
    }

    bool has_template_overload_set() const {
        return !template_overload_candidates.empty();
    }
};

class DeclContext : public std::enable_shared_from_this<DeclContext> {
public:
    DeclContext(DeclContextKind kind,
                DeclContext* lexical_parent = nullptr,
                DeclContext* semantic_parent = nullptr,
                const Decl* owner_decl = nullptr,
                std::string lookup_name = "");

    static std::shared_ptr<DeclContext> create_translation_unit();

    std::shared_ptr<DeclContext> add_lexical_child(DeclContextKind kind,
                                                   DeclContext* semantic_parent = nullptr,
                                                   const Decl* owner_decl = nullptr,
                                                   std::string lookup_name = "");

    DeclContextKind kind() const { return kind_; }
    DeclContext* lexical_parent() const { return lexical_parent_; }
    DeclContext* semantic_parent() const { return semantic_parent_; }
    DeclContext* primary_context() const { return primary_context_; }
    uint64_t stable_id() const { return stable_id_; }
    void set_stable_id(uint64_t stable_id) { stable_id_ = stable_id; }
    void set_primary_context(DeclContext* primary) {
        primary_context_ = primary ? primary : this;
    }
    const Decl* owner_decl() const { return owner_decl_; }
    const std::string& lookup_name() const { return lookup_name_; }
    void set_lookup_name(std::string lookup_name);
    DeclContext* find_named_lexical_child(std::string_view lookup_name) const;

    const std::vector<std::shared_ptr<DeclContext>>& lexical_children() const {
        return lexical_children_;
    }

    void add_declaration(DeclBinding binding);

    const std::vector<DeclBinding>& declarations() const { return declarations_; }
    size_t declaration_count() const { return declarations_.size(); }
    size_t lexical_child_count() const { return lexical_children_.size(); }
    size_t namespace_binding_count() const { return namespace_bindings_.size(); }
    size_t namespace_alias_count() const { return namespace_aliases_.size(); }
    size_t namespace_nomination_count() const { return namespace_nominations_.size(); }
    uint64_t next_lookup_event_index() const { return next_lookup_event_index_; }
    void truncate_declarations(size_t count);
    void truncate_lexical_children(size_t count);
    void truncate_namespace_bindings(size_t count);
    void truncate_namespace_aliases(size_t count);
    void truncate_namespace_nominations(size_t count);
    void set_next_lookup_event_index(uint64_t index) {
        next_lookup_event_index_ = index == 0 ? 1 : index;
    }

    const DeclBinding* lookup_local(const std::string& name,
                                    LookupNamespace ns) const;
    std::vector<const DeclBinding*> lookup_local_all(const std::string& name,
                                                     LookupNamespace ns) const;
    const NamespaceBindingEntry* lookup_local_namespace(
        std::string_view local_name) const;
    const NamespaceBindingEntry* lookup_local_namespace_alias(
        std::string_view local_name) const;
    NamespaceBindingLookup lookup_local_namespace_binding(
        std::string_view local_name) const;
    void add_namespace_binding(NamespaceBindingEntry binding);
    void add_namespace_alias(NamespaceBindingEntry alias);
    const std::vector<NamespaceNominationRecord>& namespace_nominations() const {
        return namespace_nominations_;
    }
    void add_namespace_nomination(NamespaceNominationRecord nomination);

private:
    void index_lexical_child_name(DeclContext* child);
    void remove_lexical_child_name(DeclContext* child, std::string_view lookup_name);
    void index_binding(const DeclBinding& binding, size_t idx);
    uint64_t allocate_lookup_event_index() { return next_lookup_event_index_++; }
    void reindex_namespace_bindings();
    void reindex_namespace_aliases();
    const std::unordered_map<std::string, std::vector<size_t>>&
    map_for_namespace(LookupNamespace ns) const;
    std::unordered_map<std::string, std::vector<size_t>>&
    map_for_namespace(LookupNamespace ns);

    DeclContextKind kind_ = DeclContextKind::Block;
    DeclContext* lexical_parent_ = nullptr;
    DeclContext* semantic_parent_ = nullptr;
    DeclContext* primary_context_ = nullptr;
    uint64_t stable_id_ = 0;
    const Decl* owner_decl_ = nullptr;
    std::string lookup_name_;

    std::vector<std::shared_ptr<DeclContext>> lexical_children_;
    std::unordered_map<std::string, std::vector<DeclContext*>> named_lexical_children_;
    std::vector<DeclBinding> declarations_;
    std::vector<NamespaceBindingEntry> namespace_bindings_;
    std::unordered_map<std::string, size_t> namespace_binding_indices_;
    std::vector<NamespaceBindingEntry> namespace_aliases_;
    std::unordered_map<std::string, size_t> namespace_alias_indices_;
    std::vector<NamespaceNominationRecord> namespace_nominations_;
    uint64_t next_lookup_event_index_ = 1;

    std::unordered_map<std::string, std::vector<size_t>> ordinary_lookup_;
    std::unordered_map<std::string, std::vector<size_t>> tag_lookup_;
    std::unordered_map<std::string, std::vector<size_t>> label_lookup_;
};

#endif // ABURI_DECL_CONTEXT_H
