#ifndef ABURI_DECL_CONTEXT_H
#define ABURI_DECL_CONTEXT_H

#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include "../source_mgnt.h"
#include "../ast/symbols.h"
#include "../ast/types.h"

struct Decl;
class ASTContext;
class DeclContext;
using InternedName = const std::string*;

struct NamespaceBindingEntry {
    NamespaceBindingEntry() = default;
    NamespaceBindingEntry(std::string local_name,
                          std::shared_ptr<DeclContext> target_context,
                          std::shared_ptr<Scope> target_scope,
                          InternedName interned_local_name = nullptr)
        : local_name(std::move(local_name)),
          interned_local_name(interned_local_name),
          target_context(std::move(target_context)),
          target_scope(std::move(target_scope)) {}

    std::string local_name;
    InternedName interned_local_name = nullptr;
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
    // Variables, functions, typedefs, namespace aliases, and other ordinary names.
    Ordinary = 1u << 0,
    // Struct/class/union/enum names that inhabit the tag namespace.
    Tag = 1u << 1,
    // Function-local goto labels.
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
    InternedName interned_name = nullptr;
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
                std::shared_ptr<ASTContext> ast_ctx = nullptr,
                std::shared_ptr<std::unordered_set<std::string>> local_intern_pool = nullptr,
                DeclContext* lexical_parent = nullptr,
                DeclContext* semantic_parent = nullptr,
                const Decl* owner_decl = nullptr,
                std::string lookup_name = "");

    static std::shared_ptr<DeclContext> create_translation_unit(
        std::shared_ptr<ASTContext> ast_ctx = nullptr);

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
    InternedName interned_lookup_name() const { return interned_lookup_name_; }
    InternedName intern_name(std::string_view spelling) const;
    void set_lookup_name(std::string lookup_name);
    DeclContext* find_named_lexical_child(std::string_view lookup_name) const;
    DeclContext* find_named_lexical_child(InternedName lookup_name) const;

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
    bool is_inline_namespace() const { return is_inline_namespace_; }
    DeclContext* inline_enclosing_namespace() const {
        return inline_enclosing_namespace_;
    }
    uint64_t next_lookup_event_index() const { return next_lookup_event_index_; }
    void truncate_declarations(size_t count);
    void truncate_lexical_children(size_t count);
    void truncate_namespace_bindings(size_t count);
    void truncate_namespace_aliases(size_t count);
    void truncate_namespace_nominations(size_t count);
    void set_inline_namespace(bool is_inline, DeclContext* enclosing_namespace);
    void set_next_lookup_event_index(uint64_t index) {
        next_lookup_event_index_ = index == 0 ? 1 : index;
    }

    const DeclBinding* lookup_local(const std::string& name,
                                    LookupNamespace ns) const;
    const DeclBinding* lookup_local(InternedName name,
                                    LookupNamespace ns) const;
    std::vector<const DeclBinding*> lookup_local_all(const std::string& name,
                                                     LookupNamespace ns) const;
    std::vector<const DeclBinding*> lookup_local_all(InternedName name,
                                                     LookupNamespace ns) const;
    const NamespaceBindingEntry* lookup_local_namespace(
        std::string_view local_name) const;
    const NamespaceBindingEntry* lookup_local_namespace(
        InternedName local_name) const;
    const NamespaceBindingEntry* lookup_local_namespace_alias(
        std::string_view local_name) const;
    const NamespaceBindingEntry* lookup_local_namespace_alias(
        InternedName local_name) const;
    NamespaceBindingLookup lookup_local_namespace_binding(
        std::string_view local_name) const;
    NamespaceBindingLookup lookup_local_namespace_binding(
        InternedName local_name) const;
    void add_namespace_binding(NamespaceBindingEntry binding);
    void add_namespace_alias(NamespaceBindingEntry alias);
    const std::vector<NamespaceNominationRecord>& namespace_nominations() const {
        return namespace_nominations_;
    }
    void add_namespace_nomination(NamespaceNominationRecord nomination);

private:
    static constexpr size_t k_no_decl_index = static_cast<size_t>(-1);

    struct BindingSlot {
        InternedName interned_name = nullptr;
        std::string spelled_name;
        LookupNamespace lookup_namespace = LookupNamespace::Ordinary;
        size_t visible_decl_index = k_no_decl_index;
        size_t last_update_decl_index = k_no_decl_index;
        std::vector<std::shared_ptr<Symbol>> overload_candidates;
        std::vector<const Decl*> template_candidates;
        DeclBinding cached_binding;
    };

    void index_lexical_child_name(DeclContext* child);
    void remove_lexical_child_name(DeclContext* child, InternedName lookup_name);
    BindingSlot* lookup_slot(InternedName name, LookupNamespace ns);
    const BindingSlot* lookup_slot(InternedName name, LookupNamespace ns) const;
    BindingSlot& ensure_slot(InternedName name,
                             std::string_view spelled_name,
                             LookupNamespace ns);
    void replay_binding_into_slot(const DeclBinding& binding, size_t idx);
    void refresh_cached_binding(BindingSlot& slot);
    void rebuild_binding_slots();
    uint64_t allocate_lookup_event_index() { return next_lookup_event_index_++; }
    void reindex_namespace_bindings();
    void reindex_namespace_aliases();

    std::shared_ptr<ASTContext> ast_ctx_ = nullptr;
    std::shared_ptr<std::unordered_set<std::string>> local_intern_pool_;
    DeclContextKind kind_ = DeclContextKind::Block;
    DeclContext* lexical_parent_ = nullptr;
    DeclContext* semantic_parent_ = nullptr;
    DeclContext* primary_context_ = nullptr;
    uint64_t stable_id_ = 0;
    const Decl* owner_decl_ = nullptr;
    std::string lookup_name_;
    InternedName interned_lookup_name_ = nullptr;

    std::vector<std::shared_ptr<DeclContext>> lexical_children_;
    std::unordered_map<InternedName, std::vector<DeclContext*>> named_lexical_children_;
    std::vector<DeclBinding> declarations_;
    std::vector<NamespaceBindingEntry> namespace_bindings_;
    std::unordered_map<InternedName, size_t> namespace_binding_indices_;
    std::vector<NamespaceBindingEntry> namespace_aliases_;
    std::unordered_map<InternedName, size_t> namespace_alias_indices_;
    std::vector<NamespaceNominationRecord> namespace_nominations_;
    bool is_inline_namespace_ = false;
    DeclContext* inline_enclosing_namespace_ = nullptr;
    uint64_t next_lookup_event_index_ = 1;

    std::unordered_map<InternedName, std::unique_ptr<BindingSlot>> ordinary_slots_;
    std::unordered_map<InternedName, std::unique_ptr<BindingSlot>> tag_slots_;
    std::unordered_map<InternedName, std::unique_ptr<BindingSlot>> label_slots_;
};

#endif // ABURI_DECL_CONTEXT_H
