#ifndef ABURI_SYMBOLS_H
#define ABURI_SYMBOLS_H
#include <unordered_map>
#include <optional>
#include <cstdint>
#include "types.h"
#include "attributes.h"
#include <string>
#include <vector>
enum class SymbolKind : uint8_t {
    VARIABLE,
    FUNCTION,
    TYPE,
    ENUM_CONSTANT
};
enum class StorageClass : uint8_t {
    NONE,
    STATIC,
    EXTERN,
    AUTO,
    REGISTER,
    TYPEDEF
};
enum class VariableLinkage : uint8_t {
    NONE,
    INTERNAL,
    EXTERNAL
};

enum class LanguageLinkage : uint8_t {
    None = 0,
    C = 1,
    CXX = 2,
};

enum class ScopeFlags : uint32_t {
    None = 0,
    FileScope = 1u << 0,
    FunctionScope = 1u << 1,
    BlockScope = 1u << 2,
    PrototypeScope = 1u << 3,
    LoopScope = 1u << 4,
    SwitchScope = 1u << 5,
    NamespaceScope = 1u << 6,
    TemplateParameterScope = 1u << 7
};

inline ScopeFlags operator|(ScopeFlags lhs, ScopeFlags rhs) {
    return static_cast<ScopeFlags>(
        static_cast<uint32_t>(lhs) | static_cast<uint32_t>(rhs));
}

inline ScopeFlags operator&(ScopeFlags lhs, ScopeFlags rhs) {
    return static_cast<ScopeFlags>(
        static_cast<uint32_t>(lhs) & static_cast<uint32_t>(rhs));
}

inline ScopeFlags& operator|=(ScopeFlags& lhs, ScopeFlags rhs) {
    lhs = lhs | rhs;
    return lhs;
}

inline bool scope_flags_contains(ScopeFlags flags, ScopeFlags value) {
    return (flags & value) != ScopeFlags::None;
}

struct FuncDecl;
struct Expr;
struct TemplateParameterDecl;
class DeclContext;
struct VariableDecl;
struct Symbol {
    std::string uid;
    std::string name;
    SymbolKind kind;
    StorageClass storage_class;
    VariableLinkage linkage;
    uint8_t is_defined : 1;   // function
    uint8_t is_inline : 1;
    uint8_t had_non_inline_declaration : 1;
    uint8_t is_constexpr : 1;
    uint8_t is_deprecated : 1;
    uint8_t is_block_byref : 1;
    uint8_t language_linkage : 2;
    mutable uint32_t external_semantic_owner_id = 0;
    QualType type;
    int input_types; // for functions
    int64_t enum_val; // for enum constants
    std::string deprecated_message;
    AttributeList sym_attrs;  // Merged attributes across declarations
    std::optional<std::string> asm_label;
    const FuncDecl* function_definition = nullptr;
    const VariableDecl* variable_definition = nullptr;
    const TemplateParameterDecl* template_parameter_decl = nullptr;

    bool is_const() const { return type.is_const(); }

    Symbol(std::string name, SymbolKind kind, QualType type)
        : uid(""),
          name(std::move(name)),
          kind(kind),
          storage_class(StorageClass::NONE),
          linkage(VariableLinkage::NONE),
          is_defined(false),
          is_inline(false),
          had_non_inline_declaration(false),
          is_constexpr(false),
          is_deprecated(false),
          is_block_byref(false),
          language_linkage(static_cast<uint8_t>(LanguageLinkage::None)),
          type(std::move(type)),
          input_types(0),
          enum_val(0) {}
    Symbol(std::string name, SymbolKind kind, QualType type,
        StorageClass storage_class, VariableLinkage variable_link = VariableLinkage::NONE, bool is_inline = false)
        : uid(""),
          name(std::move(name)),
          kind(kind),
          storage_class(storage_class),
          linkage(variable_link),
          is_defined(false),
          is_inline(is_inline),
          had_non_inline_declaration(!is_inline),
          is_constexpr(false),
          is_deprecated(false),
          is_block_byref(false),
          language_linkage(static_cast<uint8_t>(LanguageLinkage::None)),
          type(std::move(type)),
          input_types(0),
          enum_val(0) {}

    LanguageLinkage get_language_linkage() const {
        return static_cast<LanguageLinkage>(language_linkage);
    }

    void set_language_linkage(LanguageLinkage linkage_kind) {
        language_linkage = static_cast<uint8_t>(linkage_kind);
    }
};

void set_symbol_cxx_qualifier_prefix(const Symbol* sym,
                                     std::optional<std::string> prefix);
const std::string* get_symbol_cxx_qualifier_prefix(const Symbol* sym);
void clear_symbol_cxx_qualifier_prefixes();
void set_symbol_owner_record_type(const Symbol* sym, QualType owner_type);
QualType get_symbol_owner_record_type(const Symbol* sym);
void clear_symbol_owner_record_types();
struct FunctionTemplateSpecializationInfo;
void set_symbol_function_template_specialization(
    const Symbol* sym,
    const FunctionTemplateSpecializationInfo& info);
const FunctionTemplateSpecializationInfo*
get_symbol_function_template_specialization(const Symbol* sym);
void clear_symbol_function_template_specializations();
bool merge_symbol_cpp_default_arguments(
    const Symbol* sym,
    const std::vector<const Expr*>& defaults,
    size_t* conflict_param_index = nullptr);
const std::vector<const Expr*>* get_symbol_cpp_default_arguments(
    const Symbol* sym);
void clear_symbol_cpp_default_arguments();
struct GlobalIdentTracker {
    std::unordered_map<std::string, std::vector<std::shared_ptr<Symbol>>> all_variables;
    void add_to_global_scope(std::shared_ptr<Symbol> sym) {
        // Generate a globally unique UID based on the name of the symbol,
        // check to make sure its unique via iterating in all_variables,
        // then add it to all_variables
        std::string base_name = sym->name;
        int counter = all_variables[base_name].size() + 1;
        std::string current_uid = base_name + "_" + std::to_string(counter);
        sym->uid = current_uid;
        all_variables[base_name].push_back(sym);
        // todo: simplify by just having a global counter of all variables
    }

};
struct Scope {
    // Separate namespace for struct/union/enum tags (C has separate namespaces).
    // Canonical ownership is declaration-based.
    std::shared_ptr<Scope> parent = nullptr;
    ScopeFlags flags = ScopeFlags::None;
    std::vector<std::string> cxx_namespace_path;
    DeclContext* associated_decl_context = nullptr;


    Scope(): parent(nullptr), flags(ScopeFlags::None),
        cxx_namespace_path(),
        associated_decl_context(nullptr) {};
};

#endif //ABURI_SYMBOLS_H
