#ifndef ABURI_AST_CONTEXT_H
#define ABURI_AST_CONTEXT_H

#include <cstdint>
#include <cstddef>
#include <memory>
#include <cassert>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include "dense_map.h"
#include "attributes.h"
#include "abi/abi_policy.h"
#include "types.h"
#include "symbols.h"

// Forward declarations
struct TargetInfo;
struct Decl;
struct ObjectDecl;
struct CppRecordDecl;
struct ParamDecl;
struct FuncDecl;
struct VariableDecl;
struct TemplateDecl;
struct ClassTemplateDecl;
struct FunctionTemplateDecl;
struct VariableTemplateDecl;
struct ConceptDecl;
struct TemplateParameterDecl;
struct EnumDecl;
struct Scope;
class CollectSemanticStore;

// Bitfield layout info stored in the side table, keyed by MemberExpr node_id.
struct BitfieldInfo {
    uint32_t bit_offset = 0;
    uint32_t bit_width = 0;
    uint32_t storage_size = 0;
};

// C++ member semantic metadata keyed by member Decl node_id.
// This intentionally keeps the side-table payload minimal.
enum class CppMemberRefQualifier : uint8_t {
    None,
    LValue,
    RValue
};

struct CppMemberDeclInfo {
    // Mirrors CppAccessSpecifier encoding: 0=None, 1=Public, 2=Protected, 3=Private.
    uint8_t declared_access = 0;
    bool is_method = false;
    bool is_static = false;
    bool is_constructor = false;
    bool is_destructor = false;
    bool is_explicit = false;
    bool is_virtual = false;
    bool is_override = false;
    bool is_final = false;
    bool is_pure = false;
    bool is_constexpr = false;
    bool is_consteval = false;
    bool is_mutable = false;
    CppMemberRefQualifier ref_qualifier = CppMemberRefQualifier::None;
};

// C++ virtual-call lowering metadata keyed by CppMemberCallExpr node_id.
struct CppVirtualCallInfo {
    uint32_t slot_index = 0;
    int32_t this_adjustment = 0;
    const ObjectDecl* static_record_decl = nullptr;
    std::shared_ptr<Symbol> static_symbol = nullptr;
};

struct CppLambdaClosureDeclInfo {
    const FuncDecl* call_operator_decl = nullptr;
    const TemplateDecl* call_operator_template = nullptr;
    const FuncDecl* function_pointer_invoker_decl = nullptr;
    bool has_syntactic_captures = false;
};

struct CppLambdaInvokerInfo {
    QualType closure_type;
    const FuncDecl* call_operator_decl = nullptr;
};

using EnumSemanticsCacheEntry = EnumSemanticState;

struct TemplateSpecializationSemanticKey {
    const TemplateDecl* primary_template = nullptr;
    std::vector<TemplateArgument> arguments;

    bool operator==(const TemplateSpecializationSemanticKey& other) const;
};

struct TemplateSpecializationSemanticKeyHash {
    size_t operator()(const TemplateSpecializationSemanticKey& key) const;
};

struct ClassTemplateSpecializationEntry {
    struct PendingMemberBodyInstantiation {
        const FuncDecl* pattern_function = nullptr;
        FuncDecl* specialized_function = nullptr;
        std::shared_ptr<Symbol> specialized_symbol = nullptr;
        bool use_implicit_this = true;
        bool is_materialized = false;
        bool is_materializing = false;
        bool failed = false;
        std::unordered_map<const Symbol*, std::shared_ptr<Symbol>> symbol_remap;
        std::unordered_map<const Scope*, std::shared_ptr<Scope>> scope_remap;
        std::unordered_map<const ObjectDecl*, QualType> record_type_remap;
        std::unordered_map<const TemplateParameterDecl*, TemplateParameterDecl*>
            template_parameter_remap;
        std::unordered_map<const TemplateDecl*, TemplateDecl*> template_decl_remap;
    };

    const ClassTemplateDecl* primary_template = nullptr;
    TemplateSpecializationSemanticKey semantic_key;
    std::vector<TemplateArgument> arguments;
    std::shared_ptr<ObjectType> specialization_type = nullptr;
    std::unique_ptr<ObjectDecl> specialization_decl;
    std::vector<std::unique_ptr<Decl>> member_decls;
    // Member-template specializations can retain raw pointers to earlier
    // specialized member-template clones. Keep rebuilt members alive while
    // excluding them from current semantic lookup and codegen walks.
    std::vector<std::unique_ptr<Decl>> retired_member_decls;
    SrcLoc first_required_loc;
    std::unordered_map<const Decl*, SrcLoc> primary_member_first_required_locs;
    std::unordered_map<const Decl*, const Decl*>
        specialized_member_to_primary_member_decl;
    std::unordered_map<const Symbol*, const Decl*>
        specialized_member_symbol_to_primary_member_decl;
    std::unordered_map<const Decl*, const FunctionTemplateDecl*>
        primary_member_owner_specialized_templates;
    std::unordered_map<const Decl*, PendingMemberBodyInstantiation>
        pending_member_body_instantiations;
    bool is_instantiating = false;
    bool is_instantiated = false;
    bool instantiation_failed = false;

    void retire_member_decls_for_rebuild();

    void note_first_required_loc(SrcLoc loc) {
        if (!loc.isInvalid() && first_required_loc.isInvalid()) {
            first_required_loc = loc;
        }
    }

    void note_primary_member_first_required_loc(const Decl* primary_member_decl,
                                                SrcLoc loc) {
        if (!primary_member_decl || loc.isInvalid()) {
            return;
        }
        auto [it, inserted] =
            primary_member_first_required_locs.emplace(primary_member_decl, loc);
        if (!inserted && it->second.isInvalid()) {
            it->second = loc;
        }
    }

    SrcLoc lookup_primary_member_first_required_loc(
        const Decl* primary_member_decl) const {
        if (!primary_member_decl) {
            return SrcLoc();
        }
        auto it = primary_member_first_required_locs.find(primary_member_decl);
        if (it == primary_member_first_required_locs.end()) {
            return SrcLoc();
        }
        return it->second;
    }

    void map_specialized_member_to_primary_member(
        const Decl* specialized_member_decl,
        const Decl* primary_member_decl) {
        if (!specialized_member_decl || !primary_member_decl) {
            return;
        }
        specialized_member_to_primary_member_decl[specialized_member_decl] =
            primary_member_decl;
    }

    const Decl* lookup_primary_member_for_specialized_decl(
        const Decl* specialized_member_decl) const {
        if (!specialized_member_decl) {
            return nullptr;
        }
        auto it =
            specialized_member_to_primary_member_decl.find(specialized_member_decl);
        if (it == specialized_member_to_primary_member_decl.end()) {
            return nullptr;
        }
        return it->second;
    }

    void map_specialized_member_symbol_to_primary_member(
        const Symbol* specialized_member_symbol,
        const Decl* primary_member_decl) {
        if (!specialized_member_symbol || !primary_member_decl) {
            return;
        }
        specialized_member_symbol_to_primary_member_decl[specialized_member_symbol] =
            primary_member_decl;
    }

    const Decl* lookup_primary_member_for_specialized_symbol(
        const Symbol* specialized_member_symbol) const {
        if (!specialized_member_symbol) {
            return nullptr;
        }
        auto it = specialized_member_symbol_to_primary_member_decl.find(
            specialized_member_symbol);
        if (it == specialized_member_symbol_to_primary_member_decl.end()) {
            return nullptr;
        }
        return it->second;
    }

    void map_owner_specialized_member_template(
        const Decl* primary_member_decl,
        const FunctionTemplateDecl* specialized_template_decl) {
        if (!primary_member_decl || !specialized_template_decl) {
            return;
        }
        primary_member_owner_specialized_templates[primary_member_decl] =
            specialized_template_decl;
    }

    const FunctionTemplateDecl* lookup_owner_specialized_member_template(
        const Decl* primary_member_decl) const {
        if (!primary_member_decl) {
            return nullptr;
        }
        auto it =
            primary_member_owner_specialized_templates.find(primary_member_decl);
        if (it == primary_member_owner_specialized_templates.end()) {
            return nullptr;
        }
        return it->second;
    }

    void record_pending_member_body_instantiation(
        const Decl* primary_member_decl,
        PendingMemberBodyInstantiation instantiation) {
        if (!primary_member_decl || !instantiation.specialized_function) {
            return;
        }
        pending_member_body_instantiations[primary_member_decl] =
            std::move(instantiation);
    }

    PendingMemberBodyInstantiation*
    lookup_pending_member_body_instantiation(const Decl* primary_member_decl) {
        if (!primary_member_decl) {
            return nullptr;
        }
        auto it = pending_member_body_instantiations.find(primary_member_decl);
        if (it == pending_member_body_instantiations.end()) {
            return nullptr;
        }
        return &it->second;
    }

    const PendingMemberBodyInstantiation*
    lookup_pending_member_body_instantiation(
        const Decl* primary_member_decl) const {
        if (!primary_member_decl) {
            return nullptr;
        }
        auto it = pending_member_body_instantiations.find(primary_member_decl);
        if (it == pending_member_body_instantiations.end()) {
            return nullptr;
        }
        return &it->second;
    }
};

struct FunctionTemplateSpecializationInfo {
    const FunctionTemplateDecl* primary_template = nullptr;
    std::vector<TemplateArgument> arguments;
};

struct VariableTemplateSpecializationInfo {
    const VariableTemplateDecl* primary_template = nullptr;
    std::vector<TemplateArgument> arguments;
};

struct FunctionTemplateSpecializationEntry {
    const FunctionTemplateDecl* primary_template = nullptr;
    TemplateSpecializationSemanticKey semantic_key;
    std::vector<TemplateArgument> arguments;
    std::unique_ptr<FuncDecl> specialization_decl;
    std::shared_ptr<Symbol> specialization_symbol = nullptr;
    SrcLoc first_required_loc;
    bool is_instantiating = false;
    bool is_instantiated = false;
    bool instantiation_failed = false;

    void note_first_required_loc(SrcLoc loc) {
        if (!loc.isInvalid() && first_required_loc.isInvalid()) {
            first_required_loc = loc;
        }
    }
};

struct VariableTemplateSpecializationEntry {
    const VariableTemplateDecl* primary_template = nullptr;
    TemplateSpecializationSemanticKey semantic_key;
    std::vector<TemplateArgument> arguments;
    std::unique_ptr<VariableDecl> specialization_decl;
    std::shared_ptr<Symbol> specialization_symbol = nullptr;
    SrcLoc first_required_loc;
    bool is_instantiating = false;
    bool is_instantiated = false;
    bool instantiation_failed = false;

    void note_first_required_loc(SrcLoc loc) {
        if (!loc.isInvalid() && first_required_loc.isInvalid()) {
            first_required_loc = loc;
        }
    }
};

struct ConceptSpecializationEntry {
    const ConceptDecl* primary_template = nullptr;
    TemplateSpecializationSemanticKey semantic_key;
    std::vector<TemplateArgument> arguments;
    SrcLoc first_required_loc;
    bool is_evaluating = false;
    bool is_evaluated = false;
    bool evaluation_failed = false;
    bool satisfaction = false;

    void note_first_required_loc(SrcLoc loc) {
        if (!loc.isInvalid() && first_required_loc.isInvalid()) {
            first_required_loc = loc;
        }
    }
};

struct FuncExternalSemanticInfo {
    const std::string* cxx_qualifier_prefix = nullptr;
    QualType owner_record_type;
    std::optional<FunctionTemplateSpecializationInfo>
        function_template_specialization;

    bool empty() const {
        return cxx_qualifier_prefix == nullptr &&
               !owner_record_type &&
               !function_template_specialization.has_value();
    }
};

struct VariableExternalSemanticInfo {
    std::optional<VariableTemplateSpecializationInfo>
        variable_template_specialization;

    bool empty() const {
        return !variable_template_specialization.has_value();
    }
};

struct ParamExternalSemanticInfo {
    std::unique_ptr<Expr> default_argument;

    bool empty() const {
        return !default_argument;
    }
};

struct SymbolExternalSemanticInfo {
    const std::string* cxx_qualifier_prefix = nullptr;
    QualType owner_record_type;
    std::optional<FunctionTemplateSpecializationInfo>
        function_template_specialization;
    std::optional<VariableTemplateSpecializationInfo>
        variable_template_specialization;
    std::vector<const Expr*> cpp_default_arguments;

    bool empty() const {
        return cxx_qualifier_prefix == nullptr &&
               !owner_record_type &&
               !function_template_specialization.has_value() &&
               !variable_template_specialization.has_value() &&
               cpp_default_arguments.empty();
    }
};

class ASTContext {
public:
    // Construct with default TypeContext and GlobalIdentTracker
    ASTContext();

    // Construct with target-aware TypeContext
    explicit ASTContext(std::shared_ptr<TargetInfo> ti);
    ~ASTContext();
    uint32_t registry_id() const { return registry_id_; }
    CollectSemanticStore& semantic_store();
    const CollectSemanticStore& semantic_store() const;

    // --- Node ID allocation ---
    uint32_t next_node_id() {
        assert(node_id_counter_ < DenseMap<int>::sentinel_tombstone()
               && "node ID overflow: would collide with DenseMap sentinels");
        return node_id_counter_++;
    }

    // --- Attribute side table ---
    void set_attrs(uint32_t id, AttributeList attrs);
    void append_attrs(uint32_t id, std::vector<ParsedAttribute>&& attrs);
    const AttributeList& get_attrs(uint32_t id) const;
    AttributeList& get_attrs_mut(uint32_t id);
    bool has_attrs(uint32_t id) const;
    uint32_t attr_table_size() const { return attr_table_.size(); }
    uint32_t attr_table_capacity() const { return attr_table_.capacity(); }
    size_t attr_table_memory_usage_bytes() const { return attr_table_.memory_usage_bytes(); }

    // --- Bitfield side table ---
    void set_bitfield_info(uint32_t id, BitfieldInfo info);
    BitfieldInfo* get_bitfield_info(uint32_t id);
    const BitfieldInfo* get_bitfield_info(uint32_t id) const;
    uint32_t bitfield_table_size() const { return bitfield_table_.size(); }
    uint32_t bitfield_table_capacity() const { return bitfield_table_.capacity(); }
    size_t bitfield_table_memory_usage_bytes() const { return bitfield_table_.memory_usage_bytes(); }

    // --- C++ member-declaration side table ---
    void set_cpp_member_decl_info(uint32_t id, CppMemberDeclInfo info);
    CppMemberDeclInfo* get_cpp_member_decl_info(uint32_t id);
    const CppMemberDeclInfo* get_cpp_member_decl_info(uint32_t id) const;
    bool has_cpp_member_decl_info(uint32_t id) const;
    uint32_t cpp_member_decl_info_table_size() const { return cpp_member_decl_info_table_.size(); }
    uint32_t cpp_member_decl_info_table_capacity() const { return cpp_member_decl_info_table_.capacity(); }
    size_t cpp_member_decl_info_table_memory_usage_bytes() const {
        return cpp_member_decl_info_table_.memory_usage_bytes();
    }

    // --- C++ variable-destructor side table ---
    void set_cpp_variable_destructor_symbol(uint32_t id, std::shared_ptr<Symbol> sym);
    std::shared_ptr<Symbol>* get_cpp_variable_destructor_symbol(uint32_t id);
    const std::shared_ptr<Symbol>* get_cpp_variable_destructor_symbol(uint32_t id) const;
    bool has_cpp_variable_destructor_symbol(uint32_t id) const;
    uint32_t cpp_variable_destructor_table_size() const {
        return cpp_variable_destructor_table_.size();
    }
    uint32_t cpp_variable_destructor_table_capacity() const {
        return cpp_variable_destructor_table_.capacity();
    }
    size_t cpp_variable_destructor_table_memory_usage_bytes() const {
        return cpp_variable_destructor_table_.memory_usage_bytes();
    }

    // --- C++ virtual-call side table ---
    void set_cpp_virtual_call_info(uint32_t id, CppVirtualCallInfo info);
    CppVirtualCallInfo* get_cpp_virtual_call_info(uint32_t id);
    const CppVirtualCallInfo* get_cpp_virtual_call_info(uint32_t id) const;
    bool has_cpp_virtual_call_info(uint32_t id) const;
    uint32_t cpp_virtual_call_info_table_size() const {
        return cpp_virtual_call_info_table_.size();
    }
    uint32_t cpp_virtual_call_info_table_capacity() const {
        return cpp_virtual_call_info_table_.capacity();
    }
    size_t cpp_virtual_call_info_table_memory_usage_bytes() const {
        return cpp_virtual_call_info_table_.memory_usage_bytes();
    }

    // --- C++ lambda semantic side tables ---
    void set_cpp_lambda_closure_decl_info(uint32_t id, CppLambdaClosureDeclInfo info);
    CppLambdaClosureDeclInfo* get_cpp_lambda_closure_decl_info(uint32_t id);
    const CppLambdaClosureDeclInfo* get_cpp_lambda_closure_decl_info(uint32_t id) const;
    bool has_cpp_lambda_closure_decl_info(uint32_t id) const;
    uint32_t cpp_lambda_closure_decl_info_table_size() const {
        return cpp_lambda_closure_decl_info_table_.size();
    }
    uint32_t cpp_lambda_closure_decl_info_table_capacity() const {
        return cpp_lambda_closure_decl_info_table_.capacity();
    }
    size_t cpp_lambda_closure_decl_info_table_memory_usage_bytes() const {
        return cpp_lambda_closure_decl_info_table_.memory_usage_bytes();
    }

    void set_cpp_lambda_invoker_info(uint32_t id, CppLambdaInvokerInfo info);
    CppLambdaInvokerInfo* get_cpp_lambda_invoker_info(uint32_t id);
    const CppLambdaInvokerInfo* get_cpp_lambda_invoker_info(uint32_t id) const;
    bool has_cpp_lambda_invoker_info(uint32_t id) const;
    uint32_t cpp_lambda_invoker_info_table_size() const {
        return cpp_lambda_invoker_info_table_.size();
    }
    uint32_t cpp_lambda_invoker_info_table_capacity() const {
        return cpp_lambda_invoker_info_table_.capacity();
    }
    size_t cpp_lambda_invoker_info_table_memory_usage_bytes() const {
        return cpp_lambda_invoker_info_table_.memory_usage_bytes();
    }

    // --- Identifier interning pool ---
    const std::string* intern_identifier(std::string_view spelling);
    size_t identifier_pool_size() const { return identifier_pool_.size(); }
    size_t identifier_pool_string_storage_bytes() const { return identifier_pool_string_storage_bytes_; }
    size_t identifier_pool_memory_usage_bytes() const;

    // --- External semantic side tables (declaration/symbol metadata) ---
    void set_func_decl_cxx_qualifier_prefix(const FuncDecl* decl,
                                            std::optional<std::string> prefix);
    const std::string* get_func_decl_cxx_qualifier_prefix(
        const FuncDecl* decl) const;
    void clear_func_decl_cxx_qualifier_prefixes();
    void set_func_decl_owner_record_type(const FuncDecl* decl, QualType owner_type);
    QualType get_func_decl_owner_record_type(const FuncDecl* decl) const;
    void clear_func_decl_owner_record_types();

    void set_func_decl_function_template_specialization(
        const FuncDecl* decl,
        FunctionTemplateSpecializationInfo info);
    const FunctionTemplateSpecializationInfo*
    get_func_decl_function_template_specialization(const FuncDecl* decl) const;
    void clear_func_decl_function_template_specializations();

    void set_variable_decl_variable_template_specialization(
        const VariableDecl* decl,
        VariableTemplateSpecializationInfo info);
    const VariableTemplateSpecializationInfo*
    get_variable_decl_variable_template_specialization(
        const VariableDecl* decl) const;
    void clear_variable_decl_variable_template_specializations();

    void set_template_decl_canonical_decl(const TemplateDecl* decl,
                                          const TemplateDecl* canonical_decl);
    const TemplateDecl* get_template_decl_canonical_decl(
        const TemplateDecl* decl) const;
    void set_template_decl_definition_decl(const TemplateDecl* decl,
                                          const TemplateDecl* definition_decl);
    const TemplateDecl* get_template_decl_definition_decl(
        const TemplateDecl* decl) const;
    void clear_template_decl_canonical_decls();

    void set_template_parameter_default_argument(
        const TemplateParameterDecl* decl,
        std::optional<TemplateArgument> argument);
    const TemplateArgument* get_template_parameter_default_argument(
        const TemplateParameterDecl* decl) const;
    void clear_template_parameter_default_arguments();

    bool merge_template_decl_default_arguments(
        const TemplateDecl* decl,
        size_t* conflict_param_index = nullptr);
    const std::vector<std::optional<TemplateArgument>>*
    get_template_decl_default_arguments(const TemplateDecl* decl) const;
    void clear_template_decl_default_arguments();

    void set_param_decl_default_argument(const ParamDecl* decl,
                                         std::unique_ptr<Expr> expr);
    const Expr* get_param_decl_default_argument(const ParamDecl* decl) const;
    void clear_param_decl_default_arguments();

    void set_symbol_cxx_qualifier_prefix(const Symbol* sym,
                                         std::optional<std::string> prefix);
    const std::string* get_symbol_cxx_qualifier_prefix(
        const Symbol* sym) const;
    void clear_symbol_cxx_qualifier_prefixes();
    void set_symbol_owner_record_type(const Symbol* sym, QualType owner_type);
    QualType get_symbol_owner_record_type(const Symbol* sym) const;
    void clear_symbol_owner_record_types();

    void set_symbol_function_template_specialization(
        const Symbol* sym,
        FunctionTemplateSpecializationInfo info);
    const FunctionTemplateSpecializationInfo*
    get_symbol_function_template_specialization(const Symbol* sym) const;
    void clear_symbol_function_template_specializations();

    void set_symbol_variable_template_specialization(
        const Symbol* sym,
        VariableTemplateSpecializationInfo info);
    const VariableTemplateSpecializationInfo*
    get_symbol_variable_template_specialization(const Symbol* sym) const;
    void clear_symbol_variable_template_specializations();

    bool merge_symbol_cpp_default_arguments(
        const Symbol* sym,
        const std::vector<const Expr*>& defaults,
        size_t* conflict_param_index = nullptr);
    const std::vector<const Expr*>* get_symbol_cpp_default_arguments(
        const Symbol* sym) const;
    void clear_symbol_cpp_default_arguments();

    void set_template_specialization_resolved_type(QualType type,
                                                   QualType resolved_type);
    QualType get_template_specialization_resolved_type(
        const TemplateSpecializationType* type) const;
    void clear_template_specialization_resolved_types();

    void set_dependent_name_resolved_type(QualType type,
                                          QualType resolved_type);
    QualType get_dependent_name_resolved_type(
        const DependentNameType* type) const;
    void clear_dependent_name_resolved_types();

    void clear_record_semantics_cache();
    void set_record_semantics(const ObjectDecl* record_decl,
                              RecordSemanticState state);
    void erase_record_semantics(const ObjectDecl* record_decl);
    const RecordSemanticState* lookup_record_semantics(
        const ObjectDecl* record_decl) const;
    uint64_t record_semantics_cache_epoch() const;

    void clear_enum_semantics_cache();
    void set_enum_semantics(const EnumDecl* enum_decl,
                            EnumSemanticState state);
    void erase_enum_semantics(const EnumDecl* enum_decl);
    bool lookup_enum_semantics(const EnumDecl* enum_decl,
                               EnumSemanticState& state_out) const;

    ClassTemplateSpecializationEntry* lookup_class_template_specialization(
        const ClassTemplateDecl* primary_template,
        const std::vector<TemplateArgument>& arguments);
    const ClassTemplateSpecializationEntry* lookup_class_template_specialization(
        const ClassTemplateDecl* primary_template,
        const std::vector<TemplateArgument>& arguments) const;
    ClassTemplateSpecializationEntry& get_or_create_class_template_specialization(
        const ClassTemplateDecl* primary_template,
        std::vector<TemplateArgument> arguments,
        std::shared_ptr<ObjectType> specialization_type,
        std::unique_ptr<ObjectDecl> specialization_decl);
    const std::vector<std::unique_ptr<ClassTemplateSpecializationEntry>>&
    class_template_specializations() const;

    FunctionTemplateSpecializationEntry* lookup_function_template_specialization(
        const FunctionTemplateDecl* primary_template,
        const std::vector<TemplateArgument>& arguments);
    const FunctionTemplateSpecializationEntry* lookup_function_template_specialization(
        const FunctionTemplateDecl* primary_template,
        const std::vector<TemplateArgument>& arguments) const;
    FunctionTemplateSpecializationEntry& get_or_create_function_template_specialization(
        const FunctionTemplateDecl* primary_template,
        std::vector<TemplateArgument> arguments,
        std::unique_ptr<FuncDecl> specialization_decl,
        std::shared_ptr<Symbol> specialization_symbol);
    const std::vector<std::unique_ptr<FunctionTemplateSpecializationEntry>>&
    function_template_specializations() const;

    VariableTemplateSpecializationEntry* lookup_variable_template_specialization(
        const VariableTemplateDecl* primary_template,
        const std::vector<TemplateArgument>& arguments);
    const VariableTemplateSpecializationEntry*
    lookup_variable_template_specialization(
        const VariableTemplateDecl* primary_template,
        const std::vector<TemplateArgument>& arguments) const;
    VariableTemplateSpecializationEntry& get_or_create_variable_template_specialization(
        const VariableTemplateDecl* primary_template,
        std::vector<TemplateArgument> arguments,
        std::unique_ptr<VariableDecl> specialization_decl,
        std::shared_ptr<Symbol> specialization_symbol);
    const std::vector<std::unique_ptr<VariableTemplateSpecializationEntry>>&
    variable_template_specializations() const;

    ConceptSpecializationEntry* lookup_concept_specialization(
        const ConceptDecl* primary_template,
        const std::vector<TemplateArgument>& arguments);
    const ConceptSpecializationEntry* lookup_concept_specialization(
        const ConceptDecl* primary_template,
        const std::vector<TemplateArgument>& arguments) const;
    ConceptSpecializationEntry& get_or_create_concept_specialization(
        const ConceptDecl* primary_template,
        std::vector<TemplateArgument> arguments);
    const std::vector<std::unique_ptr<ConceptSpecializationEntry>>&
    concept_specializations() const;

    bool push_template_instantiation_frame(size_t max_depth = 64);
    void pop_template_instantiation_frame();
    size_t template_instantiation_depth() const;

    void clear_external_semantic_side_tables();
    void clear_all_semantic_state();

    // Retain declaration nodes that are only needed for semantic/type
    // ownership and are not inserted into the traversed AST.
    void retain_external_decl(std::unique_ptr<Decl> decl);
    const std::vector<std::unique_ptr<Decl>>& retained_external_decls() const;

    // --- Shared context objects ---
    std::shared_ptr<TypeContext> type_ctx;
    std::shared_ptr<GlobalIdentTracker> global_tracker;
    std::shared_ptr<AbiPolicy> abi_policy;

private:
    using FuncExternalSemanticInfoMap =
        std::unordered_map<const FuncDecl*, FuncExternalSemanticInfo>;
    using VariableExternalSemanticInfoMap =
        std::unordered_map<const VariableDecl*, VariableExternalSemanticInfo>;
    using ParamExternalSemanticInfoMap =
        std::unordered_map<const ParamDecl*, ParamExternalSemanticInfo>;
    using SymbolExternalSemanticInfoMap =
        std::unordered_map<const Symbol*, SymbolExternalSemanticInfo>;
    using TemplateSpecializationResolvedTypeMap =
        std::unordered_map<const TemplateSpecializationType*, QualType>;
    using DependentNameResolvedTypeMap =
        std::unordered_map<const DependentNameType*, QualType>;
    using RecordSemanticsCacheMap =
        std::unordered_map<const ObjectDecl*, RecordSemanticState>;
    using EnumSemanticsCacheMap =
        std::unordered_map<const EnumDecl*, EnumSemanticsCacheEntry>;

    uint32_t node_id_counter_ = 0;
    DenseMap<AttributeList> attr_table_;
    DenseMap<BitfieldInfo> bitfield_table_;
    DenseMap<CppMemberDeclInfo> cpp_member_decl_info_table_;
    DenseMap<std::shared_ptr<Symbol>> cpp_variable_destructor_table_;
    DenseMap<CppVirtualCallInfo> cpp_virtual_call_info_table_;
    DenseMap<CppLambdaClosureDeclInfo> cpp_lambda_closure_decl_info_table_;
    DenseMap<CppLambdaInvokerInfo> cpp_lambda_invoker_info_table_;
    std::unordered_set<std::string> identifier_pool_;
    size_t identifier_pool_string_storage_bytes_ = 0;
    std::unique_ptr<CollectSemanticStore> semantic_store_;
    uint32_t registry_id_ = 0;
};

ASTContext* get_active_side_table_ast_context();
ASTContext* get_side_table_ast_context_for(const FuncDecl* decl);
ASTContext* get_side_table_ast_context_for(const VariableDecl* decl);
ASTContext* get_side_table_ast_context_for(const TemplateDecl* decl);
ASTContext* get_side_table_ast_context_for(const TemplateParameterDecl* decl);
ASTContext* get_side_table_ast_context_for(const ParamDecl* decl);
ASTContext* get_side_table_ast_context_for(const ObjectDecl* decl);
ASTContext* get_side_table_ast_context_for(const EnumDecl* decl);
ASTContext* get_side_table_ast_context_for(const Symbol* sym);

class ASTContextSideTableScope {
public:
    explicit ASTContextSideTableScope(ASTContext* context);
    ~ASTContextSideTableScope();

    ASTContextSideTableScope(const ASTContextSideTableScope&) = delete;
    ASTContextSideTableScope& operator=(const ASTContextSideTableScope&) = delete;

private:
    ASTContext* previous_context_ = nullptr;
    CollectSemanticStore* previous_semantic_store_ = nullptr;
};

// Helper to create an AST node and assign it a node_id from the context.
// Works for any node type whose base class (Stmt or Decl) has a node_id field.
template<typename T, typename... Args>
std::unique_ptr<T> make_ast(ASTContext& ctx, Args&&... args) {
    auto p = std::make_unique<T>(std::forward<Args>(args)...);
    p->node_id = ctx.next_node_id();
    return p;
}

#endif // ABURI_AST_CONTEXT_H
